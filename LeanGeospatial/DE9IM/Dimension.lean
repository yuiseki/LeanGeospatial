import LeanGeospatial.Geometry
import LeanGeospatial.DE9IM

/-!
# DE-9IM with dimensions

A DE-9IM cell holds `F` (empty) or the dimension `0`, `1` or `2` of the
intersection. This file does not build a dimension theory for arbitrary sets.
It classifies a cell by the largest kind of piece it contains:

| Value | The cell |
| --- | --- |
| `F` | is empty |
| `2` | contains an open set of the plane |
| `1` | contains an arc (a continuous injective image of `[0, 1]`) but no open set |
| `0` | is nonempty, with neither |

The cells of Simple Features geometries are finite unions of points, arcs and
two-dimensional pieces, and for those this is their dimension. For wild sets
(a boundary made of a pseudo-arc, say) it need not be, and it is not meant
to be used there.

Pattern characters now include `0`, `1`, `2`. The earlier `T`/`F`/`*`
patterns embed unchanged: `Pattern.toDim_matches_area` shows that on two
areas they mean what they meant in `DE9IM.lean`.
-/

namespace Geospatial.DE9IM

open Geospatial

/-- `S` contains an arc: a continuous injective image of `[0, 1]`. -/
def HasArc (S : Region) : Prop :=
  ∃ f : ℝ → Point2D, ContinuousOn f (Set.Icc 0 1) ∧ Set.InjOn f (Set.Icc 0 1) ∧
    f '' Set.Icc 0 1 ⊆ S

theorem HasArc.nonempty {S : Region} (h : HasArc S) : S.Nonempty := by
  obtain ⟨f, -, -, hf⟩ := h
  exact ⟨f 0, hf ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩

theorem HasArc.mono {S T : Region} (h : HasArc S) (hST : S ⊆ T) : HasArc T := by
  obtain ⟨f, hc, hi, hf⟩ := h
  exact ⟨f, hc, hi, hf.trans hST⟩

/-- A single point contains no arc. -/
theorem not_hasArc_of_subset_singleton {S : Region} {q : Point2D} (h : S ⊆ {q}) :
    ¬ HasArc S := by
  rintro ⟨f, -, hi, hf⟩
  have h₀ : f 0 = q := h (hf ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
  have h₁ : f 1 = q := h (hf ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩)
  have := hi ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ (h₀.trans h₁.symm)
  norm_num at this

/-- A DE-9IM cell value. -/
inductive DimValue where
  | F | d0 | d1 | d2
  deriving DecidableEq

/-- Which value describes a cell. -/
def DimValue.Describes : DimValue → Region → Prop
  | .F, S => S = ∅
  | .d0, S => S.Nonempty ∧ interior S = ∅ ∧ ¬ HasArc S
  | .d1, S => interior S = ∅ ∧ HasArc S
  | .d2, S => (interior S).Nonempty

/-- Every set has exactly one value. -/
theorem existsUnique_describes (S : Region) : ∃! d : DimValue, d.Describes S := by
  by_cases hS : S = ∅
  · refine ⟨.F, hS, ?_⟩
    rintro (_ | _ | _ | _) h
    · rfl
    · exact absurd hS h.1.ne_empty
    · exact absurd hS h.2.nonempty.ne_empty
    · exact absurd hS (h.mono interior_subset).ne_empty
  by_cases hI : (interior S).Nonempty
  · refine ⟨.d2, hI, ?_⟩
    rintro (_ | _ | _ | _) h
    · exact absurd h hS
    · exact absurd h.2.1 hI.ne_empty
    · exact absurd h.1 hI.ne_empty
    · rfl
  have hI' : interior S = ∅ := Set.not_nonempty_iff_eq_empty.mp hI
  by_cases hA : HasArc S
  · refine ⟨.d1, ⟨hI', hA⟩, ?_⟩
    rintro (_ | _ | _ | _) h
    · exact absurd h hS
    · exact absurd hA h.2.2
    · rfl
    · exact absurd h hI
  · refine ⟨.d0, ⟨Set.nonempty_iff_ne_empty.mpr hS, hI', hA⟩, ?_⟩
    rintro (_ | _ | _ | _) h
    · exact absurd h hS
    · rfl
    · exact absurd h.2 hA
    · exact absurd h hI

/-- The value of a cell. -/
noncomputable def DimValue.of (S : Region) : DimValue :=
  Classical.choose (existsUnique_describes S).exists

theorem DimValue.of_describes (S : Region) : (DimValue.of S).Describes S :=
  Classical.choose_spec (existsUnique_describes S).exists

theorem DimValue.of_eq {S : Region} {d : DimValue} (h : d.Describes S) : DimValue.of S = d :=
  (existsUnique_describes S).unique (DimValue.of_describes S) h

theorem DimValue.of_eq_F_iff (S : Region) : DimValue.of S = .F ↔ S = ∅ :=
  ⟨fun h => by have := DimValue.of_describes S; rw [h] at this; exact this,
    fun h => DimValue.of_eq h⟩

/-- A nonempty subset of a single point has value `0`. -/
theorem describes_d0_of_subset_singleton {S : Region} {q : Point2D} (hq : q ∈ S)
    (h : S ⊆ {q}) : DimValue.d0.Describes S :=
  ⟨⟨q, hq⟩, Set.eq_empty_of_subset_empty
      ((interior_mono h).trans (interior_singleton_eq_empty q).subset),
    not_hasArc_of_subset_singleton h⟩

/-! ## Pattern characters with dimensions -/

/-- A pattern character: `T`, `F`, `*`, or an exact dimension. -/
inductive DimPatternChar where
  | T | F | any | d0 | d1 | d2
  deriving DecidableEq

/-- Whether a character accepts a cell value. -/
def DimPatternChar.Accepts : DimPatternChar → DimValue → Prop
  | .T, v => v ≠ .F
  | .F, v => v = .F
  | .any, _ => True
  | .d0, v => v = .d0
  | .d1, v => v = .d1
  | .d2, v => v = .d2

/-- A character matches a cell when it accepts the cell's value. -/
def DimPatternChar.Matches (c : DimPatternChar) (S : Region) : Prop :=
  c.Accepts (DimValue.of S)

/-- A dimensioned 9-cell pattern. -/
structure DimPattern where
  ii : DimPatternChar
  ib : DimPatternChar
  ie : DimPatternChar
  bi : DimPatternChar
  bb : DimPatternChar
  be : DimPatternChar
  ei : DimPatternChar
  eb : DimPatternChar
  ee : DimPatternChar
  deriving DecidableEq

/-- Two geometries match a pattern when each of their cells does. -/
def DimPattern.Matches (p : DimPattern) (g h : Geometry) : Prop :=
  p.ii.Matches (g.cell .I .I h) ∧ p.ib.Matches (g.cell .I .B h) ∧
  p.ie.Matches (g.cell .I .E h) ∧ p.bi.Matches (g.cell .B .I h) ∧
  p.bb.Matches (g.cell .B .B h) ∧ p.be.Matches (g.cell .B .E h) ∧
  p.ei.Matches (g.cell .E .I h) ∧ p.eb.Matches (g.cell .E .B h) ∧
  p.ee.Matches (g.cell .E .E h)

def DimPatternChar.ofChar? : Char → Option DimPatternChar
  | 'T' => some .T
  | 'F' => some .F
  | '*' => some .any
  | '0' => some .d0
  | '1' => some .d1
  | '2' => some .d2
  | _ => none

/-- Read a 9-character pattern over `T F * 0 1 2`. -/
def DimPattern.ofString? (s : String) : Option DimPattern :=
  match s.toList.map DimPatternChar.ofChar? with
  | [some a, some b, some c, some d, some e, some f, some g, some h, some i] =>
    some ⟨a, b, c, d, e, f, g, h, i⟩
  | _ => none

/-! ## The DE-9IM matrix -/

/-- The DE-9IM matrix of two geometries, as values. -/
noncomputable def matrix (g h : Geometry) (s t : Stratum) : DimValue :=
  DimValue.of (g.cell s t h)

/-! ## The earlier T/F patterns are unchanged -/

/-- A `T`/`F`/`*` character as a dimensioned one. -/
def PatternChar.toDim : PatternChar → DimPatternChar
  | .T => .T
  | .F => .F
  | .any => .any

theorem PatternChar.toDim_matches (c : PatternChar) (S : Region) :
    c.toDim.Matches S ↔ c.Matches S := by
  cases c with
  | T =>
    show DimValue.of S ≠ .F ↔ S.Nonempty
    rw [Ne, DimValue.of_eq_F_iff, Set.nonempty_iff_ne_empty]
  | F => exact DimValue.of_eq_F_iff S
  | any => exact ⟨fun _ => trivial, fun _ => trivial⟩

def Pattern.toDim (p : Pattern) : DimPattern :=
  ⟨p.ii.toDim, p.ib.toDim, p.ie.toDim, p.bi.toDim, p.bb.toDim, p.be.toDim, p.ei.toDim,
    p.eb.toDim, p.ee.toDim⟩

/-- On two areas, a `T`/`F`/`*` pattern means exactly what it meant before. -/
theorem Pattern.toDim_matches_area (p : Pattern) (A B : RegularClosedRegion) :
    p.toDim.Matches (.area A) (.area B) ↔ p.Matches A B := by
  simp only [DimPattern.Matches, Pattern.toDim, Pattern.Matches, PatternChar.toDim_matches,
    Geometry.cell_area_area]

/-! ## Values that cannot occur -/

/-- A cell through a point's interior or boundary is `F` or `0`. -/
theorem point_cell_value (p : Point2D) (s : Stratum) (hs : s ≠ .E) (h : Geometry)
    (t : Stratum) : matrix (.point p) h s t = .F ∨ matrix (.point p) h s t = .d0 := by
  have hsub : Geometry.cell s t (.point p) h ⊆ {p} := by
    cases s with
    | I => exact Set.inter_subset_left
    | B => exact Set.inter_subset_left.trans (Set.empty_subset _)
    | E => exact absurd rfl hs
  by_cases hne : (Geometry.cell s t (.point p) h).Nonempty
  · obtain ⟨q, hq⟩ := hne
    have hqp : q = p := hsub hq
    subst hqp
    exact Or.inr (DimValue.of_eq (describes_d0_of_subset_singleton hq hsub))
  · exact Or.inl ((DimValue.of_eq_F_iff _).mpr (Set.not_nonempty_iff_eq_empty.mp hne))

/-- The interiors of two areas meet in `F` or `2`: their intersection is open. -/
theorem area_II_value (A B : RegularClosedRegion) :
    matrix (.area A) (.area B) .I .I = .F ∨ matrix (.area A) (.area B) .I .I = .d2 := by
  have hopen : IsOpen (Geometry.cell .I .I (.area A) (.area B)) :=
    isOpen_interior.inter isOpen_interior
  by_cases hne : (Geometry.cell .I .I (.area A) (.area B)).Nonempty
  · exact Or.inr (DimValue.of_eq (show DimValue.d2.Describes _ by
      show (interior _).Nonempty
      rw [hopen.interior_eq]
      exact hne))
  · exact Or.inl ((DimValue.of_eq_F_iff _).mpr (Set.not_nonempty_iff_eq_empty.mp hne))

end Geospatial.DE9IM
