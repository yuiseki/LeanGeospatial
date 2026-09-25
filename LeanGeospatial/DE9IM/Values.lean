import LeanGeospatial.GeometryFacts

/-!
# Which DE-9IM values each kind of geometry allows

- A cell through a point's interior or boundary is `F` or `0`, on either side.
- A cell through a line's interior or boundary is never `2`, on either side.
- The interiors of two areas meet in `F` or `2` (`area_II_value`).
- Two lines' interiors meet in `1` exactly when their intersection contains
  an arc, and in `0` exactly when it is nonempty without one. So a crossing
  (`0`) and an overlap along a stretch (`1`) are told apart by the sets
  themselves.
-/

namespace Geospatial.DE9IM

open Geospatial

@[simp] theorem DimPatternChar.matches_T (S : Region) :
    DimPatternChar.T.Matches S ↔ S.Nonempty := by
  show DimValue.of S ≠ .F ↔ _
  rw [Ne, DimValue.of_eq_F_iff, Set.nonempty_iff_ne_empty]

@[simp] theorem DimPatternChar.matches_F (S : Region) : DimPatternChar.F.Matches S ↔ S = ∅ :=
  DimValue.of_eq_F_iff S

@[simp] theorem DimPatternChar.matches_any (S : Region) : DimPatternChar.any.Matches S ↔ True :=
  Iff.rfl

@[simp] theorem DimPatternChar.matches_d0 (S : Region) :
    DimPatternChar.d0.Matches S ↔ DimValue.of S = .d0 := Iff.rfl

@[simp] theorem DimPatternChar.matches_d1 (S : Region) :
    DimPatternChar.d1.Matches S ↔ DimValue.of S = .d1 := Iff.rfl

theorem matrix_swap (g h : Geometry) (s t : Stratum) : matrix g h s t = matrix h g t s := by
  unfold matrix
  rw [Geometry.cell_swap]

/-! ## Points -/

theorem point_value_right (p : Point2D) (t : Stratum) (ht : t ≠ .E) (g : Geometry)
    (s : Stratum) : matrix g (.point p) s t = .F ∨ matrix g (.point p) s t = .d0 := by
  rw [matrix_swap]
  exact point_cell_value p t ht g s

/-! ## Lines -/

theorem stratum_subset_carrier_of_ne_E (g : Geometry) {s : Stratum} (hs : s ≠ .E) :
    g.stratum s ⊆ g.carrier := by
  cases s with
  | I => exact g.stratum_I_subset
  | B => exact g.stratum_B_subset
  | E => exact absurd rfl hs

theorem interior_eq_empty_of_subset_line (l : LineString) {S : Region} (hS : S ⊆ l.carrier) :
    interior S = ∅ :=
  Set.eq_empty_of_subset_empty ((interior_mono hS).trans l.interior_carrier.subset)

theorem line_value_left_ne_d2 (l : LineString) (s : Stratum) (hs : s ≠ .E) (h : Geometry)
    (t : Stratum) : matrix (.line l) h s t ≠ .d2 :=
  Geometry.value_ne_d2_of_subset_line l
    (Set.inter_subset_left.trans (stratum_subset_carrier_of_ne_E (.line l) hs))

theorem line_value_right_ne_d2 (l : LineString) (t : Stratum) (ht : t ≠ .E) (g : Geometry)
    (s : Stratum) : matrix g (.line l) s t ≠ .d2 := by
  rw [matrix_swap]
  exact line_value_left_ne_d2 l t ht g s

/-! ## Two lines: `0` versus `1` -/

theorem line_value_eq_d1_iff (l : LineString) (s : Stratum) (hs : s ≠ .E) (h : Geometry)
    (t : Stratum) :
    matrix (.line l) h s t = .d1 ↔ HasArc (Geometry.cell s t (.line l) h) := by
  have hsub : Geometry.cell s t (.line l) h ⊆ l.carrier :=
    Set.inter_subset_left.trans (stratum_subset_carrier_of_ne_E (.line l) hs)
  constructor
  · intro h1
    have := DimValue.of_describes (Geometry.cell s t (.line l) h)
    rw [matrix] at h1
    rw [h1] at this
    exact this.2
  · intro harc
    exact DimValue.of_eq ⟨interior_eq_empty_of_subset_line l hsub, harc⟩

theorem line_value_eq_d0_iff (l : LineString) (s : Stratum) (hs : s ≠ .E) (h : Geometry)
    (t : Stratum) :
    matrix (.line l) h s t = .d0 ↔
      (Geometry.cell s t (.line l) h).Nonempty ∧ ¬ HasArc (Geometry.cell s t (.line l) h) := by
  have hsub : Geometry.cell s t (.line l) h ⊆ l.carrier :=
    Set.inter_subset_left.trans (stratum_subset_carrier_of_ne_E (.line l) hs)
  constructor
  · intro h0
    have := DimValue.of_describes (Geometry.cell s t (.line l) h)
    rw [matrix] at h0
    rw [h0] at this
    exact ⟨this.1, this.2.2⟩
  · rintro ⟨hne, harc⟩
    exact DimValue.of_eq ⟨hne, interior_eq_empty_of_subset_line l hsub, harc⟩

/-- For two lines, `II` is `0` or `1` whenever it is nonempty, and which one
is decided by whether the intersection contains an arc. -/
theorem line_line_II_cases (l m : LineString)
    (hne : (Geometry.cell .I .I (.line l) (.line m)).Nonempty) :
    (matrix (.line l) (.line m) .I .I = .d1 ∧ HasArc (Geometry.cell .I .I (.line l) (.line m))) ∨
    (matrix (.line l) (.line m) .I .I = .d0 ∧ ¬ HasArc (Geometry.cell .I .I (.line l) (.line m))) := by
  by_cases harc : HasArc (Geometry.cell .I .I (.line l) (.line m))
  · exact Or.inl ⟨(line_value_eq_d1_iff l .I (by decide) _ .I).mpr harc, harc⟩
  · exact Or.inr ⟨(line_value_eq_d0_iff l .I (by decide) _ .I).mpr ⟨hne, harc⟩, harc⟩

end Geospatial.DE9IM
