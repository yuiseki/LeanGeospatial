import LeanGeospatial.GeoSPARQL.Spec
import LeanGeospatial.Connected

/-!
# GeoSPARQL 1.1 on areas: patterns versus the semantics

For nonempty areas (`RegularClosedRegion`), this file compares the DE-9IM
patterns and equivalences transcribed in `GeoSPARQL/Spec.lean` with the
relations LeanGeospatial defines from sets and topology.

## Table 8 (RCC8 patterns)

- `holds_of_rcc8Pattern`: for all eight relations, matching the pattern
  implies the relation.
- The converse holds for `DC` (`rcc8Pattern_of_dc`), and for `EQ`, `NTPP`,
  `NTPPi` when the areas are not the whole plane (`rcc8Pattern_of_eq`,
  `rcc8Pattern_of_ntpp`, `rcc8Pattern_of_ntppi`).
- `GeoSPARQL/Counterexamples.lean` shows every other converse fails.

## Table 5 (Simple Features and RCC8)

`table5_row` proves five rows. The `within` and `contains` rows fail: they
leave out `EQ` (`table5_within_row_fails`), while Table 2's own patterns
include it (`sf_within_pattern`).
-/

namespace Geospatial.GeoSPARQL

open Geospatial Geospatial.RCC8 Geospatial.DE9IM

variable (A B : RegularClosedRegion)

/-! ## Cell facts for areas -/

theorem within_swap_iff :
    Within (B : Region) A ↔ EI (A : Region) B = ∅ ∧ EB (A : Region) B = ∅ := by
  rw [within_iff_cells_of_isClosed B.isClosed A.isClosed]
  simp only [IE, BE, EI, EB, cell_swap _ _ (B : Region)]

theorem not_within_swap_iff : ¬ Within (B : Region) A ↔ (EI (A : Region) B).Nonempty := by
  rw [not_within_iff_IE_nonempty B A]
  simp only [IE, EI, cell_swap _ _ (B : Region)]

theorem within_interior_iff_cells :
    Within (A : Region) (interior (B : Region)) ↔
      IE (A : Region) B = ∅ ∧ BE (A : Region) B = ∅ ∧ IB (A : Region) B = ∅ ∧
        BB (A : Region) B = ∅ := by
  have hAc := A.isClosed
  have hBc := B.isClosed
  constructor
  · intro h
    have hW : Within (A : Region) B := within_trans h interior_subset
    obtain ⟨h₁, h₂⟩ := (within_iff_cells_of_isClosed hAc hBc).mp hW
    refine ⟨h₁, h₂, ?_, ?_⟩ <;> rw [Set.eq_empty_iff_forall_not_mem]
    · rintro p ⟨hpA, hpB⟩
      exact hpB.2 (h (interior_subset hpA))
    · rintro p ⟨hpA, hpB⟩
      exact hpB.2 (h (boundary_subset_of_isClosed hAc hpA))
  · rintro ⟨h₁, h₂, h₃, h₄⟩ p hp
    have hpB : p ∈ (B : Region) := (within_iff_cells_of_isClosed hAc hBc).mpr ⟨h₁, h₂⟩ hp
    by_contra hpi
    have hpbd : p ∈ boundary (B : Region) := by
      rw [boundary_eq, hBc.closure_eq]
      exact ⟨hpB, hpi⟩
    rw [← interior_union_boundary_of_isClosed hAc] at hp
    rcases hp with hp | hp
    · have : p ∈ IB (A : Region) B := ⟨hp, hpbd⟩
      rw [h₃] at this
      exact this
    · have : p ∈ BB (A : Region) B := ⟨hp, hpbd⟩
      rw [h₄] at this
      exact this

/-! ## Table 8 patterns as records -/

theorem rcc8Pattern_eq_eq : rcc8Pattern .eq = ⟨.T, .F, .F, .F, .T, .F, .F, .F, .T⟩ := by decide
theorem rcc8Pattern_dc_eq : rcc8Pattern .dc = ⟨.F, .F, .T, .F, .F, .T, .T, .T, .T⟩ := by decide
theorem rcc8Pattern_ec_eq : rcc8Pattern .ec = ⟨.F, .F, .T, .F, .T, .T, .T, .T, .T⟩ := by decide
theorem rcc8Pattern_po_eq : rcc8Pattern .po = ⟨.T, .T, .T, .T, .T, .T, .T, .T, .T⟩ := by decide
theorem rcc8Pattern_tpp_eq : rcc8Pattern .tpp = ⟨.T, .F, .F, .T, .T, .F, .T, .T, .T⟩ := by decide
theorem rcc8Pattern_ntpp_eq : rcc8Pattern .ntpp = ⟨.T, .F, .F, .T, .F, .F, .T, .T, .T⟩ := by
  decide

/-! ## Pattern implies relation, for all eight -/

section Sound

variable {A B}

theorem eq_of_rcc8Pattern (h : (rcc8Pattern .eq).Matches A B) : EQ A B := by
  simp only [rcc8Pattern_eq_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
    at h
  obtain ⟨-, -, hIE, -, -, hBE, hEI, hEB, -⟩ := h
  exact within_antisymm ((within_iff_cells_of_isClosed A.isClosed B.isClosed).mpr ⟨hIE, hBE⟩)
    ((within_swap_iff A B).mpr ⟨hEI, hEB⟩)

theorem dc_of_rcc8Pattern (h : (rcc8Pattern .dc).Matches A B) : DC A B := by
  simp only [rcc8Pattern_dc_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
    at h
  obtain ⟨hII, hIB, -, hBI, hBB, -⟩ := h
  exact (A.disjoint_iff_cells B).mpr ⟨hII, hIB, hBI, hBB⟩

theorem ec_of_rcc8Pattern (h : (rcc8Pattern .ec).Matches A B) : EC A B := by
  simp only [rcc8Pattern_ec_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
    at h
  obtain ⟨hII, -, -, -, hBB, -⟩ := h
  exact (A.touches_iff_cells B).mpr ⟨hII, Or.inr (Or.inr hBB)⟩

theorem po_of_rcc8Pattern (h : (rcc8Pattern .po).Matches A B) : PO A B := by
  simp only [rcc8Pattern_po_eq, Pattern.Matches, PatternChar.matches_T] at h
  obtain ⟨hII, -, hIE, -, -, -, hEI, -⟩ := h
  exact (po_iff_cells A B).mpr ⟨hII, hIE, hEI⟩

theorem tpp_of_rcc8Pattern (h : (rcc8Pattern .tpp).Matches A B) : TPP A B := by
  simp only [rcc8Pattern_tpp_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
    at h
  obtain ⟨-, -, hIE, -, hBB, hBE, hEI, -⟩ := h
  refine ⟨(within_iff_cells_of_isClosed A.isClosed B.isClosed).mpr ⟨hIE, hBE⟩, fun hAB => ?_,
    fun hN => hBB.ne_empty ((within_interior_iff_cells A B).mp hN).2.2.2⟩
  exact (not_within_swap_iff A B).mpr hEI (by rw [hAB]; exact within_refl _)

theorem ntpp_of_rcc8Pattern (h : (rcc8Pattern .ntpp).Matches A B) : NTPP A B := by
  simp only [rcc8Pattern_ntpp_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
    at h
  obtain ⟨-, hIB, hIE, -, hBB, hBE, hEI, -⟩ := h
  refine ⟨(within_interior_iff_cells A B).mpr ⟨hIE, hBE, hIB, hBB⟩, fun hAB => ?_⟩
  exact (not_within_swap_iff A B).mpr hEI (by rw [hAB]; exact within_refl _)

theorem tppi_of_rcc8Pattern (h : (rcc8Pattern .tppi).Matches A B) : TPPi A B := by
  rw [rcc8Pattern_tppi, Pattern.matches_transpose] at h
  exact tpp_of_rcc8Pattern h

theorem ntppi_of_rcc8Pattern (h : (rcc8Pattern .ntppi).Matches A B) : NTPPi A B := by
  rw [rcc8Pattern_ntppi, Pattern.matches_transpose] at h
  exact ntpp_of_rcc8Pattern h

/-- For every RCC8 relation, matching its Table 8 pattern implies the
relation. -/
theorem holds_of_rcc8Pattern (r : Relation) (h : (rcc8Pattern r).Matches A B) :
    r.holds A B := by
  cases r
  · exact dc_of_rcc8Pattern h
  · exact ec_of_rcc8Pattern h
  · exact po_of_rcc8Pattern h
  · exact eq_of_rcc8Pattern h
  · exact tpp_of_rcc8Pattern h
  · exact ntpp_of_rcc8Pattern h
  · exact tppi_of_rcc8Pattern h
  · exact ntppi_of_rcc8Pattern h

end Sound

/-! ## Relation implies pattern: the cases that hold -/

section Complete

variable {A B}

/-- A point of a cell, packaged for the nonempty cases. -/
private theorem cell_mem {s t : Stratum} {p : Point2D} (hs : p ∈ s.set (A : Region))
    (ht : p ∈ t.set (B : Region)) : (cell s t (A : Region) B).Nonempty := ⟨p, hs, ht⟩

theorem rcc8Pattern_of_dc (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty)
    (h : DC A B) : (rcc8Pattern .dc).Matches A B := by
  obtain ⟨hII, hIB, hBI, hBB⟩ := (A.disjoint_iff_cells B).mp h
  have hAB : (A : Region) ∩ B = ∅ := h
  have notB : ∀ {p}, p ∈ (A : Region) → p ∉ (B : Region) := fun hpA hpB => by
    have : _ ∈ (A : Region) ∩ B := ⟨hpA, hpB⟩
    rw [hAB] at this
    exact this
  have notA : ∀ {p}, p ∈ (B : Region) → p ∉ (A : Region) := fun hpB hpA => notB hpA hpB
  have eA := exterior_eq_of_isClosed A.isClosed
  have eB := exterior_eq_of_isClosed B.isClosed
  have hUA : (A : Region) ≠ Set.univ := fun hU => by
    obtain ⟨p, hp⟩ := hB
    exact notA hp (hU ▸ trivial)
  have hUB : (B : Region) ≠ Set.univ := fun hU => by
    obtain ⟨p, hp⟩ := hA
    exact notB hp (hU ▸ trivial)
  obtain ⟨a, ha⟩ := (A.nonempty_iff_interior_nonempty).mp hA
  obtain ⟨b, hb⟩ := (B.nonempty_iff_interior_nonempty).mp hB
  obtain ⟨a', ha'⟩ := boundary_nonempty A.isClosed hA hUA
  obtain ⟨b', hb'⟩ := boundary_nonempty B.isClosed hB hUB
  obtain ⟨e, he⟩ := Set.nonempty_compl.mpr
    (union_ne_univ A.isClosed B.isClosed hA hB hAB)
  simp only [rcc8Pattern_dc_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
  refine ⟨hII, hIB, ?_, hBI, hBB, ?_, ?_, ?_, ?_⟩
  · exact cell_mem (s := .I) (t := .E) ha (by
      show a ∈ exterior (B : Region)
      rw [eB]; exact notB (interior_subset ha))
  · exact cell_mem (s := .B) (t := .E) ha' (by
      show a' ∈ exterior (B : Region)
      rw [eB]; exact notB (boundary_subset_of_isClosed A.isClosed ha'))
  · exact cell_mem (s := .E) (t := .I) (by
      show b ∈ exterior (A : Region)
      rw [eA]; exact notA (interior_subset hb)) hb
  · exact cell_mem (s := .E) (t := .B) (by
      show b' ∈ exterior (A : Region)
      rw [eA]; exact notA (boundary_subset_of_isClosed B.isClosed hb')) hb'
  · rw [Set.mem_compl_iff, Set.mem_union, not_or] at he
    exact cell_mem (s := .E) (t := .E) (by show e ∈ exterior (A : Region); rw [eA]; exact he.1)
      (by show e ∈ exterior (B : Region); rw [eB]; exact he.2)

theorem rcc8Pattern_of_eq (hA : (A : Region).Nonempty) (hU : (A : Region) ≠ Set.univ)
    (h : EQ A B) : (rcc8Pattern .eq).Matches A B := by
  obtain rfl : A = B := SetLike.coe_injective h
  obtain ⟨a, ha⟩ := (A.nonempty_iff_interior_nonempty).mp hA
  obtain ⟨a', ha'⟩ := boundary_nonempty A.isClosed hA hU
  obtain ⟨e, he⟩ := (exterior_nonempty_iff A.isClosed).mpr hU
  have dIB := interior_disjoint_boundary (A : Region)
  have dIE := interior_disjoint_exterior (A : Region)
  have dBE := boundary_disjoint_exterior (A : Region)
  unfold Geospatial.Disjoint at dIB dIE dBE
  simp only [rcc8Pattern_eq_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F,
    II, IB, IE, BI, BB, BE, EI, EB, EE, cell, Stratum.set]
  refine ⟨⟨a, ha, ha⟩, dIB, dIE, ?_, ⟨a', ha', ha'⟩, dBE, ?_, ?_, ⟨e, he, he⟩⟩
  · rw [Set.inter_comm]; exact dIB
  · rw [Set.inter_comm]; exact dIE
  · rw [Set.inter_comm]; exact dBE

theorem rcc8Pattern_of_ntpp (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty)
    (hU : (B : Region) ≠ Set.univ) (h : NTPP A B) : (rcc8Pattern .ntpp).Matches A B := by
  obtain ⟨hN, hne⟩ := h
  obtain ⟨hIE, hBE, hIB, hBB⟩ := (within_interior_iff_cells A B).mp hN
  have hW : Within (A : Region) B := within_trans hN interior_subset
  have hII := ((A.within_iff_cells B hA).mp hW).1
  have hnotBA : ¬ Within (B : Region) A := fun h => hne (within_antisymm hW h)
  have hEI := (not_within_swap_iff A B).mp hnotBA
  have hUA : (A : Region) ≠ Set.univ := fun h => hU (Set.eq_univ_of_univ_subset (h ▸ hW))
  obtain ⟨a', ha'⟩ := boundary_nonempty A.isClosed hA hUA
  obtain ⟨b', hb'⟩ := boundary_nonempty B.isClosed hB hU
  obtain ⟨e, he⟩ := (exterior_nonempty_iff B.isClosed).mpr hU
  have eA := exterior_eq_of_isClosed A.isClosed
  have eB := exterior_eq_of_isClosed B.isClosed
  simp only [rcc8Pattern_ntpp_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
  refine ⟨hII, hIB, hIE, ?_, hBB, hBE, hEI, ?_, ?_⟩
  · exact cell_mem (s := .B) (t := .I) ha' (hN (boundary_subset_of_isClosed A.isClosed ha'))
  · refine cell_mem (s := .E) (t := .B) ?_ hb'
    show b' ∈ exterior (A : Region)
    rw [eA]
    exact fun hbA => hb'.2 (hN hbA)
  · refine cell_mem (s := .E) (t := .E) ?_ he
    show e ∈ exterior (A : Region)
    have he' : e ∉ (B : Region) := by rw [eB] at he; exact he
    rw [eA]
    exact fun heA => he' (hW heA)

theorem rcc8Pattern_of_ntppi (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty)
    (hU : (A : Region) ≠ Set.univ) (h : NTPPi A B) : (rcc8Pattern .ntppi).Matches A B := by
  rw [rcc8Pattern_ntppi, Pattern.matches_transpose]
  exact rcc8Pattern_of_ntpp hB hA hU h

end Complete

/-! ## Table 5 and the Simple Features patterns -/

/-- Two regions overlap: their interiors meet and each has points outside the
other. -/
def Overlaps (A B : Region) : Prop :=
  (interior A ∩ interior B).Nonempty ∧ (A \ B).Nonempty ∧ (B \ A).Nonempty

/-- The Simple Features relation named in Table 5, as LeanGeospatial defines
it from sets. -/
def SF.pred : SF → Region → Region → Prop
  | .equals, A, B => A = B
  | .disjoint, A, B => Geospatial.Disjoint A B
  | .intersects, A, B => Intersects A B
  | .touches, A, B => Touches A B
  | .within, A, B => Within A B
  | .contains, A, B => Contains A B
  | .overlaps, A, B => Overlaps A B

/-- Some relation of the set holds. -/
def HoldsAny (S : Finset Relation) (A B : RegularClosedRegion) : Prop := ∃ r ∈ S, r.holds A B

section Table5

variable {A B}

theorem overlaps_iff_po : Overlaps (A : Region) B ↔ PO A B := by
  simp only [Overlaps, PO, Set.diff_nonempty]
  rfl

theorem within_iff_rcc8 : Within (A : Region) B ↔ TPP A B ∨ NTPP A B ∨ EQ A B := by
  constructor
  · intro h
    by_cases hE : (A : Region) = B
    · exact Or.inr (Or.inr hE)
    by_cases hN : Within (A : Region) (interior (B : Region))
    · exact Or.inr (Or.inl ⟨hN, hE⟩)
    · exact Or.inl ⟨h, hE, hN⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | h)
    · exact h
    · exact within_trans h interior_subset
    · rw [show (A : Region) = B from h]
      exact within_refl _

theorem contains_iff_rcc8 : Contains (A : Region) B ↔ TPPi A B ∨ NTPPi A B ∨ EQ A B := by
  rw [contains_iff_within, within_iff_rcc8]
  simp only [TPPi, NTPPi, EQ, eq_comm]

private theorem holdsAny_insert {r : Relation} {S : Finset Relation} :
    HoldsAny (insert r S) A B ↔ r.holds A B ∨ HoldsAny S A B := by
  simp only [HoldsAny, Finset.mem_insert]
  constructor
  · rintro ⟨s, rfl | hs, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, h⟩
  · rintro (h | ⟨s, hs, h⟩)
    · exact ⟨r, Or.inl rfl, h⟩
    · exact ⟨s, Or.inr hs, h⟩

private theorem holdsAny_singleton {r : Relation} : HoldsAny {r} A B ↔ r.holds A B := by
  simp [HoldsAny]

/-- The five rows of Table 5 that hold for nonempty areas. -/
theorem table5_row (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty) (sf : SF)
    (hsf : sf ≠ .within ∧ sf ≠ .contains) :
    sf.pred A B ↔ HoldsAny (table5 sf) A B := by
  cases sf with
  | equals => simp only [SF.pred, table5, holdsAny_singleton]; rfl
  | disjoint => simp only [SF.pred, table5, holdsAny_singleton]; rfl
  | touches => simp only [SF.pred, table5, holdsAny_singleton]; rfl
  | overlaps => simp only [SF.pred, table5, holdsAny_singleton]; exact overlaps_iff_po
  | within => exact absurd rfl hsf.1
  | contains => exact absurd rfl hsf.2
  | intersects =>
    simp only [SF.pred]
    constructor
    · intro h
      obtain ⟨t, ht⟩ := exists_relation A B hA hB
      refine ⟨t, ?_, ht⟩
      cases t
      · exact absurd (disjoint_iff_not_intersects.mp ht) (not_not.mpr h)
      all_goals decide
    · rintro ⟨t, ht, h⟩
      by_contra hI
      have hdc : Relation.dc.holds A B := disjoint_iff_not_intersects.mpr hI
      rw [relation_unique A B hA hB h hdc] at ht
      exact absurd ht (by decide)

/-- The `within` row of Table 5 is off by `EQ`: it holds with `EQ` added. -/
theorem table5_within_with_eq :
    Within (A : Region) B ↔ HoldsAny (insert .eq (table5 .within)) A B := by
  rw [within_iff_rcc8]
  simp only [table5, holdsAny_insert, holdsAny_singleton]
  simp only [Relation.holds]
  tauto

theorem table5_contains_with_eq :
    Contains (A : Region) B ↔ HoldsAny (insert .eq (table5 .contains)) A B := by
  rw [contains_iff_rcc8]
  simp only [table5, holdsAny_insert, holdsAny_singleton]
  simp only [Relation.holds]
  tauto

end Table5

/-- The `within` row of Table 5, as printed, fails: an area lies within
itself but is neither `TPP` nor `NTPP` of itself. -/
theorem table5_within_row_fails :
    ¬ ∀ A B : RegularClosedRegion, (A : Region).Nonempty → (B : Region).Nonempty →
      (Within (A : Region) B ↔ HoldsAny (table5 .within) A B) := by
  intro h
  let A := RCC8.univ
  have hA : (A : Region).Nonempty := ⟨⟨0, 0⟩, trivial⟩
  obtain ⟨r, hr, hholds⟩ := (h A A hA hA).mp (within_refl _)
  have heq : Relation.eq.holds A A := rfl
  have := relation_unique A A hA hA hholds heq
  subst this
  exact absurd hr (by decide)

theorem table5_contains_row_fails :
    ¬ ∀ A B : RegularClosedRegion, (A : Region).Nonempty → (B : Region).Nonempty →
      (Contains (A : Region) B ↔ HoldsAny (table5 .contains) A B) := by
  intro h
  let A := RCC8.univ
  have hA : (A : Region).Nonempty := ⟨⟨0, 0⟩, trivial⟩
  obtain ⟨r, hr, hholds⟩ := (h A A hA hA).mp (contains_refl _)
  have heq : Relation.eq.holds A A := rfl
  have := relation_unique A A hA hA hholds heq
  subst this
  exact absurd hr (by decide)

/-! ## Simple Features patterns (Tables 2 and 6) -/

/-- The rows of a multi-row pattern from a table; `[]` if ill-formed (only
Table 2's `disjoint` is, see `table2_disjoint_malformed`). -/
def sfPatterns (tbl : SF → List String) (sf : SF) : List Pattern :=
  (parseAll (tbl sf)).getD []

section SFPatterns

variable {A B}

theorem sf_disjoint_pattern :
    AnyOf (sfPatterns table6 .disjoint) A B ↔ DC A B := by
  rw [show sfPatterns table6 .disjoint = [⟨.F, .F, .any, .F, .F, .any, .any, .any, .any⟩]
    by decide]
  simp only [AnyOf, List.mem_singleton, exists_eq_left, Pattern.Matches,
    PatternChar.matches_F, PatternChar.matches_any, and_true, true_and]
  exact (A.disjoint_iff_cells B).symm

theorem sf_intersects_pattern :
    AnyOf (sfPatterns table2 .intersects) A B ↔ ¬ DC A B := by
  rw [show sfPatterns table2 .intersects =
      [⟨.T, .any, .any, .any, .any, .any, .any, .any, .any⟩,
       ⟨.any, .T, .any, .any, .any, .any, .any, .any, .any⟩,
       ⟨.any, .any, .any, .T, .any, .any, .any, .any, .any⟩,
       ⟨.any, .any, .any, .any, .T, .any, .any, .any, .any⟩] by decide]
  simp only [AnyOf, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, Pattern.Matches, PatternChar.matches_T,
    PatternChar.matches_any, and_true, true_and]
  rw [DC, disjoint_iff_not_intersects, not_not, A.intersects_iff_cells B]

theorem sf_touches_pattern :
    AnyOf (sfPatterns table2 .touches) A B ↔ EC A B := by
  rw [show sfPatterns table2 .touches =
      [⟨.F, .T, .any, .any, .any, .any, .any, .any, .any⟩,
       ⟨.F, .any, .any, .T, .any, .any, .any, .any, .any⟩,
       ⟨.F, .any, .any, .any, .T, .any, .any, .any, .any⟩] by decide]
  simp only [AnyOf, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, Pattern.Matches, PatternChar.matches_T,
    PatternChar.matches_F, PatternChar.matches_any, and_true, true_and]
  rw [EC, A.touches_iff_cells B]
  tauto

/-- Table 6's `sfIntersects` rows are the touches rows, so they describe
`EC`, not `¬ DC`. -/
theorem sf_intersects_table6_pattern :
    AnyOf (sfPatterns table6 .intersects) A B ↔ EC A B := by
  rw [show sfPatterns table6 .intersects = sfPatterns table2 .touches by decide]
  exact sf_touches_pattern

theorem sf_within_pattern (hA : (A : Region).Nonempty) :
    AnyOf (sfPatterns table2 .within) A B ↔ TPP A B ∨ NTPP A B ∨ EQ A B := by
  rw [show sfPatterns table2 .within = [⟨.T, .any, .F, .any, .any, .F, .any, .any, .any⟩]
    by decide]
  simp only [AnyOf, List.mem_singleton, exists_eq_left, Pattern.Matches, PatternChar.matches_T,
    PatternChar.matches_F, PatternChar.matches_any, and_true, true_and]
  rw [← within_iff_rcc8, A.within_iff_cells B hA]

theorem sf_contains_pattern (hB : (B : Region).Nonempty) :
    AnyOf (sfPatterns table2 .contains) A B ↔ TPPi A B ∨ NTPPi A B ∨ EQ A B := by
  rw [show sfPatterns table2 .contains = [⟨.T, .any, .any, .any, .any, .any, .F, .F, .any⟩]
    by decide]
  simp only [AnyOf, List.mem_singleton, exists_eq_left, Pattern.Matches, PatternChar.matches_T,
    PatternChar.matches_F, PatternChar.matches_any, and_true, true_and]
  rw [← contains_iff_rcc8, A.contains_iff_cells B hB]

theorem sf_overlaps_pattern :
    AnyOf (sfPatterns table2 .overlaps) A B ↔ PO A B := by
  rw [show sfPatterns table2 .overlaps = [⟨.T, .any, .T, .any, .any, .any, .T, .any, .any⟩]
    by decide]
  simp only [AnyOf, List.mem_singleton, exists_eq_left, Pattern.Matches, PatternChar.matches_T,
    PatternChar.matches_any, and_true, true_and]
  exact (po_iff_cells A B).symm

/-- Table 2's `equals` pattern is Table 8's `EQ` pattern. -/
theorem sf_equals_pattern_eq : sfPatterns table2 .equals = [rcc8Pattern .eq] := by decide

end SFPatterns

end Geospatial.GeoSPARQL
