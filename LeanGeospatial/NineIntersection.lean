import LeanGeospatial.RegularClosed

/-!
# The nine intersections

Every set in a topological space `α` splits the space into three disjoint
parts: its interior, its boundary and its exterior. For two sets `A` and `B`
that gives nine intersections, one for each pair of parts, named `II`, `IB`,
`IE`, `BI`, `BB`, `BE`, `EI`, `EB`, `EE` (first letter for `A`, second for
`B`).

This file only asks whether each intersection is empty. Dimensions, matrices
and pattern strings are not introduced. The theorems at the end derive, from
the set definitions in `Region.lean` and `Topology.lean`, which emptiness
conditions each spatial relation amounts to.

The characterisations need closed regions. The one for `Within` needs areas
(`RegularClosedRegion α`) that are nonempty; the counterexamples in
`Examples/NineIntersection.lean` show both conditions are necessary.
-/

namespace Geospatial

variable {α : Type*} [TopologicalSpace α]

/-! ## Exterior and the three-part split -/

/-- The exterior of a region: the interior of its complement. -/
def exterior (A : Set α) : Set α := interior Aᶜ

variable {A B : Set α}

/-- A point is exterior exactly when it is not in the closure. -/
theorem exterior_eq_compl_closure (A : Set α) : exterior A = (closure A)ᶜ :=
  interior_compl

theorem isOpen_exterior (A : Set α) : IsOpen (exterior A) :=
  isOpen_interior

/-- For a closed region the exterior is just the complement. -/
theorem exterior_eq_of_isClosed (hA : IsClosed A) : exterior A = Aᶜ := by
  rw [exterior_eq_compl_closure, hA.closure_eq]

theorem interior_union_boundary_union_exterior (A : Set α) :
    interior A ∪ boundary A ∪ exterior A = Set.univ := by
  rw [boundary_eq, exterior_eq_compl_closure,
    Set.union_sdiff_cancel interior_subset_closure, Set.union_compl_self]

theorem interior_disjoint_exterior (A : Set α) :
    Geospatial.Disjoint (interior A) (exterior A) := by
  unfold Geospatial.Disjoint
  rw [exterior_eq_compl_closure, Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp, hp'⟩
  exact hp' (interior_subset_closure hp)

theorem boundary_disjoint_exterior (A : Set α) :
    Geospatial.Disjoint (boundary A) (exterior A) := by
  unfold Geospatial.Disjoint
  rw [boundary_eq, exterior_eq_compl_closure, Set.eq_empty_iff_forall_notMem]
  rintro p ⟨⟨hp, -⟩, hp'⟩
  exact hp' hp

/-- The three parts of a region. -/
inductive Stratum where
  /-- The interior. -/
  | I
  /-- The boundary. -/
  | B
  /-- The exterior. -/
  | E
  deriving DecidableEq

/-- The points of `A` in the given part. -/
def Stratum.set : Stratum → Set α → Set α
  | .I, A => interior A
  | .B, A => boundary A
  | .E, A => exterior A

/-- Every point of the space lies in exactly one part of `A`. -/
theorem existsUnique_stratum (A : Set α) (p : α) :
    ∃! s : Stratum, p ∈ s.set A := by
  have hcover : p ∈ interior A ∪ boundary A ∪ exterior A := by
    rw [interior_union_boundary_union_exterior]
    trivial
  have hIB := interior_disjoint_boundary A
  have hIE := interior_disjoint_exterior A
  have hBE := boundary_disjoint_exterior A
  unfold Geospatial.Disjoint at hIB hIE hBE
  have nIB : ¬ (p ∈ interior A ∧ p ∈ boundary A) := fun h => by
    have : p ∈ interior A ∩ boundary A := h
    rw [hIB] at this
    exact this
  have nIE : ¬ (p ∈ interior A ∧ p ∈ exterior A) := fun h => by
    have : p ∈ interior A ∩ exterior A := h
    rw [hIE] at this
    exact this
  have nBE : ¬ (p ∈ boundary A ∧ p ∈ exterior A) := fun h => by
    have : p ∈ boundary A ∩ exterior A := h
    rw [hBE] at this
    exact this
  rcases hcover with (h | h) | h
  · refine ⟨.I, h, ?_⟩
    rintro (_ | _ | _) ht
    · rfl
    · exact absurd ⟨h, ht⟩ nIB
    · exact absurd ⟨h, ht⟩ nIE
  · refine ⟨.B, h, ?_⟩
    rintro (_ | _ | _) ht
    · exact absurd ⟨ht, h⟩ nIB
    · rfl
    · exact absurd ⟨h, ht⟩ nBE
  · refine ⟨.E, h, ?_⟩
    rintro (_ | _ | _) ht
    · exact absurd ⟨ht, h⟩ nIE
    · exact absurd ⟨ht, h⟩ nBE
    · rfl

/-! ## The nine cells -/

/-- The points in part `s` of `A` and part `t` of `B`. -/
def cell (s t : Stratum) (A B : Set α) : Set α := s.set A ∩ t.set B

abbrev II (A B : Set α) : Set α := cell .I .I A B
abbrev IB (A B : Set α) : Set α := cell .I .B A B
abbrev IE (A B : Set α) : Set α := cell .I .E A B
abbrev BI (A B : Set α) : Set α := cell .B .I A B
abbrev BB (A B : Set α) : Set α := cell .B .B A B
abbrev BE (A B : Set α) : Set α := cell .B .E A B
abbrev EI (A B : Set α) : Set α := cell .E .I A B
abbrev EB (A B : Set α) : Set α := cell .E .B A B
abbrev EE (A B : Set α) : Set α := cell .E .E A B

/-- Swapping the regions swaps the roles of the two letters. -/
theorem cell_swap (s t : Stratum) (A B : Set α) : cell s t A B = cell t s B A :=
  Set.inter_comm _ _

/-- The nine cells cover the space. -/
theorem iUnion_cell (A B : Set α) : ⋃ (s : Stratum) (t : Stratum), cell s t A B = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro p
  obtain ⟨s, hs, -⟩ := existsUnique_stratum A p
  obtain ⟨t, ht, -⟩ := existsUnique_stratum B p
  exact Set.mem_iUnion₂.mpr ⟨s, t, hs, ht⟩

/-- Two different cells share no point. -/
theorem cell_disjoint {s t s' t' : Stratum} (h : (s, t) ≠ (s', t')) (A B : Set α) :
    Geospatial.Disjoint (cell s t A B) (cell s' t' A B) := by
  unfold Geospatial.Disjoint
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨⟨hs, ht⟩, ⟨hs', ht'⟩⟩
  obtain ⟨_, -, huA⟩ := existsUnique_stratum A p
  obtain ⟨_, -, huB⟩ := existsUnique_stratum B p
  exact h (by rw [huA s hs, huA s' hs', huB t ht, huB t' ht'])

/-! ## Closed regions -/

/-- For closed regions, what they share is made of the four cells that avoid
both exteriors. -/
theorem inter_eq_cells (hA : IsClosed A) (hB : IsClosed B) :
    A ∩ B = II A B ∪ IB A B ∪ BI A B ∪ BB A B := by
  have eA := interior_union_boundary_of_isClosed hA
  have eB := interior_union_boundary_of_isClosed hB
  ext p
  constructor
  · rintro ⟨hpA, hpB⟩
    rw [← eA] at hpA
    rw [← eB] at hpB
    rw [Set.mem_union] at hpA hpB
    simp only [cell, Stratum.set, Set.mem_union, Set.mem_inter_iff]
    tauto
  · intro hp
    simp only [cell, Stratum.set, Set.mem_union, Set.mem_inter_iff] at hp
    refine ⟨?_, ?_⟩
    · rw [← eA]
      rcases hp with ((h | h) | h) | h <;> simp [h.1]
    · rw [← eB]
      rcases hp with ((h | h) | h) | h <;> simp [h.2]

theorem intersects_iff_cells_of_isClosed (hA : IsClosed A) (hB : IsClosed B) :
    Intersects A B ↔
      (II A B).Nonempty ∨ (IB A B).Nonempty ∨ (BI A B).Nonempty ∨ (BB A B).Nonempty := by
  unfold Intersects
  rw [inter_eq_cells hA hB]
  simp only [Set.union_nonempty, or_assoc]

theorem disjoint_iff_cells_of_isClosed (hA : IsClosed A) (hB : IsClosed B) :
    Geospatial.Disjoint A B ↔
      II A B = ∅ ∧ IB A B = ∅ ∧ BI A B = ∅ ∧ BB A B = ∅ := by
  unfold Geospatial.Disjoint
  rw [inter_eq_cells hA hB]
  simp only [Set.union_empty_iff, and_assoc]

theorem touches_iff_cells_of_isClosed (hA : IsClosed A) (hB : IsClosed B) :
    Touches A B ↔
      II A B = ∅ ∧ ((IB A B).Nonempty ∨ (BI A B).Nonempty ∨ (BB A B).Nonempty) := by
  unfold Touches
  rw [intersects_iff_cells_of_isClosed hA hB]
  change _ ∧ II A B = ∅ ↔ _
  constructor
  · rintro ⟨h | h, hII⟩
    · rw [hII] at h
      exact absurd h Set.not_nonempty_empty
    · exact ⟨hII, h⟩
  · rintro ⟨hII, h⟩
    exact ⟨Or.inr h, hII⟩

/-- For closed regions, `A` lies within `B` exactly when no interior or
boundary point of `A` is exterior to `B`. -/
theorem within_iff_cells_of_isClosed (hA : IsClosed A) (hB : IsClosed B) :
    Within A B ↔ IE A B = ∅ ∧ BE A B = ∅ := by
  simp only [cell, Stratum.set, exterior_eq_of_isClosed hB, Set.eq_empty_iff_forall_notMem,
    Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · intro h
    refine ⟨fun p ⟨hp, hpB⟩ => hpB (h (interior_subset hp)), fun p ⟨hp, hpB⟩ => ?_⟩
    rw [boundary_eq, hA.closure_eq] at hp
    exact hpB (h hp.1)
  · rintro ⟨hIE, hBE⟩ p hp
    by_contra hpB
    rw [← interior_union_boundary_of_isClosed hA] at hp
    rcases hp with hp | hp
    · exact hIE p ⟨hp, hpB⟩
    · exact hBE p ⟨hp, hpB⟩

/-! ## Areas -/

namespace RegularClosedRegion

variable (A B : RegularClosedRegion α)

theorem intersects_iff_cells :
    Intersects (A : Set α) B ↔
      (II (A : Set α) B).Nonempty ∨ (IB (A : Set α) B).Nonempty ∨ (BI (A : Set α) B).Nonempty ∨ (BB (A : Set α) B).Nonempty :=
  intersects_iff_cells_of_isClosed A.isClosed B.isClosed

/-- Two areas are disjoint exactly when the four cells avoiding both exteriors
are empty. -/
theorem disjoint_iff_cells :
    Geospatial.Disjoint (A : Set α) B ↔
      II (A : Set α) B = ∅ ∧ IB (A : Set α) B = ∅ ∧ BI (A : Set α) B = ∅ ∧ BB (A : Set α) B = ∅ :=
  disjoint_iff_cells_of_isClosed A.isClosed B.isClosed

/-- Two areas touch exactly when their interiors miss each other but some
interior or boundary point of one is on the boundary of the other. -/
theorem touches_iff_cells :
    Touches (A : Set α) B ↔
      II (A : Set α) B = ∅ ∧ ((IB (A : Set α) B).Nonempty ∨ (BI (A : Set α) B).Nonempty ∨ (BB (A : Set α) B).Nonempty) :=
  touches_iff_cells_of_isClosed A.isClosed B.isClosed

/-- A nonempty area lies within another exactly when their interiors meet and
no interior or boundary point of the first is exterior to the second. -/
theorem within_iff_cells (hA : (A : Set α).Nonempty) :
    Within (A : Set α) B ↔ (II (A : Set α) B).Nonempty ∧ IE (A : Set α) B = ∅ ∧ BE (A : Set α) B = ∅ := by
  rw [within_iff_cells_of_isClosed A.isClosed B.isClosed]
  constructor
  · rintro ⟨hIE, hBE⟩
    refine ⟨?_, hIE, hBE⟩
    obtain ⟨p, hp⟩ := (A.nonempty_iff_interior_nonempty).mp hA
    have hW : Within (A : Set α) B :=
      (within_iff_cells_of_isClosed A.isClosed B.isClosed).mpr ⟨hIE, hBE⟩
    exact ⟨p, hp, interior_mono hW hp⟩
  · rintro ⟨-, hIE, hBE⟩
    exact ⟨hIE, hBE⟩

/-- The same for `Contains`, read through `cell_swap`. -/
theorem contains_iff_cells (hB : (B : Set α).Nonempty) :
    Contains (A : Set α) B ↔ (II (A : Set α) B).Nonempty ∧ EI (A : Set α) B = ∅ ∧ EB (A : Set α) B = ∅ := by
  rw [contains_iff_within, B.within_iff_cells A hB]
  simp only [II, IE, BE, EI, EB, cell_swap _ _ (B : Set α)]

end RegularClosedRegion

end Geospatial
