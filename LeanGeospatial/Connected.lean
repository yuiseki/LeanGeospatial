import LeanGeospatial.NineIntersection
import Mathlib.Topology.Connected.Clopen

/-!
# Connected spaces

In a connected space the only sets that are both open and closed are `∅` and
the whole space. Consequences used for DE-9IM:

- an area other than the whole space has a nonempty boundary;
- a closed set other than the whole space has a nonempty exterior;
- two disjoint nonempty closed sets never cover the space.

The theorems ask for `PreconnectedSpace α`. `Point2D`, Mathlib's Euclidean
plane, is one (every real normed space is path-connected, and Mathlib provides
the instance). A discrete space with two points is not, and there an area can
be clopen, with no boundary at all.
-/

namespace Geospatial

variable {α : Type*} [TopologicalSpace α]

/-- The plane is connected. Mathlib already knows this: a real normed space is
path-connected. -/
example : PreconnectedSpace Point2D := inferInstance

theorem boundary_subset_of_isClosed {A : Set α} (hA : IsClosed A) : boundary A ⊆ A := by
  rw [boundary_eq, hA.closure_eq]
  exact Set.sdiff_subset

/-- A nonempty closed set with empty boundary is the whole space. -/
theorem eq_univ_of_boundary_eq_empty [PreconnectedSpace α] {A : Set α} (hA : IsClosed A)
    (hne : A.Nonempty) (h : boundary A = ∅) : A = Set.univ := by
  have hopen : IsOpen A := by
    have : interior A = A := by
      apply Set.Subset.antisymm interior_subset
      intro p hp
      by_contra hpi
      have : p ∈ boundary A := by
        rw [boundary_eq, hA.closure_eq]
        exact ⟨hp, hpi⟩
      rw [h] at this
      exact this
    rw [← this]
    exact isOpen_interior
  rcases isClopen_iff.mp ⟨hA, hopen⟩ with h' | h'
  · exact absurd h' hne.ne_empty
  · exact h'

/-- A nonempty closed set other than the whole space has boundary points. -/
theorem boundary_nonempty [PreconnectedSpace α] {A : Set α} (hA : IsClosed A) (hne : A.Nonempty)
    (hU : A ≠ Set.univ) : (boundary A).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr fun h => hU (eq_univ_of_boundary_eq_empty hA hne h)

/-- A closed set has exterior points exactly when it is not the whole space. -/
theorem exterior_nonempty_iff {A : Set α} (hA : IsClosed A) :
    (exterior A).Nonempty ↔ A ≠ Set.univ := by
  rw [exterior_eq_of_isClosed hA, Set.nonempty_compl]

/-- Two disjoint nonempty closed sets leave part of the space uncovered. -/
theorem union_ne_univ [PreconnectedSpace α] {A B : Set α} (hA : IsClosed A) (hB : IsClosed B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : A ∩ B = ∅) : A ∪ B ≠ Set.univ := by
  intro hU
  have hAc : A = Bᶜ := by
    ext p
    constructor
    · intro hpA hpB
      have : p ∈ A ∩ B := ⟨hpA, hpB⟩
      rw [hAB] at this
      exact this
    · intro hpB
      have : p ∈ A ∪ B := by rw [hU]; trivial
      exact this.resolve_right hpB
  have hopen : IsOpen A := hAc ▸ hB.isOpen_compl
  rcases isClopen_iff.mp ⟨hA, hopen⟩ with h | h
  · exact hAne.ne_empty h
  · obtain ⟨p, hp⟩ := hBne
    have : p ∈ A := by rw [h]; trivial
    have : p ∈ A ∩ B := ⟨this, hp⟩
    rw [hAB] at this
    exact this

end Geospatial
