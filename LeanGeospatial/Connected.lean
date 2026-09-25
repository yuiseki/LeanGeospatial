import LeanGeospatial.NineIntersection
import Mathlib.Topology.Connected.Clopen

/-!
# The plane is connected

`Point2D` is homeomorphic to `ℝ × ℝ`, which is connected, so the only sets
that are both open and closed are `∅` and the whole plane. Consequences used
for DE-9IM:

- an area other than the whole plane has a nonempty boundary;
- a closed region other than the whole plane has a nonempty exterior;
- two disjoint nonempty closed regions never cover the plane.
-/

namespace Geospatial

instance : PreconnectedSpace Point2D :=
  ⟨by
    have := (isPreconnected_univ (α := ℝ × ℝ)).image Point2D.homeomorphProd.symm
      Point2D.homeomorphProd.symm.continuous.continuousOn
    rwa [Set.image_univ_of_surjective Point2D.homeomorphProd.symm.surjective] at this⟩

theorem boundary_subset_of_isClosed {A : Region} (hA : IsClosed A) : boundary A ⊆ A := by
  rw [boundary_eq, hA.closure_eq]
  exact Set.diff_subset

/-- A nonempty closed region with empty boundary is the whole plane. -/
theorem eq_univ_of_boundary_eq_empty {A : Region} (hA : IsClosed A) (hne : A.Nonempty)
    (h : boundary A = ∅) : A = Set.univ := by
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

/-- A nonempty closed region other than the whole plane has boundary points. -/
theorem boundary_nonempty {A : Region} (hA : IsClosed A) (hne : A.Nonempty)
    (hU : A ≠ Set.univ) : (boundary A).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr fun h => hU (eq_univ_of_boundary_eq_empty hA hne h)

/-- A closed region has exterior points exactly when it is not the plane. -/
theorem exterior_nonempty_iff {A : Region} (hA : IsClosed A) :
    (exterior A).Nonempty ↔ A ≠ Set.univ := by
  rw [exterior_eq_of_isClosed hA, Set.nonempty_compl]

/-- Two disjoint nonempty closed regions leave part of the plane uncovered. -/
theorem union_ne_univ {A B : Region} (hA : IsClosed A) (hB : IsClosed B)
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
