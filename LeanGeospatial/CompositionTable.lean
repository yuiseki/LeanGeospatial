import LeanGeospatial.CompositionTable.Complete
import LeanGeospatial.Homeomorph

/-!
# The RCC8 weak composition table

`compose_eq_table` identifies the weak composition `r ⋄ s`, defined in
`Composition.lean` by the existence of areas, with the computed `table r s`:

- `r ⋄ s ⊆ table r s` is `mem_table_of_mem_compose`, one argument for all 64
  cells, from nine laws proved from the set and topology definitions.
- `table r s ⊆ r ⋄ s` is `realizes_of_mem_table`: rectangle witnesses for
  representative cells, reused through the converse law and the identity
  laws for the rest.

The 64 cells are stated one by one in `CompositionTable/Cells.lean`.

## Complete spaces

Weak composition depends on the space, so "the table is right" is a property
of a space. `RCC8Complete α` says that in `α` every weak composition is the
table. Since the table is sound in every space, this is the same as every
entry of the table being realised in `α` (`rcc8Complete_iff_table_subset`).

- The plane is complete (`rcc8Complete_point2D`), which is `compose_eq_table`.
- Weak composition is a topological invariant (`compose_eq_of_homeomorph`),
  so completeness passes to every homeomorphic space
  (`RCC8Complete.of_homeomorph`); `ℝ × ℝ` is one.
- No discrete space is complete (`not_rcc8Complete_of_discrete`): its areas
  have no boundary, so no two are `EC` (`not_ec_of_discrete`), yet `EC` is in
  the table's `DC ⋄ DC`. `Bool` is an example.
-/

namespace Geospatial.RCC8

theorem mem_compose_iff_realizes {r s t : Relation} : t ∈ r ⋄ s ↔ Realizes r s t :=
  Iff.rfl

/-- The weak composition of two base relations is the computed table. -/
theorem compose_eq_table (r s : Relation) : r ⋄ s = ↑(table r s) := by
  ext t
  rw [Finset.mem_coe]
  exact ⟨mem_table_of_mem_compose, realizes_of_mem_table r s t⟩

end Geospatial.RCC8

namespace Geospatial

open RCC8

/-- The RCC8 composition table is complete for `α`: in `α`, every weak
composition is exactly the computed table. -/
def RCC8Complete (α : Type*) [TopologicalSpace α] : Prop :=
  ∀ r s, compose α r s = ↑(table r s)

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The table is sound everywhere, so completeness is the realisation of every
entry. -/
theorem rcc8Complete_iff_table_subset :
    RCC8Complete α ↔ ∀ r s, (↑(table r s) : Set Relation) ⊆ compose α r s :=
  ⟨fun h r s => (h r s).ge,
    fun h r s => Set.Subset.antisymm
      (fun _ ht => Finset.mem_coe.mpr (mem_table_of_mem_compose ht)) (h r s)⟩

/-- The table is complete for the plane. -/
theorem rcc8Complete_point2D : RCC8Complete Point2D :=
  compose_eq_table

/-- A homeomorphism carries a configuration realising `t ∈ r ⋄ s` to one in
the other space. -/
theorem RCC8.mem_compose_of_homeomorph (e : α ≃ₜ β) {r s t : Relation}
    (h : t ∈ compose α r s) : t ∈ compose β r s := by
  obtain ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩ := h
  exact ⟨A.map e, B.map e, C.map e, hA.image e, hB.image e, hC.image e,
    (Relation.holds_map_iff e A B r).mpr hr, (Relation.holds_map_iff e B C s).mpr hs,
    (Relation.holds_map_iff e A C t).mpr ht⟩

/-- Weak composition is a topological invariant: homeomorphic spaces have the
same weak compositions. -/
theorem RCC8.compose_eq_of_homeomorph (e : α ≃ₜ β) (r s : Relation) :
    compose α r s = compose β r s :=
  Set.ext fun _ => ⟨mem_compose_of_homeomorph e, mem_compose_of_homeomorph e.symm⟩

/-- Completeness passes along a homeomorphism. -/
theorem RCC8Complete.of_homeomorph (h : RCC8Complete α) (e : α ≃ₜ β) : RCC8Complete β :=
  fun r s => (compose_eq_of_homeomorph e r s).symm.trans (h r s)

section Discrete

variable [DiscreteTopology α]

/-- In a discrete space no two areas are externally connected: every set is
open, so an area has no boundary to touch along. -/
theorem RCC8.not_ec_of_discrete (A B : RegularClosedRegion α) : ¬ EC A B := by
  rintro ⟨⟨p, hpA, hpB⟩, h⟩
  have hp : p ∈ interior (A : Set α) ∩ interior (B : Set α) := by
    rw [(isOpen_discrete _).interior_eq, (isOpen_discrete _).interior_eq]
    exact ⟨hpA, hpB⟩
  rw [h] at hp
  exact hp

/-- In a discrete space no area is a tangential proper part of another. -/
theorem RCC8.not_tpp_of_discrete (A B : RegularClosedRegion α) : ¬ TPP A B := by
  rintro ⟨hW, -, hN⟩
  apply hN
  rw [(isOpen_discrete _).interior_eq]
  exact hW

variable (α) in
/-- The table is complete for no discrete space: `EC` is in the table's
`DC ⋄ DC`, but no two areas of a discrete space are `EC`. -/
theorem not_rcc8Complete_of_discrete : ¬ RCC8Complete α := by
  intro h
  have hmem : Relation.ec ∈ compose α .dc .dc := by
    rw [h, Finset.mem_coe]
    decide
  obtain ⟨A, _, C, _, _, _, _, _, hAC⟩ := hmem
  exact not_ec_of_discrete A C hAC

end Discrete

end Geospatial
