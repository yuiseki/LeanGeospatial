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

- The plane is complete (`rcc8Complete_plane`), which is `compose_eq_table`.
- `Bool` is not (`not_rcc8Complete_bool`), from `table_not_complete_bool`:
  `EC` is in the table's `DC ⋄ DC` but in no weak composition over `Bool`.
  The same holds for every discrete space (`not_rcc8Complete_of_discrete`):
  its areas have no boundary, so no two are `EC` (`not_ec_of_discrete`).
- Weak composition is a topological invariant (`compose_eq_of_homeomorph`),
  so homeomorphic spaces are complete together or not at all
  (`RCC8Complete.homeomorph`); `ℝ × ℝ` is complete because the plane is.
  The composition table, in other words, is a fact about topology alone.
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
theorem rcc8Complete_plane : RCC8Complete Point2D :=
  compose_eq_table

/-- A table entry that the space does not realise rules completeness out. -/
theorem not_rcc8Complete_of_not_mem {r s t : Relation} (ht : t ∈ table r s)
    (hn : t ∉ compose α r s) : ¬ RCC8Complete α := fun h =>
  hn (by rw [h r s, Finset.mem_coe]; exact ht)

/-- A homeomorphism carries a configuration realising `t ∈ r ⋄ s` to one in
the other space. -/
theorem RCC8.mem_compose_of_homeomorph (e : α ≃ₜ β) {r s t : Relation}
    (h : t ∈ compose α r s) : t ∈ compose β r s := by
  obtain ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩ := h
  exact ⟨A.map e, B.map e, C.map e, hA.image e, hB.image e, hC.image e,
    (Relation.holds_map_iff e A B r).mpr hr, (Relation.holds_map_iff e B C s).mpr hs,
    (Relation.holds_map_iff e A C t).mpr ht⟩

/-- Weak composition is a topological invariant: homeomorphic spaces have the
same weak compositions.

This is what the composition table is about. Its entries are defined by the
existence of areas, and a homeomorphism carries areas to areas and every RCC8
relation to itself, in both directions. So `compose α r s` depends on `α` only
up to homeomorphism: the table is a fact about the topology of the space, not
about its coordinates, distances or straight lines. Stretch the plane, bend
it, or rewrite it as `ℝ × ℝ`, and the table stays where it was.

It is an invariant, not a classification: nothing here says that spaces with
the same table are homeomorphic. -/
theorem RCC8.compose_eq_of_homeomorph (e : α ≃ₜ β) (r s : Relation) :
    compose α r s = compose β r s :=
  Set.ext fun _ => ⟨mem_compose_of_homeomorph e, mem_compose_of_homeomorph e.symm⟩

/-- Completeness passes along a homeomorphism. -/
theorem RCC8Complete.of_homeomorph (h : RCC8Complete α) (e : α ≃ₜ β) : RCC8Complete β :=
  fun r s => (compose_eq_of_homeomorph e r s).symm.trans (h r s)

/-- Homeomorphic spaces are complete together or not at all. -/
theorem RCC8Complete.homeomorph (e : α ≃ₜ β) : RCC8Complete α ↔ RCC8Complete β :=
  ⟨fun h => h.of_homeomorph e, fun h => h.of_homeomorph e.symm⟩

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

/-- `EC` is in no weak composition over a discrete space. -/
theorem RCC8.ec_not_mem_compose_of_discrete (r s : Relation) : Relation.ec ∉ compose α r s :=
  fun ⟨A, _, C, _, _, _, _, _, h⟩ => not_ec_of_discrete A C h

variable (α) in
/-- A discrete space misses a table entry: `EC` is in the table's `DC ⋄ DC`,
which the plane realises, but no two areas of a discrete space are `EC`. -/
theorem table_not_complete_of_discrete :
    ∃ r s t, t ∈ table r s ∧ t ∉ compose α r s :=
  ⟨.dc, .dc, .ec, by decide, ec_not_mem_compose_of_discrete _ _⟩

variable (α) in
/-- The table is complete for no discrete space. -/
theorem not_rcc8Complete_of_discrete : ¬ RCC8Complete α :=
  let ⟨_, _, _, ht, hn⟩ := table_not_complete_of_discrete α
  not_rcc8Complete_of_not_mem ht hn

end Discrete

/-- Over `Bool`, `EC` is in the table's `DC ⋄ DC` but not in the weak
composition. -/
theorem table_not_complete_bool : ∃ r s t, t ∈ table r s ∧ t ∉ compose Bool r s :=
  table_not_complete_of_discrete Bool

/-- The table is not complete for `Bool`. -/
theorem not_rcc8Complete_bool : ¬ RCC8Complete Bool :=
  let ⟨_, _, _, ht, hn⟩ := table_not_complete_bool
  not_rcc8Complete_of_not_mem ht hn

end Geospatial
