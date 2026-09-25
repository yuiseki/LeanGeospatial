import LeanGeospatial.CompositionTable.Complete

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
