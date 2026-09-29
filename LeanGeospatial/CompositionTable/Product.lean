import LeanGeospatial.CompositionTable

/-!
# Completeness passes to products

For an area `A` of `α` and a nonempty space `β`, `A ×ˢ univ` is an area of
`α × β` (`RegularClosedRegion.prodUniv`). The factor has to be the whole of
`β`: then `interior (A ×ˢ univ) = interior A ×ˢ univ`, and meeting,
containment, equality and lying in an interior are all read off the first
factor. A bounded factor such as `[0, 1]` would not do: its boundary would
spoil `NTPP`, which asks for one area to lie in the other's interior.

So every RCC8 relation is kept (`RCC8.Relation.holds_prodUniv_iff`), every
configuration realised in `α` is realised in `α × β`, and a complete `α`
makes `α × β` complete for every nonempty `β` (`RCC8Complete.prod_right`,
`RCC8Complete.prod_left`).
-/

namespace Geospatial

open Set RCC8

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Nonempty β]

namespace RegularClosedRegion

/-- `A ×ˢ univ` as an area of `α × β`. -/
def prodUniv (A : RegularClosedRegion α) (β : Type*) [TopologicalSpace β] :
    RegularClosedRegion (α × β) where
  carrier := (A : Set α) ×ˢ (univ : Set β)
  closure_interior_eq' := by
    rw [interior_prod_eq, interior_univ, closure_prod_eq, closure_univ, A.closure_interior_eq]

omit [Nonempty β] in
@[simp] theorem coe_prodUniv (A : RegularClosedRegion α) :
    ((A.prodUniv β : RegularClosedRegion (α × β)) : Set (α × β)) = (A : Set α) ×ˢ univ :=
  rfl

end RegularClosedRegion

section Sets

variable (A B : Set α)

omit [TopologicalSpace α] [TopologicalSpace β] in
theorem prod_univ_subset_iff : A ×ˢ (univ : Set β) ⊆ B ×ˢ univ ↔ A ⊆ B :=
  ⟨fun h a ha => (h (show (a, Classical.arbitrary β) ∈ A ×ˢ (univ : Set β) from
      ⟨ha, mem_univ _⟩)).1,
    fun h => prod_mono h le_rfl⟩

omit [TopologicalSpace α] [TopologicalSpace β] in
theorem prod_univ_eq_iff : A ×ˢ (univ : Set β) = B ×ˢ univ ↔ A = B :=
  ⟨fun h => Subset.antisymm ((prod_univ_subset_iff A B).mp h.le)
    ((prod_univ_subset_iff B A).mp h.ge), fun h => h ▸ rfl⟩

omit [TopologicalSpace α] [TopologicalSpace β] in
theorem intersects_prod_univ_iff :
    Intersects (A ×ˢ (univ : Set β)) (B ×ˢ univ) ↔ Intersects A B := by
  unfold Intersects
  rw [prod_inter_prod, inter_self, prod_nonempty_iff]
  exact and_iff_left univ_nonempty

omit [TopologicalSpace α] [TopologicalSpace β] in
theorem disjoint_prod_univ_iff :
    Geospatial.Disjoint (A ×ˢ (univ : Set β)) (B ×ˢ univ) ↔ Geospatial.Disjoint A B := by
  rw [disjoint_iff_not_intersects, disjoint_iff_not_intersects, intersects_prod_univ_iff]

omit [Nonempty β] in
theorem interior_prod_univ : interior (A ×ˢ (univ : Set β)) = interior A ×ˢ univ := by
  rw [interior_prod_eq, interior_univ]

theorem touches_prod_univ_iff : Touches (A ×ˢ (univ : Set β)) (B ×ˢ univ) ↔ Touches A B := by
  unfold Touches
  rw [intersects_prod_univ_iff, interior_prod_univ, interior_prod_univ, disjoint_prod_univ_iff]

end Sets

/-- Every RCC8 relation between two areas is the relation between their
products with the whole of `β`. -/
theorem RCC8.Relation.holds_prodUniv_iff (A B : RegularClosedRegion α) (r : Relation) :
    r.holds (A.prodUniv β) (B.prodUniv β) ↔ r.holds A B := by
  cases r <;>
    simp only [Relation.holds, DC, EC, PO, EQ, TPP, NTPP, TPPi, NTPPi, ne_eq,
      RegularClosedRegion.coe_prodUniv, interior_prod_univ, disjoint_prod_univ_iff,
      touches_prod_univ_iff, intersects_prod_univ_iff, prod_univ_subset_iff, Within,
      prod_univ_eq_iff]

/-- Every configuration realised in `α` is realised in `α × β`. -/
theorem RCC8.compose_subset_compose_prod (r s : Relation) :
    compose α r s ⊆ compose (α × β) r s := by
  rintro t ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩
  exact ⟨A.prodUniv β, B.prodUniv β, C.prodUniv β, hA.prod univ_nonempty,
    hB.prod univ_nonempty, hC.prod univ_nonempty, (Relation.holds_prodUniv_iff A B r).mpr hr,
    (Relation.holds_prodUniv_iff B C s).mpr hs, (Relation.holds_prodUniv_iff A C t).mpr ht⟩

/-- A complete space times any nonempty space is complete. -/
theorem RCC8Complete.prod_right (h : RCC8Complete α) : RCC8Complete (α × β) :=
  rcc8Complete_iff_table_subset.mpr fun r s =>
    (h r s).ge.trans (compose_subset_compose_prod r s)

/-- The same with the complete factor on the right. -/
theorem RCC8Complete.prod_left (h : RCC8Complete α) : RCC8Complete (β × α) :=
  (RCC8Complete.homeomorph (Homeomorph.prodComm α β)).mp h.prod_right

end Geospatial
