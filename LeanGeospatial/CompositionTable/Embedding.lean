import LeanGeospatial.CompositionTable

/-!
# Completeness is local

An open embedding `f : β → α` is a homeomorphism of `β` onto an open subset of
`α`. It commutes with interior (`interior_image_of_isOpenEmbedding`) and is
injective, so it preserves every RCC8 relation between the images of areas.
It need not carry areas to areas, since the image of a closed set need not be
closed in `α`; but when `α` is Hausdorff, the image of a compact area is
compact, hence closed, and is an area again (`RegularClosedRegion.mapCompact`).

The plane realises every entry of the composition table with compact areas
(rectangles, `realizes_of_mem_table`). So a Hausdorff space that contains an
open copy of the plane realises them too, and the table is complete for it
(`rcc8Complete_of_isOpenEmbedding`). Completeness needs only a small open
piece of plane somewhere in the space.
-/

namespace Geospatial

open Topology RCC8

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

/-- An open embedding commutes with interior. -/
theorem interior_image_of_isOpenEmbedding (hf : IsOpenEmbedding f) (S : Set β) :
    interior (f '' S) = f '' interior S := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨x, -, rfl⟩ := interior_subset hy
    refine ⟨x, ?_, rfl⟩
    have hsub : f ⁻¹' interior (f '' S) ⊆ S := fun z hz => by
      obtain ⟨w, hw, hwz⟩ := interior_subset hz
      exact hf.injective hwz ▸ hw
    exact interior_maximal hsub (isOpen_interior.preimage hf.continuous) hy
  · exact hf.isOpenMap.image_interior_subset S

section Relations

variable (hf : IsOpenEmbedding f) (A B : Set β)
include hf

theorem image_eq_image_iff_of_isOpenEmbedding : f '' A = f '' B ↔ A = B :=
  (Set.image_injective.mpr hf.injective).eq_iff

theorem within_image_iff_of_isOpenEmbedding : Within (f '' A) (f '' B) ↔ Within A B :=
  Set.image_subset_image_iff hf.injective

theorem intersects_image_iff_of_isOpenEmbedding :
    Intersects (f '' A) (f '' B) ↔ Intersects A B := by
  unfold Intersects
  rw [← Set.image_inter hf.injective, Set.image_nonempty]

theorem disjoint_image_iff_of_isOpenEmbedding :
    Geospatial.Disjoint (f '' A) (f '' B) ↔ Geospatial.Disjoint A B := by
  unfold Geospatial.Disjoint
  rw [← Set.image_inter hf.injective, Set.image_eq_empty]

theorem touches_image_iff_of_isOpenEmbedding : Touches (f '' A) (f '' B) ↔ Touches A B := by
  unfold Touches
  rw [intersects_image_iff_of_isOpenEmbedding hf, interior_image_of_isOpenEmbedding hf,
    interior_image_of_isOpenEmbedding hf, disjoint_image_iff_of_isOpenEmbedding hf]

end Relations

namespace RegularClosedRegion

variable [T2Space α]

/-- The image of a compact area under an open embedding into a Hausdorff
space, again an area. -/
def mapCompact (hf : IsOpenEmbedding f) (A : RegularClosedRegion β)
    (hA : IsCompact (A : Set β)) : RegularClosedRegion α where
  carrier := f '' A
  closure_interior_eq' := by
    rw [interior_image_of_isOpenEmbedding hf]
    apply Set.Subset.antisymm
    · exact closure_minimal (Set.image_mono interior_subset) (hA.image hf.continuous).isClosed
    · calc f '' (A : Set β) = f '' closure (interior (A : Set β)) := by
            rw [A.closure_interior_eq]
        _ ⊆ closure (f '' interior (A : Set β)) :=
            image_closure_subset_closure_image hf.continuous

@[simp] theorem coe_mapCompact (hf : IsOpenEmbedding f) (A : RegularClosedRegion β)
    (hA : IsCompact (A : Set β)) : ((A.mapCompact hf hA : RegularClosedRegion α) : Set α) = f '' A :=
  rfl

end RegularClosedRegion

/-- An open embedding into a Hausdorff space keeps every RCC8 relation between
compact areas. -/
theorem RCC8.Relation.holds_mapCompact_iff [T2Space α] (hf : IsOpenEmbedding f)
    {A B : RegularClosedRegion β} (hA : IsCompact (A : Set β)) (hB : IsCompact (B : Set β))
    (r : Relation) :
    r.holds (A.mapCompact hf hA) (B.mapCompact hf hB) ↔ r.holds A B := by
  cases r <;>
    simp only [Relation.holds, DC, EC, PO, EQ, TPP, NTPP, TPPi, NTPPi, ne_eq,
      RegularClosedRegion.coe_mapCompact, interior_image_of_isOpenEmbedding hf,
      disjoint_image_iff_of_isOpenEmbedding hf, touches_image_iff_of_isOpenEmbedding hf,
      intersects_image_iff_of_isOpenEmbedding hf, within_image_iff_of_isOpenEmbedding hf,
      image_eq_image_iff_of_isOpenEmbedding hf]

/-- A Hausdorff space containing an open copy of the plane is complete for the
table: the plane's compact witnesses carry over. -/
theorem rcc8Complete_of_isOpenEmbedding [T2Space α] {f : Point2D → α}
    (hf : IsOpenEmbedding f) : RCC8Complete α := by
  refine rcc8Complete_iff_table_subset.mpr fun r s t ht => ?_
  obtain ⟨A, B, C, kA, kB, kC, -, -, -, hA, hB, hC, hr, hs, ht'⟩ :=
    realizes_of_mem_table r s t (Finset.mem_coe.mp ht)
  exact ⟨A.mapCompact hf kA, B.mapCompact hf kB, C.mapCompact hf kC,
    hA.image f, hB.image f, hC.image f,
    (Relation.holds_mapCompact_iff hf kA kB r).mpr hr,
    (Relation.holds_mapCompact_iff hf kB kC s).mpr hs,
    (Relation.holds_mapCompact_iff hf kA kC t).mpr ht'⟩

end Geospatial
