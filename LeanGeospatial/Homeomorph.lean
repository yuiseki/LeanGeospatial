import LeanGeospatial.RCC8
import LeanGeospatial.DE9IM.Dimension
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homeomorphisms preserve spatial relations

A homeomorphism of the plane is a continuous bijection with a continuous
inverse. It may stretch and bend the plane but never tear or glue it. The
spatial relations of this library are all built from set operations and from
interior, closure and boundary, and a homeomorphism commutes with every one of
them. So no relation can tell a configuration from its image.

The file proves this in the order the relations are built:

1. `RegularClosedRegion.map` carries an area along a homeomorphism, and the
   image is again an area.
2. Touching is preserved: `RegularClosedRegion.touches_map_iff`, resting on
   `touches_image_iff` for arbitrary regions.
3. Every RCC8 relation is preserved: `RCC8.Relation.holds_map_iff`.
4. Every DE-9IM cell is carried to the corresponding cell (`cell_image`). So a
   `T`/`F`/`*` pattern matches after the map exactly when it matched before
   (`DE9IM.Pattern.matches_image_iff`). The dimension of each cell is kept
   too (`DE9IM.DimValue.of_image`), so for areas the whole DE-9IM matrix is
   unchanged (`DE9IM.matrix_map`).

Translations, rotations, reflections and every other isometry are
homeomorphisms, so all of this applies to them.
-/

namespace Geospatial

variable (e : Point2D ≃ₜ Point2D)

/-! ## Regions and their images -/

section Image

variable (A B : Region)

theorem interior_image : interior (e '' A) = e '' interior A :=
  (e.image_interior A).symm

theorem boundary_image : boundary (e '' A) = e '' boundary A :=
  (e.image_frontier A).symm

theorem exterior_image : exterior (e '' A) = e '' exterior A := by
  rw [exterior, exterior, ← Set.image_compl_eq e.bijective, interior_image]

theorem image_eq_image_iff : e '' A = e '' B ↔ A = B :=
  (Set.image_injective.mpr e.injective).eq_iff

theorem within_image_iff : Within (e '' A) (e '' B) ↔ Within A B :=
  Set.image_subset_image_iff e.injective

theorem intersects_image_iff : Intersects (e '' A) (e '' B) ↔ Intersects A B := by
  unfold Intersects
  rw [← Set.image_inter e.injective, Set.image_nonempty]

theorem disjoint_image_iff :
    Geospatial.Disjoint (e '' A) (e '' B) ↔ Geospatial.Disjoint A B := by
  unfold Geospatial.Disjoint
  rw [← Set.image_inter e.injective, Set.image_eq_empty]

/-- Two regions touch exactly when their images under a homeomorphism do. -/
theorem touches_image_iff : Touches (e '' A) (e '' B) ↔ Touches A B := by
  unfold Touches
  rw [intersects_image_iff, interior_image, interior_image, disjoint_image_iff]

end Image

/-! ## Areas -/

namespace RegularClosedRegion

/-- The image of an area under a homeomorphism, again an area. -/
def map (A : RegularClosedRegion) : RegularClosedRegion where
  carrier := e '' A
  closure_interior_eq' := by
    rw [← e.image_interior, ← e.image_closure, A.closure_interior_eq]

@[simp] theorem coe_map (A : RegularClosedRegion) :
    ((A.map e : RegularClosedRegion) : Region) = e '' A := rfl

/-- Two areas touch exactly when their images under a homeomorphism do. -/
theorem touches_map_iff (A B : RegularClosedRegion) :
    Touches (A.map e : Region) (B.map e) ↔ Touches (A : Region) B :=
  touches_image_iff e A B

end RegularClosedRegion

/-! ## RCC8 -/

namespace RCC8

variable (A B : RegularClosedRegion)

theorem dc_map_iff : DC (A.map e) (B.map e) ↔ DC A B :=
  disjoint_image_iff e A B

theorem ec_map_iff : EC (A.map e) (B.map e) ↔ EC A B :=
  touches_image_iff e A B

theorem po_map_iff : PO (A.map e) (B.map e) ↔ PO A B := by
  simp only [PO, RegularClosedRegion.coe_map, interior_image, intersects_image_iff,
    within_image_iff]

theorem eq_map_iff : EQ (A.map e) (B.map e) ↔ EQ A B :=
  image_eq_image_iff e A B

theorem tpp_map_iff : TPP (A.map e) (B.map e) ↔ TPP A B := by
  simp only [TPP, RegularClosedRegion.coe_map, interior_image, within_image_iff, ne_eq,
    image_eq_image_iff]

theorem ntpp_map_iff : NTPP (A.map e) (B.map e) ↔ NTPP A B := by
  simp only [NTPP, RegularClosedRegion.coe_map, interior_image, within_image_iff, ne_eq,
    image_eq_image_iff]

theorem tppi_map_iff : TPPi (A.map e) (B.map e) ↔ TPPi A B :=
  tpp_map_iff e B A

theorem ntppi_map_iff : NTPPi (A.map e) (B.map e) ↔ NTPPi A B :=
  ntpp_map_iff e B A

/-- Each of the eight RCC8 relations holds between two areas exactly when it
holds between their images under a homeomorphism. -/
theorem Relation.holds_map_iff (r : Relation) :
    r.holds (A.map e) (B.map e) ↔ r.holds A B := by
  cases r
  · exact dc_map_iff e A B
  · exact ec_map_iff e A B
  · exact po_map_iff e A B
  · exact eq_map_iff e A B
  · exact tpp_map_iff e A B
  · exact ntpp_map_iff e A B
  · exact tppi_map_iff e A B
  · exact ntppi_map_iff e A B

end RCC8

/-! ## DE-9IM -/

theorem Stratum.set_image (s : Stratum) (A : Region) : s.set (e '' A) = e '' s.set A := by
  cases s
  · exact interior_image e A
  · exact boundary_image e A
  · exact exterior_image e A

/-- A homeomorphism carries each of the nine cells to the corresponding cell of
the images. -/
theorem cell_image (s t : Stratum) (A B : Region) :
    cell s t (e '' A) (e '' B) = e '' cell s t A B := by
  simp only [cell, Stratum.set_image, Set.image_inter e.injective]

namespace DE9IM

theorem PatternChar.matches_image_iff (c : PatternChar) (S : Region) :
    c.Matches (e '' S) ↔ c.Matches S := by
  cases c <;> simp only [PatternChar.Matches, Set.image_nonempty, Set.image_eq_empty]

/-- A `T`/`F`/`*` pattern matches two regions exactly when it matches their
images under a homeomorphism. -/
theorem Pattern.matches_image_iff (p : Pattern) (A B : Region) :
    p.Matches (e '' A) (e '' B) ↔ p.Matches A B := by
  simp only [Pattern.Matches, II, IB, IE, BI, BB, BE, EI, EB, EE, cell_image,
    PatternChar.matches_image_iff]

theorem hasArc_image_iff (S : Region) : HasArc (e '' S) ↔ HasArc S := by
  have key : ∀ (f : Point2D ≃ₜ Point2D) (S : Region), HasArc S → HasArc (f '' S) := by
    rintro f S ⟨g, hc, hi, hg⟩
    refine ⟨f ∘ g, f.continuous.comp_continuousOn hc, f.injective.comp_injOn hi, ?_⟩
    rw [Set.image_comp]
    exact Set.image_mono hg
  refine ⟨fun h => ?_, key e S⟩
  have h' := key e.symm _ h
  simpa only [Set.image_image, Homeomorph.symm_apply_apply, Set.image_id'] using h'

theorem DimValue.describes_image_iff (d : DimValue) (S : Region) :
    d.Describes (e '' S) ↔ d.Describes S := by
  cases d <;> simp only [DimValue.Describes, interior_image, Set.image_nonempty,
    Set.image_eq_empty, hasArc_image_iff]

/-- A homeomorphism keeps the dimension of every set: a point stays a point, an
arc an arc, and a set with interior keeps interior. -/
theorem DimValue.of_image (S : Region) : DimValue.of (e '' S) = DimValue.of S :=
  DimValue.of_eq ((DimValue.describes_image_iff e _ S).mpr (DimValue.of_describes S))

/-- The DE-9IM matrix of two areas is unchanged by a homeomorphism. -/
theorem matrix_map (A B : RegularClosedRegion) (s t : Stratum) :
    matrix (.area (A.map e)) (.area (B.map e)) s t = matrix (.area A) (.area B) s t := by
  simp only [matrix, Geometry.cell_area_area, RegularClosedRegion.coe_map, cell_image,
    DimValue.of_image]

/-- A dimensioned pattern matches two areas exactly when it matches their
images under a homeomorphism. -/
theorem DimPattern.matches_map_iff (p : DimPattern) (A B : RegularClosedRegion) :
    p.Matches (.area (A.map e)) (.area (B.map e)) ↔ p.Matches (.area A) (.area B) := by
  simp only [DimPattern.Matches, DimPatternChar.Matches, Geometry.cell_area_area,
    RegularClosedRegion.coe_map, cell_image, DimValue.of_image]

end DE9IM

end Geospatial
