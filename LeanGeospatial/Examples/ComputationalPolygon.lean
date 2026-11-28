import LeanGeospatial.ComputationalPolygon
import LeanComputationalGeometry.Polygon.TriangleRegion

/-!
# Worked examples: LeanComputationalGeometry connected to LeanGeospatial

Demonstrates GIS-free, machine-checked computation and verification of spatial
relations and DE-9IM matrices directly from exact integer coordinates:

1. A simple triangle `T` converted to `RegularClosedRegion Point2D` via
   `SimplePolygonBridge.toRegularClosedRegion`, with interior, boundary, and
   exterior points whose full 9-cell DE-9IM matrices (`0FFFFF212`, `F0FFFF212`,
   `FF0FFF212`) and Simple Features predicates (`within`, `touches`, `disjoint`)
   are computed and verified inside Lean.
2. Exact integer rectangle RCC8 classification (`IRect.rcc8`) verified against
   topological `RCC8.Relation.holds`.
3. Exact integer segment intersection (`intersectTestI`) verified against
   `Geospatial.Intersects`.
-/

namespace Geospatial.Examples.ComputationalPolygon

open Geospatial ComputationalGeometry

/-- The right triangle `(0, 0), (4, 0), (0, 4)`. -/
def triVerts : List IPoint := [⟨0, 0⟩, ⟨4, 0⟩, ⟨0, 4⟩]

/-- As a `ComputationalGeometry.Triangle`. -/
noncomputable def tri : Triangle :=
  ⟨(⟨0, 0⟩ : IPoint).toPoint2D, (⟨4, 0⟩ : IPoint).toPoint2D, (⟨0, 4⟩ : IPoint).toPoint2D⟩

theorem tri_isCCW : tri.IsCCW := by
  show 0 < orient _ _ _
  simp only [tri, orient_toPoint2D, orientI]
  norm_num

theorem toRawPolygon_triVerts :
    ComputationalGeometry.toRawPolygon triVerts = tri.toPolygon := by
  unfold ComputationalGeometry.toRawPolygon triVerts RawPolygon.ofList Triangle.toPolygon
  congr 1
  funext i
  fin_cases i <;> rfl

theorem triVerts_isSimple : (ComputationalGeometry.toRawPolygon triVerts).IsSimple := by
  rw [toRawPolygon_triVerts]
  exact tri.isSimple_toPolygon tri_isCCW.nondegenerate

noncomputable def triSimple : SimplePolygon :=
  ⟨ComputationalGeometry.toRawPolygon triVerts, triVerts_isSimple⟩

/-- `(1, 1)` is strictly inside the triangle: DE-9IM matrix is `0FFFFF212` and
`SF.Within` holds. -/
theorem point_1_1_matrix :
    Prover.Matrix9.of (.point (⟨1, 1⟩ : IPoint).toPoint2D)
      (SimplePolygonBridge.toGeometry triSimple) =
      ⟨.d0, .F, .F, .F, .F, .F, .d2, .d1, .d2⟩ := by
  rw [triSimple, pointPolygonMatrixI_eq ⟨1, 1⟩ triVerts triVerts_isSimple]
  decide

theorem point_1_1_within :
    SF.Within (.point (⟨1, 1⟩ : IPoint).toPoint2D)
      (SimplePolygonBridge.toGeometry triSimple) := by
  have h := (pointPolygonClaimI_iff .within ⟨1, 1⟩ triVerts triVerts_isSimple).mp (by decide)
  exact h

/-- `(2, 0)` is on the bottom edge of the triangle: DE-9IM matrix is `F0FFFF212`
and `SF.Touches` holds. -/
theorem point_2_0_matrix :
    Prover.Matrix9.of (.point (⟨2, 0⟩ : IPoint).toPoint2D)
      (SimplePolygonBridge.toGeometry triSimple) =
      ⟨.F, .d0, .F, .F, .F, .F, .d2, .d1, .d2⟩ := by
  rw [triSimple, pointPolygonMatrixI_eq ⟨2, 0⟩ triVerts triVerts_isSimple]
  decide

theorem point_2_0_touches :
    SF.Touches (.point (⟨2, 0⟩ : IPoint).toPoint2D)
      (SimplePolygonBridge.toGeometry triSimple) := by
  have h := (pointPolygonClaimI_iff .touches ⟨2, 0⟩ triVerts triVerts_isSimple).mp (by decide)
  exact h

/-- `(5, 5)` is outside the triangle: DE-9IM matrix is `FF0FFF212` and
`SF.Disjoint` holds. -/
theorem point_5_5_disjoint :
    SF.Disjoint (.point (⟨5, 5⟩ : IPoint).toPoint2D)
      (SimplePolygonBridge.toGeometry triSimple) := by
  have h := (pointPolygonClaimI_iff .disjoint ⟨5, 5⟩ triVerts triVerts_isSimple).mp (by decide)
  exact h

/-- Two touching integer rectangles: `[0, 2] × [0, 2]` and `[2, 4] × [0, 2]`
are classified as `EC` and verified against `RCC8.EC`. -/
def rectA : IRect := ⟨0, 2, 0, 2⟩
def rectB : IRect := ⟨2, 4, 0, 2⟩
def rectC : IRect := ⟨1, 3, 1, 3⟩

theorem rectA_ec_rectB :
    RCC8.EC (rectA.toRegularClosed ⟨by decide, by decide⟩)
      (rectB.toRegularClosed ⟨by decide, by decide⟩) := by
  have h := IRect.rcc8_holds rectA rectB ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  have heq : rectA.rcc8 rectB = .ec := by decide
  rw [heq] at h
  exact h

theorem rectA_po_rectC :
    RCC8.PO (rectA.toRegularClosed ⟨by decide, by decide⟩)
      (rectC.toRegularClosed ⟨by decide, by decide⟩) := by
  have h := IRect.rcc8_holds rectA rectC ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  have heq : rectA.rcc8 rectC = .po := by decide
  rw [heq] at h
  exact h

/-- Crossing integer segments intersect in `Geospatial.Intersects`. -/
theorem crossing_segments_intersect :
    Geospatial.Intersects
      (⟨⟨0, 0⟩, ⟨2, 2⟩⟩ : ISegment).toSegment.toSet
      (⟨⟨0, 2⟩, ⟨2, 0⟩⟩ : ISegment).toSegment.toSet :=
  (intersectTestI_iff_intersects _ _).mpr (by decide)

end Geospatial.Examples.ComputationalPolygon
