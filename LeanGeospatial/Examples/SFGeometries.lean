import LeanGeospatial.SFA.Geometries
import LeanGeospatial.Examples.ComputationalPolygon

/-!
# Worked examples: Full OGC Simple Features Geometry Hierarchy

Demonstrates all nine OGC SFA 1.2.1 geometry types (`empty`, `point`,
`multiPoint`, `lineString`, `multiLineString`, `linearRing`, `polygon`,
`multiPolygon`, `collection`), their dimensions, validity, simplicity, and
strata partition.
-/

namespace Geospatial.Examples.SFGeometries

open Geospatial Geospatial.SFA ComputationalGeometry

def gEmpty : SFGeometry := .empty
def gPoint : SFGeometry := .point (Point2D.mk 1 1)
def gMultiPoint : SFGeometry := .multiPoint ⟨[Point2D.mk 0 0, Point2D.mk 1 0]⟩
def gSeg : SFGeometry := .lineString (LineString.seg (Point2D.mk 0 0) (Point2D.mk 1 0) (by
  intro h; have := congrArg Geospatial.Point2D.x h; norm_num at this))
def gMultiLine : SFGeometry := .multiLineString ⟨[
  LineString.seg (Point2D.mk 0 0) (Point2D.mk 1 0) (by
    intro h; have := congrArg Geospatial.Point2D.x h; norm_num at this),
  LineString.seg (Point2D.mk 1 0) (Point2D.mk 2 0) (by
    intro h; have := congrArg Geospatial.Point2D.x h; norm_num at this)]⟩
noncomputable def gRing : SFGeometry := .linearRing Examples.ComputationalPolygon.triSimple
noncomputable def gPoly : SFGeometry := .polygon (SFPolygon.ofSimple Examples.ComputationalPolygon.triSimple)
noncomputable def gMultiPoly : SFGeometry :=
  .multiPolygon ⟨[SFPolygon.ofSimple Examples.ComputationalPolygon.triSimple]⟩
noncomputable def gCollection : SFGeometry := .collection [gPoint, gPoly]

theorem dims_example :
    gEmpty.dim = ⊥ ∧
    gPoint.dim = (0 : WithBot ℕ) ∧
    gMultiPoint.dim = (0 : WithBot ℕ) ∧
    gSeg.dim = (1 : WithBot ℕ) ∧
    gMultiLine.dim = (1 : WithBot ℕ) ∧
    gRing.dim = (1 : WithBot ℕ) ∧
    gPoly.dim = (2 : WithBot ℕ) ∧
    gMultiPoly.dim = (2 : WithBot ℕ) ∧
    gCollection.dim = (2 : WithBot ℕ) := by
  simp [gEmpty, gPoint, gMultiPoint, gSeg, gMultiLine, gRing, gPoly, gMultiPoly, gCollection,
    SFGeometry.dim, SFMultiPoint.dim, SFMultiLineString.dim, SFMultiPolygon.dim]

theorem multiPoint_simple_example : gMultiPoint.IsSimple := by
  simp only [gMultiPoint, SFGeometry.IsSimple, SFMultiPoint.IsSimple, List.nodup_cons,
    List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
  intro h
  have := congrArg Geospatial.Point2D.x h
  norm_num at this

/-- Every point lies in a unique stratum of the heterogeneous `GeometryCollection`. -/
theorem collection_partition_example (p : Point2D) :
    ∃! s : Stratum, p ∈ gCollection.stratum s :=
  SFGeometry.existsUnique_stratum gCollection p

end Geospatial.Examples.SFGeometries
