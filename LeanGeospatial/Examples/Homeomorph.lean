import LeanGeospatial.Homeomorph
import LeanGeospatial.Examples.Touches

/-!
# Moving touching squares

Squares A and B of `Examples.Touches` share an edge. Carried by any
homeomorphism of the plane they still touch, and the converse holds too. A
translation is the simplest instance: slide both squares ten units to the
right and they still touch.
-/

namespace Geospatial.Examples.Homeomorph

open Geospatial Geospatial.Examples.Touches

noncomputable section

/-- Whatever homeomorphism carries A and B, the images touch. -/
theorem map_areaA_touches_map_areaB (e : Point2D ≃ₜ Point2D) :
    Touches (areaA.map e : Region) (areaB.map e) :=
  (RegularClosedRegion.touches_map_iff e areaA areaB).mpr areaA_touches_areaB

/-- Sliding the plane ten units along x. -/
def slide : Point2D ≃ₜ Point2D := Homeomorph.addRight (Point2D.mk 10 0)

theorem slid_squares_touch : Touches (areaA.map slide : Region) (areaB.map slide) :=
  map_areaA_touches_map_areaB slide

end

end Geospatial.Examples.Homeomorph
