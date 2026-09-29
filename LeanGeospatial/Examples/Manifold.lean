import LeanGeospatial.Manifold
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Surfaces on which the RCC8 table is complete

Completeness is local: a Hausdorff space that contains an open copy of the
plane realises every entry of the composition table, because the plane's
witnesses are compact and can be carried into that copy. So every nonempty
Hausdorff 2-manifold is complete. Three instances:

- the sphere, the shape of the Earth in spherical geodesy;
- the open unit disk;
- the plane with one point removed.
-/

namespace Geospatial.Examples.Manifold

open Geospatial

/-- The unit sphere in space. -/
abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

instance : Nonempty S2 :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩

/-- The table is complete on the sphere. -/
theorem sphere_rcc8Complete : RCC8Complete S2 :=
  rcc8Complete_of_chartedSpace S2

/-- The table is complete on the open unit disk. -/
theorem disk_rcc8Complete : RCC8Complete (Metric.ball (0 : Point2D) 1) :=
  rcc8Complete_of_isOpen Metric.isOpen_ball ⟨0, by simp⟩

/-- The table is complete on the plane with the origin removed. -/
theorem punctured_rcc8Complete : RCC8Complete ({0}ᶜ : Set Point2D) :=
  rcc8Complete_of_isOpen isOpen_compl_singleton ⟨Point2D.mk 1 0, fun h => by
    have h' : Point2D.x (Point2D.mk 1 0) = Point2D.x 0 := congrArg Point2D.x h
    rw [Point2D.x_mk] at h'
    exact one_ne_zero (h'.trans rfl)⟩

end Geospatial.Examples.Manifold
