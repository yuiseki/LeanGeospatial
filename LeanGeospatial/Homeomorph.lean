import LeanGeospatial.RegularClosed
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homeomorphisms preserve touching

A homeomorphism of the plane is a continuous bijection with a continuous
inverse. It may stretch and bend the plane but never tear or glue it, so it
sends interiors to interiors and closures to closures. Topological relations
are the ones such maps cannot change.

This file records the smallest instance. `RegularClosedRegion.map` carries an
area along a homeomorphism, and `RegularClosedRegion.touches_map_iff` says two
areas touch exactly when their images do. The work is done for arbitrary
regions by `touches_image_iff`.
-/

namespace Geospatial

variable (e : Point2D ≃ₜ Point2D)

/-- Two regions touch exactly when their images under a homeomorphism do. -/
theorem touches_image_iff (A B : Region) :
    Touches (e '' A) (e '' B) ↔ Touches A B := by
  unfold Touches Intersects Geospatial.Disjoint
  rw [← e.image_interior, ← e.image_interior, ← Set.image_inter e.injective,
    ← Set.image_inter e.injective, Set.image_nonempty, Set.image_eq_empty]

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

end Geospatial
