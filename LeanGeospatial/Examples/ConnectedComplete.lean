import LeanGeospatial.ConnectedComplete

/-!
# Connected areas tell the line from the plane

`RCC8Complete` holds for the line, the plane and space alike. Asking the
witnesses to be connected separates them: the line is not complete for
connected areas, while the plane and space are.
-/

namespace Geospatial.Examples.ConnectedComplete

open Geospatial

/-- Complete, but not with connected areas. -/
example : RCC8Complete ℝ ∧ ¬ RCC8ConnectedComplete ℝ :=
  ⟨rcc8Complete_real, not_rcc8ConnectedComplete_real⟩

example : RCC8ConnectedComplete Point2D := rcc8ConnectedComplete_plane

example : RCC8ConnectedComplete (EuclideanSpace ℝ (Fin 3)) :=
  rcc8ConnectedComplete_euclideanSpace3

/-- Every dimension from two up. -/
example (n : ℕ) : RCC8ConnectedComplete (EuclideanSpace ℝ (Fin (n + 2))) :=
  rcc8ConnectedComplete_euclideanSpace n

end Geospatial.Examples.ConnectedComplete
