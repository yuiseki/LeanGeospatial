import LeanGeospatial.Circle

/-!
# The circle is complete for connected areas

The line is complete but not for connected areas: no three intervals touch
one another pairwise. The circle closes up, and three arcs can: going round,
each meets the next at an end. With that and its other arcs, the circle
realises the whole table with connected areas. So completeness for connected
areas is not a matter of dimension alone: the line and the circle are both
one-dimensional, and only the circle has it.
-/

namespace Geospatial.Examples.Circle

open Geospatial

example : RCC8ConnectedComplete _root_.Circle := rcc8ConnectedComplete_circle

/-- Longitude, as LeanGeodesy represents it: an angle. -/
example : RCC8ConnectedComplete Real.Angle := rcc8ConnectedComplete_angle

example : ¬ RCC8ConnectedComplete ℝ ∧ RCC8ConnectedComplete _root_.Circle :=
  ⟨not_rcc8ConnectedComplete_real, rcc8ConnectedComplete_circle⟩

end Geospatial.Examples.Circle
