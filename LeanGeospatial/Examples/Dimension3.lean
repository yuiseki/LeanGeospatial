import LeanGeospatial.DE9IM.Space3

/-!
# Dimensions in space

`cubeDim 3` is a dimension function on `E3 := EuclideanSpace ℝ (Fin 3)`.
Every value `⊥, 0, 1, 2, 3` occurs: on the empty set, a point, a segment, a
flat square and a ball. The plane's values `F, 0, 1, 2` are the special case
`cubeDim 2` on `Point2D` (`planeDim_eq_cubeDim`); in space the value `3`
appears, for instance as the interior-interior cell of a ball with itself.
-/

namespace Geospatial.Examples.Dimension3

open Geospatial DE9IM Space3

example : (cubeDim 3 : DimensionFunction E3).dim ∅ = ⊥ := (cubeDim 3).dim_empty

example : (cubeDim 3 : DimensionFunction E3).dim {0} = 0 := cubeDim_point

example : (cubeDim 3 : DimensionFunction E3).dim segment3 = 1 := cubeDim_segment

example : (cubeDim 3 : DimensionFunction E3).dim square3 = 2 := cubeDim_square

example : (cubeDim 3 : DimensionFunction E3).dim (Metric.closedBall 0 1) = 3 := cubeDim_ball

/-- A dimension-valued DE-9IM entry that the plane cannot have. -/
example : de9im (cubeDim 3) (Metric.closedBall (0 : E3) 1) (Metric.closedBall 0 1) .I .I = 3 :=
  de9im_ball_ball_II

/-- The plane's values are `cubeDim 2`. -/
example : planeDim = cubeDim 2 := planeDim_eq_cubeDim

end Geospatial.Examples.Dimension3
