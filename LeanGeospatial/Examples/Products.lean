import LeanGeospatial.Euclidean

/-!
# Completeness through products

`RCC8Complete.prod_right` lifts every witness `A` of a complete space `α` to
`A ×ˢ univ` in `α × β`, for any nonempty `β`. Starting from the line, every
Euclidean space follows, and so do spaces that are not manifolds at all.
-/

namespace Geospatial.Examples.Products

open Geospatial

/-- The plane again, now from the line rather than from rectangles. -/
example : RCC8Complete (ℝ × ℝ) := rcc8Complete_real.prod_right

/-- Space: LeanGeodesy's `E3`. -/
example : RCC8Complete (EuclideanSpace ℝ (Fin 3)) := rcc8Complete_euclideanSpace3

/-- Every dimension from one up. -/
example (n : ℕ) : RCC8Complete (EuclideanSpace ℝ (Fin (n + 1))) := rcc8Complete_euclideanSpace n

/-- Two parallel lines: `Bool` alone is not complete, but a factor only has to
be nonempty. -/
example : RCC8Complete (ℝ × Bool) := rcc8Complete_real.prod_right

/-- The factor can stand on either side. -/
example : RCC8Complete (Bool × ℝ) := rcc8Complete_real.prod_left

end Geospatial.Examples.Products
