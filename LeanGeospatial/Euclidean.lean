import LeanGeospatial.Line
import LeanGeospatial.CompositionTable.Product
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The RCC8 table is complete in every Euclidean space

The line is complete (`rcc8Complete_real`), and a complete space times a
nonempty one is complete (`RCC8Complete.prod_right`). Splitting off one
coordinate, `Fin (n + 2) → ℝ` is `ℝ × (Fin (n + 1) → ℝ)` (`Fin.consEquivL`),
so by induction every `Fin (n + 1) → ℝ` is complete (`rcc8Complete_pi`), and
so is the Euclidean space of every dimension from one up, which carries the
same topology (`rcc8Complete_euclideanSpace`).

Space, LeanGeodesy's `E3`, is the case `n = 2`
(`rcc8Complete_euclideanSpace3`). The plane is the case `n = 1`, reached here
from the line alone, without the rectangles of `CompositionTable/Complete.lean`.
-/

namespace Geospatial

/-- The table is complete for `Fin (n + 1) → ℝ`. -/
theorem rcc8Complete_pi : ∀ n : ℕ, RCC8Complete (Fin (n + 1) → ℝ)
  | 0 => (RCC8Complete.homeomorph (Homeomorph.funUnique (Fin 1) ℝ).symm).mp rcc8Complete_real
  | n + 1 =>
    (RCC8Complete.homeomorph (Fin.consEquivL ℝ fun _ : Fin (n + 2) => ℝ).toHomeomorph).mp
      (rcc8Complete_pi n).prod_left

/-- The table is complete for Euclidean space of every dimension from one
up. -/
theorem rcc8Complete_euclideanSpace (n : ℕ) : RCC8Complete (EuclideanSpace ℝ (Fin (n + 1))) :=
  (RCC8Complete.homeomorph (EuclideanSpace.equiv (Fin (n + 1)) ℝ).toHomeomorph).mpr
    (rcc8Complete_pi n)

/-- The table is complete for three-dimensional space. -/
theorem rcc8Complete_euclideanSpace3 : RCC8Complete (EuclideanSpace ℝ (Fin 3)) :=
  rcc8Complete_euclideanSpace 2

end Geospatial
