import LeanGeospatial.Circle.Witnesses
import LeanGeospatial.ConnectedComplete
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The circle is complete for connected areas

The line is not complete for connected areas: no three intervals touch one
another pairwise (`not_ec_triangle_real`). The circle closes up, and three
arcs can: going round, each meets the next at an end. The circle realises
every entry of the table with arcs, which are connected: `Circle/Witnesses.lean`
lists three arcs for each entry and `circleWitness_ok` checks all 193 by
`decide`, computing relations with `cycRel`. So the circle `AddCircle 6` is
complete for connected areas (`Cyc.rcc8ConnectedComplete_addCircle6`), and
through homeomorphisms so are `Real.Angle`, the type of LeanGeodesy's
longitudes, and Mathlib's unit circle `Circle`
(`rcc8ConnectedComplete_angle`, `rcc8ConnectedComplete_circle`).

The line and the circle are both one-dimensional manifolds, and only the
circle is complete for connected areas. So that property is not decided by
dimension alone: it depends on the global shape of the space.
-/

namespace Geospatial.Cyc

open Geospatial RCC8

/-- The cells of an arc `[a, b)`. -/
def arc (p : ℤ × ℤ) : Finset ℤ := Finset.Ico p.1 p.2

/-- The three arcs for `t ∈ r ⋄ s` are nonempty runs of cells with the right
relations. -/
def WitnessOk (r s t : Relation) : Prop :=
  (circleWitness r s t).1.1 < (circleWitness r s t).1.2 ∧
    (circleWitness r s t).2.1.1 < (circleWitness r s t).2.1.2 ∧
    (circleWitness r s t).2.2.1 < (circleWitness r s t).2.2.2 ∧
    cycRel (norm (arc (circleWitness r s t).1)) (norm (arc (circleWitness r s t).2.1)) = r ∧
    cycRel (norm (arc (circleWitness r s t).2.1)) (norm (arc (circleWitness r s t).2.2)) = s ∧
    cycRel (norm (arc (circleWitness r s t).1)) (norm (arc (circleWitness r s t).2.2)) = t

instance (r s t : Relation) : Decidable (WitnessOk r s t) := by
  unfold WitnessOk
  infer_instance

/-- Every witness checks out. -/
theorem circleWitness_ok :
    ∀ r ∈ Relation.all, ∀ s ∈ Relation.all, ∀ t ∈ table r s, WitnessOk r s t := by
  decide

/-- The circle of period `6` is complete for connected areas. -/
theorem rcc8ConnectedComplete_addCircle6 : RCC8ConnectedComplete C6 := by
  refine rcc8ConnectedComplete_iff_table_subset.mpr fun r s t ht => ?_
  have hok := circleWitness_ok r (Relation.mem_all r) s (Relation.mem_all s) t
    (Finset.mem_coe.mp ht)
  unfold WitnessOk at hok
  generalize circleWitness r s t = w at hok
  obtain ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩, ⟨a₃, b₃⟩⟩ := w
  obtain ⟨h₁, h₂, h₃, e₁, e₂, e₃⟩ := hok
  have n₁ : (arc (a₁, b₁)).Nonempty := Finset.nonempty_Ico.mpr h₁
  have n₂ : (arc (a₂, b₂)).Nonempty := Finset.nonempty_Ico.mpr h₂
  have n₃ : (arc (a₃, b₃)).Nonempty := Finset.nonempty_Ico.mpr h₃
  exact ⟨area (arc (a₁, b₁)), area (arc (a₂, b₂)), area (arc (a₃, b₃)),
    isConnected_area_Ico h₁, isConnected_area_Ico h₂, isConnected_area_Ico h₃,
    e₁ ▸ cycRel_holds n₁ n₂, e₂ ▸ cycRel_holds n₂ n₃, e₃ ▸ cycRel_holds n₁ n₃⟩

end Geospatial.Cyc

namespace Geospatial

/-- Angles, the type of LeanGeodesy's longitudes, are complete for connected
areas. -/
theorem rcc8ConnectedComplete_angle : RCC8ConnectedComplete Real.Angle :=
  (RCC8ConnectedComplete.homeomorph
    (AddCircle.homeomorphAddCircle (6 : ℝ) (2 * Real.pi) (by norm_num)
      (by positivity))).mp Cyc.rcc8ConnectedComplete_addCircle6

/-- Mathlib's unit circle is complete for connected areas. -/
theorem rcc8ConnectedComplete_circle : RCC8ConnectedComplete _root_.Circle :=
  (RCC8ConnectedComplete.homeomorph AddCircle.homeomorphCircle').mp rcc8ConnectedComplete_angle

end Geospatial
