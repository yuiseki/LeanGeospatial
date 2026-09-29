import LeanGeospatial.CompositionTable.Embedding
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# 2-manifolds are complete for the RCC8 table

A topological 2-manifold is a space `M` with charts to the plane: a
`ChartedSpace (EuclideanSpace ℝ (Fin 2)) M`, the model space being the type
LeanGeospatial calls `Point2D`. If `M` is Hausdorff and nonempty, the table is
complete for it (`rcc8Complete_of_chartedSpace`): every weak composition in
`M` is exactly the plane's.

The proof is local. The target of a chart is a nonempty open subset of the
plane; a small disk inside it is homeomorphic to the whole plane
(`exists_isOpenEmbedding_into`), and the chart's inverse carries that disk
into `M` as an open embedding. `rcc8Complete_of_isOpenEmbedding` does the
rest. The same argument gives every nonempty open subset of the plane
(`rcc8Complete_of_isOpen`).

Both hypotheses are needed by the argument. The empty space realises no
relation at all. Without Hausdorffness the image of a compact area need not be
closed, and it can fail to be an area.
-/

namespace Geospatial

open Topology

/-- Every nonempty open subset of the plane contains an open copy of the whole
plane: a small disk. -/
theorem exists_isOpenEmbedding_into {U : Set Point2D} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ g : Point2D → Point2D, IsOpenEmbedding g ∧ Set.range g ⊆ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let affine : Point2D ≃ₜ Point2D :=
    (Homeomorph.smulOfNeZero ε hε.ne').trans (Homeomorph.addLeft x)
  refine ⟨fun y => affine (Homeomorph.unitBall y : Point2D), ?_, ?_⟩
  · exact affine.isOpenEmbedding.comp
      (Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp Homeomorph.unitBall.isOpenEmbedding)
  · rintro _ ⟨y, rfl⟩
    apply hball
    have hy := (Homeomorph.unitBall y).2
    rw [Metric.mem_ball, dist_zero_right] at hy
    show x + ε • (Homeomorph.unitBall y : Point2D) ∈ Metric.ball x ε
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
    exact mul_lt_of_lt_one_right hε hy

/-- The table is complete for every nonempty open subset of the plane. -/
theorem rcc8Complete_of_isOpen {U : Set Point2D} (hU : IsOpen U) (hne : U.Nonempty) :
    RCC8Complete U := by
  obtain ⟨g, hg, hrange⟩ := exists_isOpenEmbedding_into hU hne
  refine rcc8Complete_of_isOpenEmbedding (f := fun y => (⟨g y, hrange ⟨y, rfl⟩⟩ : U)) ?_
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hg.continuous.subtype_mk _) (fun a b h => hg.injective (congrArg Subtype.val h)) ?_
  intro V hV
  have himg : (fun y => (⟨g y, hrange ⟨y, rfl⟩⟩ : U)) '' V = Subtype.val ⁻¹' (g '' V) := by
    ext ⟨z, hz⟩
    simp only [Set.mem_image, Set.mem_preimage, Subtype.mk.injEq]
  rw [himg]
  exact (hg.isOpenMap V hV).preimage continuous_subtype_val

/-- The table is complete for every nonempty Hausdorff 2-manifold. -/
theorem rcc8Complete_of_chartedSpace (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [T2Space M] [Nonempty M] : RCC8Complete M := by
  obtain ⟨x⟩ := ‹Nonempty M›
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  obtain ⟨g, hg, hrange⟩ :=
    exists_isOpenEmbedding_into e.open_target ⟨e x, mem_chart_target _ x⟩
  refine rcc8Complete_of_isOpenEmbedding (f := e.symm ∘ g) ?_
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact e.continuousOn_symm.comp_continuous hg.continuous fun y => hrange ⟨y, rfl⟩
  · intro a b h
    exact hg.injective (e.symm.injOn (hrange ⟨a, rfl⟩) (hrange ⟨b, rfl⟩) h)
  · intro V hV
    rw [Set.image_comp]
    exact e.symm.isOpen_image_of_subset_source (hg.isOpenMap V hV)
      ((Set.image_subset_range g V).trans hrange)

end Geospatial
