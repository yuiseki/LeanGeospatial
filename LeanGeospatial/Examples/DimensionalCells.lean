import LeanGeospatial.DE9IM.Dimension
import LeanGeospatial.RCC8Witnesses

/-!
# Dimensioned DE-9IM cells on small examples

The interior-interior cell `II` for four pairs, one of each value:

| Pair | `II` | Value |
| --- | --- | --- |
| a point and the same point | the point | `0` |
| two overlapping squares | an open square | `2` |
| `(0,0)–(2,0)` and `(1,-1)–(1,1)` | the crossing point `(1,0)` | `0` |
| `(0,0)–(2,0)` and `(1,0)–(3,0)` | the open segment between `x = 1` and `x = 2` | `1` |

In the crossing case, Mathlib's topology alone would say nothing: both
segments have empty topological interior. The Simple Features interiors
(the segments without their end points) are what meet.
-/

namespace Geospatial.Examples.DimensionalCells

open Geospatial Geospatial.DE9IM

noncomputable section

/-! ## Points -/

theorem point_point_II (p : Point2D) : matrix (.point p) (.point p) .I .I = .d0 :=
  DimValue.of_eq (describes_d0_of_subset_singleton ⟨rfl, rfl⟩ Set.inter_subset_left)

/-! ## Areas -/

def sqA : RegularClosedRegion := Rect.area ⟨0, 2, 0, 2⟩ (by norm_num)
def sqC : RegularClosedRegion := Rect.area ⟨1, 3, 0, 2⟩ (by norm_num)

theorem squares_II : matrix (.area sqA) (.area sqC) .I .I = .d2 := by
  rcases area_II_value sqA sqC with h | h
  · exfalso
    rw [matrix, DimValue.of_eq_F_iff, Set.eq_empty_iff_forall_not_mem] at h
    apply h ⟨3 / 2, 1⟩
    show _ ∈ interior (sqA : Region) ∧ _ ∈ interior (sqC : Region)
    rw [sqA, sqC, Rect.interior_area, Rect.interior_area]
    constructor <;>
      · show _ < _ ∧ _ < _ ∧ _ < _ ∧ _ < _
        norm_num
  · exact h

/-! ## Lines -/

def o : Point2D := ⟨0, 0⟩
def e2 : Point2D := ⟨2, 0⟩
def lineX : LineString := LineString.seg o e2 (by simp [o, e2])

theorem mem_lineX_interior {p : Point2D} (h : p ∈ (Geometry.line lineX).stratum .I) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, p = ⟨2 * t, 0⟩ := by
  change p ∈ lineX.interior at h
  rw [lineX, LineString.seg_interior] at h
  obtain ⟨⟨t, ht, rfl⟩, -⟩ := h
  exact ⟨t, ht, by simp [Point2D.lerp, o, e2]; ring⟩

/-- `(0,0)–(2,0)` and `(1,-1)–(1,1)` cross at `(1,0)`. -/
def lineY : LineString := LineString.seg ⟨1, -1⟩ ⟨1, 1⟩ (by norm_num [Point2D.ext_iff])

theorem crossing_II : matrix (.line lineX) (.line lineY) .I .I = .d0 := by
  apply DimValue.of_eq
  apply describes_d0_of_subset_singleton (q := ⟨1, 0⟩)
  · refine ⟨?_, ?_⟩
    · show _ ∈ lineX.interior
      rw [lineX, LineString.seg_interior]
      refine ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
      · norm_num [Point2D.lerp, o, e2]
      · simp [o, e2, Point2D.ext_iff]
    · show _ ∈ lineY.interior
      rw [lineY, LineString.seg_interior]
      refine ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
      · norm_num [Point2D.lerp]
      · simp [Point2D.ext_iff]
  · rintro p ⟨hX, hY⟩
    obtain ⟨t, -, rfl⟩ := mem_lineX_interior hX
    change _ ∈ lineY.interior at hY
    rw [lineY, LineString.seg_interior] at hY
    obtain ⟨⟨s, -, hs⟩, -⟩ := hY
    simp only [Point2D.lerp, Point2D.mk.injEq] at hs
    obtain ⟨h₁, h₂⟩ := hs
    show (⟨2 * t, 0⟩ : Point2D) = ⟨1, 0⟩
    congr 1
    linarith

/-! ## Collinear lines -/

/-- `(1,0)–(3,0)`, overlapping `lineX` between `x = 1` and `x = 2`. -/
def lineX' : LineString := LineString.seg ⟨1, 0⟩ ⟨3, 0⟩ (by simp)

/-- A set on a horizontal line has no interior in the plane. -/
theorem interior_eq_empty_of_horizontal {S : Region} {c : ℝ} (h : ∀ p ∈ S, p.y = c) :
    interior S = ∅ := by
  have hsub : S ⊆ Point2D.homeomorphProd ⁻¹' (Set.univ ×ˢ {c}) := fun p hp =>
    ⟨trivial, h p hp⟩
  apply Set.eq_empty_of_subset_empty
  refine (interior_mono hsub).trans ?_
  rw [← Point2D.homeomorphProd.preimage_interior, interior_prod_eq, interior_singleton,
    Set.prod_empty, Set.preimage_empty]

theorem collinear_II : matrix (.line lineX) (.line lineX') .I .I = .d1 := by
  apply DimValue.of_eq
  refine ⟨interior_eq_empty_of_horizontal (c := 0) ?_, ?_⟩
  · rintro p ⟨hX, -⟩
    obtain ⟨t, -, rfl⟩ := mem_lineX_interior hX
    rfl
  · -- The arc from (5/4, 0) to (7/4, 0).
    refine ⟨fun t => ⟨5 / 4 + t / 2, 0⟩, ?_, ?_, ?_⟩
    · apply Continuous.continuousOn
      apply continuous_induced_rng.mpr
      show Continuous fun t : ℝ => ((5 / 4 + t / 2 : ℝ), (0 : ℝ))
      fun_prop
    · intro a _ b _ hab
      simp only [Point2D.mk.injEq] at hab
      linarith [hab.1]
    · rintro p ⟨t, ⟨ht₀, ht₁⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show _ ∈ lineX.interior
        rw [lineX, LineString.seg_interior]
        refine ⟨⟨(5 / 4 + t / 2) / 2, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
        · simp only [Point2D.lerp, o, e2, Point2D.mk.injEq]
          constructor <;> ring
        · simp only [o, e2, Set.mem_insert_iff, Set.mem_singleton_iff, Point2D.mk.injEq]
          rintro (⟨h, -⟩ | ⟨h, -⟩) <;> linarith
      · show _ ∈ lineX'.interior
        rw [lineX', LineString.seg_interior]
        refine ⟨⟨(1 / 4 + t / 2) / 2, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
        · simp only [Point2D.lerp, Point2D.mk.injEq]
          constructor <;> ring
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Point2D.mk.injEq]
          rintro (⟨h, -⟩ | ⟨h, -⟩) <;> linarith

end

end Geospatial.Examples.DimensionalCells
