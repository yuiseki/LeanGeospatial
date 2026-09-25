import LeanGeospatial.Polygon

/-!
# Distance and area on concrete coordinates

These replace the old `#reduce` checks, which only printed the claim back and
so passed even with wrong expected values (5 for the distance, 50 for the area).
Each check here is a theorem: if the value were wrong, `lake build` would fail.
-/

namespace Geospatial.Examples.Measurement

open Geospatial

noncomputable section

def p1 : Point2D := ⟨0, 0⟩
def p2 : Point2D := ⟨10, 10⟩

/-- The distance from `(0,0)` to `(10,10)` is `10√2`. -/
theorem distance_p1_p2 : distance p1 p2 = 10 * Real.sqrt 2 := by
  rw [distance, p1, p2]
  norm_num
  rw [show (200 : ℝ) = 10 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

/-- The old expected value was wrong. -/
theorem distance_p1_p2_ne_five : distance p1 p2 ≠ 5 := by
  rw [distance_p1_p2]
  intro h
  have h2 : Real.sqrt 2 = 1 / 2 := by linarith
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [h2] at this
  norm_num at this

theorem midpoint_p1_p2 : midpoint p1 p2 = ⟨5, 5⟩ := by
  ext <;> simp [midpoint, p1, p2] <;> norm_num

/-- The 10 × 10 square with its lower-left corner at the origin. -/
def square : Polygon := ⟨[⟨0, 0⟩, ⟨10, 0⟩, ⟨10, 10⟩, ⟨0, 10⟩]⟩

theorem area_square : polygonArea square = 100 := by
  simp [polygonArea, signedArea2, square, cross, List.rotate]
  norm_num

/-- The old expected value was wrong. -/
theorem area_square_ne_fifty : polygonArea square ≠ 50 := by
  rw [area_square]
  norm_num

/-- Listing the same square clockwise gives the same area. -/
theorem area_square_clockwise :
    polygonArea ⟨[⟨0, 0⟩, ⟨0, 10⟩, ⟨10, 10⟩, ⟨10, 0⟩]⟩ = 100 := by
  simp [polygonArea, signedArea2, cross, List.rotate]
  norm_num

/-- The same square as a `Rect`, via the general rectangle area lemma. -/
theorem area_square_rect : polygonArea (Rect.toPolygon ⟨0, 10, 0, 10⟩) = 100 := by
  rw [Rect.area_toPolygon]
  norm_num

end

end Geospatial.Examples.Measurement
