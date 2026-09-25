import LeanGeospatial.Region

/-!
# Polygons and rectangles

A `Polygon` is data: a list of vertices. It is kept separate from `Region`,
which is meaning: a set of points. Turning an arbitrary polygon into the set of
points it encloses needs a point-in-polygon rule (and a decision about
self-intersecting rings), which this library does not provide yet. So a polygon
only has a computed area here, not a region.

A `Rect` (an axis-aligned rectangle) is the one shape whose region we define
exactly, because its interior is a plain conjunction of inequalities.
-/

namespace Geospatial

noncomputable section

/-- A polygon given by its vertices in ring order. The closing edge from the
last vertex back to the first is implicit. -/
structure Polygon where
  vertices : List Point2D

/-- The z-component of the cross product of `p` and `q` seen as vectors. -/
def cross (p q : Point2D) : ℝ := p.x * q.y - p.y * q.x

/-- Twice the signed area of a ring (shoelace formula). Positive for a
counter-clockwise ring, negative for a clockwise one. -/
def signedArea2 (vs : List Point2D) : ℝ :=
  ((vs.zip (vs.rotate 1)).map fun e => cross e.1 e.2).sum

/-- The area of a polygon by the shoelace formula. Correct for simple
(non-self-intersecting) polygons in either orientation; for a
self-intersecting ring it is only the absolute signed area. -/
def polygonArea (poly : Polygon) : ℝ := |signedArea2 poly.vertices| / 2

theorem polygonArea_nonneg (poly : Polygon) : 0 ≤ polygonArea poly := by
  unfold polygonArea
  positivity

@[simp] theorem polygonArea_nil : polygonArea ⟨[]⟩ = 0 := by
  simp [polygonArea, signedArea2]

/-- An axis-aligned rectangle `[xmin, xmax] × [ymin, ymax]`, boundary included. -/
structure Rect where
  xmin : ℝ
  xmax : ℝ
  ymin : ℝ
  ymax : ℝ

namespace Rect

/-- The points covered by the rectangle, boundary included. -/
def toRegion (r : Rect) : Region :=
  {p | r.xmin ≤ p.x ∧ p.x ≤ r.xmax ∧ r.ymin ≤ p.y ∧ p.y ≤ r.ymax}

/-- The rectangle's corners, counter-clockwise from the lower left. -/
def toPolygon (r : Rect) : Polygon :=
  ⟨[⟨r.xmin, r.ymin⟩, ⟨r.xmax, r.ymin⟩, ⟨r.xmax, r.ymax⟩, ⟨r.xmin, r.ymax⟩]⟩

/-- A rectangle lies within another when its bounds lie inside the other's. -/
theorem within_of_bounds {r s : Rect}
    (hx₁ : s.xmin ≤ r.xmin) (hx₂ : r.xmax ≤ s.xmax)
    (hy₁ : s.ymin ≤ r.ymin) (hy₂ : r.ymax ≤ s.ymax) :
    Within r.toRegion s.toRegion := by
  rintro p ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨hx₁.trans h₁, h₂.trans hx₂, hy₁.trans h₃, h₄.trans hy₂⟩

/-- The shoelace area of a rectangle is width times height. -/
theorem area_toPolygon (r : Rect) :
    polygonArea r.toPolygon = |(r.xmax - r.xmin) * (r.ymax - r.ymin)| := by
  simp only [polygonArea, signedArea2, toPolygon, cross, List.rotate]
  norm_num
  rw [show ∀ a : ℝ, |a| / 2 = |a / 2| from fun a => by
    rw [abs_div, abs_two]]
  congr 1
  ring

end Rect

end

end Geospatial
