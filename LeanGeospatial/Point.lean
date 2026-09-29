import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Points in the plane

The plane is Mathlib's Euclidean plane `EuclideanSpace ℝ (Fin 2)`, the same
type that LeanGeodesy calls `E2`, so a point produced by a LeanGeodesy map
projection is directly a point here. Its topology and metric are Mathlib's.

The coordinates are real numbers in an abstract Cartesian plane. No coordinate
reference system is attached: "distance" here is plain Euclidean distance, not a
distance on the Earth.
-/

namespace Geospatial

/-- A point in the plane: Mathlib's `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Point2D := EuclideanSpace ℝ (Fin 2)

/-- `Point2D` unfolds, at reducible transparency, to the type LeanGeodesy
calls `E2`. -/
example : Point2D = EuclideanSpace ℝ (Fin 2) := by with_reducible rfl

namespace Point2D

/-- The point with coordinates `(x, y)`. -/
def mk (x y : ℝ) : Point2D := !₂[x, y]

/-- The first coordinate. -/
def x (p : Point2D) : ℝ := p 0

/-- The second coordinate. -/
def y (p : Point2D) : ℝ := p 1

@[simp] theorem x_mk (a b : ℝ) : (mk a b).x = a := rfl

@[simp] theorem y_mk (a b : ℝ) : (mk a b).y = b := rfl

/-- Two points are equal when their coordinates are. -/
@[ext] theorem ext {p q : Point2D} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  ext i
  fin_cases i
  · exact hx
  · exact hy

@[simp] theorem mk_x_y (p : Point2D) : mk p.x p.y = p :=
  ext rfl rfl

@[simp] theorem mk.injEq (a b c d : ℝ) : (mk a b = mk c d) = (a = c ∧ b = d) := by
  apply propext
  constructor
  · intro h
    exact ⟨congrArg x h, congrArg y h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end Point2D

/-- Euclidean distance between two points: Mathlib's `dist` on the plane. -/
noncomputable def distance (p q : Point2D) : ℝ :=
  dist p q

/-- The distance in coordinates. -/
theorem distance_eq (p q : Point2D) :
    distance p q = Real.sqrt ((p.x - q.x) ^ 2 + (p.y - q.y) ^ 2) := by
  rw [distance, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs]
  rfl

/-- The midpoint of two points. -/
noncomputable def midpoint (p q : Point2D) : Point2D :=
  Point2D.mk ((p.x + q.x) / 2) ((p.y + q.y) / 2)

theorem distance_sym (p q : Point2D) : distance p q = distance q p :=
  dist_comm p q

theorem distance_nonneg (p q : Point2D) : 0 ≤ distance p q :=
  dist_nonneg

theorem distance_self (p : Point2D) : distance p p = 0 :=
  dist_self p

end Geospatial
