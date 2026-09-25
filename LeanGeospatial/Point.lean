import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Points in the plane

The coordinates are real numbers in an abstract Cartesian plane. No coordinate
reference system is attached: "distance" here is plain Euclidean distance, not a
distance on the Earth.
-/

namespace Geospatial

/-- A point in the plane. -/
@[ext]
structure Point2D where
  x : ℝ
  y : ℝ

instance : Inhabited Point2D where
  default := { x := 0, y := 0 }

/-- Euclidean distance between two points. -/
noncomputable def distance (p q : Point2D) : ℝ :=
  Real.sqrt ((p.x - q.x) ^ 2 + (p.y - q.y) ^ 2)

/-- The midpoint of two points. -/
noncomputable def midpoint (p q : Point2D) : Point2D :=
  { x := (p.x + q.x) / 2, y := (p.y + q.y) / 2 }

theorem distance_sym (p q : Point2D) : distance p q = distance q p := by
  unfold distance
  ring_nf

theorem distance_nonneg (p q : Point2D) : 0 ≤ distance p q :=
  Real.sqrt_nonneg _

theorem distance_self (p : Point2D) : distance p p = 0 := by
  simp [distance]

end Geospatial
