import Lean
import Lean.Elab.Command
import LeanGeospatial.Geospatial

open Geospatial

noncomputable section

-- distance のテスト
def p1 : Point2D := { x := 0, y := 0 }
def p2 : Point2D := { x := 10, y := 10 }

def expected_distance : Real := 5

/-- info: |distance p1 p2 - expected_distance| < 1e-3 -/
#guard_msgs (info) in #reduce abs (distance p1 p2 - expected_distance) < 0.001

-- midpoint のテスト
def expected_midpoint : Point2D := { x := 5, y := 5 }

/--
info: |(Geospatial.midpoint p1 p2).x - expected_midpoint.x| + |(Geospatial.midpoint p1 p2).y - expected_midpoint.y| < 1e-3
-/
#guard_msgs (info) in #reduce abs ((midpoint p1 p2).x - expected_midpoint.x) + abs ((midpoint p1 p2).y - expected_midpoint.y) < 0.001

-- distance_sym のテスト

/-- info: distance_sym p1 p2 -/
#guard_msgs (info) in #reduce (distance_sym p1 p2)

-- polygonArea のテスト

def poly : Polygon := { vertices := [{ x := 0, y := 0 }, { x := 10, y := 0 }, { x := 10, y := 10 }, { x := 0, y := 10 }] }

def expected_area : Real := 50

/-- info: |polygonArea poly - expected_area| < 1e-3 -/
#guard_msgs (info) in #reduce abs (polygonArea poly - expected_area) < 0.001

end
