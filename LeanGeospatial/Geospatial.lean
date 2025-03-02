import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Group.Basic

namespace Geospatial

  /-- 2次元の点の定義 -/
  structure Point2D where
    x : ℝ
    y : ℝ

  -- Point2D型のInhabitedインスタンスを定義
  instance : Inhabited Point2D where
    default := { x := 0, y := 0 }

  /-- 2点間のユークリッド距離を定義 -/
  noncomputable def distance (p q : Point2D) : ℝ :=
    Real.sqrt ((p.x - q.x) ^ 2 + (p.y - q.y) ^ 2)

  /-- 2点の中点を返す -/
  noncomputable def midpoint (p q : Point2D) : Point2D :=
    { x := (p.x + q.x) / 2, y := (p.y + q.y) / 2 }

  /-- 複数の点からなるポリラインの定義 -/
  def Polyline := List Point2D

  /-- ポリゴンの定義（頂点のリスト） -/
  structure Polygon where
    vertices : List Point2D

  /--
    ポリゴンが定める領域を抽象的に表す関数。
    ここでは、具体的な実装は後で検討するため、定数として宣言。
  -/
  axiom region : Polygon → Set Point2D

  /-- ポリゴンが点 p を含む（p がその領域に属する）という性質 -/
  def contains (poly : Polygon) (p : Point2D) : Prop :=
    p ∈ region poly

  /--
    ポリゴンの境界と内部の概念も抽象的に定義。
    これらは後で、具体的なトポロジー的性質や計算方法に基づいて実装することも可能。
  -/
  axiom boundary : Polygon → Set Point2D
  axiom interior : Polygon → Set Point2D

  /--
    2つのポリゴンが「隣接する」とは、境界部分に交わりがありながらも内部同士は交わらないという性質を表す。
  -/
  def adjacent (poly₁ poly₂ : Polygon) : Prop :=
    (boundary poly₁ ∩ boundary poly₂ ≠ ∅) ∧ (interior poly₁ ∩ interior poly₂ = ∅)

  /-- 任意の2点に対して、distance は対称であることの証明。 -/
  theorem distance_sym (p q : Point2D) : distance p q = distance q p := by
    unfold distance
    have h1 : (p.x - q.x) ^ 2 = (q.x - p.x) ^ 2 := by ring
    have h2 : (p.y - q.y) ^ 2 = (q.y - p.y) ^ 2 := by ring
    rw [h1, h2]

  /--
    ポリゴンの面積を、shoelace 公式により計算する。
    NOTE: この実装は、頂点のリストが空でないこと、およびポリゴンが単純で頂点が順に並んでいるという仮定に依存します。
  -/
  noncomputable def polygonArea (poly : Polygon) : ℝ :=
    let pts := poly.vertices
    match pts with
    | []    => 0
    | _     =>
      let first := pts.head!
      let pts' := pts ++ [first]  -- 最初の点を末尾に追加
      let pairs := pts'.zip pts'.tail  -- 隣接する点のペアのリスト
      let sum := pairs.foldl (fun acc ⟨p, q⟩ => acc + (p.x * q.y - p.y * q.x)) (0 : ℝ)
      abs sum / 2

end Geospatial
