import LeanGeospatial.Polygon
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Topology of regions

`Point2D` gets the topology it inherits from the coordinate pair `(x, y)`, that
is the product topology of `ℝ × ℝ`, which is the usual Euclidean topology of
the plane. `Point2D.homeomorphProd` records that the two spaces are the same.

With that in place, a region's interior, closure and boundary are Mathlib's
`interior`, `closure` and `frontier`. Nothing is postulated.

`Touches` is the point-set definition: the regions share a point, but their
interiors share none. It is not the DE-9IM matrix.
-/

namespace Geospatial

/-- The coordinates of a point as a pair. -/
def Point2D.toProd (p : Point2D) : ℝ × ℝ := (p.x, p.y)

/-- The plane's topology, pulled back from `ℝ × ℝ` along the coordinates. -/
instance : TopologicalSpace Point2D :=
  TopologicalSpace.induced Point2D.toProd inferInstance

/-- `Point2D` and `ℝ × ℝ` are the same topological space. -/
def Point2D.homeomorphProd : Point2D ≃ₜ ℝ × ℝ where
  toFun := Point2D.toProd
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_id

@[simp] theorem Point2D.homeomorphProd_apply (p : Point2D) :
    Point2D.homeomorphProd p = (p.x, p.y) := rfl

theorem Point2D.continuous_x : Continuous Point2D.x :=
  Point2D.homeomorphProd.continuous.fst

theorem Point2D.continuous_y : Continuous Point2D.y :=
  Point2D.homeomorphProd.continuous.snd

/-! ## Interior, closure, boundary -/

/-- The boundary of a region: Mathlib's `frontier` under its GIS name. -/
abbrev boundary (A : Region) : Region := frontier A

/-- The boundary is what the closure adds to the interior. -/
theorem boundary_eq (A : Region) : boundary A = closure A \ interior A := rfl

theorem isClosed_boundary (A : Region) : IsClosed (boundary A) :=
  isClosed_frontier

/-- The interior and the boundary never overlap. -/
theorem interior_disjoint_boundary (A : Region) :
    Geospatial.Disjoint (interior A) (boundary A) := by
  unfold Geospatial.Disjoint
  rw [boundary_eq, Set.eq_empty_iff_forall_not_mem]
  rintro p ⟨hp, -, hp'⟩
  exact hp' hp

/-- A closed region is its interior together with its boundary. -/
theorem IsClosed.interior_union_boundary {A : Region} (hA : IsClosed A) :
    interior A ∪ boundary A = A := by
  rw [boundary_eq, hA.closure_eq, Set.union_diff_cancel interior_subset]

/-! ## Touches -/

/-- `A` touches `B` when they share a point but their interiors share none. -/
def Touches (A B : Region) : Prop :=
  Intersects A B ∧ Geospatial.Disjoint (interior A) (interior B)

variable {A B : Region}

theorem Touches.intersects (h : Touches A B) : Intersects A B := h.1

theorem Touches.not_intersects_interior (h : Touches A B) :
    ¬ Intersects (interior A) (interior B) :=
  h.2.not_intersects

theorem touches_symm (h : Touches A B) : Touches B A :=
  ⟨intersects_symm h.1, disjoint_symm h.2⟩

theorem touches_comm : Touches A B ↔ Touches B A :=
  ⟨touches_symm, touches_symm⟩

/-- Among regions that intersect, touching is exactly the case where the
interiors do not meet. -/
theorem touches_iff_of_intersects (h : Intersects A B) :
    Touches A B ↔ ¬ Intersects (interior A) (interior B) :=
  ⟨Touches.not_intersects_interior, fun h' => ⟨h, disjoint_iff_not_intersects.mpr h'⟩⟩

/-- For regions that are the closure of their interior (no dangling lines or
isolated points), every shared point of touching regions lies on both
boundaries. For areas, use `RegularClosedRegion.inter_subset_boundary_of_touches`,
which needs no hypotheses. -/
theorem Touches.inter_subset_boundary
    (hA : closure (interior A) = A) (hB : closure (interior B) = B)
    (h : Touches A B) :
    A ∩ B ⊆ boundary A ∩ boundary B := by
  have hA' : IsClosed A := hA ▸ isClosed_closure
  have hB' : IsClosed B := hB ▸ isClosed_closure
  have key : ∀ {S T : Region}, closure (interior T) = T →
      Geospatial.Disjoint (interior S) (interior T) → ∀ p ∈ T, p ∉ interior S := by
    intro S T hT hST p hpT hpS
    have hp : p ∈ closure (interior T) := hT.symm ▸ hpT
    obtain ⟨q, hqS, hqT⟩ :=
      mem_closure_iff.mp hp (interior S) isOpen_interior hpS
    have : q ∈ interior S ∩ interior T := ⟨hqS, hqT⟩
    rw [hST] at this
    exact this
  rintro p ⟨hpA, hpB⟩
  refine ⟨?_, ?_⟩
  · rw [boundary_eq, hA'.closure_eq]
    exact ⟨hpA, key hB h.2 p hpB⟩
  · rw [boundary_eq, hB'.closure_eq]
    exact ⟨hpB, key hA (disjoint_symm h.2) p hpA⟩

/-! ## Rectangles -/

namespace Rect

/-- The open rectangle: the strict inequalities. -/
def openRegion (r : Rect) : Region :=
  {p | r.xmin < p.x ∧ p.x < r.xmax ∧ r.ymin < p.y ∧ p.y < r.ymax}

theorem toRegion_eq_preimage (r : Rect) :
    r.toRegion =
      Point2D.homeomorphProd ⁻¹' (Set.Icc r.xmin r.xmax ×ˢ Set.Icc r.ymin r.ymax) := by
  ext p
  simp only [toRegion, Set.mem_preimage, Point2D.homeomorphProd_apply, Set.mem_prod,
    Set.mem_Icc, Set.mem_setOf_eq]
  tauto

theorem openRegion_eq_preimage (r : Rect) :
    r.openRegion =
      Point2D.homeomorphProd ⁻¹' (Set.Ioo r.xmin r.xmax ×ˢ Set.Ioo r.ymin r.ymax) := by
  ext p
  simp only [openRegion, Set.mem_preimage, Point2D.homeomorphProd_apply, Set.mem_prod,
    Set.mem_Ioo, Set.mem_setOf_eq]
  tauto

theorem isClosed_toRegion (r : Rect) : IsClosed r.toRegion := by
  rw [toRegion_eq_preimage]
  exact (isClosed_Icc.prod isClosed_Icc).preimage Point2D.homeomorphProd.continuous

theorem closure_toRegion (r : Rect) : closure r.toRegion = r.toRegion :=
  r.isClosed_toRegion.closure_eq

theorem interior_toRegion (r : Rect) : interior r.toRegion = r.openRegion := by
  rw [toRegion_eq_preimage, ← Point2D.homeomorphProd.preimage_interior,
    interior_prod_eq, interior_Icc, interior_Icc, openRegion_eq_preimage]

theorem boundary_toRegion (r : Rect) :
    boundary r.toRegion = r.toRegion \ r.openRegion := by
  rw [boundary_eq, closure_toRegion, interior_toRegion]

end Rect

end Geospatial
