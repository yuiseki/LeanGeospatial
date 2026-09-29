import LeanGeospatial.Polygon
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Topology of regions

`Point2D` is Mathlib's `EuclideanSpace ℝ (Fin 2)` and carries Mathlib's
topology, the usual Euclidean topology of the plane. `Point2D.homeomorphProd`
records that it is the same space as the coordinate pair `(x, y)` in `ℝ × ℝ`
with the product topology.

With that in place, a region's interior, closure and boundary are Mathlib's
`interior`, `closure` and `frontier`. Nothing is postulated. `boundary` and
`Touches` are defined for sets in any topological space; only the rectangles
at the end are about the plane.

`Touches` is the point-set definition: the regions share a point, but their
interiors share none. It is not the DE-9IM matrix.
-/

namespace Geospatial

/-- The coordinates of a point as a pair. -/
def Point2D.toProd (p : Point2D) : ℝ × ℝ := (p.x, p.y)

@[fun_prop] theorem Point2D.continuous_x : Continuous Point2D.x :=
  PiLp.continuous_apply 2 _ 0

@[fun_prop] theorem Point2D.continuous_y : Continuous Point2D.y :=
  PiLp.continuous_apply 2 _ 1

/-- Building a point from continuously varying coordinates is continuous. -/
@[fun_prop] theorem Point2D.continuous_mk {α : Type*} [TopologicalSpace α] {f g : α → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => Point2D.mk (f a) (g a) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact hf
  · exact hg

/-- `Point2D` and `ℝ × ℝ` are the same topological space. -/
def Point2D.homeomorphProd : Point2D ≃ₜ ℝ × ℝ where
  toFun := Point2D.toProd
  invFun q := Point2D.mk q.1 q.2
  left_inv p := Point2D.mk_x_y p
  right_inv _ := rfl
  continuous_toFun := Point2D.continuous_x.prodMk Point2D.continuous_y
  continuous_invFun := Point2D.continuous_mk continuous_fst continuous_snd

@[simp] theorem Point2D.homeomorphProd_apply (p : Point2D) :
    Point2D.homeomorphProd p = (p.x, p.y) := rfl

@[simp] theorem Point2D.homeomorphProd_symm_apply (q : ℝ × ℝ) :
    Point2D.homeomorphProd.symm q = Point2D.mk q.1 q.2 := rfl

section General

variable {α : Type*} [TopologicalSpace α]

/-! ## Interior, closure, boundary -/

/-- The boundary of a region: Mathlib's `frontier` under its GIS name. -/
abbrev boundary (A : Set α) : Set α := frontier A

/-- The boundary is what the closure adds to the interior. -/
theorem boundary_eq (A : Set α) : boundary A = closure A \ interior A := rfl

theorem isClosed_boundary (A : Set α) : IsClosed (boundary A) :=
  isClosed_frontier

/-- The interior and the boundary never overlap. -/
theorem interior_disjoint_boundary (A : Set α) :
    Geospatial.Disjoint (interior A) (boundary A) := by
  unfold Geospatial.Disjoint
  rw [boundary_eq, Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp, -, hp'⟩
  exact hp' hp

/-- A closed region is its interior together with its boundary. -/
theorem interior_union_boundary_of_isClosed {A : Set α} (hA : IsClosed A) :
    interior A ∪ boundary A = A := by
  rw [boundary_eq, hA.closure_eq, Set.union_sdiff_cancel interior_subset]

/-! ## Touches -/

/-- `A` touches `B` when they share a point but their interiors share none. -/
def Touches (A B : Set α) : Prop :=
  Intersects A B ∧ Geospatial.Disjoint (interior A) (interior B)

variable {A B : Set α}

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
  have key : ∀ {S T : Set α}, closure (interior T) = T →
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

end General

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
    Set.mem_Icc, Set.mem_ofPred_eq]
  tauto

theorem openRegion_eq_preimage (r : Rect) :
    r.openRegion =
      Point2D.homeomorphProd ⁻¹' (Set.Ioo r.xmin r.xmax ×ˢ Set.Ioo r.ymin r.ymax) := by
  ext p
  simp only [openRegion, Set.mem_preimage, Point2D.homeomorphProd_apply, Set.mem_prod,
    Set.mem_Ioo, Set.mem_ofPred_eq]
  tauto

theorem isClosed_toRegion (r : Rect) : IsClosed r.toRegion := by
  rw [toRegion_eq_preimage]
  exact (isClosed_Icc.prod isClosed_Icc).preimage Point2D.homeomorphProd.continuous

/-- A closed rectangle is compact. -/
theorem isCompact_toRegion (r : Rect) : IsCompact r.toRegion := by
  rw [toRegion_eq_preimage]
  exact Point2D.homeomorphProd.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)

theorem closure_toRegion (r : Rect) : closure r.toRegion = r.toRegion :=
  r.isClosed_toRegion.closure_eq

theorem interior_toRegion (r : Rect) : interior r.toRegion = r.openRegion := by
  rw [toRegion_eq_preimage, ← Point2D.homeomorphProd.preimage_interior,
    interior_prod_eq, interior_Icc, interior_Icc, openRegion_eq_preimage]

theorem boundary_toRegion (r : Rect) :
    boundary r.toRegion = r.toRegion \ r.openRegion := by
  rw [boundary_eq, closure_toRegion, interior_toRegion]

/-- A rectangle lies within the interior of another when its bounds lie
strictly inside the other's. -/
theorem within_interior_of_bounds {r s : Rect}
    (hx₁ : s.xmin < r.xmin) (hx₂ : r.xmax < s.xmax)
    (hy₁ : s.ymin < r.ymin) (hy₂ : r.ymax < s.ymax) :
    Within r.toRegion (interior s.toRegion) := by
  rw [interior_toRegion]
  rintro p ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨hx₁.trans_le h₁, h₂.trans_lt hx₂, hy₁.trans_le h₃, h₄.trans_lt hy₂⟩

/-- Two rectangles differ when the second's lower-left corner lies outside
the first. -/
theorem toRegion_ne_of_xmin_lt {r s : Rect} (hx : s.xmin < r.xmin)
    (hsx : s.xmin ≤ s.xmax) (hsy : s.ymin ≤ s.ymax) :
    r.toRegion ≠ s.toRegion := by
  intro h
  have hp : Point2D.mk s.xmin s.ymin ∈ s.toRegion :=
    ⟨le_refl _, hsx, le_refl _, hsy⟩
  rw [← h] at hp
  exact absurd hp.1 (not_le.mpr hx)

end Rect

end Geospatial
