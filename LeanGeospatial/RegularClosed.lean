import LeanGeospatial.Topology
import Mathlib.Data.SetLike.Basic

/-!
# Regular closed regions

A `Region` is any set of points, including a lone point, a line, or a square
with a stray whisker attached. Geographic areas (districts, parcels, lakes) are
meant to be none of those: they are the closure of their own interior. Such a
set is called regular closed.

`RegularClosedRegion α` bundles a set in a topological space `α` with a proof
of that property, so the type says which sets are areas. Nothing here needs
the plane except the rectangles at the end; `RegularClosedRegion Point2D` is
the type of areas of the plane. Theorems about areas can then drop the
hypothesis `closure (interior A) = A`, because every value of the type carries
it.

`Region` stays as the type of arbitrary sets. The distinction matters: the
intersection of two touching areas is their shared edge, a `Region` that is
not a `RegularClosedRegion` (`Touches.inter_not_regularClosed`).
-/

namespace Geospatial

variable {α : Type*} [TopologicalSpace α]

/-- A set of `α` that is the closure of its interior: an area of `α`. -/
structure RegularClosedRegion (α : Type*) [TopologicalSpace α] where
  /-- The underlying set of points. -/
  carrier : Set α
  closure_interior_eq' : closure (interior carrier) = carrier

namespace RegularClosedRegion

instance : SetLike (RegularClosedRegion α) α where
  coe := carrier
  coe_injective A B h := by
    cases A
    cases B
    congr

@[simp] theorem coe_mk (s : Set α) (h : closure (interior s) = s) :
    ((⟨s, h⟩ : RegularClosedRegion α) : Set α) = s := rfl

variable (A B : RegularClosedRegion α)

theorem closure_interior_eq : closure (interior (A : Set α)) = A :=
  A.closure_interior_eq'

theorem isClosed : IsClosed (A : Set α) := by
  rw [← A.closure_interior_eq]
  exact isClosed_closure

theorem closure_eq : closure (A : Set α) = A :=
  A.isClosed.closure_eq

theorem boundary_eq : boundary (A : Set α) = (A : Set α) \ interior A := by
  rw [Geospatial.boundary_eq, A.closure_eq]

/-- An area is empty exactly when its interior is. There are no areas made of
boundary alone. -/
theorem nonempty_iff_interior_nonempty :
    (A : Set α).Nonempty ↔ (interior (A : Set α)).Nonempty := by
  constructor
  · intro h
    rw [← A.closure_interior_eq] at h
    exact closure_nonempty_iff.mp h
  · exact fun h => h.mono interior_subset

/-- The empty area. -/
instance : Bot (RegularClosedRegion α) :=
  ⟨⟨∅, by simp⟩⟩

@[simp] theorem coe_bot : ((⊥ : RegularClosedRegion α) : Set α) = ∅ := rfl

/-- The union of two areas is an area. -/
def union : RegularClosedRegion α where
  carrier := A ∪ B
  closure_interior_eq' := by
    apply Set.Subset.antisymm
    · calc closure (interior ((A : Set α) ∪ B))
          ⊆ closure ((A : Set α) ∪ B) := closure_mono interior_subset
        _ = (A : Set α) ∪ B := by rw [closure_union, A.closure_eq, B.closure_eq]
    · calc (A : Set α) ∪ B
          = closure (interior (A : Set α)) ∪ closure (interior (B : Set α)) := by
            rw [A.closure_interior_eq, B.closure_interior_eq]
        _ = closure (interior (A : Set α) ∪ interior (B : Set α)) :=
            closure_union.symm
        _ ⊆ closure (interior ((A : Set α) ∪ B)) :=
            closure_mono (Set.union_subset (interior_mono Set.subset_union_left)
              (interior_mono Set.subset_union_right))

@[simp] theorem coe_union : ((A.union B : RegularClosedRegion α) : Set α) = (A : Set α) ∪ B :=
  rfl

/-! ## Touching areas -/

/-- When two areas touch, every point they share lies on both boundaries. No
hypothesis beyond `Touches` is needed: being an area is part of the type. -/
theorem inter_subset_boundary_of_touches (h : Touches (A : Set α) B) :
    (A : Set α) ∩ B ⊆ boundary (A : Set α) ∩ boundary (B : Set α) :=
  h.inter_subset_boundary A.closure_interior_eq B.closure_interior_eq

/-- A shared point of two touching areas is on the boundary of each. -/
theorem mem_boundary_of_touches {p : α} (h : Touches (A : Set α) B)
    (hpA : p ∈ A) (hpB : p ∈ B) :
    p ∈ boundary (A : Set α) ∧ p ∈ boundary (B : Set α) :=
  A.inter_subset_boundary_of_touches B h ⟨hpA, hpB⟩

end RegularClosedRegion

/-- What two touching regions share has empty interior, so it is never an
area: the shared edge of two districts is a `Set α` but not a
`RegularClosedRegion`. -/
theorem Touches.inter_not_regularClosed {A B : Set α} (h : Touches A B) :
    closure (interior (A ∩ B)) ≠ A ∩ B := by
  intro hAB
  rw [interior_inter, h.2, closure_empty] at hAB
  obtain ⟨p, hp⟩ := h.1
  rw [← hAB] at hp
  exact hp

theorem Touches.not_exists_regularClosed_inter {A B : Set α} (h : Touches A B) :
    ¬ ∃ C : RegularClosedRegion α, (C : Set α) = A ∩ B := by
  rintro ⟨C, hC⟩
  exact h.inter_not_regularClosed (hC ▸ C.closure_interior_eq)

/-! ## Rectangles -/

namespace Rect

/-- A rectangle with positive width and height is the closure of its
interior. -/
theorem closure_interior_toRegion {r : Rect} (hx : r.xmin < r.xmax) (hy : r.ymin < r.ymax) :
    closure (interior r.toRegion) = r.toRegion := by
  rw [toRegion_eq_preimage, ← Point2D.homeomorphProd.preimage_interior,
    ← Point2D.homeomorphProd.preimage_closure, interior_prod_eq, closure_prod_eq,
    closure_interior_Icc hx.ne, closure_interior_Icc hy.ne]

/-- A rectangle with positive width and height, as an area. -/
def toRegularClosed (r : Rect) (hx : r.xmin < r.xmax) (hy : r.ymin < r.ymax) :
    RegularClosedRegion Point2D :=
  ⟨r.toRegion, closure_interior_toRegion hx hy⟩

@[simp] theorem coe_toRegularClosed (r : Rect) (hx : r.xmin < r.xmax)
    (hy : r.ymin < r.ymax) :
    ((r.toRegularClosed hx hy : RegularClosedRegion Point2D) : Region) = r.toRegion := rfl

/-- The positivity conditions are needed: a rectangle of width zero is a line
segment, and a segment is not the closure of its (empty) interior. -/
theorem segment_not_regularClosed :
    closure (interior (⟨0, 0, 0, 1⟩ : Rect).toRegion) ≠ (⟨0, 0, 0, 1⟩ : Rect).toRegion := by
  rw [interior_toRegion]
  have hempty : (⟨0, 0, 0, 1⟩ : Rect).openRegion = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨h₁, h₂, -, -⟩
    exact lt_asymm h₁ h₂
  rw [hempty, closure_empty]
  intro h
  have hp : Point2D.mk 0 0 ∈ (⟨0, 0, 0, 1⟩ : Rect).toRegion := by
    simp only [toRegion, Set.mem_ofPred_eq]
    norm_num
  rw [← h] at hp
  exact hp

end Rect

end Geospatial
