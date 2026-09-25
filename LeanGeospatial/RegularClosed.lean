import LeanGeospatial.Topology
import Mathlib.Data.SetLike.Basic

/-!
# Regular closed regions

A `Region` is any set of points, including a lone point, a line, or a square
with a stray whisker attached. Geographic areas (districts, parcels, lakes) are
meant to be none of those: they are the closure of their own interior. Such a
set is called regular closed.

`RegularClosedRegion` bundles a region with a proof of that property, so the
type says which sets are areas. Theorems about areas can then drop the
hypothesis `closure (interior A) = A`, because every value of the type carries
it.

`Region` stays as the type of arbitrary sets. The distinction matters: the
intersection of two touching areas is their shared edge, a `Region` that is
not a `RegularClosedRegion` (`Touches.inter_not_regularClosed`).
-/

namespace Geospatial

/-- A region that is the closure of its interior. -/
structure RegularClosedRegion where
  /-- The underlying set of points. -/
  carrier : Region
  closure_interior_eq' : closure (interior carrier) = carrier

namespace RegularClosedRegion

instance : SetLike RegularClosedRegion Point2D where
  coe := carrier
  coe_injective' A B h := by
    cases A
    cases B
    congr

@[simp] theorem coe_mk (s : Region) (h : closure (interior s) = s) :
    ((⟨s, h⟩ : RegularClosedRegion) : Region) = s := rfl

variable (A B : RegularClosedRegion)

theorem closure_interior_eq : closure (interior (A : Region)) = A :=
  A.closure_interior_eq'

theorem isClosed : IsClosed (A : Region) := by
  rw [← A.closure_interior_eq]
  exact isClosed_closure

theorem closure_eq : closure (A : Region) = A :=
  A.isClosed.closure_eq

theorem boundary_eq : boundary (A : Region) = (A : Region) \ interior A := by
  rw [Geospatial.boundary_eq, A.closure_eq]

/-- An area is empty exactly when its interior is. There are no areas made of
boundary alone. -/
theorem nonempty_iff_interior_nonempty :
    (A : Region).Nonempty ↔ (interior (A : Region)).Nonempty := by
  constructor
  · intro h
    rw [← A.closure_interior_eq] at h
    exact closure_nonempty_iff.mp h
  · exact fun h => h.mono interior_subset

/-- The empty area. -/
instance : Bot RegularClosedRegion :=
  ⟨⟨∅, by simp⟩⟩

@[simp] theorem coe_bot : ((⊥ : RegularClosedRegion) : Region) = ∅ := rfl

/-- The union of two areas is an area. -/
def union : RegularClosedRegion where
  carrier := A ∪ B
  closure_interior_eq' := by
    apply Set.Subset.antisymm
    · calc closure (interior ((A : Region) ∪ B))
          ⊆ closure ((A : Region) ∪ B) := closure_mono interior_subset
        _ = (A : Region) ∪ B := by rw [closure_union, A.closure_eq, B.closure_eq]
    · calc (A : Region) ∪ B
          = closure (interior (A : Region)) ∪ closure (interior (B : Region)) := by
            rw [A.closure_interior_eq, B.closure_interior_eq]
        _ = closure (interior (A : Region) ∪ interior (B : Region)) :=
            closure_union.symm
        _ ⊆ closure (interior ((A : Region) ∪ B)) :=
            closure_mono (Set.union_subset (interior_mono Set.subset_union_left)
              (interior_mono Set.subset_union_right))

@[simp] theorem coe_union : ((A.union B : RegularClosedRegion) : Region) = (A : Region) ∪ B :=
  rfl

/-! ## Touching areas -/

/-- When two areas touch, every point they share lies on both boundaries. No
hypothesis beyond `Touches` is needed: being an area is part of the type. -/
theorem inter_subset_boundary_of_touches (h : Touches (A : Region) B) :
    (A : Region) ∩ B ⊆ boundary (A : Region) ∩ boundary (B : Region) :=
  h.inter_subset_boundary A.closure_interior_eq B.closure_interior_eq

/-- A shared point of two touching areas is on the boundary of each. -/
theorem mem_boundary_of_touches {p : Point2D} (h : Touches (A : Region) B)
    (hpA : p ∈ A) (hpB : p ∈ B) :
    p ∈ boundary (A : Region) ∧ p ∈ boundary (B : Region) :=
  A.inter_subset_boundary_of_touches B h ⟨hpA, hpB⟩

end RegularClosedRegion

/-- What two touching regions share has empty interior, so it is never an
area: the shared edge of two districts is a `Region` but not a
`RegularClosedRegion`. -/
theorem Touches.inter_not_regularClosed {A B : Region} (h : Touches A B) :
    closure (interior (A ∩ B)) ≠ A ∩ B := by
  intro hAB
  rw [interior_inter, h.2, closure_empty] at hAB
  obtain ⟨p, hp⟩ := h.1
  rw [← hAB] at hp
  exact hp

theorem Touches.not_exists_regularClosed_inter {A B : Region} (h : Touches A B) :
    ¬ ∃ C : RegularClosedRegion, (C : Region) = A ∩ B := by
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
    RegularClosedRegion :=
  ⟨r.toRegion, closure_interior_toRegion hx hy⟩

@[simp] theorem coe_toRegularClosed (r : Rect) (hx : r.xmin < r.xmax)
    (hy : r.ymin < r.ymax) :
    ((r.toRegularClosed hx hy : RegularClosedRegion) : Region) = r.toRegion := rfl

/-- The positivity conditions are needed: a rectangle of width zero is a line
segment, and a segment is not the closure of its (empty) interior. -/
theorem segment_not_regularClosed :
    closure (interior (⟨0, 0, 0, 1⟩ : Rect).toRegion) ≠ (⟨0, 0, 0, 1⟩ : Rect).toRegion := by
  rw [interior_toRegion]
  have hempty : (⟨0, 0, 0, 1⟩ : Rect).openRegion = ∅ := by
    rw [Set.eq_empty_iff_forall_not_mem]
    rintro p ⟨h₁, h₂, -, -⟩
    exact lt_asymm h₁ h₂
  rw [hempty, closure_empty]
  intro h
  have hp : (⟨0, 0⟩ : Point2D) ∈ (⟨0, 0, 0, 1⟩ : Rect).toRegion := by
    simp only [toRegion, Set.mem_setOf_eq]
    norm_num
  rw [← h] at hp
  exact hp

end Rect

end Geospatial
