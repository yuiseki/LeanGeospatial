import LeanGeospatial.Point
import Mathlib.Order.Disjoint
import Mathlib.Data.Set.Lattice

/-!
# Regions and spatial relations

A `Region` is any set of points. It carries no geometry of its own: a region may
be a polygon's interior, an administrative area whose exact boundary we do not
know, or an arbitrary set. That is what lets us reason about places like
"District A" without ever loading their coordinates.

The four relations below are defined by set operations alone. Nothing here is
an axiom, so every theorem in this file holds for every region.
-/

namespace Geospatial

/-- A region is a set of points in the plane. -/
abbrev Region := Set Point2D

/-- Every point of `A` is a point of `B`. -/
def Within (A B : Region) : Prop := A ⊆ B

/-- Every point of `B` is a point of `A`. -/
def Contains (A B : Region) : Prop := B ⊆ A

/-- `A` and `B` share at least one point. -/
def Intersects (A B : Region) : Prop := (A ∩ B).Nonempty

/-- `A` and `B` share no point. -/
def Disjoint (A B : Region) : Prop := A ∩ B = ∅

variable {A B C : Region}

/-! ## Within -/

theorem within_refl (A : Region) : Within A A :=
  Set.Subset.refl A

theorem within_trans (hAB : Within A B) (hBC : Within B C) : Within A C :=
  Set.Subset.trans hAB hBC

theorem within_antisymm (hAB : Within A B) (hBA : Within B A) : A = B :=
  Set.Subset.antisymm hAB hBA

/-- A point of a region is a point of every region containing it. -/
theorem Within.mem {p : Point2D} (h : Within A B) (hp : p ∈ A) : p ∈ B :=
  h hp

/-! ## Contains -/

theorem contains_iff_within : Contains A B ↔ Within B A :=
  Iff.rfl

theorem contains_refl (A : Region) : Contains A A :=
  within_refl A

theorem contains_trans (hAB : Contains A B) (hBC : Contains B C) : Contains A C :=
  within_trans hBC hAB

/-! ## Intersects -/

theorem intersects_symm (h : Intersects A B) : Intersects B A := by
  unfold Intersects at *
  rwa [Set.inter_comm]

theorem intersects_comm : Intersects A B ↔ Intersects B A :=
  ⟨intersects_symm, intersects_symm⟩

/-- A nonempty region intersects itself. -/
theorem intersects_self_iff : Intersects A A ↔ A.Nonempty := by
  simp [Intersects]

/-- If `A` meets `B` and `B` lies within `C`, then `A` meets `C`. -/
theorem Intersects.mono_right (h : Intersects A B) (hBC : Within B C) : Intersects A C :=
  Set.Nonempty.mono (Set.inter_subset_inter_right A hBC) h

/-- If `A` meets `C` and `A` lies within `B`, then `B` meets `C`. -/
theorem Intersects.mono_left (h : Intersects A C) (hAB : Within A B) : Intersects B C :=
  Set.Nonempty.mono (Set.inter_subset_inter_left C hAB) h

/-! ## Disjoint -/

theorem disjoint_symm (h : Disjoint A B) : Disjoint B A := by
  unfold Disjoint at *
  rwa [Set.inter_comm]

theorem disjoint_comm : Disjoint A B ↔ Disjoint B A :=
  ⟨disjoint_symm, disjoint_symm⟩

theorem disjoint_iff_not_intersects : Disjoint A B ↔ ¬ Intersects A B := by
  unfold Disjoint Intersects
  rw [Set.not_nonempty_iff_eq_empty]

theorem Disjoint.not_intersects (h : Disjoint A B) : ¬ Intersects A B :=
  disjoint_iff_not_intersects.mp h

/-- Our `Disjoint` agrees with Mathlib's order-theoretic `Disjoint` on sets. -/
theorem disjoint_iff_set_disjoint : Disjoint A B ↔ _root_.Disjoint A B :=
  Set.disjoint_iff_inter_eq_empty.symm

/-- A region inside a region disjoint from `C` is itself disjoint from `C`. -/
theorem Disjoint.mono_left (h : Disjoint B C) (hAB : Within A B) : Disjoint A C := by
  rw [disjoint_iff_not_intersects] at *
  exact fun hAC => h (hAC.mono_left hAB)

/-! ## Intersects is not transitive -/

/-- `Intersects` is not transitive: `A` and `C` can both meet `B` without meeting
each other. The witness uses two distinct points `a` and `c`, with
`A = {a}`, `B = {a, c}` and `C = {c}`. -/
theorem intersects_not_transitive :
    ¬ ∀ A B C : Region, Intersects A B → Intersects B C → Intersects A C := by
  intro h
  let a : Point2D := ⟨0, 0⟩
  let c : Point2D := ⟨1, 0⟩
  have hAB : Intersects {a} {a, c} := ⟨a, by simp⟩
  have hBC : Intersects {a, c} {c} := ⟨c, by simp⟩
  obtain ⟨p, hpA, hpC⟩ := h {a} {a, c} {c} hAB hBC
  have hpa : p = a := hpA
  have hpc : p = c := hpC
  have : (0 : ℝ) = 1 := congrArg Point2D.x (hpa.symm.trans hpc)
  norm_num at this

end Geospatial
