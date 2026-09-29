import LeanGeospatial.Euclidean

/-!
# Completeness with connected areas

`composeConnected α r s` is weak composition with every area required to be
connected, and `RCC8ConnectedComplete α` says it is the whole table. It is
stronger than `RCC8Complete` (`RCC8ConnectedComplete.rcc8Complete`), and it
tells apart spaces that plain completeness does not: the line fails it and
the plane has it. It is not a matter of dimension alone, though: the circle,
also one-dimensional, has it (`rcc8ConnectedComplete_circle` in
`Circle.lean`).

- The line is complete but not for connected areas
  (`not_rcc8ConnectedComplete_real`). A connected area of the line is a closed
  interval, and no three of them touch one another pairwise
  (`not_ec_triangle_real`): take a point inside each; the middle one sits in
  an interval between the other two, so if the outer two met, one of them
  would reach across it and overlap its interior. So `EC ⋄ EC ∋ EC` fails.
- The plane is complete for connected areas (`rcc8ConnectedComplete_plane`):
  its witnesses are rectangles.
- A connected factor keeps connectedness, `A ×ˢ univ` being connected when
  `A` is, so the property passes to products with connected spaces
  (`RCC8ConnectedComplete.prod_right`), and every Euclidean space of
  dimension two or more has it (`rcc8ConnectedComplete_euclideanSpace`,
  `rcc8ConnectedComplete_euclideanSpace3`).
- Like plain completeness, it is a topological property
  (`RCC8ConnectedComplete.homeomorph`).
-/

namespace Geospatial

open Set RCC8

/-- Weak composition over `α` with connected areas. -/
def RCC8.composeConnected (α : Type*) [TopologicalSpace α] (r s : Relation) : Set Relation :=
  {t | ∃ A B C : RegularClosedRegion α,
    IsConnected (A : Set α) ∧ IsConnected (B : Set α) ∧ IsConnected (C : Set α) ∧
    r.holds A B ∧ s.holds B C ∧ t.holds A C}

/-- The table is complete for `α` with connected areas. -/
def RCC8ConnectedComplete (α : Type*) [TopologicalSpace α] : Prop :=
  ∀ r s, composeConnected α r s = ↑(table r s)

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- Connected configurations are configurations. -/
theorem RCC8.composeConnected_subset_compose (r s : Relation) :
    composeConnected α r s ⊆ compose α r s :=
  fun _ ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩ =>
    ⟨A, B, C, hA.nonempty, hB.nonempty, hC.nonempty, hr, hs, ht⟩

/-- The table is sound for connected areas, so completeness is the
realisation of every entry. -/
theorem rcc8ConnectedComplete_iff_table_subset :
    RCC8ConnectedComplete α ↔ ∀ r s, (↑(table r s) : Set Relation) ⊆ composeConnected α r s :=
  ⟨fun h r s => (h r s).ge, fun h r s => Subset.antisymm
    (fun _ ht => Finset.mem_coe.mpr (mem_table_of_mem_compose
      (composeConnected_subset_compose r s ht))) (h r s)⟩

/-- Completeness for connected areas implies completeness. -/
theorem RCC8ConnectedComplete.rcc8Complete (h : RCC8ConnectedComplete α) : RCC8Complete α :=
  rcc8Complete_iff_table_subset.mpr fun r s =>
    (h r s).ge.trans (composeConnected_subset_compose r s)

/-! ## The plane -/

/-- The plane is complete for connected areas: its witnesses are rectangles. -/
theorem rcc8ConnectedComplete_plane : RCC8ConnectedComplete Point2D :=
  rcc8ConnectedComplete_iff_table_subset.mpr fun r s t ht => by
    obtain ⟨A, B, C, -, -, -, cA, cB, cC, -, -, -, hr, hs, ht'⟩ :=
      realizes_of_mem_table r s t (Finset.mem_coe.mp ht)
    exact ⟨A, B, C, cA, cB, cC, hr, hs, ht'⟩

/-! ## Homeomorphisms and products -/

theorem RCC8.mem_composeConnected_of_homeomorph (e : α ≃ₜ β) {r s t : Relation}
    (h : t ∈ composeConnected α r s) : t ∈ composeConnected β r s := by
  obtain ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩ := h
  exact ⟨A.map e, B.map e, C.map e, hA.image e e.continuous.continuousOn,
    hB.image e e.continuous.continuousOn, hC.image e e.continuous.continuousOn,
    (Relation.holds_map_iff e A B r).mpr hr, (Relation.holds_map_iff e B C s).mpr hs,
    (Relation.holds_map_iff e A C t).mpr ht⟩

theorem RCC8ConnectedComplete.of_homeomorph (h : RCC8ConnectedComplete α) (e : α ≃ₜ β) :
    RCC8ConnectedComplete β :=
  rcc8ConnectedComplete_iff_table_subset.mpr fun r s =>
    (h r s).ge.trans fun _ ht => mem_composeConnected_of_homeomorph e ht

/-- Homeomorphic spaces are complete for connected areas together or not at
all. -/
theorem RCC8ConnectedComplete.homeomorph (e : α ≃ₜ β) :
    RCC8ConnectedComplete α ↔ RCC8ConnectedComplete β :=
  ⟨fun h => h.of_homeomorph e, fun h => h.of_homeomorph e.symm⟩

section Product

variable [ConnectedSpace β]

/-- Every connected configuration of `α` reappears in `α × β` for a connected
`β`. -/
theorem RCC8.composeConnected_subset_prod (r s : Relation) :
    composeConnected α r s ⊆ composeConnected (α × β) r s := by
  rintro t ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩
  exact ⟨A.prodUniv β, B.prodUniv β, C.prodUniv β, hA.prod isConnected_univ,
    hB.prod isConnected_univ, hC.prod isConnected_univ,
    (Relation.holds_prodUniv_iff A B r).mpr hr, (Relation.holds_prodUniv_iff B C s).mpr hs,
    (Relation.holds_prodUniv_iff A C t).mpr ht⟩

theorem RCC8ConnectedComplete.prod_right (h : RCC8ConnectedComplete α) :
    RCC8ConnectedComplete (α × β) :=
  rcc8ConnectedComplete_iff_table_subset.mpr fun r s =>
    (h r s).ge.trans (composeConnected_subset_prod r s)

theorem RCC8ConnectedComplete.prod_left (h : RCC8ConnectedComplete α) :
    RCC8ConnectedComplete (β × α) :=
  (RCC8ConnectedComplete.homeomorph (Homeomorph.prodComm α β)).mp h.prod_right

end Product

/-! ## Euclidean spaces of dimension two and more -/

theorem rcc8ConnectedComplete_pi : ∀ n : ℕ, RCC8ConnectedComplete (Fin (n + 2) → ℝ)
  | 0 => (RCC8ConnectedComplete.homeomorph (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph).mp
      rcc8ConnectedComplete_plane
  | n + 1 =>
    (RCC8ConnectedComplete.homeomorph
      (Fin.consEquivL ℝ fun _ : Fin (n + 3) => ℝ).toHomeomorph).mp
      (rcc8ConnectedComplete_pi n).prod_left

theorem rcc8ConnectedComplete_euclideanSpace (n : ℕ) :
    RCC8ConnectedComplete (EuclideanSpace ℝ (Fin (n + 2))) :=
  (RCC8ConnectedComplete.homeomorph (EuclideanSpace.equiv (Fin (n + 2)) ℝ).toHomeomorph).mpr
    (rcc8ConnectedComplete_pi n)

/-- Space is complete for connected areas. -/
theorem rcc8ConnectedComplete_euclideanSpace3 :
    RCC8ConnectedComplete (EuclideanSpace ℝ (Fin 3)) :=
  rcc8ConnectedComplete_euclideanSpace 1

/-! ## The line -/

/-- On the line, if `Y` sits between `X` and `Z` (points inside them in that
order) and its interior misses both of theirs, then connected `X` and `Z`
cannot meet: one of them would have to reach across `Y`'s point. -/
theorem not_intersects_of_between {X Y Z : RegularClosedRegion ℝ}
    (hX : IsConnected (X : Set ℝ)) (hZ : IsConnected (Z : Set ℝ)) {x y z : ℝ}
    (hx : x ∈ interior (X : Set ℝ)) (hy : y ∈ interior (Y : Set ℝ))
    (hz : z ∈ interior (Z : Set ℝ)) (hxy : x < y) (hyz : y < z)
    (hXY : Geospatial.Disjoint (interior (X : Set ℝ)) (interior (Y : Set ℝ)))
    (hYZ : Geospatial.Disjoint (interior (Y : Set ℝ)) (interior (Z : Set ℝ))) :
    ¬ Intersects (X : Set ℝ) Z := by
  rintro ⟨p, hpX, hpZ⟩
  have key : ∀ W : RegularClosedRegion ℝ, y ∈ (W : Set ℝ) →
      Geospatial.Disjoint (interior (W : Set ℝ)) (interior (Y : Set ℝ)) → False := by
    intro W hyW hWY
    have hcl : y ∈ closure (interior (W : Set ℝ)) := by rw [W.closure_interior_eq]; exact hyW
    obtain ⟨q, hqY, hqW⟩ := mem_closure_iff.mp hcl _ isOpen_interior hy
    have hq : q ∈ interior (W : Set ℝ) ∩ interior (Y : Set ℝ) := ⟨hqW, hqY⟩
    rw [hWY] at hq
    exact hq
  rcases le_total p y with h | h
  · exact key Z (hZ.isPreconnected.Icc_subset hpZ (interior_subset hz) ⟨h, hyz.le⟩)
      (disjoint_symm hYZ)
  · exact key X (hX.isPreconnected.Icc_subset (interior_subset hx) hpX ⟨hxy.le, h⟩) hXY

/-- No three connected areas of the line are pairwise externally connected. -/
theorem not_ec_triangle_real {A B C : RegularClosedRegion ℝ} (hA : IsConnected (A : Set ℝ))
    (hB : IsConnected (B : Set ℝ)) (hC : IsConnected (C : Set ℝ)) (hAB : EC A B)
    (hBC : EC B C) (hAC : EC A C) : False := by
  obtain ⟨a, ha⟩ := A.nonempty_iff_interior_nonempty.mp hA.nonempty
  obtain ⟨b, hb⟩ := B.nonempty_iff_interior_nonempty.mp hB.nonempty
  obtain ⟨c, hc⟩ := C.nonempty_iff_interior_nonempty.mp hC.nonempty
  have ne : ∀ {X Y : RegularClosedRegion ℝ} {x y : ℝ}, x ∈ interior (X : Set ℝ) →
      y ∈ interior (Y : Set ℝ) → EC X Y → x ≠ y := by
    rintro X Y x y hx hy hXY rfl
    have h : x ∈ interior (X : Set ℝ) ∩ interior (Y : Set ℝ) := ⟨hx, hy⟩
    rw [hXY.2] at h
    exact h
  rcases (ne ha hb hAB).lt_or_gt with h₁ | h₁ <;> rcases (ne hb hc hBC).lt_or_gt with h₂ | h₂ <;>
    rcases (ne ha hc hAC).lt_or_gt with h₃ | h₃
  · exact not_intersects_of_between hA hC ha hb hc h₁ h₂ hAB.2 hBC.2 hAC.1
  · linarith
  · exact not_intersects_of_between hA hB ha hc hb h₃ h₂ hAC.2 (disjoint_symm hBC.2) hAB.1
  · exact not_intersects_of_between hC hB hc ha hb h₃ h₁ (disjoint_symm hAC.2) hAB.2
      (intersects_symm hBC.1)
  · exact not_intersects_of_between hB hC hb ha hc h₁ h₃ (disjoint_symm hAB.2) hAC.2 hBC.1
  · exact not_intersects_of_between hB hA hb hc ha h₂ h₃ hBC.2 (disjoint_symm hAC.2)
      (intersects_symm hAB.1)
  · linarith
  · exact not_intersects_of_between hC hA hc hb ha h₂ h₁ (disjoint_symm hBC.2)
      (disjoint_symm hAB.2) (intersects_symm hAC.1)

/-- The line is complete, but not for connected areas: `EC ⋄ EC ∋ EC` would
need three pairwise touching intervals. -/
theorem not_rcc8ConnectedComplete_real : ¬ RCC8ConnectedComplete ℝ := by
  intro h
  have hmem : Relation.ec ∈ composeConnected ℝ .ec .ec := by
    rw [h, Finset.mem_coe]
    decide
  obtain ⟨A, B, C, hA, hB, hC, hAB, hBC, hAC⟩ := hmem
  exact not_ec_triangle_real hA hB hC hAB hBC hAC

end Geospatial
