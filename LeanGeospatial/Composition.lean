import LeanGeospatial.RCC8Witnesses

/-!
# Weak composition of RCC8 relations

The weak composition `compose α r s` is the set of base relations `t` for
which some nonempty areas `A`, `B`, `C` of the space `α` satisfy `r A B`,
`s B C` and `t A C`. It is defined from the RCC8 relations of `RCC8.lean` and
nothing else: no composition table is assumed, and every entry proved here is
proved from the definitions.

Weak composition depends on the space. In the plane it is the classical RCC8
table (`compose_eq_table`); in a discrete space, where areas have no
boundary, `EC` is in no composition at all. For the plane it is written
`r ⋄ s`, short for `compose Point2D r s`.

Results for every space:

- `mem_compose_converse`, `compose_converse`: `(r ⋄ s)` converted is
  `s˘ ⋄ r˘`.
- `eq_compose_of_realizable`, `compose_eq_of_realizable`: `EQ` is a left and
  right identity for every relation some pair of nonempty areas realises.
- `ntpp_trans`.

Results for the plane:

- `eq_compose`, `compose_eq`: every relation is realised
  (`Relation.realizable`, by the squares of `RCC8Witnesses.lean`), so `EQ` is
  an identity outright.
- `ntpp_compose_ntpp`: `NTPP ⋄ NTPP = {NTPP}`, and its converse
  `ntppi_compose_ntppi`.
-/

namespace Geospatial.RCC8

open Geospatial

/-- Weak composition over the space `α`: the relations that can hold from `A`
to `C` when `r` holds from `A` to `B` and `s` from `B` to `C`, over nonempty
areas of `α`. -/
def compose (α : Type*) [TopologicalSpace α] (r s : Relation) : Set Relation :=
  {t | ∃ A B C : RegularClosedRegion α,
    (A : Set α).Nonempty ∧ (B : Set α).Nonempty ∧ (C : Set α).Nonempty ∧
    r.holds A B ∧ s.holds B C ∧ t.holds A C}

/-- Weak composition in the plane. -/
scoped infixl:70 " ⋄ " => compose Point2D

/-- `r` holds between some pair of nonempty areas of `α`. -/
def Relation.Realizable (α : Type*) [TopologicalSpace α] (r : Relation) : Prop :=
  ∃ A C : RegularClosedRegion α, (A : Set α).Nonempty ∧ (C : Set α).Nonempty ∧ r.holds A C

/-- Converting every relation in a set. -/
def Relation.converseSet (S : Set Relation) : Set Relation := {t | t.converse ∈ S}

variable {α : Type*} [TopologicalSpace α]

/-! ## Converse law -/

/-- `t` is in `r ⋄ s` exactly when its converse is in `s˘ ⋄ r˘`: read the
triangle `A, B, C` backwards as `C, B, A`. -/
theorem mem_compose_converse (r s t : Relation) :
    t ∈ compose α r s ↔ t.converse ∈ compose α s.converse r.converse := by
  constructor
  · rintro ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩
    exact ⟨C, B, A, hC, hB, hA, (s.holds_converse C B).mpr hs,
      (r.holds_converse B A).mpr hr, (t.holds_converse C A).mpr ht⟩
  · rintro ⟨C, B, A, hC, hB, hA, hs, hr, ht⟩
    exact ⟨A, B, C, hA, hB, hC, (r.holds_converse B A).mp hr,
      (s.holds_converse C B).mp hs, (t.holds_converse C A).mp ht⟩

/-- The converse law as an equation of sets. -/
theorem compose_converse (r s : Relation) :
    Relation.converseSet (compose α r s) = compose α s.converse r.converse := by
  ext t
  change t.converse ∈ compose α r s ↔ _
  rw [mem_compose_converse, Relation.converse_converse]

/-! ## EQ is the identity -/

/-- `EQ` between areas is equality of the areas themselves. -/
theorem eq_iff {A B : RegularClosedRegion α} : EQ A B ↔ A = B :=
  ⟨fun h => SetLike.coe_injective h, fun h => h ▸ rfl⟩

theorem eq_compose_of_realizable {r : Relation} (hr : r.Realizable α) :
    compose α .eq r = {r} := by
  ext t
  constructor
  · rintro ⟨A, B, C, hA, hB, hC, hAB, hr', ht⟩
    obtain rfl := eq_iff.mp hAB
    exact relation_unique A C hA hC ht hr'
  · rintro rfl
    obtain ⟨A, C, hA, hC, ht⟩ := hr
    exact ⟨A, A, C, hA, hA, hC, rfl, ht, ht⟩

theorem compose_eq_of_realizable {r : Relation} (hr : r.Realizable α) :
    compose α r .eq = {r} := by
  ext t
  constructor
  · rintro ⟨A, B, C, hA, hB, hC, hr', hBC, ht⟩
    obtain rfl := eq_iff.mp hBC
    exact relation_unique A B hA hB ht hr'
  · rintro rfl
    obtain ⟨A, C, hA, hC, ht⟩ := hr
    exact ⟨A, C, C, hA, hC, hC, ht, rfl, ht⟩

theorem eq_compose (r : Relation) : .eq ⋄ r = {r} :=
  eq_compose_of_realizable r.realizable

theorem compose_eq (r : Relation) : r ⋄ .eq = {r} :=
  compose_eq_of_realizable r.realizable

/-! ## NTPP ⋄ NTPP -/

/-- If `A` is a non-tangential proper part of `B`, and `B` of `C`, then `A`
is a non-tangential proper part of `C`. -/
theorem ntpp_trans {A B C : RegularClosedRegion α} (hAB : NTPP A B) (hBC : NTPP B C) :
    NTPP A C := by
  obtain ⟨hA, hne⟩ := hAB
  obtain ⟨hB, -⟩ := hBC
  have hBC' : Within (B : Set α) C := within_trans hB interior_subset
  refine ⟨within_trans (within_trans hA interior_subset) hB, fun hAC => hne ?_⟩
  -- If A were C, then B ⊆ C = A ⊆ B, so A = B.
  exact within_antisymm (within_trans hA interior_subset) (hAC ▸ hBC')

/-- `NTPP ⋄ NTPP = {NTPP}`. -/
theorem ntpp_compose_ntpp : .ntpp ⋄ .ntpp = {Relation.ntpp} := by
  ext t
  constructor
  · rintro ⟨A, B, C, hA, -, hC, hAB, hBC, ht⟩
    exact relation_unique A C hA hC ht (ntpp_trans hAB hBC)
  · rintro rfl
    open Witnesses in
    exact ⟨_, _, _, innerSq.area_nonempty hInner, middleSq.area_nonempty hMiddle,
      outerSq.area_nonempty hOuter, inner_middle_ntpp, middle_outer_ntpp, inner_outer_ntpp⟩

/-- `NTPPi ⋄ NTPPi = {NTPPi}`, from the converse law. -/
theorem ntppi_compose_ntppi : .ntppi ⋄ .ntppi = {Relation.ntppi} := by
  ext t
  rw [mem_compose_converse]
  change t.converse ∈ Relation.ntpp ⋄ Relation.ntpp ↔ _
  rw [ntpp_compose_ntpp, Set.mem_singleton_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rw [← t.converse_converse, h]
    rfl
  · rintro rfl
    rfl

end Geospatial.RCC8
