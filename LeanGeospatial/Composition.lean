import LeanGeospatial.RCC8Witnesses

/-!
# Weak composition of RCC8 relations

The weak composition `r ⋄ s` is the set of base relations `t` for which some
nonempty areas `A`, `B`, `C` satisfy `r A B`, `s B C` and `t A C`. It is
defined from the RCC8 relations of `RCC8.lean` and nothing else: no
composition table is assumed, and every entry proved here is proved from the
definitions.

Results so far:

- `compose_converse`: `(r ⋄ s)` converted is `s˘ ⋄ r˘`.
- `eq_compose` and `compose_eq`: `EQ` is a left and right identity.
- `ntpp_compose_ntpp`: `NTPP ⋄ NTPP = {NTPP}`, and its converse
  `ntppi_compose_ntppi`.

The identity laws need every relation to be realised by some pair of nonempty
areas (`Relation.realizable`). The witnesses are the squares of
`RCC8Witnesses.lean`.
-/

namespace Geospatial.RCC8

open Geospatial

/-- Weak composition: the relations that can hold from `A` to `C` when `r`
holds from `A` to `B` and `s` from `B` to `C`, over nonempty areas. -/
def compose (r s : Relation) : Set Relation :=
  {t | ∃ A B C : RegularClosedRegion,
    (A : Region).Nonempty ∧ (B : Region).Nonempty ∧ (C : Region).Nonempty ∧
    r.holds A B ∧ s.holds B C ∧ t.holds A C}

@[inherit_doc] scoped infixl:70 " ⋄ " => compose

/-- Converting every relation in a set. -/
def Relation.converseSet (S : Set Relation) : Set Relation := {t | t.converse ∈ S}

/-! ## Converse law -/

/-- `t` is in `r ⋄ s` exactly when its converse is in `s˘ ⋄ r˘`: read the
triangle `A, B, C` backwards as `C, B, A`. -/
theorem mem_compose_converse (r s t : Relation) :
    t ∈ r ⋄ s ↔ t.converse ∈ s.converse ⋄ r.converse := by
  constructor
  · rintro ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩
    exact ⟨C, B, A, hC, hB, hA, (s.holds_converse C B).mpr hs,
      (r.holds_converse B A).mpr hr, (t.holds_converse C A).mpr ht⟩
  · rintro ⟨C, B, A, hC, hB, hA, hs, hr, ht⟩
    exact ⟨A, B, C, hA, hB, hC, (r.holds_converse B A).mp hr,
      (s.holds_converse C B).mp hs, (t.holds_converse C A).mp ht⟩

/-- The converse law as an equation of sets. -/
theorem compose_converse (r s : Relation) :
    Relation.converseSet (r ⋄ s) = s.converse ⋄ r.converse := by
  ext t
  change t.converse ∈ r ⋄ s ↔ _
  rw [mem_compose_converse, Relation.converse_converse]

/-! ## EQ is the identity -/

/-- `EQ` between areas is equality of the areas themselves. -/
theorem eq_iff {A B : RegularClosedRegion} : EQ A B ↔ A = B :=
  ⟨fun h => SetLike.coe_injective h, fun h => h ▸ rfl⟩

theorem eq_compose (r : Relation) : .eq ⋄ r = {r} := by
  ext t
  constructor
  · rintro ⟨A, B, C, hA, hB, hC, hAB, hr, ht⟩
    obtain rfl := eq_iff.mp hAB
    exact relation_unique A C hA hC ht hr
  · rintro rfl
    obtain ⟨A, C, hA, hC, ht⟩ := t.realizable
    exact ⟨A, A, C, hA, hA, hC, rfl, ht, ht⟩

theorem compose_eq (r : Relation) : r ⋄ .eq = {r} := by
  ext t
  constructor
  · rintro ⟨A, B, C, hA, hB, hC, hr, hBC, ht⟩
    obtain rfl := eq_iff.mp hBC
    exact relation_unique A B hA hB ht hr
  · rintro rfl
    obtain ⟨A, C, hA, hC, ht⟩ := t.realizable
    exact ⟨A, C, C, hA, hC, hC, ht, rfl, ht⟩

/-! ## NTPP ⋄ NTPP -/

/-- If `A` is a non-tangential proper part of `B`, and `B` of `C`, then `A`
is a non-tangential proper part of `C`. -/
theorem ntpp_trans {A B C : RegularClosedRegion} (hAB : NTPP A B) (hBC : NTPP B C) :
    NTPP A C := by
  obtain ⟨hA, hne⟩ := hAB
  obtain ⟨hB, -⟩ := hBC
  have hBC' : Within (B : Region) C := within_trans hB interior_subset
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
