import LeanGeospatial.RCC8
import LeanGeospatial.Examples.RCC8

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
`Examples/RCC8.lean`.
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

/-! ## Realisability -/

/-- Every base relation holds between some pair of nonempty areas. -/
theorem Relation.realizable (r : Relation) :
    ∃ A C : RegularClosedRegion, (A : Region).Nonempty ∧ (C : Region).Nonempty ∧
      r.holds A C := by
  open Examples.Touches Examples.NineIntersection Examples.RCC8 in
  have hB : (areaB : Region).Nonempty :=
    ⟨⟨3, 1⟩, by rw [areaB, mem_area]; norm_num [squareB]⟩
  open Examples.Touches Examples.NineIntersection Examples.RCC8 in
  have hD : (areaD : Region).Nonempty :=
    ⟨⟨5, 1⟩, by rw [areaD, mem_area]; norm_num [squareD]⟩
  open Examples.Touches Examples.NineIntersection Examples.RCC8 in
  have hC : (areaC : Region).Nonempty :=
    ⟨⟨2, 1⟩, by rw [areaC, mem_area]; norm_num [squareC]⟩
  open Examples.Touches Examples.NineIntersection Examples.RCC8 in
  cases r with
  | dc => exact ⟨areaA, areaD, areaA_nonempty, hD, A_D_dc⟩
  | ec => exact ⟨areaA, areaB, areaA_nonempty, hB, A_B_ec⟩
  | po => exact ⟨areaA, areaC, areaA_nonempty, hC, A_C_po⟩
  | eq => exact ⟨areaA, areaA, areaA_nonempty, areaA_nonempty, A_A_eq⟩
  | tpp => exact ⟨areaT, areaA, areaT_nonempty, areaA_nonempty, T_A_tpp⟩
  | ntpp => exact ⟨areaN, areaA, areaN_nonempty, areaA_nonempty, N_A_ntpp⟩
  | tppi => exact ⟨areaA, areaT, areaA_nonempty, areaT_nonempty, A_T_tppi⟩
  | ntppi => exact ⟨areaA, areaN, areaA_nonempty, areaN_nonempty, A_N_ntppi⟩

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

/-- Three nested squares with room between them: `[1,2]²` inside `[0,3]²`
inside `[-1,4]²`. -/
private def innerSq : Rect := ⟨1, 2, 1, 2⟩
private def middleSq : Rect := ⟨0, 3, 0, 3⟩
private def outerSq : Rect := ⟨-1, 4, -1, 4⟩

private theorem ntpp_of_rect {r s : Rect} (hr : r.xmin < r.xmax ∧ r.ymin < r.ymax)
    (hs : s.xmin < s.xmax ∧ s.ymin < s.ymax)
    (hx₁ : s.xmin < r.xmin) (hx₂ : r.xmax < s.xmax)
    (hy₁ : s.ymin < r.ymin) (hy₂ : r.ymax < s.ymax) :
    NTPP (r.toRegularClosed hr.1 hr.2) (s.toRegularClosed hs.1 hs.2) :=
  ⟨Rect.within_interior_of_bounds hx₁ hx₂ hy₁ hy₂,
    Rect.toRegion_ne_of_xmin_lt hx₁ hs.1.le hs.2.le⟩

private theorem rect_nonempty {r : Rect} (hr : r.xmin < r.xmax ∧ r.ymin < r.ymax) :
    ((r.toRegularClosed hr.1 hr.2 : RegularClosedRegion) : Region).Nonempty :=
  ⟨⟨r.xmin, r.ymin⟩, le_refl _, hr.1.le, le_refl _, hr.2.le⟩

/-- `NTPP ⋄ NTPP = {NTPP}`. -/
theorem ntpp_compose_ntpp : .ntpp ⋄ .ntpp = {Relation.ntpp} := by
  ext t
  constructor
  · rintro ⟨A, B, C, hA, -, hC, hAB, hBC, ht⟩
    exact relation_unique A C hA hC ht (ntpp_trans hAB hBC)
  · rintro rfl
    have hi : innerSq.xmin < innerSq.xmax ∧ innerSq.ymin < innerSq.ymax := by
      norm_num [innerSq]
    have hm : middleSq.xmin < middleSq.xmax ∧ middleSq.ymin < middleSq.ymax := by
      norm_num [middleSq]
    have ho : outerSq.xmin < outerSq.xmax ∧ outerSq.ymin < outerSq.ymax := by
      norm_num [outerSq]
    exact ⟨_, _, _, rect_nonempty hi, rect_nonempty hm, rect_nonempty ho,
      ntpp_of_rect hi hm (by norm_num [innerSq, middleSq]) (by norm_num [innerSq, middleSq])
        (by norm_num [innerSq, middleSq]) (by norm_num [innerSq, middleSq]),
      ntpp_of_rect hm ho (by norm_num [middleSq, outerSq]) (by norm_num [middleSq, outerSq])
        (by norm_num [middleSq, outerSq]) (by norm_num [middleSq, outerSq]),
      ntpp_of_rect hi ho (by norm_num [innerSq, outerSq]) (by norm_num [innerSq, outerSq])
        (by norm_num [innerSq, outerSq]) (by norm_num [innerSq, outerSq])⟩

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
