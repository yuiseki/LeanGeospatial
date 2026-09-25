import LeanGeospatial.RCC8

/-!
# Witnesses for the RCC8 relations

Concrete squares that realise each of the eight base relations, and three
nested squares for `NTPP ⋄ NTPP`. Weak composition needs them: showing that a
relation belongs to a composition means exhibiting areas.

```
  y
  2 +-------+-------+           +---+
    |  +-+  |  +----+           |   |
    |  |N|  |  | T  |  B         | D |
    |  +-+  |  +----+           |   |
  0 +-------+----+--+           +---+
    0       2    3  4           5   6  x

  A = [0,2]×[0,2]    B = [2,4]×[0,2]    C = [1,3]×[0,2]    D = [5,6]×[0,2]
  N = [1/2,3/2]²     T = [1,2]×[0,1]
```

`T` touches `A`'s right edge from inside, so it is a tangential proper part;
`N` stays off `A`'s boundary. (`T` is drawn offset for legibility.)
-/

namespace Geospatial

namespace Rect

/-- The area of a rectangle with positive width and height, with the
positivity packed into one hypothesis. -/
noncomputable def area (r : Rect) (h : r.xmin < r.xmax ∧ r.ymin < r.ymax) :
    RegularClosedRegion :=
  r.toRegularClosed h.1 h.2

theorem mem_area (r : Rect) (h : r.xmin < r.xmax ∧ r.ymin < r.ymax) (p : Point2D) :
    p ∈ ((r.area h : RegularClosedRegion) : Region) ↔
      r.xmin ≤ p.x ∧ p.x ≤ r.xmax ∧ r.ymin ≤ p.y ∧ p.y ≤ r.ymax :=
  Iff.rfl

theorem interior_area (r : Rect) (h : r.xmin < r.xmax ∧ r.ymin < r.ymax) :
    interior ((r.area h : RegularClosedRegion) : Region) = r.openRegion :=
  interior_toRegion r

theorem area_nonempty (r : Rect) (h : r.xmin < r.xmax ∧ r.ymin < r.ymax) :
    ((r.area h : RegularClosedRegion) : Region).Nonempty :=
  ⟨⟨r.xmin, r.ymin⟩, le_refl _, h.1.le, le_refl _, h.2.le⟩

variable {r s : Rect} (hr : r.xmin < r.xmax ∧ r.ymin < r.ymax)
  (hs : s.xmin < s.xmax ∧ s.ymin < s.ymax)

/-! The four building blocks of every RCC8 relation, for rectangles, as
inequalities between coordinates. -/

theorem within_area_iff :
    Within ((r.area hr : RegularClosedRegion) : Region) (s.area hs) ↔
      s.xmin ≤ r.xmin ∧ r.xmax ≤ s.xmax ∧ s.ymin ≤ r.ymin ∧ r.ymax ≤ s.ymax := by
  constructor
  · intro h
    have h₁ := h (show (⟨r.xmin, r.ymin⟩ : Point2D) ∈ ((r.area hr : RegularClosedRegion) : Region)
      from ⟨le_rfl, hr.1.le, le_rfl, hr.2.le⟩)
    have h₂ := h (show (⟨r.xmax, r.ymax⟩ : Point2D) ∈ ((r.area hr : RegularClosedRegion) : Region)
      from ⟨hr.1.le, le_rfl, hr.2.le, le_rfl⟩)
    exact ⟨h₁.1, h₂.2.1, h₁.2.2.1, h₂.2.2.2⟩
  · rintro ⟨a, b, c, d⟩
    exact within_of_bounds a b c d

theorem within_interior_area_iff :
    Within ((r.area hr : RegularClosedRegion) : Region)
        (interior ((s.area hs : RegularClosedRegion) : Region)) ↔
      s.xmin < r.xmin ∧ r.xmax < s.xmax ∧ s.ymin < r.ymin ∧ r.ymax < s.ymax := by
  constructor
  · intro h
    rw [interior_area] at h
    have h₁ := h (show (⟨r.xmin, r.ymin⟩ : Point2D) ∈ ((r.area hr : RegularClosedRegion) : Region)
      from ⟨le_rfl, hr.1.le, le_rfl, hr.2.le⟩)
    have h₂ := h (show (⟨r.xmax, r.ymax⟩ : Point2D) ∈ ((r.area hr : RegularClosedRegion) : Region)
      from ⟨hr.1.le, le_rfl, hr.2.le, le_rfl⟩)
    exact ⟨h₁.1, h₂.2.1, h₁.2.2.1, h₂.2.2.2⟩
  · rintro ⟨a, b, c, d⟩
    exact within_interior_of_bounds a b c d

theorem intersects_area_iff :
    Intersects ((r.area hr : RegularClosedRegion) : Region) (s.area hs) ↔
      r.xmin ≤ s.xmax ∧ s.xmin ≤ r.xmax ∧ r.ymin ≤ s.ymax ∧ s.ymin ≤ r.ymax := by
  constructor
  · rintro ⟨p, ⟨a₁, a₂, a₃, a₄⟩, ⟨b₁, b₂, b₃, b₄⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨max r.xmin s.xmin, max r.ymin s.ymin⟩,
      ⟨le_max_left _ _, max_le hr.1.le h₂, le_max_left _ _, max_le hr.2.le h₄⟩,
      ⟨le_max_right _ _, max_le h₁ hs.1.le, le_max_right _ _, max_le h₃ hs.2.le⟩⟩

theorem intersects_interior_area_iff :
    Intersects (interior ((r.area hr : RegularClosedRegion) : Region))
        (interior ((s.area hs : RegularClosedRegion) : Region)) ↔
      r.xmin < s.xmax ∧ s.xmin < r.xmax ∧ r.ymin < s.ymax ∧ s.ymin < r.ymax := by
  rw [interior_area, interior_area]
  constructor
  · rintro ⟨p, ⟨a₁, a₂, a₃, a₄⟩, ⟨b₁, b₂, b₃, b₄⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    have hx := max_lt (lt_min hr.1 h₁) (lt_min h₂ hs.1)
    have hy := max_lt (lt_min hr.2 h₃) (lt_min h₄ hs.2)
    have := le_max_left r.xmin s.xmin
    have := le_max_right r.xmin s.xmin
    have := min_le_left r.xmax s.xmax
    have := min_le_right r.xmax s.xmax
    have := le_max_left r.ymin s.ymin
    have := le_max_right r.ymin s.ymin
    have := min_le_left r.ymax s.ymax
    have := min_le_right r.ymax s.ymax
    refine ⟨⟨(max r.xmin s.xmin + min r.xmax s.xmax) / 2,
      (max r.ymin s.ymin + min r.ymax s.ymax) / 2⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
      dsimp only <;> linarith

end Rect

/-- Two regions are equal exactly when each lies within the other. -/
theorem region_eq_iff (A B : Region) : A = B ↔ Within A B ∧ Within B A :=
  Set.Subset.antisymm_iff

namespace RCC8

/-- Decide an RCC8 relation between two `Rect.area`s with numeral coordinates:
reduce it to coordinate inequalities, then evaluate them. -/
macro "rect_rcc8" : tactic => `(tactic| (
  simp only [Relation.holds, DC, EC, PO, EQ, TPP, NTPP, TPPi, NTPPi, Touches, ne_eq,
    region_eq_iff, disjoint_iff_not_intersects, Rect.within_area_iff,
    Rect.within_interior_area_iff, Rect.intersects_area_iff,
    Rect.intersects_interior_area_iff] <;>
  norm_num))

/-- Some nonempty areas `A`, `B`, `C` have `r A B`, `s B C` and `t A C`. This
is membership in the weak composition `r ⋄ s`, stated here so the witnesses
do not depend on `Composition.lean`. -/
def Realizes (r s t : Relation) : Prop :=
  ∃ A B C : RegularClosedRegion,
    (A : Region).Nonempty ∧ (B : Region).Nonempty ∧ (C : Region).Nonempty ∧
    r.holds A B ∧ s.holds B C ∧ t.holds A C

/-- Three rectangles witness `Realizes r s t`. -/
theorem realizes_of_rects {r s t : Relation} (a b c : Rect)
    (ha : a.xmin < a.xmax ∧ a.ymin < a.ymax) (hb : b.xmin < b.xmax ∧ b.ymin < b.ymax)
    (hc : c.xmin < c.xmax ∧ c.ymin < c.ymax)
    (h₁ : r.holds (a.area ha) (b.area hb)) (h₂ : s.holds (b.area hb) (c.area hc))
    (h₃ : t.holds (a.area ha) (c.area hc)) : Realizes r s t :=
  ⟨_, _, _, a.area_nonempty ha, b.area_nonempty hb, c.area_nonempty hc, h₁, h₂, h₃⟩

/-- Reading a witness backwards gives a witness for the converses. -/
theorem Realizes.converse {r s t : Relation} (h : Realizes r s t) :
    Realizes s.converse r.converse t.converse := by
  obtain ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩ := h
  exact ⟨C, B, A, hC, hB, hA, (s.holds_converse C B).mpr hs,
    (r.holds_converse B A).mpr hr, (t.holds_converse C A).mpr ht⟩

/-- A rectangle strictly inside another is a non-tangential proper part of it. -/
theorem ntpp_of_rect {r s : Rect} (hr : r.xmin < r.xmax ∧ r.ymin < r.ymax)
    (hs : s.xmin < s.xmax ∧ s.ymin < s.ymax)
    (hx₁ : s.xmin < r.xmin) (hx₂ : r.xmax < s.xmax)
    (hy₁ : s.ymin < r.ymin) (hy₂ : r.ymax < s.ymax) :
    NTPP (r.area hr) (s.area hs) :=
  ⟨Rect.within_interior_of_bounds hx₁ hx₂ hy₁ hy₂,
    Rect.toRegion_ne_of_xmin_lt hx₁ hs.1.le hs.2.le⟩

/-- A rectangle entirely to the left of another is disconnected from it. -/
theorem dc_of_rect {r s : Rect} (hr : r.xmin < r.xmax ∧ r.ymin < r.ymax)
    (hs : s.xmin < s.xmax ∧ s.ymin < s.ymax) (hgap : r.xmax < s.xmin) :
    DC (r.area hr) (s.area hs) := by
  unfold DC Geospatial.Disjoint
  rw [Set.eq_empty_iff_forall_not_mem]
  rintro p ⟨⟨-, h₁, -⟩, ⟨h₂, -⟩⟩
  linarith

namespace Witnesses

noncomputable section

def rectA : Rect := ⟨0, 2, 0, 2⟩
def rectB : Rect := ⟨2, 4, 0, 2⟩
def rectC : Rect := ⟨1, 3, 0, 2⟩
def rectD : Rect := ⟨5, 6, 0, 2⟩
def rectN : Rect := ⟨1 / 2, 3 / 2, 1 / 2, 3 / 2⟩
def rectT : Rect := ⟨1, 2, 0, 1⟩

theorem hA : rectA.xmin < rectA.xmax ∧ rectA.ymin < rectA.ymax := by norm_num [rectA]
theorem hB : rectB.xmin < rectB.xmax ∧ rectB.ymin < rectB.ymax := by norm_num [rectB]
theorem hC : rectC.xmin < rectC.xmax ∧ rectC.ymin < rectC.ymax := by norm_num [rectC]
theorem hD : rectD.xmin < rectD.xmax ∧ rectD.ymin < rectD.ymax := by norm_num [rectD]
theorem hN : rectN.xmin < rectN.xmax ∧ rectN.ymin < rectN.ymax := by norm_num [rectN]
theorem hT : rectT.xmin < rectT.xmax ∧ rectT.ymin < rectT.ymax := by norm_num [rectT]

def areaA : RegularClosedRegion := rectA.area hA
def areaB : RegularClosedRegion := rectB.area hB
def areaC : RegularClosedRegion := rectC.area hC
def areaD : RegularClosedRegion := rectD.area hD
def areaN : RegularClosedRegion := rectN.area hN
def areaT : RegularClosedRegion := rectT.area hT

theorem A_D_dc : DC areaA areaD := dc_of_rect hA hD (by norm_num [rectA, rectD])

theorem A_B_ec : EC areaA areaB := by
  refine ⟨⟨⟨2, 1⟩, ?_, ?_⟩, ?_⟩
  · rw [areaA, Rect.mem_area]; norm_num [rectA]
  · rw [areaB, Rect.mem_area]; norm_num [rectB]
  · rw [Geospatial.Disjoint, areaA, areaB, Rect.interior_area, Rect.interior_area,
      Set.eq_empty_iff_forall_not_mem]
    rintro p ⟨⟨-, h₁, -⟩, ⟨h₂, -⟩⟩
    simp only [rectA, rectB] at h₁ h₂
    linarith

theorem A_C_po : PO areaA areaC := by
  refine ⟨⟨⟨3 / 2, 1⟩, ?_, ?_⟩, fun h => ?_, fun h => ?_⟩
  · rw [areaA, Rect.interior_area]
    show (0 : ℝ) < 3 / 2 ∧ (3 / 2 : ℝ) < 2 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) < 2
    norm_num
  · rw [areaC, Rect.interior_area]
    show (1 : ℝ) < 3 / 2 ∧ (3 / 2 : ℝ) < 3 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) < 2
    norm_num
  · have := h (show (⟨0, 1⟩ : Point2D) ∈ (areaA : Region) by
      rw [areaA, Rect.mem_area]; norm_num [rectA])
    rw [areaC, Rect.mem_area] at this
    norm_num [rectC] at this
  · have := h (show (⟨3, 1⟩ : Point2D) ∈ (areaC : Region) by
      rw [areaC, Rect.mem_area]; norm_num [rectC])
    rw [areaA, Rect.mem_area] at this
    norm_num [rectA] at this

theorem A_A_eq : EQ areaA areaA := rfl

theorem T_A_tpp : TPP areaT areaA := by
  refine ⟨Rect.within_of_bounds (by norm_num [rectT, rectA]) (by norm_num [rectT, rectA])
      (by norm_num [rectT, rectA]) (by norm_num [rectT, rectA]),
    Rect.toRegion_ne_of_xmin_lt (by norm_num [rectT, rectA]) hA.1.le hA.2.le,
    fun h => ?_⟩
  -- (2, 0) is in T but on A's right edge, not in A's interior.
  have := h (show (⟨2, 0⟩ : Point2D) ∈ (areaT : Region) by
    rw [areaT, Rect.mem_area]; norm_num [rectT])
  rw [areaA, Rect.interior_area] at this
  obtain ⟨-, h₂, -⟩ := this
  norm_num [rectA] at h₂

theorem N_A_ntpp : NTPP areaN areaA :=
  ntpp_of_rect hN hA (by norm_num [rectN, rectA]) (by norm_num [rectN, rectA])
    (by norm_num [rectN, rectA]) (by norm_num [rectN, rectA])

theorem A_T_tppi : TPPi areaA areaT := T_A_tpp

theorem A_N_ntppi : NTPPi areaA areaN := N_A_ntpp

/-! Three nested squares with room between them, for `NTPP ⋄ NTPP`. -/

def innerSq : Rect := ⟨1, 2, 1, 2⟩
def middleSq : Rect := ⟨0, 3, 0, 3⟩
def outerSq : Rect := ⟨-1, 4, -1, 4⟩

theorem hInner : innerSq.xmin < innerSq.xmax ∧ innerSq.ymin < innerSq.ymax := by
  norm_num [innerSq]
theorem hMiddle : middleSq.xmin < middleSq.xmax ∧ middleSq.ymin < middleSq.ymax := by
  norm_num [middleSq]
theorem hOuter : outerSq.xmin < outerSq.xmax ∧ outerSq.ymin < outerSq.ymax := by
  norm_num [outerSq]

theorem inner_middle_ntpp : NTPP (innerSq.area hInner) (middleSq.area hMiddle) :=
  ntpp_of_rect hInner hMiddle (by norm_num [innerSq, middleSq])
    (by norm_num [innerSq, middleSq]) (by norm_num [innerSq, middleSq])
    (by norm_num [innerSq, middleSq])

theorem middle_outer_ntpp : NTPP (middleSq.area hMiddle) (outerSq.area hOuter) :=
  ntpp_of_rect hMiddle hOuter (by norm_num [middleSq, outerSq])
    (by norm_num [middleSq, outerSq]) (by norm_num [middleSq, outerSq])
    (by norm_num [middleSq, outerSq])

theorem inner_outer_ntpp : NTPP (innerSq.area hInner) (outerSq.area hOuter) :=
  ntpp_of_rect hInner hOuter (by norm_num [innerSq, outerSq])
    (by norm_num [innerSq, outerSq]) (by norm_num [innerSq, outerSq])
    (by norm_num [innerSq, outerSq])

end

end Witnesses

open Witnesses in
/-- Every base relation holds between some pair of nonempty areas. -/
theorem Relation.realizable (r : Relation) :
    ∃ A C : RegularClosedRegion, (A : Region).Nonempty ∧ (C : Region).Nonempty ∧
      r.holds A C := by
  have nA := rectA.area_nonempty hA
  cases r with
  | dc => exact ⟨areaA, areaD, nA, rectD.area_nonempty hD, A_D_dc⟩
  | ec => exact ⟨areaA, areaB, nA, rectB.area_nonempty hB, A_B_ec⟩
  | po => exact ⟨areaA, areaC, nA, rectC.area_nonempty hC, A_C_po⟩
  | eq => exact ⟨areaA, areaA, nA, nA, A_A_eq⟩
  | tpp => exact ⟨areaT, areaA, rectT.area_nonempty hT, nA, T_A_tpp⟩
  | ntpp => exact ⟨areaN, areaA, rectN.area_nonempty hN, nA, N_A_ntpp⟩
  | tppi => exact ⟨areaA, areaT, nA, rectT.area_nonempty hT, A_T_tppi⟩
  | ntppi => exact ⟨areaA, areaN, nA, rectN.area_nonempty hN, A_N_ntppi⟩

/-- `EQ` then `s` realises `s`. -/
theorem realizes_eq_left (s : Relation) : Realizes .eq s s := by
  obtain ⟨A, C, hA, hC, h⟩ := s.realizable
  exact ⟨A, A, C, hA, hA, hC, rfl, h, h⟩

/-- `r` then `EQ` realises `r`. -/
theorem realizes_eq_right (r : Relation) : Realizes r .eq r := by
  obtain ⟨A, C, hA, hC, h⟩ := r.realizable
  exact ⟨A, C, C, hA, hC, hC, h, rfl, h⟩

end RCC8

end Geospatial
