import LeanGeospatial.GeoSPARQL.AreaArea
import LeanGeospatial.RCC8Witnesses

/-!
# Where the Table 8 patterns are stricter than RCC8

For each of `EQ`, `NTPP`, `NTPPi`, `EC`, `PO`, `TPP`, `TPPi`, two nonempty
areas that stand in the relation but do not match its GeoSPARQL 1.1 Table 8
pattern. The patterns fully specify all nine cells, which fits two bounded
areas with connected interiors and no holes, but not areas in general:

| Relation | Areas | Cell the pattern gets wrong |
| --- | --- | --- |
| `EQ` | the whole plane, twice | `BB` (the plane has no boundary) |
| `NTPP` | a square inside the whole plane | `EB` |
| `NTPPi` | the whole plane around a square | `BE` |
| `EC` | a square and a frame around it (a polygon with a hole) | `BE` |
| `TPP` | a square and the square plus a separate square | `BI` |
| `TPPi` | the same, the other way round | `IB` |
| `PO` | two two-part areas sharing one part | `IB` |

The squares: `S₁ = [0,1]²`, `S₂ = [5,6]×[0,1]`, `S₃ = [0,1]×[5,6]`. The frame
is four rectangles around `S₁`.
-/

namespace Geospatial.GeoSPARQL.Counterexamples

open Geospatial Geospatial.RCC8 Geospatial.DE9IM Geospatial.GeoSPARQL

noncomputable section

def s1 : Rect := ⟨0, 1, 0, 1⟩
def s2 : Rect := ⟨5, 6, 0, 1⟩
def s3 : Rect := ⟨0, 1, 5, 6⟩

theorem h1 : s1.xmin < s1.xmax ∧ s1.ymin < s1.ymax := by norm_num [s1]
theorem h2 : s2.xmin < s2.xmax ∧ s2.ymin < s2.ymax := by norm_num [s2]
theorem h3 : s3.xmin < s3.xmax ∧ s3.ymin < s3.ymax := by norm_num [s3]

def S1 : RegularClosedRegion := s1.area h1
def S2 : RegularClosedRegion := s2.area h2
def S3 : RegularClosedRegion := s3.area h3

theorem S1_nonempty : (S1 : Region).Nonempty := s1.area_nonempty h1

theorem univ_nonempty : (RCC8.univ : Region).Nonempty := ⟨⟨0, 0⟩, trivial⟩

@[simp] theorem coe_univ : (RCC8.univ : Region) = Set.univ := rfl

/-! ## The whole plane -/

theorem eq_counterexample :
    ∃ A B : RegularClosedRegion, (A : Region).Nonempty ∧ (B : Region).Nonempty ∧
      EQ A B ∧ ¬ (rcc8Pattern .eq).Matches A B := by
  refine ⟨RCC8.univ, RCC8.univ, univ_nonempty, univ_nonempty, rfl, fun h => ?_⟩
  simp only [rcc8Pattern_eq_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
    at h
  obtain ⟨-, -, -, -, ⟨p, hp, -⟩, -⟩ := h
  have : p ∈ boundary (Set.univ : Region) := hp
  rw [boundary, frontier_univ] at this
  exact this

theorem S1_ne_univ : (S1 : Region) ≠ Set.univ := fun h => by
  have : (⟨5, 5⟩ : Point2D) ∈ (S1 : Region) := by rw [h]; trivial
  rw [S1, Rect.mem_area] at this
  norm_num [s1] at this

theorem S1_ntpp_univ : NTPP S1 RCC8.univ :=
  ⟨by rw [coe_univ, interior_univ]; exact Set.subset_univ _, S1_ne_univ⟩

theorem ntpp_counterexample :
    ∃ A B : RegularClosedRegion, (A : Region).Nonempty ∧ (B : Region).Nonempty ∧
      NTPP A B ∧ ¬ (rcc8Pattern .ntpp).Matches A B := by
  refine ⟨S1, RCC8.univ, S1_nonempty, univ_nonempty, S1_ntpp_univ, fun h => ?_⟩
  simp only [rcc8Pattern_ntpp_eq, Pattern.Matches, PatternChar.matches_T,
    PatternChar.matches_F] at h
  obtain ⟨-, -, -, -, -, -, -, ⟨p, -, hp⟩, -⟩ := h
  have : p ∈ boundary (Set.univ : Region) := hp
  rw [boundary, frontier_univ] at this
  exact this

theorem ntppi_counterexample :
    ∃ A B : RegularClosedRegion, (A : Region).Nonempty ∧ (B : Region).Nonempty ∧
      NTPPi A B ∧ ¬ (rcc8Pattern .ntppi).Matches A B := by
  refine ⟨RCC8.univ, S1, univ_nonempty, S1_nonempty, S1_ntpp_univ, fun h => ?_⟩
  rw [rcc8Pattern_ntppi, Pattern.matches_transpose] at h
  simp only [rcc8Pattern_ntpp_eq, Pattern.Matches, PatternChar.matches_T,
    PatternChar.matches_F] at h
  obtain ⟨-, -, -, -, -, -, -, ⟨p, -, hp⟩, -⟩ := h
  have : p ∈ boundary (Set.univ : Region) := hp
  rw [boundary, frontier_univ] at this
  exact this

/-! ## A square in a frame -/

def r1 : Rect := ⟨-1, 2, -1, 0⟩
def r2 : Rect := ⟨-1, 2, 1, 2⟩
def r3 : Rect := ⟨-1, 0, 0, 1⟩
def r4 : Rect := ⟨1, 2, 0, 1⟩

/-- The frame `[-1,2]² \ (0,1)²`, as four rectangles. -/
def frame : RegularClosedRegion :=
  (((r1.area (by norm_num [r1])).union (r2.area (by norm_num [r2]))).union
    (r3.area (by norm_num [r3]))).union (r4.area (by norm_num [r4]))

theorem mem_frame (p : Point2D) :
    p ∈ (frame : Region) ↔
      ((-1 ≤ p.x ∧ p.x ≤ 2 ∧ -1 ≤ p.y ∧ p.y ≤ 0) ∨ (-1 ≤ p.x ∧ p.x ≤ 2 ∧ 1 ≤ p.y ∧ p.y ≤ 2)) ∨
        (-1 ≤ p.x ∧ p.x ≤ 0 ∧ 0 ≤ p.y ∧ p.y ≤ 1) ∨ (1 ≤ p.x ∧ p.x ≤ 2 ∧ 0 ≤ p.y ∧ p.y ≤ 1) := by
  simp only [frame, RegularClosedRegion.coe_union, Set.mem_union, Rect.mem_area, r1, r2, r3, r4]
  tauto

theorem S1_ec_frame : EC S1 frame := by
  refine ⟨⟨⟨0, 0⟩, ?_, ?_⟩, ?_⟩
  · rw [S1, Rect.mem_area]; norm_num [s1]
  · rw [mem_frame]; norm_num
  · rw [Geospatial.Disjoint, Set.eq_empty_iff_forall_not_mem]
    rintro p ⟨hpA, hpB⟩
    rw [S1, Rect.interior_area] at hpA
    obtain ⟨a₁, a₂, a₃, a₄⟩ := hpA
    have := (mem_frame p).mp (interior_subset hpB)
    simp only [s1] at a₁ a₂ a₃ a₄
    rcases this with (⟨-, -, -, h⟩ | ⟨-, -, h, -⟩) | (⟨-, h, -, -⟩ | ⟨h, -, -, -⟩) <;> linarith

theorem ec_counterexample :
    ∃ A B : RegularClosedRegion, (A : Region).Nonempty ∧ (B : Region).Nonempty ∧
      EC A B ∧ ¬ (rcc8Pattern .ec).Matches A B := by
  refine ⟨S1, frame, S1_nonempty, ⟨⟨0, 0⟩, by rw [mem_frame]; norm_num⟩, S1_ec_frame,
    fun h => ?_⟩
  simp only [rcc8Pattern_ec_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
    at h
  obtain ⟨-, -, -, -, -, ⟨p, hp, hpE⟩, -⟩ := h
  -- Every boundary point of the square lies on the frame.
  change p ∈ boundary (S1 : Region) at hp
  change p ∈ exterior (frame : Region) at hpE
  rw [exterior_eq_of_isClosed frame.isClosed] at hpE
  rw [S1, Rect.area, Rect.coe_toRegularClosed, Rect.boundary_toRegion] at hp
  obtain ⟨⟨b₁, b₂, b₃, b₄⟩, hnot⟩ := hp
  apply hpE
  rw [mem_frame]
  simp only [s1, Rect.openRegion, Set.mem_setOf_eq, not_and_or, not_lt] at b₁ b₂ b₃ b₄ hnot
  rcases hnot with h | h | h | h
  · exact Or.inr (Or.inl ⟨by linarith, by linarith, b₃, b₄⟩)
  · exact Or.inr (Or.inr ⟨h, by linarith, b₃, b₄⟩)
  · exact Or.inl (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)
  · exact Or.inl (Or.inr ⟨by linarith, by linarith, h, by linarith⟩)

/-! ## Areas in two parts -/

/-- `S₁` and a separate square: a multi-polygon. -/
def S12 : RegularClosedRegion := S1.union S2
def S13 : RegularClosedRegion := S1.union S3

theorem S1_S2_apart (p : Point2D) (h₁ : p ∈ (S1 : Region)) (h₂ : p ∈ (S2 : Region)) : False := by
  rw [S1, Rect.mem_area] at h₁
  rw [S2, Rect.mem_area] at h₂
  simp only [s1, s2] at h₁ h₂
  linarith [h₁.2.1, h₂.1]

theorem S1_S3_apart (p : Point2D) (h₁ : p ∈ (S1 : Region)) (h₃ : p ∈ (S3 : Region)) : False := by
  rw [S1, Rect.mem_area] at h₁
  rw [S3, Rect.mem_area] at h₃
  simp only [s1, s3] at h₁ h₃
  linarith [h₁.2.2.2, h₃.2.2.1]

theorem S2_S3_apart (p : Point2D) (h₂ : p ∈ (S2 : Region)) (h₃ : p ∈ (S3 : Region)) : False := by
  rw [S2, Rect.mem_area] at h₂
  rw [S3, Rect.mem_area] at h₃
  simp only [s2, s3] at h₂ h₃
  linarith [h₂.2.2.2, h₃.2.2.1]

/-- Adding a closed part far away does not add interior points near `S₁`. -/
theorem interior_union_subset (X Y : RegularClosedRegion) :
    interior ((X.union Y : RegularClosedRegion) : Region) ⊆
      interior (X : Region) ∪ (Y : Region) :=
  IsClosed.interior_union_right Y.isClosed

theorem not_mem_interior_S1_of_boundary {p : Point2D} (hp : p ∈ boundary (S1 : Region)) :
    p ∉ interior (S1 : Region) := hp.2

theorem S1_tpp_S12 : TPP S1 S12 := by
  refine ⟨Set.subset_union_left, fun h => ?_, fun h => ?_⟩
  · have hp : (⟨5, 0⟩ : Point2D) ∈ (S12 : Region) :=
      Set.mem_union_right _ (by rw [S2, Rect.mem_area]; norm_num [s2])
    rw [← h, S1, Rect.mem_area] at hp
    norm_num [s1] at hp
  · have hp : (⟨0, 0⟩ : Point2D) ∈ (S1 : Region) := by rw [S1, Rect.mem_area]; norm_num [s1]
    rcases interior_union_subset S1 S2 (h hp) with h' | h'
    · rw [S1, Rect.interior_area] at h'
      obtain ⟨h'', -⟩ := h'
      norm_num [s1] at h''
    · rw [S2, Rect.mem_area] at h'
      norm_num [s2] at h'

theorem tpp_counterexample :
    ∃ A B : RegularClosedRegion, (A : Region).Nonempty ∧ (B : Region).Nonempty ∧
      TPP A B ∧ ¬ (rcc8Pattern .tpp).Matches A B := by
  refine ⟨S1, S12, S1_nonempty, S1_nonempty.mono Set.subset_union_left, S1_tpp_S12,
    fun h => ?_⟩
  simp only [rcc8Pattern_tpp_eq, Pattern.Matches, PatternChar.matches_T, PatternChar.matches_F]
    at h
  obtain ⟨-, -, -, ⟨p, hp, hpI⟩, -⟩ := h
  change p ∈ boundary (S1 : Region) at hp
  change p ∈ interior (S12 : Region) at hpI
  rcases interior_union_subset S1 S2 hpI with h' | h'
  · exact hp.2 h'
  · exact S1_S2_apart p (boundary_subset_of_isClosed S1.isClosed hp) h'

theorem tppi_counterexample :
    ∃ A B : RegularClosedRegion, (A : Region).Nonempty ∧ (B : Region).Nonempty ∧
      TPPi A B ∧ ¬ (rcc8Pattern .tppi).Matches A B := by
  obtain ⟨A, B, hA, hB, h, hno⟩ := tpp_counterexample
  refine ⟨B, A, hB, hA, h, fun hm => hno ?_⟩
  rwa [rcc8Pattern_tppi, Pattern.matches_transpose] at hm

theorem S12_po_S13 : PO S12 S13 := by
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · refine ⟨⟨1 / 2, 1 / 2⟩, interior_mono Set.subset_union_left ?_,
      interior_mono Set.subset_union_left ?_⟩ <;>
    · rw [S1, Rect.interior_area]
      show (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1
      norm_num
  · have hp : (⟨5, 0⟩ : Point2D) ∈ (S2 : Region) := by rw [S2, Rect.mem_area]; norm_num [s2]
    rcases h (Set.mem_union_right _ hp) with h' | h'
    · exact S1_S2_apart _ h' hp
    · exact S2_S3_apart _ hp h'
  · have hp : (⟨0, 5⟩ : Point2D) ∈ (S3 : Region) := by rw [S3, Rect.mem_area]; norm_num [s3]
    rcases h (Set.mem_union_right _ hp) with h' | h'
    · exact S1_S3_apart _ h' hp
    · exact S2_S3_apart _ h' hp

theorem po_counterexample :
    ∃ A B : RegularClosedRegion, (A : Region).Nonempty ∧ (B : Region).Nonempty ∧
      PO A B ∧ ¬ (rcc8Pattern .po).Matches A B := by
  refine ⟨S12, S13, S1_nonempty.mono Set.subset_union_left,
    S1_nonempty.mono Set.subset_union_left, S12_po_S13, fun h => ?_⟩
  simp only [rcc8Pattern_po_eq, Pattern.Matches, PatternChar.matches_T] at h
  obtain ⟨-, ⟨p, hpI, hpB⟩, -⟩ := h
  change p ∈ interior (S12 : Region) at hpI
  change p ∈ boundary (S13 : Region) at hpB
  have hpS13 := boundary_subset_of_isClosed S13.isClosed hpB
  rcases hpS13 with hp1 | hp3
  · -- On S₁: it is interior to S₁₂ only through S₁, which makes it interior to S₁₃.
    rcases interior_union_subset S1 S2 hpI with h' | h'
    · exact hpB.2 (interior_mono Set.subset_union_left h')
    · exact S1_S2_apart p hp1 h'
  · -- On S₃: S₁₂ does not reach it.
    rcases interior_subset hpI with h' | h'
    · exact S1_S3_apart p h' hp3
    · exact S2_S3_apart p h' hp3

end

end Geospatial.GeoSPARQL.Counterexamples
