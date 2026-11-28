import LeanGeospatial.SpatialPartition
import LeanGeospatial.Spaces.Unified

/-!
# Common Hierarchical Spatial Partition Semantics across `ℝ²`, `S²`, and `ℝ³`

Extends `LeanGeospatial.SpatialPartition` to the 2-sphere `S²` without
duplicating any abstract partition theory:

1. **General pullback & face-indexed constructions** (`SpatialPartition.pullback`,
   `HierarchicalPartition.pullback`, `HierarchicalPartition.faceIndexed`):
   pulling back any `HierarchicalPartition β` along a map `f : α → β` (or
   indexing by a finite face type `F`) automatically preserves exhaustiveness,
   exclusivity, parent-child containment, inner/outer approximation soundness,
   refinement monotonicity, and cell-covering relation soundness.
2. **Spherical hierarchical partition (`sphericalHierarchy : HierarchicalPartition S2`)**:
   - Deterministic 6-face cube projection `cubeFace : S2 → CubeFace` (dominant
     coordinate axis + sign) with gnomonic face coordinates `faceUV : S2 → E2`.
   - Level-`z` cells are indexed by `CubeFace × (Fin 2 → ℤ)`, partitioning `S²`
     exhaustively and pairwise exclusively at every resolution `z : ℕ`.
   - Every parent cell is the exact union of its children
     (`sphericalHierarchy.parent_eq_iUnion_children`).
3. **Spherical resolution information loss & false-positive intersection**:
   - `counterexample_spherical_resolution_loss`: at every finite level `z`,
     distinct points on `S²` map to the exact same spherical cell ID.
   - `counterexample_spherical_same_cell_not_intersects`: at every finite level
     `z`, disjoint nonempty subsets of `S²` share the same spherical cell ID.
4. **Unified 3-space view**:
   - `ℝ²` (`quadtreeHierarchy`), `S²` (`sphericalHierarchy`), and `ℝ³`
     (`octreeHierarchy`) are all instances of the exact same
     `HierarchicalPartition` structure.
-/

namespace Geospatial.Spaces

open Set Geospatial Geospatial.Partition Geospatial.DE9IM.Space3

/-! ## 1. General pullback and face-indexed hierarchical partitions -/

/-- Pull back a `SpatialPartition` along any map `f : α → β`. -/
def _root_.Geospatial.Partition.SpatialPartition.pullback {ι α β : Type*}
    (P : SpatialPartition ι β) (f : α → β) : SpatialPartition ι α where
  cell i := f ⁻¹' P.cell i
  exhaustive x := P.exhaustive (f x)
  exclusive i j hij := by
    rw [Geospatial.Disjoint, ← preimage_inter]
    have h : P.cell i ∩ P.cell j = ∅ := P.exclusive i j hij
    rw [h, preimage_empty]

/-- Pull back a `HierarchicalPartition` along any map `f : α → β`. -/
def _root_.Geospatial.Partition.HierarchicalPartition.pullback {α β : Type*}
    (H : HierarchicalPartition β) (f : α → β) : HierarchicalPartition α where
  Idx := H.Idx
  level z := (H.level z).pullback f
  parent := H.parent
  child_subset_parent c := preimage_mono (H.child_subset_parent c)

/-- Combine a face assignment `face : α → F` with a `SpatialPartition` on `β`
via `coord : α → β`. -/
def _root_.Geospatial.Partition.SpatialPartition.faceIndexed {F ι α β : Type*}
    (face : α → F) (coord : α → β) (P : SpatialPartition ι β) :
    SpatialPartition (F × ι) α where
  cell p := {x | face x = p.1 ∧ coord x ∈ P.cell p.2}
  exhaustive x := by
    obtain ⟨i, hi⟩ := P.exhaustive (coord x)
    exact ⟨(face x, i), rfl, hi⟩
  exclusive p q hpq := by
    rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro x ⟨⟨hf1, hc1⟩, ⟨hf2, hc2⟩⟩
    apply hpq
    apply Prod.ext
    · exact hf1.symm.trans hf2
    · by_contra hne
      have hdisj : P.cell p.2 ∩ P.cell q.2 = ∅ := P.exclusive p.2 q.2 hne
      have : coord x ∈ P.cell p.2 ∩ P.cell q.2 := ⟨hc1, hc2⟩
      rw [hdisj] at this
      exact this

/-- Combine a face assignment `face : α → F` with a `HierarchicalPartition` on
`β` via `coord : α → β`. -/
def _root_.Geospatial.Partition.HierarchicalPartition.faceIndexed {F : Type} {α β : Type*}
    (face : α → F) (coord : α → β) (H : HierarchicalPartition β) :
    HierarchicalPartition α where
  Idx z := F × H.Idx z
  level z := (H.level z).faceIndexed face coord
  parent c := (c.1, H.parent c.2)
  child_subset_parent c := fun _ ⟨hf, hc⟩ => ⟨hf, H.child_subset_parent c.2 hc⟩

/-! ## 2. Cube-face gnomonic hierarchical partition of `S²` -/

/-- The six faces of the inscribed/circumscribed cube around `S²`. -/
inductive CubeFace : Type
  | posX | negX | posY | negY | posZ | negZ
  deriving DecidableEq, Repr

/-- Deterministic dominant-axis + sign face assignment on `S²`. -/
noncomputable def cubeFace (p : S2) : CubeFace :=
  let x := p.1 0
  let y := p.1 1
  let z := p.1 2
  if |y| ≤ |x| ∧ |z| ≤ |x| then
    if 0 ≤ x then .posX else .negX
  else if |z| ≤ |y| then
    if 0 ≤ y then .posY else .negY
  else
    if 0 ≤ z then .posZ else .negZ

/-- Gnomonic face coordinates `(u, v) ∈ [-1, 1]²` on the dominant face of `p ∈ S²`. -/
noncomputable def faceUV (p : S2) : E2 :=
  let x := p.1 0
  let y := p.1 1
  let z := p.1 2
  match cubeFace p with
  | .posX | .negX => Point2D.mk (y / |x|) (z / |x|)
  | .posY | .negY => Point2D.mk (x / |y|) (z / |y|)
  | .posZ | .negZ => Point2D.mk (x / |z|) (y / |z|)

/-- **Spherical hierarchical spatial partition** on `S²`:
6 cube faces refined by a 2D dyadic quadtree (`dyadicHierarchy 2`) in gnomonic
face coordinates. Automatically inherits exhaustiveness, exclusivity,
parent-child containment, inner/outer approximation soundness, and refinement
monotonicity from `HierarchicalPartition`. -/
noncomputable def sphericalHierarchy : HierarchicalPartition S2 :=
  (dyadicHierarchy 2).faceIndexed cubeFace faceUV

/-- Every point on `S²` belongs to a unique spherical cell at level `z`. -/
theorem spherical_existsUnique_cell (z : ℕ) (p : S2) :
    ∃! i : CubeFace × (Fin 2 → ℤ), p ∈ (sphericalHierarchy.level z).cell i :=
  (sphericalHierarchy.level z).existsUnique_cell p

/-- Soundness of outer-cover disjointness on `S²`. -/
theorem spherical_disjoint_of_outerCover_disjoint (z : ℕ) {A B : Set S2}
    (h : Geospatial.Disjoint ((sphericalHierarchy.level z).outerCover A)
                             ((sphericalHierarchy.level z).outerCover B)) :
    Geospatial.Disjoint A B :=
  (sphericalHierarchy.level z).disjoint_of_outerCover_disjoint h

/-- Resolution refinement monotonically tightens outer approximations on `S²`. -/
theorem spherical_outerApprox_antitone (z : ℕ) (A : Set S2) :
    (sphericalHierarchy.level (z + 1)).outerApprox A ⊆
      (sphericalHierarchy.level z).outerApprox A :=
  sphericalHierarchy.outerApprox_antitone z A

/-! ## 3. Spherical resolution information loss & false-positive counterexamples -/

/-- **Spherical resolution information loss**: at every finite resolution `z`,
there exist two **distinct** points on `S²` that receive the exact same
spherical cell ID. -/
theorem counterexample_spherical_resolution_loss (z : ℕ) :
    ∃ p q : S2, p ≠ q ∧
      (sphericalHierarchy.level z).idOf p = (sphericalHierarchy.level z).idOf q := by
  have h2z_pos : (0 : ℝ) < (2 : ℝ) ^ z := by positivity
  let ε : ℝ := 1 / (2 : ℝ) ^ (z + 1)
  have hε_pos : 0 < ε := by positivity
  have hε_lt : ε < 1 / (2 : ℝ) ^ z := by
    simp only [ε, pow_succ]
    rw [div_lt_div_iff₀ (by positivity) h2z_pos]
    nlinarith
  have hε_lt_one : ε < 1 := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ z := one_le_pow₀ (by norm_num)
    have : 1 / (2 : ℝ) ^ z ≤ 1 := div_le_one_of_le₀ h1 (by positivity)
    linarith
  let r : ℝ := Real.sqrt (1 + ε ^ 2)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr_sq : r ^ 2 = 1 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hq_mem : pt (ε / r) 0 (1 / r) ∈ S2 := by
    rw [S2, Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq]
    rw [Fin.sum_univ_three]
    have hsum : ‖pt (ε / r) 0 (1 / r) 0‖ ^ 2 + ‖pt (ε / r) 0 (1 / r) 1‖ ^ 2 +
        ‖pt (ε / r) 0 (1 / r) 2‖ ^ 2 = 1 := by
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Real.norm_eq_abs, sq_abs]
      have hr0 : r ≠ 0 := hr_pos.ne'
      field_simp
      linarith
    rw [hsum, Real.sqrt_one]
  let q : S2 := ⟨pt (ε / r) 0 (1 / r), hq_mem⟩
  -- Both northPole and q lie in cell (.posZ, fun _ => 0)
  have hface_N : cubeFace northPole = .posZ := by
    unfold cubeFace northPole
    norm_num
  have huv_N : faceUV northPole = Point2D.mk 0 0 := by
    unfold faceUV
    rw [hface_N]
    simp [northPole]
  have hface_q : cubeFace q = .posZ := by
    unfold cubeFace
    have h0 : q.1 0 = ε / r := rfl
    have h1 : q.1 1 = 0 := rfl
    have h2 : q.1 2 = 1 / r := rfl
    rw [h0, h1, h2]
    dsimp only
    have habs0 : |ε / r| = ε / r := abs_of_pos (div_pos hε_pos hr_pos)
    have habs1 : |(0 : ℝ)| = 0 := abs_zero
    have habs2 : |1 / r| = 1 / r := abs_of_pos (div_pos one_pos hr_pos)
    have hlt : ε / r < 1 / r := (div_lt_div_iff_of_pos_right hr_pos).mpr hε_lt_one
    have hpos : (0 : ℝ) < 1 / r := div_pos one_pos hr_pos
    rw [habs0, habs1, habs2]
    rw [if_neg (by push_neg; intro _; exact hlt)]
    rw [if_neg (by linarith)]
    rw [if_pos hpos.le]
  have huv_q : faceUV q = Point2D.mk ε 0 := by
    unfold faceUV
    rw [hface_q]
    have h0 : q.1 0 = ε / r := rfl
    have h1 : q.1 1 = 0 := rfl
    have h2 : q.1 2 = 1 / r := rfl
    rw [h0, h1, h2]
    dsimp only
    rw [abs_of_pos (div_pos one_pos hr_pos)]
    apply Point2D.ext
    · simp only [Point2D.x_mk]
      have hr0 : r ≠ 0 := hr_pos.ne'
      field_simp
    · simp
  let cid : CubeFace × (Fin 2 → ℤ) := (.posZ, fun _ => 0)
  have hN_mem : northPole ∈ (sphericalHierarchy.level z).cell cid := by
    refine ⟨hface_N, ?_⟩
    rw [huv_N]
    intro k; fin_cases k <;> simp [cid, Point2D.mk, h2z_pos]
  have hq_cell : q ∈ (sphericalHierarchy.level z).cell cid := by
    refine ⟨hface_q, ?_⟩
    rw [huv_q]
    intro k; fin_cases k
    · simp only [cid, Point2D.mk, Int.cast_zero, zero_div, zero_add]
      exact ⟨hε_pos.le, hε_lt⟩
    · simp [cid, Point2D.mk, h2z_pos]
  refine ⟨northPole, q, ?_, ?_⟩
  · intro heq
    have h0 := congrArg (fun p : S2 => p.1 0) heq
    have hN0 : northPole.1 0 = 0 := rfl
    have hq0 : q.1 0 = ε / r := rfl
    rw [hN0, hq0] at h0
    have : 0 < ε / r := div_pos hε_pos hr_pos
    linarith
  · rw [(sphericalHierarchy.level z).idOf_eq_of_mem hN_mem,
        (sphericalHierarchy.level z).idOf_eq_of_mem hq_cell]

/-- **Sharing a spherical cell does NOT imply intersection on `S²`**:
at every finite level `z`, there exist two **disjoint** nonempty subsets of `S²`
whose outer coverings share a common cell ID. -/
theorem counterexample_spherical_same_cell_not_intersects (z : ℕ) :
    ∃ (A B : Set S2), A.Nonempty ∧ B.Nonempty ∧
      Geospatial.Disjoint A B ∧
      Intersects ((sphericalHierarchy.level z).outerCover A)
                 ((sphericalHierarchy.level z).outerCover B) := by
  obtain ⟨p, q, hpq, hid⟩ := counterexample_spherical_resolution_loss z
  refine ⟨{p}, {q}, ⟨p, rfl⟩, ⟨q, rfl⟩, ?_, ?_⟩
  · rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro x ⟨rfl, hx⟩
    exact hpq hx
  · refine ⟨(sphericalHierarchy.level z).idOf p,
      ⟨p, (sphericalHierarchy.level z).mem_cell_idOf p, rfl⟩,
      ⟨q, hid ▸ (sphericalHierarchy.level z).mem_cell_idOf q, rfl⟩⟩

end Geospatial.Spaces
