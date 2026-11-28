import LeanGeospatial.Approximation2D3D
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Hierarchical Spatial Partitions and Discrete Spatial Identifiers

Defines the mathematical semantics of spatial partitioning independently of any
vendor-specific spatial ID encoding (S2, H3, Geohash, ZFXY/3D Spatial ID):

1. **Abstract partitions & hierarchies** (over any space `α`):
   - `Grid ι α`: an indexed family of cells `ι → Set α`.
   - `SpatialPartition ι α`: a grid that is **exhaustive** (covers `α`) and
     **pairwise exclusive** (distinct cells are disjoint), so every point lies
     in a unique cell (`existsUnique_cell`).
   - `HierarchicalPartition α`: level-indexed partitions (`z : ℕ`) with a
     `parent` map such that every child cell lies inside its parent and every
     parent cell is the exact union of its children.
   - `CellCovering`: `outerCover`, `innerCover`, `outerApprox`, `innerApprox`.
   - Soundness theorems for inner/outer approximations, resolution refinement
     monotonicity (`outerApprox_antitone`, `innerApprox_monotone`), and derived
     spatial relations (`disjoint_of_outerCover_disjoint`,
     `within_of_outerCover_subset_innerCover`,
     `intersects_of_innerCover_intersects`).

2. **Dimension-unified `d`-dimensional dyadic hierarchy** on `EuclideanSpace ℝ (Fin d)`:
   - Half-open dyadic cells `∏ k, [c k / 2^z, (c k + 1) / 2^z)` form an exact
     `HierarchicalPartition` for every dimension `d` (`dyadicHierarchy d`).
   - `Quadtree` (`d = 2`, 4 children per cell) and `Octree` (`d = 3`, 8 children
     per cell) are direct instantiations sharing the exact same proofs.
   - Closed dyadic cells (`[c k / 2^z, (c k + 1) / 2^z]`) violate exclusivity on
     shared boundaries (`closedCell_adjacent_overlap`), formalizing the
     fundamental boundary-handling tradeoff.

3. **Resolution information loss and false-positive counterexamples**:
   - `counterexample_resolution_information_loss`: at every finite level `z`,
     distinct points map to the same cell ID.
   - `counterexample_same_cell_not_intersects`: at every finite level `z`, two
     **disjoint** regions share the same cell (sharing a cell ≠ intersecting in
     real space).
   - `counterexample_outerCover_subset_not_within`: `outerCover A ⊆ outerCover B`
     does NOT imply `Within A B`.

## Universal mathematics vs spatial-ID-specific properties

Properties proved here (exhaustiveness, exclusivity of half-open cells,
parent-child containment, refinement monotonicity, soundness of outer-cover
disjointness, and non-soundness of same-cell intersection) hold for **every**
hierarchical spatial partition in any dimension. Properties such as Morton/Z-order
bit interleaving, Web Mercator latitude clamping (`±85.0511°`), or hexagonal
non-containment (H3) are specific to individual encoding schemes, not to
hierarchical partitioning itself.
-/

namespace Geospatial.Partition

open Set Geospatial

/-! ## 1. Abstract Grid, SpatialPartition, and CellCovering -/

/-- A grid over `α` indexed by `ι` assigns a cell (subset of `α`) to each index. -/
abbrev Grid (ι α : Type*) := ι → Set α

/-- A spatial partition of `α` indexed by `ι`: exhaustive and pairwise exclusive. -/
structure SpatialPartition (ι α : Type*) where
  cell : Grid ι α
  exhaustive : ∀ x : α, ∃ i : ι, x ∈ cell i
  exclusive : ∀ i j : ι, i ≠ j → Geospatial.Disjoint (cell i) (cell j)

namespace SpatialPartition

variable {ι α : Type*} (P : SpatialPartition ι α)

/-- Every point of `α` belongs to a **unique** cell of the partition. -/
theorem existsUnique_cell (x : α) : ∃! i : ι, x ∈ P.cell i := by
  obtain ⟨i, hi⟩ := P.exhaustive x
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hji
  have hdisj := P.exclusive j i hji
  have : x ∈ P.cell j ∩ P.cell i := ⟨hj, hi⟩
  rw [hdisj] at this
  exact this

/-- The unique spatial identifier (cell index) containing a point `x`. -/
noncomputable def idOf (x : α) : ι :=
  Classical.choose (P.existsUnique_cell x).exists

theorem mem_cell_idOf (x : α) : x ∈ P.cell (P.idOf x) :=
  Classical.choose_spec (P.existsUnique_cell x).exists

theorem idOf_eq_of_mem {x : α} {i : ι} (h : x ∈ P.cell i) : P.idOf x = i :=
  (P.existsUnique_cell x).unique (P.mem_cell_idOf x) h

/-! ### Cell coverings and approximations -/

/-- **Outer cell covering**: all cell IDs whose cell intersects `A`. -/
def outerCover (A : Set α) : Set ι :=
  {i | Intersects (P.cell i) A}

/-- **Inner cell covering**: all cell IDs whose cell lies completely within `A`. -/
def innerCover (A : Set α) : Set ι :=
  {i | Within (P.cell i) A}

/-- **Outer approximation**: union of all cells in `outerCover A`. -/
def outerApprox (A : Set α) : Set α :=
  ⋃ i ∈ P.outerCover A, P.cell i

/-- **Inner approximation**: union of all cells in `innerCover A`. -/
def innerApprox (A : Set α) : Set α :=
  ⋃ i ∈ P.innerCover A, P.cell i

/-- **Soundness of inner approximation**: `innerApprox A ⊆ A`. -/
theorem innerApprox_subset (A : Set α) : P.innerApprox A ⊆ A := by
  rintro x hx
  simp only [innerApprox, mem_iUnion] at hx
  obtain ⟨i, hi, hxcell⟩ := hx
  exact hi hxcell

/-- **Soundness of outer approximation**: `A ⊆ outerApprox A`. -/
theorem subset_outerApprox (A : Set α) : A ⊆ P.outerApprox A := by
  intro x hx
  simp only [outerApprox, mem_iUnion]
  exact ⟨P.idOf x, ⟨x, P.mem_cell_idOf x, hx⟩, P.mem_cell_idOf x⟩

theorem innerApprox_subset_outerApprox (A : Set α) :
    P.innerApprox A ⊆ P.outerApprox A :=
  (P.innerApprox_subset A).trans (P.subset_outerApprox A)

/-! ### Soundness of spatial relations derived from cell coverings -/

/-- **Soundness of outer-cover disjointness**: if the outer cell coverings of
`A` and `B` share no cell ID, then `A` and `B` are truly disjoint in `α`. -/
theorem disjoint_of_outerCover_disjoint {A B : Set α}
    (h : Geospatial.Disjoint (P.outerCover A) (P.outerCover B)) :
    Geospatial.Disjoint A B := by
  rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
  rintro x ⟨hxA, hxB⟩
  have hA : P.idOf x ∈ P.outerCover A := ⟨x, P.mem_cell_idOf x, hxA⟩
  have hB : P.idOf x ∈ P.outerCover B := ⟨x, P.mem_cell_idOf x, hxB⟩
  have : P.idOf x ∈ P.outerCover A ∩ P.outerCover B := ⟨hA, hB⟩
  rw [h] at this
  exact this

/-- **Soundness of outer-in-inner containment**: if every cell touching `A` is
completely contained in `B`, then `A` lies within `B`. -/
theorem within_of_outerCover_subset_innerCover {A B : Set α}
    (h : P.outerCover A ⊆ P.innerCover B) :
    Within A B := by
  intro x hxA
  have hA : P.idOf x ∈ P.outerCover A := ⟨x, P.mem_cell_idOf x, hxA⟩
  exact h hA (P.mem_cell_idOf x)

/-- **Soundness of inner-cover intersection**: if a nonempty cell lies inside
both `A` and `B`, then `A` and `B` truly intersect. -/
theorem intersects_of_innerCover_intersects {A B : Set α}
    (hne : ∀ i, (P.cell i).Nonempty)
    (h : Intersects (P.innerCover A) (P.innerCover B)) :
    Intersects A B := by
  obtain ⟨i, hiA, hiB⟩ := h
  obtain ⟨x, hx⟩ := hne i
  exact ⟨x, hiA hx, hiB hx⟩

end SpatialPartition

/-! ## 2. Abstract Hierarchical Spatial Partition -/

/-- A hierarchical spatial partition of `α` across resolution levels `z : ℕ`. -/
structure HierarchicalPartition (α : Type*) where
  Idx : ℕ → Type
  level : (z : ℕ) → SpatialPartition (Idx z) α
  parent : {z : ℕ} → Idx (z + 1) → Idx z
  child_subset_parent : ∀ {z : ℕ} (c : Idx (z + 1)),
    (level (z + 1)).cell c ⊆ (level z).cell (parent c)

namespace HierarchicalPartition

variable {α : Type*} (H : HierarchicalPartition α)

/-- Every parent cell is the **exact union** of all its child cells at the next
finer level. -/
theorem parent_eq_iUnion_children {z : ℕ} (p : H.Idx z) :
    (H.level z).cell p = ⋃ c : {c : H.Idx (z + 1) // H.parent c = p}, (H.level (z + 1)).cell c.1 := by
  ext x
  constructor
  · intro hx
    simp only [mem_iUnion, Subtype.exists]
    refine ⟨(H.level (z + 1)).idOf x, ?_, (H.level (z + 1)).mem_cell_idOf x⟩
    have hxparent : x ∈ (H.level z).cell (H.parent ((H.level (z + 1)).idOf x)) :=
      H.child_subset_parent _ ((H.level (z + 1)).mem_cell_idOf x)
    exact ((H.level z).idOf_eq_of_mem hxparent).symm.trans ((H.level z).idOf_eq_of_mem hx)
  · intro hx
    simp only [mem_iUnion, Subtype.exists] at hx
    obtain ⟨c, rfl, hxc⟩ := hx
    exact H.child_subset_parent c hxc

/-- **Resolution refinement tightens outer approximation**:
`outerApprox (z + 1) A ⊆ outerApprox z A`. -/
theorem outerApprox_antitone (z : ℕ) (A : Set α) :
    (H.level (z + 1)).outerApprox A ⊆ (H.level z).outerApprox A := by
  intro x hx
  simp only [SpatialPartition.outerApprox, mem_iUnion] at hx ⊢
  obtain ⟨c, ⟨y, hyc, hyA⟩, hxc⟩ := hx
  exact ⟨H.parent c, ⟨y, H.child_subset_parent c hyc, hyA⟩, H.child_subset_parent c hxc⟩

/-- **Resolution refinement expands inner approximation**:
`innerApprox z A ⊆ innerApprox (z + 1) A`. -/
theorem innerApprox_monotone (z : ℕ) (A : Set α) :
    (H.level z).innerApprox A ⊆ (H.level (z + 1)).innerApprox A := by
  intro x hx
  simp only [SpatialPartition.innerApprox, mem_iUnion] at hx ⊢
  obtain ⟨p, hpA, hxp⟩ := hx
  set c := (H.level (z + 1)).idOf x
  have hxc : x ∈ (H.level (z + 1)).cell c := (H.level (z + 1)).mem_cell_idOf x
  have hcp : H.parent c = p :=
    ((H.level z).idOf_eq_of_mem (H.child_subset_parent c hxc)).symm.trans
      ((H.level z).idOf_eq_of_mem hxp)
  exact ⟨c, (H.child_subset_parent c).trans (hcp ▸ hpA), hxc⟩

end HierarchicalPartition

/-! ## 3. Dimension-Unified `d`-Dimensional Dyadic Hierarchy (Quadtree / Octree) -/

/-- Discrete spatial identifier at level `z` in `d` dimensions: integer lattice
coordinates `Fin d → ℤ`. -/
structure DyadicId (d : ℕ) where
  level : ℕ
  coord : Fin d → ℤ

/-- Half-open dyadic cell `∏ k, [c k / 2^z, (c k + 1) / 2^z)` in `ℝᵈ`. -/
def dyadicCell (d : ℕ) (z : ℕ) (c : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {p | ∀ k : Fin d, (c k : ℝ) / (2 : ℝ) ^ z ≤ p k ∧ p k < ((c k : ℝ) + 1) / (2 : ℝ) ^ z}

/-- Closed dyadic cell `∏ k, [c k / 2^z, (c k + 1) / 2^z]` in `ℝᵈ`. -/
def dyadicClosedCell (d : ℕ) (z : ℕ) (c : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {p | ∀ k : Fin d, (c k : ℝ) / (2 : ℝ) ^ z ≤ p k ∧ p k ≤ ((c k : ℝ) + 1) / (2 : ℝ) ^ z}

theorem dyadicCell_nonempty (d z : ℕ) (c : Fin d → ℤ) :
    (dyadicCell d z c).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun k => (c k : ℝ) / (2 : ℝ) ^ z), fun k => ?_⟩
  have hpos : (0 : ℝ) < (2 : ℝ) ^ z := by positivity
  refine ⟨le_rfl, ?_⟩
  rw [div_lt_div_iff_of_pos_right hpos]
  linarith

/-- Half-open dyadic cells at level `z` form an exact `SpatialPartition` of `ℝᵈ`. -/
def dyadicPartition (d z : ℕ) : SpatialPartition (Fin d → ℤ) (EuclideanSpace ℝ (Fin d)) where
  cell := dyadicCell d z
  exhaustive p := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ z := by positivity
    refine ⟨fun k => ⌊p k * (2 : ℝ) ^ z⌋, fun k => ?_⟩
    constructor
    · rw [div_le_iff₀ hpos]
      exact Int.floor_le (p k * (2 : ℝ) ^ z)
    · rw [lt_div_iff₀ hpos]
      exact Int.lt_floor_add_one (p k * (2 : ℝ) ^ z)
  exclusive c₁ c₂ hne := by
    rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro p ⟨hp1, hp2⟩
    apply hne
    funext k
    have hpos : (0 : ℝ) < (2 : ℝ) ^ z := by positivity
    have h1 := hp1 k
    have h2 := hp2 k
    have hlt1 : (c₁ k : ℝ) < (c₂ k : ℝ) + 1 := by
      have : (c₁ k : ℝ) / (2 : ℝ) ^ z < ((c₂ k : ℝ) + 1) / (2 : ℝ) ^ z := h1.1.trans_lt h2.2
      exact (div_lt_div_iff_of_pos_right hpos).mp this
    have hlt2 : (c₂ k : ℝ) < (c₁ k : ℝ) + 1 := by
      have : (c₂ k : ℝ) / (2 : ℝ) ^ z < ((c₁ k : ℝ) + 1) / (2 : ℝ) ^ z := h2.1.trans_lt h1.2
      exact (div_lt_div_iff_of_pos_right hpos).mp this
    have hi1 : c₁ k < c₂ k + 1 := by exact_mod_cast hlt1
    have hi2 : c₂ k < c₁ k + 1 := by exact_mod_cast hlt2
    omega

/-- Floor division by 2 on each coordinate gives the parent cell in the dyadic
hierarchy. -/
def dyadicParent {d : ℕ} (c : Fin d → ℤ) : Fin d → ℤ :=
  fun k => c k / 2

/-- **Dimension-unified `d`-dimensional dyadic hierarchy** (`d = 2` is Quadtree,
`d = 3` is Octree). -/
def dyadicHierarchy (d : ℕ) : HierarchicalPartition (EuclideanSpace ℝ (Fin d)) where
  Idx _ := Fin d → ℤ
  level z := dyadicPartition d z
  parent := dyadicParent
  child_subset_parent {z} c p hp k := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ z := by positivity
    have hpos1 : (0 : ℝ) < (2 : ℝ) ^ (z + 1) := by positivity
    have hk := hp k
    have hdiv : 2 * (c k / 2) ≤ c k ∧ c k ≤ 2 * (c k / 2) + 1 := by omega
    have hdivR1 : (2 : ℝ) * ((c k / 2 : ℤ) : ℝ) ≤ (c k : ℝ) := by exact_mod_cast hdiv.1
    have hdivR2 : (c k : ℝ) ≤ (2 : ℝ) * ((c k / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast hdiv.2
    have hpow : (2 : ℝ) ^ (z + 1) = 2 * (2 : ℝ) ^ z := by ring
    constructor
    · calc ((c k / 2 : ℤ) : ℝ) / (2 : ℝ) ^ z
          = (2 * ((c k / 2 : ℤ) : ℝ)) / (2 : ℝ) ^ (z + 1) := by rw [hpow]; field_simp
        _ ≤ (c k : ℝ) / (2 : ℝ) ^ (z + 1) := div_le_div_of_nonneg_right hdivR1 hpos1.le
        _ ≤ p k := hk.1
    · calc p k < ((c k : ℝ) + 1) / (2 : ℝ) ^ (z + 1) := hk.2
        _ ≤ (2 * ((c k / 2 : ℤ) : ℝ) + 2) / (2 : ℝ) ^ (z + 1) :=
            div_le_div_of_nonneg_right (by linarith) hpos1.le
        _ = (((c k / 2 : ℤ) : ℝ) + 1) / (2 : ℝ) ^ z := by rw [hpow]; field_simp

/-- **2D Quadtree** hierarchy on `Point2D = EuclideanSpace ℝ (Fin 2)`. -/
abbrev quadtreeHierarchy : HierarchicalPartition Point2D := dyadicHierarchy 2

/-- **3D Octree** hierarchy on `E3 = EuclideanSpace ℝ (Fin 3)`. -/
abbrev octreeHierarchy : HierarchicalPartition DE9IM.Space3.E3 := dyadicHierarchy 3

/-- **Boundary-handling tradeoff**: unlike half-open cells, adjacent **closed**
dyadic cells at level `z` are NOT disjoint — they overlap along their shared
boundary hyperplane! -/
theorem closedCell_adjacent_overlap (d : ℕ) (hd : 0 < d) (z : ℕ) :
    let c₁ : Fin d → ℤ := fun _ => 0
    let c₂ : Fin d → ℤ := fun k => if k.val = 0 then 1 else 0
    c₁ ≠ c₂ ∧ Intersects (dyadicClosedCell d z c₁) (dyadicClosedCell d z c₂) := by
  intro c₁ c₂
  refine ⟨fun h => by
    have := congrFun h ⟨0, hd⟩
    simp [c₁, c₂] at this, ?_⟩
  refine ⟨WithLp.toLp 2 (fun k : Fin d => if k.val = 0 then (1 : ℝ) / (2 : ℝ) ^ z else 0),
    fun k => ?_, fun k => ?_⟩
  · have hpos : (0 : ℝ) < (2 : ℝ) ^ z := by positivity
    by_cases hk : k.val = 0 <;> simp [c₁, hk, hpos.le]
  · have hpos : (0 : ℝ) < (2 : ℝ) ^ z := by positivity
    by_cases hk : k.val = 0
    · simp only [c₂, hk, ↓reduceIte, Int.cast_one]
      refine ⟨le_rfl, ?_⟩
      rw [div_le_div_iff_of_pos_right hpos]
      norm_num
    · simp [c₂, hk, hpos.le]

/-! ## 4. Resolution Information Loss & False-Positive Counterexamples -/

/-- **Counterexample 1 (Information loss under finite resolution)**:
for EVERY resolution level `z : ℕ`, there exist two distinct points `p ≠ q` in
`Point2D` that receive the **exact same Quadtree cell ID** at level `z`. -/
theorem counterexample_resolution_information_loss (z : ℕ) :
    ∃ p q : Point2D, p ≠ q ∧
      (quadtreeHierarchy.level z).idOf p = (quadtreeHierarchy.level z).idOf q := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ z := by positivity
  set p : Point2D := Point2D.mk 0 0
  set q : Point2D := Point2D.mk (1 / (2 * (2 : ℝ) ^ z)) 0
  have hpq : p ≠ q := by
    intro h
    have hx := congrArg Geospatial.Point2D.x h
    simp only [p, q, Point2D.x_mk] at hx
    have hgt : (0 : ℝ) < 1 / (2 * (2 : ℝ) ^ z) := by positivity
    linarith
  have hp0 : p ∈ (quadtreeHierarchy.level z).cell (fun _ => 0) := by
    intro k
    fin_cases k <;> simp [p, Point2D.mk, hpos]
  have hq0 : q ∈ (quadtreeHierarchy.level z).cell (fun _ => 0) := by
    intro k
    fin_cases k
    · simp only [q, Point2D.mk, Int.cast_zero, zero_div, zero_add]
      change (0 : ℝ) ≤ 1 / (2 * (2 : ℝ) ^ z) ∧ 1 / (2 * (2 : ℝ) ^ z) < 1 / (2 : ℝ) ^ z
      refine ⟨by positivity, ?_⟩
      rw [div_lt_div_iff₀ (by positivity) hpos]
      linarith
    · simp [q, Point2D.mk, hpos]
  exact ⟨p, q, hpq,
    ((quadtreeHierarchy.level z).idOf_eq_of_mem hp0).trans
      ((quadtreeHierarchy.level z).idOf_eq_of_mem hq0).symm⟩

/-- **Counterexample 2 (Same cell ≠ real-space intersection)**:
for EVERY resolution level `z : ℕ`, there exist two **disjoint** regions `A, B`
whose Quadtree outer coverings at level `z` **share a cell** — proving that
belonging to the same spatial ID cell does NOT imply real-space intersection. -/
theorem counterexample_same_cell_not_intersects (z : ℕ) :
    ∃ A B : Region, Geospatial.Disjoint A B ∧
      Intersects ((quadtreeHierarchy.level z).outerCover A)
        ((quadtreeHierarchy.level z).outerCover B) := by
  obtain ⟨p, q, hpq, hid⟩ := counterexample_resolution_information_loss z
  refine ⟨{p}, {q}, ?_, ?_⟩
  · rw [Geospatial.Disjoint, eq_empty_iff_forall_notMem]
    rintro x ⟨rfl, rfl⟩
    exact hpq rfl
  · refine ⟨(quadtreeHierarchy.level z).idOf p,
      ⟨p, (quadtreeHierarchy.level z).mem_cell_idOf p, rfl⟩,
      ⟨q, hid ▸ (quadtreeHierarchy.level z).mem_cell_idOf q, rfl⟩⟩

/-- **Counterexample 3 (Outer-cover inclusion ≠ real-space containment)**:
for EVERY resolution level `z : ℕ`, there exist regions `A, B` with
`outerCover A ⊆ outerCover B` yet `¬ Within A B`. -/
theorem counterexample_outerCover_subset_not_within (z : ℕ) :
    ∃ A B : Region,
      (quadtreeHierarchy.level z).outerCover A ⊆ (quadtreeHierarchy.level z).outerCover B ∧
      ¬ Within A B := by
  obtain ⟨p, q, hpq, hid⟩ := counterexample_resolution_information_loss z
  refine ⟨{p}, {q}, ?_, fun hsub => hpq (hsub rfl)⟩
  rintro i ⟨x, hxi, hxp⟩
  have hxp' : x = p := hxp
  subst hxp'
  have hi : i = (quadtreeHierarchy.level z).idOf x :=
    ((quadtreeHierarchy.level z).idOf_eq_of_mem hxi).symm
  rw [hi, hid]
  exact ⟨q, (quadtreeHierarchy.level z).mem_cell_idOf q, rfl⟩

end Geospatial.Partition
