import LeanGeospatial.DE9IM.Dimension

/-!
# Facts about points, lines and areas that DE-9IM needs

- Segments and line strings are closed and have empty interior in the plane,
  so no cell through a line's interior or boundary has value `2`.
- A segment, or a line string's interior, still contains an arc after
  removing finitely many points.
- A line string's end points are limits of its interior points.
- For every geometry, the strata give: `g ∩ h` is `II ∪ IB ∪ BI ∪ BB`,
  `g ⊆ h` is `IE = BE = ∅`, and `g ⊄ h` is `IE ≠ ∅`.
-/

namespace Geospatial

open DE9IM

instance : T2Space Point2D := Point2D.homeomorphProd.isEmbedding.t2Space

/-! ## Segments -/

theorem Point2D.continuous_lerp (a b : Point2D) : Continuous (a.lerp b) :=
  continuous_induced_rng.mpr (by
    show Continuous fun t : ℝ => ((1 - t) * a.x + t * b.x, (1 - t) * a.y + t * b.y)
    fun_prop)

theorem Point2D.lerp_injective {a b : Point2D} (h : a ≠ b) : Function.Injective (a.lerp b) := by
  intro s t hst
  simp only [Point2D.lerp, Point2D.mk.injEq] at hst
  by_contra hne
  have hst' : s - t ≠ 0 := sub_ne_zero.mpr hne
  apply h
  have hx : (s - t) * (b.x - a.x) = 0 := by linear_combination hst.1
  have hy : (s - t) * (b.y - a.y) = 0 := by linear_combination hst.2
  exact Point2D.ext
    (by have := (mul_eq_zero.mp hx).resolve_left hst'; linarith)
    (by have := (mul_eq_zero.mp hy).resolve_left hst'; linarith)

theorem segment_eq_image (a b : Point2D) : segment a b = a.lerp b '' Set.Icc 0 1 := by
  ext p
  simp only [segment, Set.mem_setOf_eq, Set.mem_image]
  exact ⟨fun ⟨t, ht, h⟩ => ⟨t, ht, h.symm⟩, fun ⟨t, ht, h⟩ => ⟨t, ht, h.symm⟩⟩

theorem isClosed_segment (a b : Point2D) : IsClosed (segment a b) := by
  rw [segment_eq_image]
  exact (isCompact_Icc.image (Point2D.continuous_lerp a b)).isClosed

theorem segment_comm (a b : Point2D) : segment a b = segment b a := by
  have key : ∀ a b : Point2D, segment a b ⊆ segment b a := by
    rintro a b p ⟨t, ⟨h₀, h₁⟩, rfl⟩
    refine ⟨1 - t, ⟨by linarith, by linarith⟩, ?_⟩
    simp only [Point2D.lerp, Point2D.mk.injEq]
    constructor <;> ring
  exact Set.Subset.antisymm (key a b) (key b a)

/-- A line through `a` in direction `u ≠ 0` has empty interior. -/
theorem interior_line_eq_empty (a u : Point2D) (hu : u.x ≠ 0 ∨ u.y ≠ 0) :
    interior {p : Point2D | u.x * (p.y - a.y) - u.y * (p.x - a.x) = 0} = ∅ := by
  set L := {p : Point2D | u.x * (p.y - a.y) - u.y * (p.x - a.x) = 0}
  rw [Set.eq_empty_iff_forall_not_mem]
  intro p hp
  -- Move off the line along the normal direction.
  let g : ℝ → Point2D := fun t => ⟨p.x - t * u.y, p.y + t * u.x⟩
  have hg : Continuous g := continuous_induced_rng.mpr (by
    show Continuous fun t : ℝ => (p.x - t * u.y, p.y + t * u.x)
    fun_prop)
  have hg0 : g 0 = p := Point2D.ext (by simp [g]) (by simp [g])
  have h0 : (0 : ℝ) ∈ g ⁻¹' interior L := by
    show g 0 ∈ interior L
    rw [hg0]; exact hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_interior.preimage hg) 0 h0
  have hmem : g (ε / 2) ∈ L := interior_subset (hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith))
  have hpL : p ∈ L := interior_subset hp
  simp only [L, Set.mem_setOf_eq, g] at hmem hpL
  have hsq : ε / 2 * (u.x ^ 2 + u.y ^ 2) = 0 := by linear_combination hmem - hpL
  have hpos : 0 < u.x ^ 2 + u.y ^ 2 := by
    rcases hu with h | h
    · have := pow_pos (abs_pos.mpr h) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg u.y]
    · have := pow_pos (abs_pos.mpr h) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg u.x]
  have : ε / 2 * (u.x ^ 2 + u.y ^ 2) > 0 := mul_pos (by linarith) hpos
  linarith

theorem interior_segment (a b : Point2D) (h : a ≠ b) : interior (segment a b) = ∅ := by
  have hu : (b.x - a.x) ≠ 0 ∨ (b.y - a.y) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Point2D.ext (by linarith [hc.1]) (by linarith [hc.2]))
  apply Set.eq_empty_of_subset_empty
  refine (interior_mono ?_).trans
    (interior_line_eq_empty a ⟨b.x - a.x, b.y - a.y⟩ hu).subset
  rintro p ⟨t, -, rfl⟩
  simp only [Set.mem_setOf_eq, Point2D.lerp]
  ring

/-- A finite union of closed sets with empty interior has empty interior. -/
theorem interior_iUnion_eq_empty {ι : Type*} [Fintype ι] (f : ι → Region)
    (hc : ∀ i, IsClosed (f i)) (hi : ∀ i, interior (f i) = ∅) : interior (⋃ i, f i) = ∅ := by
  classical
  have key : ∀ s : Finset ι, interior (⋃ i ∈ s, f i) = ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert _ ih =>
      rw [Finset.set_biUnion_insert, Set.union_comm,
        interior_union_isClosed_of_interior_empty
          (by simpa using (Finset.finite_toSet _).isClosed_biUnion fun i _ => hc i) (hi _), ih]
  simpa using key Finset.univ

/-! ## Arcs in segments -/

/-- The parameters at which the segment meets a finite set are finitely many. -/
theorem finite_lerp_preimage {a b : Point2D} (h : a ≠ b) {F : Set Point2D} (hF : F.Finite) :
    (a.lerp b ⁻¹' F).Finite :=
  hF.preimage (Point2D.lerp_injective h).injOn

/-- A segment minus finitely many points still contains an arc. -/
theorem hasArc_segment_diff {a b : Point2D} (h : a ≠ b) {F : Set Point2D} (hF : F.Finite) :
    HasArc (segment a b \ F) := by
  set T := a.lerp b ⁻¹' F
  have hT : T.Finite := finite_lerp_preimage h hF
  obtain ⟨x, hxI, hxT⟩ := ((Set.Ioo_infinite (zero_lt_one' ℝ)).diff hT).nonempty
  have hU : IsOpen (Set.Ioo (0 : ℝ) 1 \ T) := isOpen_Ioo.sdiff hT.isClosed
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x ⟨hxI, hxT⟩
  set ε := δ / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hδε : δ = 2 * ε := by rw [hεdef]; ring
  have hsub : ∀ s ∈ Set.Icc (0 : ℝ) 1, x - ε + 2 * ε * s ∈ Set.Ioo (0 : ℝ) 1 \ T := by
    rintro s ⟨hs₀, hs₁⟩
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h₁ := mul_nonneg hε.le hs₀
    have h₂ := mul_le_mul_of_nonneg_left hs₁ hε.le
    constructor <;> nlinarith
  refine ⟨fun s => a.lerp b (x - ε + 2 * ε * s), ?_, ?_, ?_⟩
  · exact ((Point2D.continuous_lerp a b).comp (by fun_prop)).continuousOn
  · intro s _ t _ hst
    have := Point2D.lerp_injective h hst
    have : 2 * ε * (s - t) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  · rintro p ⟨s, hs, rfl⟩
    obtain ⟨⟨h₀, h₁⟩, hnT⟩ := hsub s hs
    exact ⟨⟨_, ⟨h₀.le, h₁.le⟩, rfl⟩, hnT⟩

/-- The start of a segment is a limit of its points avoiding a finite set. -/
theorem left_mem_closure_segment_diff {a b : Point2D} (h : a ≠ b) {F : Set Point2D}
    (hF : F.Finite) : a ∈ closure (segment a b \ F) := by
  rw [mem_closure_iff]
  intro U hU haU
  have hV : IsOpen (a.lerp b ⁻¹' U) := hU.preimage (Point2D.continuous_lerp a b)
  have h0 : (0 : ℝ) ∈ a.lerp b ⁻¹' U := by simpa using haU
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  have hT := finite_lerp_preimage h hF
  have hpos : 0 < min δ 1 := lt_min hδ zero_lt_one
  obtain ⟨t, ⟨ht₀, ht₁⟩, htT⟩ := ((Set.Ioo_infinite hpos).diff hT).nonempty
  refine ⟨a.lerp b t, hball ?_, ⟨t, ⟨ht₀.le, ht₁.le.trans (min_le_right _ _)⟩, rfl⟩, htT⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₀]
  exact ht₁.trans_le (min_le_left _ _)

theorem right_mem_closure_segment_diff {a b : Point2D} (h : a ≠ b) {F : Set Point2D}
    (hF : F.Finite) : b ∈ closure (segment a b \ F) := by
  rw [segment_comm]
  exact left_mem_closure_segment_diff (Ne.symm h) hF

/-! ## Line strings -/

namespace LineString

variable (l : LineString)

theorem isClosed_carrier : IsClosed l.carrier :=
  isClosed_iUnion_of_finite fun _ => isClosed_segment _ _

theorem interior_carrier : _root_.interior l.carrier = ∅ :=
  interior_iUnion_eq_empty _ (fun _ => isClosed_segment _ _)
    (fun i => interior_segment _ _ (l.distinct i))

theorem boundary_finite : l.boundary.Finite := by
  unfold boundary
  split_ifs
  · exact Set.finite_empty
  · exact Set.toFinite _

theorem segment_subset_carrier (i : Fin (l.n + 1)) :
    segment (l.vertex i.castSucc) (l.vertex i.succ) ⊆ l.carrier :=
  Set.subset_iUnion (fun j : Fin (l.n + 1) => segment (l.vertex j.castSucc) (l.vertex j.succ)) i

/-- The interior minus finitely many points still contains an arc. -/
theorem hasArc_interior_diff {F : Set Point2D} (hF : F.Finite) : HasArc (l.interior \ F) := by
  apply (hasArc_segment_diff (l.distinct 0) (hF.union l.boundary_finite)).mono
  rintro p ⟨hp, hpF⟩
  rw [Set.mem_union, not_or] at hpF
  exact ⟨⟨l.segment_subset_carrier 0 hp, hpF.2⟩, hpF.1⟩

theorem hasArc_interior : HasArc l.interior := by
  simpa using l.hasArc_interior_diff Set.finite_empty

/-- The end points are limits of interior points. -/
theorem boundary_subset_closure_interior : l.boundary ⊆ closure l.interior := by
  have hsub : ∀ i : Fin (l.n + 1),
      segment (l.vertex i.castSucc) (l.vertex i.succ) \ l.boundary ⊆ l.interior :=
    fun i p ⟨hp, hpB⟩ => ⟨l.segment_subset_carrier i hp, hpB⟩
  intro p hp
  unfold boundary at hp
  split_ifs at hp with hring
  · exact absurd hp (Set.not_mem_empty p)
  rcases hp with rfl | rfl
  · exact closure_mono (hsub 0) (left_mem_closure_segment_diff (l.distinct 0) l.boundary_finite)
  · have := closure_mono (hsub (Fin.last l.n))
      (right_mem_closure_segment_diff (l.distinct (Fin.last l.n)) l.boundary_finite)
    simpa [finish, Fin.succ_last] using this

end LineString

/-! ## Geometries -/

namespace Geometry

variable (g h : Geometry)

theorem isClosed_carrier : IsClosed g.carrier := by
  cases g with
  | point p => exact isClosed_singleton
  | line l => exact l.isClosed_carrier
  | area A => exact A.isClosed

theorem stratum_I_subset : g.stratum .I ⊆ g.carrier :=
  g.stratum_I_union_B ▸ Set.subset_union_left

theorem stratum_B_subset : g.stratum .B ⊆ g.carrier :=
  g.stratum_I_union_B ▸ Set.subset_union_right

theorem boundary_subset_closure_interior : g.stratum .B ⊆ closure (g.stratum .I) := by
  cases g with
  | point p => exact Set.empty_subset _
  | line l => exact l.boundary_subset_closure_interior
  | area A =>
    intro p hp
    show p ∈ closure (interior (A : Region))
    rw [A.closure_interior_eq]
    exact boundary_subset_of_isClosed' A.isClosed hp
where
  boundary_subset_of_isClosed' {X : Region} (hX : IsClosed X) : boundary X ⊆ X := by
    rw [boundary_eq, hX.closure_eq]
    exact Set.diff_subset

theorem cell_swap (s t : Stratum) : cell s t g h = cell t s h g := Set.inter_comm _ _

theorem inter_eq_cells :
    g.carrier ∩ h.carrier = cell .I .I g h ∪ cell .I .B g h ∪ cell .B .I g h ∪ cell .B .B g h := by
  rw [← g.stratum_I_union_B, ← h.stratum_I_union_B]
  ext p
  simp only [cell, Set.mem_inter_iff, Set.mem_union]
  tauto

theorem subset_iff_cells : g.carrier ⊆ h.carrier ↔ cell .I .E g h = ∅ ∧ cell .B .E g h = ∅ := by
  simp only [cell, h.stratum_E, Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff,
    Set.mem_compl_iff]
  rw [← g.stratum_I_union_B]
  constructor
  · intro hs
    exact ⟨fun p ⟨hp, hq⟩ => hq (hs (Or.inl hp)), fun p ⟨hp, hq⟩ => hq (hs (Or.inr hp))⟩
  · rintro ⟨h₁, h₂⟩ p (hp | hp) <;> by_contra hq
    · exact h₁ p ⟨hp, hq⟩
    · exact h₂ p ⟨hp, hq⟩

/-- `g` fails to lie in `h` exactly when an interior point of `g` is exterior
to `h`. -/
theorem not_subset_iff : ¬ g.carrier ⊆ h.carrier ↔ (cell .I .E g h).Nonempty := by
  constructor
  · intro hns
    obtain ⟨p, hpg, hph⟩ := Set.not_subset.mp hns
    rw [← g.stratum_I_union_B] at hpg
    rcases hpg with hp | hp
    · exact ⟨p, hp, by rw [h.stratum_E]; exact hph⟩
    · have hopen : IsOpen (h.stratum .E) := by
        rw [h.stratum_E]; exact h.isClosed_carrier.isOpen_compl
      obtain ⟨q, hqE, hqI⟩ := mem_closure_iff.mp (g.boundary_subset_closure_interior hp) _
        hopen (by rw [h.stratum_E]; exact hph)
      exact ⟨q, hqI, hqE⟩
  · rintro ⟨p, hpI, hpE⟩ hs
    rw [h.stratum_E] at hpE
    exact hpE (hs (g.stratum_I_subset hpI))

/-! ## Cell values -/

/-- The value of the geometry's own interior: its dimension. -/
def dimValue : Geometry → DimValue
  | point _ => .d0
  | line _ => .d1
  | area _ => .d2

theorem of_stratum_I (hne : g.carrier.Nonempty) : DimValue.of (g.stratum .I) = g.dimValue := by
  cases g with
  | point p => exact DimValue.of_eq (describes_d0_of_subset_singleton rfl subset_rfl)
  | line l =>
    exact DimValue.of_eq ⟨Set.eq_empty_of_subset_empty
      ((interior_mono (Set.diff_subset)).trans l.interior_carrier.subset), l.hasArc_interior⟩
  | area A =>
    apply DimValue.of_eq
    show (interior (interior (A : Region))).Nonempty
    rw [interior_interior]
    exact (A.nonempty_iff_interior_nonempty).mp hne

/-- A set on a line has value `F`, `0` or `1`, never `2`. -/
theorem value_ne_d2_of_subset_line (l : LineString) {S : Region} (hS : S ⊆ l.carrier) :
    DimValue.of S ≠ .d2 := by
  intro h2
  have := DimValue.of_describes S
  rw [h2] at this
  obtain ⟨p, hp⟩ := this
  have := interior_mono hS hp
  rw [l.interior_carrier] at this
  exact this

end Geometry

end Geospatial
