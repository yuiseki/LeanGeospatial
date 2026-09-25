import LeanGeospatial.NineIntersection

/-!
# Points, lines and areas, with OGC Simple Features strata

DE-9IM needs an interior, a boundary and an exterior for every geometry. For
areas these are the topological ones already used (`interior`, `frontier`,
`interior Aᶜ`). For points and lines they are not: in the plane, a point and
a line have empty topological interior and are their own frontier
(`point_frontier`). Simple Features instead gives them their own:

| Geometry | Interior | Boundary | Exterior |
| --- | --- | --- | --- |
| Point `p` | `{p}` | `∅` | everything else |
| LineString | its points minus the boundary | its two end points, or `∅` if it is closed | everything off the line |
| Area | topological interior | topological boundary | topological exterior |

`Geometry.stratum` gives these, and `Geometry.existsUnique_stratum` proves
that they split the plane for every geometry.

Only single points, single line strings and areas are covered. Multi
geometries (and the mod-2 boundary rule for multi-curves) are not.
-/

namespace Geospatial

/-! ## Line strings -/

/-- The point a fraction `t` of the way from `a` to `b`. -/
def Point2D.lerp (a b : Point2D) (t : ℝ) : Point2D :=
  ⟨(1 - t) * a.x + t * b.x, (1 - t) * a.y + t * b.y⟩

@[simp] theorem Point2D.lerp_zero (a b : Point2D) : a.lerp b 0 = a := by
  simp [Point2D.lerp]

@[simp] theorem Point2D.lerp_one (a b : Point2D) : a.lerp b 1 = b := by
  simp [Point2D.lerp]

/-- The closed segment from `a` to `b`. -/
def segment (a b : Point2D) : Region := {p | ∃ t ∈ Set.Icc (0 : ℝ) 1, p = a.lerp b t}

theorem left_mem_segment (a b : Point2D) : a ∈ segment a b :=
  ⟨0, ⟨le_rfl, zero_le_one⟩, (Point2D.lerp_zero a b).symm⟩

theorem right_mem_segment (a b : Point2D) : b ∈ segment a b :=
  ⟨1, ⟨zero_le_one, le_rfl⟩, (Point2D.lerp_one a b).symm⟩

/-- A line string: at least two vertices, consecutive vertices distinct. -/
structure LineString where
  /-- The number of vertices, minus two. -/
  n : ℕ
  /-- The vertices in order. -/
  vertex : Fin (n + 2) → Point2D
  /-- Consecutive vertices differ, so every piece is a proper segment. -/
  distinct : ∀ i : Fin (n + 1), vertex i.castSucc ≠ vertex i.succ

namespace LineString

variable (l : LineString)

/-- The first vertex. -/
def start : Point2D := l.vertex 0

/-- The last vertex. -/
def finish : Point2D := l.vertex (Fin.last _)

/-- The points of the line string: the union of its segments. -/
def carrier : Region := ⋃ i : Fin (l.n + 1), segment (l.vertex i.castSucc) (l.vertex i.succ)

/-- A line string is closed when it ends where it starts. -/
def IsRing : Prop := l.start = l.finish

open Classical in
/-- Simple Features boundary: the two end points, or nothing for a closed line. -/
noncomputable def boundary : Region := if l.IsRing then ∅ else {l.start, l.finish}

/-- Simple Features interior: the line without its boundary. -/
noncomputable def interior : Region := l.carrier \ l.boundary

/-- Simple Features exterior: everything off the line. -/
def exterior : Region := l.carrierᶜ

theorem start_mem : l.start ∈ l.carrier :=
  Set.mem_iUnion.mpr ⟨0, left_mem_segment _ _⟩

theorem finish_mem : l.finish ∈ l.carrier :=
  Set.mem_iUnion.mpr ⟨Fin.last _, by
    simpa [finish, Fin.succ_last] using right_mem_segment (l.vertex (Fin.last l.n).castSucc)
      (l.vertex (Fin.last l.n).succ)⟩

theorem boundary_subset : l.boundary ⊆ l.carrier := by
  unfold boundary
  split_ifs
  · exact Set.empty_subset _
  · rintro p (rfl | rfl)
    · exact l.start_mem
    · exact l.finish_mem

/-- The line string with the two vertices `a` and `b`: a single segment. -/
def seg (a b : Point2D) (h : a ≠ b) : LineString :=
  ⟨0, ![a, b], fun i => by fin_cases i; exact h⟩

theorem seg_carrier (a b : Point2D) (h : a ≠ b) : (seg a b h).carrier = segment a b := by
  ext p
  simp only [carrier, seg, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    exact hi
  · intro hp
    exact ⟨0, hp⟩

theorem seg_boundary (a b : Point2D) (h : a ≠ b) : (seg a b h).boundary = {a, b} := by
  have : ¬ (seg a b h).IsRing := h
  simp only [boundary, this, if_false]
  rfl

theorem seg_interior (a b : Point2D) (h : a ≠ b) :
    (seg a b h).interior = segment a b \ {a, b} := by
  rw [interior, seg_carrier, seg_boundary]

end LineString

/-! ## Geometries -/

/-- A Simple Features geometry, restricted to the three kinds handled here. -/
inductive Geometry where
  | point (p : Point2D)
  | line (l : LineString)
  | area (A : RegularClosedRegion)

namespace Geometry

/-- The dimension of the geometry itself: 0, 1 or 2. -/
def dim : Geometry → ℕ
  | point _ => 0
  | line _ => 1
  | area _ => 2

/-- The points of the geometry. -/
def carrier : Geometry → Region
  | point p => {p}
  | line l => l.carrier
  | area A => A

/-- The Simple Features interior, boundary and exterior. For areas these are
exactly `Stratum.set`, the strata already used for Area/Area. -/
noncomputable def stratum : Geometry → Stratum → Region
  | point p, .I => {p}
  | point _, .B => ∅
  | point p, .E => {p}ᶜ
  | line l, .I => l.interior
  | line l, .B => l.boundary
  | line l, .E => l.exterior
  | area A, s => s.set A

@[simp] theorem stratum_area (A : RegularClosedRegion) (s : Stratum) :
    (area A).stratum s = s.set A := rfl

/-- The exterior is always everything off the geometry. -/
theorem stratum_E (g : Geometry) : g.stratum .E = g.carrierᶜ := by
  cases g with
  | point p => rfl
  | line l => rfl
  | area A => exact exterior_eq_of_isClosed A.isClosed

/-- Interior and boundary together make up the geometry. -/
theorem stratum_I_union_B (g : Geometry) : g.stratum .I ∪ g.stratum .B = g.carrier := by
  cases g with
  | point p => simp [stratum, carrier]
  | line l => exact Set.diff_union_of_subset l.boundary_subset
  | area A => exact interior_union_boundary_of_isClosed A.isClosed

/-- Interior and boundary share no point. -/
theorem stratum_I_inter_B (g : Geometry) : g.stratum .I ∩ g.stratum .B = ∅ := by
  cases g with
  | point p => simp [stratum]
  | line l => exact Set.diff_inter_self
  | area A => exact interior_disjoint_boundary (A : Region)

/-- Every point of the plane is in exactly one of the three strata. -/
theorem existsUnique_stratum (g : Geometry) (p : Point2D) : ∃! s : Stratum, p ∈ g.stratum s := by
  have hU := g.stratum_I_union_B
  have hD := g.stratum_I_inter_B
  have hE := g.stratum_E
  have hIB : ¬ (p ∈ g.stratum .I ∧ p ∈ g.stratum .B) := fun h => by
    have : p ∈ g.stratum .I ∩ g.stratum .B := h
    rw [hD] at this
    exact this
  have hIE : p ∈ g.stratum .I → p ∉ g.stratum .E := fun h h' => by
    rw [hE] at h'
    exact h' (hU ▸ Or.inl h)
  have hBE : p ∈ g.stratum .B → p ∉ g.stratum .E := fun h h' => by
    rw [hE] at h'
    exact h' (hU ▸ Or.inr h)
  by_cases hp : p ∈ g.carrier
  · rw [← hU] at hp
    rcases hp with h | h
    · refine ⟨.I, h, ?_⟩
      rintro (_ | _ | _) ht
      · rfl
      · exact absurd ⟨h, ht⟩ hIB
      · exact absurd ht (hIE h)
    · refine ⟨.B, h, ?_⟩
      rintro (_ | _ | _) ht
      · exact absurd ⟨ht, h⟩ hIB
      · rfl
      · exact absurd ht (hBE h)
  · have h : p ∈ g.stratum .E := by rw [hE]; exact hp
    refine ⟨.E, h, ?_⟩
    rintro (_ | _ | _) ht
    · exact absurd h (hIE ht)
    · exact absurd h (hBE ht)
    · rfl

/-- The DE-9IM cell of two geometries. -/
noncomputable def cell (s t : Stratum) (g h : Geometry) : Region := g.stratum s ∩ h.stratum t

/-- For two areas, the cells are the ones of `NineIntersection.lean`. -/
theorem cell_area_area (s t : Stratum) (A B : RegularClosedRegion) :
    cell s t (area A) (area B) = Geospatial.cell s t (A : Region) B := rfl

end Geometry

/-! ## Why points and lines need their own strata -/

theorem singleton_eq_preimage (p : Point2D) :
    ({p} : Region) = Point2D.homeomorphProd ⁻¹' ({p.x} ×ˢ {p.y}) := by
  ext q
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Point2D.homeomorphProd_apply,
    Set.mem_prod]
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩; exact Point2D.ext h₁ h₂

/-- Points are closed. -/
instance : T1Space Point2D :=
  ⟨fun p => by
    rw [singleton_eq_preimage, Set.singleton_prod_singleton]
    exact isClosed_singleton.preimage Point2D.homeomorphProd.continuous⟩

/-- In the plane a single point has no topological interior. -/
theorem interior_singleton_eq_empty (p : Point2D) : interior ({p} : Region) = ∅ := by
  rw [singleton_eq_preimage, ← Point2D.homeomorphProd.preimage_interior, interior_prod_eq, interior_singleton,
    Set.empty_prod, Set.preimage_empty]

/-- The topological frontier of a point is the point itself, while its
Simple Features boundary is empty. -/
theorem point_frontier (p : Point2D) : frontier ({p} : Region) = {p} := by
  rw [frontier, closure_singleton, interior_singleton_eq_empty, Set.diff_empty]

theorem point_boundary_ne_frontier (p : Point2D) :
    (Geometry.point p).stratum .B ≠ frontier ({p} : Region) := by
  rw [point_frontier]
  exact (Set.singleton_nonempty p).ne_empty.symm

end Geospatial
