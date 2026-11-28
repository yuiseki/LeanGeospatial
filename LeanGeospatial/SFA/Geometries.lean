import LeanGeospatial.ComputationalPolygon
import LeanGeospatial.SFA.Compare

/-!
# Full OGC Simple Features Geometry Hierarchy (SFA 1.2.1)

Formalizes all nine OGC Simple Feature Access 1.2.1 (§6.1) geometry types on
the Euclidean plane `Point2D`:

1. `empty` — Empty Geometry (`dim = ⊥`)
2. `point` — `Point` (`dim = 0`)
3. `multiPoint` — `MultiPoint` (`dim = 0` when nonempty, `⊥` when empty)
4. `lineString` — `LineString` (`dim = 1`)
5. `multiLineString` — `MultiLineString` with the **mod-2 boundary rule** (§6.1.8)
6. `linearRing` — `LinearRing` (simple closed 1D ring, `boundary = ∅`, `dim = 1`)
7. `polygon` — `Polygon` with exterior ring and interior holes (§6.1.11)
8. `multiPolygon` — `MultiPolygon` (§6.1.14)
9. `collection` — `GeometryCollection` (§6.1.2.4)

For every geometry we define:
- `IsValid` (OGC SFA 1.2.1 validity rules)
- `IsSimple` (OGC SFA 1.2.1 simplicity rules)
- `carrier`, `boundary`, `interior`, `exterior` (`stratum : Stratum → Region`)
- `dim : WithBot ℕ`
- `cell` and `de9im` (DE-9IM matrix using `DE9IM.DimValue.of`)

We prove `SFGeometry.existsUnique_stratum`: for every geometry (including
`empty`, `multiLineString` under mod-2, `polygon` with holes, and
`collection`), the three strata `I`, `B`, `E` partition `Point2D`.

## Specification vs implementation conventions (minimal counterexamples)

- `empty_not_matches_jtsEquals`: Empty geometries satisfy point-set `Equals`
  (`carrier = carrier`), yet fail OGC SFA / JTS `T*F**FFF*` because `II = F`.
- `mod2_shared_endpoint_cancels`: Under OGC SFA §6.1.8's mod-2 boundary rule,
  two segments sharing an endpoint `(1, 0)` cancel that endpoint out of the
  boundary so it becomes an interior point of the `MultiLineString`.
- `multiPoint_dup_valid_not_simple`: Per OGC SFA §6.1.5, a `MultiPoint` with
  repeated coordinates is not simple (`¬ IsSimple`), whereas GIS engines
  (JTS/GEOS/PostGIS) still treat it as topologically valid (`IsValid`).
- `collection_naive_strata_overlap`: OGC SFA §6.1.2.4 omits a boundary rule
  for heterogeneous `GeometryCollection`s; taking the naive union of member
  interiors and member boundaries violates `I ∩ B = ∅` when a `Point` lies on
  the boundary of a `Polygon`.
-/

namespace Geospatial.SFA

open Set Geospatial ComputationalGeometry

/-! ## Simplicity of LineStrings (OGC SFA §6.1.6) -/

/-- A `LineString` is simple (OGC SFA §6.1.6.1) when it does not pass through
the same point twice, except that start and finish may coincide for a ring:
distinct non-consecutive segments are disjoint, consecutive segments meet only
at their shared vertex, and each segment is non-degenerate (already enforced by
`LineString.distinct`). -/
def LineString.IsSimple (l : LineString) : Prop :=
  (∀ i j : Fin (l.n + 1), i.val + 1 < j.val →
    ¬ (i.val = 0 ∧ j.val = l.n ∧ l.IsRing) →
    Geospatial.Disjoint (segment (l.vertex i.castSucc) (l.vertex i.succ))
      (segment (l.vertex j.castSucc) (l.vertex j.succ))) ∧
  (∀ i : Fin l.n,
    segment (l.vertex i.castSucc.castSucc) (l.vertex i.castSucc.succ) ∩
      segment (l.vertex i.succ.castSucc) (l.vertex i.succ.succ) =
      {l.vertex i.succ.castSucc})

/-- A single non-degenerate segment is always simple. -/
theorem LineString.seg_isSimple (a b : Point2D) (h : a ≠ b) :
    SFA.LineString.IsSimple (LineString.seg a b h) := by
  refine ⟨fun i j hij _ => ?_, fun i => i.elim0⟩
  have hi := i.isLt
  have hj := j.isLt
  simp only [LineString.seg] at hi hj
  omega

/-! ## MultiPoint (OGC SFA §6.1.5) -/

/-- A MultiPoint: a finite list of points in the plane. -/
structure SFMultiPoint where
  points : List Point2D

namespace SFMultiPoint

/-- The point set of a MultiPoint. -/
def carrier (mp : SFMultiPoint) : Region := {p | p ∈ mp.points}

/-- OGC SFA §6.1.5: the boundary of a MultiPoint is always empty. -/
def boundary (_mp : SFMultiPoint) : Region := ∅

/-- OGC SFA §6.1.5: the interior of a MultiPoint is its point set. -/
def interior (mp : SFMultiPoint) : Region := mp.carrier

/-- OGC SFA §6.1.5: a MultiPoint is simple iff no two points are equal. -/
def IsSimple (mp : SFMultiPoint) : Prop := mp.points.Nodup

/-- Every MultiPoint is valid (even when it contains duplicate points;
simplicity is a stricter condition than validity in OGC SFA / JTS / PostGIS). -/
def IsValid (_mp : SFMultiPoint) : Prop := True

def dim (mp : SFMultiPoint) : WithBot ℕ :=
  if mp.points = [] then ⊥ else (0 : WithBot ℕ)

end SFMultiPoint

/-! ## MultiLineString with the Mod-2 Boundary Rule (OGC SFA §6.1.8) -/

/-- A MultiLineString: a finite list of LineStrings. -/
structure SFMultiLineString where
  lines : List LineString

namespace SFMultiLineString

/-- The point set of a MultiLineString: union of its component LineStrings. -/
def carrier (ml : SFMultiLineString) : Region :=
  {p | ∃ l ∈ ml.lines, p ∈ l.carrier}

open Classical in
/-- The number of component LineStrings whose boundary contains `p`. -/
noncomputable def boundaryCount (ml : SFMultiLineString) (p : Point2D) : ℕ :=
  ml.lines.countP (fun l => decide (p ∈ l.boundary))

open Classical in
/-- **OGC SFA §6.1.8 Mod-2 Boundary Rule**: a point is in the boundary of a
MultiLineString iff it is in the boundaries of an odd number of its component
LineStrings. -/
noncomputable def boundary (ml : SFMultiLineString) : Region :=
  {p | Odd (ml.boundaryCount p)}

/-- If `p` is in the mod-2 boundary of `ml`, then `p` is in `ml.carrier`. -/
theorem boundary_subset_carrier (ml : SFMultiLineString) :
    ml.boundary ⊆ ml.carrier := by
  classical
  intro p hp
  have hpos : 0 < ml.boundaryCount p := by
    obtain ⟨k, hk⟩ := hp
    omega
  unfold boundaryCount at hpos
  rw [List.countP_pos_iff] at hpos
  obtain ⟨l, hl, hpb⟩ := hpos
  exact ⟨l, hl, l.boundary_subset (of_decide_eq_true hpb)⟩

/-- OGC SFA §6.1.8: a MultiLineString is simple iff every component is simple
and any two distinct components intersect at most at points that are in the
boundaries of both components. -/
def IsSimple (ml : SFMultiLineString) : Prop :=
  (∀ l ∈ ml.lines, SFA.LineString.IsSimple l) ∧
  (∀ i j : Fin ml.lines.length, i ≠ j →
    (ml.lines[i].carrier ∩ ml.lines[j].carrier) ⊆
      (ml.lines[i].boundary ∩ ml.lines[j].boundary))

/-- Every MultiLineString whose components are valid LineStrings is valid. -/
def IsValid (_ml : SFMultiLineString) : Prop := True

def dim (ml : SFMultiLineString) : WithBot ℕ :=
  if ml.lines = [] then ⊥ else (1 : WithBot ℕ)

end SFMultiLineString

/-! ## Polygon with Holes (OGC SFA §6.1.11) -/

/-- An OGC Simple Features Polygon: an exterior ring (simple polygon) and a
list of interior hole rings (each a simple polygon). -/
structure SFPolygon where
  exteriorRing : SimplePolygon
  holes : List SimplePolygon

namespace SFPolygon

/-- The union of open interiors of all holes. -/
def holesOpenUnion (P : SFPolygon) : Region :=
  {p | ∃ h ∈ P.holes, p ∈ h.toOpenRegion}

/-- The union of closed regions of all holes. -/
def holesClosedUnion (P : SFPolygon) : Region :=
  {p | ∃ h ∈ P.holes, p ∈ h.toRegion}

/-- The union of boundaries of the exterior ring and all hole rings. -/
def boundary (P : SFPolygon) : Region :=
  P.exteriorRing.boundary ∪ {p | ∃ h ∈ P.holes, p ∈ h.boundary}

/-- The closed point set of a Polygon with holes: exterior region minus open
interiors of holes (hole boundaries belong to the Polygon). -/
def carrier (P : SFPolygon) : Region :=
  P.exteriorRing.toRegion \ P.holesOpenUnion

/-- The open interior of a Polygon with holes: exterior open region minus
closed regions of holes. -/
def interior (P : SFPolygon) : Region :=
  P.exteriorRing.toOpenRegion \ P.holesClosedUnion

/-- **OGC SFA 1.2.1 §6.1.11.1 Validity** for a Polygon with holes:
1. Every hole lies within the exterior ring (`h.toRegion ⊆ exteriorRing.toRegion`);
2. Each hole boundary meets the exterior boundary in at most one point (`Subsingleton`);
3. Distinct holes have disjoint closed interiors and their boundaries meet in
   at most one point (`Subsingleton`);
4. The interior of the polygon is connected (`IsConnected P.interior`). -/
def IsValid (P : SFPolygon) : Prop :=
  (∀ h ∈ P.holes, h.toRegion ⊆ P.exteriorRing.toRegion) ∧
  (∀ h ∈ P.holes, (h.boundary ∩ P.exteriorRing.boundary).Subsingleton) ∧
  (∀ i j : Fin P.holes.length, i ≠ j →
    P.holes[i].toOpenRegion ∩ P.holes[j].toOpenRegion = ∅ ∧
    (P.holes[i].boundary ∩ P.holes[j].boundary).Subsingleton) ∧
  IsConnected P.interior

/-- Every valid OGC Polygon is simple (surfaces are always simple in SFA §6.1.10). -/
def IsSimple (P : SFPolygon) : Prop := P.IsValid

/-- A hole-free simple polygon as an `SFPolygon`. -/
def ofSimple (P : SimplePolygon) : SFPolygon := ⟨P, []⟩

theorem ofSimple_carrier (P : SimplePolygon) :
    (ofSimple P).carrier = P.toRegion := by
  ext p
  simp [ofSimple, carrier, holesOpenUnion]

theorem ofSimple_boundary (P : SimplePolygon) :
    (ofSimple P).boundary = P.boundary := by
  ext p
  simp [ofSimple, boundary]

theorem ofSimple_interior (P : SimplePolygon) :
    (ofSimple P).interior = P.toOpenRegion := by
  ext p
  simp [ofSimple, interior, holesClosedUnion]

/-- For a valid `SFPolygon`, the boundary is contained in the carrier. -/
theorem boundary_subset_carrier {P : SFPolygon} (hV : P.IsValid) :
    P.boundary ⊆ P.carrier := by
  rintro p (hpExt | ⟨h, hh, hph⟩)
  · refine ⟨P.exteriorRing.boundary_subset_toRegion hpExt, ?_⟩
    rintro ⟨h, hh, hphOpen⟩
    -- `p ∈ h.toOpenRegion ⊆ interior P.exteriorRing.toRegion = P.exteriorRing.toOpenRegion`
    have hsub : h.toOpenRegion ⊆ P.exteriorRing.toOpenRegion := by
      rw [← SimplePolygonBridge.interior_toRegion P.exteriorRing]
      exact interior_maximal (h.toOpenRegion_subset_toRegion.trans (hV.1 h hh)) h.isOpen_toOpenRegion
    exact (hsub hphOpen).1 hpExt
  · refine ⟨hV.1 h hh (h.boundary_subset_toRegion hph), ?_⟩
    rintro ⟨h', hh', hph'Open⟩
    -- Obtain indices `i, j` for `h, h'` in `P.holes`.
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hh
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hh'
    by_cases hij : i = j
    · subst hij
      exact hph'Open.1 hph
    · have hdisj := (hV.2.2.1 ⟨i, hi⟩ ⟨j, hj⟩ (fun e => hij (congrArg Fin.val e))).1
      -- `p ∈ h.boundary ⊆ closure h.toOpenRegion`, while `h'.toOpenRegion` is open and contains `p`.
      have hpcl : p ∈ closure P.holes[i].toOpenRegion := by
        rw [SimplePolygonBridge.closure_toOpenRegion]
        exact P.holes[i].boundary_subset_toRegion hph
      obtain ⟨q, hq1, hq2⟩ := mem_closure_iff.mp hpcl _ P.holes[j].isOpen_toOpenRegion hph'Open
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj) q ⟨hq2, hq1⟩

end SFPolygon

/-! ## MultiPolygon (OGC SFA §6.1.14) -/

/-- A MultiPolygon: a finite list of `SFPolygon`s. -/
structure SFMultiPolygon where
  polygons : List SFPolygon

namespace SFMultiPolygon

def carrier (mp : SFMultiPolygon) : Region :=
  {p | ∃ P ∈ mp.polygons, p ∈ P.carrier}

def boundary (mp : SFMultiPolygon) : Region :=
  {p | ∃ P ∈ mp.polygons, p ∈ P.boundary}

/-- **OGC SFA 1.2.1 §6.1.14 Validity** for a MultiPolygon:
1. Every element Polygon is valid;
2. Interiors of distinct elements are disjoint;
3. Boundaries of distinct elements intersect at most in a finite number of
   points (no shared edge). -/
def IsValid (mp : SFMultiPolygon) : Prop :=
  (∀ P ∈ mp.polygons, P.IsValid) ∧
  (∀ i j : Fin mp.polygons.length, i ≠ j →
    mp.polygons[i].interior ∩ mp.polygons[j].interior = ∅ ∧
    (mp.polygons[i].boundary ∩ mp.polygons[j].boundary).Finite)

def IsSimple (mp : SFMultiPolygon) : Prop := mp.IsValid

def dim (mp : SFMultiPolygon) : WithBot ℕ :=
  if mp.polygons = [] then ⊥ else (2 : WithBot ℕ)

end SFMultiPolygon

/-! ## Complete 9-Type OGC Simple Features Geometry Hierarchy -/

/-- All nine OGC Simple Feature Access 1.2.1 geometry types. -/
inductive SFGeometry where
  | empty
  | point (p : Point2D)
  | multiPoint (mp : SFMultiPoint)
  | lineString (l : LineString)
  | multiLineString (ml : SFMultiLineString)
  | linearRing (r : SimplePolygon)
  | polygon (P : SFPolygon)
  | multiPolygon (mp : SFMultiPolygon)
  | collection (gs : List SFGeometry)

namespace SFGeometry

mutual
/-- Point-set carrier of any OGC Simple Features geometry. -/
def carrier : SFGeometry → Region
  | .empty => ∅
  | .point p => {p}
  | .multiPoint mp => mp.carrier
  | .lineString l => l.carrier
  | .multiLineString ml => ml.carrier
  | .linearRing r => r.boundary
  | .polygon P => P.carrier
  | .multiPolygon mp => mp.carrier
  | .collection gs => carrierList gs

/-- Union of carriers of a list of geometries. -/
def carrierList : List SFGeometry → Region
  | [] => ∅
  | g :: gs => g.carrier ∪ carrierList gs
end

mutual
/-- Boundary of any OGC Simple Features geometry, intersected with `carrier`
for `polygon`/`multiPolygon`/`collection` so that `boundary ⊆ carrier` holds
unconditionally even on invalid inputs (and agrees with the exact SFA boundary
on all valid inputs). -/
noncomputable def boundary : SFGeometry → Region
  | .empty => ∅
  | .point _ => ∅
  | .multiPoint _ => ∅
  | .lineString l => l.boundary
  | .multiLineString ml => ml.boundary
  | .linearRing _ => ∅
  | .polygon P => P.boundary ∩ P.carrier
  | .multiPolygon mp => mp.boundary ∩ mp.carrier
  | .collection gs => boundaryList gs ∩ carrierList gs

/-- Union of boundaries of a list of geometries. -/
noncomputable def boundaryList : List SFGeometry → Region
  | [] => ∅
  | g :: gs => g.boundary ∪ boundaryList gs
end

/-- Interior: carrier minus boundary (`I = G \ ∂G`, OGC SFA §6.1.2.1). -/
noncomputable def interior (g : SFGeometry) : Region :=
  g.carrier \ g.boundary

/-- Exterior: complement of carrier (`E = ℝ² \ G`, OGC SFA §6.1.2.1). -/
def exterior (g : SFGeometry) : Region :=
  g.carrierᶜ

/-- The three DE-9IM strata of any `SFGeometry`. -/
noncomputable def stratum (g : SFGeometry) : Stratum → Region
  | .I => g.interior
  | .B => g.boundary
  | .E => g.exterior

/-- OGC SFA dimension (`⊥` for empty, `0` for pointal, `1` for lineal, `2` for
areal, and supremum of member dimensions for `GeometryCollection`). -/
def dim : SFGeometry → WithBot ℕ
  | .empty => ⊥
  | .point _ => (0 : WithBot ℕ)
  | .multiPoint mp => mp.dim
  | .lineString _ => (1 : WithBot ℕ)
  | .multiLineString ml => ml.dim
  | .linearRing _ => (1 : WithBot ℕ)
  | .polygon _ => (2 : WithBot ℕ)
  | .multiPolygon mp => mp.dim
  | .collection gs => gs.foldl (fun acc g => max acc g.dim) ⊥

/-- OGC SFA validity predicate across all nine geometry types. -/
def IsValid : SFGeometry → Prop
  | .empty => True
  | .point _ => True
  | .multiPoint mp => mp.IsValid
  | .lineString _ => True
  | .multiLineString ml => ml.IsValid
  | .linearRing _ => True
  | .polygon P => P.IsValid
  | .multiPolygon mp => mp.IsValid
  | .collection gs => ∀ g ∈ gs, g.IsValid

/-- OGC SFA simplicity predicate across all nine geometry types. -/
def IsSimple : SFGeometry → Prop
  | .empty => True
  | .point _ => True
  | .multiPoint mp => mp.IsSimple
  | .lineString l => SFA.LineString.IsSimple l
  | .multiLineString ml => ml.IsSimple
  | .linearRing _ => True
  | .polygon P => P.IsSimple
  | .multiPolygon mp => mp.IsSimple
  | .collection gs => ∀ g ∈ gs, g.IsSimple

/-- For every `SFGeometry`, the boundary is a subset of the carrier. -/
theorem boundary_subset_carrier (g : SFGeometry) : g.boundary ⊆ g.carrier := by
  cases g with
  | empty => exact Subset.rfl
  | point _ => exact empty_subset _
  | multiPoint _ => exact empty_subset _
  | lineString l => exact l.boundary_subset
  | multiLineString ml => exact ml.boundary_subset_carrier
  | linearRing _ => exact empty_subset _
  | polygon _ => exact inter_subset_right
  | multiPolygon _ => exact inter_subset_right
  | collection _ => exact inter_subset_right

/-- For a valid `SFPolygon`, the `SFGeometry.boundary` equals `SFPolygon.boundary`
exactly (no clipping needed). -/
theorem boundary_polygon_of_isValid {P : SFPolygon} (hV : P.IsValid) :
    (SFGeometry.polygon P).boundary = P.boundary :=
  inter_eq_left.mpr (P.boundary_subset_carrier hV)

theorem stratum_I_union_B (g : SFGeometry) :
    g.stratum .I ∪ g.stratum .B = g.carrier :=
  sdiff_union_of_subset (g.boundary_subset_carrier)

theorem stratum_I_inter_B (g : SFGeometry) :
    g.stratum .I ∩ g.stratum .B = ∅ :=
  sdiff_inter_self

/-- **Universal partition theorem**: for ALL nine OGC Simple Features geometry
types (including Empty, MultiLineString with mod-2 boundary, Polygon with
holes, and GeometryCollection), every point of the plane belongs to a unique
stratum `I`, `B`, or `E`. -/
theorem existsUnique_stratum (g : SFGeometry) (p : Point2D) :
    ∃! s : Stratum, p ∈ g.stratum s := by
  have hU := g.stratum_I_union_B
  have hD := g.stratum_I_inter_B
  have hIB : ¬ (p ∈ g.stratum .I ∧ p ∈ g.stratum .B) := fun h => by
    have : p ∈ g.stratum .I ∩ g.stratum .B := h
    rw [hD] at this; exact this
  have hIE : p ∈ g.stratum .I → p ∉ g.stratum .E := fun h h' =>
    h' (hU ▸ Or.inl h)
  have hBE : p ∈ g.stratum .B → p ∉ g.stratum .E := fun h h' =>
    h' (hU ▸ Or.inr h)
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
  · refine ⟨.E, hp, ?_⟩
    rintro (_ | _ | _) ht
    · exact absurd hp (hIE ht)
    · exact absurd hp (hBE ht)
    · rfl

/-- DE-9IM cell of two `SFGeometry` values. -/
noncomputable def cell (s t : Stratum) (g h : SFGeometry) : Region :=
  g.stratum s ∩ h.stratum t

/-- DE-9IM matrix of two `SFGeometry` values using `DE9IM.DimValue.of`. -/
noncomputable def matrix (g h : SFGeometry) (s t : Stratum) : DE9IM.DimValue :=
  DE9IM.DimValue.of (cell s t g h)

/-- Whether two `SFGeometry` values match a `DE9IM.DimPattern`. -/
def MatchesPattern (p : DE9IM.DimPattern) (g h : SFGeometry) : Prop :=
  p.ii.Matches (cell .I .I g h) ∧ p.ib.Matches (cell .I .B g h) ∧
  p.ie.Matches (cell .I .E g h) ∧ p.bi.Matches (cell .B .I g h) ∧
  p.bb.Matches (cell .B .B g h) ∧ p.be.Matches (cell .B .E g h) ∧
  p.ei.Matches (cell .E .I g h) ∧ p.eb.Matches (cell .E .B g h) ∧
  p.ee.Matches (cell .E .E g h)

/-! ## Minimal counterexamples: OGC SFA vs GeoSPARQL vs GIS conventions -/

/-- **Counterexample 1 (Empty Geometry & Equals)**:
Two empty geometries have identical point sets (`empty.carrier = empty.carrier`),
yet they do NOT match OGC SFA / JTS's `T*F**FFF*` (`SFA.jtsEquals`) pattern
because `II = ∅`. This is why `Prover.Claim.rows .equals` must include
`FFFFFFFF*` alongside `T*F**FFF*`. -/
theorem empty_not_matches_jtsEquals :
    empty.carrier = empty.carrier ∧ ¬ MatchesPattern SFA.jtsEquals empty empty := by
  refine ⟨rfl, fun h => ?_⟩
  have hII := h.1
  change DE9IM.DimValue.of (cell .I .I empty empty) ≠ .F at hII
  rw [Ne, DE9IM.DimValue.of_eq_F_iff] at hII
  exact hII (by simp [cell, stratum, interior, carrier])

/-- **Counterexample 2 (`MultiLineString` Mod-2 Boundary Rule)**:
The two segments `[(0,0), (1,0)]` and `[(1,0), (2,0)]` share the endpoint
`(1, 0)`. Under OGC SFA §6.1.8's mod-2 boundary rule, `(1, 0)` belongs to two
component boundaries (even), so it cancels out of the `MultiLineString` boundary
and becomes an **interior** point, leaving boundary `{(0,0), (2,0)}`. -/
theorem mod2_shared_endpoint_cancels :
    let a : Point2D := Point2D.mk 0 0
    let b : Point2D := Point2D.mk 1 0
    let c : Point2D := Point2D.mk 2 0
    have hab : a ≠ b := fun h => by
      have := congrArg Geospatial.Point2D.x h; norm_num [a, b] at this
    have hbc : b ≠ c := fun h => by
      have := congrArg Geospatial.Point2D.x h; norm_num [b, c] at this
    let ml : SFMultiLineString := ⟨[LineString.seg a b hab, LineString.seg b c hbc]⟩
    b ∉ ml.boundary ∧ b ∈ (SFGeometry.multiLineString ml).interior := by
  intro a b c hab hbc ml
  have hba : b ≠ a := hab.symm
  have hcb : c ≠ b := hbc.symm
  have hca : c ≠ a := fun h => by
    have := congrArg Geospatial.Point2D.x h; norm_num [a, c] at this
  have hcnt : ml.boundaryCount b = 2 := by
    classical
    unfold SFMultiLineString.boundaryCount
    simp only [ml, List.countP_cons, List.countP_nil, LineString.seg_boundary]
    have h1 : b ∈ ({a, b} : Region) := Or.inr rfl
    have h2 : b ∈ ({b, c} : Region) := Or.inl rfl
    simp [h1, h2]
  have hnotB : b ∉ ml.boundary := by
    show ¬ Odd (ml.boundaryCount b)
    rw [hcnt]
    decide
  refine ⟨hnotB, ?_, hnotB⟩
  exact ⟨LineString.seg a b hab, List.mem_cons_self, by
    rw [LineString.seg_carrier]; exact right_mem_segment a b⟩

/-- **Counterexample 3 (`MultiPoint` simplicity vs validity)**:
A `MultiPoint` with a duplicated point `[(0, 0), (0, 0)]` is NOT simple per
OGC SFA §6.1.5 (`¬ IsSimple`), yet is still valid (`IsValid`), matching
JTS/GEOS/PostGIS practice. -/
theorem multiPoint_dup_valid_not_simple :
    let p := Point2D.mk 0 0
    let mp : SFMultiPoint := ⟨[p, p]⟩
    mp.IsValid ∧ ¬ mp.IsSimple := by
  intro p mp
  refine ⟨trivial, fun h => ?_⟩
  simp [mp, SFMultiPoint.IsSimple] at h

/-- **Counterexample 4 (`GeometryCollection` naive strata overlap)**:
OGC SFA §6.1.2.4 does not specify a boundary rule for heterogeneous
`GeometryCollection`s. If one naively takes the union of member interiors and
the union of member boundaries for `{point (0, 0), square [0, 2]×[0, 2]}`,
`(0, 0)` lies in BOTH the point's interior and the square's boundary, violating
disjointness of `I` and `B`. -/
theorem collection_naive_strata_overlap :
    let p := Point2D.mk 0 0
    let r : Rect := ⟨0, 2, 0, 2⟩
    p ∈ (Geometry.point p).stratum .I ∧
      p ∈ (Geometry.area (r.toRegularClosed (by norm_num) (by norm_num))).stratum .B := by
  intro p r
  refine ⟨rfl, ?_⟩
  change p ∈ Geospatial.boundary r.toRegion
  rw [Rect.boundary_toRegion]
  refine ⟨⟨by norm_num [p, r], by norm_num [p, r], by norm_num [p, r], by norm_num [p, r]⟩, ?_⟩
  rintro ⟨h, -, -, -⟩
  norm_num [p, r] at h

/-- A `LinearRing` is closed and therefore has empty SFA boundary. -/
theorem linearRing_boundary_empty (r : SimplePolygon) :
    (SFGeometry.linearRing r).boundary = ∅ := rfl

end SFGeometry

end Geospatial.SFA
