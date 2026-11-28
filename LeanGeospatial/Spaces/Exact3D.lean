import LeanGeospatial.ComputationalPolygon
import LeanGeospatial.Spaces.IntrinsicVsAmbient

/-!
# Exact Computational Geometry across `ℝ²`, `S²`, and `ℝ³`

Extends the GIS-free computational geometry bridge (`ComputationalPolygon.lean`)
across all three spaces `ℝ²`, `S²`, and `ℝ³`:

1. **`S²` (Spherical lift of exact integer rectangles)**:
   - `IRect.liftToS2`: lifts any proper integer rectangle `IRect` to a
     `RegularClosedRegion S2` via inverse stereographic projection.
   - `IRect.rcc8_holds_S2`: the computable integer decision procedure
     `IRect.rcc8` is proved **exact** for the topological `RCC8` relation on `S²`.
2. **`ℝ³` (Exact integer 3D axis-aligned boxes `IBox3`)**:
   - `IBox3`: integer 3D bounding box (`xy : IRect`, `zmin zmax : ℤ`) whose
     point-set semantics `IBox3.toSolid3D` is built directly via
     `extrudeRegularClosed` (reusing 2D `IRect` without duplication).
   - `IBox3.rcc8` / `IBox3.rcc8_holds`: computable exact integer 3D RCC8
     decision procedure proved equivalent to topological `RCC8.Relation.holds`
     on `RegularClosedRegion E3` (no external 3D GIS engine needed).
   - `IBox3.intersectsB` / `IBox3.intersectsB_iff`: computable 3D intersection
     test proved equivalent to `Geospatial.Intersects` in `ℝ³`.
-/

namespace Geospatial.Spaces

open Set Topology Geospatial Geospatial.DE9IM.Space3 Geospatial.Space2D3D

/-! ## 1. Exact computational RCC8 on `S²` -/

/-- Lift a proper integer rectangle `IRect` to a `RegularClosedRegion S2` via
inverse stereographic projection. -/
noncomputable def _root_.Geospatial.IRect.liftToS2 (r : IRect) (hr : r.IsProper) :
    RegularClosedRegion S2 :=
  Geospatial.Spaces.liftToS2 (r.toRegularClosed hr) r.toRect.isCompact_toRegion

/-- **GIS-free exact RCC8 on `S²`**: the computable integer decision procedure
`IRect.rcc8` decides the exact topological `RCC8` relation on `S²`. -/
theorem _root_.Geospatial.IRect.rcc8_holds_S2 (r s : IRect)
    (hr : r.IsProper) (hs : s.IsProper) :
    (r.rcc8 s).holds (r.liftToS2 hr) (s.liftToS2 hs) :=
  (liftToS2_rcc8_iff r.toRect.isCompact_toRegion s.toRect.isCompact_toRegion (r.rcc8 s)).mpr
    (r.rcc8_holds s hr hs)

/-! ## 2. Exact integer 3D axis-aligned boxes (`IBox3`) on `ℝ³` -/

/-- Exact integer 3D axis-aligned box `[xmin, xmax] × [ymin, ymax] × [zmin, zmax]`. -/
structure IBox3 where
  xy : IRect
  zmin : Int
  zmax : Int
  deriving DecidableEq, Repr

namespace IBox3

/-- A 3D box is proper when all three side lengths are strictly positive. -/
def IsProper (b : IBox3) : Prop :=
  b.xy.IsProper ∧ b.zmin < b.zmax

/-- Point-set semantics of a proper `IBox3` as a 3D `RegularClosedRegion E3`. -/
noncomputable def toSolid3D (b : IBox3) (hb : b.IsProper) : RegularClosedRegion E3 :=
  extrudeRegularClosed (Int.cast_lt.mpr hb.2) (b.xy.toRegularClosed hb.1)

/-- Computable exact integer 3D RCC8 decision procedure for two `IBox3` solids. -/
def rcc8 (a b : IBox3) : RCC8.Relation :=
  if a == b then .eq
  else if a.xy.xmax < b.xy.xmin || b.xy.xmax < a.xy.xmin ||
          a.xy.ymax < b.xy.ymin || b.xy.ymax < a.xy.ymin ||
          a.zmax < b.zmin || b.zmax < a.zmin then .dc
  else if a.xy.xmax == b.xy.xmin || b.xy.xmax == a.xy.xmin ||
          a.xy.ymax == b.xy.ymin || b.xy.ymax == a.xy.ymin ||
          a.zmax == b.zmin || b.zmax == a.zmin then .ec
  else if b.xy.xmin < a.xy.xmin && a.xy.xmax < b.xy.xmax &&
          b.xy.ymin < a.xy.ymin && a.xy.ymax < b.xy.ymax &&
          b.zmin < a.zmin && a.zmax < b.zmax then .ntpp
  else if b.xy.xmin ≤ a.xy.xmin && a.xy.xmax ≤ b.xy.xmax &&
          b.xy.ymin ≤ a.xy.ymin && a.xy.ymax ≤ b.xy.ymax &&
          b.zmin ≤ a.zmin && a.zmax ≤ b.zmax then .tpp
  else if a.xy.xmin < b.xy.xmin && b.xy.xmax < a.xy.xmax &&
          a.xy.ymin < b.xy.ymin && b.xy.ymax < a.xy.ymax &&
          a.zmin < b.zmin && b.zmax < a.zmax then .ntppi
  else if a.xy.xmin ≤ b.xy.xmin && b.xy.xmax ≤ a.xy.xmax &&
          a.xy.ymin ≤ b.xy.ymin && b.xy.ymax ≤ a.xy.ymax &&
          a.zmin ≤ b.zmin && b.zmax ≤ a.zmax then .tppi
  else .po

/-- Computable exact integer 3D intersection test. -/
def intersectsB (a b : IBox3) : Bool :=
  !(a.xy.xmax < b.xy.xmin || b.xy.xmax < a.xy.xmin ||
    a.xy.ymax < b.xy.ymin || b.xy.ymax < a.xy.ymin ||
    a.zmax < b.zmin || b.zmax < a.zmin)

private theorem mem_toSolid3D_iff (b : IBox3) (hb : b.IsProper) (p : E3) :
    p ∈ (b.toSolid3D hb : Set E3) ↔
      (b.xy.xmin : ℝ) ≤ p 0 ∧ p 0 ≤ (b.xy.xmax : ℝ) ∧
      (b.xy.ymin : ℝ) ≤ p 1 ∧ p 1 ≤ (b.xy.ymax : ℝ) ∧
      (b.zmin : ℝ) ≤ p 2 ∧ p 2 ≤ (b.zmax : ℝ) := by
  change projXY p ∈ b.xy.toRect.toRegion ∧ p 2 ∈ Icc (b.zmin : ℝ) (b.zmax : ℝ) ↔ _
  simp only [Rect.toRegion, IRect.toRect, mem_ofPred_eq, mem_Icc, projXY,
    Point2D.x_mk, Point2D.y_mk]
  tauto

private theorem mem_interior_toSolid3D_iff (b : IBox3) (hb : b.IsProper) (p : E3) :
    p ∈ interior (b.toSolid3D hb : Set E3) ↔
      (b.xy.xmin : ℝ) < p 0 ∧ p 0 < (b.xy.xmax : ℝ) ∧
      (b.xy.ymin : ℝ) < p 1 ∧ p 1 < (b.xy.ymax : ℝ) ∧
      (b.zmin : ℝ) < p 2 ∧ p 2 < (b.zmax : ℝ) := by
  change p ∈ interior (extrude (b.zmin : ℝ) (b.zmax : ℝ) b.xy.toRect.toRegion) ↔ _
  rw [interior_extrude]
  change projXY p ∈ interior b.xy.toRect.toRegion ∧ p 2 ∈ Ioo (b.zmin : ℝ) (b.zmax : ℝ) ↔ _
  rw [Rect.interior_toRegion]
  simp only [Rect.openRegion, IRect.toRect, mem_ofPred_eq, mem_Ioo, projXY,
    Point2D.x_mk, Point2D.y_mk]
  tauto

private theorem subset_iff (a b : IBox3) (ha : a.IsProper) (hb : b.IsProper) :
    ((a.toSolid3D ha : Set E3) ⊆ (b.toSolid3D hb : Set E3)) ↔
      (b.xy.xmin ≤ a.xy.xmin ∧ a.xy.xmax ≤ b.xy.xmax ∧
       b.xy.ymin ≤ a.xy.ymin ∧ a.xy.ymax ≤ b.xy.ymax ∧
       b.zmin ≤ a.zmin ∧ a.zmax ≤ b.zmax) := by
  constructor
  · intro hsub
    have h1 := (mem_toSolid3D_iff b hb _).mp <| hsub <| (mem_toSolid3D_iff a ha (pt a.xy.xmin a.xy.ymin a.zmin)).mpr (by
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      exact ⟨le_rfl, Int.cast_le.mpr ha.1.1.le, le_rfl, Int.cast_le.mpr ha.1.2.le, le_rfl, Int.cast_le.mpr ha.2.le⟩)
    have h2 := (mem_toSolid3D_iff b hb _).mp <| hsub <| (mem_toSolid3D_iff a ha (pt a.xy.xmax a.xy.ymax a.zmax)).mpr (by
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      exact ⟨Int.cast_le.mpr ha.1.1.le, le_rfl, Int.cast_le.mpr ha.1.2.le, le_rfl, Int.cast_le.mpr ha.2.le, le_rfl⟩)
    simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 h2
    exact ⟨Int.cast_le.mp h1.1, Int.cast_le.mp h2.2.1,
           Int.cast_le.mp h1.2.2.1, Int.cast_le.mp h2.2.2.2.1,
           Int.cast_le.mp h1.2.2.2.2.1, Int.cast_le.mp h2.2.2.2.2.2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ p hp
    rw [mem_toSolid3D_iff] at hp ⊢
    exact ⟨(Int.cast_le.mpr h1).trans hp.1, hp.2.1.trans (Int.cast_le.mpr h2),
           (Int.cast_le.mpr h3).trans hp.2.2.1, hp.2.2.2.1.trans (Int.cast_le.mpr h4),
           (Int.cast_le.mpr h5).trans hp.2.2.2.2.1, hp.2.2.2.2.2.trans (Int.cast_le.mpr h6)⟩

private theorem subset_interior_iff (a b : IBox3) (ha : a.IsProper) (hb : b.IsProper) :
    ((a.toSolid3D ha : Set E3) ⊆ interior (b.toSolid3D hb : Set E3)) ↔
      (b.xy.xmin < a.xy.xmin ∧ a.xy.xmax < b.xy.xmax ∧
       b.xy.ymin < a.xy.ymin ∧ a.xy.ymax < b.xy.ymax ∧
       b.zmin < a.zmin ∧ a.zmax < b.zmax) := by
  constructor
  · intro hsub
    have h1 := (mem_interior_toSolid3D_iff b hb _).mp <| hsub <| (mem_toSolid3D_iff a ha (pt a.xy.xmin a.xy.ymin a.zmin)).mpr (by
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      exact ⟨le_rfl, Int.cast_le.mpr ha.1.1.le, le_rfl, Int.cast_le.mpr ha.1.2.le, le_rfl, Int.cast_le.mpr ha.2.le⟩)
    have h2 := (mem_interior_toSolid3D_iff b hb _).mp <| hsub <| (mem_toSolid3D_iff a ha (pt a.xy.xmax a.xy.ymax a.zmax)).mpr (by
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      exact ⟨Int.cast_le.mpr ha.1.1.le, le_rfl, Int.cast_le.mpr ha.1.2.le, le_rfl, Int.cast_le.mpr ha.2.le, le_rfl⟩)
    simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h1 h2
    exact ⟨Int.cast_lt.mp h1.1, Int.cast_lt.mp h2.2.1,
           Int.cast_lt.mp h1.2.2.1, Int.cast_lt.mp h2.2.2.2.1,
           Int.cast_lt.mp h1.2.2.2.2.1, Int.cast_lt.mp h2.2.2.2.2.2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ p hp
    rw [mem_toSolid3D_iff] at hp
    rw [mem_interior_toSolid3D_iff]
    exact ⟨(Int.cast_lt.mpr h1).trans_le hp.1, hp.2.1.trans_lt (Int.cast_lt.mpr h2),
           (Int.cast_lt.mpr h3).trans_le hp.2.2.1, hp.2.2.2.1.trans_lt (Int.cast_lt.mpr h4),
           (Int.cast_lt.mpr h5).trans_le hp.2.2.2.2.1, hp.2.2.2.2.2.trans_lt (Int.cast_lt.mpr h6)⟩

private theorem inter_nonempty_iff (a b : IBox3) (ha : a.IsProper) (hb : b.IsProper) :
    ((a.toSolid3D ha : Set E3) ∩ (b.toSolid3D hb : Set E3)).Nonempty ↔
      (max a.xy.xmin b.xy.xmin ≤ min a.xy.xmax b.xy.xmax ∧
       max a.xy.ymin b.xy.ymin ≤ min a.xy.ymax b.xy.ymax ∧
       max a.zmin b.zmin ≤ min a.zmax b.zmax) := by
  constructor
  · rintro ⟨p, hpA, hpB⟩
    rw [mem_toSolid3D_iff] at hpA hpB
    have hx : (max a.xy.xmin b.xy.xmin : ℝ) ≤ (min a.xy.xmax b.xy.xmax : ℝ) :=
      max_le (hpA.1.trans (le_min hpA.2.1 hpB.2.1)) (hpB.1.trans (le_min hpA.2.1 hpB.2.1))
    have hy : (max a.xy.ymin b.xy.ymin : ℝ) ≤ (min a.xy.ymax b.xy.ymax : ℝ) :=
      max_le (hpA.2.2.1.trans (le_min hpA.2.2.2.1 hpB.2.2.2.1)) (hpB.2.2.1.trans (le_min hpA.2.2.2.1 hpB.2.2.2.1))
    have hz : (max a.zmin b.zmin : ℝ) ≤ (min a.zmax b.zmax : ℝ) :=
      max_le (hpA.2.2.2.2.1.trans (le_min hpA.2.2.2.2.2 hpB.2.2.2.2.2)) (hpB.2.2.2.2.1.trans (le_min hpA.2.2.2.2.2 hpB.2.2.2.2.2))
    exact ⟨Int.cast_le.mp (by exact_mod_cast hx),
           Int.cast_le.mp (by exact_mod_cast hy),
           Int.cast_le.mp (by exact_mod_cast hz)⟩
  · rintro ⟨hx, hy, hz⟩
    refine ⟨pt (max a.xy.xmin b.xy.xmin : Int) (max a.xy.ymin b.xy.ymin : Int) (max a.zmin b.zmin : Int), ?_, ?_⟩
    · rw [mem_toSolid3D_iff]
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      exact ⟨by exact_mod_cast le_max_left a.xy.xmin b.xy.xmin,
             by exact_mod_cast hx.trans (min_le_left a.xy.xmax b.xy.xmax),
             by exact_mod_cast le_max_left a.xy.ymin b.xy.ymin,
             by exact_mod_cast hy.trans (min_le_left a.xy.ymax b.xy.ymax),
             by exact_mod_cast le_max_left a.zmin b.zmin,
             by exact_mod_cast hz.trans (min_le_left a.zmax b.zmax)⟩
    · rw [mem_toSolid3D_iff]
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      exact ⟨by exact_mod_cast le_max_right a.xy.xmin b.xy.xmin,
             by exact_mod_cast hx.trans (min_le_right a.xy.xmax b.xy.xmax),
             by exact_mod_cast le_max_right a.xy.ymin b.xy.ymin,
             by exact_mod_cast hy.trans (min_le_right a.xy.ymax b.xy.ymax),
             by exact_mod_cast le_max_right a.zmin b.zmin,
             by exact_mod_cast hz.trans (min_le_right a.zmax b.zmax)⟩

private theorem interior_inter_nonempty_iff (a b : IBox3) (ha : a.IsProper) (hb : b.IsProper) :
    (interior (a.toSolid3D ha : Set E3) ∩ interior (b.toSolid3D hb : Set E3)).Nonempty ↔
      (max a.xy.xmin b.xy.xmin < min a.xy.xmax b.xy.xmax ∧
       max a.xy.ymin b.xy.ymin < min a.xy.ymax b.xy.ymax ∧
       max a.zmin b.zmin < min a.zmax b.zmax) := by
  constructor
  · rintro ⟨p, hpA, hpB⟩
    rw [mem_interior_toSolid3D_iff] at hpA hpB
    have hx : (max a.xy.xmin b.xy.xmin : ℝ) < (min a.xy.xmax b.xy.xmax : ℝ) :=
      max_lt (hpA.1.trans (lt_min hpA.2.1 hpB.2.1)) (hpB.1.trans (lt_min hpA.2.1 hpB.2.1))
    have hy : (max a.xy.ymin b.xy.ymin : ℝ) < (min a.xy.ymax b.xy.ymax : ℝ) :=
      max_lt (hpA.2.2.1.trans (lt_min hpA.2.2.2.1 hpB.2.2.2.1)) (hpB.2.2.1.trans (lt_min hpA.2.2.2.1 hpB.2.2.2.1))
    have hz : (max a.zmin b.zmin : ℝ) < (min a.zmax b.zmax : ℝ) :=
      max_lt (hpA.2.2.2.2.1.trans (lt_min hpA.2.2.2.2.2 hpB.2.2.2.2.2)) (hpB.2.2.2.2.1.trans (lt_min hpA.2.2.2.2.2 hpB.2.2.2.2.2))
    exact ⟨Int.cast_lt.mp (by exact_mod_cast hx),
           Int.cast_lt.mp (by exact_mod_cast hy),
           Int.cast_lt.mp (by exact_mod_cast hz)⟩
  · rintro ⟨hx, hy, hz⟩
    set x := ((max a.xy.xmin b.xy.xmin : ℝ) + (min a.xy.xmax b.xy.xmax : ℝ)) / 2
    set y := ((max a.xy.ymin b.xy.ymin : ℝ) + (min a.xy.ymax b.xy.ymax : ℝ)) / 2
    set z := ((max a.zmin b.zmin : ℝ) + (min a.zmax b.zmax : ℝ)) / 2
    have hx' : (max a.xy.xmin b.xy.xmin : ℝ) < (min a.xy.xmax b.xy.xmax : ℝ) := by exact_mod_cast hx
    have hy' : (max a.xy.ymin b.xy.ymin : ℝ) < (min a.xy.ymax b.xy.ymax : ℝ) := by exact_mod_cast hy
    have hz' : (max a.zmin b.zmin : ℝ) < (min a.zmax b.zmax : ℝ) := by exact_mod_cast hz
    have hax1 : (a.xy.xmin : ℝ) ≤ (max a.xy.xmin b.xy.xmin : ℝ) := by exact_mod_cast le_max_left a.xy.xmin b.xy.xmin
    have hax2 : (min a.xy.xmax b.xy.xmax : ℝ) ≤ (a.xy.xmax : ℝ) := by exact_mod_cast min_le_left a.xy.xmax b.xy.xmax
    have hbx1 : (b.xy.xmin : ℝ) ≤ (max a.xy.xmin b.xy.xmin : ℝ) := by exact_mod_cast le_max_right a.xy.xmin b.xy.xmin
    have hbx2 : (min a.xy.xmax b.xy.xmax : ℝ) ≤ (b.xy.xmax : ℝ) := by exact_mod_cast min_le_right a.xy.xmax b.xy.xmax
    have hay1 : (a.xy.ymin : ℝ) ≤ (max a.xy.ymin b.xy.ymin : ℝ) := by exact_mod_cast le_max_left a.xy.ymin b.xy.ymin
    have hay2 : (min a.xy.ymax b.xy.ymax : ℝ) ≤ (a.xy.ymax : ℝ) := by exact_mod_cast min_le_left a.xy.ymax b.xy.ymax
    have hby1 : (b.xy.ymin : ℝ) ≤ (max a.xy.ymin b.xy.ymin : ℝ) := by exact_mod_cast le_max_right a.xy.ymin b.xy.ymin
    have hby2 : (min a.xy.ymax b.xy.ymax : ℝ) ≤ (b.xy.ymax : ℝ) := by exact_mod_cast min_le_right a.xy.ymax b.xy.ymax
    have haz1 : (a.zmin : ℝ) ≤ (max a.zmin b.zmin : ℝ) := by exact_mod_cast le_max_left a.zmin b.zmin
    have haz2 : (min a.zmax b.zmax : ℝ) ≤ (a.zmax : ℝ) := by exact_mod_cast min_le_left a.zmax b.zmax
    have hbz1 : (b.zmin : ℝ) ≤ (max a.zmin b.zmin : ℝ) := by exact_mod_cast le_max_right a.zmin b.zmin
    have hbz2 : (min a.zmax b.zmax : ℝ) ≤ (b.zmax : ℝ) := by exact_mod_cast min_le_right a.zmax b.zmax
    refine ⟨pt x y z, ?_, ?_⟩
    · rw [mem_interior_toSolid3D_iff]
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, x, y, z]
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rw [mem_interior_toSolid3D_iff]
      simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, x, y, z]
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **GIS-free exact 3D intersection**: `IBox3.intersectsB` decides
`Geospatial.Intersects` in `ℝ³`. -/
theorem intersectsB_iff (a b : IBox3) (ha : a.IsProper) (hb : b.IsProper) :
    a.intersectsB b = true ↔ Intersects (a.toSolid3D ha : Set E3) (b.toSolid3D hb : Set E3) := by
  rw [Geospatial.Intersects, inter_nonempty_iff a b ha hb]
  simp only [intersectsB, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
    not_lt, max_le_iff, le_min_iff]
  rcases ha with ⟨⟨ha1, ha2⟩, ha3⟩
  rcases hb with ⟨⟨hb1, hb2⟩, hb3⟩
  omega

/-- **GIS-free exact 3D RCC8**: `IBox3.rcc8` decides the exact topological
`RCC8.Relation.holds` on `RegularClosedRegion E3`. -/
theorem rcc8_holds (a b : IBox3) (ha : a.IsProper) (hb : b.IsProper) :
    (a.rcc8 b).holds (a.toSolid3D ha) (b.toSolid3D hb) := by
  have ha' := ha; have hb' := hb
  rcases ha with ⟨⟨ha1, ha2⟩, ha3⟩
  rcases hb with ⟨⟨hb1, hb2⟩, hb3⟩
  unfold rcc8
  split_ifs with hEQ hDC hEC hNTPP hTPP hNTPPi hTPPi
  · -- EQ
    have heq : a = b := beq_iff_eq.mp hEQ
    subst heq; exact rfl
  · -- DC
    show Geospatial.Disjoint (a.toSolid3D ha' : Set E3) (b.toSolid3D hb' : Set E3)
    rw [disjoint_iff_not_intersects, Geospatial.Intersects, inter_nonempty_iff a b ha' hb']
    simp only [Bool.or_eq_true, decide_eq_true_eq, max_le_iff, le_min_iff] at hDC ⊢
    omega
  · -- EC
    show Geospatial.Touches (a.toSolid3D ha' : Set E3) (b.toSolid3D hb' : Set E3)
    refine ⟨(inter_nonempty_iff a b ha' hb').mpr ?_, disjoint_iff_not_intersects.mpr fun h => ?_⟩
    · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, max_le_iff, le_min_iff] at hDC ⊢
      omega
    · have := (interior_inter_nonempty_iff a b ha' hb').mp h
      simp only [Bool.or_eq_true, beq_iff_eq, max_lt_iff, lt_min_iff] at hEC this
      omega
  · -- NTPP
    show RCC8.NTPP (a.toSolid3D ha') (b.toSolid3D hb')
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hEQ hNTPP
    refine ⟨(subset_interior_iff a b ha' hb').mpr
      ⟨hNTPP.1.1.1.1.1, hNTPP.1.1.1.1.2, hNTPP.1.1.1.2, hNTPP.1.1.2, hNTPP.1.2, hNTPP.2⟩,
      fun heq => hEQ ?_⟩
    have hba := (subset_iff b a hb' ha').mp (show (b.toSolid3D hb' : Set E3) ⊆ (a.toSolid3D ha' : Set E3) by rw [heq])
    rcases a with ⟨⟨ax1, ax2, ay1, ay2⟩, az1, az2⟩
    rcases b with ⟨⟨bx1, bx2, by1, by2⟩, bz1, bz2⟩
    dsimp only at hba hNTPP; simp only [IBox3.mk.injEq, IRect.mk.injEq]; omega
  · -- TPP
    show RCC8.TPP (a.toSolid3D ha') (b.toSolid3D hb')
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hEQ hNTPP hTPP
    refine ⟨(subset_iff a b ha' hb').mpr
      ⟨hTPP.1.1.1.1.1, hTPP.1.1.1.1.2, hTPP.1.1.1.2, hTPP.1.1.2, hTPP.1.2, hTPP.2⟩,
      fun heq => hEQ ?_, fun hint => hNTPP ?_⟩
    · have hba := (subset_iff b a hb' ha').mp (show (b.toSolid3D hb' : Set E3) ⊆ (a.toSolid3D ha' : Set E3) by rw [heq])
      rcases a with ⟨⟨ax1, ax2, ay1, ay2⟩, az1, az2⟩
      rcases b with ⟨⟨bx1, bx2, by1, by2⟩, bz1, bz2⟩
      dsimp only at hba hTPP; simp only [IBox3.mk.injEq, IRect.mk.injEq]; omega
    · have := (subset_interior_iff a b ha' hb').mp hint
      exact ⟨⟨⟨⟨⟨this.1, this.2.1⟩, this.2.2.1⟩, this.2.2.2.1⟩, this.2.2.2.2.1⟩, this.2.2.2.2.2⟩
  · -- NTPPi
    show RCC8.NTPPi (a.toSolid3D ha') (b.toSolid3D hb')
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hEQ hNTPPi
    refine ⟨(subset_interior_iff b a hb' ha').mpr
      ⟨hNTPPi.1.1.1.1.1, hNTPPi.1.1.1.1.2, hNTPPi.1.1.1.2, hNTPPi.1.1.2, hNTPPi.1.2, hNTPPi.2⟩,
      fun heq => hEQ ?_⟩
    have hab := (subset_iff a b ha' hb').mp (show (a.toSolid3D ha' : Set E3) ⊆ (b.toSolid3D hb' : Set E3) by rw [heq])
    rcases a with ⟨⟨ax1, ax2, ay1, ay2⟩, az1, az2⟩
    rcases b with ⟨⟨bx1, bx2, by1, by2⟩, bz1, bz2⟩
    dsimp only at hab hNTPPi; simp only [IBox3.mk.injEq, IRect.mk.injEq]; omega
  · -- TPPi
    show RCC8.TPPi (a.toSolid3D ha') (b.toSolid3D hb')
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hEQ hNTPPi hTPPi
    refine ⟨(subset_iff b a hb' ha').mpr
      ⟨hTPPi.1.1.1.1.1, hTPPi.1.1.1.1.2, hTPPi.1.1.1.2, hTPPi.1.1.2, hTPPi.1.2, hTPPi.2⟩,
      fun heq => hEQ ?_, fun hint => hNTPPi ?_⟩
    · have hab := (subset_iff a b ha' hb').mp (show (a.toSolid3D ha' : Set E3) ⊆ (b.toSolid3D hb' : Set E3) by rw [heq])
      rcases a with ⟨⟨ax1, ax2, ay1, ay2⟩, az1, az2⟩
      rcases b with ⟨⟨bx1, bx2, by1, by2⟩, bz1, bz2⟩
      dsimp only at hab hTPPi; simp only [IBox3.mk.injEq, IRect.mk.injEq]; omega
    · have := (subset_interior_iff b a hb' ha').mp hint
      exact ⟨⟨⟨⟨⟨this.1, this.2.1⟩, this.2.2.1⟩, this.2.2.2.1⟩, this.2.2.2.2.1⟩, this.2.2.2.2.2⟩
  · -- PO
    show RCC8.PO (a.toSolid3D ha') (b.toSolid3D hb')
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, not_lt] at hDC hEC hTPP hTPPi
    refine ⟨(interior_inter_nonempty_iff a b ha' hb').mpr (by simp only [max_lt_iff, lt_min_iff]; omega),
      fun h => hTPP ?_, fun h => hTPPi ?_⟩
    · have := (subset_iff a b ha' hb').mp h
      exact ⟨⟨⟨⟨⟨this.1, this.2.1⟩, this.2.2.1⟩, this.2.2.2.1⟩, this.2.2.2.2.1⟩, this.2.2.2.2.2⟩
    · have := (subset_iff b a hb' ha').mp h
      exact ⟨⟨⟨⟨⟨this.1, this.2.1⟩, this.2.2.1⟩, this.2.2.2.1⟩, this.2.2.2.2.1⟩, this.2.2.2.2.2⟩

end IBox3

end Geospatial.Spaces
