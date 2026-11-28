import LeanGeospatial.Spaces.Exact3D
import LeanGeospatial.Spaces.SphericalPartition

/-!
# Worked Proof Examples across `ℝ²`, `S²`, and `ℝ³`

Concrete machine-checked examples demonstrating the unified geospatial
semantics and GIS-free computational decision procedures across all three
spaces:

1. **`ℝ²` (Plane)**: two exact integer rectangles proved `RCC8.EC` by computation.
2. **`S²` (2-Sphere)**: two lifted spherical regions proved `RCC8.EC` and
   `RCC8.PO` by integer computation via `IRect.rcc8_holds_S2`, plus concrete
   spherical cell membership in `sphericalHierarchy`.
3. **`ℝ³` (3D Space)**: concrete 3D integer boxes (`IBox3`) proved `RCC8.DC`
   (stacked floors), `RCC8.EC` (face-sharing rooms), and `RCC8.NTPP`
   (vault strictly inside floor 1) directly by `IBox3.rcc8_holds`.
-/

namespace Geospatial.Examples.ThreeSpaces

open Geospatial Geospatial.Spaces

/-! ## 1. `ℝ²` examples -/

def rectWest : IRect := ⟨0, 2, 0, 2⟩
def rectEast : IRect := ⟨2, 4, 0, 2⟩
def rectOverlap : IRect := ⟨1, 3, 0, 2⟩

private theorem rectWest_proper : rectWest.IsProper := ⟨by decide, by decide⟩
private theorem rectEast_proper : rectEast.IsProper := ⟨by decide, by decide⟩
private theorem rectOverlap_proper : rectOverlap.IsProper := ⟨by decide, by decide⟩

theorem plane_west_ec_east :
    RCC8.EC (rectWest.toRegularClosed rectWest_proper)
            (rectEast.toRegularClosed rectEast_proper) :=
  rectWest.rcc8_holds rectEast rectWest_proper rectEast_proper

/-! ## 2. `S²` examples -/

/-- Two adjacent spherical regions on `S²` proved `RCC8.EC` by integer computation. -/
theorem sphere_west_ec_east :
    RCC8.EC (rectWest.liftToS2 rectWest_proper) (rectEast.liftToS2 rectEast_proper) :=
  rectWest.rcc8_holds_S2 rectEast rectWest_proper rectEast_proper

/-- Two overlapping spherical regions on `S²` proved `RCC8.PO` by integer computation. -/
theorem sphere_west_po_overlap :
    RCC8.PO (rectWest.liftToS2 rectWest_proper) (rectOverlap.liftToS2 rectOverlap_proper) :=
  rectWest.rcc8_holds_S2 rectOverlap rectWest_proper rectOverlap_proper

/-- The north pole lies in spherical cell `(.posZ, (0, 0))` at level `0`. -/
theorem sphere_northPole_cell0 :
    northPole ∈ (sphericalHierarchy.level 0).cell (.posZ, fun _ => 0) := by
  refine ⟨?_, ?_⟩
  · unfold cubeFace northPole; norm_num
  · have hface : cubeFace northPole = .posZ := by unfold cubeFace northPole; norm_num
    unfold faceUV
    rw [hface]
    intro k; fin_cases k <;> simp [northPole, Point2D.mk]

/-! ## 3. `ℝ³` examples -/

def floor1 : IBox3 := ⟨⟨0, 10, 0, 10⟩, 0, 3⟩
def floor2 : IBox3 := ⟨⟨0, 10, 0, 10⟩, 3, 6⟩
def floor3 : IBox3 := ⟨⟨0, 10, 0, 10⟩, 6, 9⟩
def innerVault : IBox3 := ⟨⟨2, 8, 2, 8⟩, 1, 2⟩

private theorem floor1_proper : floor1.IsProper := ⟨⟨by decide, by decide⟩, by decide⟩
private theorem floor2_proper : floor2.IsProper := ⟨⟨by decide, by decide⟩, by decide⟩
private theorem floor3_proper : floor3.IsProper := ⟨⟨by decide, by decide⟩, by decide⟩
private theorem innerVault_proper : innerVault.IsProper := ⟨⟨by decide, by decide⟩, by decide⟩

/-- Floor 1 (`z ∈ [0, 3]`) and Floor 3 (`z ∈ [6, 9]`) are disjoint (`RCC8.DC`) in `ℝ³`. -/
theorem space3_floor1_dc_floor3 :
    RCC8.DC (floor1.toSolid3D floor1_proper) (floor3.toSolid3D floor3_proper) :=
  floor1.rcc8_holds floor3 floor1_proper floor3_proper

/-- Floor 1 (`z ∈ [0, 3]`) and Floor 2 (`z ∈ [3, 6]`) externally touch (`RCC8.EC`)
along the shared ceiling/floor slab `z = 3` in `ℝ³`. -/
theorem space3_floor1_ec_floor2 :
    RCC8.EC (floor1.toSolid3D floor1_proper) (floor2.toSolid3D floor2_proper) :=
  floor1.rcc8_holds floor2 floor1_proper floor2_proper

/-- An interior vault (`[2, 8] × [2, 8] × [1, 2]`) is strictly inside Floor 1
(`RCC8.NTPP`) in `ℝ³`. -/
theorem space3_vault_ntpp_floor1 :
    RCC8.NTPP (innerVault.toSolid3D innerVault_proper) (floor1.toSolid3D floor1_proper) :=
  innerVault.rcc8_holds floor1 innerVault_proper floor1_proper

end Geospatial.Examples.ThreeSpaces
