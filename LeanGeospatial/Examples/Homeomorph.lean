import LeanGeospatial.Homeomorph
import LeanGeospatial.Examples.RCC8

/-!
# Moving the example areas

The areas of `Examples.Touches` and `Examples.RCC8` keep all their relations
when the plane is moved. Two homeomorphisms serve as instances: `slide`
translates the plane ten units along x, and `flip` reflects it through the
origin. Nothing here is computed for the moved areas; each fact follows from
the fact before the move and one theorem of `Homeomorph.lean`.
-/

namespace Geospatial.Examples.Homeomorph

open Geospatial Geospatial.RCC8 Geospatial.DE9IM
open Geospatial.Examples.Touches Geospatial.Examples.RCC8

noncomputable section

/-- Sliding the plane ten units along x. -/
def slide : Point2D ≃ₜ Point2D := Homeomorph.addRight (Point2D.mk 10 0)

/-- Reflecting the plane through the origin. -/
def flip : Point2D ≃ₜ Point2D := Homeomorph.neg Point2D

/-! ## Touches -/

/-- Whatever homeomorphism carries A and B, the images touch. -/
theorem map_areaA_touches_map_areaB (e : Point2D ≃ₜ Point2D) :
    Touches (areaA.map e : Region) (areaB.map e) :=
  (RegularClosedRegion.touches_map_iff e areaA areaB).mpr areaA_touches_areaB

theorem slid_squares_touch : Touches (areaA.map slide : Region) (areaB.map slide) :=
  map_areaA_touches_map_areaB slide

/-! ## RCC8 -/

/-- The square T stays a tangential proper part of A after the reflection. -/
theorem flipped_T_A_tpp : TPP (areaT.map flip) (areaA.map flip) :=
  (tpp_map_iff flip areaT areaA).mpr T_A_tpp

/-- After any homeomorphism, A and C still partially overlap, and no other RCC8
relation holds between them. -/
theorem map_A_C_only_po (e : Point2D ≃ₜ Point2D) (r : Relation) :
    r.holds (areaA.map e) (areaC.map e) ↔ r = .po :=
  (Relation.holds_map_iff e areaA areaC r).trans (A_C_only_po r)

/-! ## DE-9IM -/

/-- The DE-9IM matrix of the slid squares is the matrix of the squares. -/
theorem slid_matrix (s t : Stratum) :
    matrix (.area (areaA.map slide)) (.area (areaB.map slide)) s t =
      matrix (.area areaA) (.area areaB) s t :=
  matrix_map slide areaA areaB s t

end

end Geospatial.Examples.Homeomorph
