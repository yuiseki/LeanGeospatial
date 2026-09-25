import LeanGeospatial.Prover.DE9IMClaim

/-!
# What a prover answer means

The prover's DE-9IM answers come from `Claim.decide`. For the matrix GEOS
reports for two Tokyo wards sharing a border, `FF2F11212`, these theorems
spell out what `entailed` and `refuted` mean: any two points, lines or
areas with that matrix touch, intersect, and are not within one another.
They say nothing about whether the matrix is right for the wards; that is
the premise.
-/

namespace Geospatial.Examples.Prover

open Geospatial DE9IM Prover

/-- `FF2F11212`. -/
def borderMatrix : Matrix9 := ⟨.F, .F, .d2, .F, .d1, .d1, .d2, .d1, .d2⟩

theorem borderMatrix_parse : Matrix9.ofString? "FF2F11212" = some borderMatrix := by decide

variable {g h : Geometry} (hm : Matrix9.of g h = borderMatrix)
include hm

theorem touches_of_borderMatrix : SF.Touches g h :=
  (Claim.touches.decide_iff_of_kindFree rfl .A .A hm).mp (by decide)

theorem intersects_of_borderMatrix : SF.Intersects g h :=
  (Claim.intersects.decide_iff_of_kindFree rfl .A .A hm).mp (by decide)

theorem not_within_of_borderMatrix : ¬ SF.Within g h :=
  fun hw => absurd ((Claim.within.decide_iff_of_kindFree rfl .A .A hm).mpr hw) (by decide)

theorem not_disjoint_of_borderMatrix : ¬ SF.Disjoint g h :=
  fun hd => absurd ((Claim.disjoint.decide_iff_of_kindFree rfl .A .A hm).mpr hd) (by decide)

omit hm

/-! ## Equals, overlaps and crosses -/

/-- `0FFFFFFF2`, what GEOS reports for a point and itself. -/
def samePointMatrix : Matrix9 := ⟨.d0, .F, .F, .F, .F, .F, .F, .F, .d2⟩

/-- A point with that matrix equals the other geometry, although Table 2's
`TFFFTFFFT` fails on it. -/
theorem equals_of_samePointMatrix {g h : Geometry} (hm : Matrix9.of g h = samePointMatrix) :
    SF.Equals g h :=
  (Claim.equals.decide_iff_of_kindFree rfl .P .P hm).mp (by decide)

/-- `0F1FF0102`: two lines crossing in a point. -/
def crossingMatrix : Matrix9 := ⟨.d0, .F, .d1, .F, .F, .d0, .d1, .d0, .d2⟩

/-- `1010F0102`: two collinear lines overlapping along a stretch. -/
def collinearMatrix : Matrix9 := ⟨.d1, .d0, .d1, .d0, .F, .d0, .d1, .d0, .d2⟩

section Lines

variable {g h : Geometry} (hg : g.kind = .L) (hh : h.kind = .L)
include hg hh

theorem crosses_of_crossingMatrix (hm : Matrix9.of g h = crossingMatrix) : SF.Crosses g h :=
  (Claim.crosses.decide_iff hg hh hm).mp (by decide)

theorem not_overlaps_of_crossingMatrix (hm : Matrix9.of g h = crossingMatrix) :
    ¬ SF.Overlaps g h :=
  fun ho => absurd ((Claim.overlaps.decide_iff hg hh hm).mpr ho) (by decide)

theorem overlaps_of_collinearMatrix (hm : Matrix9.of g h = collinearMatrix) : SF.Overlaps g h :=
  (Claim.overlaps.decide_iff hg hh hm).mp (by decide)

theorem not_crosses_of_collinearMatrix (hm : Matrix9.of g h = collinearMatrix) :
    ¬ SF.Crosses g h :=
  fun hc => absurd ((Claim.crosses.decide_iff hg hh hm).mpr hc) (by decide)

end Lines

end Geospatial.Examples.Prover
