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
  (Claim.touches.decide_iff hm).mp (by decide)

theorem intersects_of_borderMatrix : SF.Intersects g h :=
  (Claim.intersects.decide_iff hm).mp (by decide)

theorem not_within_of_borderMatrix : ¬ SF.Within g h :=
  fun hw => absurd ((Claim.within.decide_iff hm).mpr hw) (by decide)

theorem not_disjoint_of_borderMatrix : ¬ SF.Disjoint g h :=
  fun hd => absurd ((Claim.disjoint.decide_iff hm).mpr hd) (by decide)

end Geospatial.Examples.Prover
