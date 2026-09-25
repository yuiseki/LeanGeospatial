import LeanGeospatial.Region

/-!
# Nested administrative areas

We never load the boundaries of District A, City B or Province C. The two
containment facts are assumptions about external data (a gazetteer, a census
boundary file, a human statement). Lean checks only the reasoning step from
them to the conclusion, and that step is the general `within_trans`.
-/

namespace Geospatial.Examples.Administrative

open Geospatial

variable (DistrictA CityB ProvinceC : Region)

/-- District A within City B, City B within Province C, therefore District A
within Province C. -/
theorem districtA_within_provinceC
    (hDistrictCity : Within DistrictA CityB)
    (hCityProvince : Within CityB ProvinceC) :
    Within DistrictA ProvinceC :=
  within_trans hDistrictCity hCityProvince

/-- The same fact read the other way round. -/
theorem provinceC_contains_districtA
    (hDistrictCity : Within DistrictA CityB)
    (hCityProvince : Within CityB ProvinceC) :
    Contains ProvinceC DistrictA :=
  contains_iff_within.mpr (within_trans hDistrictCity hCityProvince)

/-- Any place located in District A is located in Province C. -/
theorem place_in_provinceC (p : Point2D)
    (hDistrictCity : Within DistrictA CityB)
    (hCityProvince : Within CityB ProvinceC)
    (hp : p ∈ DistrictA) :
    p ∈ ProvinceC :=
  (within_trans hDistrictCity hCityProvince).mem hp

/-- If another district D lies in a province disjoint from Province C, it cannot
share a point with District A. -/
theorem districts_in_disjoint_provinces (DistrictD ProvinceE : Region)
    (hDistrictCity : Within DistrictA CityB)
    (hCityProvince : Within CityB ProvinceC)
    (hDistrictD : Within DistrictD ProvinceE)
    (hProvinces : Geospatial.Disjoint ProvinceC ProvinceE) :
    ¬ Intersects DistrictA DistrictD := by
  intro h
  have h₁ : Intersects ProvinceC DistrictD :=
    h.mono_left (within_trans hDistrictCity hCityProvince)
  exact hProvinces.not_intersects (h₁.mono_right hDistrictD)

end Geospatial.Examples.Administrative
