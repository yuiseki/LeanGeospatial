import LeanGeospatial.Validator

/-!
# Three validator cases

Each case computes a verdict with `decide` and then turns it into a statement
about every possible model, through the soundness theorems of
`Validator.lean`. The same inputs are in `samples/`, for the command line
tool.
-/

namespace Geospatial.Examples.Validator

open Geospatial Geospatial.RCC8

/-! ## Case 1: the relation is forced -/

/-- District A lies strictly inside City B, and City B strictly inside
Province C. -/
def nested : Graph := ⟨[⟨"DistrictA", .ntpp, "CityB"⟩, ⟨"CityB", .ntpp, "ProvinceC"⟩]⟩

theorem nested_verdict : nested.check "DistrictA" "ProvinceC" = .entailed .ntpp := by
  decide

/-- In every model, District A is a non-tangential proper part of
Province C. -/
theorem nested_entails (M : FeatureId → RegularClosedRegion) (hM : nested.Satisfies M) :
    NTPP (M "DistrictA") (M "ProvinceC") :=
  Graph.check_entailed nested_verdict hM

/-! ## Case 2: several relations remain -/

/-- Parcel A touches road B, and road B touches parcel C. -/
def touching : Graph := ⟨[⟨"ParcelA", .ec, "RoadB"⟩, ⟨"RoadB", .ec, "ParcelC"⟩]⟩

theorem touching_verdict :
    touching.check "ParcelA" "ParcelC" = .possible {.dc, .ec, .po, .eq, .tpp, .tppi} := by
  decide

/-- In every model, parcels A and C are in one of six relations; in
particular they are never `NTPP` or `NTPPi`. -/
theorem touching_possible (M : FeatureId → RegularClosedRegion) (hM : touching.Satisfies M)
    {t : Relation} (ht : t.holds (M "ParcelA") (M "ParcelC")) :
    t ∈ ({.dc, .ec, .po, .eq, .tpp, .tppi} : Finset Relation) :=
  Graph.check_possible touching_verdict hM ht

/-- And each of the six does occur in some model: the list is exact. -/
theorem touching_each_occurs {t : Relation}
    (ht : t ∈ ({.dc, .ec, .po, .eq, .tpp, .tppi} : Finset Relation)) :
    ∃ M, touching.Satisfies M ∧ t.holds (M "ParcelA") (M "ParcelC") := by
  have : t ∈ table .ec .ec := by
    rw [show table .ec .ec = {.dc, .ec, .po, .eq, .tpp, .tppi} by decide]
    exact ht
  exact triangle_realizes (by decide) (by decide) (by decide) this

/-! ## Case 3: the facts contradict each other -/

/-- Building A is strictly inside lot B, lot B strictly inside block C, yet A
is stated to be disconnected from C. -/
def inconsistent : Graph :=
  ⟨[⟨"BuildingA", .ntpp, "LotB"⟩, ⟨"LotB", .ntpp, "BlockC"⟩, ⟨"BuildingA", .dc, "BlockC"⟩]⟩

theorem inconsistent_verdict : inconsistent.check "BuildingA" "BlockC" = .contradictory := by
  decide

/-- No assignment of nonempty areas satisfies these facts. -/
theorem inconsistent_has_no_model : ¬ ∃ M, inconsistent.Satisfies M :=
  Graph.check_contradictory inconsistent_verdict

end Geospatial.Examples.Validator
