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

/-! ## Stated facts between the queried pair -/

/-- A fact about the queried pair decides it. -/
def direct : Graph := ⟨[⟨"A", .ntpp, "B"⟩]⟩

theorem direct_verdict : direct.check "A" "B" = .entailed .ntpp := by decide

/-- Stating the same fact twice is no contradiction. -/
def duplicate : Graph := ⟨[⟨"A", .ntpp, "B"⟩, ⟨"A", .ntpp, "B"⟩]⟩

theorem duplicate_verdict : duplicate.check "A" "B" = .entailed .ntpp := by decide

/-- A fact and its converse, stated the other way round, are the same
constraint. -/
def converseEquivalent : Graph := ⟨[⟨"A", .tpp, "B"⟩, ⟨"B", .tppi, "A"⟩]⟩

theorem converseEquivalent_verdict : converseEquivalent.check "A" "B" = .entailed .tpp := by
  decide

/-- Two different relations stated for one pair contradict each other. -/
def conflicting : Graph := ⟨[⟨"A", .dc, "B"⟩, ⟨"A", .eq, "B"⟩]⟩

theorem conflicting_verdict : conflicting.check "A" "B" = .contradictory := by decide

theorem conflicting_has_no_model : ¬ ∃ M, conflicting.Satisfies M :=
  Graph.check_contradictory conflicting_verdict

/-- A contradiction between other features makes every query contradictory:
the graph as a whole has no model. -/
def unrelatedConflict : Graph :=
  ⟨[⟨"A", .ntpp, "B"⟩, ⟨"X", .dc, "Y"⟩, ⟨"X", .eq, "Y"⟩]⟩

theorem unrelatedConflict_verdict : unrelatedConflict.check "A" "B" = .contradictory := by
  decide

theorem unrelatedConflict_has_no_model : ¬ ∃ M, unrelatedConflict.Satisfies M :=
  Graph.check_contradictory unrelatedConflict_verdict

end Geospatial.Examples.Validator
