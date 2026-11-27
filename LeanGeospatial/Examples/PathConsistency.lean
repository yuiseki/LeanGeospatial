import LeanGeospatial.PathConsistency

/-!
# Multi-hop path consistency examples

Examples where 1-step `Graph.check` / `Graph.checkList` misses constraints over
paths of length 3 or more, whereas `Graph.propagateCheck` infers them and turns
the kernel verdict into a theorem about every planar model.
-/

namespace Geospatial.Examples.PathConsistency

open Geospatial Geospatial.RCC8

/-! ## Case 1: Three-hop administrative nesting -/

/-- A 4-node nesting chain: Ward < District < City < Prefecture. -/
def hierarchy4 : Graph :=
  ⟨[ ⟨"Ward", .ntpp, "District"⟩
   , ⟨"District", .ntpp, "City"⟩
   , ⟨"City", .ntpp, "Prefecture"⟩ ]⟩

/-- One-step `checkList` has no common intermediate node between `Ward` and
`Prefecture`, so it leaves all eight relations open. -/
theorem hierarchy4_oneStep :
    hierarchy4.checkList "Ward" "Prefecture" = .possible Relation.list := by
  decide

/-- Multi-hop path consistency deduces `NTPP`. -/
theorem hierarchy4_propagated :
    hierarchy4.propagateCheck "Ward" "Prefecture" = .entailed .ntpp := by
  decide

/-- Every model satisfies `NTPP (M "Ward") (M "Prefecture")`. -/
theorem hierarchy4_entails (M : FeatureId → RegularClosedRegion Point2D)
    (hM : hierarchy4.Satisfies M) :
    NTPP (M "Ward") (M "Prefecture") :=
  Graph.propagateCheck_entailed hierarchy4_propagated hM

/-! ## Case 2: Four-node cycle contradiction -/

/-- A 4-node cycle: `A ⊂ᵢ B ⊂ᵢ C ⊂ᵢ D` together with `A` disconnected from `D`. -/
def cycle4 : Graph :=
  ⟨[ ⟨"A", .ntpp, "B"⟩
   , ⟨"B", .ntpp, "C"⟩
   , ⟨"C", .ntpp, "D"⟩
   , ⟨"A", .dc, "D"⟩ ]⟩

/-- One-step `checkList` sees no single intermediate contradiction and echoes `.dc`. -/
theorem cycle4_oneStep : cycle4.checkList "A" "D" = .entailed .dc := by
  decide

/-- Multi-hop path consistency detects the 4-cycle contradiction. -/
theorem cycle4_propagated : cycle4.propagateCheck "A" "D" = .contradictory := by
  decide

/-- No assignment of nonempty planar areas satisfies `cycle4`. -/
theorem cycle4_unsatisfiable : ¬ ∃ M, cycle4.Satisfies M :=
  Graph.propagateCheck_contradictory cycle4_propagated

/-! ## Case 3: Mixed indirect propagation (`NTPP ∘ TPP ∘ EC`) -/

/-- Building strictly inside Lot (TPP of Block), and Block touches Road:
Building must be disconnected from Road. -/
def mixed4 : Graph :=
  ⟨[ ⟨"Building", .ntpp, "Lot"⟩
   , ⟨"Lot", .tpp, "Block"⟩
   , ⟨"Block", .ec, "Road"⟩ ]⟩

theorem mixed4_propagated : mixed4.propagateCheck "Building" "Road" = .entailed .dc := by
  decide

theorem mixed4_disjoint (M : FeatureId → RegularClosedRegion Point2D)
    (hM : mixed4.Satisfies M) :
    Disjoint (M "Building" : Region) (M "Road") :=
  (dc_iff_disjoint _ _).mp (Graph.propagateCheck_entailed mixed4_propagated hM)

end Geospatial.Examples.PathConsistency
