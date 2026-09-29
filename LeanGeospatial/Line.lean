import LeanGeospatial.Line.Witnesses
import LeanGeospatial.CompositionTable

/-!
# The RCC8 table is complete on the real line

The line has no room for the plane's rectangles, but it does not need them.
Areas made of unit cells (`Line.area`) realise every entry of the table:
`Line/Witnesses.lean` lists three sets of cells for each entry, and
`lineWitness_ok` checks all 193 of them by `decide`, computing each relation
with `cellRel`. `cellRel_holds` says the computed relation is the one that
holds between the areas, so every entry is realised
(`rcc8Complete_real`).

The witnesses need disconnected areas. With intervals alone the generator
finds no witness for four entries, `EC ⋄ EC ∋ EC`, `EC ⋄ EC ∋ PO`,
`EC ⋄ PO ∋ EC` and `PO ⋄ EC ∋ EC`: three intervals cannot, for instance, touch
one another pairwise. Unions of cells fill those entries. For
`EC ⋄ EC ∋ EC` that intervals cannot do it is a theorem,
`not_ec_triangle_real` in `ConnectedComplete.lean`; for the other three it is
what the search observed up to eight cells.
-/

namespace Geospatial.Line

open Geospatial.RCC8

/-- The witness for `t ∈ r ⋄ s` has three nonempty sets with the right
relations. -/
def WitnessOk (r s t : Relation) : Prop :=
  (lineWitness r s t).1.Nonempty ∧ (lineWitness r s t).2.1.Nonempty ∧
    (lineWitness r s t).2.2.Nonempty ∧
    cellRel (lineWitness r s t).1 (lineWitness r s t).2.1 = r ∧
    cellRel (lineWitness r s t).2.1 (lineWitness r s t).2.2 = s ∧
    cellRel (lineWitness r s t).1 (lineWitness r s t).2.2 = t

instance (r s t : Relation) : Decidable (WitnessOk r s t) := by
  unfold WitnessOk
  infer_instance

/-- Every witness checks out. -/
theorem lineWitness_ok :
    ∀ r ∈ Relation.all, ∀ s ∈ Relation.all, ∀ t ∈ table r s, WitnessOk r s t := by
  decide

end Geospatial.Line

namespace Geospatial

open RCC8 Line

/-- The table is complete for the real line. -/
theorem rcc8Complete_real : RCC8Complete ℝ := by
  refine rcc8Complete_iff_table_subset.mpr fun r s t ht => ?_
  have hok := lineWitness_ok r (Relation.mem_all r) s (Relation.mem_all s) t (Finset.mem_coe.mp ht)
  unfold WitnessOk at hok
  generalize lineWitness r s t = w at hok
  obtain ⟨S, T, U⟩ := w
  obtain ⟨hS, hT, hU, h₁, h₂, h₃⟩ := hok
  exact ⟨area S, area T, area U, area_nonempty hS, area_nonempty hT, area_nonempty hU,
    h₁ ▸ cellRel_holds hS hT, h₂ ▸ cellRel_holds hT hU, h₃ ▸ cellRel_holds hS hU⟩

end Geospatial
