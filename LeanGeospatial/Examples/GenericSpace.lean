import LeanGeospatial.CompositionTable
import LeanGeospatial.Homeomorph
import LeanGeospatial.Examples.Touches

/-!
# Areas and RCC8 beyond the plane

`RegularClosedRegion α` and the RCC8 relations are defined for any
topological space `α`. Three spaces other than the plane show what carries
over and what does not.

- On the real line, `[0, 1]` and `[1, 2]` are externally connected, and
  exactly one RCC8 relation holds between them, by the same theorem as in the
  plane.
- In a discrete space every set is open, so an area has no boundary: no two
  areas are ever `EC`, and none is ever a `TPP` of another. The composition
  table is still sound there (`mem_table_of_mem_compose` holds in every
  space), but it is no longer complete: `DC ⋄ DC` in `Bool` misses `EC`, which
  the plane realises. In the terms of `RCC8Complete`, the plane and `ℝ × ℝ`
  are complete and `Bool` is not.
- A homeomorphism between two different spaces carries areas and their RCC8
  relations across. `Point2D.homeomorphProd` takes the touching squares of
  `Examples.Touches` into `ℝ × ℝ`, where they still touch.
-/

namespace Geospatial.Examples.GenericSpace

open Geospatial Geospatial.RCC8

/-! ## The real line -/

/-- `[0, 1]` as an area of the line. -/
def unitLeft : RegularClosedRegion ℝ :=
  ⟨Set.Icc 0 1, by rw [interior_Icc, closure_Ioo zero_ne_one]⟩

/-- `[1, 2]` as an area of the line. -/
def unitRight : RegularClosedRegion ℝ :=
  ⟨Set.Icc 1 2, by rw [interior_Icc, closure_Ioo (by norm_num)]⟩

theorem unitLeft_nonempty : (unitLeft : Set ℝ).Nonempty := ⟨0, by norm_num [unitLeft]⟩

theorem unitRight_nonempty : (unitRight : Set ℝ).Nonempty := ⟨1, by norm_num [unitRight]⟩

/-- The two intervals share the point `1` and no interior point. -/
theorem line_ec : EC unitLeft unitRight := by
  refine ⟨⟨1, by norm_num [unitLeft], by norm_num [unitRight]⟩, ?_⟩
  show interior (Set.Icc (0 : ℝ) 1) ∩ interior (Set.Icc 1 2) = ∅
  rw [interior_Icc, interior_Icc, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨-, h₁⟩, ⟨h₂, -⟩⟩
  linarith

/-- Exactly one relation holds, and it is `EC`, by the theorem that also
serves the plane. -/
theorem line_only_ec (r : Relation) : r.holds unitLeft unitRight ↔ r = .ec := by
  constructor
  · intro h
    exact relation_unique unitLeft unitRight unitLeft_nonempty unitRight_nonempty h line_ec
  · rintro rfl
    exact line_ec

/-! ## Discrete spaces

`RCC8.not_ec_of_discrete` and `RCC8.not_tpp_of_discrete`: in a discrete space
every set is open, so no two areas are `EC` and none is a `TPP` of another.
-/

/-- `EC` is in no weak composition over `Bool`. -/
theorem ec_not_mem_compose_bool (r s : Relation) : Relation.ec ∉ compose Bool r s :=
  fun ⟨A, _, C, _, _, _, _, _, h⟩ => not_ec_of_discrete A C h

/-- The table is sound over `Bool`, as over every space. -/
example {r s t : Relation} (h : t ∈ compose Bool r s) : t ∈ table r s :=
  mem_table_of_mem_compose h

/-- It is not complete over `Bool`: `EC` is in the table's `DC ⋄ DC`, which the
plane realises, but not in `Bool`'s. -/
theorem table_not_complete_bool : ∃ r s t, t ∈ table r s ∧ t ∉ compose Bool r s :=
  ⟨.dc, .dc, .ec, by decide, ec_not_mem_compose_bool _ _⟩

/-! ## From the plane to `ℝ × ℝ` -/

/-- The touching squares, carried into `ℝ × ℝ`, are still externally
connected. -/
theorem squares_ec_in_prod :
    EC (Touches.areaA.map Point2D.homeomorphProd) (Touches.areaB.map Point2D.homeomorphProd) :=
  (ec_map_iff Point2D.homeomorphProd _ _).mpr Touches.areaA_touches_areaB

/-! ## Which spaces the table is complete for -/

/-- The plane: every entry of the table is realised. -/
example : RCC8Complete Point2D := rcc8Complete_point2D

/-- `ℝ × ℝ` is homeomorphic to the plane, so the table is complete there too. -/
example : RCC8Complete (ℝ × ℝ) := rcc8Complete_point2D.of_homeomorph Point2D.homeomorphProd

/-- `Bool`, like every discrete space, is not. -/
example : ¬ RCC8Complete Bool := not_rcc8Complete_of_discrete Bool

end Geospatial.Examples.GenericSpace
