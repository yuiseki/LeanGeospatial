import LeanGeospatial
import LeanGeospatial.Examples.Administrative
import LeanGeospatial.Examples.Intersects
import LeanGeospatial.Examples.Measurement
import LeanGeospatial.Examples.Touches
import LeanGeospatial.RegularClosed
import LeanGeospatial.NineIntersection
import LeanGeospatial.Examples.NineIntersection

/-!
# Axiom audit

Each theorem below may depend only on Lean's three standard axioms. They come
in through Mathlib's construction of the real numbers. If anything in this
project adds an `axiom` or leaves a proof unfinished (which shows up as
`sorryAx`), the expected messages stop matching and `lake build` fails.
-/

/-- info: 'Geospatial.within_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.within_refl

/-- info: 'Geospatial.within_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.within_trans

/-- info: 'Geospatial.contains_iff_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.contains_iff_within

/-- info: 'Geospatial.intersects_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.intersects_symm

/-- info: 'Geospatial.disjoint_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.disjoint_symm

/-- info: 'Geospatial.Disjoint.not_intersects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Disjoint.not_intersects

/-- info: 'Geospatial.intersects_not_transitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.intersects_not_transitive

/-- info: 'Geospatial.Examples.Administrative.districtA_within_provinceC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Administrative.districtA_within_provinceC

/-- info: 'Geospatial.Examples.Intersects.intersects_chain_does_not_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Intersects.intersects_chain_does_not_close

/-- info: 'Geospatial.Examples.Measurement.distance_p1_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Measurement.distance_p1_p2

/-- info: 'Geospatial.Examples.Measurement.area_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Measurement.area_square

/-- info: 'Geospatial.touches_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.touches_symm

/-- info: 'Geospatial.Touches.inter_subset_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Touches.inter_subset_boundary

/-- info: 'Geospatial.Rect.interior_toRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Rect.interior_toRegion

/-- info: 'Geospatial.Rect.boundary_toRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Rect.boundary_toRegion

/-- info: 'Geospatial.Examples.Touches.touches_distinguishes_from_intersects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Touches.touches_distinguishes_from_intersects

/-- info: 'Geospatial.Examples.Touches.intersects_not_imp_touches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Touches.intersects_not_imp_touches

/-- info: 'Geospatial.RegularClosedRegion.inter_subset_boundary_of_touches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RegularClosedRegion.inter_subset_boundary_of_touches

/-- info: 'Geospatial.RegularClosedRegion.union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RegularClosedRegion.union

/-- info: 'Geospatial.Touches.not_exists_regularClosed_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Touches.not_exists_regularClosed_inter

/-- info: 'Geospatial.Rect.closure_interior_toRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Rect.closure_interior_toRegion

/-- info: 'Geospatial.Rect.segment_not_regularClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Rect.segment_not_regularClosed

/-- info: 'Geospatial.Examples.Touches.A_inter_B_subset_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Touches.A_inter_B_subset_boundaries

/-- info: 'Geospatial.Examples.Touches.shared_edge_not_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Touches.shared_edge_not_area

/-- info: 'Geospatial.interior_union_boundary_union_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.interior_union_boundary_union_exterior

/-- info: 'Geospatial.existsUnique_stratum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.existsUnique_stratum

/-- info: 'Geospatial.iUnion_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.iUnion_cell

/-- info: 'Geospatial.cell_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.cell_disjoint

/-- info: 'Geospatial.RegularClosedRegion.disjoint_iff_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RegularClosedRegion.disjoint_iff_cells

/-- info: 'Geospatial.RegularClosedRegion.touches_iff_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RegularClosedRegion.touches_iff_cells

/-- info: 'Geospatial.RegularClosedRegion.within_iff_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RegularClosedRegion.within_iff_cells

/-- info: 'Geospatial.RegularClosedRegion.contains_iff_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RegularClosedRegion.contains_iff_cells

/-- info: 'Geospatial.Examples.NineIntersection.empty_within_but_II_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.NineIntersection.empty_within_but_II_empty

/-- info: 'Geospatial.Examples.NineIntersection.segment_within_but_II_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.NineIntersection.segment_within_but_II_empty
