import LeanGeospatial
import LeanGeospatial.Examples.Administrative
import LeanGeospatial.Examples.Intersects
import LeanGeospatial.Examples.Measurement
import LeanGeospatial.Examples.Touches
import LeanGeospatial.RegularClosed
import LeanGeospatial.NineIntersection
import LeanGeospatial.Examples.NineIntersection
import LeanGeospatial.RCC8
import LeanGeospatial.Examples.RCC8
import LeanGeospatial.Composition
import LeanGeospatial.CompositionTable.Cells
import LeanGeospatial.Examples.PublishedTable
import LeanGeospatial.Examples.Validator
import LeanGeospatial.GeoSPARQL.Counterexamples
import LeanGeospatial.Examples.DimensionalCells
import LeanGeospatial.GeoSPARQL.Table2.Counterexamples
import LeanGeospatial.SFA.Compare
import LeanGeospatial.Examples.Prover

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

/-- info: 'Geospatial.RCC8.existsUnique_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.existsUnique_relation

/-- info: 'Geospatial.RCC8.pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.pairwise_disjoint

/-- info: 'Geospatial.RCC8.jointly_exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.jointly_exhaustive

/-- info: 'Geospatial.RCC8.Relation.holds_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.Relation.holds_converse

/-- info: 'Geospatial.RCC8.po_iff_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.po_iff_cells

/-- info: 'Geospatial.RCC8.not_within_iff_IE_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.not_within_iff_IE_nonempty

/-- info: 'Geospatial.Examples.RCC8.T_A_only_tpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.RCC8.T_A_only_tpp

/-- info: 'Geospatial.Examples.RCC8.N_A_ntpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.RCC8.N_A_ntpp

/-- info: 'Geospatial.Examples.RCC8.A_C_only_po' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.RCC8.A_C_only_po

/-- info: 'Geospatial.RCC8.mem_compose_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.mem_compose_converse

/-- info: 'Geospatial.RCC8.compose_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.compose_converse

/-- info: 'Geospatial.RCC8.Relation.realizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.Relation.realizable

/-- info: 'Geospatial.RCC8.eq_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.eq_compose

/-- info: 'Geospatial.RCC8.compose_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.compose_eq

/-- info: 'Geospatial.RCC8.ntpp_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.ntpp_trans

/-- info: 'Geospatial.RCC8.ntpp_compose_ntpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.ntpp_compose_ntpp

/-- info: 'Geospatial.RCC8.ntppi_compose_ntppi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.ntppi_compose_ntppi

/-- info: 'Geospatial.RCC8.schema_sigOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.schema_sigOf

/-- info: 'Geospatial.RCC8.sigOf_mem_sigs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.sigOf_mem_sigs

/-- info: 'Geospatial.RCC8.mem_table_of_mem_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.mem_table_of_mem_compose

/-- info: 'Geospatial.RCC8.realizes_of_mem_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.realizes_of_mem_table

/-- info: 'Geospatial.RCC8.compose_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.compose_eq_table

/-- info: 'Geospatial.RCC8.compose_dc_dc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.compose_dc_dc

/-- info: 'Geospatial.RCC8.compose_ec_ec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.compose_ec_ec

/-- info: 'Geospatial.RCC8.compose_ec_ntpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.compose_ec_ntpp

/-- info: 'Geospatial.RCC8.compose_tppi_tpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.compose_tppi_tpp

/-- info: 'Geospatial.RCC8.compose_ntpp_ntppi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.compose_ntpp_ntppi

/-- info: 'Geospatial.Examples.PublishedTable.table_eq_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.PublishedTable.table_eq_published

/-- info: 'Geospatial.RCC8.Graph.check_contradictory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.Graph.check_contradictory

/-- info: 'Geospatial.RCC8.Graph.check_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.Graph.check_entailed

/-- info: 'Geospatial.RCC8.Graph.check_possible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.Graph.check_possible

/-- info: 'Geospatial.RCC8.triangle_realizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.triangle_realizes

/-- info: 'Geospatial.Examples.Validator.nested_entails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Validator.nested_entails

/-- info: 'Geospatial.Examples.Validator.touching_possible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Validator.touching_possible

/-- info: 'Geospatial.Examples.Validator.touching_each_occurs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Validator.touching_each_occurs

/-- info: 'Geospatial.Examples.Validator.inconsistent_has_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Validator.inconsistent_has_no_model

/-- info: 'Geospatial.GeoSPARQL.holds_of_rcc8Pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.holds_of_rcc8Pattern

/-- info: 'Geospatial.GeoSPARQL.rcc8Pattern_of_dc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.rcc8Pattern_of_dc

/-- info: 'Geospatial.GeoSPARQL.rcc8Pattern_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.rcc8Pattern_of_eq

/-- info: 'Geospatial.GeoSPARQL.rcc8Pattern_of_ntpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.rcc8Pattern_of_ntpp

/-- info: 'Geospatial.GeoSPARQL.rcc8Pattern_of_ntppi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.rcc8Pattern_of_ntppi

/-- info: 'Geospatial.GeoSPARQL.table5_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.table5_row

/-- info: 'Geospatial.GeoSPARQL.table5_within_row_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.table5_within_row_fails

/-- info: 'Geospatial.GeoSPARQL.table5_contains_row_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.table5_contains_row_fails

/-- info: 'Geospatial.GeoSPARQL.sf_intersects_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.sf_intersects_pattern

/-- info: 'Geospatial.GeoSPARQL.sf_intersects_table6_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.sf_intersects_table6_pattern

/-- info: 'Geospatial.GeoSPARQL.sf_within_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.sf_within_pattern

/-- info: 'Geospatial.GeoSPARQL.sf_overlaps_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.sf_overlaps_pattern

/-- info: 'Geospatial.GeoSPARQL.Counterexamples.ec_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Counterexamples.ec_counterexample

/-- info: 'Geospatial.GeoSPARQL.Counterexamples.po_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Counterexamples.po_counterexample

/-- info: 'Geospatial.GeoSPARQL.Counterexamples.tpp_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Counterexamples.tpp_counterexample

/-- info: 'Geospatial.GeoSPARQL.Counterexamples.eq_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Counterexamples.eq_counterexample

/-- info: 'Geospatial.Geometry.existsUnique_stratum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Geometry.existsUnique_stratum

/-- info: 'Geospatial.point_boundary_ne_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.point_boundary_ne_frontier

/-- info: 'Geospatial.DE9IM.existsUnique_describes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.DE9IM.existsUnique_describes

/-- info: 'Geospatial.DE9IM.Pattern.toDim_matches_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.DE9IM.Pattern.toDim_matches_area

/-- info: 'Geospatial.DE9IM.point_cell_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.DE9IM.point_cell_value

/-- info: 'Geospatial.DE9IM.area_II_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.DE9IM.area_II_value

/-- info: 'Geospatial.Examples.DimensionalCells.crossing_II' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.DimensionalCells.crossing_II

/-- info: 'Geospatial.Examples.DimensionalCells.collinear_II' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.DimensionalCells.collinear_II

/-- info: 'Geospatial.Examples.DimensionalCells.squares_II' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.DimensionalCells.squares_II

/-- info: 'Geospatial.Examples.DimensionalCells.point_point_II' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.DimensionalCells.point_point_II

/-- info: 'Geospatial.DE9IM.point_value_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.DE9IM.point_value_right

/-- info: 'Geospatial.DE9IM.line_value_left_ne_d2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.DE9IM.line_value_left_ne_d2

/-- info: 'Geospatial.DE9IM.line_value_right_ne_d2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.DE9IM.line_value_right_ne_d2

/-- info: 'Geospatial.DE9IM.line_line_II_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.DE9IM.line_line_II_cases

/-- info: 'Geospatial.Geometry.not_subset_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Geometry.not_subset_iff

/-- info: 'Geospatial.GeoSPARQL.Table2.disjoint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.disjoint_iff

/-- info: 'Geospatial.GeoSPARQL.Table2.intersects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.intersects_iff

/-- info: 'Geospatial.GeoSPARQL.Table2.touches_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.touches_iff

/-- info: 'Geospatial.GeoSPARQL.Table2.within_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.within_iff

/-- info: 'Geospatial.GeoSPARQL.Table2.contains_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.contains_iff

/-- info: 'Geospatial.GeoSPARQL.Table2.equals_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.equals_of_holds

/-- info: 'Geospatial.GeoSPARQL.Table2.overlaps_area_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.overlaps_area_area

/-- info: 'Geospatial.GeoSPARQL.Table2.overlaps_line_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.overlaps_line_line

/-- info: 'Geospatial.GeoSPARQL.Table2.overlaps_point_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.overlaps_point_point

/-- info: 'Geospatial.GeoSPARQL.Table2.crosses_line_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.crosses_line_line

/-- info: 'Geospatial.GeoSPARQL.Table2.crosses_line_line_table6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.crosses_line_line_table6

/-- info: 'Geospatial.GeoSPARQL.Table2.crosses_line_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.crosses_line_area

/-- info: 'Geospatial.GeoSPARQL.Table2.crosses_point_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.crosses_point_line

/-- info: 'Geospatial.GeoSPARQL.Table2.crosses_point_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.crosses_point_area

/-- info: 'Geospatial.GeoSPARQL.Table2.equals_iff_of_kind_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.equals_iff_of_kind_ne

/-- info: 'Geospatial.GeoSPARQL.Table2.point_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.point_counterexample

/-- info: 'Geospatial.GeoSPARQL.Table2.ring_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.ring_counterexample

/-- info: 'Geospatial.GeoSPARQL.Table2.backtrack_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.backtrack_counterexample

/-- info: 'Geospatial.GeoSPARQL.Table2.equals_area_area_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.equals_area_area_iff

/-- info: 'Geospatial.GeoSPARQL.Table2.univ_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.GeoSPARQL.Table2.univ_counterexample

/-- info: 'Geospatial.SFA.interior_eq_carrier_diff_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.interior_eq_carrier_diff_boundary

/-- info: 'Geospatial.SFA.exterior_eq_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.exterior_eq_compl

/-- info: 'Geospatial.SFA.equals_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.equals_iff

/-- info: 'Geospatial.SFA.intersects_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.intersects_iff

/-- info: 'Geospatial.SFA.touches_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.touches_iff

/-- info: 'Geospatial.SFA.overlaps_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.overlaps_iff

/-- info: 'Geospatial.SFA.within_of_sf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.within_of_sf

/-- info: 'Geospatial.SFA.crosses_of_sf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.crosses_of_sf

/-- info: 'Geospatial.SFA.crosses_line_area_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.crosses_line_area_iff

/-- info: 'Geospatial.SFA.within_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.within_counterexample

/-- info: 'Geospatial.SFA.crosses_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.crosses_counterexample

/-- info: 'Geospatial.SFA.sfa_equals_inconsistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.sfa_equals_inconsistent

/-- info: 'Geospatial.SFA.sfa_within_inconsistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.sfa_within_inconsistent

/-- info: 'Geospatial.SFA.sfa_crosses_inconsistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.sfa_crosses_inconsistent

/-- info: 'Geospatial.SFA.crosses_line_area_patterns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.crosses_line_area_patterns

/-- info: 'Geospatial.SFA.equals_iff_jtsEquals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.equals_iff_jtsEquals

/-- info: 'Geospatial.SFA.sfaEquals_iff_jtsEquals_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.SFA.sfaEquals_iff_jtsEquals_and

/-- info: 'Geospatial.Prover.Claim.decide_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Prover.Claim.decide_iff

/-- info: 'Geospatial.Prover.Claim.holds_iff_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Prover.Claim.holds_iff_rows

/-- info: 'Geospatial.DE9IM.DimPattern.acceptsB_of_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.DE9IM.DimPattern.acceptsB_of_iff

/-- info: 'Geospatial.Examples.Prover.touches_of_borderMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Prover.touches_of_borderMatrix

/-- info: 'Geospatial.Examples.Prover.not_within_of_borderMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Prover.not_within_of_borderMatrix

/-- info: 'Geospatial.RCC8.Graph.mem_stated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.Graph.mem_stated

/-- info: 'Geospatial.RCC8.Graph.no_model_of_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.Graph.no_model_of_conflict

/-- info: 'Geospatial.RCC8.Graph.mem_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.RCC8.Graph.mem_allowed

/-- info: 'Geospatial.Examples.Validator.direct_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Validator.direct_verdict

/-- info: 'Geospatial.Examples.Validator.conflicting_has_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Validator.conflicting_has_no_model

/-- info: 'Geospatial.Examples.Validator.unrelatedConflict_has_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geospatial.Examples.Validator.unrelatedConflict_has_no_model
