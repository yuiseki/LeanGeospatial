import LeanGeospatial.DE9IM.Values

/-!
# The Simple Features relations, defined from point sets

The eight named relations, for points, line strings and areas, defined from
the geometries' point sets, their Simple Features interiors, and the
dimension values of `DE9IM/Dimension.lean`. They follow the point-set
definitions of the Simple Features model. No DE-9IM pattern is used:
`GeoSPARQL/Table2.lean` compares the patterns with these definitions.

| Relation | Definition |
| --- | --- |
| `Equals` | same points |
| `Disjoint` | no common point |
| `Intersects` | a common point |
| `Touches` | a common point, but no common interior point |
| `Within` | inside, sharing an interior point |
| `Contains` | the other is `Within` |
| `Overlaps` | interiors of equal dimension meeting in that dimension, neither inside the other |
| `Crosses` | interiors meeting in a lower dimension than the larger one, neither inside the other |
-/

namespace Geospatial.SF

open Geospatial DE9IM

/-- Dimension values as numbers, with `F` below `0`. -/
def rank : DimValue → ℤ
  | .F => -1
  | .d0 => 0
  | .d1 => 1
  | .d2 => 2

variable (g h : Geometry)

/-- The interiors' intersection. -/
noncomputable abbrev II : Region := Geometry.cell .I .I g h

def Equals : Prop := g.carrier = h.carrier

def Disjoint : Prop := g.carrier ∩ h.carrier = ∅

def Intersects : Prop := (g.carrier ∩ h.carrier).Nonempty

def Touches : Prop := Intersects g h ∧ II g h = ∅

def Within : Prop := g.carrier ⊆ h.carrier ∧ (II g h).Nonempty

def Contains : Prop := Within h g

def Overlaps : Prop :=
  DimValue.of (g.stratum .I) = DimValue.of (h.stratum .I) ∧
  DimValue.of (II g h) = DimValue.of (g.stratum .I) ∧
  ¬ g.carrier ⊆ h.carrier ∧ ¬ h.carrier ⊆ g.carrier

def Crosses : Prop :=
  (II g h).Nonempty ∧
  rank (DimValue.of (II g h)) <
    max (rank (DimValue.of (g.stratum .I))) (rank (DimValue.of (h.stratum .I))) ∧
  ¬ g.carrier ⊆ h.carrier ∧ ¬ h.carrier ⊆ g.carrier

end Geospatial.SF
