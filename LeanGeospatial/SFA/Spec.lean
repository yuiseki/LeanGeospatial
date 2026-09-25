import LeanGeospatial.GeoSPARQL.Table2.Spec

/-!
# OGC Simple Feature Access 1.2.1, transcribed for comparison

Source: OGC 06-103r4, "OpenGIS Implementation Standard for Geographic
information - Simple feature access - Part 1: Common architecture",
version 1.2.1, 2011-05-28, clause 6.1.15, from
<https://docs.ogc.org/is/06-103r4/06-103r4.pdf> (SHA-256
`4e64b5a22815a680e24c8d07af5d86df3abebc0b9bb7f40939a0c539dd3d56a9`),
fetched 2026-09-25.

Clause 6.1.15.3 gives each named predicate twice: as a statement about point
sets, and "expressed in terms of the DE-9IM" as a pattern. Both are
transcribed here as printed, separately: `SFA.Equals` and friends are the
point-set statements, `SFA.pattern` the patterns. Nothing in LeanGeospatial
is defined from them; `SFA/Compare.lean` compares them with the definitions
of `SimpleFeatures.lean`, with each other, and with GeoSPARQL Table 2.

Clause 6.1.15.1 on the strata, which `Geometry.lean` follows: the boundary of
a Point is empty; of a non-closed Curve its two end points; of a closed
Curve empty; of a Polygon its rings. "The interior of a geometric object
consists of those Points that are left when the boundary Points are removed.
The exterior of a geometric object consists of Points not in the interior or
boundary."
-/

namespace Geospatial.SFA

open Geospatial DE9IM GeoSPARQL.Table2

variable (a b : Geometry)

/-- The interiors' intersection `I(a) ∩ I(b)`. -/
noncomputable abbrev II : Region := Geometry.cell .I .I a b

/-- "a.Equals(b) ⇔ a ⊆ b ∧ b ⊆ a" -/
def Equals : Prop := a.carrier ⊆ b.carrier ∧ b.carrier ⊆ a.carrier

/-- "a.Disjoint(b) ⇔ a ∩ b = ∅" -/
def Disjoint : Prop := a.carrier ∩ b.carrier = ∅

/-- "a.Touch(b) ⇔ (I(a)∩I(b)=∅)∧(a∩b)≠∅" -/
def Touches : Prop := II a b = ∅ ∧ a.carrier ∩ b.carrier ≠ ∅

/-- "a.Cross(b) ⇔ [I(a)∩I(b)≠∅ ∧ (a ∩ b ≠a) ∧ (a ∩ b ≠b)]", with the note
"Previous definition had an unnecessary statement on dimension which was
always true." -/
def Crosses : Prop :=
  II a b ≠ ∅ ∧ a.carrier ∩ b.carrier ≠ a.carrier ∧ a.carrier ∩ b.carrier ≠ b.carrier

/-- "a.Within(b) ⇔ (a∩b=a) ∧ (I(a)∩E(b)=∅)" -/
def Within : Prop := a.carrier ∩ b.carrier = a.carrier ∧ Geometry.cell .I .E a b = ∅

/-- "a.Overlaps(b) ⇔ ( dim(I(a)) = dim(I(b)) = dim(I(a) ∩ I(b))) ∧ (a ∩ b ≠ a) ∧
(a ∩ b ≠ b)" -/
def Overlaps : Prop :=
  DimValue.of (a.stratum .I) = DimValue.of (b.stratum .I) ∧
  DimValue.of (b.stratum .I) = DimValue.of (II a b) ∧
  a.carrier ∩ b.carrier ≠ a.carrier ∧ a.carrier ∩ b.carrier ≠ b.carrier

/-- "a.Contains(b) ⇔ b.Within(a)" -/
def Contains : Prop := Within b a

/-- "a.Intersects(b) ⇔ ! a.Disjoint(b)" -/
def Intersects : Prop := ¬ Disjoint a b

/-- The DE-9IM patterns of clause 6.1.15.3, as printed, where a pattern is
given (`intersects` and `contains` are defined from other predicates). -/
def pattern : Rel → Kind → Kind → Option (List String)
  | .equals, _, _ => some ["TFFFTFFFT"]
  | .disjoint, _, _ => some ["FF*FF****"]
  | .touches, .P, .P => none
  | .touches, _, _ => some ["FT*******", "F**T*****", "F***T****"]
  | .crosses, .P, .L => some ["T*T******"]
  | .crosses, .P, .A => some ["T*T******"]
  | .crosses, .L, .A => some ["T*T******"]
  | .crosses, .L, .L => some ["0********"]
  | .crosses, _, _ => none
  | .within, _, _ => some ["T*F**F***"]
  | .overlaps, .P, .P => some ["T*T***T**"]
  | .overlaps, .A, .A => some ["T*T***T**"]
  | .overlaps, .L, .L => some ["1*T***T**"]
  | .overlaps, _, _ => none
  | .intersects, _, _ => none
  | .contains, _, _ => none

end Geospatial.SFA
