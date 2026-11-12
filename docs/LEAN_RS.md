# Toward Rust with lean-rs

This note records which definitions of LeanGeospatial could later be compiled
to Rust with [lean-rs](https://github.com/conao3/lean-rs), which theorems
would then describe the Rust functions, and what stands in the way. Nothing
here is generated or built yet: there is no Rust code in this repository, and
CI does not run lean-rs. The two executables (`lean-geospatial`,
`lean-geospatial-prover`) are compiled by Lean's own C backend, as before.

It was written against lean-rs at commit `90bdd9c` (generator version 3, Lean
`v4.35.0`), from its README and its sources (`LeanRust/Marshal.lean`,
`Main.lean`). lean-rs was not run on this library; every "expected" below is
read from that code, not observed.

## What lean-rs does, and what it guarantees

lean-rs compiles the IR that Lean's compiler produces for a module
(`Lean.Compiler.IR`) to Rust source that mirrors Lean's C backend
(`lean-rust module generate`, or `lean-rust project generate` for a whole
Lake package; `lean!` embeds Lean source in a Rust file). Theorems are not
compiled; they have no IR. What carries over is this: a generated function
computes what the Lean definition computes, so the theorems proved about that
definition describe the values the Rust function returns.

That transfer rests on things Lean does not check:

- lean-rs itself: its translation of the IR and its runtime are tested
  against Lean's C backend, not proved;
- Lean's compiler, as for any compiled Lean code;
- the hypotheses of each theorem, which the Rust caller has to establish;
- any hand-written Rust around the generated code (parsing JSON, calling GEOS).

The trust boundary of this library does not move. `Graph.check` and
`Claim.decide` are proved correct about the facts or the matrix they are
given. Whether those facts or that matrix are true of real geometries is
outside Lean, in Lean and in Rust alike: a Rust program that computes a
DE-9IM matrix with GEOS and passes it to a generated `Claim.decide` gets an
answer that follows from that matrix, not a check of GEOS.

A definition becomes a public Rust function only if every argument and the
result have a Rust type: `Bool` and `Decidable p` (as `bool`), `Nat` and
`Int` (arbitrary precision), fixed-width integers, `Float`, `Char`, `String`,
`List`, `Array`, `Option`, `Except`, products, `Fin n` with `n` reducing to a
literal, and structures and inductive types built from these. lean-rs skips,
with a reason, a definition that has no IR (`noncomputable`), takes a proof
argument, uses a function type, a type variable, `Subtype`, a type family or
a type that is not an inductive (such as `ℝ`, `Set`, `Finset`, whose
`Multiset` is a quotient), or takes an argument whose type has proof fields.
By default it exports the public definitions written in a module, but not
instances.

## Candidates

The decision procedures are already separate from the topology: they work on
enumerations, strings and lists, and theorems relate them to the relations
defined from sets. "As is" means no change to the Lean code is needed.

### DE-9IM claims (`Prover/DE9IMClaim.lean`, `DE9IM/Dimension.lean`, `GeoSPARQL/Table2/Spec.lean`)

| Definition | Expected Rust shape | Theorems that describe it | Status |
| --- | --- | --- | --- |
| `Geospatial.DE9IM.DimValue`, `DimPatternChar` | field-less enums | | as is |
| `Geospatial.DE9IM.DimPattern`, `Geospatial.Prover.Matrix9` | structs of nine enum fields | | as is |
| `Geospatial.GeoSPARQL.Table2.Kind`, `Geospatial.Prover.Claim` | field-less enums | | as is |
| `DimPatternChar.ofChar?`, `DimPattern.ofString?`, `Prover.DimValue.ofChar?`, `Matrix9.ofString?` | `-> Option<...>` | used by the `parse_*` theorems (`decide`) | as is; parsing is unproved beyond those cases |
| `DimPatternChar.acceptsB`, `DimPattern.acceptsB` | `-> bool` | `DimPatternChar.acceptsB_iff`, `DimPattern.acceptsB_of_iff` | as is |
| `Claim.needsKinds`, `Claim.rows`, `Kind.dimValue`, `Matrix9.aEmpty`, `Matrix9.bEmpty`, `interiorValue` | `-> bool`, `-> Vec<DimPattern>`, `-> DimValue` | `Claim.holds_iff_rows`, `equals_iff_rows`, `kind_dimValue`, `aEmpty_of_iff`, `bEmpty_of_iff` | as is |
| `Claim.decide` | `(c: Claim, k: Kind, k2: Kind, m: Matrix9) -> bool` | `Claim.decide_iff` (exact, given `g.kind = k`, `h.kind = k'`, `Matrix9.of g h = m`), `Claim.decide_kinds_irrel`, `Claim.decide_iff_of_kindFree` | as is |
| `Geospatial.SF.rank` | `(v: DimValue) -> Int` | used in `SF.Crosses` and `Claim.decide` | as is |

### RCC8 (`RCC8.lean`, `CompositionTable/Abstract.lean`, `Validator.lean`, `ValidatorText.lean`)

| Definition | Expected Rust shape | Theorems that describe it | Status |
| --- | --- | --- | --- |
| `Geospatial.RCC8.Relation`, `Relation.converse`, `Relation.list` | field-less enum; `-> Relation`; `-> Vec<Relation>` | `Relation.converse_converse`, `Relation.holds_converse`, `Relation.mem_list` | as is |
| `Sig`, `Sig.swap`, `Relation.sigs`, `schema`, `consistent`, `admits` | struct of six `bool`s; `-> bool` | `schema_sigOf`, `consistent_sigOf`, `sigOf_mem_sigs`; `t ∈ table r s` is `admits r s t = true` by the definition of `table`, so `mem_table_of_mem_compose` (sound everywhere) and `compose_eq_table` (exact in the plane) describe it | as is |
| `Fact`, `Graph`, `lookupFacts`, `Graph.lookup`, `Graph.features` | structs of `String`s and `Relation`; `-> Option<Relation>`; `-> Vec<String>` | `lookupFacts_sound`, `Graph.lookup_sound` | as is |
| `Graph.conflict` | `(g: Graph) -> bool` | `Graph.no_model_of_conflict` | as is |
| `Relation.ofString?`, `Relation.name`, `Input`, `Input.parse` | `-> Option<Relation>`, `-> String`, `-> Result<Input, String>` | none (unproved front end) | as is |
| `table`, `Relation.all`, `Graph.constrain`, `Graph.derived`, `statedFacts`, `Graph.stated`, `Graph.allowed`, `verdictOf` | | `mem_table_of_mem_compose`, `Graph.mem_constrain`, `Graph.mem_derived`, `mem_statedFacts`, `Graph.mem_stated`, `Graph.mem_allowed` | blocked: return `Finset Relation` |
| `Verdict`, `Graph.check`, `Verdict.render` | | `Graph.check_entailed`, `Graph.check_possible`, `Graph.check_contradictory`, `triangle_realizes` | blocked: `Verdict.possible` carries a `Finset Relation` |

### Published tables (`GeoSPARQL/Spec.lean`, `GeoSPARQL/Table2/Spec.lean`, `DE9IM.lean`)

`GeoSPARQL.table4`, `table8`, `SF`, `table2`, `table6`, `parseAll`,
`rcc8Pattern`, `Table2.Rel`, `Table2.table2`, `table6CrossesLL`, `parseRows`,
and in `DE9IM.lean` `PatternChar`, `Pattern`, `Pattern.transpose`,
`PatternChar.ofChar?`, `PatternChar.toChar`, `Pattern.ofString?`,
`Pattern.toString`: enumerations, strings and lists, exportable as is. They
are transcriptions of the published tables; the theorems about them
(`table4_eq_table8`, `table2_eq_table6`, `Pattern.matches_transpose`, and the
Table 2 theorems in `GeoSPARQL/Table2/Generic.lean` through `Holds`) say what
the rows mean, not that a Rust program reading them is right about geometry.
`GeoSPARQL.table5` returns a `Finset` and is blocked like `table`.

## Kept out, and why

- Everything defined from sets: `Region`, `RegularClosedRegion` (a structure
  with a proof field), `Geometry`, `LineString`, the relations (`DC` … `NTPPi`,
  `Relation.holds`, `SF.*`, `SFA.*`), `Stratum.set`, `cell`, `compose`,
  `RCC8Complete`, `Pattern.Matches`, `DimValue.Describes`. They are
  propositions or sets over `ℝ` and have no IR.
- `classify`, `sigOf`, `DimValue.of`, `Matrix9.of`, `Geometry.stratum`:
  `noncomputable` (classical choice over sets). They are what makes the
  theorems about real geometries; the computable side takes their values as
  input.
- `Pattern.parse`: takes a proof argument (`(Pattern.ofString? s).isSome =
  true`). `Pattern.ofString?` is the exportable form.
- `Polygon`, `signedArea2`, `polygonArea`, `Rect`, `distance`: over `ℝ`.
  A Rust version in `f64` would not inherit any theorem, and this library
  does not replace `ℝ` by `Float`.
- `ProverJSON.lean` (`handleLine`, `handleRCC8`, `handleDE9IM`): unproved
  glue whose types include `Lean.Json`. A Rust program would parse JSON
  itself and call the proved functions; whether `Lean.Json` crosses lean-rs
  was not checked.

## Why `Finset` stays

`table`, `Graph.allowed` and `Verdict.possible` use `Finset Relation`, and
`check_possible`, `mem_table_of_mem_compose`, `compose_eq_table` and the
completeness results are stated with it. Changing the type to make
`Graph.check` exportable would change those statements, so it was not done.
What is exportable now covers the RCC8 side up to `admits` and `conflict`;
`Graph.check` itself is not. If it is wanted later, the choice is between a
lean-rs that accepts `Finset` (its runtime representation is a list) and a
`List`-valued checker with its own correctness theorems, which is new work.

## Changes made for this

None to the Lean code. The decision procedures were already separate
definitions with their own theorems; nothing in them depends on `ℝ` or on
`noncomputable` definitions.

## Open before starting

- Toolchain. lean-rs is pinned to Lean `v4.35.0`, and `lean-rust` reads the IR
  stored in `.olean` files built by its own Lean version. LeanGeospatial,
  LeanGeodesy and LeanComputationalGeometry are on Lean `v4.34.0` and Mathlib
  `v4.34.0`. Generating Rust needs the three upgraded together (see
  `AGENTS.md`) or a lean-rs for `v4.34.0`; neither was done here.
- Not tried: running `lean-rust module generate` on
  `LeanGeospatial.Prover.DE9IMClaim` and `LeanGeospatial.Validator` with
  `--output json`; whether the runtime has every extern the Mathlib-built IR
  calls (`List.dedup` in `Graph.features`, for example; exit code 254 means
  it does not).
- Each generated module defines its own copies of the types it mentions, so
  `Relation` generated from two modules gives two Rust types unless
  `--type-path` or `uses` links them.
