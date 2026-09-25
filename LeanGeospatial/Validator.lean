import LeanGeospatial.CompositionTable

/-!
# An RCC8 validator

Input: a list of facts `a r b`, where `a` and `b` are feature IDs and `r` is
an RCC8 base relation. A *model* of the facts gives every feature a nonempty
area so that every fact holds.

For a pair of features `a`, `c`, `derived` intersects `table r s` over every
feature `b` with a known relation `r` from `a` to `b` and `s` from `b` to `c`.
`check` then gives one of three verdicts:

| Verdict | Meaning | Theorem |
| --- | --- | --- |
| `entailed t` | only `t` is left | every model has `t` between `a` and `c` (`check_entailed`) |
| `possible S` | several are left | every model has one of `S` (`check_possible`) |
| `contradictory` | nothing is left, or the stated `a c` fact is not among them | no model exists (`check_contradictory`) |

The verdicts rest on `mem_table_of_mem_compose`, the soundness half of the
composition table, and on RCC8's "exactly one relation holds".

`possible` is sound but not always tight: with several intermediate features,
constraints further away could rule out more. For a single triangle it is
tight: every candidate has a model (`triangle_realizes`).
-/

namespace Geospatial.RCC8

open Geospatial

/-- Feature identifiers. -/
abbrev FeatureId := String

/-- A stated relation `a rel b`. -/
structure Fact where
  a : FeatureId
  rel : Relation
  b : FeatureId
  deriving DecidableEq

/-- A set of stated relations. -/
structure Graph where
  facts : List Fact

/-- An assignment of nonempty areas to features that makes every fact true. -/
def Graph.Satisfies (g : Graph) (M : FeatureId → RegularClosedRegion) : Prop :=
  (∀ x, (M x : Region).Nonempty) ∧ ∀ f ∈ g.facts, f.rel.holds (M f.a) (M f.b)

/-! ## Reading the graph -/

/-- The first stated relation from `a` to `b` in a list of facts, using the
converse for a fact stated from `b` to `a`. -/
def lookupFacts : List Fact → FeatureId → FeatureId → Option Relation
  | [], _, _ => none
  | f :: g, a, b =>
    if f.a = a ∧ f.b = b then some f.rel
    else if f.a = b ∧ f.b = a then some f.rel.converse
    else lookupFacts g a b

/-- The stated relation from `a` to `b`. -/
def Graph.lookup (g : Graph) (a b : FeatureId) : Option Relation := lookupFacts g.facts a b

theorem lookupFacts_sound {M : FeatureId → RegularClosedRegion} {g : List Fact}
    (hM : ∀ f ∈ g, f.rel.holds (M f.a) (M f.b)) {a b : FeatureId} {r : Relation}
    (h : lookupFacts g a b = some r) : r.holds (M a) (M b) := by
  induction g with
  | nil => simp [lookupFacts] at h
  | cons f g ih =>
    have hf : f.rel.holds (M f.a) (M f.b) := hM f (List.mem_cons_self _ _)
    have hM' : ∀ f' ∈ g, f'.rel.holds (M f'.a) (M f'.b) :=
      fun f' hf' => hM f' (List.mem_cons_of_mem _ hf')
    simp only [lookupFacts] at h
    split_ifs at h with h₁ h₂
    · obtain ⟨rfl, rfl⟩ := h₁
      cases h
      exact hf
    · obtain ⟨rfl, rfl⟩ := h₂
      cases h
      exact (f.rel.holds_converse _ _).mpr hf
    · exact ih hM' h

theorem Graph.lookup_sound {g : Graph} {M : FeatureId → RegularClosedRegion}
    (hM : g.Satisfies M) {a b : FeatureId} {r : Relation} (h : g.lookup a b = some r) :
    r.holds (M a) (M b) :=
  lookupFacts_sound hM.2 h

/-- Every feature mentioned in the graph. -/
def Graph.features (g : Graph) : List FeatureId :=
  (g.facts.flatMap fun f => [f.a, f.b]).dedup

/-! ## Deriving the allowed relations -/

/-- Intersect `table r s` over the intermediate features `bs`. -/
def Graph.constrain (g : Graph) (a c : FeatureId) : List FeatureId → Finset Relation
  | [] => Relation.all
  | b :: bs =>
    match g.lookup a b, g.lookup b c with
    | some r, some s => Graph.constrain g a c bs ∩ table r s
    | _, _ => Graph.constrain g a c bs

/-- The relations the graph allows from `a` to `c`, through every
intermediate feature. -/
def Graph.derived (g : Graph) (a c : FeatureId) : Finset Relation :=
  g.constrain a c g.features

/-- Whatever relation a model has from `a` to `c` survives every
intermediate feature. -/
theorem Graph.mem_constrain {g : Graph} {M : FeatureId → RegularClosedRegion}
    (hM : g.Satisfies M) {a c : FeatureId} {t : Relation} (ht : t.holds (M a) (M c))
    (bs : List FeatureId) : t ∈ g.constrain a c bs := by
  induction bs with
  | nil => exact Relation.mem_all t
  | cons b bs ih =>
    simp only [Graph.constrain]
    split
    · next r s hr hs =>
      refine Finset.mem_inter.mpr ⟨ih, mem_table_of_mem_compose ?_⟩
      exact ⟨M a, M b, M c, hM.1 a, hM.1 b, hM.1 c,
        Graph.lookup_sound hM hr, Graph.lookup_sound hM hs, ht⟩
    · exact ih

theorem Graph.mem_derived {g : Graph} {M : FeatureId → RegularClosedRegion}
    (hM : g.Satisfies M) {a c : FeatureId} {t : Relation} (ht : t.holds (M a) (M c)) :
    t ∈ g.derived a c :=
  Graph.mem_constrain hM ht _

/-! ## Verdicts -/

/-- The outcome of checking a pair of features. -/
inductive Verdict where
  /-- Exactly one relation is allowed. -/
  | entailed (t : Relation)
  /-- Several relations are allowed. -/
  | possible (S : Finset Relation)
  /-- No relation is allowed, or the stated one is not. -/
  | contradictory
  deriving DecidableEq

/-- The eight relations in a fixed order. -/
def Relation.list : List Relation := [.dc, .ec, .po, .eq, .tpp, .ntpp, .tppi, .ntppi]

theorem Relation.mem_list (t : Relation) : t ∈ Relation.list := by
  cases t <;> decide

/-- The verdict for a set of allowed relations. -/
def verdictOf (S : Finset Relation) : Verdict :=
  match Relation.list.filter (· ∈ S) with
  | [] => .contradictory
  | [t] => .entailed t
  | _ => .possible S

theorem mem_filter_list {S : Finset Relation} {t : Relation} (ht : t ∈ S) :
    t ∈ Relation.list.filter (· ∈ S) :=
  List.mem_filter.mpr ⟨Relation.mem_list t, decide_eq_true ht⟩

theorem not_mem_of_verdictOf_contradictory {S : Finset Relation}
    (h : verdictOf S = .contradictory) (t : Relation) : t ∉ S := by
  intro ht
  have hL := mem_filter_list ht
  unfold verdictOf at h
  split at h
  · next hnil => rw [hnil] at hL; simp at hL
  · simp at h
  · simp at h

theorem eq_of_verdictOf_entailed {S : Finset Relation} {t : Relation}
    (h : verdictOf S = .entailed t) {t' : Relation} (ht' : t' ∈ S) : t' = t := by
  have hL := mem_filter_list ht'
  unfold verdictOf at h
  split at h
  · simp at h
  · next u hone =>
    cases h
    rw [hone] at hL
    exact List.mem_singleton.mp hL
  · simp at h

theorem eq_of_verdictOf_possible {S S' : Finset Relation} (h : verdictOf S = .possible S') :
    S' = S := by
  unfold verdictOf at h
  split at h
  · simp at h
  · simp at h
  · cases h
    rfl

/-- Whether the stated relation from `a` to `c`, if any, is allowed. -/
def Graph.statedOk (g : Graph) (a c : FeatureId) : Bool :=
  match g.lookup a c with
  | some t => decide (t ∈ g.derived a c)
  | none => true

/-- In a model, the stated relation is always allowed. -/
theorem Graph.statedOk_of_model {g : Graph} {M : FeatureId → RegularClosedRegion}
    (hM : g.Satisfies M) (a c : FeatureId) : g.statedOk a c = true := by
  unfold Graph.statedOk
  split
  · next t ht => exact decide_eq_true (Graph.mem_derived hM (Graph.lookup_sound hM ht))
  · rfl

/-- Check the pair `a`, `c`. -/
def Graph.check (g : Graph) (a c : FeatureId) : Verdict :=
  if g.statedOk a c then verdictOf (g.derived a c) else .contradictory

/-- A `contradictory` verdict means the facts have no model. -/
theorem Graph.check_contradictory {g : Graph} {a c : FeatureId}
    (h : g.check a c = .contradictory) : ¬ ∃ M, g.Satisfies M := by
  rintro ⟨M, hM⟩
  obtain ⟨t, ht⟩ := exists_relation (M a) (M c) (hM.1 a) (hM.1 c)
  unfold Graph.check at h
  rw [Graph.statedOk_of_model hM, if_pos rfl] at h
  exact not_mem_of_verdictOf_contradictory h t (Graph.mem_derived hM ht)

/-- An `entailed t` verdict means every model has `t` from `a` to `c`. -/
theorem Graph.check_entailed {g : Graph} {a c : FeatureId} {t : Relation}
    (h : g.check a c = .entailed t) {M : FeatureId → RegularClosedRegion}
    (hM : g.Satisfies M) : t.holds (M a) (M c) := by
  obtain ⟨t₀, ht₀⟩ := exists_relation (M a) (M c) (hM.1 a) (hM.1 c)
  unfold Graph.check at h
  rw [Graph.statedOk_of_model hM, if_pos rfl] at h
  rw [← eq_of_verdictOf_entailed h (Graph.mem_derived hM ht₀)]
  exact ht₀

/-- A `possible S` verdict means every model has one of `S` from `a` to `c`. -/
theorem Graph.check_possible {g : Graph} {a c : FeatureId} {S : Finset Relation}
    (h : g.check a c = .possible S) {M : FeatureId → RegularClosedRegion}
    (hM : g.Satisfies M) {t : Relation} (ht : t.holds (M a) (M c)) : t ∈ S := by
  unfold Graph.check at h
  rw [Graph.statedOk_of_model hM, if_pos rfl] at h
  rw [eq_of_verdictOf_possible h]
  exact Graph.mem_derived hM ht

/-! ## A single triangle is tight -/

/-- For the graph `a r b`, `b s c` with distinct features, every relation in
`table r s` occurs between `a` and `c` in some model. So a `possible`
verdict on a single triangle lists exactly the relations that can occur. -/
theorem triangle_realizes {a b c : FeatureId} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {r s t : Relation} (ht : t ∈ table r s) :
    ∃ M, Graph.Satisfies ⟨[⟨a, r, b⟩, ⟨b, s, c⟩]⟩ M ∧ t.holds (M a) (M c) := by
  obtain ⟨A, B, C, hA, hB, hC, hr, hs, htAC⟩ := realizes_of_mem_table r s t ht
  classical
  let M : FeatureId → RegularClosedRegion := fun x => if x = a then A else if x = b then B else C
  have Ma : M a = A := by simp [M]
  have Mb : M b = B := by simp [M, hab.symm]
  have Mc : M c = C := by simp [M, hac.symm, hbc.symm]
  refine ⟨M, ⟨fun x => ?_, ?_⟩, by rw [Ma, Mc]; exact htAC⟩
  · simp only [M]
    split_ifs
    · exact hA
    · exact hB
    · exact hC
  · intro f hf
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · rw [Ma, Mb]; exact hr
    · rw [Mb, Mc]; exact hs

end Geospatial.RCC8
