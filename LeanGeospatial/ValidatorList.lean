import LeanGeospatial.Validator

/-!
# A `List`-valued RCC8 checker

`Graph.check` returns a `Verdict` holding a `Finset Relation`, which lean-rs cannot compile (a `Finset`
holds a `Multiset`, a quotient). This file restates the checker with `Bool` predicates and `List`s only,
and proves it agrees with `Graph.check`:

* `Graph.checkList_toVerdict`: `(g.checkList a c).toVerdict = g.check a c`.

So every theorem about `Graph.check` (`check_entailed`, `check_possible`, `check_contradictory`)
describes `checkList`, and `checkList` can be compiled to Rust. Nothing in `Validator.lean` changes.
-/

namespace Geospatial.RCC8

open Geospatial

/-! ## Membership tests as `Bool` -/

/-- `t` is allowed by the single fact `f`, for the pair `a`, `b` (cf. `statedFacts`). -/
def statedOK (f : Fact) (a b : FeatureId) (t : Relation) : Bool :=
  if f.a = a ∧ f.b = b then decide (t = f.rel)
  else if f.a = b ∧ f.b = a then decide (t = f.rel.converse)
  else true

/-- `t` is allowed by the facts stated between `a` and `b` (cf. `Graph.stated`). -/
def Graph.statedB (g : Graph) (a b : FeatureId) (t : Relation) : Bool :=
  g.facts.all fun f => statedOK f a b t

/-- `t` survives the intermediate feature `b` (cf. `Graph.constrain`). -/
def derivedOK (g : Graph) (a c : FeatureId) (t : Relation) (b : FeatureId) : Bool :=
  match g.lookup a b, g.lookup b c with
  | some r, some s => admits r s t
  | _, _ => true

/-- `t` is allowed between `a` and `c` (cf. `Graph.allowed`). -/
def Graph.allowedB (g : Graph) (a c : FeatureId) (t : Relation) : Bool :=
  (g.features.all fun b => derivedOK g a c t b) && g.statedB a c t

/-- `table r s` as a list, in the order of `Relation.list`. -/
def tableList (r s : Relation) : List Relation := Relation.list.filter fun t => admits r s t

/-- The relations allowed between `a` and `c`, in the order of `Relation.list`. -/
def Graph.allowedList (g : Graph) (a c : FeatureId) : List Relation :=
  Relation.list.filter fun t => g.allowedB a c t

/-- Directly contradicting facts (cf. `Graph.conflict`). -/
def Graph.conflictList (g : Graph) : Bool :=
  g.facts.any fun f => Relation.list.all fun t => !g.statedB f.a f.b t

/-- The outcome of checking a pair, with a list instead of a `Finset`. -/
inductive VerdictL where
  | entailed (t : Relation)
  | possible (S : List Relation)
  | contradictory
  deriving DecidableEq

/-- Check the pair `a`, `c` (cf. `Graph.check`). -/
def Graph.checkList (g : Graph) (a c : FeatureId) : VerdictL :=
  if g.conflictList then .contradictory
  else
    match g.allowedList a c with
    | [] => .contradictory
    | [t] => .entailed t
    | S => .possible S

/-- Forget the list order. -/
def VerdictL.toVerdict : VerdictL → Verdict
  | .entailed t => .entailed t
  | .possible S => .possible S.toFinset
  | .contradictory => .contradictory

/-! ## Agreement with the `Finset` checker -/

theorem mem_table_iff {r s t : Relation} : t ∈ table r s ↔ admits r s t = true := by
  simp [table, Relation.mem_all]

theorem mem_tableList {r s t : Relation} : t ∈ tableList r s ↔ t ∈ table r s := by
  simp [tableList, mem_table_iff, Relation.mem_list]

theorem mem_statedFacts_iff (a b : FeatureId) (t : Relation) (fs : List Fact) :
    t ∈ statedFacts fs a b ↔ (fs.all fun f => statedOK f a b t) = true := by
  induction fs with
  | nil => simp [statedFacts, Relation.mem_all]
  | cons f fs ih =>
    rw [statedFacts, List.all_cons]
    split_ifs with c1 c2
    · rw [Finset.mem_inter, ih, Finset.mem_singleton]
      simp [statedOK, c1, and_comm]
    · rw [Finset.mem_inter, ih, Finset.mem_singleton]
      by_cases hab : a = b
      · subst hab
        exact absurd c2 c1
      · simp [statedOK, c2, hab, and_comm]
    · rw [ih]
      simp [statedOK, c1, c2]

theorem mem_stated_iff (g : Graph) (a b : FeatureId) (t : Relation) :
    t ∈ g.stated a b ↔ g.statedB a b t = true :=
  mem_statedFacts_iff a b t g.facts

theorem mem_constrain_iff (g : Graph) (a c : FeatureId) (t : Relation) (bs : List FeatureId) :
    t ∈ g.constrain a c bs ↔ (bs.all fun b => derivedOK g a c t b) = true := by
  induction bs with
  | nil => simp [Graph.constrain, Relation.mem_all]
  | cons b bs ih =>
    unfold Graph.constrain
    rcases h1 : g.lookup a b with _ | r <;> rcases h2 : g.lookup b c with _ | s <;>
      simp [derivedOK, h1, h2, ih, mem_table_iff, Finset.mem_inter, and_comm]

theorem mem_allowed_iff (g : Graph) (a c : FeatureId) (t : Relation) :
    t ∈ g.allowed a c ↔ g.allowedB a c t = true := by
  simp [Graph.allowed, Graph.derived, Finset.mem_inter, mem_constrain_iff, mem_stated_iff,
    Graph.allowedB]

theorem mem_allowedList (g : Graph) (a c : FeatureId) (t : Relation) :
    t ∈ g.allowedList a c ↔ t ∈ g.allowed a c := by
  simp [Graph.allowedList, Relation.mem_list, mem_allowed_iff]

theorem stated_eq_empty_iff (g : Graph) (a b : FeatureId) :
    g.stated a b = ∅ ↔ (Relation.list.all fun t => !g.statedB a b t) = true := by
  rw [Finset.eq_empty_iff_forall_notMem, List.all_eq_true]
  constructor
  · intro h t _
    have := h t
    rw [mem_stated_iff] at this
    simpa using this
  · intro h t
    have := h t (Relation.mem_list t)
    rw [mem_stated_iff]
    simpa using this

theorem conflictList_eq (g : Graph) : g.conflictList = g.conflict := by
  unfold Graph.conflictList Graph.conflict
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, (stated_eq_empty_iff g f.a f.b).mpr h⟩
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, (stated_eq_empty_iff g f.a f.b).mp h⟩

theorem toFinset_allowedList (g : Graph) (a c : FeatureId) :
    (g.allowedList a c).toFinset = g.allowed a c := by
  ext t
  simp [mem_allowedList]

/-- The list checker is the `Finset` checker. -/
theorem Graph.checkList_toVerdict (g : Graph) (a c : FeatureId) :
    (g.checkList a c).toVerdict = g.check a c := by
  have hf : Relation.list.filter (fun t => decide (t ∈ g.allowed a c)) = g.allowedList a c := by
    unfold Graph.allowedList
    apply List.filter_congr
    intro t _
    rw [Bool.eq_iff_iff]
    simp [mem_allowed_iff]
  unfold Graph.checkList Graph.check
  rw [conflictList_eq]
  by_cases hc : g.conflict = true
  · simp [hc, VerdictL.toVerdict]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    unfold verdictOf
    rw [hf]
    rcases h : g.allowedList a c with _ | ⟨t, _ | ⟨u, rest⟩⟩
    · simp [VerdictL.toVerdict]
    · simp [VerdictL.toVerdict]
    · have hs := toFinset_allowedList g a c
      rw [h] at hs
      simp [VerdictL.toVerdict, hs]

end Geospatial.RCC8
