import LeanGeospatial.ValidatorList

/-!
# Multi-hop RCC8 path consistency

`Graph.check` and `Graph.checkList` in `Validator.lean` / `ValidatorList.lean`
intersect composition tables only over one intermediate feature (`a → b → c`),
so multi-hop chains (`A → B → C → D`) and cycles of length ≥ 4 escape them.

This module implements algebraic closure (path consistency) over a finite
feature set using only `Bool` masks and `List`s (no `Finset`, structural
recursion on `Nat` fuel), so:

- every theorem reduces in Lean's kernel with `decide`, and
- `lean-rs` can compile `Graph.propagateCheck` directly to Rust.

The main soundness theorems prove that algebraic closure never drops a relation
realized by any model:

- `Graph.propagateCheck_entailed`
- `Graph.propagateCheck_possible`
- `Graph.propagateCheck_contradictory`
-/

namespace Geospatial.RCC8

open Geospatial

/-! ## Relation masks -/

/-- An 8-bit boolean mask of allowed RCC8 base relations between two features. -/
structure RelMask where
  dc : Bool
  ec : Bool
  po : Bool
  eq : Bool
  tpp : Bool
  ntpp : Bool
  tppi : Bool
  ntppi : Bool
  deriving DecidableEq, BEq

namespace RelMask

/-- Read whether a base relation is allowed by the mask. -/
def get (m : RelMask) : Relation → Bool
  | .dc => m.dc
  | .ec => m.ec
  | .po => m.po
  | .eq => m.eq
  | .tpp => m.tpp
  | .ntpp => m.ntpp
  | .tppi => m.tppi
  | .ntppi => m.ntppi

/-- Mask allowing all eight base relations. -/
def all : RelMask := ⟨true, true, true, true, true, true, true, true⟩

@[simp] theorem get_all (t : Relation) : all.get t = true := by
  cases t <;> rfl

/-- Build a mask from a boolean predicate on the eight base relations. -/
def ofPred (f : Relation → Bool) : RelMask :=
  ⟨f .dc, f .ec, f .po, f .eq, f .tpp, f .ntpp, f .tppi, f .ntppi⟩

@[simp] theorem get_ofPred (f : Relation → Bool) (t : Relation) :
    (ofPred f).get t = f t := by
  cases t <;> rfl

/-- Whether the mask allows no base relation at all. -/
def isEmpty (m : RelMask) : Bool :=
  !(m.dc || m.ec || m.po || m.eq || m.tpp || m.ntpp || m.tppi || m.ntppi)

theorem get_eq_false_of_isEmpty {m : RelMask} (h : m.isEmpty = true) (t : Relation) :
    m.get t = false := by
  cases m
  cases t <;> simp_all [isEmpty, get]

end RelMask

/-! ## Constraint networks -/

/-- One entry of an RCC8 constraint network. -/
structure NetEntry where
  src : FeatureId
  dst : FeatureId
  mask : RelMask
  deriving DecidableEq, BEq

/-- Look up the candidate mask for `(u, v)` in `net` (defaulting to `RelMask.all`). -/
def netGet : List NetEntry → FeatureId → FeatureId → RelMask
  | [], _, _ => RelMask.all
  | e :: rest, u, v => if e.src = u ∧ e.dst = v then e.mask else netGet rest u v

theorem netGet_eq_of_mem {net : List NetEntry} {u v : FeatureId} {m : RelMask}
    (hmem : ⟨u, v, m⟩ ∈ net)
    (huniq : ∀ e ∈ net, e.src = u → e.dst = v → e.mask = m) :
    netGet net u v = m := by
  induction net with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [netGet]
    split_ifs with hk
    · exact huniq hd List.mem_cons_self hk.1 hk.2
    · refine ih ?_ (fun e he => huniq e (List.mem_cons_of_mem _ he))
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact absurd ⟨rfl, rfl⟩ hk
      · exact htl

theorem netGet_eq_all_of_forall_ne {net : List NetEntry} {u v : FeatureId}
    (hne : ∀ e ∈ net, ¬ (e.src = u ∧ e.dst = v)) :
    netGet net u v = RelMask.all := by
  induction net with
  | nil => rfl
  | cons hd tl ih =>
    simp only [netGet]
    split_ifs with hk
    · exact absurd hk (hne hd List.mem_cons_self)
    · exact ih fun e he => hne e (List.mem_cons_of_mem _ he)

/-! ## Propagation and verdicts -/

/-- Initial mask allowed between `u` and `v` by the stated facts and reflexivity. -/
def pairInitMask (g : Graph) (u v : FeatureId) : RelMask :=
  RelMask.ofPred fun t => g.statedB u v t && if u == v then decide (t = .eq) else true

/-- Initial constraint network on `fs × fs`. -/
def initNet (g : Graph) (fs : List FeatureId) : List NetEntry :=
  fs.flatMap fun u => fs.map fun v => ⟨u, v, pairInitMask g u v⟩

/-- `t` is admitted by composing some relation in `m1` with some relation in `m2`. -/
def relsAllow (m1 m2 : RelMask) (t : Relation) : Bool :=
  Relation.list.any fun r => m1.get r && Relation.list.any fun s => m2.get s && admits r s t

/-- Intersect mask `m` (for `(u, w)`) with the composition via intermediate feature `b`. -/
def stepVia (net : List NetEntry) (u w b : FeatureId) (m : RelMask) : RelMask :=
  let m1 := netGet net u b
  let m2 := netGet net b w
  RelMask.ofPred fun t => m.get t && relsAllow m1 m2 t

/-- Fold `stepVia` across a list of intermediate features `bs`. -/
def stepPairFold (net : List NetEntry) (u w : FeatureId) : List FeatureId → RelMask → RelMask
  | [], m => m
  | b :: bs, m => stepPairFold net u w bs (stepVia net u w b m)

/-- Refine the mask for `(u, w)` against all intermediate features in `fs`. -/
def stepPair (fs : List FeatureId) (net : List NetEntry) (u w : FeatureId) : RelMask :=
  stepPairFold net u w fs (netGet net u w)

/-- One path-consistency sweep over `fs × fs`. -/
def stepNet (fs : List FeatureId) (net : List NetEntry) : List NetEntry :=
  fs.flatMap fun u => fs.map fun w => ⟨u, w, stepPair fs net u w⟩

/-- Iterate `stepNet` until convergence or fuel exhaustion. -/
def propagateLoop (fs : List FeatureId) (net : List NetEntry) : Nat → List NetEntry
  | 0 => net
  | k + 1 =>
    let next := stepNet fs net
    if next == net then net else propagateLoop fs next k

/-- Compute the path-consistent closure of `g` on the feature set `fs`. -/
def propagateNet (g : Graph) (fs : List FeatureId) : List NetEntry :=
  propagateLoop fs (initNet g fs) (8 * fs.length * fs.length + 1)

/-- Whether some pair in `fs × fs` has an empty candidate mask. -/
def hasEmptyPair (fs : List FeatureId) (net : List NetEntry) : Bool :=
  fs.any fun u => fs.any fun v => (netGet net u v).isEmpty

/-- The features tracked for checking `a` and `c`. -/
def queryFeatures (g : Graph) (a c : FeatureId) : List FeatureId :=
  (a :: c :: g.features).dedup

/-- The relations remaining between `a` and `c` after multi-hop path consistency. -/
def Graph.propagateAllowed (g : Graph) (a c : FeatureId) : List Relation :=
  let fs := queryFeatures g a c
  let net := propagateNet g fs
  Relation.list.filter fun t => (netGet net a c).get t

/-- Check the pair `(a, c)` using multi-hop algebraic closure. -/
def Graph.propagateCheck (g : Graph) (a c : FeatureId) : VerdictL :=
  let fs := queryFeatures g a c
  let net := propagateNet g fs
  if g.conflictList || hasEmptyPair fs net then .contradictory
  else
    match Relation.list.filter fun t => (netGet net a c).get t with
    | [] => .contradictory
    | [t] => .entailed t
    | S => .possible S

/-! ## Soundness -/

/-- A network is sound for a model `M` when every pair's realized relation
remains set in the network's mask. -/
def Net.Satisfies (net : List NetEntry) (M : FeatureId → RegularClosedRegion Point2D) : Prop :=
  (∀ x, (M x : Region).Nonempty) ∧
    ∀ u w t, t.holds (M u) (M w) → (netGet net u w).get t = true

/-- Lookup in a dense `fs × fs` entry table: returns `val u w` inside `fs × fs`,
and `RelMask.all` outside, so any predicate holding for `val u w` holds everywhere. -/
private theorem netGet_pairTable_get (fs : List FeatureId)
    (val : FeatureId → FeatureId → RelMask) {u w : FeatureId} {t : Relation}
    (hval : (val u w).get t = true) :
    (netGet (fs.flatMap fun x => fs.map fun y => ⟨x, y, val x y⟩) u w).get t = true := by
  by_cases huv : u ∈ fs ∧ w ∈ fs
  · have hget : netGet (fs.flatMap fun x => fs.map fun y => ⟨x, y, val x y⟩) u w = val u w := by
      refine netGet_eq_of_mem ?_ ?_
      · exact List.mem_flatMap.mpr ⟨u, huv.1, List.mem_map.mpr ⟨w, huv.2, rfl⟩⟩
      · intro e he hsrc hdst
        obtain ⟨x, -, y, -, rfl⟩ := by simpa using he
        cases hsrc; cases hdst; rfl
    rw [hget]
    exact hval
  · have hall : netGet (fs.flatMap fun x => fs.map fun y => ⟨x, y, val x y⟩) u w = RelMask.all := by
      refine netGet_eq_all_of_forall_ne ?_
      intro e he ⟨hsrc, hdst⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := by simpa using he
      exact huv ⟨hsrc ▸ hx, hdst ▸ hy⟩
    rw [hall, RelMask.get_all]

theorem initNet_satisfies {g : Graph} {M : FeatureId → RegularClosedRegion Point2D}
    (hM : g.Satisfies M) (fs : List FeatureId) :
    Net.Satisfies (initNet g fs) M := by
  refine ⟨hM.1, fun u w t ht => netGet_pairTable_get fs (pairInitMask g) ?_⟩
  rw [pairInitMask, RelMask.get_ofPred]
  have hst : g.statedB u w t = true := (mem_stated_iff g u w t).mp (Graph.mem_stated hM ht)
  rw [hst, Bool.true_and]
  by_cases h : u = w
  · subst h
    have heq : t = .eq :=
      relation_unique _ _ (hM.1 u) (hM.1 u) ht (rfl : Relation.eq.holds (M u) (M u))
    simp [heq]
  · simp [h]

theorem stepVia_sound {net : List NetEntry} {M : FeatureId → RegularClosedRegion Point2D}
    (hnet : Net.Satisfies net M) {u w b : FeatureId} {t : Relation}
    (ht : t.holds (M u) (M w)) {m : RelMask} (hm : m.get t = true) :
    (stepVia net u w b m).get t = true := by
  obtain ⟨r, hr⟩ := exists_relation (M u) (M b) (hnet.1 u) (hnet.1 b)
  obtain ⟨s, hs⟩ := exists_relation (M b) (M w) (hnet.1 b) (hnet.1 w)
  have hm1 : (netGet net u b).get r = true := hnet.2 u b r hr
  have hm2 : (netGet net b w).get s = true := hnet.2 b w s hs
  have hadm : admits r s t = true := by
    rw [← mem_table_iff]
    exact mem_table_of_mem_compose (α := Point2D)
      ⟨M u, M b, M w, hnet.1 u, hnet.1 b, hnet.1 w, hr, hs, ht⟩
  have hrall : relsAllow (netGet net u b) (netGet net b w) t = true := by
    unfold relsAllow
    refine List.any_eq_true.mpr ⟨r, Relation.mem_list r, ?_⟩
    rw [hm1, Bool.true_and]
    exact List.any_eq_true.mpr ⟨s, Relation.mem_list s, by simp [hm2, hadm]⟩
  simp [stepVia, hm, hrall]

theorem stepPairFold_sound {net : List NetEntry} {M : FeatureId → RegularClosedRegion Point2D}
    (hnet : Net.Satisfies net M) {u w : FeatureId} {t : Relation}
    (ht : t.holds (M u) (M w)) :
    ∀ (bs : List FeatureId) (m : RelMask), m.get t = true →
      (stepPairFold net u w bs m).get t = true
  | [], _, hm => hm
  | _ :: bs, _, hm =>
    stepPairFold_sound hnet ht bs _ (stepVia_sound hnet ht hm)

theorem stepNet_satisfies {net : List NetEntry} {M : FeatureId → RegularClosedRegion Point2D}
    (hnet : Net.Satisfies net M) (fs : List FeatureId) :
    Net.Satisfies (stepNet fs net) M :=
  ⟨hnet.1, fun u w t ht =>
    netGet_pairTable_get fs (stepPair fs net) (stepPairFold_sound hnet ht fs _ (hnet.2 u w t ht))⟩

theorem propagateLoop_satisfies (fs : List FeatureId)
    {M : FeatureId → RegularClosedRegion Point2D} :
    ∀ (k : Nat) (net : List NetEntry), Net.Satisfies net M →
      Net.Satisfies (propagateLoop fs net k) M
  | 0, _, hnet => hnet
  | k + 1, net, hnet => by
    unfold propagateLoop
    dsimp only
    split_ifs
    · exact hnet
    · exact propagateLoop_satisfies fs k (stepNet fs net) (stepNet_satisfies hnet fs)

theorem propagateNet_satisfies {g : Graph} {M : FeatureId → RegularClosedRegion Point2D}
    (hM : g.Satisfies M) (fs : List FeatureId) :
    Net.Satisfies (propagateNet g fs) M :=
  propagateLoop_satisfies fs _ _ (initNet_satisfies hM fs)

theorem no_model_of_hasEmptyPair {g : Graph} (fs : List FeatureId)
    (h : hasEmptyPair fs (propagateNet g fs) = true) :
    ¬ ∃ M, g.Satisfies M := by
  rintro ⟨M, hM⟩
  unfold hasEmptyPair at h
  obtain ⟨u, -, hv⟩ := List.any_eq_true.mp h
  obtain ⟨v, -, hempty⟩ := List.any_eq_true.mp hv
  obtain ⟨t, ht⟩ := exists_relation (M u) (M v) (hM.1 u) (hM.1 v)
  have hget := (propagateNet_satisfies hM fs).2 u v t ht
  rw [RelMask.get_eq_false_of_isEmpty hempty t] at hget
  cases hget

private theorem mem_propagateFiltered {g : Graph} {a c : FeatureId}
    {M : FeatureId → RegularClosedRegion Point2D} (hM : g.Satisfies M)
    {t : Relation} (ht : t.holds (M a) (M c)) :
    t ∈ Relation.list.filter fun r =>
      (netGet (propagateNet g (queryFeatures g a c)) a c).get r :=
  List.mem_filter.mpr ⟨Relation.mem_list t,
    (propagateNet_satisfies hM (queryFeatures g a c)).2 a c t ht⟩

/-- If `g.propagateCheck a c = .entailed t`, every model of `g` puts `t`
between `a` and `c`. -/
theorem Graph.propagateCheck_entailed {g : Graph} {a c : FeatureId} {t : Relation}
    (h : g.propagateCheck a c = .entailed t)
    {M : FeatureId → RegularClosedRegion Point2D} (hM : g.Satisfies M) :
    t.holds (M a) (M c) := by
  obtain ⟨t', ht'⟩ := exists_relation (M a) (M c) (hM.1 a) (hM.1 c)
  have hmem := mem_propagateFiltered hM ht'
  unfold Graph.propagateCheck at h
  dsimp only at h
  set fs := queryFeatures g a c
  set net := propagateNet g fs
  by_cases hc : (g.conflictList || hasEmptyPair fs net) = true
  · simp [hc] at h
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    rcases hfilt : Relation.list.filter (fun r => (netGet net a c).get r) with
      _ | ⟨u, _ | ⟨v, rest⟩⟩
    · rw [hfilt] at h; cases h
    · rw [hfilt] at h hmem
      cases h
      cases List.mem_singleton.mp hmem
      exact ht'
    · rw [hfilt] at h; cases h

/-- If `g.propagateCheck a c = .possible S`, every model of `g` realizes one of `S`. -/
theorem Graph.propagateCheck_possible {g : Graph} {a c : FeatureId} {S : List Relation}
    (h : g.propagateCheck a c = .possible S)
    {M : FeatureId → RegularClosedRegion Point2D} (hM : g.Satisfies M)
    {t : Relation} (ht : t.holds (M a) (M c)) :
    t ∈ S := by
  have hmem := mem_propagateFiltered hM ht
  unfold Graph.propagateCheck at h
  dsimp only at h
  set fs := queryFeatures g a c
  set net := propagateNet g fs
  by_cases hc : (g.conflictList || hasEmptyPair fs net) = true
  · simp [hc] at h
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    rcases hfilt : Relation.list.filter (fun r => (netGet net a c).get r) with
      _ | ⟨u, _ | ⟨v, rest⟩⟩
    · rw [hfilt] at h; cases h
    · rw [hfilt] at h; cases h
    · rw [hfilt] at h
      cases h
      rwa [← hfilt]

/-- If `g.propagateCheck a c = .contradictory`, the facts have no model. -/
theorem Graph.propagateCheck_contradictory {g : Graph} {a c : FeatureId}
    (h : g.propagateCheck a c = .contradictory) :
    ¬ ∃ M, g.Satisfies M := by
  unfold Graph.propagateCheck at h
  dsimp only at h
  set fs := queryFeatures g a c
  set net := propagateNet g fs
  by_cases hc : (g.conflictList || hasEmptyPair fs net) = true
  · rcases Bool.or_eq_true_iff.mp hc with hconf | hemp
    · rw [conflictList_eq] at hconf
      exact Graph.no_model_of_conflict hconf
    · exact no_model_of_hasEmptyPair fs hemp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    rcases hfilt : Relation.list.filter (fun r => (netGet net a c).get r) with
      _ | ⟨u, _ | ⟨v, rest⟩⟩
    · rintro ⟨M, hM⟩
      obtain ⟨t, ht⟩ := exists_relation (M a) (M c) (hM.1 a) (hM.1 c)
      have hmem := mem_propagateFiltered hM ht
      rw [hfilt] at hmem
      simp at hmem
    · rw [hfilt] at h; cases h
    · rw [hfilt] at h; cases h

end Geospatial.RCC8
