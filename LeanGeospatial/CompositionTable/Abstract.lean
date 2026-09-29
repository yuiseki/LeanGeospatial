import LeanGeospatial.Composition

/-!
# An over-approximation of weak composition, proved sound

For an ordered pair of areas `(X, Y)`, record six facts as booleans, its
*signature*:

| Field | Fact |
| --- | --- |
| `c` | `Intersects X Y` |
| `o` | `Intersects (interior X) (interior Y)` |
| `p` | `Within X Y` |
| `q` | `Within Y X` |
| `n` | `Within X (interior Y)` |
| `m` | `Within Y (interior X)` |

Each RCC8 relation between nonempty areas fixes the signature
(`sigOf_mem_sigs`), except that `EQ` leaves `n = m` open: the whole space lies
within its own interior, other areas do not.

Nine laws link the signatures of the three pairs of a triangle `X, Y, Z`
(`schema_sigOf`), each proved from the set and topology definitions; two of
them use that areas are the closure of their interior. `table r s` keeps the
relations `t` for which some choice of signatures for `r`, `s`, `t` satisfies
the nine laws around every orientation of the triangle. It is computed by
`decide`, and `mem_table_of_mem_compose` proves `compose α r s ⊆ table r s`
in every topological space `α`: the laws use nothing about the plane.

No composition table is assumed. The other inclusion is proved separately, by
witnesses, in `CompositionTable/Complete.lean`.
-/

namespace Geospatial.RCC8

open Geospatial

variable {α : Type*} [TopologicalSpace α]

/-- The six facts about an ordered pair of areas. -/
structure Sig where
  c : Bool
  o : Bool
  p : Bool
  q : Bool
  n : Bool
  m : Bool
  deriving DecidableEq

/-- The signature of the reversed pair. -/
def Sig.swap (s : Sig) : Sig := ⟨s.c, s.o, s.q, s.p, s.m, s.n⟩

/-- The signatures a relation allows between nonempty areas. -/
def Relation.sigs : Relation → List Sig
  | .dc => [⟨false, false, false, false, false, false⟩]
  | .ec => [⟨true, false, false, false, false, false⟩]
  | .po => [⟨true, true, false, false, false, false⟩]
  | .eq => [⟨true, true, true, true, false, false⟩, ⟨true, true, true, true, true, true⟩]
  | .tpp => [⟨true, true, true, false, false, false⟩]
  | .ntpp => [⟨true, true, true, false, true, false⟩]
  | .tppi => [⟨true, true, false, true, false, false⟩]
  | .ntppi => [⟨true, true, false, true, false, true⟩]

/-- The nine laws for a triangle `X, Y, Z`, given the signatures of
`(X, Y)`, `(Y, Z)` and `(X, Z)`. -/
def schema (xy yz xz : Sig) : Bool :=
  (!(xy.p && yz.p) || xz.p) &&         -- S1: X ⊆ Y ⊆ Z
  ((!(xy.n && yz.p) || xz.n) &&        -- S2: X ⊆ int Y ⊆ int Z
  ((!(xy.p && yz.n) || xz.n) &&        -- S3: X ⊆ Y ⊆ int Z
  ((!(xy.p && !yz.c) || !xz.c) &&      -- S4: X ⊆ Y, Y ∩ Z = ∅
  ((!(xy.p && !yz.o) || !xz.o) &&      -- S5: X ⊆ Y, interiors of Y, Z apart
  ((!(xy.n && !yz.o) || !xz.c) &&      -- S6: X ⊆ int Y, interiors of Y, Z apart
  ((!(xy.c && yz.n) || xz.o) &&        -- S7: X meets Y ⊆ int Z
  ((!(xy.o && yz.p) || xz.o) &&        -- S8: interiors of X, Y meet, Y ⊆ Z
  (!(xy.c && yz.p) || xz.c))))))))     -- S9: X meets Y ⊆ Z

/-- The nine laws around all six orientations of the triangle `A, B, C`. -/
def consistent (ab bc ac : Sig) : Bool :=
  schema ab bc ac && (schema ac bc.swap ab && (schema ab.swap ac bc &&
    (schema bc ac.swap ab.swap && (schema ac.swap ab bc.swap &&
      schema bc.swap ab.swap ac.swap))))

/-- Whether `t` survives the laws for `r` then `s`. -/
def admits (r s t : Relation) : Bool :=
  r.sigs.any fun ab => s.sigs.any fun bc => t.sigs.any fun ac => consistent ab bc ac

/-- All eight base relations. -/
def Relation.all : Finset Relation := {.dc, .ec, .po, .eq, .tpp, .ntpp, .tppi, .ntppi}

theorem Relation.mem_all (t : Relation) : t ∈ Relation.all := by
  cases t <;> decide

/-- The computed composition table. -/
def table (r s : Relation) : Finset Relation := Relation.all.filter fun t => admits r s t

/-! ## Signatures of actual areas -/

open Classical in
/-- The signature of an ordered pair of areas. -/
noncomputable def sigOf (X Y : RegularClosedRegion α) : Sig :=
  ⟨decide (Intersects (X : Set α) Y),
    decide (Intersects (interior (X : Set α)) (interior (Y : Set α))),
    decide (Within (X : Set α) Y), decide (Within (Y : Set α) X),
    decide (Within (X : Set α) (interior (Y : Set α))),
    decide (Within (Y : Set α) (interior (X : Set α)))⟩

theorem sigOf_swap (X Y : RegularClosedRegion α) : sigOf Y X = (sigOf X Y).swap := by
  simp only [sigOf, Sig.swap, Sig.mk.injEq]
  exact ⟨decide_eq_decide.mpr intersects_comm, decide_eq_decide.mpr intersects_comm,
    trivial, trivial, trivial, trivial⟩

/-! ## The nine laws hold for actual areas -/

private theorem bimp {P Q R : Prop} {_ : Decidable P} {_ : Decidable Q} {_ : Decidable R}
    (h : P → Q → R) : (!(decide P && decide Q) || decide R) = true := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]
  exact h hp hq

private theorem bimpN {P Q R : Prop} {_ : Decidable P} {_ : Decidable Q} {_ : Decidable R}
    (h : P → ¬ Q → ¬ R) : (!(decide P && !decide Q) || !decide R) = true := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]
  exact h hp hq

variable (X Y Z : RegularClosedRegion α)

theorem schema_sigOf : schema (sigOf X Y) (sigOf Y Z) (sigOf X Z) = true := by
  simp only [schema, sigOf, Bool.and_eq_true]
  refine ⟨bimp within_trans, bimp fun h₁ h₂ => within_trans h₁ (interior_mono h₂),
    bimp within_trans, bimpN fun h₁ h₂ h₃ => h₂ (h₃.mono_left h₁),
    bimpN fun h₁ h₂ h₃ => h₂ (h₃.mono_left (interior_mono h₁)),
    bimpN fun h₁ h₂ h₃ => h₂ ?_, bimp fun h₁ h₂ => ?_,
    bimp fun h₁ h₂ => h₁.mono_right (interior_mono h₂), bimp fun h₁ h₂ => h₁.mono_right h₂⟩
  · -- S6: X ⊆ int Y and a point of X ∩ Z give a point of int Y ∩ int Z,
    -- because Z is the closure of its interior and int Y is open.
    obtain ⟨p, hpX, hpZ⟩ := h₃
    have hp : p ∈ closure (interior (Z : Set α)) := by
      rw [Z.closure_interior_eq]
      exact hpZ
    obtain ⟨q, hqY, hqZ⟩ := mem_closure_iff.mp hp _ isOpen_interior (h₁ hpX)
    exact ⟨q, hqY, hqZ⟩
  · -- S7: a point of X ∩ Y lies in int Z, and X is the closure of its
    -- interior, so int X meets int Z.
    obtain ⟨p, hpX, hpY⟩ := h₁
    have hp : p ∈ closure (interior (X : Set α)) := by
      rw [X.closure_interior_eq]
      exact hpX
    obtain ⟨q, hqZ, hqX⟩ := mem_closure_iff.mp hp _ isOpen_interior (h₂ hpY)
    exact ⟨q, hqX, hqZ⟩

theorem consistent_sigOf : consistent (sigOf X Y) (sigOf Y Z) (sigOf X Z) = true := by
  simp only [consistent, ← sigOf_swap, Bool.and_eq_true]
  exact ⟨schema_sigOf X Y Z, schema_sigOf X Z Y, schema_sigOf Y X Z, schema_sigOf Y Z X,
    schema_sigOf Z X Y, schema_sigOf Z Y X⟩

/-! ## Each relation fixes the signature -/

open Classical in
theorem sigOf_mem_sigs {X Y : RegularClosedRegion α} (hX : (X : Set α).Nonempty)
    (hY : (Y : Set α).Nonempty) {r : Relation} (h : r.holds X Y) :
    sigOf X Y ∈ r.sigs := by
  -- Facts linking the six building blocks for nonempty areas.
  have hPO : Within (X : Set α) Y →
      Intersects (interior (X : Set α)) (interior (Y : Set α)) :=
    fun h => ((X.within_iff_cells Y hX).mp h).1
  have hQO : Within (Y : Set α) X →
      Intersects (interior (X : Set α)) (interior (Y : Set α)) :=
    fun h => intersects_symm ((Y.within_iff_cells X hY).mp h).1
  have hOC : Intersects (interior (X : Set α)) (interior (Y : Set α)) →
      Intersects (X : Set α) Y :=
    fun h => (h.mono_left interior_subset).mono_right interior_subset
  have hNP : Within (X : Set α) (interior (Y : Set α)) → Within (X : Set α) Y :=
    fun h => within_trans h interior_subset
  have hMQ : Within (Y : Set α) (interior (X : Set α)) → Within (Y : Set α) X :=
    fun h => within_trans h interior_subset
  have hanti : Within (X : Set α) Y → Within (Y : Set α) X → (X : Set α) = Y :=
    within_antisymm
  -- In each case, settle all six facts, then read off the signature.
  cases r with
  | dc =>
    have hc : ¬ Intersects (X : Set α) Y := disjoint_iff_not_intersects.mp h
    have ho : ¬ Intersects (interior (X : Set α)) (interior (Y : Set α)) :=
      fun h => hc (hOC h)
    have hp : ¬ Within (X : Set α) Y := fun h => ho (hPO h)
    have hq : ¬ Within (Y : Set α) X := fun h => ho (hQO h)
    have hn : ¬ Within (X : Set α) (interior (Y : Set α)) := fun h => hp (hNP h)
    have hm : ¬ Within (Y : Set α) (interior (X : Set α)) := fun h => hq (hMQ h)
    simp [sigOf, Relation.sigs, hc, ho, hp, hq, hn, hm]
  | ec =>
    obtain ⟨hc, ho⟩ := h
    have ho : ¬ Intersects (interior (X : Set α)) (interior (Y : Set α)) :=
      disjoint_iff_not_intersects.mp ho
    have hp : ¬ Within (X : Set α) Y := fun h => ho (hPO h)
    have hq : ¬ Within (Y : Set α) X := fun h => ho (hQO h)
    have hn : ¬ Within (X : Set α) (interior (Y : Set α)) := fun h => hp (hNP h)
    have hm : ¬ Within (Y : Set α) (interior (X : Set α)) := fun h => hq (hMQ h)
    simp [sigOf, Relation.sigs, hc, ho, hp, hq, hn, hm]
  | po =>
    obtain ⟨ho, hp, hq⟩ := h
    have hn : ¬ Within (X : Set α) (interior (Y : Set α)) := fun h => hp (hNP h)
    have hm : ¬ Within (Y : Set α) (interior (X : Set α)) := fun h => hq (hMQ h)
    simp [sigOf, Relation.sigs, hOC ho, ho, hp, hq, hn, hm]
  | eq =>
    obtain rfl := eq_iff.mp h
    have hp : Within (X : Set α) X := within_refl _
    by_cases hn : Within (X : Set α) (interior (X : Set α))
    · simp [sigOf, Relation.sigs, hn, hOC (hPO hp), hPO hp, hp]
    · simp [sigOf, Relation.sigs, hn, hOC (hPO hp), hPO hp, hp]
  | tpp =>
    obtain ⟨hp, hne, hn⟩ := h
    have hq : ¬ Within (Y : Set α) X := fun hq => hne (hanti hp hq)
    have hm : ¬ Within (Y : Set α) (interior (X : Set α)) := fun h => hq (hMQ h)
    simp [sigOf, Relation.sigs, hOC (hPO hp), hPO hp, hp, hq, hn, hm]
  | ntpp =>
    obtain ⟨hn, hne⟩ := h
    have hp := hNP hn
    have hq : ¬ Within (Y : Set α) X := fun hq => hne (hanti hp hq)
    have hm : ¬ Within (Y : Set α) (interior (X : Set α)) := fun h => hq (hMQ h)
    simp [sigOf, Relation.sigs, hOC (hPO hp), hPO hp, hp, hq, hn, hm]
  | tppi =>
    obtain ⟨hq, hne, hm⟩ := h
    have hp : ¬ Within (X : Set α) Y := fun hp => hne (hanti hp hq).symm
    have hn : ¬ Within (X : Set α) (interior (Y : Set α)) := fun h => hp (hNP h)
    simp [sigOf, Relation.sigs, hOC (hQO hq), hQO hq, hp, hq, hn, hm]
  | ntppi =>
    obtain ⟨hm, hne⟩ := h
    have hq := hMQ hm
    have hp : ¬ Within (X : Set α) Y := fun hp => hne (hanti hp hq).symm
    have hn : ¬ Within (X : Set α) (interior (Y : Set α)) := fun h => hp (hNP h)
    simp [sigOf, Relation.sigs, hOC (hQO hq), hQO hq, hp, hq, hn, hm]

/-! ## Soundness -/

/-- Everything in the weak composition is in the computed table. -/
theorem mem_table_of_mem_compose {r s t : Relation} (h : t ∈ compose α r s) :
    t ∈ table r s := by
  obtain ⟨A, B, C, hA, hB, hC, hr, hs, ht⟩ := h
  simp only [table, Finset.mem_filter, Relation.mem_all, true_and, admits, List.any_eq_true]
  exact ⟨sigOf A B, sigOf_mem_sigs hA hB hr, sigOf B C, sigOf_mem_sigs hB hC hs,
    sigOf A C, sigOf_mem_sigs hA hC ht, consistent_sigOf A B C⟩

end Geospatial.RCC8
