import LeanGeospatial.NineIntersection

/-!
# RCC8

The eight base relations of the Region Connection Calculus, for areas
(`RegularClosedRegion`). Each is defined from the relations and topology that
already exist, not postulated and not read off a table:

| Relation | Meaning | Definition |
| --- | --- | --- |
| `DC` | disconnected | `Disjoint a b` |
| `EC` | externally connected | `Touches a b` |
| `PO` | partial overlap | interiors meet, neither within the other |
| `EQ` | equal | `a = b` |
| `TPP` | tangential proper part | within, not equal, not within the interior |
| `NTPP` | non-tangential proper part | within the interior, not equal |
| `TPPi`, `NTPPi` | the converses | `TPP B A`, `NTPP B A` |

The main theorem, `existsUnique_relation`, says that for nonempty areas
exactly one of the eight holds.

`NTPP` includes `a ≠ b` on purpose: the whole plane is an area that lies
within its own interior, and without that clause it would be both `EQ` and
`NTPP` with itself (`univ_eq_and_within_interior`).
-/

namespace Geospatial.RCC8

open Geospatial

variable (A B : RegularClosedRegion)

/-- Disconnected. -/
def DC : Prop := Geospatial.Disjoint (A : Region) B

/-- Externally connected. -/
def EC : Prop := Touches (A : Region) B

/-- Partially overlapping. -/
def PO : Prop :=
  Intersects (interior (A : Region)) (interior (B : Region)) ∧
    ¬ Within (A : Region) B ∧ ¬ Within (B : Region) A

/-- Equal. -/
def EQ : Prop := (A : Region) = B

/-- Tangential proper part. -/
def TPP : Prop :=
  Within (A : Region) B ∧ (A : Region) ≠ B ∧ ¬ Within (A : Region) (interior (B : Region))

/-- Non-tangential proper part. -/
def NTPP : Prop := Within (A : Region) (interior (B : Region)) ∧ (A : Region) ≠ B

/-- Tangential proper part, inverse. -/
def TPPi : Prop := TPP B A

/-- Non-tangential proper part, inverse. -/
def NTPPi : Prop := NTPP B A

/-! ## Agreement with the existing relations -/

theorem dc_iff_disjoint : DC A B ↔ Geospatial.Disjoint (A : Region) B := Iff.rfl

theorem ec_iff_touches : EC A B ↔ Touches (A : Region) B := Iff.rfl

theorem tppi_iff_tpp : TPPi A B ↔ TPP B A := Iff.rfl

theorem ntppi_iff_ntpp : NTPPi A B ↔ NTPP B A := Iff.rfl

theorem tpp_iff_tppi : TPP A B ↔ TPPi B A := Iff.rfl

theorem ntpp_iff_ntppi : NTPP A B ↔ NTPPi B A := Iff.rfl

theorem dc_symm : DC A B → DC B A := disjoint_symm

theorem ec_symm : EC A B → EC B A := touches_symm

theorem po_symm : PO A B → PO B A :=
  fun ⟨h, hAB, hBA⟩ => ⟨intersects_symm h, hBA, hAB⟩

theorem eq_symm : EQ A B → EQ B A := Eq.symm

/-- `DC` in terms of the nine cells. -/
theorem dc_iff_cells :
    DC A B ↔ II A B = ∅ ∧ IB A B = ∅ ∧ BI A B = ∅ ∧ BB A B = ∅ :=
  A.disjoint_iff_cells B

/-- `EC` in terms of the nine cells. -/
theorem ec_iff_cells :
    EC A B ↔ II A B = ∅ ∧ ((IB A B).Nonempty ∨ (BI A B).Nonempty ∨ (BB A B).Nonempty) :=
  A.touches_iff_cells B

/-- An area fails to lie within a closed region exactly when some interior
point of the area is exterior to it. -/
theorem not_within_iff_IE_nonempty :
    ¬ Within (A : Region) B ↔ (IE A B).Nonempty := by
  constructor
  · intro h
    obtain ⟨p, hpA, hpB⟩ := Set.not_subset.mp h
    have hpE : p ∈ exterior (B : Region) := by
      rw [exterior_eq_of_isClosed B.isClosed]
      exact hpB
    have hp : p ∈ closure (interior (A : Region)) := by
      rw [A.closure_interior_eq]
      exact hpA
    obtain ⟨q, hqE, hqI⟩ :=
      mem_closure_iff.mp hp (exterior (B : Region)) (isOpen_exterior _) hpE
    exact ⟨q, hqI, hqE⟩
  · rintro ⟨p, hpI, hpE⟩ h
    change p ∈ interior (A : Region) at hpI
    change p ∈ exterior (B : Region) at hpE
    rw [exterior_eq_of_isClosed B.isClosed] at hpE
    exact hpE (h (interior_subset hpI))

/-- `PO` in terms of the nine cells: each interior meets the other's interior
and the other's exterior. -/
theorem po_iff_cells :
    PO A B ↔ (II A B).Nonempty ∧ (IE A B).Nonempty ∧ (EI A B).Nonempty := by
  unfold PO
  rw [not_within_iff_IE_nonempty, not_within_iff_IE_nonempty,
    show IE (B : Region) A = EI (A : Region) B from cell_swap _ _ _ _]
  exact Iff.rfl

/-! ## The eight relations as one type -/

/-- The eight base relations. -/
inductive Relation where
  | dc | ec | po | eq | tpp | ntpp | tppi | ntppi
  deriving DecidableEq

/-- Whether a base relation holds between two areas. -/
def Relation.holds : Relation → RegularClosedRegion → RegularClosedRegion → Prop
  | .dc, A, B => DC A B
  | .ec, A, B => EC A B
  | .po, A, B => PO A B
  | .eq, A, B => EQ A B
  | .tpp, A, B => TPP A B
  | .ntpp, A, B => NTPP A B
  | .tppi, A, B => TPPi A B
  | .ntppi, A, B => NTPPi A B

/-- The converse of a base relation. -/
def Relation.converse : Relation → Relation
  | .dc => .dc
  | .ec => .ec
  | .po => .po
  | .eq => .eq
  | .tpp => .tppi
  | .ntpp => .ntppi
  | .tppi => .tpp
  | .ntppi => .ntpp

theorem Relation.converse_converse (r : Relation) : r.converse.converse = r := by
  cases r <;> rfl

/-- A relation holds from `A` to `B` exactly when its converse holds from `B`
to `A`. -/
theorem Relation.holds_converse (r : Relation) :
    r.converse.holds A B ↔ r.holds B A := by
  cases r
  · exact ⟨dc_symm A B, dc_symm B A⟩
  · exact ⟨ec_symm A B, ec_symm B A⟩
  · exact ⟨po_symm A B, po_symm B A⟩
  · exact ⟨eq_symm A B, eq_symm B A⟩
  all_goals exact Iff.rfl

/-! ## Exactly one relation holds -/

/-- The facts about the building blocks that the case analysis needs. -/
private theorem facts (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty) :
    (Geospatial.Disjoint (A : Region) B ↔ ¬ Intersects (A : Region) B) ∧
    (Touches (A : Region) B ↔
      Intersects (A : Region) B ∧ ¬ Intersects (interior (A : Region)) (interior (B : Region))) ∧
    (Intersects (interior (A : Region)) (interior (B : Region)) → Intersects (A : Region) B) ∧
    (Within (A : Region) B → Intersects (interior (A : Region)) (interior (B : Region))) ∧
    (Within (B : Region) A → Intersects (interior (A : Region)) (interior (B : Region))) ∧
    (Within (A : Region) (interior (B : Region)) → Within (A : Region) B) ∧
    (Within (B : Region) (interior (A : Region)) → Within (B : Region) A) ∧
    ((A : Region) = B ↔ Within (A : Region) B ∧ Within (B : Region) A) ∧
    ((B : Region) = A ↔ (A : Region) = B) := by
  refine ⟨disjoint_iff_not_intersects, ?_, ?_, ?_, ?_, ?_, ?_, ?_, eq_comm⟩
  · unfold Touches
    rw [disjoint_iff_not_intersects]
  · intro h
    exact (h.mono_left interior_subset).mono_right interior_subset
  · intro h
    exact ((A.within_iff_cells B hA).mp h).1
  · intro h
    exact intersects_symm ((B.within_iff_cells A hB).mp h).1
  · exact fun h => within_trans h interior_subset
  · exact fun h => within_trans h interior_subset
  · exact ⟨fun h => h ▸ ⟨within_refl _, within_refl _⟩,
      fun ⟨h₁, h₂⟩ => within_antisymm h₁ h₂⟩

/-- Jointly exhaustive: some base relation holds. -/
theorem exists_relation (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty) :
    ∃ r : Relation, r.holds A B := by
  obtain ⟨hDC, hEC, -, -, -, -, -, hEQ, hEQ'⟩ := facts A B hA hB
  by_cases hC : Intersects (A : Region) B
  swap
  · exact ⟨.dc, hDC.mpr hC⟩
  by_cases hO : Intersects (interior (A : Region)) (interior (B : Region))
  swap
  · exact ⟨.ec, hEC.mpr ⟨hC, hO⟩⟩
  by_cases hE : (A : Region) = B
  · exact ⟨.eq, hE⟩
  by_cases hP : Within (A : Region) B
  · by_cases hN : Within (A : Region) (interior (B : Region))
    · exact ⟨.ntpp, hN, hE⟩
    · exact ⟨.tpp, hP, hE, hN⟩
  by_cases hQ : Within (B : Region) A
  · have hE' : (B : Region) ≠ A := fun h => hE (hEQ'.mp h)
    by_cases hN : Within (B : Region) (interior (A : Region))
    · exact ⟨.ntppi, hN, hE'⟩
    · exact ⟨.tppi, hQ, hE', hN⟩
  exact ⟨.po, hO, hP, hQ⟩

/-- The decision tree behind the case analysis: connected? interiors meet?
equal? within? within the interior? It is only a proof device; the relations
themselves are the definitions above. -/
noncomputable def classify : Relation :=
  open Classical in
  if ¬ Intersects (A : Region) B then .dc
  else if ¬ Intersects (interior (A : Region)) (interior (B : Region)) then .ec
  else if (A : Region) = B then .eq
  else if Within (A : Region) B then
    (if Within (A : Region) (interior (B : Region)) then .ntpp else .tpp)
  else if Within (B : Region) A then
    (if Within (B : Region) (interior (A : Region)) then .ntppi else .tppi)
  else .po

/-- Whichever base relation holds is the one the decision tree picks. -/
theorem classify_eq_of_holds (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty)
    {r : Relation} (hr : r.holds A B) : classify A B = r := by
  obtain ⟨hDC, hEC, hOC, hPO, hQO, hNP, hNQ, hEQ, hEQ'⟩ := facts A B hA hB
  have nn : ∀ {P : Prop}, P → ¬ ¬ P := fun h h' => h' h
  cases r with
  | dc => exact if_pos (hDC.mp hr)
  | ec =>
    obtain ⟨hc, ho⟩ := hEC.mp hr
    rw [classify, if_neg (nn hc), if_pos ho]
  | eq =>
    change (A : Region) = B at hr
    have ho := hPO (hEQ.mp hr).1
    rw [classify, if_neg (nn (hOC ho)), if_neg (nn ho), if_pos hr]
  | tpp =>
    obtain ⟨hp, he, hn⟩ := hr
    have ho := hPO hp
    rw [classify, if_neg (nn (hOC ho)), if_neg (nn ho), if_neg he, if_pos hp, if_neg hn]
  | ntpp =>
    obtain ⟨hn, he⟩ := hr
    have hp := hNP hn
    have ho := hPO hp
    rw [classify, if_neg (nn (hOC ho)), if_neg (nn ho), if_neg he, if_pos hp, if_pos hn]
  | tppi =>
    obtain ⟨hq, he', hn⟩ := hr
    have he : (A : Region) ≠ B := fun h => he' (hEQ'.mpr h)
    have hp : ¬ Within (A : Region) B := fun hp => he (hEQ.mpr ⟨hp, hq⟩)
    have ho := hQO hq
    rw [classify, if_neg (nn (hOC ho)), if_neg (nn ho), if_neg he, if_neg hp, if_pos hq,
      if_neg hn]
  | ntppi =>
    obtain ⟨hn, he'⟩ := hr
    have hq := hNQ hn
    have he : (A : Region) ≠ B := fun h => he' (hEQ'.mpr h)
    have hp : ¬ Within (A : Region) B := fun hp => he (hEQ.mpr ⟨hp, hq⟩)
    have ho := hQO hq
    rw [classify, if_neg (nn (hOC ho)), if_neg (nn ho), if_neg he, if_neg hp, if_pos hq,
      if_pos hn]
  | po =>
    obtain ⟨ho, hp, hq⟩ := hr
    have he : (A : Region) ≠ B := fun h => hp (hEQ.mp h).1
    rw [classify, if_neg (nn (hOC ho)), if_neg (nn ho), if_neg he, if_neg hp, if_neg hq]

/-- Pairwise disjoint: at most one base relation holds. -/
theorem relation_unique (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty)
    {r s : Relation} (hr : r.holds A B) (hs : s.holds A B) : r = s :=
  (classify_eq_of_holds A B hA hB hr).symm.trans (classify_eq_of_holds A B hA hB hs)

/-- Pairwise disjoint, stated for two different relations. -/
theorem pairwise_disjoint (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty)
    {r s : Relation} (hrs : r ≠ s) : ¬ (r.holds A B ∧ s.holds A B) :=
  fun ⟨hr, hs⟩ => hrs (relation_unique A B hA hB hr hs)

/-- Jointly exhaustive, under its usual name. -/
theorem jointly_exhaustive (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty) :
    ∃ r : Relation, r.holds A B :=
  exists_relation A B hA hB

/-- For nonempty areas, exactly one of the eight base relations holds. -/
theorem existsUnique_relation (hA : (A : Region).Nonempty) (hB : (B : Region).Nonempty) :
    ∃! r : Relation, r.holds A B := by
  obtain ⟨r, hr⟩ := exists_relation A B hA hB
  exact ⟨r, hr, fun s hs => relation_unique A B hA hB hs hr⟩

/-! ## Why `NTPP` excludes equality -/

/-- The whole plane, as an area. -/
def univ : RegularClosedRegion := ⟨Set.univ, by simp⟩

/-- The whole plane equals itself and lies within its own interior. Without
the `a ≠ b` clause in `NTPP`, it would be both `EQ` and `NTPP` with itself. -/
theorem univ_eq_and_within_interior :
    EQ univ univ ∧ Within (univ : Region) (interior (univ : Region)) :=
  ⟨rfl, by simp [univ, Within]⟩

end Geospatial.RCC8
