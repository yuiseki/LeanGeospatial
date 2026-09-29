import LeanGeospatial.Homeomorph

/-!
# Dimension functions and the dimension-valued DE-9IM matrix

A `DimensionFunction α` assigns to every set of `α` a value in `WithBot ℕ`,
with one contract: the value is `⊥` exactly on the empty set
(`dim_eq_bot_iff`). The contract is what lets the dimension values carry the
old meaning of DE-9IM's letters, `F` for empty and `T` for nonempty
(`de9im_eq_bot_iff`, `de9im_ne_bot_iff`).

Nothing else is asked, and nothing ties a dimension function to
homeomorphisms by itself. Compatibility across spaces is a separate predicate,
`DimensionCompatible dα dβ e` for `e : α ≃ₜ β`: `e` carries every set to one of
the same dimension. With it the matrix is preserved (`de9im_map`), and so is
every pattern (`CellPattern.matches_map`).

`de9im d A B s t` is `d.dim` of the cell `s t`, in any space and any
dimension. Patterns are a character per cell: `T`, `F`, `*` or an exact value
`k` (`DimChar`). The earlier `T`/`F`/`*` patterns are patterns of this kind,
and they mean the same thing for every dimension function
(`Pattern.toCell_matches`).
-/

namespace Geospatial.DE9IM

open Set

/-- A dimension for every set, `⊥` exactly on the empty set. -/
structure DimensionFunction (α : Type*) [TopologicalSpace α] where
  /-- The dimension of a set. -/
  dim : Set α → WithBot ℕ
  /-- `⊥` is the dimension of the empty set and of nothing else. -/
  dim_eq_bot_iff : ∀ {S : Set α}, dim S = ⊥ ↔ S = ∅

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace DimensionFunction

variable (d : DimensionFunction α)

@[simp] theorem dim_empty : d.dim ∅ = ⊥ := d.dim_eq_bot_iff.mpr rfl

theorem dim_ne_bot_iff {S : Set α} : d.dim S ≠ ⊥ ↔ S.Nonempty := by
  rw [Ne, d.dim_eq_bot_iff, nonempty_iff_ne_empty]

theorem ext' {d d' : DimensionFunction α} (h : ∀ S, d.dim S = d'.dim S) : d = d' := by
  cases d
  cases d'
  congr
  exact funext h

end DimensionFunction

/-- `e` carries every set to a set of the same dimension. -/
def DimensionCompatible (dα : DimensionFunction α) (dβ : DimensionFunction β) (e : α ≃ₜ β) :
    Prop :=
  ∀ S, dβ.dim (e '' S) = dα.dim S

namespace DimensionCompatible

variable {dα : DimensionFunction α} {dβ : DimensionFunction β} {dγ : DimensionFunction γ}

theorem refl (d : DimensionFunction α) : DimensionCompatible d d (Homeomorph.refl α) :=
  fun S => by simp

theorem symm {e : α ≃ₜ β} (h : DimensionCompatible dα dβ e) :
    DimensionCompatible dβ dα e.symm := fun S => by
  have := h (e.symm '' S)
  simpa only [image_image, Homeomorph.apply_symm_apply, image_id'] using this.symm

theorem trans {e : α ≃ₜ β} {f : β ≃ₜ γ} (h : DimensionCompatible dα dβ e)
    (h' : DimensionCompatible dβ dγ f) : DimensionCompatible dα dγ (e.trans f) := fun S => by
  change dγ.dim ((f ∘ e) '' S) = _
  rw [image_comp, h', h]

end DimensionCompatible

/-! ## The matrix -/

/-- The dimension-valued DE-9IM matrix of two sets. -/
def de9im (d : DimensionFunction α) (A B : Set α) (s t : Stratum) : WithBot ℕ :=
  d.dim (cell s t A B)

/-- `F`: the entry is `⊥` exactly when the cell is empty. -/
theorem de9im_eq_bot_iff (d : DimensionFunction α) (A B : Set α) (s t : Stratum) :
    de9im d A B s t = ⊥ ↔ cell s t A B = ∅ :=
  d.dim_eq_bot_iff

/-- `T`: the entry is not `⊥` exactly when the cell is nonempty. -/
theorem de9im_ne_bot_iff (d : DimensionFunction α) (A B : Set α) (s t : Stratum) :
    de9im d A B s t ≠ ⊥ ↔ (cell s t A B).Nonempty :=
  d.dim_ne_bot_iff

/-- A homeomorphism compatible with the dimensions keeps the matrix. -/
theorem de9im_map {dα : DimensionFunction α} {dβ : DimensionFunction β} {e : α ≃ₜ β}
    (h : DimensionCompatible dα dβ e) (A B : Set α) :
    de9im dβ (e '' A) (e '' B) = de9im dα A B := by
  funext s t
  simp only [de9im, cell_image]
  exact h _

/-! ## Patterns -/

/-- A pattern character: `T`, `F`, `*`, or an exact dimension `k`. -/
inductive DimChar where
  | T | F | any
  | dim (k : ℕ)
  deriving DecidableEq

/-- Whether a character accepts a matrix entry. -/
def DimChar.Accepts : DimChar → WithBot ℕ → Prop
  | .T, v => v ≠ ⊥
  | .F, v => v = ⊥
  | .any, _ => True
  | .dim k, v => v = (k : WithBot ℕ)

/-- A pattern: a character for every cell. -/
def CellPattern := Stratum → Stratum → DimChar

/-- Two sets match a pattern when every entry of their matrix is accepted. -/
def CellPattern.Matches (p : CellPattern) (d : DimensionFunction α) (A B : Set α) : Prop :=
  ∀ s t, (p s t).Accepts (de9im d A B s t)

/-- A compatible homeomorphism keeps every pattern. -/
theorem CellPattern.matches_map {dα : DimensionFunction α} {dβ : DimensionFunction β}
    {e : α ≃ₜ β} (h : DimensionCompatible dα dβ e) (p : CellPattern) (A B : Set α) :
    p.Matches dβ (e '' A) (e '' B) ↔ p.Matches dα A B := by
  simp only [CellPattern.Matches, de9im_map h]

/-- A `T`/`F`/`*` character as a dimension character. -/
def PatternChar.toDimChar : PatternChar → DimChar
  | .T => .T
  | .F => .F
  | .any => .any

theorem PatternChar.toDimChar_accepts (c : PatternChar) (d : DimensionFunction α) (S : Set α) :
    c.toDimChar.Accepts (d.dim S) ↔ c.Matches S := by
  cases c
  · exact d.dim_ne_bot_iff
  · exact d.dim_eq_bot_iff
  · exact Iff.rfl

/-- A `T`/`F`/`*` pattern as a pattern of cells. -/
def Pattern.toCell (p : Pattern) : CellPattern
  | .I, .I => p.ii.toDimChar
  | .I, .B => p.ib.toDimChar
  | .I, .E => p.ie.toDimChar
  | .B, .I => p.bi.toDimChar
  | .B, .B => p.bb.toDimChar
  | .B, .E => p.be.toDimChar
  | .E, .I => p.ei.toDimChar
  | .E, .B => p.eb.toDimChar
  | .E, .E => p.ee.toDimChar

theorem forall_stratum {P : Stratum → Prop} : (∀ s, P s) ↔ P .I ∧ P .B ∧ P .E :=
  ⟨fun h => ⟨h _, h _, h _⟩, fun ⟨hI, hB, hE⟩ s => by cases s <;> assumption⟩

/-- A `T`/`F`/`*` pattern means the same for every dimension function: the
contract `dim_eq_bot_iff` gives back empty and nonempty. -/
theorem Pattern.toCell_matches (p : Pattern) (d : DimensionFunction α) (A B : Set α) :
    p.toCell.Matches d A B ↔ p.Matches A B := by
  simp only [CellPattern.Matches, forall_stratum, Pattern.toCell, de9im,
    PatternChar.toDimChar_accepts, Pattern.Matches, II, IB, IE, BI, BB, BE, EI, EB, EE,
    and_assoc]

end Geospatial.DE9IM
