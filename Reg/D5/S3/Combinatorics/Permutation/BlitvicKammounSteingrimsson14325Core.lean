import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Mathlib.Data.Fintype.Perm
import D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core

/-! Typed whole-family audits for the exact source bounds.
The observations retain the original rank functions and dependent source domains.
-/

namespace Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core

open _root_.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core
open _root_.D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private theorem packed_pattern : Packs pattern 2 1 pattern := by
  intro t a b
  have ht : t = 0 := Subsingleton.elim _ _
  subst t
  simp [windowIndex]

namespace Bounds

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun j => Fin (5 + (j - 1) * 3) → Fin (5 + (j - 1) * 3))
    (fun j => Fin (5 + (j - 1) * 3) → Fin (5 + (j - 1) * 3))

def actual : Realization signature :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ x => if x.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ j : ℕ, ∀ hj : 1 ≤ j,
    ∀ w : Fin (5 + (j - 1) * 3) → Fin (5 + (j - 1) * 3),
    Packs pattern 2 j w → ∀ x,
      r.readout () j w ⟨0, by omega⟩ ≤ r.readout () j w x ∧
      r.readout () j w x ≤ r.readout () j w ⟨3 * j + 1, by omega⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 (by decide) pattern packed_pattern 1).1
  change (1 : Fin 5) ≤ 0 at hh
  exact (by decide : ¬ (1 : Fin 5) ≤ 0) hh

def family : Registration arena (type_of% @packing_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨packing_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have hh := congrFun h 0
    change (0 : Fin 5) = 1 at hh
    exact (by decide : (0 : Fin 5) ≠ 1) hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@packing_bounds) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core.Bounds.unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core.Bounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Bounds

namespace Extrema

private def patternPerm : Equiv.Perm (Fin 5) where
  toFun := pattern
  invFun := pattern
  left_inv a := by fin_cases a <;> rfl
  right_inv a := by fin_cases a <;> rfl

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun j => Equiv.Perm (Fin (5 + (j - 1) * 3)))
    (fun j => Fin (5 + (j - 1) * 3) → Fin (5 + (j - 1) * 3))

def actual : Realization signature :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ⟨1, by omega⟩) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ j : ℕ, ∀ hj : 1 ≤ j,
    ∀ w : Equiv.Perm (Fin (5 + (j - 1) * 3)), Packs pattern 2 j w →
      (r.readout () j w ⟨0, by omega⟩).val = 0 ∧
      (r.readout () j w ⟨3 * j + 1, by omega⟩).val = 3 * j + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 (by decide) patternPerm packed_pattern).1
  change (1 : ℕ) = 0 at hh
  omega

def family : Registration arena (type_of% @packing_extrema) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨packing_extrema, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, Equiv.refl _, Equiv.swap 0 1, ?_⟩
    intro h
    have hh := congrFun h 0
    change (0 : Fin 5) = Equiv.swap 0 1 0 at hh
    simp at hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@packing_extrema) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core.Extrema.unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core.Extrema.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Extrema
namespace CountGrid

noncomputable section

private theorem count_zero : count pattern 2 0 = 120 := by
  have he : SourcePacking pattern 2 0 ≃ Equiv.Perm (Fin 5) :=
    Equiv.subtypeUnivEquiv (by intro w t; exact Fin.elim0 t)
  change Nat.card (SourcePacking pattern 2 0) = _
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]

private def singleGrid : GridPacking 1 := by
  refine ⟨Equiv.swap 0 2, ?_⟩
  constructor
  · intro t ht
    have he : t = 0 := by omega
    subst t
    change (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 2 < Equiv.swap 0 2 1 ∧
      (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 1 < Equiv.swap 0 2 0
    decide +kernel
  · intro t ht
    omega

private theorem grid_one_unique (q : GridPacking 1) : q = singleGrid := by
  apply Subtype.ext
  ext i
  have he := q.property.1 0 (by decide)
  change (q.val 2).val < (q.val 1).val ∧ (q.val 1).val < (q.val 0).val at he
  have h0 := (q.val 0).isLt
  have h1 := (q.val 1).isLt
  have h2 := (q.val 2).isLt
  have hi := i.isLt
  fin_cases i
  · change (q.val 0).val = 2
    omega
  · change (q.val 1).val = 1
    omega
  · change (q.val 2).val = 0
    omega

private theorem count_one : count pattern 2 1 = 1 := by
  rw [count_eq_grid 1 (by decide)]
  exact Nat.card_eq_one_iff_exists.mpr ⟨singleGrid, grid_one_unique⟩

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ j => count pattern 2 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ j => count pattern 2 j + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ j : ℕ, 1 ≤ j → r.readout () () j = Nat.card (GridPacking j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 (by decide)
  change count pattern 2 1 + 1 = Nat.card (GridPacking 1) at he
  rw [← count_eq_grid 1 (by decide)] at he
  omega

def family : Registration arena (type_of% @count_eq_grid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨count_eq_grid, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change count pattern 2 0 ≠ count pattern 2 1
    rw [count_zero, count_one]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_eq_grid) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core.CountGrid.unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core.CountGrid.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => count pattern 2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end CountGrid
end Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Core
