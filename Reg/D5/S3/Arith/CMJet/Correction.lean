import D5.S3.Arith.CMJet.Correction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The restricted recurrence is observed as the column varies. -/

noncomputable section

namespace Reg.D5.S3.Arith.CMJet.Correction

open LeanInformationAudit
open _root_.D5.S3.Arith.CMJet
open _root_.D5.S3.Arith.CMJet.ActualRestricted
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open Polynomial
open scoped Polynomial

abbrev readoutSignature : Signature :=
  signature (Σ _ : ℕ, Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization readoutSignature :=
  realize readoutSignature
    (fun _ phk j => jet phk.2.1 (phk.1 + phk.2.2) j) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature
    (fun _ phk j => jet phk.2.1 (phk.1 + phk.2.2) j + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ (p : ℕ) [Fact p.Prime], 2 < p → Odd p → ∀ (h k j : ℕ),
    (R.readout () ⟨p, h, k⟩ j : ZMod p) =
      cmLambda p * (jet h (k + 1) j : ZMod p) +
        (k : ZMod p) * (2 * (h : ZMod p) * atO (iter (p - 1) ((x (ZMod p)) ^ 2))) *
          (jet h (k - 1) j : ZMod p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbad := h 3 (by decide) (by decide) 0 0 0
  change ((jet 0 (3 + 0) 0 + 1 : ℤ) : ZMod 3) = _ at hbad
  push_cast at hbad
  have hgood := integer_jet_recurrence 3 (by decide) (by decide) 0 0 0
  simp only [Nat.cast_zero, zero_mul, add_zero] at hbad hgood
  have heq : (jet 0 3 0 : ZMod 3) + 1 = (jet 0 3 0 : ZMod 3) := hbad.trans hgood.symm
  exact one_ne_zero (add_left_cancel (heq.trans (add_zero _).symm))

private theorem sample (j : ℕ) : (jet 1 4 j : ZMod 3) = (jet 1 0 j : ZMod 3) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl : cmLambda 3 = 0 := by
    have hs := Q_iter_monomial_support (A := ZMod 3) 1 1 1 (by decide)
    rw [cmLambda, coeff_derivative]
    norm_num at hs ⊢
    rw [hs]
  have he : atO (iter 2 ((x (ZMod 3)) ^ 2)) = 2 := by
    rw [x_pow, iter_two_poly, Q_X_pow]
    norm_num [atO_apply, coeff_X_pow]
  have h := integer_jet_recurrence 3 (by decide) (by decide) 1 1 j
  change (jet 1 4 j : ZMod 3) = cmLambda 3 * (jet 1 2 j : ZMod 3) +
    1 * (2 * 1 * atO (iter 2 ((x (ZMod 3)) ^ 2))) * (jet 1 0 j : ZMod 3) at h
  rw [hl, he, zero_mul, zero_add, one_mul, mul_one, show (2 : ZMod 3) * 2 = 1 by decide,
    one_mul] at h
  exact h

def family : Registration arena (type_of% @integer_jet_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integer_jet_recurrence, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨3, 1, 1⟩, 0, 1, ?_⟩
    change jet 1 4 0 ≠ jet 1 4 1
    intro heq
    have hcast : (jet 1 4 0 : ZMod 3) = (jet 1 4 1 : ZMod 3) :=
      congrArg (fun z : ℤ => (z : ZMod 3)) heq
    simp [sample, jet_zero_order] at hcast

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@integer_jet_recurrence) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CMJet.Correction.unit
  realizationName := `Reg.D5.S3.Arith.CMJet.Correction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature
    (fun _ phk j => jet phk.2.1 (phk.1 + phk.2.2) j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.CMJet.Correction
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.CMJet.Correction
