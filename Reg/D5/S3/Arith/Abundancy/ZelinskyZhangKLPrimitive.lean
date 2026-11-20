import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
import Reg.Support.SingleDependentReadout

/-! The complete unbounded source law with the witness as the selected observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ B : ℕ, ∃ n : ℕ,
    B < R.readout () () n ∧ 0 < n ∧ Deficient n ∧ KLPrimitive n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn, hpos, hdef, hprimitive⟩ := h 0
  change 0 < 0 at hn
  exact (Nat.lt_irrefl 0) hn

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    exact Nat.zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace SigmaPrimeMul

/-- Observe the original arithmetic function on the entire natural domain. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => sig n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p n : ℕ}, p.Prime → p.Coprime n →
    R.readout () () (p * n) = ((p : ℝ) + 1) * sig n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (p := 2) (n := 1) Nat.prime_two (by simp)
  norm_num [rejected, realize, sig] at bad

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.sig_prime_mul) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.sig_prime_mul,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change sig 0 ≠ sig 1
    norm_num [sig]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.sig_prime_mul)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.sig_prime_mul.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.SigmaPrimeMul.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SigmaPrimeMul

namespace KLPrimeMul

/-- Observe the original arithmetic function on the entire natural domain. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => KL n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p n : ℕ}, p.Prime → p.Coprime n →
    R.readout () () (p * n) = ((p : ℝ) + 1) * KL n +
      (p : ℝ) * sig n * Real.log ((p : ℝ) / (p - 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (p := 2) (n := 1) Nat.prime_two (by simp)
  norm_num [rejected, realize, KL, sig, Real.log_div] at bad
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.kl_prime_mul) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.kl_prime_mul,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change KL 0 ≠ KL 1
    norm_num [KL, Real.log_div] <;>
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.kl_prime_mul)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.kl_prime_mul.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.KLPrimeMul.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KLPrimeMul

end Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
