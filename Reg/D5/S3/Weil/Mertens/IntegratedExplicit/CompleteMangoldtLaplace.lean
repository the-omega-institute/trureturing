import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import Reg.Support.SingleDependentReadout

/-!
Source-owner audit for the newly public complete finite Mangoldt localization.
The law retains the theorem's nonnegativity hypothesis, arbitrary real t,
implicit natural N and strict cutoff t<N, and the literal range sum. The
rejected constant-one realization fails at t=0,N=1. Actual dependence uses
actual Mangoldt ramps at t=0 and t=3; no auxiliary anchor or detached utility
is introduced.
-/

noncomputable section

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace

open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => mangoldtPart z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t : ℝ}, 0 ≤ t → ∀ {N : ℕ}, t < N →
    R.readout () () t = ∑ n ∈ Finset.range N, mangoldtRamp n t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (t := 0) (by norm_num) (N := 1) (by norm_num)
  change (1 : ℝ) = ∑ n ∈ Finset.range 1, mangoldtRamp n 0 at hb
  norm_num [mangoldtRamp] at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 3, ?_⟩
  change mangoldtPart 0 ≠ mangoldtPart 3
  have hzero : mangoldtPart 0 = 0 := by
    rw [@mangoldtPart_eq_range (t := 0) (by norm_num) (N := 1) (by norm_num)]
    norm_num [mangoldtRamp]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hthree : 0 < mangoldtPart 3 := by
    rw [@mangoldtPart_eq_range (t := 3) (by norm_num) (N := 4) (by norm_num)]
    have hterm : 0 < mangoldtRamp 2 3 := by
      rw [mangoldtRamp, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact mul_pos hlog (by norm_num)
    exact hterm.trans_le (Finset.single_le_sum
      (fun n _ => mangoldtRamp_nonneg n 3) (by norm_num : 2 ∈ Finset.range 4))
  rw [hzero]
  exact hthree.ne

def family : Registration arena
    (type_of% @mangoldtPart_eq_range) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mangoldtPart_eq_range, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mangoldtPart_eq_range) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace.mangoldtPart_eq_range
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ z => mangoldtPart z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
