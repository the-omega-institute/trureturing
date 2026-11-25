import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination

/-! A source-bound audit of the strictly positive gain bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination
open _root_.D5.S3.Quantum.Divergence.UmegakiRareFlagBKM (block_diag_posDef)
open private Qubit Ray Qutrit D from D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination

namespace Reg.D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

set_option linter.unusedVariables false in
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (Cₚ F : Qubit) (h : Matrix (Fin 2) Unit ℂ)
    (ρ : Qutrit) (a lam e : ℝ) (hCₚ : Cₚ.PosDef)
    (hlam : 0 < lam) (hsmall : lam < 1 / 500) (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (hc : 11 / 19 ≤ Cₚ.trace.re + lam) (he : (Cₚ.trace.re + lam) / 3 ≤ e)
    (hfloor : lam • (1 : Qubit) ≤ Cₚ)
    (htr : F.trace.re + a = 1)
    (hlo : (4 / 3 : ℝ) • fromBlocks Cₚ 0 0 (lam • (1 : Ray)) ≤
      fromBlocks F h hᴴ (a • (1 : Ray)))
    (hhi : fromBlocks F h hᴴ (a • (1 : Ray)) ≤
      (7 / 3 : ℝ) • fromBlocks Cₚ 0 0 (lam • (1 : Ray))),
    let b := Cₚ.trace.re
    let c := b + lam
    let τ := b⁻¹ • Cₚ
    let F' := F + a • τ
    let C' := c • τ
    let C := fromBlocks Cₚ 0 0 (lam • (1 : Ray))
    let A := fromBlocks F h hᴴ (a • (1 : Ray))
    let A' := fromBlocks F' 0 0 (0 : Ray)
    let B' := fromBlocks C' 0 0 (e • (1 : Ray))
    let bound := (4 / 3 : ℝ) * lam * Real.log (1 + e / lam) -
      (12 / 55 : ℝ) * lam * (c / b) * Real.log (c / lam) -
      (a * (Real.log (a / (lam * (4 / 3))) - 1) + Real.log (c / b)) +
      ((a • τ)ᴴ * (a • τ)).trace.re / 2
    R.readout () () 0 bound ∧ bound ≤ D A' B' - D A (C + e • ρ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hbad
  let lam : ℝ := 1 / 600
  let a : ℝ := (5 / 3) * lam
  let e : ℝ := 2 / 5
  let Cₚ : Qubit := (359 / 1200 : ℝ) • 1
  let F : Qubit := (5 / 3 : ℝ) • Cₚ
  let h : Matrix (Fin 2) Unit ℂ := 0
  let ρ : Qutrit := (1 / 3 : ℝ) • 1
  let C : Qutrit := fromBlocks Cₚ 0 0 (lam • (1 : Ray))
  have hlam : 0 < lam := by norm_num [lam]
  have hsmall : lam < 1 / 500 := by norm_num [lam]
  have hCₚ : Cₚ.PosDef := Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 359 / 1200)
  have hρ : ρ.PosSemidef := Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hρtr : ρ.trace = 1 := by
    norm_num [ρ, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul, Fintype.card_sum]
  have hc : 11 / 19 ≤ Cₚ.trace.re + lam := by
    norm_num [Cₚ, lam, Matrix.trace_smul, Matrix.trace_one, Complex.smul_re, smul_eq_mul]
  have he : (Cₚ.trace.re + lam) / 3 ≤ e := by
    norm_num [Cₚ, lam, e, Matrix.trace_smul, Matrix.trace_one, Complex.smul_re, smul_eq_mul]
  have hfloor : lam • (1 : Qubit) ≤ Cₚ :=
    smul_le_smul_of_nonneg_right (by norm_num [lam]) (zero_le_one' _)
  have htr : F.trace.re + a = 1 := by
    norm_num [F, Cₚ, a, lam, Matrix.trace_smul, Matrix.trace_one, Complex.smul_re, smul_eq_mul]
  have hC : 0 ≤ C :=
    (block_diag_posDef Cₚ (1 : Ray) hCₚ Matrix.PosDef.one hlam).posSemidef.nonneg
  have hA : fromBlocks F h hᴴ (a • (1 : Ray)) = (5 / 3 : ℝ) • C := by
    simp [C, F, h, a, fromBlocks_smul, smul_smul]
  have hlo : (4 / 3 : ℝ) • C ≤ fromBlocks F h hᴴ (a • (1 : Ray)) := by
    rw [hA]
    exact smul_le_smul_of_nonneg_right (by norm_num) hC
  have hhi : fromBlocks F h hᴴ (a • (1 : Ray)) ≤ (7 / 3 : ℝ) • C := by
    rw [hA]
    exact smul_le_smul_of_nonneg_right (by norm_num) hC
  exact (hbad Cₚ F h ρ a lam e hCₚ hlam hsmall hρ hρtr hc he hfloor htr hlo hhi).1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 1
  change ((0 : ℝ) < 1) = ((1 : ℝ) < 1) at h
  exact (lt_irrefl _) (h.mp zero_lt_one)

def family : Registration arena (type_of% @strict_block_domination) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@strict_block_domination, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_block_domination) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination.strict_block_domination.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination
