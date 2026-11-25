import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport

/-! Source-bound registration of the strict relocated divergence comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport
open _root_.D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport.Transport
  (M₃ Ray coordinates compress nullRay divergence)

namespace Reg.D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

set_option linter.unusedVariables false in
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A C ρ : M₃) (e : ℝ) (hC : C.PosDef)
        (hlo : (4 / 3 : ℝ) • C ≤ A) (hhi : A ≤ (7 / 3 : ℝ) • C)
        (hA : A.trace = 1) (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
        (hc : 11 / 19 ≤ C.trace.re) (he : C.trace.re / 3 ≤ e)
        (hloss : (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re ≤ 1 / 114),
        ∃ (U : unitaryGroup (Fin 3) ℂ) (f : Fin 3 ≃ Fin 2 ⊕ Unit) (lam : ℝ),
          let E := coordinates U f
          let Cₚ := (E C).toBlocks₁₁
          let τ := (Cₚ.trace.re)⁻¹ • Cₚ
          let T := (compress τ).comp E.toLinearMap
          let A' := T A
          let C' := T C
          0 < lam ∧ lam < 1 / 500 ∧ lam • (1 : M₃) ≤ C ∧
            E C = fromBlocks Cₚ 0 0 (lam • (1 : Ray)) ∧
            τ.PosDef ∧ τ.trace = 1 ∧ A'.PosSemidef ∧ A'.trace = 1 ∧
            C'.PosSemidef ∧ C'.trace = C.trace ∧ A'.rank ≤ 2 ∧ C'.rank ≤ 2 ∧
            nullRay.PosSemidef ∧ nullRay.trace = 1 ∧ (C' + e • nullRay).PosDef ∧
            (∀ X, X.PosSemidef → (T X).PosSemidef ∧ (T X).trace = X.trace ∧ (T X).rank ≤ 2) ∧
            (∀ (ι : Type) [Fintype ι] (X : ι → M₃) (p γ : ι → ℝ),
              A = ∑ i, p i • X i → C = ∑ i, γ i • X i →
              A' = ∑ i, p i • T (X i) ∧ C' + e • nullRay = (∑ i, γ i • T (X i)) + e • nullRay) ∧
            R.readout () () (divergence A (C + e • ρ)) (divergence A' (C' + e • nullRay))

set_option maxHeartbeats 800000 in
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hbad
  let lam : ℝ := 1 / 10000
  let e : ℝ := 1 / 5
  let d (i : Fin 3) : ℝ := if i = 0 then lam else 5999 / 20000
  let C : M₃ := diagonal fun i => (d i : ℂ)
  let A : M₃ := (5 / 3 : ℝ) • C
  let v : Fin 3 → ℂ := Pi.single 0 1
  let ρ : M₃ := vecMulVec v (star v)
  have hC : C.PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    apply Complex.pos_iff.mpr
    constructor
    · change 0 < d i
      by_cases hi : i = 0 <;> norm_num [d, hi, lam]
    · rfl
  have htr : C.trace = (3 / 5 : ℝ) := by
    change (diagonal fun i => (d i : ℂ)).trace = _
    rw [Matrix.trace_diagonal, Fin.sum_univ_succ, Fin.sum_univ_two]
    norm_num [d, lam]
  have hA : A.trace = 1 := by
    norm_num [A, Matrix.trace_smul, htr, Complex.real_smul]
  have hlo : (4 / 3 : ℝ) • C ≤ A :=
    smul_le_smul_of_nonneg_right (by norm_num) hC.posSemidef.nonneg
  have hhi : A ≤ (7 / 3 : ℝ) • C :=
    smul_le_smul_of_nonneg_right (by norm_num) hC.posSemidef.nonneg
  have hfloor : lam • (1 : M₃) ≤ C := by
    apply Matrix.le_iff.mpr
    change (diagonal (fun i => (d i : ℂ)) - lam • (1 : M₃)).PosSemidef
    rw [← diagonal_one, ← diagonal_smul]
    have hconst : lam • (fun _ : Fin 3 => (1 : ℂ)) = fun _ => (lam : ℂ) := by
      funext i
      simp [Complex.real_smul]
    rw [hconst]
    rw [diagonal_sub, Matrix.posSemidef_diagonal_iff]
    intro i
    have hi : lam ≤ d i := by by_cases hz : i = 0 <;> norm_num [d, hz, lam]
    exact Complex.nonneg_iff.mpr ⟨by simpa using sub_nonneg.mpr hi, by simp⟩
  have hv : star v ⬝ᵥ v = 1 := by
    simp [v, dotProduct, Pi.single_apply]
  have hev : C *ᵥ v = (lam : ℂ) • v := by
    change (diagonal fun i => (d i : ℂ)) *ᵥ Pi.single 0 1 = (lam : ℂ) • Pi.single 0 1
    rw [Matrix.diagonal_mulVec_single]
    ext i
    by_cases hi : i = 0 <;> simp [d, hi]
  open _root_.D5.S3.Quantum.Divergence.UmegakiNullReferencePenalty in
  obtain ⟨hρ, hρtr, hcost⟩ := log_increment_eq_of_eigenvector
    C v (5 / 3) lam e (by norm_num [lam]) (by norm_num [e]) hfloor hv hev
  have hloss : (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re ≤ 1 / 114 := by
    change (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re =
      (5 / 3 : ℝ) * lam * Real.log (1 + e / lam) at hcost
    rw [hcost]
    have hlog := Real.log_le_log (by norm_num [e, lam] : 0 < 1 + e / lam)
      (by norm_num [e, lam] : 1 + e / lam ≤ (2 : ℝ) ^ (12 : ℕ))
    rw [Real.log_pow] at hlog
    norm_num [e, lam] at hlog ⊢
    linarith only [hlog, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  obtain ⟨U, f, l, h⟩ := hbad A C ρ e hC hlo hhi hA hρ hρtr
    (by rw [htr]; norm_num) (by rw [htr]; norm_num [e]) hloss
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 1
  change ((0 : ℝ) < 1) = ((1 : ℝ) < 1) at h
  exact (lt_irrefl _) (h.mp zero_lt_one)

def family : Registration arena (type_of% @strict_spectral_transport) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@strict_spectral_transport, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_spectral_transport) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport.strict_spectral_transport.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport.family
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
    owner := `D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
        "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport
