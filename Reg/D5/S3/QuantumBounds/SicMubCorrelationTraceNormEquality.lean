import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality
import Reg.Support.DependentFamily

/-! Source-bound audit of the SIC–complete-MUB trace-norm equality. -/

namespace Reg.D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality

open _root_.D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality
open _root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB (MUBFamily)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private def sicVectors (a b : ℝ) : Fin 4 → Fin 2 → ℂ :=
  ![![1, 0], ![(a : ℂ), b * a],
    ![(a : ℂ), -b * a / 2 + b * Complex.I / 2],
    ![(a : ℂ), -b * a / 2 - b * Complex.I / 2]]

private theorem sicVectors_laws (a b : ℝ) (ha : a ^ 2 = 1 / 3) (hb : b ^ 2 = 2) :
    (∀ i, star (sicVectors a b i) ⬝ᵥ sicVectors a b i = 1) ∧
    ∀ i j, i ≠ j → ‖star (sicVectors a b i) ⬝ᵥ sicVectors a b j‖ ^ 2 = 1 / 3 := by
  have ha4 : a ^ 4 = 1 / 9 := by rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ha]; norm_num
  have hb4 : b ^ 4 = 4 := by rw [show b ^ 4 = (b ^ 2) ^ 2 by ring, hb]; norm_num
  constructor
  · intro i
    fin_cases i <;> apply Complex.ext <;>
      simp [sicVectors, dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;>
      ring_nf <;> norm_num [ha, hb, ha4, hb4] <;>
      ring_nf <;> norm_num [ha, hb, ha4, hb4]
  · intro i j hij
    rw [← Complex.normSq_eq_norm_sq]
    fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
    all_goals
      simp [sicVectors, dotProduct, Fin.sum_univ_two, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im]
      ring_nf
      norm_num [ha, hb, ha4, hb4]
    all_goals ring_nf
    all_goals norm_num [ha, hb, ha4, hb4]

private def qubitSIC : SICFamily 2 :=
  ⟨sicVectors ((Real.sqrt 3)⁻¹) (Real.sqrt 2), by
    convert sicVectors_laws ((Real.sqrt 3)⁻¹) (Real.sqrt 2)
      (by rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num)
      (Real.sq_sqrt (by norm_num)) using 1
    norm_num⟩

private def mubMatrices (a : ℝ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, !![(a : ℂ), a; a, -a],
    !![(a : ℂ), a; a * Complex.I, -a * Complex.I]]

private theorem mubMatrices_unitary (a : ℝ) (ha : a ^ 2 = 1 / 2) (i : Fin 3) :
    mubMatrices a i ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    apply Complex.ext <;>
    simp [mubMatrices, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [ha]

private theorem mubMatrices_overlap (a : ℝ) (ha : a ^ 2 = 1 / 2)
    (i j : Fin 3) (hij : i ≠ j) (k l : Fin 2) :
    ‖((mubMatrices a i)ᴴ * mubMatrices a j) k l‖ ^ 2 = 1 / 2 := by
  have ha4 : a ^ 4 = 1 / 4 := by rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ha]; norm_num
  rw [← Complex.normSq_eq_norm_sq]
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals
    fin_cases k <;> fin_cases l <;>
      simp [mubMatrices, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
      ring_nf <;> norm_num [ha, ha4]

private def qubitMUB : MUBFamily 2 3 :=
  ⟨fun i => ⟨mubMatrices ((Real.sqrt 2)⁻¹) i,
      mubMatrices_unitary _ (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num) i⟩,
    mubMatrices_overlap _ (by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num)⟩

/-- The MUB correlation norm is observed as the bipartite matrix varies. -/
abbrev signature : Signature where
  Params := Σ dA : ℕ, Σ dB : ℕ,
    Σ _ : MUBFamily dA (dA + 1), MUBFamily dB (dB + 1)
  State p := Matrix (Fin p.1 × Fin p.2.1) (Fin p.1 × Fin p.2.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p ρ => traceNorm (mubCorrelation ρ p.2.2.1 p.2.2.2))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Retain both dimension bounds, both measurement families, and both density hypotheses. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (dA dB : ℕ), 2 ≤ dA → 2 ≤ dB →
    ∀ (SA : SICFamily dA) (SB : SICFamily dB)
      (MA : MUBFamily dA (dA + 1)) (MB : MUBFamily dB (dB + 1))
      (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      ρ.PosSemidef → ρ.trace = 1 →
        r.readout () ⟨dA, dB, MA, MB⟩ ρ =
          Real.sqrt (dA * (dA + 1)) * Real.sqrt (dB * (dB + 1)) *
            traceNorm (sicCorrelation ρ SA SB)

private def density : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 4 : ℂ) • 1

private theorem density_posSemidef : density.PosSemidef := by
  have hc := Complex.zero_le_real.mpr (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one] at hc
  exact Matrix.PosSemidef.one.smul hc

private theorem density_trace : density.trace = 1 := by
  norm_num [density, Matrix.trace_smul, Matrix.trace_one]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 2 (by norm_num) (by norm_num) qubitSIC qubitSIC
    qubitMUB qubitMUB density density_posSemidef density_trace
  change (-1 : ℝ) = _ at hbad
  have hn := traceNorm_nonneg (sicCorrelation density qubitSIC qubitSIC)
  norm_num at hbad
  linarith

private def oneMUB : MUBFamily 1 2 :=
  ⟨fun _ => 1, by intro i j _ k l; fin_cases k; fin_cases l; simp⟩

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, oneMUB, oneMUB⟩, 0, 1, ?_⟩
  change traceNorm (mubCorrelation 0 oneMUB oneMUB) ≠
    traceNorm (mubCorrelation 1 oneMUB oneMUB)
  have hz : mubCorrelation 0 oneMUB oneMUB = 0 := by
    ext p q
    simp [mubCorrelation]
  have he (p : Fin 2 × Fin 1) : oneMUB.effect p = 1 := by
    rcases p with ⟨p, a⟩
    fin_cases a
    ext i j
    fin_cases i; fin_cases j
    simp [MUBFamily.effect, MUBFamily.ket, oneMUB, Ket.apply]
  have ho : mubCorrelation 1 oneMUB oneMUB =
      rankOneDensity (fun _ : Fin 2 × Fin 1 => (1 : ℂ)) := by
    ext p q
    simp [mubCorrelation, he, rankOneDensity, Matrix.trace, Matrix.vecMulVec_apply]
  rw [hz, ho]
  have hn := congrArg Complex.re
    (_root_.D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_of_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 2 × Fin 1 => (1 : ℂ))))
  norm_num [Matrix.trace, Matrix.vecMulVec_apply] at hn
  simp only [rankOneDensity, hn]
  norm_num [_root_.D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality.unit
  realizationName := `Reg.D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p ρ => traceNorm (mubCorrelation ρ p.2.2.1 p.2.2.2))
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality
    definition := some {
      owner := `D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality
      name := `D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality.claim
      path := #[] }
    coordinates := #[0, 1, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

namespace TracePairingExt

universe u_1

abbrev signature : Signature where
  Params := Σ d : ℕ, Σ ι : Type u_1,
    Σ _ : ι → Matrix (Fin d) (Fin d) ℂ, Matrix (Fin d) (Fin d) ℂ
  State p := p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature (fun _ p i => (p.2.2.2 * p.2.2.1 i).trace) (fun e => nomatch e)

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law r := ∀ {d : ℕ} {ι : Type u_1} (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hP : Submodule.span ℂ (Set.range P) = ⊤) {X Y : Matrix (Fin d) (Fin d) ℂ},
    (∀ i, r.readout () ⟨d, ι, P, X⟩ i = (Y * P i).trace) → X = Y

private theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  let P : ULift.{u_1} (Matrix (Fin 1) (Fin 1) ℂ) → Matrix (Fin 1) (Fin 1) ℂ :=
    fun i => i.down
  have hP : Submodule.span ℂ (Set.range P) = ⊤ := by
    have hr : Set.range P = Set.univ := Set.range_eq_univ.mpr (fun X => ⟨ULift.up X, rfl⟩)
    rw [hr, Submodule.span_univ]
  have hh := h P hP (X := 1) (Y := 0) (by intro i; simp [rejected, realize])
  have he := congrArg (fun M => M 0 0) hh
  simp at he

private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨⟨1, ULift.{u_1} Bool, (fun i => if i.down then 1 else 0), 1⟩,
    ULift.up false, ULift.up true, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena.{u_1} (type_of% (@trace_pairing_ext.{u_1})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_pairing_ext, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_pairing_ext.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality.TracePairingExt.unit
  realizationName :=
    `Reg.D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality.TracePairingExt.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end TracePairingExt

end
end Reg.D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality
