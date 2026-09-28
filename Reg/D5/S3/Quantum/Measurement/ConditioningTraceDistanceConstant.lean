import D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
open _root_.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant
open _root_.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x⁻¹) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law W := ∀
    {d : ℕ} (hd : 2 ≤ d) (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosDef),
    let h0 : 0 < d := by omega
    letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp h0
    (∀ ρ σ : DensityState (Fin d),
      W.readout () () (greatestEigenvalue R hR / leastEigenvalue R hR) * traceDistance ρ σ ≤
        traceDistance (conditionedState h0 R hR ρ)
          (conditionedState h0 R hR σ) ∧
      traceDistance (conditionedState h0 R hR ρ)
          (conditionedState h0 R hR σ) ≤
        (greatestEigenvalue R hR / leastEigenvalue R hR) * traceDistance ρ σ) ∧
      (∀ ρ : DensityState (Fin d),
        leastEigenvalue R hR = greatestEigenvalue R hR →
          conditionedState h0 R hR ρ = ρ) ∧
      IsLUB {x : ℝ | ∃ ρ σ : DensityState (Fin d),
        ρ ≠ σ ∧
          x = traceDistance (conditionedState h0 R hR ρ)
              (conditionedState h0 R hR σ) /
            traceDistance ρ σ} (greatestEigenvalue R hR / leastEigenvalue R hR)

theorem actual_law : arena.Law actual := by
  exact conditioning_trace_distance_constant

private theorem identity_extremes :
    leastEigenvalue (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one =
      greatestEigenvalue (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one := by
  let hR : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosDef := Matrix.PosDef.one
  have heigs : hR.isHermitian.eigenvalues = fun _ => (1 : ℝ) := by
    funext i
    have hi : hR.isHermitian.eigenvalues i ∈
        spectrum ℝ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hR.isHermitian.spectrum_real_eq_range_eigenvalues]
      exact ⟨i, rfl⟩
    simpa only [spectrum.one_eq, Set.mem_singleton_iff] using hi
  change Finset.univ.inf' Finset.univ_nonempty hR.isHermitian.eigenvalues =
    Finset.univ.sup' Finset.univ_nonempty hR.isHermitian.eigenvalues
  rw [heigs]
  simp

private def projector (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single i i 1

private theorem projector_psd (i : Fin 2) : (projector i).PosSemidef := by
  rw [projector, Matrix.single_eq_single_vecMulVec_single]
  simpa using Matrix.posSemidef_vecMulVec_self_star (Pi.single i (1 : ℂ))

private theorem projector_trace (i : Fin 2) : (projector i).trace = 1 := by
  simp [projector, Matrix.trace]

private def basisState (i : Fin 2) : DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix (projector i),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (projector_psd i).nonneg,
    projector_trace i⟩

private theorem basis_distance : traceDistance (basisState 0) (basisState 1) = 1 := by
  have hstar : (projector 0)ᴴ = projector 0 := (projector_psd 0).isHermitian.eq
  have hid : projector 0 * projector 0 = projector 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projector, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]
  have horth : projector 1 * projector 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projector, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]
  have hcomp : 1 - projector 0 = projector 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [projector, Matrix.single_apply, Matrix.one_apply]
  let K : Unit → Matrix (Fin 2) (Fin 2) ℂ := fun _ => projector 0
  have hB : (∑ i, (K i)ᴴ * K i) ≤ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [K, Finset.univ_unique, Finset.sum_singleton, hstar, hid]
    apply sub_nonneg.mp
    rw [hcomp]
    exact (projector_psd 1).nonneg
  have hb := (branch_conditioned_trace_distance (projector 0) (projector 1) K
    (projector_psd 0) (projector_trace 0)
    (projector_psd 1) (projector_trace 1) hB).1
  have hlower : 1 ≤ traceDistance (basisState 0) (basisState 1) := by
    change 1 ≤ traceNorm (projector 0 - projector 1) / 2
    simpa [K, hstar, hid, horth, projector_trace] using hb
  exact le_antisymm (traceDistance_le_one _ _) hlower

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfixed (ρ : DensityState (Fin 2)) :
      conditionedState (by omega) (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one ρ = ρ :=
    (conditioning_trace_distance_constant (by omega)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one).2.1 ρ identity_extremes
  have impossible := (h (d := 2) (by omega)
    (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one).1 (basisState 0) (basisState 1) |>.1
  change 2 * traceDistance (basisState 0) (basisState 1) ≤
    traceDistance (conditionedState _ _ _ (basisState 0))
      (conditionedState _ _ _ (basisState 1)) at impossible
  rw [hfixed, hfixed, basis_distance] at impossible
  norm_num at impossible

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (0 : ℝ)⁻¹ ≠ 1⁻¹; norm_num⟩

register_information_theorem conditioning_trace_distance_constant in arena
  readout via (realize signature (fun _ _ x => x⁻¹) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body",
        "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

end Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant
