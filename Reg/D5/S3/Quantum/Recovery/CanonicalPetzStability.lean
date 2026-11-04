import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.CanonicalPetzStability
import Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
import Reg.Support.SingleDependentReadout

/-! The full fixed-channel theorem is reconstructed with its actual trace inequality as readout. -/

noncomputable section
universe u v
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open _root_.D5.S3.Quantum.Recovery.CanonicalPetzStability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Recovery.CanonicalPetzStability

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (σ : DensityState a),
    let K := (actual_kraus_representation Φ).kraus
    let H := cfc Real.sqrt (CStarMatrix.ofMatrix.symm σ.1)
    let Q := CStarMatrix.ofMatrix.symm (Φ.mapState σ).1
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    ∃ recovery : QuantumChannel b a,
      (∀ X : Matrix b b ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ c, H * (K c)ᴴ * W * X * W * K c * H) +
            Matrix.trace ((1 - P) * X) • CStarMatrix.ofMatrix.symm σ.1) ∧
      recovery.mapState (Φ.mapState σ) = σ ∧
      ∀ (ρ : DensityState a) (support : SupportContained ρ σ),
        let M := supported_relative_modular_model Φ ρ σ support
        ∀ (m L : ℝ), 0 < m → 0 ≤ L →
          m • (1 : Matrix (M.data.J × M.data.I) (M.data.J × M.data.I) ℂ) ≤ M.data.A →
          m • (1 : Matrix (M.data.L × M.data.K) (M.data.L × M.data.K) ℂ) ≤ M.data.B →
          (∀ ji : M.data.J × M.data.I, M.data.sj ji.1 / M.data.ri ji.2 ≤ L) →
          R.readout () ()
            (traceNorm (CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1 -
              CStarMatrix.ofMatrix.symm ρ.1))
            ((16 / Real.pi) * Real.sqrt (L / m) *
              (finiteTraceLogRelativeEntropy ρ σ -
                finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) ^
                  (1 / 4 : ℝ))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{v} Unit
  let ρ : DensityState a := ⟨1, zero_le_one, by simp [Matrix.trace, Matrix.diag, CStarMatrix.one_apply_eq]⟩
  let Φ : QuantumChannel a b := {
    toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b))
    trace_preserving := by
      intro X
      change Matrix.trace (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b) X) = Matrix.trace X
      simp [Matrix.trace, Matrix.diag, CStarMatrix.reindexₐ_apply, Matrix.reindex_apply,
        Matrix.submatrix_apply]
      change X ((Equiv.ofUnique a b).symm default) ((Equiv.ofUnique a b).symm default) =
        X default default
      simp only [Subsingleton.elim ((Equiv.ofUnique a b).symm default) (default : a)] }
  obtain ⟨recovery, _, _, hb⟩ := @h a b inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance Φ ρ
  let M := supported_relative_modular_model Φ ρ ρ (supportContained_refl ρ)
  obtain ⟨r, hr, hAr⟩ :=
    _root_.Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.positive_floor M.data.A M.hA
  obtain ⟨s, hs, hBs⟩ :=
    _root_.Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.positive_floor M.data.B M.hB
  have hmin : 0 < min r s := lt_min hr hs
  have hAf : min r s • (1 : Matrix (M.data.J × M.data.I) _ ℂ) ≤ M.data.A :=
    (smul_le_smul_of_nonneg_right (min_le_left r s) zero_le_one).trans hAr
  have hBf : min r s • (1 : Matrix (M.data.L × M.data.K) _ ℂ) ≤ M.data.B :=
    (smul_le_smul_of_nonneg_right (min_le_right r s) zero_le_one).trans hBs
  let L := ∑ ji : M.data.J × M.data.I, |M.data.sj ji.1 / M.data.ri ji.2|
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hL (ji : M.data.J × M.data.I) : M.data.sj ji.1 / M.data.ri ji.2 ≤ L :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg
      (M.data.sj i.1 / M.data.ri i.2)) (Finset.mem_univ ji))
  exact hb ρ (supportContained_refl ρ) (min r s) L hmin hL0 hAf hBf hL

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v}
    (type_of% @supported_entropy_defect_fixed_petz_trace_stability.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@supported_entropy_defect_fixed_petz_trace_stability, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@supported_entropy_defect_fixed_petz_trace_stability.{u,v})
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.CanonicalPetzStability.supported_entropy_defect_fixed_petz_trace_stability.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.CanonicalPetzStability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Recovery.CanonicalPetzStability
