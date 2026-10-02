import D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open MeasureTheory ProbabilityTheory Matrix LeanInformationAudit
open scoped CStarAlgebra MatrixOrder ComplexOrder ComplexConjugate ENNReal BigOperators Kronecker

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.seminormedAddCommGroup
local instance (I : Type*) : MeasurableSpace (Matrix I I ℂ) :=
  inferInstanceAs (MeasurableSpace (I → I → ℂ))
local instance (I : Type*) [Fintype I] : ContinuousENorm (Matrix I I ℂ) :=
  inferInstanceAs (ContinuousENorm (I → I → ℂ))

namespace Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw

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
  realize signature (fun _ _ β => β) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law W := ∀ {A : Type} [Fintype A] [DecidableEq A]
    (e : ℕ) (he : 2 ≤ e) (β : ℝ) (hβ : 0 < β)
    (N : ℕ) (F : Fin (N+1) → Type u) [∀ i, MeasurableSpace (F i)]
    (D : Type u) [MeasurableSpace D] (P : FiniteStoppedPolicy N F D A)
    (H_A : Matrix A A ℂ) (hH_A : H_A.IsHermitian)
    (h₀ : F (historyIndex N 0)) (ρ₀ : Matrix A A ℂ) (hρ₀ : ρ₀.PosSemidef)
    (hρ₀trace : Matrix.trace ρ₀ = 1)
    (G : DensityState (Fin e) → ∀ i, ActualHistory (F i) (A × Fin e))
    (hinit : ∀ σ, (G σ (historyIndex N 0)).law = Measure.dirac h₀)
    (hproduct : ∀ σ, (G σ (historyIndex N 0)).density =ᵐ[(G σ (historyIndex N 0)).law]
      (fun _ => ρ₀ ⊗ₖ CStarMatrix.ofMatrix.symm σ.1))
    (hnormalized : ∀ σ n hn, ∀ᵐ h ∂(G σ (historyIndex N n)).law, h ∉ P.stop n hn →
      ∀ X : Matrix A A ℂ, Matrix.trace (CStarMatrix.ofMatrix.symm
        ((P.stage n hn).operation h Set.univ (CStarMatrix.ofMatrix X))) = Matrix.trace X)
    (hphysical : ∀ σ n hn E, MeasurableSet E → ∀ i j,
      (∫ h in E, (G σ (historyIndex N (n+1))).density h i j ∂(G σ (historyIndex N (n+1))).law) =
        ∫ h, actualFiniteStep P H_A n hn h E ((G σ (historyIndex N n)).density h) i j
          ∂(G σ (historyIndex N n)).law),
    letI : NeZero e := ⟨by omega⟩
    let θ := fun σ : DensityState (Fin e) => (Real.log e - vonNeumannEntropy σ) / W.readout () () β
    ∃ μ : Measure (F (historyIndex N N)), IsProbabilityMeasure μ ∧
      (∀ σ, (G σ (historyIndex N N)).law = μ) ∧
      (∀ σ, (G σ (historyIndex N N)).law.map (P.record (historyIndex N N)) =
        μ.map (P.record (historyIndex N N))) ∧
      (∀ σ n hn, ∀ E : Set (ℕ × D), MeasurableSet E →
        (G σ (historyIndex N (n+1))).law ((P.stage n hn).preceding ⁻¹' P.stop n hn ∩
          P.record (historyIndex N (n+1)) ⁻¹' E) =
          (G σ (historyIndex N n)).law (P.stop n hn ∩ P.record (historyIndex N n) ⁻¹' E)) ∧
      (⨅ κ : RealOutput (ℕ × D), ⨆ σ : DensityState (Fin e),
        ∫⁻ z : ℝ, ENNReal.ofReal |z - θ σ|
          ∂(((G σ (historyIndex N N)).law.map (P.record (historyIndex N N))).bind κ.kernel)) =
        ENNReal.ofReal (Real.log e / (2 * β))

theorem actual_law : arena.{u}.Law actual := by
  exact visible_adaptive_record_law_and_absolute_minimax

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q := PUnit.{u+1}
  letI : MeasurableSpace Q := ⊤
  let P : FiniteStoppedPolicy 0 (fun _ => Q) Q Unit :=
    { stop := fun n hn => False.elim (by omega)
      measurable_stop := fun n hn => False.elim (by omega)
      stage := fun n hn => False.elim (by omega)
      time := fun n hn => False.elim (by omega)
      measurable_time := fun n hn => False.elim (by omega)
      cemetery := fun n hn => False.elim (by omega)
      measurable_cemetery := fun n hn => False.elim (by omega)
      preceding_cemetery := fun n hn => False.elim (by omega)
      stopped_cemetery := fun n hn => False.elim (by omega)
      record := fun _ _ => (0, PUnit.unit)
      measurable_record := fun _ => measurable_const
      stopped_record := fun n hn => False.elim (by omega)
      active_length := fun n hn => False.elim (by omega) }
  have hσ (σ : DensityState (Fin 2)) : (CStarMatrix.ofMatrix.symm σ.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1)
  let G : DensityState (Fin 2) → ∀ _ : Fin 1, ActualHistory Q (Unit × Fin 2) := fun σ _ =>
    { law := Measure.dirac PUnit.unit
      probability := inferInstance
      density := fun _ => (1 : Matrix Unit Unit ℂ) ⊗ₖ CStarMatrix.ofMatrix.symm σ.1
      measurable_density := measurable_const
      integrable_density := integrable_const _
      state_density := fun _ => ⟨Matrix.PosSemidef.one.kronecker (hσ σ), by
        have ht : Matrix.trace (CStarMatrix.ofMatrix.symm σ.1) = 1 := σ.2.2
        rw [Matrix.trace_kronecker, ht, mul_one]
        simp⟩ }
  obtain ⟨μ, hprob, hlaw, hrecord, hstop, hrisk⟩ :=
    h (A := Unit) 2 (by norm_num) 1 (by norm_num) 0 (fun _ => Q) Q P
      0 Matrix.isHermitian_zero PUnit.unit 1 Matrix.PosSemidef.one (by simp) G
      (fun _ => rfl) (fun _ => Filter.EventuallyEq.rfl)
      (fun σ n hn => False.elim (by omega))
      (fun σ n hn => False.elim (by omega))
  have hzero : (⨅ κ : RealOutput (ℕ × Q), ⨆ σ : DensityState (Fin 2),
      ∫⁻ z : ℝ, ENNReal.ofReal |z|
        ∂(((G σ (historyIndex 0 0)).law.map (P.record (historyIndex 0 0))).bind κ.kernel)) = 0 := by
    apply le_antisymm
    · let κ : RealOutput (ℕ × Q) := ⟨Kernel.const _ (Measure.dirac (0 : ℝ)), inferInstance⟩
      refine (iInf_le _ κ).trans (iSup_le fun σ => ?_)
      change (∫⁻ z : ℝ, ENNReal.ofReal |z|
        ∂(((G σ (historyIndex 0 0)).law.map (P.record (historyIndex 0 0))).bind
          (fun _ => Measure.dirac (0 : ℝ)))) ≤ 0
      haveI : IsProbabilityMeasure
          ((G σ (historyIndex 0 0)).law.map (P.record (historyIndex 0 0))) := by
        constructor
        rw [Measure.map_apply (P.measurable_record _) MeasurableSet.univ]
        simp [G]
      rw [Measure.bind_const, measure_univ, one_smul, lintegral_dirac]
      simp
    · exact bot_le
  have hrisk' : (⨅ κ : RealOutput (ℕ × Q), ⨆ σ : DensityState (Fin 2),
      ∫⁻ z : ℝ, ENNReal.ofReal |z|
        ∂(((G σ (historyIndex 0 0)).law.map (P.record (historyIndex 0 0))).bind κ.kernel)) =
      ENNReal.ofReal (Real.log 2 / 2) := by
    simpa only [rejected, realize, signature, div_zero, sub_zero, mul_one, Nat.cast_ofNat] using hrisk
  have hpos : 0 < Real.log (2 : ℝ) / 2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hne := ENNReal.ofReal_pos.mpr hpos
  rw [hzero] at hrisk'
  exact (ne_of_gt hne) hrisk'.symm

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact False.elim (hji (Subsingleton.elim j i))
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
  norm_num [actual, realize, signature]

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem visible_adaptive_record_law_and_absolute_minimax in arena
  readout via (realize signature (fun _ _ β => β) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value", "body", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw
