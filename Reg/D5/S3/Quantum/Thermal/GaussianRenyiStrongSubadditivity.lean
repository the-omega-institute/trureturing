import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for bosonic Gaussian Rényi strong subadditivity. -/

namespace Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity

open _root_.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
open _root_.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ n : ℕ, Σ _ : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ, Finset (Fin n))
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p α => gaussianRenyiEntropy α
    (reducedCovariance (Sigma.fst (Sigma.snd p)) (Sigma.snd (Sigma.snd p)))
    (reducedCovariance (symplecticForm (Sigma.fst p)) (Sigma.snd (Sigma.snd p))))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ),
    physicalCovariance V → ∀ A B C : Finset (Fin n),
      Disjoint A B → Disjoint A C → Disjoint B C → ∀ α : ℝ,
        0 < α → α ≤ 2 → α ≠ 1 →
          gaussianRenyiEntropy α (reducedCovariance V (A ∪ B))
              (reducedCovariance (symplecticForm n) (A ∪ B)) +
            gaussianRenyiEntropy α (reducedCovariance V (B ∪ C))
              (reducedCovariance (symplecticForm n) (B ∪ C)) ≥
          gaussianRenyiEntropy α (reducedCovariance V (A ∪ B ∪ C))
              (reducedCovariance (symplecticForm n) (A ∪ B ∪ C)) +
            R.readout () ⟨n, V, B⟩ α

lemma empty_entropy {n : ℕ} (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (α : ℝ) :
    gaussianRenyiEntropy α (reducedCovariance V ∅)
      (reducedCovariance (symplecticForm n) ∅) = 0 := by
  have : IsEmpty {p : Fin n × Fin 2 // p.1 ∈ (∅ : Finset (Fin n))} :=
    ⟨fun p => by simpa using p.property⟩
  unfold gaussianRenyiEntropy
  split_ifs <;> simp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hV : physicalCovariance (n := 0) 0 := by
    unfold physicalCovariance
      _root_.D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov
    constructor
    · ext i; exact Fin.elim0 i
    · convert (Matrix.PosSemidef.zero : (0 : Matrix (Fin 0) (Fin 0) ℂ).PosSemidef) using 1
      ext i; exact Fin.elim0 i
  have hh := h 0 0 hV ∅ ∅ ∅ (by simp) (by simp) (by simp)
    2 (by norm_num) (by norm_num) (by norm_num)
  let E := gaussianRenyiEntropy 2 (reducedCovariance (n := 0) 0 ∅)
    (reducedCovariance (symplecticForm 0) ∅)
  change E + 1 ≤ E + E at hh
  have he : E = 0 := empty_entropy 0 2
  rw [he] at hh
  norm_num at hh

lemma zero_entropy {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ω : Matrix ι ι ℝ) (α : ℝ) :
    gaussianRenyiEntropy α 0 Ω =
      (1 / 2 : ℝ) * ((Fintype.card ι : ℝ) * renyiFunction α 0) := by
  have hmap : (0 : Matrix ι ι ℝ).map Complex.ofReal = 0 := by ext; simp
  have hz : symplecticOperator 0 Ω = 0 := by simp [symplecticOperator, hmap]
  have hH : (symplecticOperator 0 Ω).IsHermitian := hz ▸ Matrix.isHermitian_zero
  have he : hH.eigenvalues = 0 := hH.eigenvalues_eq_zero_iff.mpr hz
  rw [gaussianRenyiEntropy, dite_eq_left hH]
  simp [he]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0, Finset.univ⟩, 1, 3, ?_⟩
  change gaussianRenyiEntropy 1 (reducedCovariance 0 Finset.univ) _ ≠
    gaussianRenyiEntropy 3 (reducedCovariance 0 Finset.univ) _
  have hr : reducedCovariance (n := 1) 0 Finset.univ = 0 := rfl
  rw [hr, zero_entropy, zero_entropy]
  have hc : Fintype.card {p : Fin 1 × Fin 2 //
      p.1 ∈ (Finset.univ : Finset (Fin 1))} = 2 := by decide
  rw [hc]
  norm_num [renyiFunction, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.result)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.unit
  realizationName := `Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p α => gaussianRenyiEntropy α
    (reducedCovariance (Sigma.fst (Sigma.snd p)) (Sigma.snd (Sigma.snd p)))
    (reducedCovariance (symplecticForm (Sigma.fst p)) (Sigma.snd (Sigma.snd p))))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
    definition := some {
      owner := `D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
      name := `D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.claim
      path := #[] }
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
