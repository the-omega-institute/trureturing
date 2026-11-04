import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for fermionic Gaussian Rényi strong subadditivity. -/

namespace Reg.D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity

open _root_.D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity
open _root_.D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity (reducedCovariance)
open _root_.D5.S3.Quantum.Analysis.FermionicRenyiStieltjes (fermionicRenyiFunction)
open _root_.D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining (hRenyi)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

#print _root_.D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity.result
#print _root_.D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity.claim

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ n : ℕ, Σ _ : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ, Finset (Fin n))
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p α => fermionicGaussianRenyiEntropy α
    (reducedCovariance (Sigma.fst (Sigma.snd p)) (Sigma.snd (Sigma.snd p))))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ),
    physicalCovariance G → ∀ A B C : Finset (Fin n),
      Disjoint A B → Disjoint A C → Disjoint B C → ∀ α : ℝ,
        0 < α → α < 1 →
          fermionicGaussianRenyiEntropy α (reducedCovariance G (A ∪ B)) +
            fermionicGaussianRenyiEntropy α (reducedCovariance G (B ∪ C)) ≥
          fermionicGaussianRenyiEntropy α (reducedCovariance G (A ∪ B ∪ C)) +
            R.readout () ⟨n, G, B⟩ α

lemma empty_entropy {n : ℕ} (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (α : ℝ) :
    fermionicGaussianRenyiEntropy α (reducedCovariance G ∅) = 0 := by
  have : IsEmpty {p : Fin n × Fin 2 // p.1 ∈ (∅ : Finset (Fin n))} :=
    ⟨fun p => by simpa using p.property⟩
  unfold fermionicGaussianRenyiEntropy
  split_ifs <;> simp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hG : physicalCovariance (n := 0) 0 := by
    constructor
    · ext i
      exact Fin.elim0 i.1
    · have hH : (Complex.I • (0 : Matrix (Fin 0 × Fin 2) (Fin 0 × Fin 2) ℝ).map
          Complex.ofReal).IsHermitian := by
        convert (Matrix.isHermitian_zero :
          (0 : Matrix (Fin 0 × Fin 2) (Fin 0 × Fin 2) ℂ).IsHermitian) using 1
        ext i
        exact Fin.elim0 i.1
      exact ⟨hH, fun i => Fin.elim0 i.1⟩
  have hb := h 0 0 hG ∅ ∅ ∅ (by simp) (by simp) (by simp)
    (1 / 2) (by norm_num) (by norm_num)
  let E := fermionicGaussianRenyiEntropy (1 / 2) (reducedCovariance (n := 0) 0 ∅)
  change E + 1 ≤ E + E at hb
  have he : E = 0 := empty_entropy 0 (1 / 2)
  rw [he] at hb
  norm_num at hb

lemma zero_entropy {n : ℕ} (X : Finset (Fin n)) (α : ℝ) :
    fermionicGaussianRenyiEntropy α (reducedCovariance 0 X) =
      (1 / 2 : ℝ) * ((Fintype.card {p : Fin n × Fin 2 // p.1 ∈ X} : ℝ) *
        fermionicRenyiFunction α 0) := by
  have hz : Complex.I • (reducedCovariance (n := n) 0 X).map Complex.ofReal = 0 := by
    ext
    simp [reducedCovariance]
  have hH : (Complex.I • (reducedCovariance (n := n) 0 X).map Complex.ofReal).IsHermitian :=
    hz ▸ Matrix.isHermitian_zero
  have he : hH.eigenvalues = 0 := hH.eigenvalues_eq_zero_iff.mpr hz
  rw [fermionicGaussianRenyiEntropy, dite_eq_left hH]
  simp [he]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0, Finset.univ⟩, 0, 1, ?_⟩
  change fermionicGaussianRenyiEntropy 0 (reducedCovariance 0 Finset.univ) ≠
    fermionicGaussianRenyiEntropy 1 (reducedCovariance (n := 1) 0 Finset.univ)
  rw [zero_entropy, zero_entropy]
  have hc : Fintype.card {p : Fin 1 × Fin 2 //
      p.1 ∈ (Finset.univ : Finset (Fin 1))} = 2 := by decide
  rw [hc]
  norm_num [fermionicRenyiFunction, hRenyi]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p α => fermionicGaussianRenyiEntropy α
    (reducedCovariance (Sigma.fst (Sigma.snd p)) (Sigma.snd (Sigma.snd p))))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity
    definition := some {
      owner := `D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity
      name := `D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity.claim
      path := #[] }
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity
