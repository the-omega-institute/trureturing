import D5.S3.Quantum.Entanglement.ExponentialSectorKernel
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.ExponentialSectorKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => 1 / x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observation := ∀ (loss : ℕ → ℝ) (_horder : Monotone loss) (n : ℕ),
    (∀ w : Fin (n + 1) → ℝ, 0 ≤ energy n loss w) ∧
    (∀ i, 0 ≤ equilibriumWeight n loss i) ∧
    (∀ i : Fin (n + 1),
      ∑ j : Fin (n + 1), kernel loss i j * equilibriumWeight n loss j = 1) ∧
    (∑ i, equilibriumWeight n loss i) = normalizer n loss ∧
    0 < normalizer n loss ∧
    (fun i => equilibriumWeight n loss i / normalizer n loss) ∈
      stdSimplex ℝ (Fin (n + 1)) ∧
    energy n loss (fun i => equilibriumWeight n loss i / normalizer n loss) =
      observation.readout () () (normalizer n loss) ∧
    (∀ p ∈ stdSimplex ℝ (Fin (n + 1)),
      1 / normalizer n loss ≤ energy n loss p) ∧
    normalizer n loss = 1 +
      ∑ i : Fin n, Real.tanh ((loss (i + 1) - loss i) / 4) ∧
    1 - kernel loss 0 n ≤ 2 * (1 - 1 / normalizer n loss) ∧
    2 * (1 - 1 / normalizer n loss) ≤
      2 * (loss n - loss 0) / (4 + (loss n - loss 0)) ∧
    (∀ epsilon : ℝ, epsilon < 2 →
      (2 * (1 - 1 / normalizer n loss) ≤ epsilon ↔
        normalizer n loss - 1 ≤ epsilon / (2 - epsilon))) ∧
    ((∀ i < n, loss i < loss (i + 1)) → ∀ i, 0 < equilibriumWeight n loss i)

theorem actual_law : arena.Law actual := by
  intro loss horder n
  exact _root_.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result loss horder n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (fun _ => 0) (by intro i j hij; rfl) 0).2.2.2.2.2.2.1
  norm_num [energy, equilibriumWeight, normalizer, kernel, rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem _root_.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result
  in arena
  readout via (realize signature (fun _ _ x => 1 / x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms _root_.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result
#print axioms registration
end Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel
