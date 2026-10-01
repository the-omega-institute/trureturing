import D5.S3.Quantum.Measurement.ContinuationEffectClosure
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.ContinuationEffectClosure
open LeanInformationAudit Matrix Filter Topology

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure

@[reducible] def signature : Signature where
  Params := ℕ
  State d := Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ W => W) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {J : Type} {κ : J → Type} [∀ j, Fintype (κ j)]
    (K : (j : J) → κ j → Matrix (Fin d) (Fin d) ℂ)
    (Z₀ : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ)) (hZ₀ : ∀ H ∈ Z₀, Hᴴ = H),
    (∀ n, d ^ 2 - Module.finrank ℝ Z₀ ≤ n →
        continuationSpace K Z₀ n = continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀)) ∧
      Z₀ ≤ continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀) ∧
      (∀ j, ∀ H ∈ continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀),
        branchDual K j H ∈ continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀)) ∧
      ∀ W : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ), Z₀ ≤ W →
        (∀ j, ∀ H ∈ W, branchDual K j H ∈ W) →
          continuationSpace K Z₀ (d ^ 2 - Module.finrank ℝ Z₀) ≤ R.readout () d W

theorem actual_law : arena.Law actual := by
  intro d J κ _ K Z₀ hZ₀
  exact continuationSpace_closure K Z₀ hZ₀

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let K : (j : Unit) → Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 0
  let Z₀ : Submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ) := Submodule.span ℝ {1}
  have hZ₀ : ∀ H ∈ Z₀, Hᴴ = H := by
    intro H hH
    induction hH using Submodule.span_induction with
    | mem X hX =>
        have : X = 1 := Set.mem_singleton_iff.mp hX
        subst X
        exact Matrix.conjTranspose_one
    | zero => exact Matrix.conjTranspose_zero
    | add X Y _ _ hX hY => rw [Matrix.conjTranspose_add, hX, hY]
    | smul r X _ hX =>
        rw [Matrix.conjTranspose_smul, hX]
        congr 1
  have hgood : ∀ n, Z₀ ≤ continuationSpace K Z₀ n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact le_trans ih le_sup_left
  have hbad := (h K Z₀ hZ₀).2.2.2 ⊤ le_top (fun _ _ _ => Submodule.mem_top)
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ Z₀ := Submodule.subset_span rfl
  have hz : (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := hbad (hgood _ h1)
  have he := congrFun (congrFun hz 0) 0
  norm_num at he

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨1, ⊥, ⊤, bot_ne_top⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem continuationSpace_closure in arena
  readout via (realize signature (fun _ _ W => W) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.ContinuationEffectClosure
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.ContinuationEffectClosure
