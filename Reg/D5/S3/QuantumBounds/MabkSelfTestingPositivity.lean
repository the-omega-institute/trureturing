import D5.S3.QuantumBounds.MabkSelfTestingPositivity
import Reg.Support.DependentFamily

open _root_.D5.S3.QuantumBounds.MabkSelfTestingPositivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped Classical

noncomputable section
namespace Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity

abbrev signature : Signature where
  Params := Σ n : ℕ, Finset (Fin n)
  State := fun p => Fin p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => lambdaA p.1 p.2 v) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, 6 ≤ n → ∀ T : Finset (Fin n),
    (T.card = 1 ∨ T.card = 2) → ∀ v : Fin n → ℝ,
    (∀ i, 0 ≤ v i ∧ v i ≤ kappa) → 0 ≤ R.readout () ⟨n, T⟩ v

theorem zero_cube : ∀ i : Fin 6, 0 ≤ (0 : Fin 6 → ℝ) i ∧ (0 : Fin 6 → ℝ) i ≤ kappa := by
  have hr : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hr0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  intro i
  constructor
  · norm_num
  · change 0 ≤ 1 - 1 / Real.sqrt 2
    have := (div_le_one hr0).mpr hr
    linarith

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 6 (by norm_num) {0} (Or.inl (by simp)) 0 zero_cube
  norm_num [rejected, realize] at hb

private def sample : Fin 6 → ℝ := fun i => if i = 0 then 1 else 0

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨6, {0}⟩, 0, sample, ?_⟩
  have hJ : ({0} : Finset (Fin 6))ᶜ.Nonempty := by
    refine ⟨1, ?_⟩
    simp
  have hsample (j : Fin 6) (hj : j ∈ ({0} : Finset (Fin 6))ᶜ) : sample j = 0 := by
    simp only [mem_compl, mem_singleton] at hj
    simp [sample, hj]
  have hzero (f : ℝ → ℝ) :
      (∏ j ∈ ({0} : Finset (Fin 6))ᶜ, f (sample j)) = ∏ _j ∈ ({0} : Finset (Fin 6))ᶜ, f 0 :=
    prod_congr rfl fun j hj => congrArg f (hsample j hj)
  have hfull : (∏ j : Fin 6, sample j * (1 - ((1 + Real.sqrt 2) / Real.sqrt 2) * sample j)) = 0 := by
    apply prod_eq_zero (mem_univ (1 : Fin 6))
    norm_num [sample]
  have h1 : lambdaA 6 {0} (0 : Fin 6 → ℝ) = 1 := by
    simp [lambdaA, prod_const, card_compl]
  have h2 : lambdaA 6 {0} sample = 2 + Real.sqrt 2 := by
    let c := (1 + Real.sqrt 2) / Real.sqrt 2
    have hA : (∏ j ∈ ({0} : Finset (Fin 6))ᶜ, (1 - c * sample j)) = 1 := by
      apply prod_eq_one
      intro j hj
      rw [hsample j hj]
      ring
    have hX : (∏ j ∈ ({0} : Finset (Fin 6))ᶜ, (1 - sample j) ^ 2) = 1 := by
      apply prod_eq_one
      intro j hj
      rw [hsample j hj]
      norm_num
    have hAX : (∏ j ∈ ({0} : Finset (Fin 6))ᶜ,
        (1 - c * sample j) * (1 - sample j)) = 1 := by
      apply prod_eq_one
      intro j hj
      rw [hsample j hj]
      ring
    dsimp only [lambdaA]
    rw [hfull]
    simp only [prod_singleton]
    simp_rw [hzero]
    rw [hA, hX, hAX]
    norm_num [sample, prod_const, card_compl]
    have hr : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hr2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith only [hr2]
  change lambdaA 6 {0} 0 ≠ lambdaA 6 {0} sample
  rw [h1, h2]
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  linarith

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def selection : SourceSelection := {
  owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity
  definition := some {
    owner := `D5.S3.QuantumBounds.MabkSelfTestingPositivity
    name := `D5.S3.QuantumBounds.MabkSelfTestingPositivity.claim }
  coordinates := #[0, 2]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "arg"]
    stateBinder := 4 }] }

register_information_theorem result in arena
  readout via (realize signature (fun _ p v => lambdaA p.1 p.2 v) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

#print axioms registration

end Reg.D5.S3.QuantumBounds.MabkSelfTestingPositivity
