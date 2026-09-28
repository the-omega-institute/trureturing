import D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization

universe u

def signature : Signature where
  Params := Σ ι : Type u, Σ _ : ι → ℝ, ℝ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p l => Real.sqrt (p.2.1 l)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

open scoped Classical in
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (_ha : ∀ l, 0 < a l) (_hsum : ∑ l, a l = 1)
    (ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1),
    let v : ι → ℝ := fun l => R.readout () ⟨ι, a, ε⟩ l
    let F : (ι → ℝ) → ℝ := fun x => (∑ l, v l * x l) ^ 2 - ε * ∑ l, (x l) ^ 2
    let X : ℝ → ι → ℝ := fun c l => min 1 (c * v l)
    let H : ℝ → Finset ι := fun c => Finset.univ.filter fun l => 1 ≤ c * v l
    let d : ℝ → ℝ := fun c =>
      ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c), a l
    let S : ℝ → ℝ := fun c => ∑ l ∈ H c, v l
    ∃ c : ℝ,
      (0 < c ∧
        (∑ l, min (a l) (v l / c)) = ε ∧
        (∀ l, 0 ≤ X c l ∧ X c l ≤ 1) ∧
        (∀ x, (∀ l, 0 ≤ x l ∧ x l ≤ 1) → F x ≤ F (X c)) ∧
        d c < ε ∧
        c = S c / (ε - d c) ∧
        F (X c) = ε * (S c) ^ 2 / (ε - d c) - ε * (H c).card) ∧
      (∀ c', 0 < c' → (∑ l, min (a l) (v l / c')) = ε → c' = c)

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have ht := h (ι := ULift.{u} Unit)
    (a := fun _ : ULift.{u} Unit => (1 : ℝ))
    (by intro; norm_num) (by simp) (1 / 2) (by norm_num) (by norm_num)
  dsimp [rejected, realize, signature] at ht
  obtain ⟨c, hc, _⟩ := ht
  have hroot := hc.2.1
  norm_num at hroot

open scoped Classical in
def registration : Registration arena.{u} (∀ {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (_ha : ∀ l, 0 < a l) (_hsum : ∑ l, a l = 1)
    (ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1),
    let v : ι → ℝ := fun l => Real.sqrt (a l)
    let F : (ι → ℝ) → ℝ := fun x => (∑ l, v l * x l) ^ 2 - ε * ∑ l, (x l) ^ 2
    let X : ℝ → ι → ℝ := fun c l => min 1 (c * v l)
    let H : ℝ → Finset ι := fun c => Finset.univ.filter fun l => 1 ≤ c * v l
    let d : ℝ → ℝ := fun c =>
      ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c), a l
    let S : ℝ → ℝ := fun c => ∑ l ∈ H c, v l
    ∃ c : ℝ,
      (0 < c ∧
        (∑ l, min (a l) (v l / c)) = ε ∧
        (∀ l, 0 ≤ X c l ∧ X c l ≤ 1) ∧
        (∀ x, (∀ l, 0 ≤ x l ∧ x l ≤ 1) → F x ≤ F (X c)) ∧
        d c < ε ∧
        c = S c / (ε - d c) ∧
        F (X c) = ε * (S c) ^ 2 / (ε - d c) - ε * (H c).card) ∧
      (∀ c', 0 < c' → (∑ l, min (a l) (v l / c')) = ε → c' = c)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨probe_threshold_optimization, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 2),
        (fun l => if l.down = 0 then (0 : ℝ) else 1), (1 / 2 : ℝ)⟩,
      ULift.up (0 : Fin 2), ULift.up (1 : Fin 2), ?_⟩
    dsimp [arena, actual, realize, signature]
    norm_num

register_information_theorem probe_threshold_optimization in arena
  readout via (realize signature.{u}
    (fun _ p l => Real.sqrt (p.2.1 l)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization
    coordinates := #[0, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "value", "body"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms rejected_law

end Reg.D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization
