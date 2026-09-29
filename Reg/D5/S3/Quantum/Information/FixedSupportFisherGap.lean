import D5.S3.Quantum.Information.FixedSupportFisherGap
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

namespace Reg.D5.S3.Quantum.Information.FixedSupportFisherGap
open _root_.D5.S3.Quantum.Information.FixedSupportFisherGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Finset
open scoped BigOperators
noncomputable section
universe u

abbrev signature : Signature where
  Params := (ι : Type u) × (ι → ℝ → ℝ)
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law O := ∀ {ι : Type u} [Fintype ι] (a R : ℝ) (x : ι → ℝ) (p : ι → ℝ → ℝ),
    0 < a → a < 1 →
    (∀ j, x j ∈ Icc (-1 : ℝ) 1) →
    (∀ u ∈ Ioo (2*a-1) 1, ∀ j, 0 ≤ p j u) →
    (∀ j, DifferentiableOn ℝ (p j) (Ioo (2*a-1) 1)) →
    (∀ u ∈ Ioo (2*a-1) 1, ∑ j, p j u = 1) →
    (∀ u ∈ Ioo (2*a-1) 1, ∑ j, p j u * x j = a) →
    (∀ u ∈ Ioo (2*a-1) 1, ∑ j, p j u * x j^2 = (1+u)/2) →
    (∀ u ∈ Ioo (2*a-1) 1,
      (∑ j ∈ univ.filter (fun j => 0 < p j u), (O.readout () ⟨ι,p⟩ j u)^2 / p j u) ≤
        R*(1-a^2)/((1-u)*(1+u-2*a^2))) →
    1 + a^2 / (1+4*a+2*(1+a)*Real.log 2)^2 ≤ R

def actual : Realization signature.{u} :=
  realize signature (fun _ p j => deriv (p.2 j)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

-- A single affine probability curve with all three moments, on the full open interval.
def support (j : ULift.{u} (Fin 3)) : ℝ := ![-1,0,1] j.down
def curve (j : ULift.{u} (Fin 3)) (t : ℝ) : ℝ := ![t/4,(1-t)/2,(2+t)/4] j.down

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hx : ∀ j, support.{u} j ∈ Icc (-1 : ℝ) 1 := by
    intro ⟨j⟩; fin_cases j <;> norm_num [support]
  have hp : ∀ t ∈ Ioo (2*(1/2 : ℝ)-1) 1, ∀ j, 0 ≤ curve.{u} j t := by
    intro t ht ⟨j⟩
    have ht0 : 0 < t := by linarith [ht.1]
    fin_cases j <;> simp [curve] <;> linarith [ht.2]
  have hd : ∀ j, DifferentiableOn ℝ (curve.{u} j) (Ioo (2*(1/2 : ℝ)-1) 1) := by
    intro ⟨j⟩; fin_cases j <;> change DifferentiableOn ℝ (fun t => _) _ <;>
      dsimp [curve] <;> fun_prop
  have h0 : ∀ t ∈ Ioo (2*(1/2 : ℝ)-1) 1, ∑ j, curve.{u} j t = 1 := by
    intro t _
    rw [← Equiv.sum_comp (Equiv.ulift.symm : Fin 3 ≃ ULift.{u} (Fin 3))]
    simp [curve, Fin.sum_univ_three]; ring
  have h1 : ∀ t ∈ Ioo (2*(1/2 : ℝ)-1) 1, ∑ j, curve.{u} j t * support j = (1/2 : ℝ) := by
    intro t _
    rw [← Equiv.sum_comp (Equiv.ulift.symm : Fin 3 ≃ ULift.{u} (Fin 3))]
    simp [curve, support, Fin.sum_univ_three]; ring
  have h2 : ∀ t ∈ Ioo (2*(1/2 : ℝ)-1) 1, ∑ j, curve.{u} j t * support j^2 = (1+t)/2 := by
    intro t _
    rw [← Equiv.sum_comp (Equiv.ulift.symm : Fin 3 ≃ ULift.{u} (Fin 3))]
    simp [curve, support, Fin.sum_univ_three]; ring
  have hh := h (1/2) 0 support curve (by norm_num) (by norm_num) hx hp hd h0 h1 h2
    (by intro t ht; simp [rejected, realize])
  have hn : 0 ≤ (1/2 : ℝ)^2 / (1+4*(1/2)+2*(1+1/2)*Real.log 2)^2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, (fun j t => if j.down then (0 : ℝ) else t)⟩,
      ⟨false⟩, ⟨true⟩, ?_⟩
    intro h
    have he := congrFun h 0
    norm_num [actual, realize] at he

register_information_theorem result in arena
  readout via (realize signature.{u} (fun _ p j => deriv (p.2 j)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Information.FixedSupportFisherGap
    coordinates := #[0, 5]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "fn", "arg", "arg", "body",
        "fn", "arg", "fn", "arg", "fn"], stateBinder := 16 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Quantum.Information.FixedSupportFisherGap
