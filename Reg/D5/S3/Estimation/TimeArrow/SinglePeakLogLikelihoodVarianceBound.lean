import D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
open Finset LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
universe u

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := ⟨{⟨()⟩}, fun x => by
    have hx : x = ⟨()⟩ := Subsingleton.elim _ _
    simp only [hx, Finset.mem_singleton]⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => 2 * x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} [Fintype X]
    (chi : X → ℝ) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1)
    (r q : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (M : ℕ) (hcard : Fintype.card X = 2 * M)
    (hplus : (univ.filter fun x => chi x = 1).card = M) (hM : 2 ≤ M)
    (hq : q = r / ((M : ℝ) - 1)),
    let P := kernel chi z r q (Fintype.card X)
    let k := (M : ℝ) - 1
    let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
    let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
    let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
    let Prev := Function.swap P
    let Lrev : (s : ℕ) → (Fin (s + 1) → X) → ℝ :=
      fun s x ↦ logLikelihoodSum chi z r q s (fun t ↦ x t.rev)
    (∀ u, |u| < 1 → psi u ≤ R.readout ⟨()⟩ () (phi u)) ∧
    J ≤ 0 ∧
    v ≤ 2 * I ∧
    0 ≤ I ∧
    (∀ s, pathVariance P s (logLikelihoodSum chi z r q s) ≤ 2 * s * I) ∧
    ∀ s, pathVariance Prev s (Lrev s) ≤ 2 * s * I

theorem actual_law : arena.Law actual := by
  exact uniform_single_peak_log_likelihood_variance_bound

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let chi : ULift.{u} (Fin 4) → ℝ := fun x => if x.down.val < 2 then 1 else -1
  have hchi : ∀ x, chi x = 1 ∨ chi x = -1 := by
    intro x
    dsimp [chi]
    split_ifs <;> simp
  have hplus : (univ.filter fun x => chi x = 1).card = 2 := by
    rw [Finset.card_filter]
    rw [← (Equiv.ulift.symm : Fin 4 ≃ ULift.{u} (Fin 4)).sum_comp]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    norm_num [chi]
  have hcase := h chi hchi ⟨0⟩ (by norm_num [chi]) (1/2) (1/2)
    (by norm_num) (by norm_num) 2 (by simp) hplus (by omega) (by norm_num)
  have impossible := hcase.1 0 (by norm_num)
  norm_num [rejected, realize, psi] at impossible

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (2 : ℝ) * 0 ≠ 2 * 1; norm_num⟩

register_information_theorem uniform_single_peak_log_likelihood_variance_bound in arena
  readout via (realize signature.{u} (fun _ _ x => 2 * x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

end Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
