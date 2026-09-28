import D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
open Finset LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
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
  realize signature (fun _ _ x => phi x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} [Fintype X]
    (chi : X → ℝ) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1)
    (r q : ℝ) (_hr0 : 0 < r) (_hr1 : r < 1) (M : ℕ) (hcard : Fintype.card X = 2 * M)
    (hplus : (univ.filter fun x => chi x = 1).card = M) (hM : 2 ≤ M)
    (hq : q = r / ((M : ℝ) - 1)),
    let P := kernel chi z r q (Fintype.card X)
    let L := fun x y => Real.log ((Fintype.card X : ℝ) * P x y)
    let k := (M : ℝ) - 1
    let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
    let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
    let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
    (∀ x, ∑ y, P x y * L x y = R.readout ⟨()⟩ () (profile chi z r q x)) ∧
    (∀ y, ∑ x, P x y * L x y = I + J * chi y) ∧
    (∀ n, pathExpectation P (n + 1)
      (fun x => logIncrement chi z r q (Fin.last n) x) = I) ∧
    pathCovariance P 2 (fun x => logIncrement chi z r q 0 x)
      (fun x => logIncrement chi z r q 1 x) = I * J ∧
    (∀ j, 2 ≤ j → pathCovariance P (j + 1) (fun x => logIncrement chi z r q 0 x)
      (fun x => logIncrement chi z r q (Fin.last j) x) = 0) ∧
    ∀ s, 1 ≤ s → pathVariance P s (logLikelihoodSum chi z r q s) =
      (s : ℝ) * v + 2 * ((s - 1 : ℕ) : ℝ) * I * J

theorem actual_law : arena.Law actual := by
  exact exact_single_peak_log_likelihood_covariances

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
  have impossible := hcase.1 (⟨2⟩ : ULift.{u} (Fin 4))
  have hne : (⟨2⟩ : ULift.{u} (Fin 4)) ≠ ⟨0⟩ := by
    intro he
    have hv := congrArg (fun x : ULift.{u} (Fin 4) => x.down.val) he
    norm_num at hv
  have hprofile : profile chi ⟨0⟩ (1/2) (1/2) (⟨2⟩ : ULift.{u} (Fin 4)) = 0 := by
    norm_num [profile, region, chi, hne]
  norm_num [rejected, realize, kernel, hprofile] at impossible

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change phi 0 ≠ phi 1
    intro he
    have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    norm_num [phi] at he
    linarith

register_information_theorem exact_single_peak_log_likelihood_covariances in arena
  readout via (realize signature.{u} (fun _ _ x => phi x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "body",
        "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
