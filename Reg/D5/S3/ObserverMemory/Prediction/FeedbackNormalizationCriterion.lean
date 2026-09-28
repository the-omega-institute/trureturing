import D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
universe u v

@[reducible] def signature : Signature where
  Params := ℕ
  State T := Fin T → ℝ
  Role := ULift.{u} Unit
  finiteRole := ⟨{⟨()⟩}, fun x => by
    have hx : x = ⟨()⟩ := Subsingleton.elim _ _
    simp only [hx, Finset.mem_singleton]⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := ULift.{v} Empty
  finiteAnchor := ⟨∅, fun x => nomatch x.down⟩

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ f => ∏ t, f t) (fun e => nomatch e.down)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e.down)

@[reducible] def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀
    (T : ℕ) (hT : 1 ≤ T)
    (A : Fin T → Type u) (Y : Fin T → Type v)
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)] [∀ t, DecidableEq (A t)]
    [∀ t, Fintype (Y t)] [∀ t, Nonempty (Y t)] [∀ t, DecidableEq (Y t)]
    (P : (∀ t, Y t) → (∀ t, A t) → ℝ)
    (hP : ∀ y a, 0 ≤ P y a)
    (hPsum : ∀ a, ∑ y, P y a = 1),
    List.TFAE [
      ∀ f : (t : Fin T) → Prefix Y t.val → A t, feedbackMass P f = 1,
      ∀ n, 1 ≤ n → n < T →
        ∀ (u : Prefix A n)
          (v w : (i : {i : Fin T // n ≤ i.val}) → A i.1)
          (E : Set (Prefix Y n)),
          feedbackMass P (singleCutSwitch n u v w E) = 1,
      ∀ n, n ≤ T → ∀ (x : Prefix Y n) (a b : ∀ t, A t),
        (∀ i, i.val < n → a i = b i) →
          prefixMarginal P n x a = prefixMarginal P n x b,
      ∃ q : (t : Fin T) → Prefix A (t.val + 1) → Prefix Y t.val → Y t → ℝ,
        (∀ t a x y, 0 ≤ q t a x y) ∧
        (∀ t a x, ∑ y, q t a x y = 1) ∧
        ∀ y a, P y a = R.readout ⟨()⟩ T (fun t => q t (restrictPrefix a (t.val + 1))
          (restrictPrefix y t.val) (y t))]

theorem actual_law : arena.Law actual := by
  exact feedback_normalization_prefix_causality_sequential_kernels

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  have hcase := h 1 (by omega) (fun _ => ULift.{u} Unit) (fun _ => ULift.{v} Unit)
    (fun _ _ => (1 : ℝ)) (by intros; norm_num) (by intro a; simp)
  have hfirst : ∀ f : (t : Fin 1) → Prefix (fun _ => ULift.{v} Unit) t.val →
      ULift.{u} Unit, feedbackMass (fun _ _ => (1 : ℝ)) f = 1 := by
    intro f
    simp [feedbackMass]
  have hfourth := (List.TFAE.out hcase 0 3).mp hfirst
  obtain ⟨q, _, _, hfactor⟩ := hfourth
  have impossible := hfactor (fun _ => ⟨()⟩) (fun _ => ⟨()⟩)
  norm_num [rejected, realize] at impossible

def registration : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i.down⟩
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    change (∏ _t : Fin 1, (0 : ℝ)) ≠ ∏ _t : Fin 1, (1 : ℝ)
    norm_num

register_information_theorem feedback_normalization_prefix_causality_sequential_kernels in arena
  readout via (realize signature.{u,v} (fun _ _ f => ∏ t, f t) (fun e => nomatch e.down))
  realizes registration
  escape from source ({
    owner := `D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg", "arg",
        "arg", "fn", "arg", "arg", "body", "arg", "arg", "body",
        "body", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

end Reg.D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
