/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The counted renewal controller uses the actual block history and its paid bit clock. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalOneGap
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPayment
import D5.S3.Estimation.SequentialDecisionRisk.CriticalRenewalStoppedDrift
import Mathlib.Probability.ConditionalExpectation

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalController
open CriticalRenewalTable CriticalRenewalPaths CriticalRenewalFreshBlocks
open CriticalRenewalOneGap
namespace Stop := D5.S3.Estimation.SequentialDecisionRisk.CriticalRenewalStoppedDrift

abbrev Sample := ℕ × (ℕ → Block)

/-- The initial wait and the first n complete gap and coin blocks. -/
def history (n : ℕ) (ω : Sample) : ℕ × (Fin n → Block) :=
  (ω.1, fun k => ω.2 k)

private lemma measurable_history (n : ℕ) : Measurable (history n) := by
  exact measurable_fst.prodMk (measurable_pi_iff.mpr fun k =>
    (measurable_pi_apply k.val).comp measurable_snd)

/-- The proof filtration retains full past blocks, including their coin traces. -/
def filtration : Filtration ℕ (inferInstance : MeasurableSpace Sample) where
  seq n := MeasurableSpace.comap (history n) inferInstance
  mono' := by
    intro n m hnm s hs
    obtain ⟨t, ht, rfl⟩ := hs
    let R : (ℕ × (Fin m → Block)) → ℕ × (Fin n → Block) :=
      fun v => (v.1,fun k => v.2 ⟨k,lt_of_lt_of_le k.isLt hnm⟩)
    exact ⟨R ⁻¹' t, (by fun_prop : Measurable R) ht, rfl⟩
  le' n := (measurable_history n).comap_le

private lemma next_block_independent {J : ℕ} (w f : PMF ℕ) (t : Tick J) (n : ℕ) :
    IndepFun (fun ω : Sample => ω.2 n) (history n) (sourceLaw w f t) := by
  let ν := Measure.infinitePi (fun _ : ℕ => (blockLaw f t).toMeasure)
  let R : (ℕ → Block) → (Fin n → Block) := fun bs k => bs k
  let X : (ℕ → Block) → Block := fun bs => bs n
  have hR : Measurable R := by fun_prop
  have hX : Measurable X := measurable_pi_apply n
  have hi := (iIndepFun_infinitePi (P := fun _ : ℕ => (blockLaw f t).toMeasure)
    (X := fun _ b => b) (fun _ => measurable_id)).indepFun_finset
      (range n) {n} (by simp) (fun k => measurable_pi_apply k)
  have hi' : IndepFun R X ν := by
    exact hi.comp (measurable_pi_iff.mpr fun k : Fin n =>
      measurable_pi_apply (⟨k,mem_range.mpr k.isLt⟩ : range n))
      (measurable_pi_apply (⟨n,mem_singleton_self n⟩ : ({n} : Finset ℕ)))
  have hjoint : (sourceLaw w f t).map (fun ω => (history n ω,ω.2 n)) =
      (w.toMeasure.prod (ν.map R)).prod (ν.map X) := by
    have he : (fun ω : Sample => (history n ω,ω.2 n)) =
        MeasurableEquiv.prodAssoc.symm ∘ Prod.map id (fun bs => (R bs,X bs)) := rfl
    rw [he, ← Measure.map_map (MeasurableEquiv.measurable _)
      (measurable_id.prodMap (hR.prodMk hX))]
    change ((w.toMeasure.prod ν).map (Prod.map id (fun bs => (R bs,X bs)))).map _ = _
    rw [← Measure.map_prod_map _ _ measurable_id (hR.prodMk hX), Measure.map_id,
      hi'.map_prod_eq_prod_map_map hR.aemeasurable hX.aemeasurable,
      ← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]
  have hm : (sourceLaw w f t).map (history n) = w.toMeasure.prod (ν.map R) := by
    change (w.toMeasure.prod ν).map (Prod.map id R) = _
    rw [← Measure.map_prod_map _ _ measurable_id hR, Measure.map_id]
  have hx : (sourceLaw w f t).map (fun ω : Sample => ω.2 n) = ν.map X := by
    change (w.toMeasure.prod ν).map (X ∘ Prod.snd) = _
    rw [← Measure.map_map hX measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul]
  apply IndepFun.symm
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_history n).aemeasurable (by fun_prop)).mpr
  rw [hjoint,hm,hx]

private lemma next_block_conditional {J : ℕ} (w f : PMF ℕ) (t : Tick J)
    (n : ℕ) (a : Block → ℝ) :
    (sourceLaw w f t)[fun ω : Sample => a (ω.2 n) | filtration n] =ᵐ[sourceLaw w f t]
      fun _ => ∫ b, a b ∂(blockLaw f t).toMeasure := by
  have ha : Measurable a := measurable_of_countable _
  have hi := (next_block_independent w f t n).comp ha measurable_id
  have hma : Measurable (fun ω : Sample => a (ω.2 n)) := by fun_prop
  have hc := condExp_indep_eq hma.comap_le (filtration.le n)
    (comap_measurable (fun ω : Sample => a (ω.2 n))).stronglyMeasurable hi
  have hlaw : (sourceLaw w f t).map (fun ω : Sample => ω.2 n) =
      (blockLaw f t).toMeasure := by
    change (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => (blockLaw f t).toMeasure)).map
      ((fun bs : ℕ → Block => bs n) ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_pi_apply n) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
  have he : (∫ ω : Sample, a (ω.2 n) ∂sourceLaw w f t) =
      ∫ b, a b ∂(blockLaw f t).toMeasure := by
    rw [← hlaw, integral_map (by fun_prop) ha.aestronglyMeasurable]
  simpa only [he] using hc

private lemma score_adapted {J : ℕ} (δ : ℝ) (t : Tick J) :
    StronglyAdapted filtration (fun n (ω : Sample) => score δ t ω.2 n) := by
  intro n
  let F : (ℕ × (Fin n → Block)) → ℝ := fun v =>
    ∑ k : Fin n, (increment t (v.2 k) : ℝ) * δ
  have hF : Measurable F := measurable_of_countable _
  have he : (fun ω : Sample => score δ t ω.2 n) = F ∘ history n := by
    funext ω
    simp [F,score,history,Fin.sum_univ_eq_sum_range]
  rw [he]
  exact (hF.comp (comap_measurable _)).stronglyMeasurable

private lemma score_step {J : ℕ} (δ : ℝ) (t : Tick J) (n : ℕ) (ω : Sample) :
    score δ t ω.2 (n+1) - score δ t ω.2 n = (increment t (ω.2 n) : ℝ)*δ := by
  simp [score,sum_range_succ]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalController
