/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalFreshBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same-source product law of complete duration-mark blocks. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalOneGap
import Mathlib.Probability.Independence.InfinitePi

section
/-! Full finite coin traces and their same-source renewal product law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalFreshBlocks
open CriticalRenewalTable CriticalRenewalPaths

/-- The whole experiment has one initial wait and one sequence of full blocks. -/
def sourceLaw {J : ℕ} (w f : PMF ℕ) (t : Tick J) : Measure (ℕ × (ℕ → Block)) :=
  w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => (blockLaw f t).toMeasure)

instance {J : ℕ} (w f : PMF ℕ) (t : Tick J) : IsProbabilityMeasure (sourceLaw w f t) := by
  unfold sourceLaw
  infer_instance

private lemma product_snd_map {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (F : β → γ) (hF : Measurable F) :
    (μ.prod ν).map (fun x => F x.2) = ν.map F := by
  change (μ.prod ν).map (F ∘ Prod.snd) = _
  rw [← Measure.map_map hF measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

/-- Potential pairs are iid on the same source history, and the complete pair
    sequence is independent of the initial wait. Their common law is the actual
    phase/tick joint law, including duration-mark dependence within each block. -/
theorem fresh_same_source {J : ℕ} (w f : PMF ℕ) (t : Tick J) :
    iIndepFun (fun n (ω : ℕ × (ℕ → Block)) =>
      ((ω.2 n).zeros.length,increment t (ω.2 n))) (sourceLaw w f t) ∧
    (∀ n, (sourceLaw w f t).map (fun ω =>
      ((ω.2 n).zeros.length,increment t (ω.2 n))) = (pairLaw f t).toMeasure) ∧
    IndepFun (fun ω : ℕ × (ℕ → Block) => ω.1)
      (fun ω => fun n => ((ω.2 n).zeros.length,increment t (ω.2 n))) (sourceLaw w f t) ∧
    (sourceLaw w f t).map (fun ω => (ω.1,fun n => (ω.2 n).zeros.length)) =
      w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure) ∧
    (∀ (H : ℕ) (hH : 0 < H) (e : Evidence H),
      (blockLaw f t).map (fun b => target H J (e.val + increment t b)) =
        f.bind (fun k => wordLaw hH t (active e (Phase.first J))
          (List.replicate k false ++ [true]))) := by
  let F : Block → ℕ × ℤ := fun b => (b.zeros.length,increment t b)
  let ν := Measure.infinitePi (fun _ : ℕ => (blockLaw f t).toMeasure)
  have hF : Measurable F := measurable_of_countable _
  have hpair : (blockLaw f t).toMeasure.map F = (pairLaw f t).toMeasure := by
    rw [PMF.toMeasure_map F (blockLaw f t) hF, block_pair_law]
  have hi : iIndepFun (fun n (ω : ℕ → Block) => F (ω n)) ν :=
    iIndepFun_infinitePi (fun _ => hF)
  have hmap (n : ℕ) : ν.map (fun ω => F (ω n)) = (pairLaw f t).toMeasure := by
    change ν.map (F ∘ fun ω => ω n) = _
    rw [← Measure.map_map hF (measurable_pi_apply n), Measure.infinitePi_map_eval, hpair]
  have hlift : iIndepFun (fun n (ω : ℕ × (ℕ → Block)) => F (ω.2 n)) (sourceLaw w f t) := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
    change (w.toMeasure.prod ν).map (fun ω n => F (ω.2 n)) = _
    rw [product_snd_map w.toMeasure ν (fun ω n => F (ω n)) (by fun_prop),
      hi.map_fun_eq_infinitePi_map (by fun_prop)]
    congr 1
    funext n
    symm
    exact product_snd_map w.toMeasure ν (fun ω => F (ω n)) (by fun_prop)
  refine ⟨hlift, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (product_snd_map w.toMeasure ν (fun ω => F (ω n)) (by fun_prop)).trans (hmap n)
  · exact indepFun_prod (μ := w.toMeasure) (ν := ν) (X := id)
      (Y := fun ω : ℕ → Block => fun n => F (ω n)) measurable_id (by fun_prop)
  · have hduration : (blockLaw f t).map (fun b => b.zeros.length) = f := by
      calc
        _ = ((blockLaw f t).map (fun b => (b.zeros.length,increment t b))).map Prod.fst := by
          rw [PMF.map_comp]
          rfl
        _ = (pairLaw f t).map Prod.fst := by rw [block_pair_law]
        _ = f := by
          simp only [pairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
          change (f.bind fun k => (GeometricPhaseOccupation.finiteCappedLaw J k).bind
            fun z => (t.coin z).map (Function.const Bool k)) = f
          simp only [PMF.map_const, PMF.bind_const, PMF.bind_pure]
    have hdm : (blockLaw f t).toMeasure.map (fun b => b.zeros.length) = f.toMeasure := by
      rw [PMF.toMeasure_map _ _ (measurable_of_countable _), hduration]
    change (w.toMeasure.prod ν).map
      (Prod.map id (fun bs : ℕ → Block => fun n => (bs n).zeros.length)) = _
    have hL : Measurable (fun b : Block => b.zeros.length) := measurable_of_countable _
    have hLs : Measurable (fun bs : ℕ → Block => fun n => (bs n).zeros.length) :=
      measurable_pi_iff.mpr (fun n => hL.comp (measurable_pi_apply n))
    rw [← Measure.map_prod_map _ _ measurable_id hLs, Measure.map_id]
    dsimp only [ν]
    rw [Measure.infinitePi_map_pi _ (fun _ => hL)]
    simp only [hdm]
  · intro H hH e
    calc
      _ = ((blockLaw f t).map (fun b => (b.zeros.length,increment t b))).map
          (fun ku => target H J (e.val + ku.2)) := by rw [PMF.map_comp]; rfl
      _ = (pairLaw f t).map (fun ku => target H J (e.val + ku.2)) := by rw [block_pair_law]
      _ = _ := (random_gap_row hH f t e).symm

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalFreshBlocks

end
end
