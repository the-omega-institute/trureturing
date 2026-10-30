/- GID: D5/S3/StatisticalMechanics/NoisyVoter/SourceCoinMoments
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/NoisyVoter/SourceCoinMoments
   mirror-E: none
   anchors: []
   utility: none
   digest: Native source partitions determine the fair-coin moments of synchronous opinions. -/

import D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
import Mathlib.MeasureTheory.Integral.Pi

/-! # Fair opinion moments on the actual source partition -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace D5.S3.StatisticalMechanics.NoisyVoter.SourceCoinMoments

open RepetitionVarianceLinear AncestralSources
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)

variable {V Ω : Type} {G : SimpleGraph V} [G.LocallyFinite] [MeasurableSpace Ω]

private theorem finite_selector_integral {α β : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Ω → α) (X : Ω → β)
    (hA : Measurable A) (hX : Measurable X) (hi : IndepFun A X P)
    (s : Finset α) (hs : ∀ ω, A ω ∈ s) (f : α → β → ℝ) (C : ℝ)
    (hf : ∀ a ∈ s, Measurable (f a)) (hb : ∀ a ∈ s, ∀ x, ‖f a x‖ ≤ C) :
    (∫ ω, f (A ω) (X ω) ∂P) =
      ∑ a ∈ s, P.real {ω | A ω = a} * ∫ ω, f a (X ω) ∂P := by
  classical
  have hrepr (ω : Ω) : f (A ω) (X ω) =
      ∑ a ∈ s, if A ω = a then f a (X ω) else 0 := by
    rw [Finset.sum_eq_single_of_mem (A ω) (hs ω)]
    · simp
    · intro b hb hba; simp [Ne.symm hba]
  simp_rw [hrepr]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro a ha
    have hφ : Measurable (fun b : α => if b = a then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_singleton a) measurable_const measurable_const
    have he := hi.integral_fun_comp_mul_comp hA.aemeasurable hX.aemeasurable
      hφ.aestronglyMeasurable (hf a ha).aestronglyMeasurable
    have hind : (∫ ω, if A ω = a then (1 : ℝ) else 0 ∂P) = P.real {ω | A ω = a} := by
      simpa only [Set.indicator_apply, Pi.one_apply] using
        integral_indicator_one (hA (measurableSet_singleton a))
    simpa only [ite_mul, one_mul, zero_mul, hind] using he
  · intro a ha
    exact (MemLp.of_bound
      (Measurable.ite (hA (measurableSet_singleton a)) ((hf a ha).comp hX)
        measurable_const).aestronglyMeasurable (max C 0)
      (Eventually.of_forall (by
        intro ω
        split_ifs
        · exact (hb a ha _).trans (le_max_left _ _)
        · simpa only [norm_zero] using le_max_right C 0))).integrable one_le_two

private theorem fixed_pair_sign_mean (P : Measure Ω) (M : Model G P) (a b : Label V) :
    (∫ ω, sgn (coin M.coordinate a ω) * sgn (coin M.coordinate b ω) ∂P) =
      if a = b then 1 else 0 := by
  classical
  letI := M.probability
  by_cases hab : a = b
  · subst b
    have he (ω : Ω) : sgn (coin M.coordinate a ω) * sgn (coin M.coordinate a ω) = 1 := by
      cases coin M.coordinate a ω <;> norm_num [sgn]
    simp [he]
  · have hi := (coins_independent P M).indepFun hab
    have hm (l : Label V) : Measurable (coin M.coordinate l) := by
      cases l <;> exact M.measurable_coordinate _
    have he := hi.integral_fun_comp_mul_comp (hm a).aemeasurable (hm b).aemeasurable
      (measurable_of_finite sgn).aestronglyMeasurable
      (measurable_of_finite sgn).aestronglyMeasurable
    have hmean (l : Label V) : (∫ ω, sgn (coin M.coordinate l ω) ∂P) = 0 := by
      change (∫ ω, (sgn ∘ coin M.coordinate l) ω ∂P) = 0
      rw [(coin_hasLaw P M l).integral_comp (measurable_of_finite sgn).aestronglyMeasurable]
      norm_num [integral_bernoulliMeasure, sgn]
    simp only [hmean, mul_zero] at he
    simpa only [if_neg hab] using he

theorem native_pair_sign_mean (P : Measure Ω) (M : Model G P) (n m : ℕ) (u v : V) :
    (∫ ω, sgn (nvm M.coordinate n u ω) * sgn (nvm M.coordinate m v ω) ∂P) =
      P.real {ω | source M.coordinate n u ω = source M.coordinate m v ω} := by
  classical
  letI := M.probability
  let A (ω : Ω) := (source M.coordinate n u ω, source M.coordinate m v ω)
  let X (ω : Ω) (l : Label V) := coin M.coordinate l ω
  have hA : Measurable A := (source_measurable M.coordinate M.measurable_coordinate n u).prodMk
    (source_measurable M.coordinate M.measurable_coordinate m v)
  have hX : Measurable X := measurable_pi_iff.mpr (by
    intro l; cases l <;> exact M.measurable_coordinate _)
  have hi : IndepFun A X P := (sources_independent_coins P M).comp
    ((measurable_pi_apply (n,u)).prodMk (measurable_pi_apply (m,v))) measurable_id
  let s := (possibleSources (G := G) n u) ×ˢ (possibleSources (G := G) m v)
  have hs (ω : Ω) : A ω ∈ s := Finset.mem_product.mpr
    ⟨source_mem_possible M.coordinate n u ω, source_mem_possible M.coordinate m v ω⟩
  let f (a : Label V × Label V) (x : Label V → Bool) := sgn (x a.1) * sgn (x a.2)
  have hf (a : Label V × Label V) : Measurable (f a) :=
    ((measurable_of_finite sgn).comp (measurable_pi_apply a.1)).mul
      ((measurable_of_finite sgn).comp (measurable_pi_apply a.2))
  have hb (a : Label V × Label V) (x : Label V → Bool) : ‖f a x‖ ≤ 1 := by
    cases x a.1 <;> cases x a.2 <;> norm_num [f, sgn]
  have hmain := finite_selector_integral P A X hA hX hi s hs f 1
    (fun a _ => hf a) (fun a _ => hb a)
  have hdiag := finite_selector_integral P A X hA hX hi s hs
    (fun a _ => if a.1 = a.2 then (1 : ℝ) else 0) 1
    (by intros; exact measurable_const)
    (by intros; split_ifs <;> norm_num)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hdiag
  have hmean : (∫ ω, if (A ω).1 = (A ω).2 then (1 : ℝ) else 0 ∂P) =
      P.real {ω | source M.coordinate n u ω = source M.coordinate m v ω} := by
    simpa only [Set.indicator_apply, Pi.one_apply] using
      integral_indicator_one (measurableSet_eq_fun
        (source_measurable M.coordinate M.measurable_coordinate n u)
        (source_measurable M.coordinate M.measurable_coordinate m v))
  simp_rw [show ∀ a, (∫ ω, f a (X ω) ∂P) = if a.1 = a.2 then 1 else 0
    from fun a => fixed_pair_sign_mean P M a.1 a.2] at hmain
  rw [← hdiag, hmean] at hmain
  simpa only [f, A, X, native_source] using hmain

end D5.S3.StatisticalMechanics.NoisyVoter.SourceCoinMoments
