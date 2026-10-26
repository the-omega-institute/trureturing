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

/-! Complete block histories and the literal counted bit execution. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalController
open CriticalRenewalTable CriticalRenewalPaths CriticalRenewalFreshBlocks
open CriticalRenewalOneGap
open D5.S3.Estimation.SequentialDecisionRisk.CriticalRenewalStoppedDrift

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
    change (∑ k ∈ range n, (increment t (ω.2 k) : ℝ)*δ) =
      ∑ k : Fin n, (increment t (ω.2 k) : ℝ)*δ
    exact (Fin.sum_univ_eq_sum_range (fun k => (increment t (ω.2 k) : ℝ)*δ) n).symm
  change StronglyMeasurable[filtration n] (fun ω : Sample => score δ t ω.2 n)
  rw [he]
  exact (hF.comp (comap_measurable _)).stronglyMeasurable

private lemma score_step {J : ℕ} (δ : ℝ) (t : Tick J) (n : ℕ) (ω : Sample) :
    score δ t ω.2 (n+1) - score δ t ω.2 n = (increment t (ω.2 n) : ℝ)*δ := by
  simp [score,sum_range_succ]

private lemma conditional_pair {J : ℕ} (w f : PMF ℕ) (t : Tick J)
    (n : ℕ) (a : ℕ × ℤ → ℝ) :
    (sourceLaw w f t)[fun ω : Sample =>
      a ((ω.2 n).zeros.length,increment t (ω.2 n)) | filtration n]
      =ᵐ[sourceLaw w f t] fun _ => ∫ ku, a ku ∂(pairLaw f t).toMeasure := by
  have h := next_block_conditional w f t n
    (fun b => a (b.zeros.length,increment t b))
  have he : (∫ b, a (b.zeros.length,increment t b) ∂(blockLaw f t).toMeasure) =
      ∫ ku, a ku ∂(pairLaw f t).toMeasure := by
    rw [← block_pair_law f t, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
      integral_map (by fun_prop) (measurable_of_countable a).aestronglyMeasurable]
  simpa only [he] using h

private lemma score_evidence {J : ℕ} (δ : ℝ) (t : Tick J)
    (bs : ℕ → Block) (n : ℕ) :
    score δ t bs n = (evidence t bs n : ℝ)*δ := by
  simp only [score,evidence,Int.cast_sum,Finset.sum_mul]

private lemma outside_score {H J : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (t : Tick J) (bs : ℕ → Block) (n : ℕ) :
    ¬ inside H (evidence t bs n) ↔ (H : ℝ)*δ ≤ |score δ t bs n| := by
  rw [score_evidence,abs_mul,abs_of_pos hδ,
    mul_le_mul_iff_left₀ hδ,le_abs]
  simp only [inside,not_and_or,not_lt]
  constructor
  · rintro (h | h)
    · right
      have hh : (evidence t bs n : ℝ) ≤ -(H : ℝ) := by exact_mod_cast h
      linarith
    · left
      exact_mod_cast h
  · rintro (h | h)
    · right
      exact_mod_cast h
    · left
      have hh : (evidence t bs n : ℝ) ≤ -(H : ℝ) := by linarith
      exact_mod_cast hh

private lemma exit_eq_gapStop {H J : ℕ} (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ)
    (t : Tick J) (ω : Sample) :
    exitTime (fun n (ω : Sample) => score δ t ω.2 n) ((H : ℝ)*δ) ω =
      gapStop H t ω.2 := by
  have hcond (n : ℕ) :
      (1 ≤ n ∧ (H : ℝ)*δ ≤ |score δ t ω.2 n|) ↔
        ¬ inside H (evidence t ω.2 n) := by
    rw [← outside_score δ hδ]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_,h⟩
      by_contra hn
      have hn0 : n = 0 := by omega
      subst n
      simp [inside,evidence] at h
      omega
  unfold exitTime hittingAfter gapStop
  simp only [Set.mem_ofPred_eq,hcond]
  split_ifs with h
  · congr 1
    rw [Nat.sInf_def (s := {j | ¬ inside H (evidence t ω.2 j)}) h]
    congr 1
  · rfl

private lemma score_conditional_mean {J : ℕ} (w f : PMF ℕ) (δ : ℝ) (t : Tick J)
    (n : ℕ) :
    (sourceLaw w f t)[fun ω : Sample =>
      score δ t ω.2 (n+1)-score δ t ω.2 n | filtration n]
      =ᵐ[sourceLaw w f t] fun _ =>
        ∫ ku : ℕ × ℤ, (ku.2 : ℝ)*δ ∂(pairLaw f t).toMeasure := by
  simpa only [score_step] using conditional_pair w f t n
    (fun ku : ℕ × ℤ => (ku.2 : ℝ)*δ)

private lemma score_conditional_second {J : ℕ} (w f : PMF ℕ) (δ : ℝ) (t : Tick J)
    (n : ℕ) :
    (sourceLaw w f t)[fun ω : Sample =>
      (score δ t ω.2 (n+1)-score δ t ω.2 n)^2 | filtration n]
      =ᵐ[sourceLaw w f t] fun _ =>
        ∫ ku : ℕ × ℤ, ((ku.2 : ℝ)*δ)^2 ∂(pairLaw f t).toMeasure := by
  simpa only [score_step] using conditional_pair w f t n
    (fun ku : ℕ × ℤ => ((ku.2 : ℝ)*δ)^2)

private lemma finite_gap_path {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (ω : Sample) (hf : gapStop H t ω.2 ≠ ⊤) :
    let g := (gapStop H t ω.2).toNat
    gapStop H t ω.2 = (g : ℕ∞) ∧
    paidStop hH t ω.1 ω.2 = (clock ω.1 ω.2 g : ℕ∞) ∧
    run hH t ω.1 ω.2 (clock ω.1 ω.2 g) = target H J (evidence t ω.2 g) ∧
    (run hH t ω.1 ω.2 (clock ω.1 ω.2 g) = label true ↔
      (H : ℤ) ≤ evidence t ω.2 g) ∧
    (run hH t ω.1 ω.2 (clock ω.1 ω.2 g) = label false ↔
      evidence t ω.2 g ≤ -(H : ℤ)) := by
  have hex : ∃ n, ¬ inside H (evidence t ω.2 n) := by
    by_contra hn
    simp [gapStop,hn] at hf
  have hprev : ∀ n < Nat.find hex, inside H (evidence t ω.2 n) := by
    intro n hn
    exact not_not.mp (Nat.find_min hex hn)
  have hp := stopped_prefix_payment hH t ω.1 ω.2 (Nat.find hex)
    (Nat.find_spec hex) hprev
  have hg : (gapStop H t ω.2).toNat = Nat.find hex := by rw [hp.1]; simp
  dsimp only
  rw [hg]
  refine ⟨hp.1,?_,hp.2.2.1,hp.2.2.2.2.2.2.1,hp.2.2.2.2.2.2.2.1⟩
  simpa only [clock,Nat.add_comm 1 ω.1] using hp.2.1

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalController
