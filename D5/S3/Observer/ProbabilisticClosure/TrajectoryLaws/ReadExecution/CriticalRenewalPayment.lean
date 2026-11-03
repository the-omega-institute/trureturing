/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Predictable completed-gap inclusion gives the exact paid mean on the actual renewal execution. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalFreshBlocks
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPaths
import Mathlib.Probability.Independence.Integration

section
/-! Payment includes the initial wait and tick and every zero through the last closing tick. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPayment
open CriticalRenewalTable CriticalRenewalPaths CriticalRenewalFreshBlocks

/-- Inclusion of zero-indexed block n depends only on the first n completed blocks. -/
def survives {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ) (bs : ℕ → Block) : Prop :=
  ∀ m ≤ n, inside H (evidence t bs m)

private lemma survives_iff {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ) (bs : ℕ → Block) :
    survives H t n bs ↔ (n : ℕ∞) < gapStop H t bs := by
  unfold gapStop
  split_ifs with h
  · simpa [survives, Nat.lt_find_iff]
  · have hh : ∀ m, inside H (evidence t bs m) := by simpa using h
    simp [survives, hh]

private lemma measurable_evidence {J : ℕ} (t : Tick J) (n : ℕ) :
    Measurable (fun ω : ℕ × (ℕ → Block) => evidence t ω.2 n) := by
  unfold evidence
  fun_prop

private lemma measurable_survives {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ) :
    MeasurableSet {ω : ℕ × (ℕ → Block) | survives H t n ω.2} := by
  simp only [survives, Set.ofPred_forall]
  exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    (Set.to_countable {u : ℤ | inside H u}).measurableSet.preimage (measurable_evidence t m)

/-- An extended nonnegative cost on each included block. -/
def includedCost {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ)
    (ω : ℕ × (ℕ → Block)) : ℝ≥0∞ :=
  if survives H t n ω.2 then ((ω.2 n).zeros.length + 1 : ℕ) else 0

private lemma predictable_duration {J : ℕ} (H : ℕ) (t : Tick J)
    (w f : PMF ℕ) (n : ℕ) :
    (∫⁻ ω, includedCost H t n ω ∂sourceLaw w f t) =
      (∫⁻ k : ℕ, (k + 1 : ℕ) ∂f.toMeasure) *
        (sourceLaw w f t) {ω | survives H t n ω.2} := by
  let pair (k : ℕ) (ω : ℕ × (ℕ → Block)) :=
    ((ω.2 k).zeros.length, increment t (ω.2 k))
  let past (v : (k : range n) → ℕ × ℤ) : ℝ≥0∞ :=
    if ∀ m ≤ n, inside H (∑ k ∈ range m,
      if hk : k < n then (v ⟨k,mem_range.mpr hk⟩).2 else 0) then 1 else 0
  let duration (v : (k : ({n} : Finset ℕ)) → ℕ × ℤ) : ℝ≥0∞ :=
    ((v ⟨n,mem_singleton_self n⟩).1 + 1 : ℕ)
  have hdis : Disjoint (range n) {n} := by simp
  have hind := (fresh_same_source w f t).1.indepFun_finset (range n) {n} hdis
    (fun k => (measurable_of_countable (fun b : Block =>
      (b.zeros.length, increment t b))).comp ((measurable_pi_apply k).comp measurable_snd))
  -- Orient the disjoint tuples with the next duration first.
  have hind' := hind.symm.comp (measurable_of_countable duration) (measurable_of_countable past)
  have hpast (ω : ℕ × (ℕ → Block)) :
      past (fun k : range n => pair k ω) = if survives H t n ω.2 then 1 else 0 := by
    have he (m : ℕ) (hm : m ≤ n) :
        (∑ k ∈ range m, if hk : k < n then (pair k ω).2 else 0) =
          evidence t ω.2 m := by
      apply sum_congr rfl
      intro k hk
      simp [pair, show k < n by have := mem_range.mp hk; omega]
    dsimp only [past, survives]
    congr 1
    apply propext
    constructor <;> intro h m hm
    · simpa only [he m hm] using h m hm
    · simpa only [he m hm] using h m hm
  change IndepFun (fun ω : ℕ × (ℕ → Block) =>
      (((ω.2 n).zeros.length + 1 : ℕ) : ℝ≥0∞))
    (fun ω => past (fun k : range n => pair k ω)) (sourceLaw w f t) at hind'
  simp_rw [hpast] at hind'
  have hblock : Measurable (fun ω : ℕ × (ℕ → Block) => ω.2 n) :=
    (measurable_pi_apply n).comp measurable_snd
  have hmDur : Measurable (fun ω : ℕ × (ℕ → Block) =>
      (((ω.2 n).zeros.length + 1 : ℕ) : ℝ≥0∞)) :=
    (measurable_of_countable (fun b : Block => ((b.zeros.length+1 : ℕ) : ℝ≥0∞))).comp hblock
  have hmPast : Measurable (fun ω : ℕ × (ℕ → Block) =>
      if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite (measurable_survives H t n) measurable_const
  have hfactor := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    hmDur hmPast hind'
  have hduration : (sourceLaw w f t).map (fun ω => (ω.2 n).zeros.length) = f.toMeasure := by
    have hh := congrArg (fun μ : Measure (ℕ × (ℕ → ℕ)) =>
      μ.map (fun ω => ω.2 n)) (fresh_same_source w f t).2.2.2.1
    rw [Measure.map_map (by fun_prop) (by
      exact measurable_fst.prodMk (measurable_pi_iff.mpr fun k =>
        (measurable_of_countable (fun b : Block => b.zeros.length)).comp
          ((measurable_pi_apply k).comp measurable_snd)))] at hh
    have hm : (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure)).map
        (fun ω => ω.2 n) = f.toMeasure := by
      change (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => f.toMeasure)).map
        ((fun bs : ℕ → ℕ => bs n) ∘ Prod.snd) = _
      rw [← Measure.map_map (measurable_pi_apply n) measurable_snd,
        Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
    exact hh.trans hm
  have hmean : (∫⁻ ω : ℕ × (ℕ → Block),
      (((ω.2 n).zeros.length + 1 : ℕ) : ℝ≥0∞) ∂sourceLaw w f t) =
      ∫⁻ k : ℕ, (k+1 : ℕ) ∂f.toMeasure := by
    rw [← hduration]
    exact (lintegral_map (measurable_of_countable (fun k : ℕ => ((k+1 : ℕ) : ℝ≥0∞)))
      ((measurable_of_countable (fun b : Block => b.zeros.length)).comp hblock)).symm
  rw [hmean] at hfactor
  have hi : (fun ω : ℕ × (ℕ → Block) =>
      if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) =
      Set.indicator {ω | survives H t n ω.2} (fun _ => 1) := rfl
  rw [hi, lintegral_indicator (measurable_survives H t n), setLIntegral_one] at hfactor
  convert hfactor using 1
  apply lintegral_congr
  intro ω
  by_cases h : survives H t n ω.2 <;> simp [includedCost, h]

private lemma measurable_cost {J : ℕ} (H : ℕ) (t : Tick J) (n : ℕ) :
    Measurable (includedCost H t n) :=
  ((measurable_of_countable (fun b : Block => ((b.zeros.length+1 : ℕ) : ℝ≥0∞))).comp
    ((measurable_pi_apply n).comp measurable_snd)).ite
      (measurable_survives H t n) measurable_const

private lemma payment_series {J : ℕ} (H : ℕ) (t : Tick J) (w f : PMF ℕ) :
    (∫⁻ ω, ∑' n, includedCost H t n ω ∂sourceLaw w f t) =
      (∫⁻ k : ℕ, (k+1 : ℕ) ∂f.toMeasure) *
        ∫⁻ ω, ∑' n, (if survives H t n ω.2 then (1 : ℝ≥0∞) else 0)
          ∂sourceLaw w f t := by
  rw [lintegral_tsum (fun n => (measurable_cost H t n).aemeasurable)]
  simp_rw [predictable_duration H t w f]
  rw [ENNReal.tsum_mul_left,
    lintegral_tsum (fun n => (measurable_const.ite
      (measurable_survives H t n) measurable_const).aemeasurable)]
  congr 1
  apply tsum_congr
  intro n
  simpa only [one_mul, Set.indicator_apply, Set.mem_setOf_eq] using
    (lintegral_indicator_const (measurable_survives H t n) 1).symm

private lemma finite_payment {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (ω : ℕ × (ℕ → Block)) (hfinite : gapStop H t ω.2 ≠ ⊤) :
    paidStop hH t ω.1 ω.2 ≠ ⊤ ∧
    (∑' n, if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) =
      ((gapStop H t ω.2).toNat : ℝ≥0∞) ∧
    ((paidStop hH t ω.1 ω.2).toNat : ℝ≥0∞) =
      1 + (ω.1 : ℝ≥0∞) + ∑' n, includedCost H t n ω := by
  have hexists : ∃ g, ¬ inside H (evidence t ω.2 g) := by
    by_contra hh
    simp [gapStop, hh] at hfinite
  let g := Nat.find hexists
  have hg : ¬ inside H (evidence t ω.2 g) := Nat.find_spec hexists
  have hp : ∀ n < g, inside H (evidence t ω.2 n) := by
    intro n hn
    exact not_not.mp (Nat.find_min hexists hn)
  have hpath := stopped_prefix_payment hH t ω.1 ω.2 g hg hp
  have hinc (n : ℕ) : survives H t n ω.2 ↔ n < g := by
    rw [survives_iff, hpath.1]
    exact ENat.natCast_lt_natCast
  have hcount : (∑' n, if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) = g := by
    simp_rw [hinc]
    rw [tsum_eq_sum (s := range g)]
    · calc
        _ = ∑ _n ∈ range g, (1 : ℝ≥0∞) :=
          sum_congr rfl (fun n hn => if_pos (mem_range.mp hn))
        _ = _ := by simp
    · intro n hn
      simp [mem_range.not.mp hn]
  have hcost : (∑' n, includedCost H t n ω) =
      ((∑ n ∈ range g, ((ω.2 n).zeros.length+1) : ℕ) : ℝ≥0∞) := by
    simp only [includedCost, hinc]
    rw [tsum_eq_sum (s := range g)]
    · simp only [Nat.cast_sum]
      apply sum_congr rfl
      intro n hn
      rw [if_pos (mem_range.mp hn)]
    · intro n hn
      simp [mem_range.not.mp hn]
  refine ⟨by rw [hpath.2.1]; exact ENat.natCast_ne_top _, ?_, ?_⟩
  · simpa [hpath.1] using hcount
  · rw [hpath.2.1, ENat.toNat_natCast, hcost]
    simp

/-- Exact paid expectation for both derived equilibrium renewal laws and the same
    actual bit table. Almost-sure gap exit and integrability remain explicit inputs. -/
theorem actual_source_payment (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c)
    (s : ℝ) (hs : 0 < s) {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (hfinite : ∀ i : Bool, ∀ᵐ ω ∂sourceLaw
      (CriticalRenewalSource.waitLaw r hr c hc i s hs)
      (CriticalRenewalSource.gapLaw r hr c hc i s hs) t, gapStop H t ω.2 ≠ ⊤)
    (hG : ∀ i : Bool, Integrable (fun ω : ℕ × (ℕ → Block) =>
      ((gapStop H t ω.2).toNat : ℝ)) (sourceLaw
        (CriticalRenewalSource.waitLaw r hr c hc i s hs)
        (CriticalRenewalSource.gapLaw r hr c hc i s hs) t)) :
    ∀ i : Bool,
      (∀ᵐ ω ∂sourceLaw (CriticalRenewalSource.waitLaw r hr c hc i s hs)
        (CriticalRenewalSource.gapLaw r hr c hc i s hs) t,
          paidStop hH t ω.1 ω.2 ≠ ⊤) ∧
      Integrable (fun ω : ℕ × (ℕ → Block) => ((paidStop hH t ω.1 ω.2).toNat : ℝ))
        (sourceLaw (CriticalRenewalSource.waitLaw r hr c hc i s hs)
          (CriticalRenewalSource.gapLaw r hr c hc i s hs) t) ∧
      (∫ ω : ℕ × (ℕ → Block), ((paidStop hH t ω.1 ω.2).toNat : ℝ)
        ∂sourceLaw (CriticalRenewalSource.waitLaw r hr c hc i s hs)
          (CriticalRenewalSource.gapLaw r hr c hc i s hs) t) =
        1 + CriticalRenewalSource.beta r c i s + CriticalRenewalSource.mean r c i s *
          ∫ ω : ℕ × (ℕ → Block), ((gapStop H t ω.2).toNat : ℝ)
            ∂sourceLaw (CriticalRenewalSource.waitLaw r hr c hc i s hs)
              (CriticalRenewalSource.gapLaw r hr c hc i s hs) t := by
  intro i
  let w := CriticalRenewalSource.waitLaw r hr c hc i s hs
  let f := CriticalRenewalSource.gapLaw r hr c hc i s hs
  let μ := sourceLaw w f t
  let N (ω : ℕ × (ℕ → Block)) : ℝ := (gapStop H t ω.2).toNat
  let T (ω : ℕ × (ℕ → Block)) : ℝ := (paidStop hH t ω.1 ω.2).toNat
  let total (ω : ℕ × (ℕ → Block)) : ℝ≥0∞ :=
    1 + (ω.1 : ℝ≥0∞) + ∑' n, includedCost H t n ω
  have hpath := (hfinite i).mono (fun ω hω => finite_payment hH t ω hω)
  have hcount : (∫⁻ ω, ∑' n, (if survives H t n ω.2 then (1 : ℝ≥0∞) else 0) ∂μ) =
      ENNReal.ofReal (∫ ω, N ω ∂μ) := by
    calc
      _ = ∫⁻ ω, ((gapStop H t ω.2).toNat : ℝ≥0∞) ∂μ :=
        lintegral_congr_ae (hpath.mono fun _ hω => hω.2.1)
      _ = ∫⁻ ω, ENNReal.ofReal (N ω) ∂μ := by simp [N]
      _ = _ := (ofReal_integral_eq_lintegral_ofReal (hG i)
        (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)).symm
  have hsrc := CriticalRenewalSource.source_laws r hr c hc s hs
  have hk : Integrable (fun k : ℕ => (k : ℝ)) f.toMeasure := by
    simpa only [pow_one] using (hsrc.2.1 i 1).1
  have hk1 : Integrable (fun k : ℕ => (k : ℝ)+1) f.toMeasure := hk.add (integrable_const 1)
  have hkm : (∫ k : ℕ, (k : ℝ)+1 ∂f.toMeasure) = CriticalRenewalSource.mean r c i s := by
    rw [integral_add hk (integrable_const 1)]
    have hfirst := (hsrc.2.1 i 1).2
    simp only [pow_one] at hfirst
    change (∫ k : ℕ, (k : ℝ) ∂f.toMeasure) = _ at hfirst
    simp only [integral_const, probReal_univ, one_smul, CriticalRenewalSource.mean]
    exact congrArg (fun x : ℝ => x+1) hfirst
  have hmean : (∫⁻ k : ℕ, (k+1 : ℕ) ∂f.toMeasure) =
      ENNReal.ofReal (CriticalRenewalSource.mean r c i s) := by
    calc
      _ = ∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ)+1) ∂f.toMeasure := by
        congr 1
        funext k
        rw [ENNReal.ofReal_add (Nat.cast_nonneg k) (by norm_num)]
        simp
      _ = ENNReal.ofReal (∫ k : ℕ, (k : ℝ)+1 ∂f.toMeasure) :=
        (ofReal_integral_eq_lintegral_ofReal hk1 (Filter.Eventually.of_forall
          fun k => by positivity)).symm
      _ = _ := congrArg ENNReal.ofReal hkm
  have hwait : (∫⁻ ω : ℕ × (ℕ → Block), (ω.1 : ℝ≥0∞) ∂μ) =
      ENNReal.ofReal (CriticalRenewalSource.beta r c i s) := by
    have hm : μ.map Prod.fst = w.toMeasure := by
      simp only [μ, sourceLaw, Measure.map_fst_prod, measure_univ, one_smul]
    calc
      _ = ∫⁻ u : ℕ, (u : ℝ≥0∞) ∂w.toMeasure := by
        rw [← hm]
        exact (lintegral_map (measurable_of_countable _) measurable_fst).symm
      _ = ∫⁻ u : ℕ, ENNReal.ofReal (u : ℝ) ∂w.toMeasure := by simp
      _ = ENNReal.ofReal (∫ u : ℕ, (u : ℝ) ∂w.toMeasure) :=
        (ofReal_integral_eq_lintegral_ofReal (hsrc.2.2 i).1
          (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)).symm
      _ = _ := congrArg ENNReal.ofReal (hsrc.2.2 i).2
  have hmWait : Measurable (fun ω : ℕ × (ℕ → Block) => (ω.1 : ℝ≥0∞)) :=
    (measurable_of_countable (fun u : ℕ => (u : ℝ≥0∞))).comp measurable_fst
  have hmSeries := Measurable.ennreal_tsum (fun n => measurable_cost H t n)
  have hmTotal : Measurable total := (measurable_const.add hmWait).add hmSeries
  have hext : (∫⁻ ω, total ω ∂μ) = 1 + ENNReal.ofReal (CriticalRenewalSource.beta r c i s) +
      ENNReal.ofReal (CriticalRenewalSource.mean r c i s) * ENNReal.ofReal (∫ ω, N ω ∂μ) := by
    dsimp only [total]
    rw [lintegral_add_left (f := fun ω : ℕ × (ℕ → Block) => 1 + (ω.1 : ℝ≥0∞))
      (measurable_const.add hmWait) (fun ω => ∑' n, includedCost H t n ω),
      lintegral_add_left (f := fun _ : ℕ × (ℕ → Block) => (1 : ℝ≥0∞))
        measurable_const (fun ω => (ω.1 : ℝ≥0∞)),
      lintegral_const, measure_univ, mul_one, hwait, payment_series H t w f, hmean, hcount]
  have htotal : (∫⁻ ω, total ω ∂μ) ≠ ⊤ := by rw [hext]; finiteness
  have htotalFinite : ∀ᵐ ω ∂μ, total ω < ⊤ := by
    filter_upwards [hpath] with ω hω
    dsimp only [total]
    rw [← hω.2.2]
    exact ENNReal.natCast_lt_top _
  have hreal : (fun ω => (total ω).toReal) =ᵐ[μ] T := by
    filter_upwards [hpath] with ω hω
    dsimp only [total]
    rw [← hω.2.2]
    simp [T]
  refine ⟨hpath.mono (fun _ hω => hω.1),
    (integrable_toReal_of_lintegral_ne_top hmTotal.aemeasurable htotal).congr hreal, ?_⟩
  change (∫ ω, T ω ∂μ) = _
  rw [← integral_congr_ae hreal, integral_toReal hmTotal.aemeasurable htotalFinite, hext]
  have hb : 0 ≤ CriticalRenewalSource.beta r c i s := by
    rw [← (hsrc.2.2 i).2]
    exact integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hm := (hsrc.1.1 i).mean_positive.le
  have hn : 0 ≤ ∫ ω, N ω ∂μ := integral_nonneg (fun _ => Nat.cast_nonneg _)
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_one,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hb, ENNReal.toReal_ofReal hm,
    ENNReal.toReal_ofReal hn]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPayment

end
end
