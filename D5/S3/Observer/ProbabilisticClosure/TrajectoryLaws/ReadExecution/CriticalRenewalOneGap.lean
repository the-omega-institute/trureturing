/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual one-gap coin traces, normalized terminal rewards and signed adjacent-grid evidence. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

section
/-! Full finite coin traces and their same-source renewal product law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalFreshBlocks
open CriticalRenewalTable CriticalRenewalPaths

instance : MeasurableSpace Block := ⊤
instance : MeasurableSingletonClass Block := ⟨fun _ => trivial⟩

/-- A new zero samples its own row coin and appends just its outcome to a proof trace. -/
def zeroTraceLaw (J : ℕ) : ℕ → PMF (List Bool × Phase.T J)
  | 0 => PMF.pure ([],Phase.first J)
  | k+1 => (zeroTraceLaw J k).bind fun v =>
      (Phase.coin v.2).map fun b => (v.1 ++ [b],Phase.step v.2 b)

private lemma phaseAt_append (J : ℕ) (xs : List Bool) (b d : Bool)
    (k : ℕ) (hk : k ≤ xs.length) :
    phaseAt J ⟨xs ++ [b],d⟩ k = phaseAt J ⟨xs,false⟩ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlt : k < xs.length := by omega
    simp only [phaseAt, ih (by omega), List.getElem?_append_left hlt]

private lemma phaseAt_append_last (J : ℕ) (xs : List Bool) (b d : Bool) :
    phaseAt J ⟨xs ++ [b],d⟩ (xs.length+1) =
      Phase.step (phaseAt J ⟨xs,false⟩ xs.length) b := by
  rw [phaseAt, phaseAt_append J xs b d xs.length le_rfl]
  simp

private theorem zero_trace_support (J k : ℕ) (v : List Bool × Phase.T J)
    (hv : v ∈ (zeroTraceLaw J k).support) :
    v.1.length = k ∧ phaseAt J ⟨v.1,false⟩ k = v.2 := by
  induction k generalizing v with
  | zero =>
    have hh : v = ([],Phase.first J) := by simpa [zeroTraceLaw] using hv
    subst v
    simp [phaseAt]
  | succ k ih =>
    obtain ⟨w,hw,hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
    obtain ⟨b,hb,hv⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    subst v
    obtain ⟨hlen,hphase⟩ := ih w hw
    constructor
    · simp [hlen]
    · dsimp only
      rw [← hlen, phaseAt_append_last, hlen, hphase]

private theorem zero_trace_phase (J k : ℕ) :
    (zeroTraceLaw J k).map Prod.snd = GeometricPhaseOccupation.finiteCappedLaw J k := by
  induction k with
  | zero => simp [zeroTraceLaw, GeometricPhaseOccupation.finiteCappedLaw,
      PMF.pure_map, Phase.first]
  | succ k ih =>
    simp only [zeroTraceLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
    have hh : (fun v : List Bool × Phase.T J =>
        (Phase.coin v.2).map (Phase.step v.2)) =
        fun v => GeometricPhaseOccupation.finiteCappedRow J v.2 := by
      funext v; exact phase_coin_row J v.2
    rw [hh]
    change (zeroTraceLaw J k).bind ((GeometricPhaseOccupation.finiteCappedRow J) ∘ Prod.snd) = _
    rw [← PMF.bind_map, ih]
    rfl

private lemma bind_support_congr {α β : Type} (p : PMF α) (f g : α → PMF β)
    (h : ∀ x ∈ p.support, f x = g x) : p.bind f = p.bind g := by
  apply PMF.ext
  intro y
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ p.support
  · rw [h x hx]
  · have hz : p x = 0 := by simpa only [PMF.mem_support_iff, not_not] using hx
    simp [hz]

/-- Conditional on a duration, all its actual zero coins and the terminal tick
    coin are sampled in order. -/
def markedTraceLaw (J : ℕ) (t : Tick J) (k : ℕ) : PMF Block :=
  (zeroTraceLaw J k).bind fun v => (t.coin v.2).map fun b => ⟨v.1,b⟩

def blockLaw {J : ℕ} (f : PMF ℕ) (t : Tick J) : PMF Block :=
  f.bind (markedTraceLaw J t)

/-- The pathwise duration and mark from these very coins have the specified
    joint law. No product of their two marginals is substituted. -/
theorem block_pair_law {J : ℕ} (f : PMF ℕ) (t : Tick J) :
    (blockLaw f t).map (fun b => (b.zeros.length,increment t b)) = pairLaw f t := by
  simp only [blockLaw, pairLaw, PMF.map_bind]
  congr 1
  funext k
  simp only [markedTraceLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have he : (zeroTraceLaw J k).bind (fun v => (t.coin v.2).map
      (fun b => ((v.1.length),increment t ⟨v.1,b⟩))) =
      (zeroTraceLaw J k).bind (fun v => (t.coin v.2).map
        (fun b => (k,t.increment v.2 b))) := by
    apply bind_support_congr
    intro v hv
    obtain ⟨hlen,hphase⟩ := zero_trace_support J k v hv
    congr 1
    funext b
    dsimp [increment]
    have hh : phaseAt J ⟨v.1,b⟩ v.1.length = v.2 := by
      rw [hlen]
      have htick (m : ℕ) : phaseAt J ⟨v.1,b⟩ m = phaseAt J ⟨v.1,false⟩ m := by
        induction m with
        | zero => rfl
        | succ m ih => simp only [phaseAt, ih]
      exact (htick k).trans hphase
    rw [hh, hlen]
  rw [he]
  rw [← zero_trace_phase J k]
  simp only [PMF.bind_map, Function.comp_def]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalFreshBlocks

end
end

section
/-! Source-normalized terminal phase statistics and their adjacent-grid evidence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators NNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalOneGap


def reward (r J : ℕ) (z : Fin (J + 1)) : ℝ :=
  if z.val < J then 1 / (2 : ℝ)^(r*(z.val+1)) else 0

def phase (J : ℕ) (f : PMF ℕ) : PMF (Fin (J + 1)) :=
  f.bind (GeometricPhaseOccupation.finiteCappedLaw J)

def average {J : ℕ} (p : PMF (Fin (J + 1))) (v : Fin (J + 1) → ℝ) : ℝ :=
  ∑ z, (p z).toReal * v z

def grid (r J : ℕ) : ℝ := (J : ℝ)/(2 : ℝ)^(r*J)

private lemma pmf_sum_real {α : Type*} [Fintype α] (p : PMF α) :
    ∑ z, (p z).toReal = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [ENNReal.tsum_toReal_eq p.apply_ne_top, tsum_fintype, ENNReal.toReal_one] at h
  exact h

private lemma average_nonneg {J : ℕ} (p : PMF (Fin (J + 1)))
    (v : Fin (J + 1) → ℝ) (hv : ∀ z, 0 ≤ v z) : 0 ≤ average p v :=
  sum_nonneg fun z _ => mul_nonneg ENNReal.toReal_nonneg (hv z)

private lemma average_le {J : ℕ} (p : PMF (Fin (J + 1)))
    (v : Fin (J + 1) → ℝ) (C : ℝ) (hv : ∀ z, v z ≤ C) :
    average p v ≤ C := by
  calc
    _ ≤ ∑ z, (p z).toReal * C :=
      sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hv z) ENNReal.toReal_nonneg
    _ = C := by rw [← sum_mul, pmf_sum_real, one_mul]

private lemma reward_bounds (r J : ℕ) (hr : 1 ≤ r) (z : Fin (J + 1)) :
    0 ≤ reward r J z ∧ reward r J z ≤ 1/(2 : ℝ)^r ∧
      reward r J z ≤ 1/2 := by
  have hpow : (2 : ℝ)^r ≤ (2 : ℝ)^(r*(z.val+1)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
  have htwo : (2 : ℝ) ≤ (2 : ℝ)^r := by
    simpa using pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hr
  unfold reward
  split_ifs <;> constructor <;> try positivity
  · constructor
    · exact one_div_le_one_div_of_le (by positivity) hpow
    · exact one_div_le_one_div_of_le (by norm_num) (htwo.trans hpow)
  · constructor <;> positivity

private lemma discounted_real (m : ℕ) (s : ℝ) (k : ℕ) :
    (GeometricPhaseOccupation.discountedWeight m s k).toReal = CriticalRenewalSource.term m s k := by
  by_cases hk : k = 0
  · simp [GeometricPhaseOccupation.discountedWeight, CriticalRenewalSource.term, hk]
  · simp [GeometricPhaseOccupation.discountedWeight, CriticalRenewalSource.term, hk, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

private lemma occupation_series (m J : ℕ) (j : Fin J) (s eta : ℝ)
    (hs : 0 < s) (hscale : s * (2 : ℝ) ^ J ≤ eta) (heta : eta ≤ 1) :
    Summable (fun k => CriticalRenewalSource.term m s k *
      (GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc).toReal) ∧
    (∑' k, CriticalRenewalSource.term m s k *
      (GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc).toReal) = GeometricPhaseOccupation.occupation m s (j.val+1) ∧
    GeometricPhaseOccupation.lowerConstant m * (2 : ℝ)^((j.val+1)*(m+1)) ≤
      GeometricPhaseOccupation.occupation m s (j.val+1) ∧
    GeometricPhaseOccupation.occupation m s (j.val+1) ≤
      GeometricPhaseOccupation.upperConstant m * (2 : ℝ)^((j.val+1)*(m+1)) := by
  have hj : j.val+1 ≤ J := by omega
  have hsj : s*(2 : ℝ)^(j.val+1) ≤ eta :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num) hj) hs.le).trans hscale
  have h := GeometricPhaseOccupation.uniform_discounted_phase_occupation m (j.val+1) (by omega)
    s eta hs hsj heta
  have he := h.2.2.2.2.2.2.2 J hj
  have hcast : (⟨j.val+1-1, by omega⟩ : Fin (J + 1)) = j.castSucc :=
    Fin.ext (by simp)
  rw [hcast] at he
  have hf : (∑' k, GeometricPhaseOccupation.discountedWeight m s k *
      GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc) ≠ ⊤ := by
    exact he.trans_ne h.2.2.2.1
  have hh := ENNReal.hasSum_toReal hf
  simp only [ENNReal.toReal_mul, discounted_real] at hh
  refine ⟨hh.summable, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  change _ = (GeometricPhaseOccupation.actualOccupation
    (GeometricPhaseOccupation.discountedWeight m s) ((j.val+1)-1)).toReal
  rw [← he, ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hf)]
  simp only [ENNReal.toReal_mul, discounted_real]

private lemma phase_live_mass (r J : ℕ) (hr : 1 ≤ r) (c s eta : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hscale : s * (2 : ℝ) ^ J ≤ eta) (heta : eta ≤ 1)
    (i : Bool) (j : Fin J) :
    (phase J (CriticalRenewalSource.gapLaw r hr c hc i s hs) j.castSucc).toReal =
      (GeometricPhaseOccupation.occupation (2*r-1) s (j.val+1) +
        if i then c*GeometricPhaseOccupation.occupation (r-1) s (j.val+1) else 0) /
        CriticalRenewalSource.normalizer r c i s := by
  have hsrc := (CriticalRenewalSource.source_laws r hr c hc s hs).1.1 i
  have he (k : ℕ) : (CriticalRenewalSource.gapLaw r hr c hc i s hs k).toReal = CriticalRenewalSource.density r c i s k :=
    ENNReal.toReal_ofReal (hsrc.density_nonnegative k)
  have hd := occupation_series (2*r-1) J j s eta hs hscale heta
  have hl := occupation_series (r-1) J j s eta hs hscale heta
  have hb := ENNReal.hasSum_toReal
    (show (∑' k, CriticalRenewalSource.gapLaw r hr c hc i s hs k *
      GeometricPhaseOccupation.finiteCappedLaw J k j.castSucc) ≠ ⊤ from
        by rw [← PMF.bind_apply]; exact (phase J _).apply_ne_top _)
  simp only [ENNReal.toReal_mul, he] at hb
  rw [phase, PMF.bind_apply, ENNReal.tsum_toReal_eq (fun k =>
    ENNReal.mul_ne_top ((CriticalRenewalSource.gapLaw r hr c hc i s hs).apply_ne_top k)
      ((GeometricPhaseOccupation.finiteCappedLaw J k).apply_ne_top j.castSucc))]
  simp only [ENNReal.toReal_mul, he]
  simp only [CriticalRenewalSource.density, CriticalRenewalSource.weight, add_div, mul_add, add_mul, div_mul_eq_mul_div]
  cases i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_div, zero_mul]
    rw [tsum_div_const, hd.2.1]
  | true =>
    simp only [↓reduceIte]
    have hs2 := hl.1.mul_left c
    rw [Summable.tsum_add (hd.1.div_const _) (by simpa only [mul_assoc] using hs2.div_const _),
      tsum_div_const, hd.2.1, tsum_div_const]
    simp_rw [mul_assoc, tsum_mul_left, hl.2.1]

open CriticalRenewalSource GeometricPhaseOccupation CriticalRenewalTable

/-- A single terminal reward is powered before it is averaged. -/
def rewardMean (r J : ℕ) (f : PMF ℕ) : ℝ :=
  average (phase J f) (reward r J)

def occupationReward (r m J : ℕ) (s : ℝ) (p : ℕ) : ℝ :=
  ∑ j : Fin J, (1/(2 : ℝ)^(r*(j.val+1)))^p * occupation m s (j.val+1)

private lemma reward_moment_formula (r J : ℕ) (hr : 1 ≤ r) (c s eta : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hscale : s * (2 : ℝ) ^ J ≤ eta) (heta : eta ≤ 1)
    (i : Bool) (p : ℕ) (hp : p ≠ 0) :
    average (phase J (gapLaw r hr c hc i s hs)) (fun z => (reward r J z)^p) =
      (occupationReward r (2*r-1) J s p +
        if i then c*occupationReward r (r-1) J s p else 0) / normalizer r c i s := by
  rw [average, Fin.sum_univ_castSucc]
  simp only [reward, Fin.val_last, lt_self_iff_false, ↓reduceIte,
    zero_pow hp, mul_zero, add_zero, Fin.val_castSucc]
  simp only [show ∀ j : Fin J, j.val < J from fun j => j.isLt, ↓reduceIte]
  simp_rw [phase_live_mass r J hr c s eta hc hs hscale heta]
  cases i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [occupationReward, sum_div]
    apply sum_congr rfl
    intro j _
    ring
  | true =>
    simp only [↓reduceIte]
    simp only [occupationReward, mul_sum, ← sum_add_distrib, sum_div]
    apply sum_congr rfl
    intro j _
    ring

private lemma occupation_mono (r J : ℕ) (j : Fin J) (s eta : ℝ)
    (hs : 0 < s) (hscale : s * (2 : ℝ) ^ J ≤ eta) (heta : eta ≤ 1) :
    occupation (r-1) s (j.val+1) ≤ occupation (2*r-1) s (j.val+1) := by
  have hl := occupation_series (r-1) J j s eta hs hscale heta
  have hd := occupation_series (2*r-1) J j s eta hs hscale heta
  rw [← hl.2.1, ← hd.2.1]
  apply hl.1.tsum_le_tsum _ hd.1
  intro k
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  by_cases hk : k = 0
  · simp [term, hk]
  · simp only [term, hk, ↓reduceIte]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ k by omega))
      (by omega : r-1 ≤ 2*r-1)

private lemma occupation_reward_mono (r J : ℕ) (s eta : ℝ)
    (hs : 0 < s) (hscale : s * (2 : ℝ) ^ J ≤ eta) (heta : eta ≤ 1) (p : ℕ) :
    occupationReward r (r-1) J s p ≤ occupationReward r (2*r-1) J s p := by
  apply sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (occupation_mono r J j s eta hs hscale heta) (by positivity)

private lemma small_reward_bounds (r J : ℕ) (hr : 1 ≤ r) (s eta : ℝ)
    (hs : 0 < s) (hscale : s * (2 : ℝ) ^ J ≤ eta) (heta : eta ≤ 1) :
    lowerConstant (r-1)*(J : ℝ) ≤ occupationReward r (r-1) J s 1 ∧
      occupationReward r (r-1) J s 1 ≤ upperConstant (r-1)*(J : ℝ) := by
  have he : r-1+1 = r := by omega
  have hterm (j : Fin J) :
      lowerConstant (r-1) ≤
        (1/(2 : ℝ)^(r*(j.val+1))) * occupation (r-1) s (j.val+1) ∧
      (1/(2 : ℝ)^(r*(j.val+1))) * occupation (r-1) s (j.val+1) ≤
        upperConstant (r-1) := by
    have h := occupation_series (r-1) J j s eta hs hscale heta
    have ht : 0 < (2 : ℝ)^(r*(j.val+1)) := by positivity
    rw [he, Nat.mul_comm (j.val+1) r] at h
    constructor
    · have hh := (le_div_iff₀ ht).2 h.2.2.1
      simpa [div_eq_mul_inv, mul_comm] using hh
    · have hh := (div_le_iff₀ ht).2 h.2.2.2
      simpa [div_eq_mul_inv, mul_comm] using hh
  constructor
  · simpa [occupationReward, mul_comm] using
      (sum_le_sum (s := univ) fun j _ => (hterm j).1)
  · simpa [occupationReward, mul_comm] using
      (sum_le_sum (s := univ) fun j _ => (hterm j).2)

private lemma dyadic_sum (r J : ℕ) (hr : 1 ≤ r) :
    (∑ j : Fin J, (2 : ℝ)^(r*(j.val+1))) ≤
      (2 : ℝ)^(r*J)/(1-1/(2 : ℝ)^r) := by
  let t : ℝ := (2 : ℝ)^r
  have ht : 1 < t := one_lt_pow₀ (by norm_num) (by omega)
  have hid (n : ℕ) :
      (∑ j : Fin n, t^(j.val+1))*(t-1) = t*(t^n-1) := by
    calc
      _ = ((∑ j : Fin n, t^j.val)*t)*(t-1) := by
        simp only [pow_succ, ← sum_mul]
      _ = t*((∑ j ∈ range n, t^j)*(t-1)) := by
        rw [← Fin.sum_univ_eq_sum_range]
        ring
      _ = _ := by rw [geom_sum_mul]
  have hden : 0 < 1-1/t := sub_pos.mpr ((div_lt_one (by linarith)).2 ht)
  apply (le_div_iff₀ hden).2
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have he : (∑ j : Fin J, t^(j.val+1))*(1-1/t) = t^J-1 := by
    apply (mul_right_inj' ht0).1
    calc
      t*((∑ j : Fin J, t^(j.val+1))*(1-1/t)) =
          (∑ j : Fin J, t^(j.val+1))*(t-1) := by field_simp
      _ = t*(t^J-1) := hid J
  have hpow (n : ℕ) : t^n = (2 : ℝ)^(r*n) := (pow_mul _ _ _).symm
  simpa only [← hpow] using (show
    (∑ j : Fin J, t^(j.val+1))*(1-1/t) ≤ t^J by rw [he]; linarith)

private lemma large_reward_bounds (r J : ℕ) (hr : 1 ≤ r) (s eta : ℝ)
    (hs : 0 < s) (hscale : s * (2 : ℝ) ^ J ≤ eta) (heta : eta ≤ 1) :
    occupationReward r (2*r-1) J s 1 ≤
        (upperConstant (2*r-1)/(1-1/(2 : ℝ)^r))*(2 : ℝ)^(r*J) ∧
      occupationReward r (2*r-1) J s 2 ≤ upperConstant (2*r-1)*(J : ℝ) := by
  have he : 2*r-1+1 = 2*r := by omega
  have hterm (j : Fin J) :
      (1/(2 : ℝ)^(r*(j.val+1))) * occupation (2*r-1) s (j.val+1) ≤
        upperConstant (2*r-1)*(2 : ℝ)^(r*(j.val+1)) ∧
      (1/(2 : ℝ)^(r*(j.val+1)))^2 * occupation (2*r-1) s (j.val+1) ≤
        upperConstant (2*r-1) := by
    have h := (occupation_series (2*r-1) J j s eta hs hscale heta).2.2.2
    have hp : (2 : ℝ)^((j.val+1)*(2*r-1+1)) =
        ((2 : ℝ)^(r*(j.val+1)))^2 := by
      rw [← pow_mul, he]
      congr 1
      ring
    rw [hp] at h
    have ht : 0 < (2 : ℝ)^(r*(j.val+1)) := by positivity
    constructor
    · have hh := (div_le_iff₀ ht).2 (show occupation (2*r-1) s (j.val+1) ≤
        (upperConstant (2*r-1)*(2 : ℝ)^(r*(j.val+1))) *
          (2 : ℝ)^(r*(j.val+1)) by nlinarith)
      simpa [div_eq_mul_inv, mul_comm] using hh
    · have hh := (div_le_iff₀ (sq_pos_of_pos ht)).2 h
      simpa [div_eq_mul_inv, mul_comm, inv_pow] using hh
  constructor
  · calc
      _ ≤ ∑ j : Fin J, upperConstant (2*r-1)*(2 : ℝ)^(r*(j.val+1)) := by
        simpa [occupationReward] using sum_le_sum (s := univ) (fun j _ => (hterm j).1)
      _ ≤ upperConstant (2*r-1) * ((2 : ℝ)^(r*J)/(1-1/(2 : ℝ)^r)) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (dyadic_sum r J hr) (by unfold upperConstant; positivity)
      _ = _ := by ring
  · simpa [occupationReward, mul_comm] using sum_le_sum (s := univ) (fun j _ => (hterm j).2)

def lowerCell (delta x : ℝ) : ℤ := ⌊x/delta⌋
def upperProbability (delta x : ℝ) : ℝ := x/delta - (lowerCell delta x : ℝ)

def roundedTick {J : ℕ} (v : Fin (J + 1) → ℝ) (theta delta : ℝ) : Tick J where
  lower z := lowerCell delta (v z-theta)
  prob z := ⟨upperProbability delta (v z-theta), Int.fract_nonneg _⟩
  prob_le_one z := by
    exact_mod_cast (Int.fract_lt_one ((v z-theta)/delta)).le

private lemma rounded_probability {J : ℕ} (v : Fin (J + 1) → ℝ) (theta delta : ℝ)
    (z : Fin (J + 1)) :
    ((roundedTick v theta delta).prob z : ℝ) = upperProbability delta (v z-theta) := rfl

private lemma signed_rounding (delta x : ℝ) (hd : 0 < delta) :
    let n : ℝ := lowerCell delta x
    let p := upperProbability delta x
    0 ≤ p ∧ p < 1 ∧
    (1-p)*(delta*n)+p*(delta*(n+1)) = x ∧
    (1-p)*(delta*n)^2+p*(delta*(n+1))^2 =
      x^2+delta^2*p*(1-p) ∧
    delta^2*p*(1-p) ≤ delta*|x| ∧
    (∀ b : Bool, |delta*(n+if b then 1 else 0)| ≤ |x|+delta) := by
  intro n p
  have hp0 : 0 ≤ p := Int.fract_nonneg _
  have hp1 : p < 1 := Int.fract_lt_one _
  have ht : delta*(n+p) = x := by
    dsimp [n,p,upperProbability]
    field_simp
    ring
  have hnlo : delta*n ≤ x := by nlinarith
  have hnhi : x ≤ delta*(n+1) := by nlinarith
  have hv : p*(1-p) ≤ |x|/delta := by
    by_cases hx : 0 ≤ x
    · have hn : 0 ≤ n := by
        dsimp [n,lowerCell]
        exact_mod_cast Int.floor_nonneg.2 (div_nonneg hx hd.le)
      rw [abs_of_nonneg hx]
      have hpt : p ≤ x/delta := by
        dsimp [p,upperProbability,n] at *
        linarith
      nlinarith [sq_nonneg p]
    · have hn : n+1 ≤ 0 := by
        have hfl : lowerCell delta x < 0 := Int.floor_lt.2 (by simpa only [Int.cast_zero] using div_neg_of_neg_of_pos (lt_of_not_ge hx) hd)
        have hni : lowerCell delta x + 1 ≤ 0 := by omega
        change (lowerCell delta x : ℝ)+1 ≤ 0
        exact_mod_cast hni
      rw [abs_of_neg (lt_of_not_ge hx)]
      have hpt : 1-p ≤ -x/delta := by
        dsimp [p,upperProbability]
        dsimp [n] at hn
        rw [neg_div]
        linarith
      nlinarith [sq_nonneg (1-p)]
  refine ⟨hp0,hp1,by nlinarith,by rw [← ht]; ring,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hv (sq_nonneg delta)
    have he : delta^2*(|x|/delta) = delta*|x| := by field_simp
    nlinarith [he]
  · intro b
    have habs := abs_le.mp (le_refl |x|)
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero, mul_add, mul_one]
    · apply abs_le.2
      constructor <;> nlinarith
    · apply abs_le.2
      constructor <;> nlinarith

private lemma occupation_reward_nonneg (r m J : ℕ) (s : ℝ) (p : ℕ) :
    0 ≤ occupationReward r m J s p := by
  apply sum_nonneg
  intro j _
  exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

private lemma quotient_nonneg (r : ℕ) (s : ℝ) : 0 ≤ quotient r s := by
  apply div_nonneg <;> apply tsum_nonneg <;> intro k <;>
    unfold term <;> split_ifs <;> positivity

private lemma exact_contrast (r J : ℕ) (hr : 1 ≤ r) (c s eta : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hscale : s * (2 : ℝ) ^ J ≤ eta) (heta : eta ≤ 1) :
    rewardMean r J (gapLaw r hr c hc true s hs) -
      rewardMean r J (gapLaw r hr c hc false s hs) =
      c / normalizer r c true s *
        (occupationReward r (r-1) J s 1 -
          quotient r s * occupationReward r (2*r-1) J s 1) := by
  have h1 := reward_moment_formula r J hr c s eta hc hs hscale heta true 1 one_ne_zero
  have h0 := reward_moment_formula r J hr c s eta hc hs hscale heta false 1 one_ne_zero
  simp only [pow_one, ↓reduceIte, Bool.false_eq_true, add_zero] at h0 h1
  change rewardMean r J _ = _ at h0 h1
  rw [h1,h0]
  have hZ := (source_laws r hr c hc s hs).1.2.1
  have hp0 := ((source_laws r hr c hc s hs).1.1 false).normalizer_positive
  have hp1 := ((source_laws r hr c hc s hs).1.1 true).normalizer_positive
  apply (mul_right_inj' (mul_ne_zero hp0.ne' hp1.ne')).mp
  field_simp
  rw [hZ]
  ring

set_option maxHeartbeats 1000000 in
-- A common neighborhood controls both labels and both reward moments uniformly in the cap.
private lemma source_reward_bounds (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c) :
    ∃ eta sStar Dlo Dhi Cmean Csecond : ℝ,
      0 < eta ∧ eta < 1 ∧ 0 < sStar ∧ sStar < 1 ∧
      0 < Dlo ∧ 0 < Dhi ∧ 0 < Cmean ∧ 0 < Csecond ∧
      ∀ (s : ℝ) (hs : 0 < s), s < sStar → ∀ J : ℕ, 1 ≤ J →
        s * (2 : ℝ) ^ J ≤ eta →
        let m := fun i => rewardMean r J (gapLaw r hr c hc i s hs)
        let I := s^(2*r)*(J : ℝ)
        Dlo*I ≤ m true-m false ∧ m true-m false ≤ Dhi*I ∧
        (∀ i, 0 ≤ m i ∧ m i ≤ Cmean*s^(2*r)*(2 : ℝ)^(r*J) ∧
          average (phase J (gapLaw r hr c hc i s hs)) (fun z => (reward r J z)^2)
            ≤ Csecond*I) := by
  obtain ⟨sStar,zlo,zhi,G,Cmu,Cbeta,hsStar,hsStar1,hzlo,hzhi,hG,hCmu,hCbeta,hscalar⟩ :=
    common_scalar_neighborhood r hr c hc
  let b := lowerConstant (r-1)
  let B := upperConstant (r-1)
  let Cstar := upperConstant (2*r-1)/(1-1/(2 : ℝ)^r)
  have hb : 0 < b := by dsimp [b,lowerConstant]; positivity
  have hB : 0 < B := by dsimp [B,upperConstant]; positivity
  have ht : 1 < (2 : ℝ)^r := one_lt_pow₀ (by norm_num) (by omega)
  have hden : 0 < 1-1/(2 : ℝ)^r := by
    apply sub_pos.2
    exact (div_lt_one (by positivity)).2 ht
  have hCstar : 0 < Cstar := div_pos (by unfold upperConstant; positivity) hden
  let eta := min (1/2 : ℝ) (b/(2*G*Cstar))
  have heta : 0 < eta := lt_min (by norm_num) (div_pos hb (by positivity))
  have heta1 : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hsmall : G*Cstar*eta^r ≤ b/2 := by
    have hp := pow_le_of_le_one heta.le heta1.le (by omega : r ≠ 0)
    have he := (le_div_iff₀ (by positivity : 0 < 2*G*Cstar)).mp (min_le_right (1/2) (b/(2*G*Cstar)))
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ G*Cstar by positivity)
    nlinarith
  refine ⟨eta,sStar,c*b/(2*zhi),c*B/zlo,(1+c)*Cstar/zlo,
    (1+c)*upperConstant (2*r-1)/zlo,heta,heta1,hsStar,hsStar1,
    by positivity,by positivity,by positivity,
    by unfold upperConstant; positivity,?_⟩
  intro s hs hss J hJ hscale m I
  have hsc := hscalar s hs hss
  have hp : 0 < s^(2*r) := pow_pos hs _
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hQ := small_reward_bounds r J hr s eta hs hscale heta1.le
  have hR := large_reward_bounds r J hr s eta hs hscale heta1.le
  let Q := occupationReward r (r-1) J s 1
  let R := occupationReward r (2*r-1) J s 1
  have hQlo : b*(J : ℝ) ≤ Q := hQ.1
  have hQhi : Q ≤ B*(J : ℝ) := hQ.2
  have hRhi : R ≤ Cstar*(2 : ℝ)^(r*J) := hR.1
  have hR0 : 0 ≤ R := occupation_reward_nonneg _ _ _ _ _
  have hg0 : 0 ≤ quotient r s := quotient_nonneg _ _
  have hcorr : quotient r s * R ≤ b/2 := by
    calc
      _ ≤ (G*s^r)*(Cstar*(2 : ℝ)^(r*J)) :=
        mul_le_mul hsc.2 hRhi hR0 (by positivity)
      _ = G*Cstar*(s * (2 : ℝ) ^ J)^r := by rw [mul_pow, ← pow_mul]; ring_nf
      _ ≤ G*Cstar*eta^r := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hscale r) (by positivity)
      _ ≤ b/2 := hsmall
  have hbrace0 : b/2*(J : ℝ) ≤ Q-quotient r s*R := by
    nlinarith [mul_le_mul_of_nonneg_left hJr hb.le]
  have hbrace1 : Q-quotient r s*R ≤ B*(J : ℝ) := by
    nlinarith [mul_nonneg hg0 hR0]
  have hcontrast : m true-m false = c*(1/normalizer r c true s)*
      (Q-quotient r s*R) := by
    simpa only [m,Q,R,div_eq_mul_inv,mul_one_div,one_mul] using
      exact_contrast r J hr c s eta hc hs hscale heta1.le
  have hinv (i : Bool) :
      s^(2*r)/zhi ≤ 1/normalizer r c i s ∧
        1/normalizer r c i s ≤ s^(2*r)/zlo := by
    have hz := ((source_laws r hr c hc s hs).1.1 i).normalizer_positive
    constructor
    · rw [div_le_div_iff₀ hzhi hz]
      have hh := (le_div_iff₀ hp).1 (hsc.1 i).2.1
      nlinarith
    · rw [div_le_div_iff₀ hz hzlo]
      have hh := (div_le_iff₀ hp).1 (hsc.1 i).1
      nlinarith
  refine ⟨?_,?_,?_⟩
  · rw [hcontrast]
    calc
      _ = (c*(s^(2*r)/zhi))*(b/2*(J : ℝ)) := by dsimp [I]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hinv true).1 hc.le)
        hbrace0 (mul_nonneg (by positivity) (by linarith))
          (mul_nonneg hc.le (one_div_nonneg.mpr
            ((source_laws r hr c hc s hs).1.1 true).normalizer_positive.le))
  · rw [hcontrast]
    calc
      _ ≤ (c*(s^(2*r)/zlo))*(B*(J : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hinv true).2 hc.le)
          hbrace1 ((mul_nonneg (by positivity) (by linarith)).trans hbrace0) (by positivity)
      _ = _ := by dsimp [I]; ring
  · intro i
    have hm := reward_moment_formula r J hr c s eta hc hs hscale heta1.le i 1 one_ne_zero
    have hv := reward_moment_formula r J hr c s eta hc hs hscale heta1.le i 2 (by omega)
    simp only [pow_one] at hm
    change m i = _ at hm
    have hnum (p : ℕ) :
        occupationReward r (2*r-1) J s p +
          (if i then c*occupationReward r (r-1) J s p else 0) ≤
          (1+c)*occupationReward r (2*r-1) J s p := by
      have hmono := occupation_reward_mono r J s eta hs hscale heta1.le p
      have hnon := occupation_reward_nonneg r (2*r-1) J s p
      cases i <;> simp only [Bool.false_eq_true,↓reduceIte,add_zero]
      · nlinarith
      · nlinarith [mul_le_mul_of_nonneg_left hmono hc.le]
    have hmoment (p : ℕ) :
        (occupationReward r (2*r-1) J s p +
          (if i then c*occupationReward r (r-1) J s p else 0))/normalizer r c i s ≤
          ((1+c)*occupationReward r (2*r-1) J s p)*(s^(2*r)/zlo) := by
      have hnon : 0 ≤ occupationReward r (2*r-1) J s p +
          (if i then c*occupationReward r (r-1) J s p else 0) := by
        split_ifs
        · exact add_nonneg (occupation_reward_nonneg _ _ _ _ _)
            (mul_nonneg hc.le (occupation_reward_nonneg _ _ _ _ _))
        · exact add_nonneg (occupation_reward_nonneg _ _ _ _ _) (le_refl 0)
      calc
        _ ≤ ((1+c)*occupationReward r (2*r-1) J s p)/normalizer r c i s :=
          div_le_div_of_nonneg_right (hnum p) (by
            exact ((source_laws r hr c hc s hs).1.1 i).normalizer_positive.le)
        _ ≤ _ := by
          rw [div_eq_mul_inv, ← one_div]
          exact mul_le_mul_of_nonneg_left (hinv i).2 (by
            exact mul_nonneg (by positivity) (occupation_reward_nonneg _ _ _ _ _))
    refine ⟨average_nonneg _ _ (fun z => (reward_bounds r J hr z).1),?_,?_⟩
    · rw [hm]
      calc
        _ ≤ ((1+c)*R)*(s^(2*r)/zlo) := hmoment 1
        _ ≤ ((1+c)*(Cstar*(2 : ℝ)^(r*J)))*(s^(2*r)/zlo) := by
          gcongr
        _ = _ := by ring
    · rw [hv]
      calc
        _ ≤ ((1+c)*occupationReward r (2*r-1) J s 2)*(s^(2*r)/zlo) := hmoment 2
        _ ≤ ((1+c)*(upperConstant (2*r-1)*(J : ℝ)))*(s^(2*r)/zlo) := by
          gcongr
          exact hR.2
        _ = _ := by dsimp [I]; ring

private lemma grid_bounds (r J : ℕ) (hr : 1 ≤ r) (hJ : 1 ≤ J) :
    0 < grid r J ∧ grid r J ≤ 1/2 := by
  have hlin : 2*(J : ℝ) ≤ (2 : ℝ)^J := by
    exact_mod_cast (Nat.mul_le_pow (a := 2) (by decide) J)
  have he : J ≤ r*J := Nat.le_mul_of_pos_left _ (by omega)
  have hp := hlin.trans (pow_le_pow_right₀ (by norm_num) he)
  constructor
  · exact div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^(r*J))).2
    linarith

private lemma average_const {J : ℕ} (p : PMF (Fin (J + 1))) (a : ℝ) :
    average p (fun _ => a) = a := by
  simp only [average, ← sum_mul, pmf_sum_real, one_mul]

private lemma average_add {J : ℕ} (p : PMF (Fin (J + 1)))
    (v w : Fin (J + 1) → ℝ) :
    average p (fun z => v z+w z) = average p v+average p w := by
  simp only [average, mul_add, sum_add_distrib]

private lemma average_sub {J : ℕ} (p : PMF (Fin (J + 1)))
    (v w : Fin (J + 1) → ℝ) :
    average p (fun z => v z-w z) = average p v-average p w := by
  simp only [average, mul_sub, sum_sub_distrib]

private lemma average_mul {J : ℕ} (p : PMF (Fin (J + 1)))
    (v : Fin (J + 1) → ℝ) (a : ℝ) :
    average p (fun z => v z*a) = average p v*a := by
  simp only [average, ← mul_assoc, sum_mul]

private lemma average_square {J : ℕ} (p : PMF (Fin (J + 1)))
    (v : Fin (J + 1) → ℝ) :
    (average p v)^2 ≤ average p (fun z => (v z)^2) := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (s := univ)
    (r := fun z => (p z).toReal*v z)
    (f := fun z => (p z).toReal)
    (g := fun z => (p z).toReal*(v z)^2)
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    (fun _ _ => le_of_eq (by ring))
  simpa only [average, pmf_sum_real, one_mul] using h

/-- The terminal phase and fresh tick are retained only in this mathematical joint law. -/
def phaseTickLaw {J : ℕ} (p : PMF (Fin (J + 1))) (t : Tick J) :
    PMF (Fin (J + 1) × Bool) :=
  p.bind fun z => (t.coin z).map fun b => (z,b)

private lemma phaseTick_mass {J : ℕ} (p : PMF (Fin (J + 1))) (t : Tick J)
    (z : Fin (J + 1)) (b : Bool) :
    phaseTickLaw p t (z,b) = p z*(t.coin z b) := by
  simp only [phaseTickLaw, PMF.bind_apply, PMF.map_apply, tsum_fintype]
  cases b <;> simp [mul_ite, eq_comm]

private lemma phaseTick_integral {J : ℕ} (p : PMF (Fin (J + 1))) (t : Tick J)
    (v : Fin (J + 1) × Bool → ℝ) :
    ∫ zb, v zb ∂(phaseTickLaw p t).toMeasure =
      average p (fun z =>
        (1-(t.prob z : ℝ))*v (z,false)+(t.prob z : ℝ)*v (z,true)) := by
  rw [PMF.integral_eq_sum, Fintype.sum_prod_type]
  simp_rw [phaseTick_mass, ENNReal.toReal_mul, smul_eq_mul]
  apply sum_congr rfl
  intro z _
  have hprob : (t.prob z : ℝ) ≤ 1 := by exact_mod_cast t.prob_le_one z
  simp [Tick.coin, PMF.bernoulli_apply, NNReal.coe_sub (t.prob_le_one z), mul_add, mul_assoc, add_comm]

private lemma pair_marginal {J : ℕ} (f : PMF ℕ) (t : Tick J) :
    (pairLaw f t).map Prod.snd =
      (phaseTickLaw (phase J f) t).map (fun zb => t.increment zb.1 zb.2) := by
  simp only [pairLaw, phaseTickLaw, phase, PMF.map_bind, PMF.map_comp,
    PMF.bind_bind, Function.comp_def]

private lemma pair_integral {J : ℕ} (f : PMF ℕ) (t : Tick J) (g : ℤ → ℝ) :
    Integrable (fun ku : ℕ × ℤ => g ku.2) (pairLaw f t).toMeasure ∧
      (∫ ku, g ku.2 ∂(pairLaw f t).toMeasure) =
        average (phase J f) (fun z =>
          (1-(t.prob z : ℝ))*g (t.increment z false)+
            (t.prob z : ℝ)*g (t.increment z true)) := by
  let q := phaseTickLaw (phase J f) t
  let inc : Fin (J + 1) × Bool → ℤ := fun zb => t.increment zb.1 zb.2
  have hi : Measurable inc := measurable_of_countable _
  have hg : Measurable g := measurable_of_countable _
  have hm : (pairLaw f t).toMeasure.map Prod.snd = q.toMeasure.map inc := by
    rw [PMF.toMeasure_map Prod.snd _ measurable_snd, PMF.toMeasure_map inc _ hi, pair_marginal]
  have hgi : Integrable g (q.toMeasure.map inc) :=
    (integrable_map_measure hg.aestronglyMeasurable hi.aemeasurable).2
      (show Integrable (g ∘ inc) q.toMeasure from .of_finite)
  have hgp : Integrable g ((pairLaw f t).toMeasure.map Prod.snd) := by
    rw [hm]
    exact hgi
  refine ⟨hgp.comp_measurable measurable_snd, ?_⟩
  calc
    _ = ∫ u, g u ∂((pairLaw f t).toMeasure.map Prod.snd) :=
      (integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ u, g u ∂(q.toMeasure.map inc) := by rw [hm]
    _ = ∫ zb, g (inc zb) ∂q.toMeasure :=
      integral_map hi.aemeasurable hg.aestronglyMeasurable
    _ = _ := phaseTick_integral _ _ _


private lemma rounded_mean {J : ℕ} (f : PMF ℕ)
    (v : Fin (J + 1) → ℝ) (theta delta : ℝ) (hd : 0 < delta) :
    Integrable (fun ku : ℕ × ℤ => (ku.2 : ℝ)*delta)
      (pairLaw f (roundedTick v theta delta)).toMeasure ∧
    (∫ ku, (ku.2 : ℝ)*delta ∂(pairLaw f (roundedTick v theta delta)).toMeasure) =
      average (phase J f) v-theta := by
  obtain ⟨hi,he⟩ := pair_integral f (roundedTick v theta delta) (fun u => (u : ℝ)*delta)
  refine ⟨hi, he.trans ?_⟩
  calc
    _ = average (phase J f) (fun z => v z-theta) := by
      congr 1
      funext z
      have h := (signed_rounding delta (v z-theta) hd).2.2.1
      rw [rounded_probability]
      simp only [Tick.increment,roundedTick,Int.cast_add,Int.cast_ite,Int.cast_one,
        Int.cast_zero,Bool.false_eq_true,↓reduceIte,add_zero]
      nlinarith only [h]
    _ = _ := by rw [average_sub,average_const]

private lemma rounded_second {J : ℕ} (f : PMF ℕ)
    (v : Fin (J + 1) → ℝ) (theta delta : ℝ) (hd : 0 < delta) :
    Integrable (fun ku : ℕ × ℤ => ((ku.2 : ℝ)*delta)^2)
      (pairLaw f (roundedTick v theta delta)).toMeasure ∧
    (∫ ku, ((ku.2 : ℝ)*delta)^2
      ∂(pairLaw f (roundedTick v theta delta)).toMeasure) ≤
      average (phase J f) (fun z => (v z-theta)^2) +
        delta*average (phase J f) (fun z => |v z-theta|) := by
  obtain ⟨hi,he⟩ := pair_integral f (roundedTick v theta delta)
    (fun u => ((u : ℝ)*delta)^2)
  refine ⟨hi, he.le.trans ?_⟩
  rw [← mul_comm (average _ _) delta, ← average_mul, ← average_add]
  apply sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have h := signed_rounding delta (v z-theta) hd
  have heq := h.2.2.2.1
  have hnoise := h.2.2.2.2.1
  have hcast (b : Bool) :
      ((roundedTick v theta delta).increment z b : ℝ)*delta =
        delta*((lowerCell delta (v z-theta) : ℝ)+if b then 1 else 0) := by
    simp only [Tick.increment,roundedTick, Int.cast_add, Int.cast_ite,
      Int.cast_one, Int.cast_zero]
    ring
  dsimp only
  rw [rounded_probability, hcast false, hcast true]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  nlinarith only [heq,hnoise]

private lemma centered_bounds {J : ℕ} (p0 p1 : PMF (Fin (J + 1)))
    (v : Fin (J + 1) → ℝ) (Cmean Csecond I Lr : ℝ)
    (hmean : ∀ i : Bool, 0 ≤ average (if i then p1 else p0) v ∧
      average (if i then p1 else p0) v ≤ Cmean*Lr)
    (hsecond : ∀ i : Bool,
      average (if i then p1 else p0) (fun z => (v z)^2) ≤ Csecond*I)
    (hv : ∀ z, 0 ≤ v z) :
    let theta := (average p0 v+average p1 v)/2
    0 ≤ theta ∧ theta ≤ Cmean*Lr ∧ theta^2 ≤ Csecond*I ∧
      ∀ i : Bool,
        average (if i then p1 else p0) (fun z => (v z-theta)^2) ≤ 4*Csecond*I ∧
        average (if i then p1 else p0) (fun z => |v z-theta|) ≤ 2*Cmean*Lr := by
  intro theta
  have hm0 := hmean false
  have hm1 := hmean true
  have hs0 := hsecond false
  have hs1 := hsecond true
  simp only [Bool.false_eq_true,↓reduceIte] at hm0 hm1 hs0 hs1
  have ht0 : 0 ≤ theta := by dsimp [theta]; linarith
  have ht1 : theta ≤ Cmean*Lr := by dsimp [theta]; linarith
  have htsq : theta^2 ≤ Csecond*I := by
    have hj0 := average_square p0 v
    have hj1 := average_square p1 v
    dsimp [theta]
    nlinarith [sq_nonneg (average p0 v-average p1 v)]
  refine ⟨ht0,ht1,htsq,?_⟩
  intro i
  let p := if i then p1 else p0
  constructor
  · calc
      _ ≤ average p (fun z => 2*(v z)^2+2*theta^2) := by
        apply sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        nlinarith [sq_nonneg (v z+theta)]
      _ = 2*average p (fun z => (v z)^2)+2*theta^2 := by
        simp_rw [mul_comm (2 : ℝ) ((v _)^2), average_add, average_mul, average_const]
        ring
      _ ≤ _ := by have hh := hsecond i; change average p _ ≤ _ at hh; nlinarith
  · calc
      _ ≤ average p (fun z => v z+theta) := by
        apply sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [hv z],by linarith [hv z]⟩) ENNReal.toReal_nonneg
      _ = average p v+theta := by rw [average_add,average_const]
      _ ≤ _ := by have hh := (hmean i).2; change average p v ≤ _ at hh; linarith

set_option maxHeartbeats 1000000 in
-- The uniform source estimates and two finite joint-law integrals share a large dependent telescope.
/-- All source-specific clauses of the one-gap theorem, with one common literal tick table. -/
theorem uniform_one_gap (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c) :
    ∃ eta sStar Dlo Dhi Cmean Csecond Vzero : ℝ,
      0 < eta ∧ eta < 1 ∧ 0 < sStar ∧ sStar < 1 ∧
      0 < Dlo ∧ 0 < Dhi ∧ 0 < Cmean ∧ 0 < Csecond ∧ 0 < Vzero ∧
      Vzero = 4*Csecond+2*Cmean ∧
      ∀ (s : ℝ) (hs : 0 < s), s < sStar → ∀ J : ℕ, 1 ≤ J →
        s * (2 : ℝ) ^ J ≤ eta →
        let f := fun i => gapLaw r hr c hc i s hs
        let m := fun i => rewardMean r J (f i)
        let theta := (m false+m true)/2
        let Delta := m true-m false
        let I := s^(2*r)*(J : ℝ)
        let delta := grid r J
        let t := roundedTick (reward r J) theta delta
        0 < I ∧ 0 < delta ∧ delta ≤ 1/2 ∧
        Dlo*I ≤ Delta ∧ Delta ≤ Dhi*I ∧
        0 ≤ theta ∧ theta ≤ 1/(2 : ℝ)^r ∧ theta^2 ≤ Csecond*I ∧
        Delta = c/normalizer r c true s *
          (occupationReward r (r-1) J s 1 -
            quotient r s*occupationReward r (2*r-1) J s 1) ∧
        (∀ z, 0 ≤ reward r J z ∧ reward r J z ≤ 1/(2 : ℝ)^r ∧
          0 ≤ (t.prob z : ℝ) ∧ (t.prob z : ℝ) < 1 ∧
          ∀ b, |(t.increment z b : ℝ)*delta| ≤ 1) ∧
        (∀ (i : Bool) (j : Fin J),
          (phase J (f i) j.castSucc).toReal =
            (occupation (2*r-1) s (j.val+1) +
              if i then c*occupation (r-1) s (j.val+1) else 0)/normalizer r c i s) ∧
        ∀ i : Bool,
          0 ≤ m i ∧ m i ≤ Cmean*s^(2*r)*(2 : ℝ)^(r*J) ∧
          average (phase J (f i)) (fun z => (reward r J z)^2) ≤ Csecond*I ∧
          average (phase J (f i)) (fun z => (reward r J z-theta)^2) ≤ 4*Csecond*I ∧
          delta*average (phase J (f i)) (fun z => |reward r J z-theta|) ≤ 2*Cmean*I ∧
          Integrable (fun ku : ℕ × ℤ => (ku.2 : ℝ)*delta) (pairLaw (f i) t).toMeasure ∧
          Integrable (fun ku : ℕ × ℤ => ((ku.2 : ℝ)*delta)^2) (pairLaw (f i) t).toMeasure ∧
          (∫ ku, (ku.2 : ℝ)*delta ∂(pairLaw (f i) t).toMeasure) =
            (if i then Delta/2 else -Delta/2) ∧
          (∫ ku, ((ku.2 : ℝ)*delta)^2 ∂(pairLaw (f i) t).toMeasure) ≤ Vzero*I := by
  obtain ⟨eta,sStar,Dlo,Dhi,Cmean,Csecond,heta,heta1,hsStar,hsStar1,
    hDlo,hDhi,hCmean,hCsecond,hbounds⟩ := source_reward_bounds r hr c hc
  refine ⟨eta,sStar,Dlo,Dhi,Cmean,Csecond,4*Csecond+2*Cmean,
    heta,heta1,hsStar,hsStar1,hDlo,hDhi,hCmean,hCsecond,by positivity,rfl,?_⟩
  intro s hs hss J hJ hscale f m theta Delta I delta t
  have hb := hbounds s hs hss J hJ hscale
  have hgrid := grid_bounds r J hr hJ
  have hI : 0 < I := mul_pos (pow_pos hs _) (by exact_mod_cast (show 0 < J by omega))
  have hseconds (i : Bool) :
      average (if i then phase J (f true) else phase J (f false))
        (fun z => (reward r J z)^2) ≤ Csecond*I := by
    cases i
    · exact (hb.2.2 false).2.2
    · exact (hb.2.2 true).2.2
  have hmeans' (i : Bool) :
      0 ≤ average (if i then phase J (f true) else phase J (f false)) (reward r J) ∧
        average (if i then phase J (f true) else phase J (f false)) (reward r J) ≤
          Cmean*(s^(2*r)*(2 : ℝ)^(r*J)) := by
    cases i
    · exact ⟨(hb.2.2 false).1, by simpa only [mul_assoc,rewardMean,f,Bool.false_eq_true,↓reduceIte] using (hb.2.2 false).2.1⟩
    · exact ⟨(hb.2.2 true).1, by simpa only [mul_assoc,rewardMean,f,Bool.false_eq_true,↓reduceIte] using (hb.2.2 true).2.1⟩
  have hcents := centered_bounds (phase J (f false)) (phase J (f true)) (reward r J)
    Cmean Csecond I (s^(2*r)*(2 : ℝ)^(r*J))
    hmeans' hseconds (fun z => (reward_bounds r J hr z).1)
  change 0 ≤ theta ∧ theta ≤ _ ∧ theta^2 ≤ _ ∧ _ at hcents
  have htheta : theta ≤ 1/(2 : ℝ)^r := by
    have hm0 := average_le (phase J (f false)) (reward r J) (1/(2 : ℝ)^r)
      (fun z => (reward_bounds r J hr z).2.1)
    have hm1 := average_le (phase J (f true)) (reward r J) (1/(2 : ℝ)^r)
      (fun z => (reward_bounds r J hr z).2.1)
    change m false ≤ _ at hm0
    change m true ≤ _ at hm1
    dsimp [theta]
    linarith
  have hhalf : 1/(2 : ℝ)^r ≤ 1/2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    simpa using pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) hr
  refine ⟨hI,hgrid.1,hgrid.2,hb.1,hb.2.1,hcents.1,htheta,hcents.2.2.1,
    exact_contrast r J hr c s eta hc hs hscale heta1.le,?_,?_,?_⟩
  · intro z
    have hrz := reward_bounds r J hr z
    have hround := signed_rounding delta (reward r J z-theta) hgrid.1
    refine ⟨hrz.1,hrz.2.1,hround.1,hround.2.1,?_⟩
    intro b
    have habs : |reward r J z-theta| ≤ 1/(2 : ℝ)^r :=
      abs_le.2 ⟨by linarith [hcents.1],by linarith [hcents.1]⟩
    have h := hround.2.2.2.2.2 b
    have hcast :
        (t.increment z b : ℝ)*delta =
          delta*((lowerCell delta (reward r J z-theta) : ℝ)+if b then 1 else 0) := by
      simp only [t,Tick.increment,roundedTick,Int.cast_add,Int.cast_ite,Int.cast_one,Int.cast_zero]
      ring
    rw [hcast]
    exact h.trans (by linarith [hgrid.2])
  · intro i j
    exact phase_live_mass r J hr c s eta hc hs hscale heta1.le i j
  · intro i
    have hceni :
        average (phase J (f i)) (fun z => (reward r J z-theta)^2) ≤ 4*Csecond*I ∧
        average (phase J (f i)) (fun z => |reward r J z-theta|) ≤
          2*Cmean*(s^(2*r)*(2 : ℝ)^(r*J)) := by
      cases i
      · exact hcents.2.2.2 false
      · exact hcents.2.2.2 true
    have hnoise :
        delta*average (phase J (f i)) (fun z => |reward r J z-theta|) ≤ 2*Cmean*I := by
      calc
        _ ≤ delta*(2*Cmean*(s^(2*r)*(2 : ℝ)^(r*J))) :=
          mul_le_mul_of_nonneg_left hceni.2 hgrid.1.le
        _ = _ := by dsimp [delta,grid,I]; field_simp <;> ring
    have hmean := rounded_mean (f i) (reward r J) theta delta hgrid.1
    have hsecond := rounded_second (f i) (reward r J) theta delta hgrid.1
    refine ⟨(hb.2.2 i).1,(hb.2.2 i).2.1,(hb.2.2 i).2.2,hceni.1,hnoise,
      hmean.1,hsecond.1,?_,?_⟩
    · rw [hmean.2]
      change m i-theta = _
      cases i <;> dsimp [theta,Delta] <;> ring
    · exact hsecond.2.trans (by nlinarith only [hceni.1,hnoise])

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalOneGap

end
end
