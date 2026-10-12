/- GID: D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationConfidenceFailure
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Learning/RawCorrelationConfidenceFailure
   mirror-E: none(waiver:unbounded-symbolic-estimate)
   anchors: []
   utility: none
   digest: Raw correlation strictly misorders the actual teacher with limiting probability one half. -/

import D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
import D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped BigOperators Topology

open _root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities

namespace D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure
open _root_.D5.S3.Arith.FibonacciAtomic
open Law
set_option quotPrecheck false in
local notation "trueClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.1, w.2.2.1, w.2.2.2.1])
set_option quotPrecheck false in
local notation "rivalClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.2.1, w.2.2.1, w.2.2.2.1])


namespace ScoreBridge
open Law

def delta (b : Fin 3) : ℤ := (b.val : ℤ) - 1
def category (w : Record) : Fin 3 := if score w = -1 then 0 else if score w = 0 then 1 else 2

/-- The three-valued score encoding preserves the actual integer score. -/
private theorem category_score (w : Record) : delta (category w) = score w := by
  rcases score_range w with h | h | h <;> simp [category, delta, h]

/-- The score category determines exactly its corresponding integer value. -/
private theorem category_iff (w : Record) (b : Fin 3) : category w = b ↔ score w = delta b := by
  constructor
  · intro h
    rw [← category_score, h]
  · intro h
    have he := category_score w
    unfold delta at *
    apply Fin.ext
    omega

def lazyMass (p : ℝ) (b : Fin 3) : ℝ := if b = 1 then 1 - p else p / 2

/-- The actual conditioned score law is the symmetric three-category law. -/
private theorem clean_pushforward (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) (b : Fin 3) :
    lazyMass (Scale.activeProbability rho a) b =
      ∑ w, if category w = b then cleanRecordMass rho a w else 0 := by
  simp_rw [category_iff]
  change lazyMass (Scale.activeProbability rho a) b = cleanScore rho a (delta b)
  fin_cases b
  · simpa [lazyMass, delta, Scale.activeProbability] using (clean_score_signs rho a).2.symm
  · have ht := clean_score_partition rho a
    rw [clean_record_mass_total rho a hr hr8, (clean_score_signs rho a).1,
      (clean_score_signs rho a).2] at ht
    simp [lazyMass, delta]
    unfold Scale.activeProbability
    linarith
  · simpa [lazyMass, delta, Scale.activeProbability] using (clean_score_signs rho a).1.symm

/-- The complete conditional sample score pushes forward to the symmetric lazy-walk score. -/
private theorem sample_pushforward (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (m : ℕ) (F : ℤ → ℝ) :
    (∑ w : Fin m → Record, F (∑ i, score (w i)) * ∏ i, cleanRecordMass rho a (w i)) =
      ∑ v : Fin m → Fin 3, F (∑ i, delta (v i)) *
        ∏ i, lazyMass (Scale.activeProbability rho a) (v i) := by
  have h := Pushforward.product_pushforward category (cleanRecordMass rho a)
    (lazyMass (Scale.activeProbability rho a)) (clean_pushforward rho a hr hr8)
    m (fun v => F (∑ i, delta (v i)))
  simpa only [category_score] using h

def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p
def pairCategory (x : Bool × Bool) : Fin 3 := if x.1 then if x.2 then 2 else 0 else 1
def pairMass (p : ℝ) (x : Bool × Bool) : ℝ := bernoulliMass p x.1 / 2

/-- An independent activation bit and fair sign have the symmetric three-category law. -/
private theorem pair_pushforward (p : ℝ) (b : Fin 3) :
    lazyMass p b = ∑ x, if pairCategory x = b then pairMass p x else 0 := by
  fin_cases b <;> simp [Fintype.sum_prod_type, pairCategory, pairMass, bernoulliMass, lazyMass] <;> ring

/-- The activation-and-fair-sign representation preserves every total-score observable. -/
private theorem lazy_pair_pushforward (p : ℝ) (m : ℕ) (F : ℤ → ℝ) :
    (∑ x : Fin m → Bool × Bool, F (∑ i, delta (pairCategory (x i))) * ∏ i, pairMass p (x i)) =
      ∑ v : Fin m → Fin 3, F (∑ i, delta (v i)) * ∏ i, lazyMass p (v i) :=
  Pushforward.product_pushforward pairCategory (pairMass p) (lazyMass p)
    (pair_pushforward p) m (fun v => F (∑ i, delta (v i)))

def activity (w : Record) : Bool := decide (score w ≠ 0)

/-- The actual conditioned nonzero indicator has the Bernoulli law. -/
private theorem activity_pushforward (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) (b : Bool) :
    bernoulliMass (Scale.activeProbability rho a) b =
      ∑ w, if activity w = b then cleanRecordMass rho a w else 0 := by
  cases b
  · have hz := clean_score_partition rho a
    rw [clean_record_mass_total rho a hr hr8] at hz
    have ha := clean_active_mass rho a
    have hsplit : (∑ w, if score w = 0 then cleanRecordMass rho a w else 0) +
        (∑ w, if score w ≠ 0 then cleanRecordMass rho a w else 0) = 1 := by
      rw [← clean_record_mass_total rho a hr hr8, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : score w = 0 <;> simp [h]
    simp [bernoulliMass, activity]
    rw [ha] at hsplit
    linarith
  · simpa [bernoulliMass, activity] using (clean_active_mass rho a).symm

/-- The actual conditioned count lower tail equals the corresponding Bernoulli count lower tail. -/
private theorem actual_tail_eq_bernoulli (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) (m N : ℕ) :
    FiniteTail.tail (cleanRecordMass rho a) nonzero m N =
      FiniteTail.tail (bernoulliMass (Scale.activeProbability rho a))
        (fun b => if b then 1 else 0) m N := by
  have h := Pushforward.product_pushforward activity (cleanRecordMass rho a)
    (bernoulliMass (Scale.activeProbability rho a)) (activity_pushforward rho a hr hr8)
    m (fun v => if (∑ i, if v i then (1 : ℕ) else 0) ≤ N then (1 : ℝ) else 0)
  have ht (w : Record) : (if activity w then (1 : ℕ) else 0) = nonzero w := by
    by_cases h : score w = 0 <;> simp [activity,nonzero,h]
  simp only [ht, FiniteTail.tail, FiniteTail.count, ite_mul, one_mul, zero_mul] at h ⊢
  convert h using 1 <;> (
    apply Finset.sum_congr
    · ext w; simp
    · intro w hw
      congr 1)

end ScoreBridge

namespace LazySymmetry
open ScoreBridge

def totalScore {m : ℕ} (v : Fin m → Fin 3) : ℤ := ∑ i, delta (v i)
def sampleMass (p : ℝ) {m : ℕ} (v : Fin m → Fin 3) : ℝ := ∏ i, lazyMass p (v i)
def negative (p : ℝ) (m : ℕ) : ℝ := ∑ v : Fin m → Fin 3, if totalScore v < 0 then sampleMass p v else 0
def positive (p : ℝ) (m : ℕ) : ℝ := ∑ v : Fin m → Fin 3, if 0 < totalScore v then sampleMass p v else 0
def tie (p : ℝ) (m : ℕ) : ℝ := ∑ v : Fin m → Fin 3, if totalScore v = 0 then sampleMass p v else 0

/-- The actual window-label mass has total one. -/
private theorem total_mass (p : ℝ) (m : ℕ) : (∑ v : Fin m → Fin 3, sampleMass p v) = 1 := by
  unfold sampleMass
  have h : (∑ b : Fin 3, lazyMass p b) = 1 := by simp [Fin.sum_univ_three, lazyMass]; ring
  rw [← Fintype.sum_pow, h, one_pow]

/-- Sign reversal equates the strict negative and positive total-score masses. -/
private theorem neg_eq_pos (p : ℝ) (m : ℕ) : negative p m = positive p m := by
  classical
  let er : Fin 3 ≃ Fin 3 := {
    toFun := Fin.rev
    invFun := Fin.rev
    left_inv := fun b => by simp
    right_inv := fun b => by simp }
  let e : (Fin m → Fin 3) ≃ (Fin m → Fin 3) := Equiv.piCongrRight (fun _ => er)
  have hd (b : Fin 3) : delta b.rev = -delta b := by
    fin_cases b <;> norm_num [delta, Fin.rev]
  have hq (b : Fin 3) : lazyMass p b.rev = lazyMass p b := by
    fin_cases b <;> simp [lazyMass, Fin.rev]
  have hs (v : Fin m → Fin 3) : totalScore (e v) = -totalScore v := by
    change (∑ i, delta (v i).rev) = -∑ i, delta (v i)
    simp_rw [hd]
    rw [Finset.sum_neg_distrib]
  have hm (v : Fin m → Fin 3) : sampleMass p (e v) = sampleMass p v := by
    change (∏ i, lazyMass p (v i).rev) = ∏ i, lazyMass p (v i)
    simp_rw [hq]
  unfold negative positive
  rw [← e.sum_comp]
  simp_rw [hs, hm, neg_lt_zero]

/-- Strict negative mass is half of one minus the tie mass. -/
private theorem negative_eq_half (p : ℝ) (m : ℕ) : negative p m = (1 - tie p m) / 2 := by
  have hsplit : negative p m + tie p m + positive p m = 1 := by
    unfold negative tie positive
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← total_mass p m]
    apply Finset.sum_congr rfl
    intro v hv
    rcases lt_trichotomy (totalScore v) 0 with h | h | h
    · have h0 := ne_of_lt h
      have hp := not_lt.mpr h.le
      simp [h,h0,hp]
    · simp [h]
    · have h0 := ne_of_gt h
      have hn := not_lt.mpr h.le
      simp [h,h0,hn]
  rw [← neg_eq_pos] at hsplit
  linarith

end LazySymmetry

namespace LazyLimit
local notation "walkSign" => (fun b : Bool => D5.S3.Arith.GoldenPell.signedInt (!b) 1)
open ScoreBridge Law

local notation "bit" => Bool.toNat

/-- The activation-sign representation has zero increment when inactive and its fair sign when active. -/
private theorem pair_delta (b : Bool × Bool) : delta (pairCategory b) =
    if b.1 then walkSign b.2 else 0 := by
  rcases b with ⟨a,u⟩
  cases a <;> cases u <;> norm_num [delta, pairCategory, D5.S3.Arith.GoldenPell.signedInt]

/-- The lazy-walk tie mass is the mixture of fair-sign tie masses over the activation count. -/
private theorem tie_mixture (p : ℝ) (m : ℕ) :
    LazySymmetry.tie p m = FiniteTail.expectation (bernoulliMass p) bit m
      Binomial.fairTie := by
  classical
  have hc := lazy_pair_pushforward p m (fun s => if s = 0 then (1 : ℝ) else 0)
  have hp : LazySymmetry.tie p m =
      ∑ x : Fin m → Bool × Bool,
        if (∑ i, delta (pairCategory (x i))) = 0 then ∏ i, pairMass p (x i) else 0 := by
    simp only [LazySymmetry.tie, LazySymmetry.totalScore,
      LazySymmetry.sampleMass, ite_mul, one_mul, zero_mul] at hc ⊢
    convert hc.symm using 1 <;> (
      apply Finset.sum_congr
      · ext v; simp
      · intro v hv; rfl)
  rw [hp]
  let e := Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Bool) (fun _ => Bool)
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have mass (a u : Fin m → Bool) :
      (∏ i, pairMass p (e.symm (a,u) i)) =
        (∏ i, bernoulliMass p (a i)) * (1 / 2 : ℝ) ^ m := by
    change (∏ i, bernoulliMass p (a i) / 2) = _
    rw [Finset.prod_div_distrib]
    simp [div_pow, div_eq_mul_inv]
  have vals (a u : Fin m → Bool) :
      (∑ i, delta (pairCategory (e.symm (a,u) i))) =
        ∑ i, if a i then walkSign (u i) else 0 := by
    change (∑ i, delta (pairCategory (a i,u i))) = _
    simp_rw [pair_delta]
  simp_rw [vals, mass]
  unfold FiniteTail.expectation
  apply Finset.sum_congr rfl
  intro a ha
  have hterm (u : Fin m → Bool) :
      (if (∑ i, if a i then walkSign (u i) else 0) = 0 then
        (∏ i, bernoulliMass p (a i)) * (1 / 2 : ℝ) ^ m else 0) =
      (∏ i, bernoulliMass p (a i)) *
        (if (∑ i, if a i then walkSign (u i) else 0) = 0 then (1 / 2 : ℝ) ^ m else 0) := by
    split_ifs <;> simp
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hf := ActiveFair.active_fair_tie a
  have hj : Fintype.card {i : Fin m // a i = true} = FiniteTail.count bit a := by
    rw [Fintype.card_subtype]
    simpa only [FiniteTail.count, Bool.toNat, Bool.cond_eq_ite] using
      (Finset.card_filter (fun i : Fin m => a i = true) Finset.univ)
  have hf' := congrArg ((∏ i, bernoulliMass p (a i)) * ·) hf
  simp only [Fintype.card_fin, hj] at hf'
  convert hf' using 1
  congr 1
  apply Finset.sum_congr
  · ext u; simp
  · intro u hu; rfl

/-- The actual conditional activation probability lies in the unit interval. -/
private theorem active_probability_mem (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    0 ≤ Scale.activeProbability rho a ∧ Scale.activeProbability rho a ≤ 1 := by
  rw [← clean_active_mass]
  constructor
  · apply Finset.sum_nonneg
    intro w hw
    split_ifs
    · exact clean_record_mass_nonneg rho a hr hr8 ha ha1 w
    · exact le_rfl
  · rw [← clean_record_mass_total rho a hr hr8]
    apply Finset.sum_le_sum
    intro w hw
    split_ifs
    · exact le_rfl
    · exact clean_record_mass_nonneg rho a hr hr8 ha ha1 w

/-- Each fair-sign tie coefficient is at most one. -/
private theorem fair_tie_le_one (j : ℕ) : Binomial.fairTie j ≤ 1 := by
  have h := Binomial.fair_tie_square_bound j
  have hb : 1 / ((j : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  nlinarith [Binomial.fair_tie_nonneg j]

/-- The target-scale conditional total-score tie probability tends to zero. -/
private theorem tie_vanishes (a K : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K) :
    Tendsto (fun rho => LazySymmetry.tie (Scale.activeProbability rho a)
      (Scale.sampleLength rho a K)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have small : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ), 0 < rho ∧ rho ≤ 1 / 8 := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ)<1 / 8))] with rho hr hr8
    exact ⟨hr, hr8.le⟩
  have hq : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ), ∀ b,
      0 ≤ bernoulliMass (Scale.activeProbability rho a) b := by
    filter_upwards [small] with rho hr b
    have hp := active_probability_mem rho a hr.1 hr.2 ha ha1
    cases b <;> simp [bernoulliMass] <;> linarith
  have ht (N : ℕ) : Tendsto (fun rho => FiniteTail.tail
      (bernoulliMass (Scale.activeProbability rho a)) bit
      (Scale.sampleLength rho a K) N) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply (nonzero_count_diverges a K ha ha1 hK N).congr'
    filter_upwards [small] with rho hr
    have hbit : (fun b : Bool => if b then (1 : ℕ) else 0) = bit := by
      funext b
      cases b <;> rfl
    simpa only [hbit] using
      actual_tail_eq_bernoulli rho a hr.1 hr.2 (Scale.sampleLength rho a K) N
  have hv := FiniteTail.expectation_vanishes (𝓝[>] (0 : ℝ))
    (fun rho => bernoulliMass (Scale.activeProbability rho a)) bit
    (fun rho => Scale.sampleLength rho a K) Binomial.fairTie hq
    (Filter.Eventually.of_forall (fun rho => by simp [bernoulliMass]))
    Binomial.fair_tie_nonneg fair_tie_le_one Binomial.fair_tie_vanishes ht
  simpa only [tie_mixture] using hv

end LazyLimit

local notation "eventMass" p:max E:max =>
  @_root_.D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement.eventMass
    _ (fun x y => Classical.propDecidable (x = y))
    p (@Finset.filter _ E (fun x => Classical.propDecidable (E x)) Finset.univ)
      Finset.univ

namespace Conditioning


/-- Nonnegative masses give nonnegative event masses. -/
private theorem event_mass_nonneg {α : Type*} [Fintype α] (p : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (E : α → Prop) : 0 ≤ eventMass p E := by
  simp only [_root_.D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement.eventMass, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact hp x
  · exact le_rfl

/-- Event inclusion preserves the ordering of finite nonnegative masses. -/
private theorem event_mass_mono {α : Type*} [Fintype α] (p : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (E A : α → Prop) (h : ∀ x, E x → A x) : eventMass p E ≤ eventMass p A := by
  simp only [_root_.D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement.eventMass, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : E x
  · have ha : A x := h x he
    simp [he,ha]
  · by_cases ha : A x <;> simp [he,ha,hp x]

/-- An event and its complement partition the total finite mass. -/
private theorem event_mass_compl {α : Type*} [Fintype α] (p : α → ℝ) (E : α → Prop) :
    eventMass p E + eventMass p (fun x => ¬ E x) = ∑ x, p x := by
  simp only [_root_.D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement.eventMass, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : E x <;> simp [h]

/-- Conditioning on a positive-probability event changes any event mass by at most its omitted mass. -/
private theorem conditioning_bound {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hprob : ∑ x, p x = 1) (E A : α → Prop)
    (hE : 0 < eventMass p E) :
    |eventMass p A - eventMass p (fun x => E x ∧ A x) / eventMass p E| ≤ 1 - eventMass p E := by
  let c := eventMass p E
  let x := eventMass p (fun x => E x ∧ A x)
  let y := eventMass p (fun x => ¬ E x ∧ A x)
  have hc : 0 < c := hE
  have hc1 : c ≤ 1 := by
    have h := event_mass_compl p E
    rw [hprob] at h
    have hn := event_mass_nonneg p hp (fun x => ¬ E x)
    change eventMass p E ≤ 1
    linarith only [h, hn]
  have hx0 : 0 ≤ x := event_mass_nonneg p hp _
  have hy0 : 0 ≤ y := event_mass_nonneg p hp _
  have hx : x ≤ c := event_mass_mono p hp _ E (fun z hz => hz.1)
  have hy : y ≤ 1 - c := by
    have h := event_mass_mono p hp (fun z => ¬ E z ∧ A z) (fun z => ¬ E z) (fun z hz => hz.1)
    have hh := event_mass_compl p E
    rw [hprob] at hh
    dsimp only [y,c]
    linarith only [h, hh]
  have hxy : eventMass p A = x + y := by
    dsimp [x,y]
    simp only [_root_.D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement.eventMass, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases he : E z <;> by_cases ha : A z <;> simp [he,ha]
  have hd0 : 0 ≤ x / c := div_nonneg hx0 hc.le
  have hd1 : x / c ≤ 1 := (div_le_one hc).mpr hx
  have hmul0 := mul_nonneg (sub_nonneg.mpr hc1) hd0
  have hmul1 := mul_le_mul_of_nonneg_left hd1 (sub_nonneg.mpr hc1)
  have heq : x + y - x / c = y - (1 - c) * (x / c) := by field_simp <;> ring
  change |eventMass p A - x / c| ≤ 1 - c
  rw [hxy,heq]
  exact abs_le.2 ⟨by nlinarith,by nlinarith⟩

end Conditioning

namespace RawLimit
open Law

def cleanNegative (rho a : ℝ) (m : ℕ) : ℝ :=
  ∑ w : Fin m → Record, if (∑ i, score (w i)) < 0 then
    ∏ i, cleanRecordMass rho a (w i) else 0

/-- The actual conditional strict misordering mass is the symmetric lazy-walk negative mass. -/
private theorem clean_negative_eq (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) (m : ℕ) :
    cleanNegative rho a m = LazySymmetry.negative (Scale.activeProbability rho a) m := by
  have h := ScoreBridge.sample_pushforward rho a hr hr8 m
    (fun s => if s < 0 then (1 : ℝ) else 0)
  simp only [cleanNegative, LazySymmetry.negative, LazySymmetry.totalScore,
    LazySymmetry.sampleMass, ite_mul, one_mul, zero_mul] at h ⊢
  convert h using 1 <;> (
    apply Finset.sum_congr
    · ext w; simp
    · intro w hw; rfl)

/-- Actual conditioned strict misordering tends to one half. -/
private theorem clean_negative_limit (a K : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K) :
    Tendsto (fun rho => cleanNegative rho a (Scale.sampleLength rho a K))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have ht := LazyLimit.tie_vanishes a K ha ha1 hK
  have hc : Tendsto (fun rho => (1 - LazySymmetry.tie (Scale.activeProbability rho a)
      (Scale.sampleLength rho a K)) / 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub ht).div_const (2 : ℝ)
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ)<1 / 8))] with rho hr hr8
  rw [clean_negative_eq rho a hr hr8.le, LazySymmetry.negative_eq_half]

/-- The original and conditioned strict misordering masses differ by at most the reverse-event exclusion loss. -/
private theorem raw_clean_bound (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (m : ℕ) :
    |misorder rho a m - cleanNegative rho a m| ≤ 1 - (1 - 12 * rho ^ 3) ^ m := by
  let p : (Fin m → Record) → ℝ := fun w => ∏ i, recordMass rho a (w i)
  let E : (Fin m → Record) → Prop := fun w => ∀ i, ¬ reverse (w i)
  let A : (Fin m → Record) → Prop := fun w => (∑ i, score (w i)) < 0
  have hp : ∀ w, 0 ≤ p w := fun w =>
    Finset.prod_nonneg (fun i hi => record_mass_nonneg rho a hr hr8 ha ha1 _)
  have hprob : ∑ w, p w = 1 := by
    dsimp [p]
    rw [← Fintype.sum_pow, total_mass, one_pow]
  have hE : eventMass p E = (1 - 12 * rho ^ 3) ^ m := by
    simp only [_root_.D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement.eventMass, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [p,E]
    exact all_clean_mass rho a m
  have hc : 0 < eventMass p E := by
    rw [hE]
    exact pow_pos (clean_denominator_pos rho hr hr8) m
  have h := Conditioning.conditioning_bound p hp hprob E A hc
  have hcond : cleanNegative rho a m =
      eventMass p (fun w => E w ∧ A w) / eventMass p E := by
    rw [hE]
    unfold cleanNegative
    simp_rw [← clean_sample_factor]
    unfold cleanSampleMass
    simp only [_root_.D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement.eventMass, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases he : ∀ i, ¬ reverse (w i)
    <;> by_cases hn : (∑ i, score (w i)) < 0
    <;> simp [E,A,p,he,hn]
  have hA : eventMass p A = misorder rho a m := by
    unfold misorder
    simp only [_root_.D5.S3.ConceptDynamics.ObservationOrder.CommonPriorPosteriorAgreement.eventMass, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [← hcond, hE, hA] at h
  exact h

/-- The actual raw-score strict misordering probability tends to one half at the target sample scale. -/
theorem raw_confidence_failure (a K : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K) :
    Tendsto (fun rho => misorder rho a (Scale.sampleLength rho a K))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have hn := clean_negative_limit a K ha ha1 hK
  have hc := Law.all_clean_limit a K ha hK
  simp only [Law.all_clean_mass] at hc
  have hb : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ),
      |misorder rho a (Scale.sampleLength rho a K)-
        cleanNegative rho a (Scale.sampleLength rho a K)| ≤
      1 - (1 - 12 * rho ^ 3) ^ (Scale.sampleLength rho a K) := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ)<1 / 8))] with rho hr hr8
    exact raw_clean_bound rho a hr hr8.le ha ha1 _
  have hbad : Tendsto (fun rho => 1 - (1 - 12 * rho ^ 3) ^ (Scale.sampleLength rho a K))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hn.sub hbad)
    (by simpa using hn.add hbad)
  · filter_upwards [hb] with rho h
    have hlow := (abs_le.mp h).1
    linarith
  · filter_upwards [hb] with rho h
    have hhigh := (abs_le.mp h).2
    linarith

end RawLimit

namespace Selection
open Law D5.S3.Arith.FibonacciAtomic

def candidateClass (c : Fin 4) (w : Record) : Fin 3 :=
  if c = 0 then GarbledPosteriorRootGap.teacher (m := 0) ![w.1,w.2.1,w.2.2.1]
  else if c = 1 then GarbledPosteriorRootGap.teacher (m := 0) ![w.1,w.2.1,w.2.2.2.1]
  else if c = 2 then trueClass w else rivalClass w

def candidateScore {m : ℕ} (c : Fin 4) (w : Fin m → Record) : ℤ :=
  ∑ i, (((w i).2.2.2.2.val : ℤ) - 1) * ((candidateClass c (w i)).val : ℤ)

/-- The difference of the two raw candidate totals is the sum of their actual record score differences. -/
private theorem score_gap (m : ℕ) (w : Fin m → Record) :
    candidateScore 2 w - candidateScore 3 w = ∑ i, score (w i) := by
  unfold candidateScore score
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [candidateClass]
  ring

def failureMass (rho a : ℝ) (m : ℕ) (select : (Fin m → Record) → Fin 4) : ℝ :=
  ∑ w : Fin m → Record, if select w ≠ 2 then ∏ i, recordMass rho a (w i) else 0

/-- Strict misordering is contained in the failure event of every deterministic raw-score maximizer. -/
private theorem argmax_failure_bound (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (m : ℕ) (select : (Fin m → Record) → Fin 4)
    (hmax : ∀ w c, candidateScore c w ≤ candidateScore (select w) w) :
    misorder rho a m ≤ failureMass rho a m select := by
  unfold misorder failureMass
  apply Finset.sum_le_sum
  intro w hw
  by_cases hn : (∑ i, score (w i)) < 0
  · have hs : select w ≠ 2 := by
      intro heq
      have hh := hmax w 3
      rw [heq] at hh
      have hg := score_gap m w
      omega
    simp [hn,hs]
  · simp only [if_neg hn]
    split_ifs
    · exact Finset.prod_nonneg (fun i hi => record_mass_nonneg rho a hr hr8 ha ha1 _)
    · exact le_rfl

/-- Every deterministic selection failure mass lies in the unit interval. -/
private theorem failure_mass_bounds (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (m : ℕ) (select : (Fin m → Record) → Fin 4) :
    0 ≤ failureMass rho a m select ∧ failureMass rho a m select ≤ 1 := by
  have hp : ∀ w : Fin m → Record, 0 ≤ ∏ i, recordMass rho a (w i) := fun w =>
    Finset.prod_nonneg (fun i hi => record_mass_nonneg rho a hr hr8 ha ha1 _)
  have hprob : (∑ w : Fin m → Record, ∏ i, recordMass rho a (w i)) = 1 := by
    rw [← Fintype.sum_pow, Law.total_mass, one_pow]
  constructor
  · unfold failureMass
    apply Finset.sum_nonneg
    intro w hw
    split_ifs
    · exact hp w
    · exact le_rfl
  · rw [← hprob]
    apply Finset.sum_le_sum
    intro w hw
    split_ifs
    · exact le_rfl
    · exact hp w

/-- Every full-candidate raw-score maximizer has failure probability lower limit at least one half. -/
theorem deterministic_failure_liminf (a K : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K)
    (select : (rho : ℝ) → (Fin (Scale.sampleLength rho a K) → Record) → Fin 4)
    (hmax : ∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w c, candidateScore c w ≤ candidateScore (select rho w) w) :
    (1 / 2 : ℝ) ≤ liminf (fun rho => failureMass rho a (Scale.sampleLength rho a K) (select rho))
      (𝓝[>] (0 : ℝ)) := by
  have small : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ), 0 < rho ∧ rho ≤ 1 / 8 := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ)<1 / 8))] with rho hr hr8
    exact ⟨hr, hr8.le⟩
  have hupper : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ),
      failureMass rho a (Scale.sampleLength rho a K) (select rho) ≤ 1 := by
    filter_upwards [small] with rho hr
    exact (failure_mass_bounds rho a hr.1 hr.2 ha ha1 _ _).2
  have hlower : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ failureMass rho a (Scale.sampleLength rho a K) (select rho) := by
    filter_upwards [small] with rho hr
    exact (failure_mass_bounds rho a hr.1 hr.2 ha ha1 _ _).1
  apply (le_liminf_iff (isCoboundedUnder_ge_of_eventually_le (𝓝[>] (0 : ℝ)) hupper) ⟨0,hlower⟩).mpr
  intro z hz
  filter_upwards [small, (RawLimit.raw_confidence_failure a K ha ha1 hK).eventually
    (lt_mem_nhds hz)] with rho hr hprob
  exact hprob.trans_le (argmax_failure_bound rho a hr.1 hr.2 ha ha1 _ (select rho) (hmax rho hr.1 hr.2))

end Selection

namespace RandomSelection
open Law Selection

def failureMass (rho a : ℝ) (m : ℕ) (q : (Fin m → Record) → Fin 4 → ℝ) : ℝ :=
  ∑ w : Fin m → Record, (∏ i, recordMass rho a (w i)) * (1 - q w 2)

/-- Strict misordering forces every randomized maximizing kernel to assign zero mass to the true teacher. -/
private theorem failure_bound (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (m : ℕ) (q : (Fin m → Record) → Fin 4 → ℝ)
    (hq : ∀ w c, 0 ≤ q w c) (hnorm : ∀ w, ∑ c, q w c = 1)
    (hsupport : ∀ w c, 0 < q w c → ∀ d, candidateScore d w ≤ candidateScore c w) :
    misorder rho a m ≤ failureMass rho a m q := by
  unfold misorder failureMass
  apply Finset.sum_le_sum
  intro w hw
  have hp : 0 ≤ ∏ i, recordMass rho a (w i) :=
    Finset.prod_nonneg (fun i hi => record_mass_nonneg rho a hr hr8 ha ha1 _)
  have hq1 : q w 2 ≤ 1 := by
    rw [← hnorm w]
    exact Finset.single_le_sum (fun c hc => hq w c) (Finset.mem_univ 2)
  by_cases hn : (∑ i, score (w i)) < 0
  · have hz : q w 2 = 0 := by
      apply le_antisymm _ (hq w 2)
      by_contra h
      have hh := hsupport w 2 (lt_of_not_ge h) 3
      have hg := score_gap m w
      omega
    simp [hn,hz]
  · simp only [if_neg hn]
    exact mul_nonneg hp (sub_nonneg.mpr hq1)

/-- Every full-candidate raw-score maximizer has failure probability lower limit at least one half. -/
theorem randomized_failure_liminf (a K : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K)
    (q : (rho : ℝ) → (Fin (Scale.sampleLength rho a K) → Record) → Fin 4 → ℝ)
    (hq : ∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w c, 0 ≤ q rho w c)
    (hnorm : ∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w, ∑ c, q rho w c = 1)
    (hsupport : ∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w c, 0 < q rho w c →
      ∀ d, candidateScore d w ≤ candidateScore c w) :
    (1 / 2 : ℝ) ≤ liminf (fun rho => failureMass rho a (Scale.sampleLength rho a K) (q rho))
      (𝓝[>] (0 : ℝ)) := by
  have small : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ), 0 < rho ∧ rho ≤ 1 / 8 := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ)<1 / 8))] with rho hr hr8
    exact ⟨hr, hr8.le⟩
  have hprob (rho : ℝ) : (∑ w : Fin (Scale.sampleLength rho a K) → Record,
      ∏ i, recordMass rho a (w i)) = 1 := by
    rw [← Fintype.sum_pow, Law.total_mass, one_pow]
  have bounds : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ failureMass rho a (Scale.sampleLength rho a K) (q rho) ∧
      failureMass rho a (Scale.sampleLength rho a K) (q rho) ≤ 1 := by
    filter_upwards [small] with rho hr
    have hq1 (w) : q rho w 2 ≤ 1 := by
      rw [← hnorm rho hr.1 hr.2 w]
      exact Finset.single_le_sum (fun c hc => hq rho hr.1 hr.2 w c) (Finset.mem_univ 2)
    have hp (w : Fin (Scale.sampleLength rho a K) → Record) :
        0 ≤ ∏ i, recordMass rho a (w i) :=
      Finset.prod_nonneg (fun i hi => record_mass_nonneg rho a hr.1 hr.2 ha ha1 _)
    constructor
    · exact Finset.sum_nonneg (fun w hw => mul_nonneg (hp w) (sub_nonneg.mpr (hq1 w)))
    · rw [← hprob rho]
      apply Finset.sum_le_sum
      intro w hw
      have h := hq rho hr.1 hr.2 w 2
      nlinarith [hp w]
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_eventually_le (𝓝[>] (0 : ℝ)) (bounds.mono fun rho hr => hr.2))
    ⟨0,bounds.mono fun rho hr => hr.1⟩).mpr
  intro z hz
  filter_upwards [small, (RawLimit.raw_confidence_failure a K ha ha1 hK).eventually
    (lt_mem_nhds hz)] with rho hr hprob
  exact hprob.trans_le (failure_bound rho a hr.1 hr.2 ha ha1 _ (q rho)
    (hq rho hr.1 hr.2) (hnorm rho hr.1 hr.2) (hsupport rho hr.1 hr.2))

end RandomSelection

end D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure

namespace D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
open Law
set_option quotPrecheck false in
local notation "trueClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.1, w.2.2.1, w.2.2.2.1])
set_option quotPrecheck false in
local notation "rivalClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.2.1, w.2.2.1, w.2.2.2.1])

/-- The legal actual-record family has the exact moments and half-probability
misordering limit; every maximum-score rule has failure lower limit at least one half. -/
theorem result (a K : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K) :
    (∀ rho : ℝ, 0 < rho → rho ≤ 1 / 8 →
      HeterogeneousTeacherSeparation.Admissible rho (positionLaw rho) ∧
      (∀ w : Record, difference w =
        (HeterogeneousTeacherSeparation.highIndicator w.1 -
          HeterogeneousTeacherSeparation.highIndicator w.2.1) *
        HeterogeneousTeacherSeparation.lowIndicator w.2.2.1 *
        (1 - 2 * HeterogeneousTeacherSeparation.highIndicator w.2.2.1 *
          HeterogeneousTeacherSeparation.lowIndicator w.2.2.2.1)) ∧
      (expectation rho a (fun w => difference w ^ 2) = 2 * rho * (1 - 5 * rho + 12 * rho ^ 2) ∧
        expectation rho a (fun w => (((trueClass w).val : ℝ) - 1) ^ 2 -
          (((rivalClass w).val : ℝ) - 1) ^ 2) = -2 * rho + 10 * rho ^ 2 ∧
        expectation rho a (fun w => (score w : ℝ)) = 3 * a * rho ^ 3 ∧
        variance rho a = (8 + a) / 12 * (2 * rho * (1 - 5 * rho + 12 * rho ^ 2)) -
          9 * a ^ 2 * rho ^ 6 ∧
        0 < expectation rho a (fun w => (score w : ℝ)))) ∧
    Tendsto (fun rho => misorder rho a (Scale.sampleLength rho a K))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) ∧
    (∀ select : (rho : ℝ) → (Fin (Scale.sampleLength rho a K) → Record) → Fin 4,
      (∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w c,
        Selection.candidateScore c w ≤ Selection.candidateScore (select rho w) w) →
      (1 / 2 : ℝ) ≤ liminf
        (fun rho => Selection.failureMass rho a (Scale.sampleLength rho a K) (select rho))
        (𝓝[>] (0 : ℝ))) ∧
    (∀ q : (rho : ℝ) → (Fin (Scale.sampleLength rho a K) → Record) → Fin 4 → ℝ,
      (∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w c, 0 ≤ q rho w c) →
      (∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w, ∑ c, q rho w c = 1) →
      (∀ rho, 0 < rho → rho ≤ 1 / 8 → ∀ w c, 0 < q rho w c →
        ∀ d, Selection.candidateScore d w ≤ Selection.candidateScore c w) →
      (1 / 2 : ℝ) ≤ liminf
        (fun rho => RandomSelection.failureMass rho a (Scale.sampleLength rho a K) (q rho))
        (𝓝[>] (0 : ℝ))) := by
  refine ⟨?_, RawLimit.raw_confidence_failure a K ha ha1 hK, ?_, ?_⟩
  · intro rho hr hr8
    exact ⟨position_law_admissible rho hr hr8, difference_formula, actual_moments rho a hr ha⟩
  · intro select hmax
    exact Selection.deterministic_failure_liminf a K ha ha1 hK select hmax
  · intro q hq hnorm hsupport
    exact RandomSelection.randomized_failure_liminf a K ha ha1 hK q hq hnorm hsupport

end D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure
