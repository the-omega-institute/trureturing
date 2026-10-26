/- GID: D5/S3/Quantum/Analysis/TraceClass/SpectralMomentEnvelope
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/SpectralMomentEnvelope
   mirror-E: none(waiver:countable-positive-operator-spectrum)
   anchors: []
   utility: none
   digest: Actual trace-class spectral moments and their countable probability envelope. -/

import D5.S3.Entropy.SpectralEnvelope
import D5.S3.Quantum.Analysis.TraceClass.Spectral
import D5.S3.Quantum.Analysis.TraceClass.GeneralIdeal

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder

namespace TraceClassSpectralEnvelope
open D5.S3.Entropy.CountableSpectralMoments
open D5.S3.Entropy.SpectralEnvelopeParameters
open D5.S3.Entropy.SpectralEnvelope

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A full eigenbasis of the actual operator, together with an embedding of its
nonzero spectrum into Nat. The full basis, including its kernel, is retained. -/
structure CountableSpectralData (T : H →L[ℂ] H) where
  index : Set H
  basis : HilbertBasis index ℂ H
  value : index → ℝ
  nonneg : ∀ i, 0 ≤ value i
  eigen : ∀ i, T (basis i) = (value i : ℂ) • basis i
  embed : Function.support value ↪ ℕ

private def spectralData {T : H →L[ℂ] H} (hT : 0 ≤ T) (hTC : IsTraceClass T) :
    CountableSpectralData T := by
  classical
  obtain ⟨w, b, s, hn, he, hs, _⟩ :=
    TraceClassSpectral.exists_nonneg_trace_spectral_data hT hTC
  letI : Countable (Function.support s) := hs.countable_support.to_subtype
  letI : Encodable (Function.support s) := Countable.toEncodable _
  exact ⟨w, b, s, hn, he, ⟨Encodable.encode, Encodable.encode_injective⟩⟩

def spectrum {T : H →L[ℂ] H} (d : CountableSpectralData T) : ℕ → ℝ :=
  Function.extend d.embed (fun i => d.value i) 0

private theorem spectrum_nonneg {T : H →L[ℂ] H} (d : CountableSpectralData T) :
    ∀ n, 0 ≤ spectrum d n := by
  classical
  intro n
  by_cases h : ∃ i, d.embed i = n
  · obtain ⟨i, rfl⟩ := h
    rw [spectrum, d.embed.injective.extend_apply]
    exact d.nonneg i
  · rw [spectrum, Function.extend_apply' _ _ _ h]
    exact le_rfl

private theorem traceClass_power {T : H →L[ℂ] H} (hTC : IsTraceClass T) (n : ℕ) :
    IsTraceClass (T ^ (n + 1)) := by
  simpa only [mul_one, ← pow_succ] using
    isTraceClass_mul_mul (A := T ^ n) (B := 1) hTC

def powerTrace (T : H →L[ℂ] H) (hTC : IsTraceClass T) (n : ℕ) : ℝ :=
  (trace (T ^ (n + 1)) (traceClass_power hTC n)).re

/-- The Newton functional on actual operator traces. The spectral theorem below
identifies it with the absolutely convergent increasing-triple sum. -/
def operatorThird (T : H →L[ℂ] H) (hTC : IsTraceClass T) : ℝ :=
  (powerTrace T hTC 0 ^ 3 - 3 * powerTrace T hTC 0 * powerTrace T hTC 1 +
    2 * powerTrace T hTC 2) / 6

private theorem eigen_power {T : H →L[ℂ] H} (d : CountableSpectralData T)
    (n : ℕ) (i : d.index) :
    (T ^ (n + 1)) (d.basis i) = ((d.value i ^ (n + 1) : ℝ) : ℂ) • d.basis i := by
  induction n with
  | zero => simpa using d.eigen i
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, d.eigen, map_smul, ih, smul_smul]
    push_cast
    congr 1
    ring

private theorem value_power_hasSum {T : H →L[ℂ] H} (d : CountableSpectralData T)
    (hTC : IsTraceClass T) (n : ℕ) :
    HasSum (fun i => d.value i ^ (n + 1)) (powerTrace T hTC n) := by
  have hd (i : d.index) :
      inner ℂ (d.basis i) ((T ^ (n + 1)) (d.basis i)) =
      (d.value i ^ (n + 1) : ℂ) := by
    rw [eigen_power d n i, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [d.basis.orthonormal.1 i]
  have hs := (summable_trace_diagonal_of_isTraceClass (traceClass_power hTC n) d.basis).hasSum
  rw [← trace_eq_of_hilbertBasis (traceClass_power hTC n) d.basis] at hs
  have hr := Complex.hasSum_re hs
  simpa only [hd, powerTrace, ← Complex.ofReal_pow, Complex.ofReal_re] using hr

private theorem spectrum_power_hasSum {T : H →L[ℂ] H} (d : CountableSpectralData T)
    (hTC : IsTraceClass T) (n : ℕ) :
    HasSum (fun k => spectrum d k ^ (n + 1)) (powerTrace T hTC n) := by
  classical
  have hsupport : Function.support (fun i => d.value i ^ (n + 1)) ⊆ Function.support d.value := by
    intro i hi
    change d.value i ≠ 0
    intro hz
    simpa [Function.mem_support, hz] using hi
  have hs : HasSum (fun i : Function.support d.value => d.value i ^ (n + 1))
      (powerTrace T hTC n) :=
    (hasSum_subtype_iff_of_support_subset hsupport).mpr (value_power_hasSum d hTC n)
  have hext : (fun k => spectrum d k ^ (n + 1)) =
      Function.extend d.embed (fun i : Function.support d.value => d.value i ^ (n + 1)) 0 := by
    funext k
    simpa only [spectrum, Function.comp_apply, zero_pow (by omega : n + 1 ≠ 0)] using
      Function.apply_extend (fun z : ℝ => z ^ (n + 1)) d.embed 0 k
  rw [hext]
  exact (hasSum_extend_zero d.embed.injective).mpr hs

/-- Every actual positive trace-class density has a countable nonnegative
probability spectrum with the exact second and third operator traces. No
faithfulness, finite rank, or separability premise is added. -/
theorem spectral_moments {T : H →L[ℂ] H} (hT : 0 ≤ T) (hTC : IsTraceClass T)
    (htrace : trace T hTC = 1) :
    ∃ d : CountableSpectralData T,
      Summable (spectrum d) ∧ (∀ n, 0 ≤ spectrum d n) ∧ mass (spectrum d) = 1 ∧
      purity (spectrum d) = powerTrace T hTC 1 ∧
      cubicMoment (spectrum d) = powerTrace T hTC 2 ∧
      third (spectrum d) = operatorThird T hTC ∧
      Summable (fun t => ‖tripleTerm (spectrum d) t‖) ∧
      (∀ i, operatorThird T hTC - 1 / 32 =
        (2 * spectrum d i - 1) * (4 * spectrum d i - 1) ^ 2 / 32 +
        (spectrum d i / 2) * (3 / 8 - powerTrace T hTC 1) +
        third (erase (spectrum d) i)) := by
  let d := spectralData hT hTC
  have hs0 := spectrum_power_hasSum d hTC 0
  have hs1 := spectrum_power_hasSum d hTC 1
  have hs2 := spectrum_power_hasSum d hTC 2
  have ht : powerTrace T hTC 0 = 1 := by simp [powerTrace, htrace]
  have hmass : mass (spectrum d) = 1 := by
    simpa only [mass, pow_one, ht] using hs0.tsum_eq
  have hsum : Summable (spectrum d) := by simpa only [pow_one] using hs0.summable
  have hq : purity (spectrum d) = powerTrace T hTC 1 := by
    simpa only [purity, Nat.reduceAdd] using hs1.tsum_eq
  have hr : cubicMoment (spectrum d) = powerTrace T hTC 2 := by
    simpa only [cubicMoment, Nat.reduceAdd] using hs2.tsum_eq
  have he : third (spectrum d) = operatorThird T hTC := by
    have hn := countable_newton hsum (spectrum_nonneg d) hmass.le
    rw [hmass, hq, hr] at hn
    unfold operatorThird
    rw [ht]
    linarith
  refine ⟨d, hsum, spectrum_nonneg d, hmass, hq, hr, he,
    (absolute_triple_sum hsum (spectrum_nonneg d)).1, ?_⟩
  intro i
  simpa only [he, hq] using distinguished_identity hsum (spectrum_nonneg d) hmass i

/-- The trace/purity envelope on actual positive trace-class densities. -/
theorem trace_class_envelope {T : H →L[ℂ] H} (hT : 0 ≤ T) (hTC : IsTraceClass T)
    (htrace : trace T hTC = 1) :
    (powerTrace T hTC 1 ≤ 1 / 3 →
      (1 - 3 * powerTrace T hTC 1 + 2 * powerTrace T hTC 1 ^ 2) / 6 ≤ operatorThird T hTC ∧
      1 / 27 ≤ (1 - 3 * powerTrace T hTC 1 + 2 * powerTrace T hTC 1 ^ 2) / 6) ∧
    (1 / 3 ≤ powerTrace T hTC 1 → powerTrace T hTC 1 ≤ 3 / 8 →
      envelope (powerTrace T hTC 1) ≤ operatorThird T hTC) ∧
    (powerTrace T hTC 1 ≤ 3 / 8 → 25 / 864 ≤ operatorThird T hTC) ∧
    (powerTrace T hTC 1 ≤ threshold → 1 / 32 ≤ operatorThird T hTC) := by
  obtain ⟨d, hs, hn, hm, hq, _, he, _, _⟩ := spectral_moments hT hTC htrace
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hl
    simpa only [hq, he] using third_lower_of_purity_le_third hs hn hm (hq.trans_le hl)
  · intro hl hu
    simpa only [hq, he] using countable_budget_envelope hs hn hm
      (by simpa only [hq] using hl) (hq.trans_le hu)
  · intro hu
    simpa only [he] using third_lower_of_purity_le_three_eighths hs hn hm (hq.trans_le hu)
  · intro hu
    simpa only [he] using third_lower_of_purity_le_threshold hs hn hm (hq.trans_le hu)

#print axioms spectral_moments
#print axioms trace_class_envelope

/-- Normalize the actual eigenvalue sequence at a positive trace, retaining
its exact moments and increasing-triple value. The normalized sequence is not
an assertion that an arbitrary abstract optimizer is physically realizable. -/
theorem spectral_moments_at_mass {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (hTC : IsTraceClass T) {t : ℝ} (ht : 0 < t)
    (htrace : trace T hTC = (t : ℂ)) :
    ∃ d : CountableSpectralData T,
      let p := fun n => spectrum d n / t
      Summable p ∧ (∀ n, 0 ≤ p n) ∧ mass p = 1 ∧
      purity p = powerTrace T hTC 1 / t ^ 2 ∧
      cubicMoment p = powerTrace T hTC 2 / t ^ 3 ∧
      t ^ 3 * third p = operatorThird T hTC ∧
      Summable (fun s => ‖tripleTerm (spectrum d) s‖) ∧
      third (spectrum d) = operatorThird T hTC := by
  let d := spectralData hT hTC
  let p := fun n => spectrum d n / t
  have hs0 := spectrum_power_hasSum d hTC 0
  have hs1 := spectrum_power_hasSum d hTC 1
  have hs2 := spectrum_power_hasSum d hTC 2
  have hmass : powerTrace T hTC 0 = t := by simp [powerTrace, htrace]
  have hsum : Summable (spectrum d) := by simpa only [pow_one] using hs0.summable
  have hp : Summable p := hsum.div_const t
  have hn : ∀ n, 0 ≤ p n := fun n => div_nonneg (spectrum_nonneg d n) ht.le
  have hm : mass p = 1 := by
    unfold mass p
    rw [tsum_div_const]
    have hs : (∑' n, spectrum d n) = t := by
      simpa only [pow_one, hmass] using hs0.tsum_eq
    rw [hs, div_self ht.ne']
  have hq : purity p = powerTrace T hTC 1 / t ^ 2 := by
    unfold purity p
    simp only [div_pow]
    rw [tsum_div_const]
    exact congrArg (fun z : ℝ => z / t ^ 2) hs1.tsum_eq
  have hr : cubicMoment p = powerTrace T hTC 2 / t ^ 3 := by
    unfold cubicMoment p
    simp only [div_pow]
    rw [tsum_div_const]
    exact congrArg (fun z : ℝ => z / t ^ 3) hs2.tsum_eq
  have he : t ^ 3 * third p = operatorThird T hTC := by
    have h := countable_newton hp hn hm.le
    rw [hm, hq, hr] at h
    unfold operatorThird
    rw [hmass]
    field_simp [ht.ne'] at h ⊢
    nlinarith
  have hscale : third (spectrum d) = t ^ 3 * third p := by
    have hl (k : ℕ) : tripleLayer (spectrum d) k = t ^ 3 * tripleLayer p k := by
      unfold tripleLayer
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [p]
      field_simp [ht.ne']
      <;> ring
    unfold third
    simp_rw [hl]
    exact tsum_mul_left
  refine ⟨d, hp, hn, hm, hq, hr, he,
    (absolute_triple_sum hsum (spectrum_nonneg d)).1, hscale.trans he⟩

/-- Homogeneous spectral envelope at positive trace. This statement concerns
the original trace-class operator and its actual third symmetric moment. -/
theorem trace_class_homogeneous_envelope {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (hTC : IsTraceClass T) {t : ℝ} (ht : 0 < t)
    (htrace : trace T hTC = (t : ℂ))
    (hpurity : powerTrace T hTC 1 ≤ (3 / 8) * t ^ 2) :
    (25 / 864) * t ^ 3 ≤ operatorThird T hTC ∧
      -(t ^ 3) / 432 ≤ operatorThird T hTC - t ^ 3 / 32 := by
  obtain ⟨d, hp, hn, hm, hq, _, he, _, _⟩ :=
    spectral_moments_at_mass hT hTC ht htrace
  have hq' : purity (fun n => spectrum d n / t) ≤ 3 / 8 := by
    rw [hq]
    exact (div_le_iff₀ (sq_pos_of_pos ht)).mpr hpurity
  have hb := third_lower_of_purity_le_three_eighths hp hn hm hq'
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg ht.le 3)
  rw [he] at hm
  constructor <;> nlinarith

#print axioms spectral_moments_at_mass
#print axioms trace_class_homogeneous_envelope

end TraceClassSpectralEnvelope
