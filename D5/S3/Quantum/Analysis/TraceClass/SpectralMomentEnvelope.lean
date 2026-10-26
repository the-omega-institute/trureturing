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
      third (spectrum d) = operatorThird T hTC := by
  let d := spectralData hT hTC
  have hs0 := spectrum_power_hasSum d hTC 0
  have hs1 := spectrum_power_hasSum d hTC 1
  have hs2 := spectrum_power_hasSum d hTC 2
  have ht : powerTrace T hTC 0 = 1 := by simp [powerTrace, htrace]
  have hmass : mass (spectrum d) = 1 := by
    simpa only [mass, pow_one, ht] using hs0.tsum_eq
  have hsum : Summable (spectrum d) := by simpa only [pow_one] using hs0.summable
  refine ⟨d, hsum, spectrum_nonneg d, hmass, ?_, ?_, ?_⟩
  · simpa only [purity, Nat.reduceAdd] using hs1.tsum_eq
  · simpa only [cubicMoment, Nat.reduceAdd] using hs2.tsum_eq
  · have hn := countable_newton hsum (spectrum_nonneg d) hmass.le
    have hq : purity (spectrum d) = powerTrace T hTC 1 := hs1.tsum_eq
    have hr : cubicMoment (spectrum d) = powerTrace T hTC 2 := hs2.tsum_eq
    rw [hmass, hq, hr] at hn
    unfold operatorThird
    rw [ht]
    linarith

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
  obtain ⟨d, hs, hn, hm, hq, _, he⟩ := spectral_moments hT hTC htrace
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

end TraceClassSpectralEnvelope
