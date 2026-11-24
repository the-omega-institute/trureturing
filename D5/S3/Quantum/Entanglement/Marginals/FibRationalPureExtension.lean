/- GID: D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A rational norm criterion for pure two-word Fibonacci marginal extensions. -/

import D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension
import D5.S3.Quantum.PureState.PureStateHandshake

/-! Rational pure extensions for the two-word Fibonacci marginal family. -/

open Matrix Complex
open scoped ComplexConjugate ComplexOrder
open D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension
open D5.S3.Quantum.PureState.PureStateHandshake

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension

private theorem pure_pair_norm (b : ℝ) (ψ : Word → ℂ)
    (hl : edgeTrace (rankOneDensity ψ) 1 2 = edgeState (1 - b) b 0)
    (hr : edgeTrace (rankOneDensity ψ) 2 1 = edgeState (1 - b) b 0) :
    normSq (rankOneDensity ψ (.inl 0) (.inr true)) = b * (1 - b) := by
  have hb := congrFun (congrFun hl 1) 1
  change ψ (.inl 0) * conj (ψ (.inl 0)) + 0 = (b : ℂ) at hb
  rw [add_zero, Complex.mul_conj] at hb
  have hbr : normSq (ψ (.inl 0)) = b := Complex.ofReal_injective hb
  have hz := congrFun (congrFun hr 0) 0
  change ψ (.inr false) * conj (ψ (.inr false)) +
    ψ (.inl 1) * conj (ψ (.inl 1)) = ((1-(1 - b)-b : ℝ) : ℂ) at hz
  rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add] at hz
  have hzr := Complex.ofReal_injective hz
  have hzero : normSq (ψ (.inl 1)) = 0 := by
    linarith only [hzr, normSq_nonneg (ψ (.inl 1)), normSq_nonneg (ψ (.inr false))]
  have he := congrFun (congrFun hl 2) 2
  change ψ (.inl 1) * conj (ψ (.inl 1)) +
    ψ (.inr true) * conj (ψ (.inr true)) = ((1 - b : ℝ) : ℂ) at he
  rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add] at he
  have her := Complex.ofReal_injective he
  rw [hzero, zero_add] at her
  change normSq (ψ (.inl 0) * conj (ψ (.inr true))) = _
  rw [normSq_mul, normSq_conj, hbr, her]

private def pairKet (x y : ℂ) (i : Word) : ℂ :=
  if i = .inl 0 then x else if i = .inr true then y else 0

private theorem pairKet_read (x y : ℂ) (b : ℝ)
    (hx : normSq x = b) (hy : normSq y = 1 - b) :
    let ρ := rankOneDensity (pairKet x y)
    edgeTrace ρ 1 2 = edgeState (1 - b) b 0 ∧
      edgeTrace ρ 2 1 = edgeState (1 - b) b 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [edgeTrace, edgeState, rankOneDensity, Matrix.vecMulVec_apply, pairKet,
      Complex.mul_conj, hx, hy]
  all_goals
    first
    | change (0 : ℂ) = 0
      rfl
    | change x = 0 ∨ (0 : ℂ) = 0
      exact Or.inr rfl
    | change y * conj y = 1 - (b : ℂ)
      rw [Complex.mul_conj, hy, Complex.ofReal_sub, Complex.ofReal_one]


/-- A matrix entry whose real and imaginary parts are rational. -/
def RationalEntry (z : ℂ) : Prop :=
  ∃ a c : ℚ, (a : ℝ) = z.re ∧ (c : ℝ) = z.im

private theorem rationalEntry_zero : RationalEntry 0 := ⟨0, 0, by simp, by simp⟩

private theorem rationalEntry_real (b : ℚ) : RationalEntry (↑(b : ℝ) : ℂ) :=
  ⟨b, 0, rfl, by simp⟩

private theorem rationalEntry_conj {z : ℂ} (hz : RationalEntry z) : RationalEntry (conj z) := by
  obtain ⟨a, c, ha, hc⟩ := hz
  exact ⟨a, -c, by simpa using ha, by simpa using congrArg Neg.neg hc⟩

private theorem pairKet_trace (x y : ℂ) (b : ℝ)
    (hx : normSq x = b) (hy : normSq y = 1 - b) :
    (rankOneDensity (pairKet x y)).trace = 1 := by
  simp [Matrix.trace, Fintype.sum_sum_type, rankOneDensity, Matrix.vecMulVec_apply, pairKet,
    Complex.mul_conj, hx, hy, Complex.ofReal_sub]

private theorem pairKet_rat (x y z : ℂ) (b : ℚ)
    (hx : normSq x = (b : ℝ)) (hy : normSq y = 1 - (b : ℝ))
    (hz : x * conj y = z) (hq : RationalEntry z) :
    ∀ i j, RationalEntry (rankOneDensity (pairKet x y) i j) := by
  intro i j
  have hxc : RationalEntry (x * conj x) := by
    rw [Complex.mul_conj, hx]
    exact rationalEntry_real b
  have hyc : RationalEntry (y * conj y) := by
    rw [Complex.mul_conj, hy]
    simpa [Rat.cast_sub, Complex.ofReal_sub] using rationalEntry_real (1 - b)
  have hxy : RationalEntry (x * conj y) := hz ▸ hq
  have hyx : RationalEntry (y * conj x) := by
    simpa [map_mul, mul_comm] using rationalEntry_conj hxy
  change RationalEntry (pairKet x y i * conj (pairKet x y j))
  by_cases hi : i = .inl 0 <;> by_cases hj : j = .inl 0 <;>
    by_cases hi' : i = .inr true <;> by_cases hj' : j = .inr true <;>
    simp only [pairKet, hi, hj, hi', hj', ite_true, ite_false, map_zero, zero_mul, mul_zero] <;>
    first | exact hxc | exact hyc | exact hxy | exact hyx | exact rationalEntry_zero

/-- The exact couplings of rational pure extensions in the two-word Fibonacci family. -/
theorem rational_pure_coupling_iff (b : ℝ) (z : ℂ) :
    (∃ ψ : Word → ℂ, let ρ := rankOneDensity ψ
      ρ.trace = 1 ∧ edgeTrace ρ 1 2 = edgeState (1 - b) b 0 ∧
      edgeTrace ρ 2 1 = edgeState (1 - b) b 0 ∧
      ρ (.inl 0) (.inr true) = z ∧ ∀ i j, RationalEntry (ρ i j)) ↔
      (∃ q : ℚ, (q : ℝ) = b) ∧ RationalEntry z ∧ normSq z = b * (1 - b) := by
  constructor
  · rintro ⟨ψ, _, hl, hr, hxy, hrat⟩
    obtain ⟨q, _, hq, _⟩ := hrat (.inl 0) (.inl 0)
    have hb := congrFun (congrFun hl 1) 1
    change rankOneDensity ψ (.inl 0) (.inl 0) + 0 = (b : ℂ) at hb
    rw [add_zero] at hb
    refine ⟨⟨q, ?_⟩, hxy ▸ hrat (.inl 0) (.inr true), ?_⟩
    · simpa only [Complex.ofReal_re, hb] using hq
    · rw [← hxy]
      exact pure_pair_norm b ψ hl hr
  · rintro ⟨⟨q, rfl⟩, hrat, hz⟩
    have hb : 0 ≤ (q : ℝ) := by nlinarith [normSq_nonneg z]
    have hsome (x y : ℂ) (hx : normSq x = (q : ℝ)) (hy : normSq y = 1 - (q : ℝ))
        (hxy : x * conj y = z) :
        ∃ ψ : Word → ℂ, let ρ := rankOneDensity ψ
          ρ.trace = 1 ∧ edgeTrace ρ 1 2 = edgeState (1 - (q : ℝ)) q 0 ∧
          edgeTrace ρ 2 1 = edgeState (1 - (q : ℝ)) q 0 ∧
          ρ (.inl 0) (.inr true) = z ∧ ∀ i j, RationalEntry (ρ i j) := by
      have hout := pairKet_read x y q hx hy
      refine ⟨pairKet x y, pairKet_trace x y q hx hy, hout.1, hout.2, ?_,
        pairKet_rat x y z q hx hy hxy hrat⟩
      change pairKet x y (.inl 0) * conj (pairKet x y (.inr true)) = z
      simpa [pairKet] using hxy
    rcases hb.eq_or_lt with h0 | hp
    · have hz0 : z = 0 := normSq_eq_zero.mp (by simp [hz, ← h0])
      apply hsome 0 1 <;> simp [hz0, ← h0]
    · let s : ℝ := Real.sqrt q
      let y := conj z / (s : ℂ)
      have hs : (s : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
      have hnorm : normSq (s : ℂ) = (q : ℝ) := by
        rw [normSq_ofReal]
        exact Real.mul_self_sqrt hb
      apply hsome (s : ℂ) y hnorm
      · rw [show y = conj z / (s : ℂ) from rfl, normSq_div, normSq_conj, hnorm, hz]
        exact mul_div_cancel_left₀ _ hp.ne'
      · simp [y, map_div₀]
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hs]

end D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
