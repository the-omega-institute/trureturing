/- GID: D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/ThreePhaseHistoryRigidity
   mirror-E: none(waiver:all-depth-ordered-histories)
   anchors: []
   utility: none
   digest: Uniformly bounded original ordered histories eliminate a nonzero Fourier increment. -/

import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

/-! The all-depth finite-history mechanism of C133 Continuation V, Section 3.
The conditional Fourier recursion is explicit; deriving it and both uniform
pairing bounds from the raw comparison remains a separate original-domain
obligation. The phase index is a group; the original label type is only a magma. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity

/-- All phase words, retaining order and multiplicity even at coincident labels. -/
def PhaseWords : ℕ → Type
  | 0 => Unit
  | n + 1 => PhaseWords n × ZMod 3

instance phaseWordsFintype (n : ℕ) : Fintype (PhaseWords n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (PhaseWords n × ZMod 3))

private lemma phaseWords_card (n : ℕ) : Fintype.card (PhaseWords n) = 3 ^ n := by
  induction n with
  | zero =>
      change Fintype.card Unit = 1
      exact Fintype.card_unique
  | succ n ih =>
      calc
        Fintype.card (PhaseWords (n + 1)) = Fintype.card (PhaseWords n × ZMod 3) :=
          Fintype.card_congr (Equiv.refl _)
        _ = Fintype.card (PhaseWords n) * 3 := by rw [Fintype.card_prod, ZMod.card]
        _ = 3 ^ (n + 1) := by rw [ih, pow_succ]

/-- The original binary operation is applied once at each step, with left bracketing. -/
def orderedHistory {M : Type*} [MulOneClass M] (U : M → M) (u : M) :
    (n : ℕ) → PhaseWords n → M
  | 0, _ => 1
  | n + 1, w => orderedHistory U u n w.1 * U^[w.2.val] u

private lemma history_mem {M : Type*} [MulOneClass M]
    (U : M → M) (u : M) (N : Set M) (h₁ : (1 : M) ∈ N)
    (hs : ∀ x ∈ N, ∀ k : ZMod 3, x * U^[k.val] u ∈ N)
    (n : ℕ) (w : PhaseWords n) : orderedHistory U u n w ∈ N := by
  induction n with
  | zero => exact h₁
  | succ n ih => exact hs _ (ih w.1) w.2

private lemma history_energy_growth {M : Type*} [MulOneClass M]
    (U : M → M) (u : M) (N : Set M) (h₁ : (1 : M) ∈ N)
    (hs : ∀ x ∈ N, ∀ k : ZMod 3, x * U^[k.val] u ∈ N)
    (E : M → ℝ) (d : ℝ)
    (he : ∀ x ∈ N, 3 * (E x + d) ≤ ∑ k : ZMod 3, E (x * U^[k.val] u))
    (n : ℕ) :
    (3 : ℝ) ^ n * (E 1 + (n : ℝ) * d) ≤
      ∑ w : PhaseWords n, E (orderedHistory U u n w) := by
  induction n with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, one_mul, orderedHistory]
      simp only [Finset.sum_const, Finset.card_univ, phaseWords_card, pow_zero, one_nsmul]
      exact le_rfl
  | succ n ih =>
      change _ ≤ ∑ w : PhaseWords n × ZMod 3,
        E (orderedHistory U u n w.1 * U^[w.2.val] u)
      rw [Fintype.sum_prod_type]
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
        he (orderedHistory U u n w) (history_mem U u N h₁ hs n w))
      have hc : (Fintype.card (PhaseWords n) : ℝ) = (3 : ℝ) ^ n := by
        rw [phaseWords_card]; norm_cast
      change (∑ w : PhaseWords n, 3 * (E (orderedHistory U u n w) + d)) ≤
        ∑ w : PhaseWords n, ∑ k : ZMod 3, E (orderedHistory U u n w * U^[k.val] u) at hsum
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hsum
      rw [hc] at hsum
      push_cast
      rw [pow_succ]
      nlinarith

private lemma bounded_energy_increment_nonpos {M : Type*} [MulOneClass M]
    (U : M → M) (u : M) (N : Set M) (h₁ : (1 : M) ∈ N)
    (hs : ∀ x ∈ N, ∀ k : ZMod 3, x * U^[k.val] u ∈ N)
    (E : M → ℝ) (d C : ℝ) (hb : ∀ x ∈ N, E x ≤ C)
    (he : ∀ x ∈ N, 3 * (E x + d) ≤ ∑ k : ZMod 3, E (x * U^[k.val] u)) :
    d ≤ 0 := by
  have hg (n : ℕ) : E 1 + (n : ℝ) * d ≤ C := by
    have hl := history_energy_growth U u N h₁ hs E d he n
    have hu := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
      hb (orderedHistory U u n w) (history_mem U u N h₁ hs n w))
    have hc : (Fintype.card (PhaseWords n) : ℝ) = (3 : ℝ) ^ n := by
      rw [phaseWords_card]; norm_cast
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
    rw [hc] at hu
    exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 3 ^ n)).mp (hl.trans hu)
  by_contra hd
  have hd' : 0 < d := lt_of_not_ge hd
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - E 1) / d)
  have hm := (div_lt_iff₀ hd').mp hn
  linarith [hg n]

private lemma phase_energy (χ : AddChar (ZMod 3) ℂ) (hχ : Function.Injective χ)
    (Z A D : ℂ) :
    ∑ k : ZMod 3, Complex.normSq (Z + χ k * A + χ⁻¹ k * D) =
      3 * (Complex.normSq Z + Complex.normSq A + Complex.normSq D) := by
  have h01 : (1 : AddChar (ZMod 3) ℂ) ≠ χ := by
    intro hh
    have hx : χ 1 = χ 0 := by rw [← hh]; simp
    have := hχ hx
    norm_num at this
  have h02 : (1 : AddChar (ZMod 3) ℂ) ≠ χ⁻¹ := by
    intro hh
    have hx : χ (-1) = χ 0 := by
      simpa using congrArg (fun ψ : AddChar (ZMod 3) ℂ => ψ 1) hh.symm
    have := hχ hx
    norm_num at this
  have h12 : χ ≠ χ⁻¹ := by
    intro hh
    have hx : χ 1 = χ (-1) := by
      simpa using congrArg (fun ψ : AddChar (ZMod 3) ℂ => ψ 1) hh
    exact (by decide : (1 : ZMod 3) ≠ -1) (hχ hx)
  let f : ZMod 3 → ℂ := Z • (⇑(1 : AddChar (ZMod 3) ℂ)) +
    A • (⇑χ) + D • (⇑(χ⁻¹))
  have hi : RCLike.wInner RCLike.cWeight f f =
      ((Complex.normSq Z + Complex.normSq A + Complex.normSq D : ℝ) : ℂ) := by
    dsimp only [f]
    simp only [RCLike.wInner_add_left, RCLike.wInner_add_right,
      RCLike.wInner_smul_left, RCLike.wInner_smul_right,
      AddChar.wInner_cWeight_eq_boole]
    simp only [ite_true, ite_eq_right h01, ite_eq_right h02, ite_eq_right h12,
      ite_eq_right (Ne.symm h01), ite_eq_right (Ne.symm h02), ite_eq_right (Ne.symm h12),
      smul_eq_mul, mul_zero, mul_one, zero_add, add_zero]
    change Z * conj Z + A * conj A + D * conj D =
      ((Complex.normSq Z + Complex.normSq A + Complex.normSq D : ℝ) : ℂ)
    simp only [Complex.mul_conj, Complex.ofReal_add]
  have hh := congrArg Complex.re hi
  have hs : (RCLike.wInner (𝕜 := ℂ) RCLike.cWeight f f).re =
      (1 / 3 : ℝ) * ∑ k : ZMod 3, Complex.normSq (f k) := by
    simp [RCLike.wInner, RCLike.cWeight,
      Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow, ← Finset.mul_sum]
  rw [hs] at hh
  have hf (k : ZMod 3) : f k = Z + χ k * A + χ⁻¹ k * D := by
    simp [f, mul_comm]
  simp only [Complex.ofReal_re, hf] at hh
  linarith

/-- A bounded Fourier mode vanishes using every ordered finite history.
Only the phase-index type is a group; no algebraic law is assumed on M beyond
its two-sided unit. The local Fourier recursion and uniform bound are premises. -/
theorem bounded_phase_recursion_vanishes {M : Type*} [MulOneClass M]
    (U : M → M) (u : M) (N : Set M) (h₁ : (1 : M) ∈ N)
    (hs : ∀ x ∈ N, ∀ k : ZMod 3, x * U^[k.val] u ∈ N)
    (χ : AddChar (ZMod 3) ℂ) (hχ : Function.Injective χ)
    (f D : M → ℂ) (C : ℝ)
    (hb : ∀ x ∈ N, Complex.normSq (f x) ≤ C)
    (hr : ∀ x ∈ N, ∀ k : ZMod 3,
      f (x * U^[k.val] u) = f x + χ k * f u + χ⁻¹ k * D x) :
    f u = 0 := by
  have he (x : M) (hx : x ∈ N) :
      3 * (Complex.normSq (f x) + Complex.normSq (f u)) ≤
        ∑ k : ZMod 3, Complex.normSq (f (x * U^[k.val] u)) := by
    simp_rw [hr x hx]
    rw [phase_energy χ hχ]
    nlinarith [Complex.normSq_nonneg (D x)]
  have hz := bounded_energy_increment_nonpos U u N h₁ hs
    (fun x => Complex.normSq (f x)) (Complex.normSq (f u)) C hb he
  exact Complex.normSq_eq_zero.mp (le_antisymm hz (Complex.normSq_nonneg _))

end D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity
