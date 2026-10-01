/- GID: D5/S3/Quantum/Measurement/HoggarSicSumNegativity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/HoggarSicSumNegativity
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Hoggar-SIC Q-minus sum negativity has the sharp global maximum 7/8. -/

/-
proof_shape: result: content; private sic_negativity_bound: content
escape_witness: sic_negativity_bound constructs the trace-orthogonal operator basis,
  recovers its coefficients, derives Parseval and the purity bound, and sums the
  quadratic majorant to bound every positive-semidefinite trace-one state by 7/8.
admission_basis: open-problem-resolution (#11512; Proved)
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.trace_hermitian_product_real
    statement_id: sha256:d57aafbe2afd1228c9b5e26bf06684ec80accc922d16f29290f16819337adc81
  D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef (namespace RHLinalg)
    statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
  D5/S3/Observer/BornReduction.rank_one_pure_state_modulus_square_reduction
    statement_id: sha256:b7155f94bd432210b5cbf71d0d3184450ca73a997dcd978a493c907ee4fc45e0
Utility: the result is universal over all density matrices. The finite Gaussian-integer
  computations certify frame identities and an attaining state; they are not the bound.
-/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Observer.BornReduction

open scoped BigOperators ComplexOrder
open Matrix
namespace D5.S3.Quantum.Measurement.HoggarSicSumNegativity

private theorem sic_negativity_bound
    (P : Fin 64 → Matrix (Fin 8) (Fin 8) ℂ)
    (hp : ∀ j, (P j).PosSemidef) (htp : ∀ j, (P j).trace = 1)
    (hov : ∀ j k, (P j * P k).trace = if j=k then 1 else 1/9)
    (ρ : Matrix (Fin 8) (Fin 8) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace=1) :
    ∑ j, max 0 (-((ρ * ((3:ℂ) • P j - (1/4:ℂ) • 1)).trace.re / 8)) ≤ 7/8 := by
  let Q := fun j => (3:ℂ) • P j - (1/4:ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ)
  have hQt (j) : (Q j).trace = 1 := by
    simp [Q, Matrix.trace_sub, Matrix.trace_smul, htp]
    norm_num
  have hQh (j) : (Q j).IsHermitian := by
    exact ((hp j).isHermitian.smul (by norm_num : star (3:ℂ)=3)).sub
      (Matrix.isHermitian_one.smul (by norm_num : star (1/4:ℂ)=1/4))
  have ho (j k) : (Q j * Q k).trace = if j=k then 8 else 0 := by
    simp only [Q, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul, mul_one, one_mul, smul_smul,
      hov, htp, smul_eq_mul, Matrix.trace_one, Fintype.card_fin]
    split_ifs <;> norm_num
  have hli : LinearIndependent ℂ Q := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have he := congrArg (fun A => (A * Q j).trace) hc
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      Matrix.zero_mul, Matrix.trace_zero] at he
    simp_rw [ho, smul_eq_mul, mul_ite, mul_zero] at he
    simpa using he
  let b := basisOfLinearIndependentOfCardEqFinrank hli
    (by simp [Module.finrank_matrix] : Fintype.card (Fin 64) =
      Module.finrank ℂ (Matrix (Fin 8) (Fin 8) ℂ))
  have hb (j) : b j = Q j := by simp [b]
  have hr (A : Matrix (Fin 8) (Fin 8) ℂ) (j) :
      b.repr A j = (A * Q j).trace / 8 := by
    have he := congrArg (fun A => (A * Q j).trace) (b.sum_repr A)
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul] at he
    simp_rw [hb, ho, smul_eq_mul, mul_ite, mul_zero] at he
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at he
    apply (eq_div_iff (by norm_num : (8:ℂ) ≠ 0)).mpr
    exact he
  have hsumQ : ∑ j, Q j = (8:ℂ) • 1 := by
    have hi := b.sum_repr (1 : Matrix (Fin 8) (Fin 8) ℂ)
    simp_rw [hb, hr, one_mul, hQt] at hi
    rw [← Finset.smul_sum] at hi
    calc
      ∑ j, Q j = (8:ℂ) • ((1/8:ℂ) • ∑ j, Q j) := by norm_num [smul_smul]
      _ = (8:ℂ) • 1 := by rw [hi]
  have hparseval : ∑ j, (ρ * Q j).trace ^ 2 = 8 * (ρ * ρ).trace := by
    have he := congrArg (fun A => (A * ρ).trace) (b.sum_repr ρ)
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul] at he
    simp_rw [hb, hr, Matrix.trace_mul_comm (Q _) ρ, smul_eq_mul] at he
    calc
      ∑ j, (ρ * Q j).trace ^ 2 = 8 * ∑ j, ((ρ * Q j).trace / 8) * (ρ * Q j).trace := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 8 * (ρ * ρ).trace := by rw [he]
  have hreal (j) : (ρ * Q j).trace.im = 0 :=
    D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real
      ρ (Q j) hρ.isHermitian (hQh j)
  let q := fun j => (ρ * Q j).trace.re / 8
  have hlow (j) : -(1/32:ℝ) ≤ q j := by
    have hn := RHLinalg.trace_mul_nonneg_of_posSemidef hρ (hp j)
    simp only [q, Q, mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      mul_one, ht, smul_eq_mul, Complex.sub_re, Complex.mul_re] 
    norm_num at *
    linarith
  have hsum : ∑ j, q j = 1 := by
    simp only [q, ← Finset.sum_div, ← Complex.re_sum, ← Matrix.trace_sum,
      ← Matrix.mul_sum, hsumQ, Matrix.mul_smul, mul_one, Matrix.trace_smul, ht]
    norm_num
  have hsq : ∑ j, (q j)^2 = (ρ * ρ).trace.re / 8 := by
    have he := congrArg Complex.re hparseval
    simp only [Complex.re_sum, Complex.mul_re, pow_two, hreal] at he
    norm_num at he
    have he' : ∑ j, (ρ * Q j).trace.re ^ 2 = 8 * (ρ * ρ).trace.re := by
      simpa only [pow_two] using he
    simp only [q, div_pow, ← Finset.sum_div]
    norm_num
    linarith only [he']
  have hpur : (ρ * ρ).trace.re ≤ 1 := by
    let h := hρ.isHermitian
    have hs : ∑ i, h.eigenvalues i = 1 := by
      have hh := congrArg Complex.re h.trace_eq_sum_eigenvalues
      simpa [ht] using hh.symm
    have hsq : (ρ * ρ).trace = ∑ i, ((h.eigenvalues i : ℂ) ^ 2) := by
      conv_lhs => rw [h.spectral_theorem]
      rw [Unitary.conjStarAlgAut_apply]
      simp only [mul_assoc]
      rw [← mul_assoc (star (h.eigenvectorUnitary : Matrix (Fin 8) (Fin 8) ℂ))
        (h.eigenvectorUnitary : Matrix (Fin 8) (Fin 8) ℂ)]
      simp only [Unitary.coe_star_mul_self, one_mul]
      rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_cycle]
      simp only [← mul_assoc, Unitary.coe_star_mul_self, one_mul,
        Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Function.comp_apply, pow_two]
      rfl
    rw [hsq]
    simp only [← Complex.ofReal_pow, Complex.re_sum, Complex.ofReal_re]
    have hb := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := h.eigenvalues) (fun i _ => hρ.eigenvalues_nonneg i)
    simpa [hs] using hb
  have hqb : ∑ j, (q j)^2 ≤ 1/8 := by rw [hsq]; linarith
  have hm (t : ℝ) (ht : -(1/32:ℝ) ≤ t) :
      max 0 (-t) ≤ 9/2 * (t - 5/96)^2 := by
    apply max_le
    · positivity
    · have hp : 0 ≤ (32*t+1)*(288*t+25) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  change ∑ j, max 0 (-q j) ≤ 7/8
  calc
    ∑ j, max 0 (-q j) ≤ ∑ j, 9/2 * (q j - 5/96)^2 :=
      Finset.sum_le_sum (fun j _ => hm (q j) (hlow j))
    _ = 9/2 * (∑ j, (q j)^2) - 15/32 * (∑ j, q j) + 25/2048 * 64 := by
      simp_rw [show ∀ t : ℝ, 9/2 * (t-5/96)^2 = 9/2*t^2-15/32*t+25/2048 by intro t; ring]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ 7/8 := by rw [hsum]; linarith

def bitSign (z b : ℕ) : GaussianInt :=
  if (z%2 * (b%2) + z/2%2 * (b/2%2) + z/4%2 * (b/4%2)) % 2 = 0 then 1 else -1

def orbitG (j : Fin 64) (b : Fin 8) : GaussianInt :=
  bitSign (j.val%8) (Nat.xor b.val (j.val/8)) *
    (if b.val = j.val/8 then ⟨-1,2⟩ else 1)

private def orbitTable (j : Fin 64) : Fin 8 → GaussianInt :=
  if j.val < 32 then
    if j.val < 16 then
      if j.val < 8 then
        if j.val < 4 then
          if j.val < 2 then
            if j.val < 1 then
              ![⟨-1,2⟩, 1, 1, 1, 1, 1, 1, 1]
            else
              ![⟨-1,2⟩, -1, 1, -1, 1, -1, 1, -1]
          else
            if j.val < 3 then
              ![⟨-1,2⟩, 1, -1, -1, 1, 1, -1, -1]
            else
              ![⟨-1,2⟩, -1, -1, 1, 1, -1, -1, 1]
        else
          if j.val < 6 then
            if j.val < 5 then
              ![⟨-1,2⟩, 1, 1, 1, -1, -1, -1, -1]
            else
              ![⟨-1,2⟩, -1, 1, -1, -1, 1, -1, 1]
          else
            if j.val < 7 then
              ![⟨-1,2⟩, 1, -1, -1, -1, -1, 1, 1]
            else
              ![⟨-1,2⟩, -1, -1, 1, -1, 1, 1, -1]
      else
        if j.val < 12 then
          if j.val < 10 then
            if j.val < 9 then
              ![1, ⟨-1,2⟩, 1, 1, 1, 1, 1, 1]
            else
              ![-1, ⟨-1,2⟩, -1, 1, -1, 1, -1, 1]
          else
            if j.val < 11 then
              ![1, ⟨-1,2⟩, -1, -1, 1, 1, -1, -1]
            else
              ![-1, ⟨-1,2⟩, 1, -1, -1, 1, 1, -1]
        else
          if j.val < 14 then
            if j.val < 13 then
              ![1, ⟨-1,2⟩, 1, 1, -1, -1, -1, -1]
            else
              ![-1, ⟨-1,2⟩, -1, 1, 1, -1, 1, -1]
          else
            if j.val < 15 then
              ![1, ⟨-1,2⟩, -1, -1, -1, -1, 1, 1]
            else
              ![-1, ⟨-1,2⟩, 1, -1, 1, -1, -1, 1]
    else
      if j.val < 24 then
        if j.val < 20 then
          if j.val < 18 then
            if j.val < 17 then
              ![1, 1, ⟨-1,2⟩, 1, 1, 1, 1, 1]
            else
              ![1, -1, ⟨-1,2⟩, -1, 1, -1, 1, -1]
          else
            if j.val < 19 then
              ![-1, -1, ⟨-1,2⟩, 1, -1, -1, 1, 1]
            else
              ![-1, 1, ⟨-1,2⟩, -1, -1, 1, 1, -1]
        else
          if j.val < 22 then
            if j.val < 21 then
              ![1, 1, ⟨-1,2⟩, 1, -1, -1, -1, -1]
            else
              ![1, -1, ⟨-1,2⟩, -1, -1, 1, -1, 1]
          else
            if j.val < 23 then
              ![-1, -1, ⟨-1,2⟩, 1, 1, 1, -1, -1]
            else
              ![-1, 1, ⟨-1,2⟩, -1, 1, -1, -1, 1]
      else
        if j.val < 28 then
          if j.val < 26 then
            if j.val < 25 then
              ![1, 1, 1, ⟨-1,2⟩, 1, 1, 1, 1]
            else
              ![-1, 1, -1, ⟨-1,2⟩, -1, 1, -1, 1]
          else
            if j.val < 27 then
              ![-1, -1, 1, ⟨-1,2⟩, -1, -1, 1, 1]
            else
              ![1, -1, -1, ⟨-1,2⟩, 1, -1, -1, 1]
        else
          if j.val < 30 then
            if j.val < 29 then
              ![1, 1, 1, ⟨-1,2⟩, -1, -1, -1, -1]
            else
              ![-1, 1, -1, ⟨-1,2⟩, 1, -1, 1, -1]
          else
            if j.val < 31 then
              ![-1, -1, 1, ⟨-1,2⟩, 1, 1, -1, -1]
            else
              ![1, -1, -1, ⟨-1,2⟩, -1, 1, 1, -1]
  else
    if j.val < 48 then
      if j.val < 40 then
        if j.val < 36 then
          if j.val < 34 then
            if j.val < 33 then
              ![1, 1, 1, 1, ⟨-1,2⟩, 1, 1, 1]
            else
              ![1, -1, 1, -1, ⟨-1,2⟩, -1, 1, -1]
          else
            if j.val < 35 then
              ![1, 1, -1, -1, ⟨-1,2⟩, 1, -1, -1]
            else
              ![1, -1, -1, 1, ⟨-1,2⟩, -1, -1, 1]
        else
          if j.val < 38 then
            if j.val < 37 then
              ![-1, -1, -1, -1, ⟨-1,2⟩, 1, 1, 1]
            else
              ![-1, 1, -1, 1, ⟨-1,2⟩, -1, 1, -1]
          else
            if j.val < 39 then
              ![-1, -1, 1, 1, ⟨-1,2⟩, 1, -1, -1]
            else
              ![-1, 1, 1, -1, ⟨-1,2⟩, -1, -1, 1]
      else
        if j.val < 44 then
          if j.val < 42 then
            if j.val < 41 then
              ![1, 1, 1, 1, 1, ⟨-1,2⟩, 1, 1]
            else
              ![-1, 1, -1, 1, -1, ⟨-1,2⟩, -1, 1]
          else
            if j.val < 43 then
              ![1, 1, -1, -1, 1, ⟨-1,2⟩, -1, -1]
            else
              ![-1, 1, 1, -1, -1, ⟨-1,2⟩, 1, -1]
        else
          if j.val < 46 then
            if j.val < 45 then
              ![-1, -1, -1, -1, 1, ⟨-1,2⟩, 1, 1]
            else
              ![1, -1, 1, -1, -1, ⟨-1,2⟩, -1, 1]
          else
            if j.val < 47 then
              ![-1, -1, 1, 1, 1, ⟨-1,2⟩, -1, -1]
            else
              ![1, -1, -1, 1, -1, ⟨-1,2⟩, 1, -1]
    else
      if j.val < 56 then
        if j.val < 52 then
          if j.val < 50 then
            if j.val < 49 then
              ![1, 1, 1, 1, 1, 1, ⟨-1,2⟩, 1]
            else
              ![1, -1, 1, -1, 1, -1, ⟨-1,2⟩, -1]
          else
            if j.val < 51 then
              ![-1, -1, 1, 1, -1, -1, ⟨-1,2⟩, 1]
            else
              ![-1, 1, 1, -1, -1, 1, ⟨-1,2⟩, -1]
        else
          if j.val < 54 then
            if j.val < 53 then
              ![-1, -1, -1, -1, 1, 1, ⟨-1,2⟩, 1]
            else
              ![-1, 1, -1, 1, 1, -1, ⟨-1,2⟩, -1]
          else
            if j.val < 55 then
              ![1, 1, -1, -1, -1, -1, ⟨-1,2⟩, 1]
            else
              ![1, -1, -1, 1, -1, 1, ⟨-1,2⟩, -1]
      else
        if j.val < 60 then
          if j.val < 58 then
            if j.val < 57 then
              ![1, 1, 1, 1, 1, 1, 1, ⟨-1,2⟩]
            else
              ![-1, 1, -1, 1, -1, 1, -1, ⟨-1,2⟩]
          else
            if j.val < 59 then
              ![-1, -1, 1, 1, -1, -1, 1, ⟨-1,2⟩]
            else
              ![1, -1, -1, 1, 1, -1, -1, ⟨-1,2⟩]
        else
          if j.val < 62 then
            if j.val < 61 then
              ![-1, -1, -1, -1, 1, 1, 1, ⟨-1,2⟩]
            else
              ![1, -1, 1, -1, -1, 1, -1, ⟨-1,2⟩]
          else
            if j.val < 63 then
              ![1, 1, -1, -1, -1, -1, 1, ⟨-1,2⟩]
            else
              ![-1, 1, 1, -1, 1, -1, -1, ⟨-1,2⟩]

noncomputable def hoggarVector (j : Fin 64) (b : Fin 8) : ℂ := GaussianInt.toComplex (orbitG j b)
noncomputable def hoggarProjector (j : Fin 64) : Matrix (Fin 8) (Fin 8) ℂ :=
  (1/12:ℂ) • vecMulVec (hoggarVector j) (star (hoggarVector j))
noncomputable def hoggarQ (j : Fin 64) : Matrix (Fin 8) (Fin 8) ℂ :=
  (3:ℂ) • hoggarProjector j - (1/4:ℂ) • 1
noncomputable def quasiprobability (ρ : Matrix (Fin 8) (Fin 8) ℂ) (j : Fin 64) : ℝ :=
  (ρ * hoggarQ j).trace.re / 8
noncomputable def negativePart (p : ℝ) : ℝ := (|p| - p) / 2

noncomputable def sumNegativity (ρ : Matrix (Fin 8) (Fin 8) ℂ) : ℝ :=
  ∑ j, negativePart (quasiprobability ρ j)

def claim : Prop :=
  IsGreatest {r : ℝ | ∃ ρ : Matrix (Fin 8) (Fin 8) ℂ,
    ρ.PosSemidef ∧ ρ.trace = 1 ∧ sumNegativity ρ = r} (7/8)

theorem result : claim := by
  have hnegative (p : ℝ) : negativePart p = max 0 (-p) := by
    by_cases h : 0 ≤ p
    · rw [negativePart, abs_of_nonneg h, max_eq_left (by linarith)]
      ring
    · have hle : p ≤ 0 := le_of_lt (lt_of_not_ge h)
      rw [negativePart, abs_of_nonpos hle, max_eq_right (by linarith)]
      ring
  have hn : ∀ j : Fin 64, ∑ a : Fin 8, Zsqrtd.norm (orbitG j a) = 12 := by
    decide +kernel
  have htable : ∀ j : Fin 64, ∀ a : Fin 8, orbitG j a = orbitTable j a := by
    intro j
    fin_cases j <;> decide +kernel
  have hov : ∀ j k : Fin 64,
      Zsqrtd.norm (∑ a : Fin 8, star (orbitG j a) * orbitG k a) =
        if j=k then 144 else 16 := by
    intro j
    simp_rw [htable]
    simp only [Fin.sum_univ_succ, Zsqrtd.norm, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
    fin_cases j <;> decide +kernel
  have hp : (∀ j, (hoggarProjector j).PosSemidef) ∧
      (∀ j, (hoggarProjector j).trace = 1) ∧
      (∀ j k, (hoggarProjector j * hoggarProjector k).trace = if j=k then 1 else 1/9) := by
    have hdot (j k) : star (hoggarVector j) ⬝ᵥ hoggarVector k =
        GaussianInt.toComplex (∑ a : Fin 8, star (orbitG j a) * orbitG k a) := by
      simp only [dotProduct, hoggarVector, map_sum, map_mul, GaussianInt.toComplex_star,
        Pi.star_apply, Complex.star_def]
    have hnorm (j k) : Complex.normSq (star (hoggarVector j) ⬝ᵥ hoggarVector k) =
        if j=k then 144 else 16 := by
      rw [hdot, ← GaussianInt.intCast_real_norm, hov]
      split_ifs <;> norm_num
    refine ⟨?_, ?_, ?_⟩
    · intro j
      exact (Matrix.posSemidef_vecMulVec_self_star (hoggarVector j)).smul (by norm_num [Complex.nonneg_iff] : (0:ℂ) ≤ 1/12)
    · intro j
      have hs : hoggarVector j ⬝ᵥ star (hoggarVector j) = 12 := by
        change (∑ a, hoggarVector j a * star (hoggarVector j a)) = 12
        have hc := congrArg (fun z : ℤ => (z : ℂ)) (hn j)
        simp only [Int.cast_sum, Int.cast_ofNat] at hc
        simp only [hoggarVector, Complex.star_def]
        simp_rw [mul_comm (GaussianInt.toComplex _), ← Complex.normSq_eq_conj_mul_self,
          ← GaussianInt.intCast_complex_norm]
        exact hc
      simp [hoggarProjector, Matrix.trace_smul, Matrix.trace_vecMulVec, hs]
    · intro j k
      have hb := D5.S3.Observer.BornReduction.rank_one_pure_state_modulus_square_reduction
        (fun k => vecMulVec (hoggarVector k) (star (hoggarVector k))) (vecMulVec (hoggarVector j) (star (hoggarVector j)))
        k (hoggarVector k) (hoggarVector j) rfl rfl
      simp only [D5.S3.Observer.Conditioning.recordWeight,
        D5.S3.Quantum.FiniteDimensional.bornProbability] at hb
      rw [hoggarProjector, hoggarProjector, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.trace_smul, smul_eq_mul, hb, ← Complex.normSq_eq_norm_sq, hnorm]
      by_cases h : j=k
      · subst k; norm_num
      · have h' : k≠j := Ne.symm h
        norm_num [h, h']
  have attain : ∃ ρ : Matrix (Fin 8) (Fin 8) ℂ,
      ρ.PosSemidef ∧ ρ.trace=1 ∧ sumNegativity ρ = 7/8 := by
    let wG : Fin 8 → GaussianInt := fun b => if b=0 then ⟨-1,-2⟩ else 1
    let w : Fin 8 → ℂ := fun b => GaussianInt.toComplex (wG b)
    let ρ : Matrix (Fin 8) (Fin 8) ℂ := (1/12:ℂ) • vecMulVec w (star w)
    let n : Fin 64 → ℤ := fun j => Zsqrtd.norm (∑ a, star (orbitG j a) * wG a)
    have hn (j) : n j = 0 ∨ n j = 32 := by
      fin_cases j <;> decide +kernel
    have hcount : (Finset.univ.filter (fun j => n j = 0)).card = 28 := by decide +kernel
    have hwG : ∑ a, Zsqrtd.norm (wG a) = 12 := by decide +kernel
    have hwt : (vecMulVec w (star w)).trace = 12 := by
      rw [Matrix.trace_vecMulVec]
      change ∑ a, w a * star (w a) = 12
      have hc := congrArg (fun z : ℤ => (z : ℂ)) hwG
      simp only [Int.cast_sum, Int.cast_ofNat] at hc
      simp only [w, Complex.star_def]
      simp_rw [mul_comm (GaussianInt.toComplex _), ← Complex.normSq_eq_conj_mul_self,
        ← GaussianInt.intCast_complex_norm]
      exact hc
    have ht : ρ.trace=1 := by simp [ρ, Matrix.trace_smul, hwt]
    have hdot (j) : star (hoggarVector j) ⬝ᵥ w = GaussianInt.toComplex (∑ a, star (orbitG j a) * wG a) := by
      simp only [dotProduct, hoggarVector, w, map_sum, map_mul, GaussianInt.toComplex_star,
        Pi.star_apply, Complex.star_def]
    have hb (j) : (vecMulVec w (star w) * vecMulVec (hoggarVector j) (star (hoggarVector j))).trace =
        (n j : ℂ) := by
      have hh := D5.S3.Observer.BornReduction.rank_one_pure_state_modulus_square_reduction
        (fun k => vecMulVec (hoggarVector k) (star (hoggarVector k))) (vecMulVec w (star w))
        j (hoggarVector j) w rfl rfl
      simp only [D5.S3.Observer.Conditioning.recordWeight,
        D5.S3.Quantum.FiniteDimensional.bornProbability] at hh
      rw [hh, ← Complex.normSq_eq_norm_sq, hdot, ← GaussianInt.intCast_complex_norm]
    have hqj (j) : quasiprobability ρ j = if n j=0 then -1/32 else 5/96 := by
      have hraw : (ρ * hoggarProjector j).trace = (1/144:ℂ) * (n j:ℂ) := by
        simp only [hoggarProjector, ρ, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          Matrix.trace_smul, hb, smul_eq_mul]
        ring
      simp only [quasiprobability, hoggarQ, mul_sub, Matrix.mul_smul, Matrix.trace_sub,
        Matrix.trace_smul, mul_one, ht, hraw, smul_eq_mul]
      rcases hn j with h | h <;> simp [h] <;> norm_num
    refine ⟨ρ, ?_, ht, ?_⟩
    · exact (Matrix.posSemidef_vecMulVec_self_star w).smul (by norm_num [Complex.nonneg_iff] : (0:ℂ) ≤ 1/12)
    · unfold sumNegativity
      simp_rw [hnegative, hqj]
      have hm (j) : max 0 (-(if n j=0 then (-1/32:ℝ) else 5/96)) =
          if n j=0 then 1/32 else 0 := by split_ifs <;> norm_num
      simp_rw [hm]
      rw [← Finset.sum_filter]
      norm_num [hcount]
  constructor
  · exact attain
  · intro r hr
    rcases hr with ⟨ρ, hρ, ht, rfl⟩
    simpa only [sumNegativity, hnegative, quasiprobability, hoggarQ] using
      sic_negativity_bound hoggarProjector hp.1 hp.2.1 hp.2.2 ρ hρ ht

end D5.S3.Quantum.Measurement.HoggarSicSumNegativity
