/- GID: D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.claim; result=D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.result; claim=D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.claim
   digest: The Harrow channel pair has parallel Chernoff exponent at least two. -/

import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation

/-! The input |01⟩ yields a parallel error exponent bounded below by two. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.QuantumChannels.HarrowParallelChernoffExponentRefutation

open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder ENNReal
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (kron kron_def)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation (diagonal_norm)

/-- Example 5, with the input factors ordered as A, C. -/
def harrowM : MatrixMap (Fin 2 × Fin 2) (Fin 2) ℂ where
  toFun x := fun c d =>
    if c = d then
      (if c = 0 then x (0, 0) (0, 0) + x (1, 0) (1, 0) + x (0, 1) (0, 1) else 0) +
        x (1, 1) (1, 1) / 2
    else 0
  map_add' := by
    intro x y
    ext c d
    change (if c = d then
      (if c = 0 then (x + y) (0, 0) (0, 0) + (x + y) (1, 0) (1, 0) + (x + y) (0, 1) (0, 1) else 0) +
        (x + y) (1, 1) (1, 1) / 2
    else 0) = (if c = d then
      (if c = 0 then x (0, 0) (0, 0) + x (1, 0) (1, 0) + x (0, 1) (0, 1) else 0) +
        x (1, 1) (1, 1) / 2
    else 0) + (if c = d then
      (if c = 0 then y (0, 0) (0, 0) + y (1, 0) (1, 0) + y (0, 1) (0, 1) else 0) +
        y (1, 1) (1, 1) / 2
    else 0)
    simp only [Matrix.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro r x
    ext c d
    change (if c = d then
      (if c = 0 then
        (r • x) (0, 0) (0, 0) + (r • x) (1, 0) (1, 0) + (r • x) (0, 1) (0, 1) else 0) +
        (r • x) (1, 1) (1, 1) / 2
    else 0) = r * (if c = d then
      (if c = 0 then x (0, 0) (0, 0) + x (1, 0) (1, 0) + x (0, 1) (0, 1) else 0) +
        x (1, 1) (1, 1) / 2
    else 0)
    simp only [Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring

/-- The second channel of Example 5, including the off-diagonal A entries. -/
def harrowMbar : MatrixMap (Fin 2 × Fin 2) (Fin 2) ℂ where
  toFun x := fun c d =>
    (x (0, 0) (0, 0) + x (1, 0) (1, 0)) / 2 +
    (if c = 1 ∧ d = 1 then
      (x (0, 1) (0, 1) + x (0, 1) (1, 1) + x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 2
    else 0) +
    (if c = d then
      (x (0, 1) (0, 1) - x (0, 1) (1, 1) - x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 4
    else 0)
  map_add' := by
    intro x y
    ext c d
    change (((x + y) (0, 0) (0, 0) + (x + y) (1, 0) (1, 0)) / 2 +
    (if c = 1 ∧ d = 1 then
      ((x + y) (0, 1) (0, 1) + (x + y) (0, 1) (1, 1) + (x + y) (1, 1) (0, 1) + (x +
      y) (1, 1) (1, 1)) / 2
    else 0) +
    (if c = d then
      ((x + y) (0, 1) (0, 1) - (x + y) (0, 1) (1, 1) - (x + y) (1, 1) (0, 1) + (x +
      y) (1, 1) (1, 1)) / 4
    else 0)) = ((x (0, 0) (0, 0) + x (1, 0) (1, 0)) / 2 +
    (if c = 1 ∧ d = 1 then
      (x (0, 1) (0, 1) + x (0, 1) (1, 1) + x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 2
    else 0) +
    (if c = d then
      (x (0, 1) (0, 1) - x (0, 1) (1, 1) - x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 4
    else 0)) + ((y (0, 0) (0, 0) + y (1, 0) (1, 0)) / 2 +
    (if c = 1 ∧ d = 1 then
      (y (0, 1) (0, 1) + y (0, 1) (1, 1) + y (1, 1) (0, 1) + y (1, 1) (1, 1)) / 2
    else 0) +
    (if c = d then
      (y (0, 1) (0, 1) - y (0, 1) (1, 1) - y (1, 1) (0, 1) + y (1, 1) (1, 1)) / 4
    else 0))
    simp only [Matrix.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro r x
    ext c d
    change (((r • x) (0, 0) (0, 0) + (r • x) (1, 0) (1, 0)) / 2 +
    (if c = 1 ∧ d = 1 then
      ((r • x) (0, 1) (0, 1) + (r • x) (0, 1) (1, 1) + (r • x) (1, 1) (0, 1) +
      (r • x) (1, 1) (1, 1)) / 2
    else 0) +
    (if c = d then
      ((r • x) (0, 1) (0, 1) - (r • x) (0, 1) (1, 1) - (r • x) (1, 1) (0, 1) +
      (r • x) (1, 1) (1, 1)) / 4
    else 0)) = r * ((x (0, 0) (0, 0) + x (1, 0) (1, 0)) / 2 +
    (if c = 1 ∧ d = 1 then
      (x (0, 1) (0, 1) + x (0, 1) (1, 1) + x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 2
    else 0) +
    (if c = d then
      (x (0, 1) (0, 1) - x (0, 1) (1, 1) - x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 4
    else 0))
    simp only [Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring

/-- The tensor power specified on all matrix units, including n = 0. -/
def tensorPow {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (φ : MatrixMap ι κ ℂ) (n : ℕ) : MatrixMap (Fin n → ι) (Fin n → κ) ℂ where
  toFun x := fun c d => ∑ a, ∑ b, x a b * ∏ k, φ (single (a k) (b k) 1) (c k) (d k)
  map_add' := by
    intro x y
    ext c d
    change (∑ a, ∑ b, (x + y) a b * ∏ k,
      φ (single (a k) (b k) 1) (c k) (d k)) =
      (∑ a, ∑ b, x a b * ∏ k, φ (single (a k) (b k) 1) (c k) (d k)) +
      (∑ a, ∑ b, y a b * ∏ k, φ (single (a k) (b k) 1) (c k) (d k))
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro r x
    ext c d
    change (∑ a, ∑ b, (r • x) a b * ∏ k,
      φ (single (a k) (b k) 1) (c k) (d k)) =
      r * (∑ a, ∑ b, x a b * ∏ k, φ (single (a k) (b k) 1) (c k) (d k))
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Stabilization by an input-sized reference, optimized over every density matrix. -/
def diamondNorm {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (φ : MatrixMap ι κ ℂ) : ℝ≥0∞ :=
  sSup {r | ∃ ρ : Matrix (ι × ι) (ι × ι) ℂ,
    ρ.PosSemidef ∧ ρ.trace = 1 ∧
      r = ENNReal.ofReal (traceNorm (kron φ (LinearMap.id : MatrixMap ι ι ℂ) ρ))}

/-- The source's equal-prior parallel discrimination error, in nonnegative extended reals. -/
def parallelError (n : ℕ) : ℝ≥0∞ :=
  (1 - diamondNorm (tensorPow harrowM n - tensorPow harrowMbar n) / 2) / 2

/-- Base-two error exponent; zero error has exponent +infinity at every positive n. -/
def exponent (n : ℕ) : EReal :=
  (((n : ℝ) * Real.log 2)⁻¹ : ℝ) * (-ENNReal.log (parallelError n))

/-- Salek--Hayashi--Winter's conjecture for the channels in Example 5. -/
def claim : Prop := Tendsto exponent atTop (𝓝 (1 : EReal))

private def input (n : ℕ) : Fin n → Fin 2 × Fin 2 := fun _ => (0, 1)

private def reference (n : ℕ) : Fin n → Fin 2 × Fin 2 := fun _ => (0, 0)

private def weight (n : ℕ) (c : Fin n → Fin 2) : ℝ :=
  ∏ k, if c k = 0 then (1 / 4 : ℝ) else 3 / 4

private def difference (n : ℕ) (c : (Fin n → Fin 2) × (Fin n → Fin 2 × Fin 2)) : ℝ :=
  if c.2 = reference n then (if c.1 = fun _ => 0 then 1 else 0) - weight n c.1 else 0

private theorem channel_values :
    harrowM (single (0, 1) (0, 1) 1) = diagonal (fun c => if c = 0 then 1 else 0) ∧
    harrowMbar (single (0, 1) (0, 1) 1) =
      diagonal (fun c => if c = 0 then 1 / 4 else 3 / 4) := by
  let x : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := single (0, 1) (0, 1) 1
  constructor
  · ext c d
    change (if c = d then
      (if c = 0 then x (0, 0) (0, 0) + x (1, 0) (1, 0) + x (0, 1) (0, 1) else 0) +
        x (1, 1) (1, 1) / 2
    else 0) = (diagonal (fun c => if c = 0 then 1 else 0)) c d
    dsimp only [x]
    fin_cases c <;> fin_cases d <;>
      norm_num [Matrix.single_apply, Matrix.diagonal_apply]
  · ext c d
    change ((x (0, 0) (0, 0) + x (1, 0) (1, 0)) / 2 +
    (if c = 1 ∧ d = 1 then
      (x (0, 1) (0, 1) + x (0, 1) (1, 1) + x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 2
    else 0) +
    (if c = d then
      (x (0, 1) (0, 1) - x (0, 1) (1, 1) - x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 4
    else 0)) = (diagonal (fun c => if c = 0 then 1 / 4 else 3 / 4)) c d
    dsimp only [x]
    fin_cases c <;> fin_cases d <;>
      norm_num [Matrix.single_apply, Matrix.diagonal_apply]

private theorem tensor_single {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (φ : MatrixMap ι κ ℂ) (n : ℕ) (a b : Fin n → ι) (c d : Fin n → κ) :
    tensorPow φ n (single a b 1) c d = ∏ k, φ (single (a k) (b k) 1) (c k) (d k) := by
  classical
  change (∑ x, ∑ y, single a b 1 x y * ∏ k,
    φ (single (x k) (y k) 1) (c k) (d k)) = _
  simp [Matrix.single_apply, ite_and]

private theorem tensor_diagonal {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (φ : MatrixMap ι κ ℂ) (n : ℕ) (a : Fin n → ι)
    (w : Fin n → κ → ℂ) (hw : ∀ k, φ (single (a k) (a k) 1) = diagonal (w k)) :
    tensorPow φ n (single a a 1) = diagonal (fun c => ∏ k, w k (c k)) := by
  classical
  ext c d
  rw [tensor_single]
  simp only [hw]
  by_cases h : c = d
  · subst d
    simp only [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (Matrix.diagonal_apply_ne _ hk)

private theorem tensor_values (n : ℕ) :
    (tensorPow harrowM n - tensorPow harrowMbar n) (single (input n) (input n) 1) =
      diagonal (fun c => (((if c = fun _ => 0 then 1 else 0) - weight n c : ℝ) : ℂ)) := by
  classical
  have hm := tensor_diagonal harrowM n (input n)
    (fun _ c => if c = 0 then 1 else 0) (fun _ => channel_values.1)
  have hb := tensor_diagonal harrowMbar n (input n)
    (fun _ c => if c = 0 then 1 / 4 else 3 / 4) (fun _ => channel_values.2)
  change tensorPow harrowM n _ - tensorPow harrowMbar n _ = _
  rw [hm, hb, Matrix.diagonal_sub]
  congr 1
  funext c
  have hp : (∏ k : Fin n, if c k = 0 then (1 : ℂ) else 0) =
      if c = fun _ => 0 then 1 else 0 := by
    simpa only [← funext_iff] using
      (Fintype.prod_boole (p := fun k : Fin n => c k = 0) (M₀ := ℂ))
  change (∏ k, if c k = 0 then (1 : ℂ) else 0) -
    (∏ k, if c k = 0 then (1 / 4 : ℂ) else 3 / 4) = _
  rw [hp]
  dsimp only [weight]
  simp only [Complex.ofReal_sub, Complex.ofReal_prod, apply_ite Complex.ofReal,
    Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_div, Complex.ofReal_ofNat]

private theorem input_density (n : ℕ) :
    (single (input n, reference n) (input n, reference n) (1 : ℂ)).PosSemidef ∧
    (single (input n, reference n) (input n, reference n) (1 : ℂ)).trace = 1 := by
  classical
  constructor
  · rw [← Matrix.diagonal_single]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    rw [Pi.single_apply]
    split_ifs <;> norm_num
  · exact Matrix.trace_single_eq_same _ _

private theorem amplified_output (n : ℕ) :
    kron (tensorPow harrowM n - tensorPow harrowMbar n) LinearMap.id
      (single (input n, reference n) (input n, reference n) 1) =
      diagonal (fun c => (difference n c : ℂ)) := by
  classical
  ext ⟨c, r⟩ ⟨d, s⟩
  rw [kron_def]
  simp only [LinearMap.id_apply, Matrix.single_apply, Prod.mk.injEq]
  simp only [ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const_zero]
  rw [tensor_values]
  simp only [Matrix.diagonal_apply]
  dsimp only [difference]
  by_cases hcd : c = d <;> by_cases hrs : r = s <;> by_cases hr : r = reference n
  all_goals simp_all [Complex.ofReal_sub, eq_comm]


private theorem weight_mass (n : ℕ) :
    (∑ c, weight n c) = 1 ∧ weight n (fun _ => 0) = (1 / 4 : ℝ) ^ n ∧
      (∀ c, 0 ≤ weight n c) ∧ (∀ c, weight n c ≤ 1) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (∑ c : Fin n → Fin 2, ∏ k, if c k = 0 then (1 / 4 : ℝ) else 3 / 4) = 1
    rw [← Fintype.prod_sum (fun (_ : Fin n) (j : Fin 2) =>
      if j = 0 then (1 / 4 : ℝ) else 3 / 4)]
    norm_num [Fin.sum_univ_two]
  · change (∏ k : Fin n, if (0 : Fin 2) = 0 then (1 / 4 : ℝ) else 3 / 4) = _
    simp only [ite_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro c
    apply Finset.prod_nonneg
    intro k hk
    split_ifs <;> norm_num
  · intro c
    apply Finset.prod_le_one₀
    · intro k hk
      split_ifs <;> norm_num
    · intro k hk
      split_ifs <;> norm_num

private theorem witness_norm (n : ℕ) :
    traceNorm (diagonal (fun c => (difference n c : ℂ))) =
      2 * (1 - (1 / 4 : ℝ) ^ n) := by
  classical
  obtain ⟨hs, hz, hp, hu⟩ := weight_mass n
  have ha (c : Fin n → Fin 2) :
      |(if c = fun _ => 0 then 1 else 0) - weight n c| =
        weight n c + if c = fun _ => 0 then 1 - 2 * weight n c else 0 := by
    by_cases hc : c = fun _ => 0
    · rw [ite_eq_left hc, ite_eq_left hc, abs_of_nonneg (sub_nonneg.mpr (hu c))]
      ring
    · rw [ite_eq_right hc, ite_eq_right hc, zero_sub, abs_neg, abs_of_nonneg (hp c), add_zero]
  rw [diagonal_norm]
  dsimp only [difference]
  rw [Fintype.sum_prod_type]
  simp only [apply_ite abs, abs_zero, Fintype.sum_ite_eq', ha,
    Finset.sum_add_distrib, hs, hz]
  ring

private theorem diamond_lower (n : ℕ) :
    ENNReal.ofReal (2 * (1 - (1 / 4 : ℝ) ^ n)) ≤
      diamondNorm (tensorPow harrowM n - tensorPow harrowMbar n) := by
  apply le_sSup
  refine ⟨single (input n, reference n) (input n, reference n) 1,
    (input_density n).1, (input_density n).2, ?_⟩
  rw [amplified_output, witness_norm]

private theorem error_upper (n : ℕ) : parallelError n ≤ (1 / 4 : ℝ≥0∞) ^ n / 2 := by
  have hcast : ENNReal.ofReal (2 * (1 - (1 / 4 : ℝ) ^ n)) =
      2 * (1 - (1 / 4 : ℝ≥0∞) ^ n) := by
    rw [ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hd := diamond_lower n
  rw [hcast] at hd
  have hs : 1 - (1 / 4 : ℝ≥0∞) ^ n ≤
      diamondNorm (tensorPow harrowM n - tensorPow harrowMbar n) / 2 := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
    rw [mul_comm]
    exact hd
  change (1 - _ / 2) / 2 ≤ _
  apply ENNReal.div_le_div_right
  exact (tsub_le_tsub_left hs 1).trans_eq
    (ENNReal.sub_sub_cancel (by norm_num) (pow_le_one₀ (by positivity) (by norm_num)))

private theorem exponent_lower (n : ℕ) (hn : 1 ≤ n) : (2 : EReal) ≤ exponent n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprob : parallelError n ≤ (1 / 4 : ℝ≥0∞) ^ n := by
    apply (error_upper n).trans
    simpa only [div_one] using
      (ENNReal.div_le_div (le_refl ((1 / 4 : ℝ≥0∞) ^ n))
        (show (1 : ℝ≥0∞) ≤ 2 by norm_num))
  have hquarter : (1 / 4 : ℝ≥0∞) ^ n = ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hlog : ENNReal.log ((1 / 4 : ℝ≥0∞) ^ n) =
      ((-2 * (n : ℝ) * Real.log 2 : ℝ) : EReal) := by
    rw [hquarter, ENNReal.log_ofReal_of_pos (by positivity), Real.log_pow]
    congr 1
    have hfour : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log 2 := Real.log_pow (2 : ℝ) 2
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, hfour]
    ring
  have hl := ENNReal.log_le_log hprob
  rw [hlog] at hl
  have hm := mul_le_mul_of_nonneg_left (EReal.neg_le_neg_iff.mpr hl)
    (show (0 : EReal) ≤ (((n : ℝ) * Real.log 2)⁻¹ : ℝ) by
      exact_mod_cast (inv_nonneg.mpr (mul_pos hnpos hlpos).le))
  rw [← EReal.coe_neg, ← EReal.coe_mul] at hm
  have he : ((n : ℝ) * Real.log 2)⁻¹ * -(-2 * (n : ℝ) * Real.log 2) = 2 := by
    field_simp
  rw [he] at hm
  exact hm

private theorem not_tendsto
    (h : ∀ n : ℕ, 1 ≤ n → (2 : EReal) ≤ exponent n) : ¬ claim := by
  intro hc
  have hf : ∀ᶠ n : ℕ in atTop, (2 : EReal) ≤ exponent n :=
    (eventually_ge_atTop 1).mono fun n hn => h n hn
  have hbad : (2 : EReal) ≤ 1 := ge_of_tendsto hc hf
  norm_num at hbad

theorem result : ¬ claim := not_tendsto exponent_lower

end D5.S3.Quantum.QuantumChannels.HarrowParallelChernoffExponentRefutation
