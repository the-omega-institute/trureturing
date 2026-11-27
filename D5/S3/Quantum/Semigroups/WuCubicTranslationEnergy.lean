/- GID: D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicTranslationEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact charge-weighted slope and centered degree gap for the Wu cubic translation energy. -/

import D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NoncommRing

/-! The energy along scalar translations of a complex Hermitian Wu direction. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy

open WuCubicOperatorBridge (D G Mat Occupation generator)
open WuCubicThermalBasis (Index basis basis_apply basis_repr charge coefficient degree direction
  expansion generator_direction generator_expansion generatorLinear generatorLinear_apply
  leftFamily localVector modular_direction modularEigenvalue rightFamily)
open WuCubicThermalOrthogonality (gibbsPairing gibbsPairing_eq_trace_G gibbsPairing_expansion
  directionNormSq localNormSq)
open private G_pow_six rootValue rootValue_pos from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

def base (r : ℝ) : Mat := G r ^ 2

def sandwich (r : ℝ) (A : Mat) : Mat := G r * A * G r

def translate (A : Mat) (t : ℝ) : Mat := t • (1 : Mat) + A

/-- The energy term of the literal Wu cubic operator deficit. -/
def cubicEnergy (r : ℝ) (X : Mat) : ℝ :=
  (9 / 8 : ℝ) * ((sandwich r X) ^ 2 * sandwich r (generator r X)).trace.re

/-- The ordinary trace variance of the sandwiched direction. -/
def V (r : ℝ) (A : Mat) : ℝ := (base r * (sandwich r A) ^ 2).trace.re

private theorem direction_zero (r : ℝ) : direction r (0, 0) = 1 := by
  have hlocal : localVector r 0 = 1 := rfl
  have hparity : ¬ ((0 : Fin 4) = 1 ∨ (0 : Fin 4) = 2) := by decide
  simp only [direction, leftFamily, rightFamily, Prod.fst, Prod.snd, hlocal,
    if_neg hparity, Matrix.one_kronecker_one, one_mul]

private theorem degree_zero (k : Index) : degree k = 0 ↔ k = (0, 0) := by
  obtain ⟨p, q⟩ := k
  fin_cases p <;> fin_cases q <;> decide

private theorem coefficient_generator {r : ℝ} (hr : 0 ≤ r) (A : Mat) (k : Index) :
    coefficient r (generator r A) k = (degree k : ℂ) * coefficient r A k := by
  rw [← basis_repr hr, generator_expansion hr A]
  simp_rw [← basis_apply (hr := hr)]
  exact congrFun ((basis r hr).repr_sum_self
    (fun j => (degree j : ℂ) * coefficient r A j)) k

private theorem trace_density {r : ℝ} (hr : 1 ≤ r) (A : Mat) :
    (D r * A).trace = coefficient r A (0, 0) := by
  have hr₀ : 0 ≤ r := zero_le_one.trans hr
  have hcoords (k : Index) :
      coefficient r (1 : Mat) k = if (0, 0) = k then 1 else 0 := by
    rw [← basis_repr hr₀, ← direction_zero r, ← basis_apply (hr := hr₀)]
    exact (basis r hr₀).repr_self_apply ((0, 0) : Index) k
  have hpair : gibbsPairing r 1 A = (D r * A).trace := by
    rw [gibbsPairing_eq_trace_G hr, Matrix.conjTranspose_one, mul_one, ← pow_add,
      G_pow_six hr]
  have hnorm : directionNormSq r (0, 0) = 1 := by
    change (1 : ℝ) * 1 = 1
    exact mul_one 1
  rw [← hpair, gibbsPairing_expansion hr₀, Finset.sum_eq_single ((0, 0) : Index)]
  · simp [hcoords, hnorm]
  · intro k _ hk
    simp [hcoords, Ne.symm hk]
  · simp

/-- The actual Gibbs density is stationary for the signed two-mode generator. -/
theorem stationary {r : ℝ} (hr : 1 ≤ r) (A : Mat) :
    (D r * generator r A).trace = 0 := by
  rw [trace_density hr, coefficient_generator (zero_le_one.trans hr)]
  simp [(degree_zero ((0, 0) : Index)).2 rfl]

private theorem generator_translate {r : ℝ} (hr : 1 ≤ r) (A : Mat) (t : ℝ) :
    generator r (translate A t) = generator r A := by
  have h₁ : generator r 1 = 0 := by
    rw [← direction_zero r, generator_direction (zero_le_one.trans hr)]
    simp [(degree_zero ((0, 0) : Index)).2 rfl]
  have hscalar : t • (1 : Mat) = (t : ℂ) • (1 : Mat) := by
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [translate, hscalar]
  change generatorLinear r (((t : ℂ) • (1 : Mat)) + A) = generatorLinear r A
  simp only [map_add, map_smul, generatorLinear_apply, h₁, smul_zero, zero_add]

private theorem sandwich_translate (r : ℝ) (A : Mat) (t : ℝ) :
    sandwich r (translate A t) = t • base r + sandwich r A := by
  simp only [sandwich, translate, base, pow_two, Matrix.mul_add, Matrix.add_mul,
    mul_one, mul_smul_comm, smul_mul_assoc]

private theorem trace_stationary_sandwich {r : ℝ} (hr : 1 ≤ r) (A : Mat) :
    (base r ^ 2 * sandwich r (generator r A)).trace = 0 := by
  calc
    _ = (G r ^ 5 * generator r A * G r).trace := by
      congr 1
      unfold base sandwich
      noncomm_ring
    _ = (D r * generator r A).trace := by
      rw [Matrix.trace_mul_cycle, ← pow_succ' (G r) 5, G_pow_six hr]
    _ = 0 := stationary hr A

private theorem real_trace_smul (t : ℝ) (M : Mat) :
    (t • M).trace.re = t * M.trace.re := by
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

/-- Stationarity makes the energy affine on the full scalar translate. -/
theorem cubicEnergy_translate {r : ℝ} (hr : 1 ≤ r) (A : Mat) (t : ℝ) :
    cubicEnergy r (translate A t) =
      t * ((9 / 8 : ℝ) * ((base r * sandwich r A + sandwich r A * base r) *
        sandwich r (generator r A)).trace.re) + cubicEnergy r A := by
  let B := base r
  let U := sandwich r A
  let W := sandwich r (generator r A)
  have hpoly : (t • B + U) ^ 2 * W =
      t ^ 2 • (B ^ 2 * W) + t • ((B * U + U * B) * W) + U ^ 2 * W := by
    simp only [pow_two, Matrix.mul_add, Matrix.add_mul, mul_smul_comm, smul_mul_assoc,
      smul_smul, smul_add]
    module
  unfold cubicEnergy
  rw [generator_translate hr, sandwich_translate]
  change (9 / 8 : ℝ) * ((t • B + U) ^ 2 * W).trace.re = _
  rw [hpoly]
  simp only [Matrix.trace_add, Complex.add_re, real_trace_smul,
    trace_stationary_sandwich hr A, Complex.zero_re, mul_zero, zero_add, B, U, W]
  ring

/-- Exact source energy derivative on a scalar translate, before degree decomposition. -/
theorem cubicEnergy_hasDerivAt_trace {r : ℝ} (hr : 1 ≤ r) (A : Mat) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cubicEnergy r (translate A s))
      ((9 / 8 : ℝ) * ((base r * sandwich r A + sandwich r A * base r) *
        sandwich r (generator r A)).trace.re) t := by
  simp_rw [cubicEnergy_translate hr]
  let slope := (9 / 8 : ℝ) * ((base r * sandwich r A + sandwich r A * base r) *
    sandwich r (generator r A)).trace.re
  simpa only [one_mul, add_zero, slope] using
    (hasDerivAt_mul_const (x := t) slope).add_const (cubicEnergy r A)


/-- Diagonal entries of the physical base matrix. -/
def baseEntry (r : ℝ) (i : Occupation) : ℝ := rootValue r i ^ 2

private theorem base_diagonal (r : ℝ) :
    base r = diagonal (fun i => (baseEntry r i : ℂ)) := by
  rw [base, G, Matrix.diagonal_pow]
  congr 1
  funext i
  rw [Pi.pow_apply, baseEntry, Complex.ofReal_pow]

private theorem baseEntry_pos {r : ℝ} (hr : 1 ≤ r) (i : Occupation) :
    0 < baseEntry r i := pow_pos (rootValue_pos hr i) 2

/-- The ordinary-trace variance pairing on complex directions. -/
def vPairing (r : ℝ) (X Y : Mat) : ℂ :=
  let U := (sandwich r X)ᴴ
  ((1 / 2 : ℂ) * ((base r * U + U * base r) * sandwich r Y).trace)

/-- Weight of the squared modulus of a matrix entry in the variance. -/
def pairWeight (r : ℝ) (i j : Occupation) : ℝ :=
  baseEntry r i * baseEntry r j * (baseEntry r i + baseEntry r j) / 2

private theorem vPairing_entries (r : ℝ) (X Y : Mat) :
    vPairing r X Y = ∑ i : Occupation, ∑ j : Occupation,
      (pairWeight r i j : ℂ) * (conj (X i j) * Y i j) := by
  dsimp only [vPairing]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.add_apply, base_diagonal r, sandwich, G, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def, map_mul,
    Complex.conj_ofReal, pairWeight, baseEntry, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

private theorem gibbsPairing_entries {r : ℝ} (hr : 1 ≤ r) (X Y : Mat) :
    gibbsPairing r X Y = ∑ i : Occupation, ∑ j : Occupation,
      ((rootValue r i ^ 3 * rootValue r j ^ 3 : ℝ) : ℂ) * (conj (X i j) * Y i j) := by
  rw [gibbsPairing_eq_trace_G hr, Matrix.trace_mul_comm]
  simp only [G, Matrix.diagonal_pow, Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.ofReal_mul, Complex.ofReal_pow, Pi.pow_apply]
  ring

/-- Ratio of ordinary variance to Gibbs-symmetric weight at an entry. -/
def entryMultiplier (r : ℝ) (i j : Occupation) : ℝ :=
  (baseEntry r i + baseEntry r j) / (2 * Real.sqrt (baseEntry r i * baseEntry r j))

/-- Value of the variance multiplier on signed charge `q`. -/
def chargeMultiplier (r : ℝ) (q : ℤ) : ℝ :=
  (r ^ q + 1) / (2 * Real.sqrt (r ^ q))

private theorem pairWeight_eq {r : ℝ} (hr : 1 ≤ r) (i j : Occupation) :
    pairWeight r i j = entryMultiplier r i j * (rootValue r i ^ 3 * rootValue r j ^ 3) := by
  have hi := rootValue_pos hr i
  have hj := rootValue_pos hr j
  unfold pairWeight entryMultiplier baseEntry
  rw [Real.sqrt_mul (sq_nonneg (rootValue r i)), Real.sqrt_sq hi.le, Real.sqrt_sq hj.le]
  field_simp [hi.ne', hj.ne'] <;> ring

private theorem baseEntry_of_charge {r : ℝ} (hr : 1 ≤ r) (k : Index) (i j : Occupation)
    (hij : direction r k i j ≠ 0) :
    baseEntry r i = r ^ charge k * baseEntry r j := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have he := congrArg (fun M : Mat => M i j) (modular_direction hr₀.ne' k)
  rw [← G_pow_six hr, G, Matrix.diagonal_pow] at he
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.pow_apply, Matrix.smul_apply,
    smul_eq_mul] at he
  have hpow : (rootValue r i : ℂ) ^ 6 =
      modularEigenvalue r (charge k) * (rootValue r j : ℂ) ^ 6 := by
    apply mul_right_cancel₀ hij
    calc
      _ = modularEigenvalue r (charge k) * (direction r k i j * (rootValue r j : ℂ) ^ 6) :=
        he
      _ = _ := by ring
  have hz (z : ℂ) : z ^ (3 : ℤ) = z ^ (3 : ℕ) := by norm_num
  have hmod : modularEigenvalue r (charge k) = (((r ^ charge k) ^ 3 : ℝ) : ℂ) := by
    unfold modularEigenvalue
    calc
      ((r : ℂ) ^ (3 : ℕ)) ^ charge k = ((r : ℂ) ^ (3 : ℤ)) ^ charge k := by rw [hz]
      _ = ((r : ℂ) ^ charge k) ^ (3 : ℤ) := by
        rw [← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm (3 : ℤ)]
      _ = _ := by rw [hz, Complex.ofReal_pow, Complex.ofReal_zpow]
  rw [hmod, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul] at hpow
  have hreal : rootValue r i ^ 6 = (r ^ charge k) ^ 3 * rootValue r j ^ 6 :=
    Complex.ofReal_injective hpow
  apply (pow_left_inj₀ (baseEntry_pos hr i).le
    (mul_pos (zpow_pos hr₀ _) (baseEntry_pos hr j)).le (by decide : (3 : ℕ) ≠ 0)).mp
  simpa only [baseEntry, mul_pow, ← pow_mul] using hreal

/-- The entry multiplier is constant on each occupied charge block of the signed basis. -/
theorem entryMultiplier_of_direction {r : ℝ} (hr : 1 ≤ r)
    (k : Index) (i j : Occupation) (hij : direction r k i j ≠ 0) :
    entryMultiplier r i j = chargeMultiplier r (charge k) := by
  have hp : 0 < r ^ charge k := zpow_pos (zero_lt_one.trans_le hr) _
  have hb := baseEntry_pos hr j
  unfold entryMultiplier chargeMultiplier
  rw [baseEntry_of_charge hr k i j hij,
    show r ^ charge k * baseEntry r j * baseEntry r j =
      r ^ charge k * baseEntry r j ^ 2 by ring,
    Real.sqrt_mul hp.le, Real.sqrt_sq hb.le]
  field_simp [hb.ne', (Real.sqrt_pos.2 hp).ne'] <;> ring

/-- The old Gibbs Gram diagonal survives the change of weight on each charge block. -/
theorem vPairing_expansion {r : ℝ} (hr : 1 ≤ r) (X Y : Mat) :
    vPairing r X Y = ∑ k : Index,
      conj (coefficient r X k) * coefficient r Y k *
        ((chargeMultiplier r (charge k) * directionNormSq r k : ℝ) : ℂ) := by
  have hr₀ : 0 ≤ r := zero_le_one.trans hr
  let c : Index → ℂ := fun k => (chargeMultiplier r (charge k) : ℂ) * coefficient r Y k
  let Z : Mat := ∑ k : Index, c k • direction r k
  have hz (i j : Occupation) : Z i j = (entryMultiplier r i j : ℂ) * Y i j := by
    have hY := congrArg (fun M : Mat => M i j) (expansion hr₀ Y)
    rw [← hY]
    simp only [Z, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, c]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : direction r k i j = 0
    · simp [hk]
    · rw [entryMultiplier_of_direction hr k i j hk]
      ring
  have hpair : vPairing r X Y = gibbsPairing r X Z := by
    rw [vPairing_entries, gibbsPairing_entries hr]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hz, pairWeight_eq hr, Complex.ofReal_mul]
    ring
  have hcoeff (k : Index) : coefficient r Z k = c k := by
    rw [← basis_repr hr₀]
    dsimp only [Z]
    simp_rw [← basis_apply (hr := hr₀)]
    exact congrFun ((basis r hr₀).repr_sum_self c) k
  rw [hpair, gibbsPairing_expansion hr₀]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hcoeff, Complex.ofReal_mul]
  dsimp only [c]
  ring

private theorem conj_mul_self (z : ℂ) : conj z * z = (Complex.normSq z : ℂ) := by
  rw [mul_comm, Complex.mul_conj]

private theorem sandwich_hermitian (r : ℝ) (A : Mat) (hA : A.IsHermitian) :
    (sandwich r A).IsHermitian := by
  have hG : (G r)ᴴ = G r := by
    rw [G, Matrix.diagonal_conjTranspose]
    exact congrArg diagonal (funext fun i => Complex.conj_ofReal (rootValue r i))
  change (sandwich r A)ᴴ = sandwich r A
  simp only [sandwich, Matrix.conjTranspose_mul, hG, hA.eq, Matrix.mul_assoc]

private theorem vPairing_self_re (r : ℝ) (A : Mat) (hA : A.IsHermitian) :
    (vPairing r A A).re = V r A := by
  let B := base r
  let U := sandwich r A
  have hU : Uᴴ = U := (sandwich_hermitian r A hA).eq
  have htrace : (U * B * U).trace = (B * (U * U)).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  change ((1 / 2 : ℂ) * ((B * Uᴴ + Uᴴ * B) * U).trace).re =
    (B * U ^ 2).trace.re
  rw [hU, Matrix.add_mul, Matrix.mul_assoc B U U, Matrix.trace_add, htrace]
  rw [show (1 / 2 : ℂ) * ((B * (U * U)).trace + (B * (U * U)).trace) =
    (B * (U * U)).trace by ring, pow_two]

private theorem vPairing_self_entries (r : ℝ) (A : Mat) :
    (vPairing r A A).re = ∑ i : Occupation, ∑ j : Occupation,
      pairWeight r i j * Complex.normSq (A i j) := by
  rw [vPairing_entries]
  simp only [conj_mul_self, ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]

/-- The entry formula for the same variance used in the energy bound. -/
theorem V_eq_entries (r : ℝ) (A : Mat) (hA : A.IsHermitian) :
    V r A = ∑ i : Occupation, ∑ j : Occupation,
      pairWeight r i j * Complex.normSq (A i j) := by
  rw [← vPairing_self_re r A hA, vPairing_self_entries]

/-- The variance mass of one actual complex basis component. -/
def vWeight (r : ℝ) (A : Mat) (k : Index) : ℝ :=
  Complex.normSq (coefficient r A k) * (chargeMultiplier r (charge k) * directionNormSq r k)

/-- The variance mass is the entry norm of the actual component, which may be complex. -/
theorem vWeight_eq_component {r : ℝ} (hr : 1 ≤ r) (A : Mat) (k : Index) :
    let Z := coefficient r A k • direction r k
    vWeight r A k = ∑ i : Occupation, ∑ j : Occupation,
      pairWeight r i j * Complex.normSq (Z i j) := by
  intro Z
  have hr₀ : 0 ≤ r := zero_le_one.trans hr
  have hz (l : Index) :
      coefficient r Z l = if k = l then coefficient r A k else 0 := by
    rw [← basis_repr hr₀]
    dsimp only [Z]
    rw [← basis_apply (hr := hr₀), map_smul]
    change coefficient r A k * (basis r hr₀).repr (basis r hr₀ k) l = _
    rw [(basis r hr₀).repr_self_apply k l]
    by_cases h : k = l <;> simp [h]
  rw [← vPairing_self_entries, vPairing_expansion hr, Complex.re_sum, Finset.sum_eq_single k]
  · simp only [hz, ite_true, conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re, vWeight]
  · intro l _ hl
    simp [hz, Ne.symm hl]
  · simp

private theorem vWeight_nonneg {r : ℝ} (hr : 1 ≤ r) (A : Mat) (k : Index) :
    0 ≤ vWeight r A k := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have ha : 0 ≤ WuCubicThermalBasis.a r := by unfold WuCubicThermalBasis.a; positivity
  have hb : 0 ≤ WuCubicThermalBasis.b r := by unfold WuCubicThermalBasis.b; positivity
  have hlocal (j : Fin 4) : 0 ≤ localNormSq r j := by
    fin_cases j
    · exact zero_le_one
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
    · exact mul_nonneg ha hb
  have hcharge : 0 ≤ chargeMultiplier r (charge k) := by
    unfold chargeMultiplier
    have hq := zpow_pos hr₀ (charge k)
    positivity
  exact mul_nonneg (Complex.normSq_nonneg _) (mul_nonneg hcharge
    (mul_nonneg (hlocal k.1) (hlocal k.2)))

private theorem vPairing_re_of_coeff {r : ℝ} (hr : 1 ≤ r) (X Y : Mat) (d : Index → ℝ)
    (hY : ∀ k, coefficient r Y k = (d k : ℂ) * coefficient r X k) :
    (vPairing r X Y).re = ∑ k : Index, d k * vWeight r X k := by
  rw [vPairing_expansion hr, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hY k]
  have h (c w : ℂ) :
      conj (coefficient r X k) * (c * coefficient r X k) * w =
        c * ((conj (coefficient r X k) * coefficient r X k) * w) := by ring
  rw [h, conj_mul_self]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re, vWeight]

/-- The variance is the sum of the sixteen complex quadratic weights. -/
theorem V_eq_sum {r : ℝ} (hr : 1 ≤ r) (A : Mat) (hA : A.IsHermitian) :
    V r A = ∑ k : Index, vWeight r A k := by
  rw [← vPairing_self_re r A hA]
  simpa only [one_mul] using vPairing_re_of_coeff hr A A (fun _ => 1) (by simp)

/-- The degree-one part of the same variance. -/
def V₁ (r : ℝ) (A : Mat) : ℝ :=
  ∑ k : Index, if degree k = 1 then vWeight r A k else 0

/-- The derivative of the literal Wu cubic energy in the signed Gibbs basis. -/
theorem cubicEnergy_hasDerivAt_degree {r : ℝ} (hr : 1 ≤ r) (A : Mat)
    (hA : A.IsHermitian) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cubicEnergy r (translate A s))
      ((9 / 4 : ℝ) * ∑ k : Index, (degree k : ℝ) * vWeight r A k) t := by
  have hpair := vPairing_re_of_coeff hr A (generator r A) (fun k => (degree k : ℝ))
    (fun k => by simpa only [Complex.ofReal_natCast] using
      coefficient_generator (zero_le_one.trans hr) A k)
  have hU := (sandwich_hermitian r A hA).eq
  have hhalf (z : ℂ) : ((1 / 2 : ℂ) * z).re = (1 / 2 : ℝ) * z.re := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by
      norm_num [Complex.ofReal_div, Complex.ofReal_ofNat], Complex.re_ofReal_mul]
  simp only [vPairing, hU, hhalf] at hpair
  have hslope :
      (9 / 8 : ℝ) * ((base r * sandwich r A + sandwich r A * base r) *
        sandwich r (generator r A)).trace.re =
      (9 / 4 : ℝ) * ∑ k : Index, (degree k : ℝ) * vWeight r A k := by
    linarith only [hpair]
  simpa only [hslope] using cubicEnergy_hasDerivAt_trace hr A t

/-- Centering kills degree zero, leaving degree one and degrees at least two. -/
theorem degree_sum_ge {r : ℝ} (hr : 1 ≤ r) (A : Mat) (hA : A.IsHermitian)
    (hcenter : (D r * A).trace = 0) :
    2 * V r A - V₁ r A ≤ ∑ k : Index, (degree k : ℝ) * vWeight r A k := by
  have hc : coefficient r A (0, 0) = 0 := (trace_density hr A).symm.trans hcenter
  have hpoint (k : Index) :
      2 * vWeight r A k - (if degree k = 1 then vWeight r A k else 0) ≤
        (degree k : ℝ) * vWeight r A k := by
    by_cases h0 : degree k = 0
    · have hw : vWeight r A k = 0 := by
        rw [(degree_zero k).mp h0]
        simp [vWeight, hc]
      simp [hw]
    by_cases h1 : degree k = 1
    · rw [if_pos h1, h1, Nat.cast_one, one_mul]
      linarith
    have hd : (2 : ℝ) ≤ (degree k : ℝ) := by
      exact_mod_cast (show 2 ≤ degree k by omega)
    simpa only [if_neg h1, sub_zero] using mul_le_mul_of_nonneg_right hd (vWeight_nonneg hr A k)
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Index)) => hpoint k)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← V_eq_sum hr A hA] at hsum
  exact hsum

/-- The lower bound uses the same ordinary trace variance and degree-one mass. -/
theorem cubicEnergy_deriv_ge {r : ℝ} (hr : 1 ≤ r) (A : Mat) (hA : A.IsHermitian)
    (hcenter : (D r * A).trace = 0) (t : ℝ) :
    (9 / 4 : ℝ) * (2 * V r A - V₁ r A) ≤
      deriv (fun s : ℝ => cubicEnergy r (translate A s)) t := by
  rw [(cubicEnergy_hasDerivAt_degree hr A hA t).deriv]
  exact mul_le_mul_of_nonneg_left (degree_sum_ge hr A hA hcenter) (by norm_num)

end D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
