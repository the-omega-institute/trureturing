/- GID: D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral formal exponentials remain integral under diagonal powers of their ghosts. -/

/-
Paul D. Hanna's OEIS A156216, second comment (revision #3), concerns ordinary
formal power series; C(0) is ignored and no convergence or sign condition is imposed.
The source expressions define logarithmicInput and exponentialSum exactly;
IntegralSeries is reused from HannaLogarithmicPowerClosure.
admission_basis: open-problem-resolution (#21407; Proved)
No escape witness is claimed for admission.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21518
The public integral_input_ledger and divisor_ghost_gauss audit is unfinished: https://github.com/the-omega-institute/trureturing/issues/25058
Direct frozen dependencies are identified below by declaration, not module pins.
Published owners retain their original private baseline identities here;
their current public declaration identities require the canonical scope report.
The positive-coefficient series in the differential equations is the existing
HannaDiagonalDerivativeParity.step a 0.
F1: D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.IntegralSeries; sha256:63e70f464749e368856bfaa91133b0adfeda478327572310319dbf6077b632cb.
F2: D5/S1/Recurrence/Witt/PrimitiveEulerLedger.coeff_eulerFactor; sha256:0b3195d40655cd915a6d347f321e500e9f419eb6d1831fdd0bf95ce1a8c6fb8c.
F3: D5/S1/Recurrence/Witt/PrimitiveEulerLedger.eulerFactor; sha256:3ab1d32218cbc34fe76283777609dc9324e72c639cc6b1685b6a375f17d6be49.
F4: D5/S1/Recurrence/Witt/PrimitiveEulerLedger.ledgerProduct; sha256:68b89fc02ffe3c3af479529813227d49d2e1dc604fac5bfa8490c8991a2f9e03.
F5: D5/S1/Recurrence/Witt/PrimitiveEulerLedger.ledgerProduct_succ; sha256:60eacab0ceaa4bc54f7de5dcb9035b6b7ff6836284dcab2709646c26d1f43aa2 (original private identity).
F6: D5/S1/Recurrence/Witt/PrimitiveEulerLedger.Represents; sha256:bced3568aef9c4491770b4a83b7120b73e3f3a537b0b3867a40a4d756fa15f1d.
F7: D5/S1/Recurrence/Witt/PrimitiveEulerLedger.coeff_mul_eulerFactor_of_lt; sha256:43955db272d917e7b96898bed103e29f1065820607f4ac8e76c2081fc58179c0 (original private identity).
F8: D5/S1/Recurrence/Witt/PrimitiveEulerLedger.ledgerProduct_zero; sha256:389cf36a9c0f14ac7b786bae03f02abd169c3bab3be9666f9987a8b4312cb80e (private compiled constant: _private.D5.S1.Recurrence.Witt.PrimitiveEulerLedger.0.D5.S1.Recurrence.Witt.PrimitiveEulerLedger.ledgerProduct_zero).
F9: D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.derivative_map; sha256:836b4964698e27f0fa6c9a00406235db9bd0337b0cc06f4d72c592960ca72d58.
F10: D5/S1/Recurrence/Witt/PrimitiveEulerLedger.unique_primitive_euler_ledger; sha256:d165385fc17ed8b6f40903b9a54d714049fa6c69196e3426b06a84e1c43430a7.
F11: D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.step; sha256:44f442df1f9b494383f61c4d601cf82e1ebc1892be5527e924bf4075c5f3f3df (original private identity).
F12: D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.nonlinear; sha256:88041a98b81b1ebd8679244f5d7152556bf34c25e1514606789210d77d8ebec2 (private compiled constant: _private.D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.0.D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.nonlinear).
logarithmicInput: proof_shape: definition; escape_witness: none; consumers: exponentialSum, input_x_derivative, exponential_sum_constant, exponential_sum_equation, result; Direct frozen dependencies: none.
exponentialSum: proof_shape: definition; escape_witness: none; consumers: claim, exponential_sum_constant, exponential_sum_equation, integral_input_ledger, gauss_exponential_integral, result; Direct frozen dependencies: none.
claim: proof_shape: definition; escape_witness: none; consumers: result; Direct frozen dependencies: F1.
fermat_lift: proof_shape: bind-only; escape_witness: none; consumers: diagonal_congruence; Direct frozen dependencies: none.
diagonal_congruence: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none.
binomial_series_differential: proof_shape: bind-only; escape_witness: none; consumers: euler_factor_differential; Direct frozen dependencies: none.
euler_factor_as_subst: proof_shape: bind-only; escape_witness: none; consumers: euler_factor_differential; Direct frozen dependencies: F2, F3.
euler_factor_differential: proof_shape: bind-only; escape_witness: none; consumers: euler_factor_ghost_equation; Direct frozen dependencies: F2, F3.
geometricAt: proof_shape: definition; escape_witness: none; consumers: factorGhost, geometric_at_inverse, euler_factor_ghost_equation; Direct frozen dependencies: none.
factorGhost: proof_shape: definition; escape_witness: none; consumers: euler_factor_ghost_equation, coeff_factor_ghost, finiteGhost, ledger_product_differential, coeff_finite_ghost; Direct frozen dependencies: none.
geometric_at_inverse: proof_shape: bind-only; escape_witness: none; consumers: euler_factor_ghost_equation; Direct frozen dependencies: none.
euler_factor_ghost_equation: proof_shape: bind-only; escape_witness: none; consumers: ledger_product_differential; Direct frozen dependencies: F2, F3.
coeff_factor_ghost: proof_shape: bind-only; escape_witness: none; consumers: coeff_finite_ghost; Direct frozen dependencies: none.
finiteGhost: proof_shape: definition; escape_witness: none; consumers: ledger_product_differential, coeff_finite_ghost, euler_series_differential; Direct frozen dependencies: none.
divisorGhost: proof_shape: definition; escape_witness: none; consumers: ghostSeries, coeff_finite_ghost, divisor_ghost_gauss, gauss_has_ledger, integral_input_ledger, gauss_exponential_integral, result; Direct frozen dependencies: none.
ghostSeries: proof_shape: definition; escape_witness: none; consumers: coeff_finite_ghost, euler_series_differential, integral_input_ledger, gauss_exponential_integral; Direct frozen dependencies: none.
ledger_product_differential: proof_shape: bind-only; escape_witness: none; consumers: euler_series_differential; Direct frozen dependencies: F2, F3, F4, F5.
coeff_finite_ghost: proof_shape: bind-only; escape_witness: none; consumers: euler_series_differential; Direct frozen dependencies: none.
eulerSeries: proof_shape: definition; escape_witness: none; consumers: euler_series_represents, euler_series_differential, integral_input_ledger, gauss_exponential_integral; Direct frozen dependencies: F4.
euler_series_represents: proof_shape: bind-only; escape_witness: none; consumers: euler_series_differential, integral_input_ledger; Direct frozen dependencies: F6, F7, F3, F4, F5.
euler_series_differential: proof_shape: content; escape_witness: none; consumers: integral_input_ledger, gauss_exponential_integral; Direct frozen dependencies: F6, F2, F7, F3, F4, F5, F8.
prime_power_dvd_new_divisor: proof_shape: bind-only; escape_witness: none; consumers: divisor_ghost_gauss; Direct frozen dependencies: none.
GaussCondition: proof_shape: definition; escape_witness: none; consumers: divisor_ghost_gauss, gauss_moebius_divisible, gauss_has_ledger, gauss_exponential_integral, result; Direct frozen dependencies: none.
divisor_ghost_gauss: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none.
moebius_prime_pairing: proof_shape: bind-only; escape_witness: none; consumers: gauss_moebius_divisible; Direct frozen dependencies: none.
gauss_moebius_divisible: proof_shape: bind-only; escape_witness: none; consumers: gauss_has_ledger; Direct frozen dependencies: none.
input_x_derivative: proof_shape: bind-only; escape_witness: none; consumers: exponential_sum_equation; Direct frozen dependencies: F11.
exponential_sum_constant: proof_shape: bind-only; escape_witness: none; consumers: integral_input_ledger, gauss_exponential_integral; Direct frozen dependencies: none.
exponential_sum_equation: proof_shape: bind-only; escape_witness: none; consumers: integral_input_ledger, gauss_exponential_integral; Direct frozen dependencies: F11.
x_differential_unique: proof_shape: content; escape_witness: none; consumers: gauss_exponential_integral; Direct frozen dependencies: none.
gauss_has_ledger: proof_shape: bind-only; escape_witness: none; consumers: gauss_exponential_integral; Direct frozen dependencies: none.
integral_input_ledger: proof_shape: content; escape_witness: none; consumers: result; Direct frozen dependencies: F1, F9, F6, F2, F7, F3, F4, F5, F10, F8, F11, F12.
gauss_exponential_integral: proof_shape: content; escape_witness: none; consumers: result; Direct frozen dependencies: F1, F9, F6, F2, F7, F3, F4, F5, F8, F11, F12.
result: proof_shape: content; escape_witness: none; consumers: external settlement; Direct frozen dependencies: F1, F9, F6, F2, F7, F3, F4, F5, F10, F8, F11, F12.
-/

import D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
import Mathlib.LinearAlgebra.SModEq.Pow
import D5.S1.Recurrence.Witt.PrimitiveEulerLedger
import D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity


namespace D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

open PowerSeries
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)

noncomputable section

/-- The literal formal sum ∑_{n≥1} C(n) X^n/n, with zero constant coefficient. -/
def logarithmicInput {K : Type*} [Field K] [CharZero K] (C : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 0 else C n / (n : K)

/-- The literal formal exponential exp(∑_{n≥1} C(n) X^n/n). -/
def exponentialSum {K : Type*} [Field K] [CharZero K] (C : ℕ → K) : PowerSeries K :=
  (PowerSeries.exp K).subst (logarithmicInput C)

/-- Hanna's universal assertion; all fields, field structures, characteristic-zero
structures and sequences are quantified. IntegralSeries is the existing D5 owner. -/
def claim : Prop :=
  ∀ (K : Type) (_ : Field K) (_ : CharZero K) (C : ℕ → K),
    IntegralSeries (exponentialSum C) →
      IntegralSeries (exponentialSum (fun n => C n ^ n))

end

end D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

namespace D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

private theorem fermat_lift (p s : ℕ) (hp : p.Prime) (z : ℤ) :
    (p : ℤ) ^ (s + 1) ∣ z ^ (p ^ (s + 1)) - z ^ (p ^ s) := by
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hb : z ^ p ≡ z [SMOD I] := by
    rw [SModEq.sub_mem]
    exact Ideal.mem_span_singleton.mpr (Int.prime_dvd_pow_self_sub hp z)
  have hpI : (p : ℤ) ∈ I := Ideal.subset_span (by simp)
  have h := hb.pow_pow_add_one hpI s
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  simpa only [← pow_mul, ← pow_succ'] using h

private theorem diagonal_congruence (p s m : ℕ) (hp : p.Prime) (A B : ℤ)
    (h : (p : ℤ) ^ (s + 1) ∣ B - A) :
    (p : ℤ) ^ (s + 1) ∣ B ^ (m * p ^ (s + 1)) - A ^ (m * p ^ s) := by
  have hbase : B ^ (m * p ^ (s + 1)) ≡ A ^ (m * p ^ (s + 1))
      [ZMOD (p : ℤ) ^ (s + 1)] := (Int.modEq_iff_dvd.mpr ?_).pow _
  · have hf := fermat_lift p s hp (A ^ m)
    rw [← pow_mul, ← pow_mul] at hf
    have hexp : A ^ (m * p ^ (s + 1)) ≡ A ^ (m * p ^ s)
        [ZMOD (p : ℤ) ^ (s + 1)] := Int.modEq_iff_dvd.mpr (by simpa only [neg_sub] using dvd_neg.mpr hf)
    simpa only [neg_sub] using dvd_neg.mpr (Int.modEq_iff_dvd.mp (hbase.trans hexp))
  · simpa only [neg_sub] using dvd_neg.mpr h

end D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

namespace D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open PowerSeries
open D5.S1.Recurrence.Witt.PrimitiveEulerLedger
noncomputable section

private theorem binomial_series_differential (z : ℤ) :
    (1 + X : PowerSeries ℤ) * derivative (R := ℤ) (binomialSeries ℤ z) =
      C z * binomialSeries ℤ z := by
  have hd : derivative (R := ℤ) (binomialSeries ℤ z) =
      C z * binomialSeries ℤ (z - 1) := by
    ext k
    rw [coeff_derivative, coeff_C_mul]
    have h := Ring.choose_smul_choose z (n := k + 1) (k := 1) (by omega)
    simpa [binomialSeries_coeff, zsmul_eq_mul, mul_comm] using h
  rw [hd]
  have hz : binomialSeries ℤ z = binomialSeries ℤ (z - 1) * (1 + X) := by
    have hb1 : binomialSeries ℤ (1 : ℤ) = 1 + X := by
      simpa using (binomialSeries_nat (R := ℤ) (A := ℤ) 1)
    simpa only [sub_add_cancel, hb1] using (binomialSeries_add (A := ℤ) (z - 1) (1 : ℤ))
  rw [hz]
  ring

private theorem euler_factor_as_subst (n : ℕ) (hn : n ≠ 0) (c : ℤ) :
    eulerFactor n c = (binomialSeries ℤ (-c)).subst (-(X ^ n : PowerSeries ℤ)) := by
  have he : eulerFactor n c =
      (rescale (-1 : ℤ) (binomialSeries ℤ (-c))).subst (X ^ n) := by
    ext k
    simp [coeff_eulerFactor, coeff_subst_X_pow hn, coeff_rescale]
  rw [he, rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X' (-1 : ℤ)) (HasSubst.X_pow hn)]
  congr 1
  rw [← coe_substAlgHom (R := ℤ) (HasSubst.X_pow (R := ℤ) hn),
    map_smul, substAlgHom_X]
  ext k
  simp

private theorem euler_factor_differential (n : ℕ) (hn : n ≠ 0) (c : ℤ) :
    (1 - X ^ n) * (X * derivative (R := ℤ) (eulerFactor n c)) =
      C ((n : ℤ) * c) * X ^ n * eulerFactor n c := by
  have hg : HasSubst (-(X ^ n : PowerSeries ℤ)) :=
    HasSubst.of_constantCoeff_zero (by
      change constantCoeff (-(X ^ n : PowerSeries ℤ)) = 0
      simp [hn])
  have h := congrArg (PowerSeries.substAlgHom hg)
    (binomial_series_differential (-c))
  simp only [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom, subst_C] at h
  rw [← euler_factor_as_subst n hn c] at h
  have hd : derivative (R := ℤ) (eulerFactor n c) =
      (derivative (R := ℤ) (binomialSeries ℤ (-c))).subst (-(X ^ n)) *
        (-C (n : ℤ) * X ^ (n - 1)) := by
    rw [euler_factor_as_subst n hn c, derivative_subst hg]
    simp [smul_eq_mul]
  rw [hd]
  have hx : (X : PowerSeries ℤ) * X ^ (n - 1) = X ^ n := by
    exact mul_pow_sub_one hn X
  change (1 - X ^ n) * (derivative (R := ℤ) (binomialSeries ℤ (-c))).subst (-(X ^ n)) = C (-c) * eulerFactor n c at h
  simp only [map_neg] at h
  rw [map_mul]
  linear_combination (-C (n : ℤ) * X ^ n) * h -
    C (n : ℤ) * (1 - X ^ n) *
      (derivative (R := ℤ) (binomialSeries ℤ (-c))).subst (-(X ^ n)) * hx

end
end D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

namespace D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open PowerSeries Finset
open D5.S1.Recurrence.Witt.PrimitiveEulerLedger
noncomputable section

private def geometricAt (n : ℕ) : PowerSeries ℤ :=
  (invUnitsSub (1 : ℤˣ)).subst (X ^ n)

private def factorGhost (n : ℕ) (c : ℤ) : PowerSeries ℤ :=
  C ((n : ℤ) * c) * (geometricAt n - 1)

private theorem geometric_at_inverse (n : ℕ) (hn : n ≠ 0) :
    geometricAt n * (1 - X ^ n) = 1 := by
  let φ : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ :=
    PowerSeries.substAlgHom (R := ℤ) (HasSubst.X_pow (R := ℤ) hn)
  have hi : invUnitsSub (1 : ℤˣ) * (1 - X) = 1 := by
    simpa using (invUnitsSub_mul_sub (1 : ℤˣ))
  have h := congrArg φ hi
  simp only [map_mul, map_sub, map_one] at h
  dsimp only [φ] at h
  rw [substAlgHom_X] at h
  simpa only [geometricAt, coe_substAlgHom] using h

private theorem euler_factor_ghost_equation (n : ℕ) (hn : n ≠ 0) (c : ℤ) :
    X * derivative (R := ℤ) (eulerFactor n c) = factorGhost n c * eulerFactor n c := by
  have h := geometric_at_inverse n hn
  have hX : geometricAt n * X ^ n = geometricAt n - 1 := by linear_combination -h
  calc
    X * derivative (R := ℤ) (eulerFactor n c) =
        geometricAt n * ((1 - X ^ n) * (X * derivative (R := ℤ) (eulerFactor n c))) := by
      rw [← mul_assoc, h, one_mul]
    _ = geometricAt n * (C ((n : ℤ) * c) * X ^ n * eulerFactor n c) := by
      rw [euler_factor_differential n hn c]
    _ = C ((n : ℤ) * c) * (geometricAt n * X ^ n) * eulerFactor n c := by ring
    _ = factorGhost n c * eulerFactor n c := by rw [hX]; rfl

private theorem coeff_factor_ghost (n : ℕ) (hn : n ≠ 0) (c : ℤ) (k : ℕ) :
    coeff k (factorGhost n c) =
      if k = 0 then 0 else if n ∣ k then (n : ℤ) * c else 0 := by
  simp only [factorGhost, geometricAt, invUnitsSub, coeff_C_mul, map_sub,
    coeff_subst_X_pow hn, coeff_mk, coeff_one]
  split_ifs <;> simp_all

private def finiteGhost (b : ℕ → ℤ) (N : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ range N, factorGhost (i + 1) (b i)

def divisorGhost (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ) * b d

private def ghostSeries (b : ℕ → ℤ) : PowerSeries ℤ :=
  mk (divisorGhost (fun d => b (d - 1)))

private theorem ledger_product_differential (b : ℕ → ℤ) (N : ℕ) :
    X * derivative (R := ℤ) (ledgerProduct b N) =
      finiteGhost b N * ledgerProduct b N := by
  induction N with
  | zero => simp [ledgerProduct, finiteGhost]
  | succ N ih =>
    rw [ledgerProduct_succ]
    have hg : finiteGhost b (N + 1) = finiteGhost b N + factorGhost (N + 1) (b N) := by
      simp [finiteGhost, sum_range_succ]
    rw [hg, Derivation.leibniz]
    simp only [smul_eq_mul]
    linear_combination eulerFactor (N + 1) (b N) * ih +
      ledgerProduct b N * euler_factor_ghost_equation (N + 1) (by omega) (b N)

private theorem coeff_finite_ghost (b : ℕ → ℤ) (N k : ℕ) (hk : k ≤ N) :
    coeff k (finiteGhost b N) = coeff k (ghostSeries b) := by
  classical
  simp only [finiteGhost, map_sum, coeff_factor_ghost _ (Nat.succ_ne_zero _) _ _,
    ghostSeries, divisorGhost, coeff_mk]
  by_cases hk0 : k = 0
  · simp [hk0]
  simp only [ite_eq_right hk0]
  rw [← sum_filter]
  apply sum_bij (fun i _ => i + 1)
  · intro i hi
    rcases mem_filter.mp hi with ⟨hi, hd⟩
    exact Nat.mem_divisors.mpr ⟨hd, hk0⟩
  · intro i hi j hj h
    omega
  · intro d hd
    have hdp := Nat.pos_of_mem_divisors hd
    have hdle := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (Nat.dvd_of_mem_divisors hd)
    refine ⟨d - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, by omega⟩
    simpa [Nat.sub_add_cancel hdp] using Nat.dvd_of_mem_divisors hd
  · intro i hi
    simp

private def eulerSeries (b : ℕ → ℤ) : PowerSeries ℤ :=
  mk fun n => coeff n (ledgerProduct b n)

private theorem euler_series_represents (b : ℕ → ℤ) : Represents (eulerSeries b) b := by
  intro N k hk
  change coeff k (ledgerProduct b N) = coeff k (mk fun n => coeff n (ledgerProduct b n))
  rw [coeff_mk]
  induction N with
  | zero =>
    have hk0 : k = 0 := by exact Nat.eq_zero_of_le_zero hk
    subst k
    rfl
  | succ N ih =>
    by_cases hkle : k ≤ N
    · rw [ledgerProduct_succ, coeff_mul_eulerFactor_of_lt _ N k _ (by omega)]
      exact ih hkle
    · have hkN : k = N + 1 := by omega
      subst k
      rfl

private theorem euler_series_differential (b : ℕ → ℤ) :
    X * derivative (R := ℤ) (eulerSeries b) = ghostSeries b * eulerSeries b := by
  ext k
  have hrep := euler_series_represents b
  have h := congrArg (coeff k) (ledger_product_differential b k)
  have hl : coeff k (X * derivative (R := ℤ) (eulerSeries b)) =
      coeff k (X * derivative (R := ℤ) (ledgerProduct b k)) := by
    cases k with
    | zero => simp
    | succ k => rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative,
        hrep (k + 1) (k + 1) le_rfl]
  rw [hl, h, coeff_mul, coeff_mul]
  apply sum_congr rfl
  intro ij hij
  have hijsum := Finset.mem_antidiagonal.mp hij
  rw [coeff_finite_ghost b k ij.1 (by omega), hrep k ij.2 (by omega)]

end
end D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

namespace D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open Finset
noncomputable section

private theorem prime_power_dvd_new_divisor (p s m d : ℕ) (hp : p.Prime) (hm : 0 < m)
    (hd : d ∣ m * p ^ (s + 1)) (hnot : ¬ d ∣ m * p ^ s) : p ^ (s + 1) ∣ d := by
  have hbig0 : m * p ^ (s + 1) ≠ 0 := mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)
  have hsmall0 : m * p ^ s ≠ 0 := mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hbig0 hd
  by_contra hpd
  have hdp : d.factorization p ≤ s := by
    have h := hp.pow_dvd_iff_le_factorization hd0 (k := s + 1)
    omega
  apply hnot
  apply (Nat.factorization_prime_le_iff_dvd hd0 hsmall0).mp
  intro q hq
  by_cases hqp : q = p
  · subst q
    simp only [Nat.factorization_mul hm.ne' (pow_ne_zero _ hp.ne_zero),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      hp.factorization_self]
    omega
  · have h := (Nat.factorization_le_iff_dvd hd0 hbig0).mpr hd
    have hqle := Finsupp.le_def.mp h q
    simpa [Nat.factorization_mul hm.ne' (pow_ne_zero _ hp.ne_zero),
      Nat.factorization_pow, hp.factorization, hqp] using hqle

def GaussCondition (a : ℕ → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ s m : ℕ, 0 < m →
    (p : ℤ) ^ (s + 1) ∣ a (m * p ^ (s + 1)) - a (m * p ^ s)

theorem divisor_ghost_gauss (b : ℕ → ℤ) : GaussCondition (divisorGhost b) := by
  intro p hp s m hm
  have hn0 : m * p ^ (s + 1) ≠ 0 := mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)
  have hk0 : m * p ^ s ≠ 0 := mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)
  have hkn : m * p ^ s ∣ m * p ^ (s + 1) := by
    rw [pow_succ, ← mul_assoc]
    exact dvd_mul_right _ _
  have hsub := Nat.divisors_subset_of_dvd hn0 hkn
  unfold divisorGhost
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro d hd
  rcases mem_sdiff.mp hd with ⟨hdn, hdk⟩
  have hdiv : d ∣ m * p ^ (s + 1) := Nat.dvd_of_mem_divisors hdn
  have hnot : ¬ d ∣ m * p ^ s := by simpa [Nat.mem_divisors, hk0] using hdk
  have hpd := prime_power_dvd_new_divisor p s m d hp hm hdiv hnot
  have hpd' : (p : ℤ) ^ (s + 1) ∣ (d : ℤ) := by exact Int.ofNat_dvd_right.mpr hpd
  exact dvd_mul_of_dvd_left hpd' _

private theorem moebius_prime_pairing (a : ℕ → ℤ) (n p : ℕ) (hn : n ≠ 0)
    (hp : p.Prime) (hpn : p ∣ n) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d * a (n / d)) =
      ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d),
        ArithmeticFunction.moebius d * (a (n / d) - a (n / (p * d))) := by
  classical
  let S := n.divisors.filter (fun d => ¬ p ∣ d)
  let T := n.divisors.filter (fun d => p ∣ d)
  have hmul (d : ℕ) (hd : d ∈ S) : p * d ∣ n := by
    have hcop := hp.coprime_iff_not_dvd.mpr (mem_filter.mp hd).2
    exact hcop.mul_dvd_of_dvd_of_dvd hpn (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
  have hmu (d : ℕ) (hd : d ∈ S) :
      ArithmeticFunction.moebius (p * d) = - ArithmeticFunction.moebius d := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr (mem_filter.mp hd).2),
      ArithmeticFunction.moebius_apply_prime hp, neg_one_mul]
  have hbij :
      (∑ d ∈ S, ArithmeticFunction.moebius (p * d) * a (n / (p * d))) =
        ∑ d ∈ T, ArithmeticFunction.moebius d * a (n / d) := by
    apply Finset.sum_bij_ne_zero (fun d _ _ => p * d)
    · intro d hd _
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hmul d hd, hn⟩, dvd_mul_right p d⟩
    · intro d hd hdn e he hen hde
      exact Nat.eq_of_mul_eq_mul_left hp.pos hde
    · intro d hd hne
      have hpd : p ∣ d := (mem_filter.mp hd).2
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
      have hmu0 : ArithmeticFunction.moebius d ≠ 0 := (mul_ne_zero_iff.mp hne).1
      have hsq := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu0
      have hpq : ¬ p ∣ d / p := by
        intro hq
        have hppd : p * p ∣ d := by
          exact (Nat.dvd_div_iff_mul_dvd hpd).mp hq
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) hppd
      have hqS : d / p ∈ S := mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hpd).trans hdn, hn⟩, hpq⟩
      refine ⟨d / p, hqS, ?_, Nat.mul_div_cancel' hpd⟩
      simpa [Nat.mul_div_cancel' hpd] using hne
    · intro d hd hne
      rfl
  have hsplit :
      (∑ d ∈ n.divisors, ArithmeticFunction.moebius d * a (n / d)) =
        (∑ d ∈ S, ArithmeticFunction.moebius d * a (n / d)) +
        ∑ d ∈ T, ArithmeticFunction.moebius d * a (n / d) := by
    exact Eq.symm
      (sum_filter_not_add_sum_filter n.divisors (Dvd.dvd p)
        (fun d => ArithmeticFunction.moebius d * a (n / d)))
  rw [hsplit, ← hbij, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [hmu d hd]
  ring

private theorem gauss_moebius_divisible (a : ℕ → ℤ) (ha : GaussCondition a)
    (n : ℕ) (hn : 0 < n) :
    (n : ℤ) ∣ ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * a (n / d) := by
  rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p r hp hpr
  cases r with
  | zero => simp
  | succ s =>
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs, Nat.cast_pow]
    have hpn : p ∣ n := (dvd_pow_self p (Nat.succ_ne_zero s)).trans hpr
    rw [moebius_prime_pairing a n p hn.ne' hp hpn]
    apply Finset.dvd_sum
    intro d hd
    rcases mem_filter.mp hd with ⟨hdn, hpd⟩
    have hdn' := Nat.dvd_of_mem_divisors hdn
    have hquot : p ^ (s + 1) ∣ n / d := by
      have hcop := (hp.coprime_iff_not_dvd.mpr hpd).pow_left (s + 1)
      apply hcop.dvd_of_dvd_mul_right
      simpa [Nat.div_mul_cancel hdn'] using hpr
    obtain ⟨m, hm⟩ := hquot
    have hmpos : 0 < m := by
      have hqpos := Nat.div_pos (Nat.le_of_dvd hn hdn') (Nat.pos_of_mem_divisors hdn)
      rw [hm] at hqpos
      exact Nat.pos_of_mul_pos_left hqpos
    have hdiv : n / (p * d) = m * p ^ s := by
      rw [mul_comm p d, ← Nat.div_div_eq_div_mul, hm, pow_succ]
      have he : p ^ s * p * m = (m * p ^ s) * p := by exact Eq.symm (mul_rotate m (p ^ s) p)
      rw [he, Nat.mul_div_cancel _ hp.pos]
    have hlocal := ha p hp s m hmpos
    rw [mul_comm m (p ^ (s + 1)), ← hm, ← hdiv] at hlocal
    exact dvd_mul_of_dvd_right hlocal _

end
end D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

namespace D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open PowerSeries Finset
noncomputable section

private theorem input_x_derivative {K : Type*} [Field K] [CharZero K] (a : ℕ → K) :
    X * derivative (R := K) (logarithmicInput a) = (D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.step a 0) := by
  change X * derivative (R := K) (logarithmicInput a) =
    mk (fun n => if n = 0 then 0 else a n -
      coeff n ((X * derivative (R := K) 0) * 0 * invOfUnit (1 - C (n : K) * 0) 1))
  simp only [mul_zero, zero_mul, map_zero, sub_zero]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative]
    simp [logarithmicInput, Nat.cast_add_one_ne_zero]

private theorem exponential_sum_constant {K : Type*} [Field K] [CharZero K] (a : ℕ → K) :
    constantCoeff (exponentialSum a) = 1 := by
  change MvPowerSeries.constantCoeff ((exp K).subst (logarithmicInput a)) = 1
  rw [constantCoeff_subst_of_constantCoeff_zero]
  · exact constantCoeff_exp
  · change constantCoeff (logarithmicInput a) = 0
    simp [logarithmicInput, ← coeff_zero_eq_constantCoeff_apply]

private theorem exponential_sum_equation {K : Type*} [Field K] [CharZero K] (a : ℕ → K) :
    X * derivative (R := K) (exponentialSum a) = (D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.step a 0) * exponentialSum a := by
  have hh : HasSubst (logarithmicInput a) := HasSubst.of_constantCoeff_zero
    (by
      change constantCoeff (logarithmicInput a) = 0
      simp [logarithmicInput, ← coeff_zero_eq_constantCoeff_apply])
  rw [exponentialSum, derivative_subst hh, derivative_exp]
  change X * ((exp K).subst (logarithmicInput a) * derivative (R := K) (logarithmicInput a)) = _
  calc
    _ = (X * derivative (R := K) (logarithmicInput a)) * exponentialSum a := by
      unfold exponentialSum
      ring
    _ = _ := by rw [input_x_derivative]; rfl

private theorem x_differential_unique {K : Type*} [Field K] [CharZero K]
    (L f g : PowerSeries K) (hL : constantCoeff L = 0)
    (hc : constantCoeff f = constantCoeff g)
    (hf : X * derivative (R := K) f = L * f)
    (hg : X * derivative (R := K) g = L * g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff] using hc
    | succ n =>
      have hp : coeff (n + 1) (L * f) = coeff (n + 1) (L * g) := by
        rw [coeff_mul, coeff_mul]
        apply sum_congr rfl
        intro ij hij
        have hijsum := Finset.mem_antidiagonal.mp hij
        by_cases hi0 : ij.1 = 0
        · simp [hi0, coeff_zero_eq_constantCoeff, hL]
        · rw [ih ij.2 (by omega)]
      have h1 := congrArg (coeff (n + 1)) hf
      have h2 := congrArg (coeff (n + 1)) hg
      rw [coeff_succ_X_mul, coeff_derivative] at h1 h2
      have hz : (n : K) + 1 ≠ 0 := by exact Nat.cast_add_one_ne_zero n
      exact mul_right_cancel₀ hz (h1.trans (hp.trans h2.symm))

end
end D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

namespace D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open PowerSeries Finset
open D5.S1.Recurrence.Witt.PrimitiveEulerLedger
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)
noncomputable section

private theorem gauss_has_ledger (a : ℕ → ℤ) (ha : GaussCondition a) :
    ∃ b : ℕ → ℤ, ∀ n : ℕ, 0 < n → divisorGhost b n = a n := by
  let b : ℕ → ℤ := fun n =>
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d * a (n / d)) / (n : ℤ)
  refine ⟨b, ?_⟩
  apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
  intro n hn
  simp only [Int.cast_id]
  rw [Nat.sum_divisorsAntidiagonal (fun i j => ArithmeticFunction.moebius i * a j)]
  exact (Int.mul_ediv_cancel' (gauss_moebius_divisible a ha n hn)).symm

theorem integral_input_ledger {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (ha : IntegralSeries (exponentialSum a)) :
    ∃ b : ℕ → ℤ, ∀ n : ℕ, 0 < n → a n = (divisorGhost b n : K) := by
  classical
  choose w hw using ha
  let f : PowerSeries ℤ := mk w
  have hmap : f.map (Int.castRingHom K) = exponentialSum a := by
    ext n
    simpa [f, coeff_map] using (hw n).symm
  have hf0 : constantCoeff f = 1 := by
    have h := congrArg (constantCoeff (R := K)) hmap
    change ((constantCoeff f : ℤ) : K) = constantCoeff (exponentialSum a) at h
    rw [exponential_sum_constant] at h
    exact_mod_cast h
  obtain ⟨b, hrep, _⟩ := unique_primitive_euler_ledger f hf0
  have he : f = eulerSeries b := by
    ext n
    exact (hrep n n le_rfl).symm.trans (euler_series_represents b n n le_rfl)
  have hEmap : (eulerSeries b).map (Int.castRingHom K) = exponentialSum a := by
    rwa [← he]
  have hdiff := congrArg (PowerSeries.map (Int.castRingHom K)) (euler_series_differential b)
  simp only [map_mul, map_X, D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.derivative_map, hEmap] at hdiff
  have hU : IsUnit (exponentialSum a) := isUnit_iff_constantCoeff.mpr
    (by rw [exponential_sum_constant]; exact isUnit_one)
  have hg : (D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.step a 0) = (ghostSeries b).map (Int.castRingHom K) :=
    hU.mul_right_cancel ((exponential_sum_equation a).symm.trans hdiff)
  refine ⟨fun d => b (d - 1), ?_⟩
  intro n hn
  have h := congrArg (coeff n) hg
  simp only [D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.step, coeff_mk] at h
  change (if n = 0 then 0 else a n -
    coeff n ((X * derivative (R := K) 0) * 0 * invOfUnit (1 - C (n : K) * 0) 1)) = _ at h
  simpa [hn.ne', coeff_map, ghostSeries, divisorGhost] using h

private theorem gauss_exponential_integral {K : Type*} [Field K] [CharZero K]
    (a : ℕ → ℤ) (ha : GaussCondition a) :
    IntegralSeries (exponentialSum (fun n => (a n : K))) := by
  classical
  obtain ⟨b, hb⟩ := gauss_has_ledger a ha
  let c : ℕ → ℤ := fun n => b (n + 1)
  let f : PowerSeries K := (eulerSeries c).map (Int.castRingHom K)
  have hghost : (ghostSeries c).map (Int.castRingHom K) =
      (D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.step (fun n => (a n : K)) 0) := by
    change (ghostSeries c).map (Int.castRingHom K) =
      mk (fun n => if n = 0 then 0 else (a n : K) -
        coeff n ((X * derivative (R := K) 0) * 0 * invOfUnit (1 - C (n : K) * 0) 1))
    simp only [mul_zero, zero_mul, map_zero, sub_zero]
    ext n
    by_cases hn : n = 0
    · subst n
      simp [ghostSeries, divisorGhost]
    · have hs : (∑ d ∈ n.divisors, (d : ℤ) * c (d - 1)) = a n := by
        change (∑ d ∈ n.divisors, (d : ℤ) * b (d - 1 + 1)) = a n
        rw [← hb n (Nat.pos_of_ne_zero hn)]
        unfold divisorGhost
        apply sum_congr rfl
        intro d hd
        rw [Nat.sub_add_cancel (Nat.pos_of_mem_divisors hd)]
      simpa [ghostSeries, divisorGhost, hn, coeff_map] using
        congrArg (Int.castRingHom K) hs
  have hf : X * derivative (R := K) f = (D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.step (fun n => (a n : K)) 0) * f := by
    have h := congrArg (PowerSeries.map (Int.castRingHom K)) (euler_series_differential c)
    simpa only [map_mul, map_X, D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.derivative_map, hghost] using h
  have hf0 : constantCoeff f = 1 := by
    simp [f, eulerSeries, ← coeff_zero_eq_constantCoeff_apply, ledgerProduct]
  have he : f = exponentialSum (fun n => (a n : K)) := by
    apply x_differential_unique ((D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.step (fun n => (a n : K)) 0)) f
      (exponentialSum (fun n => (a n : K)))
    · simp [D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.step, ← coeff_zero_eq_constantCoeff_apply]
    · rw [hf0, exponential_sum_constant]
    · exact hf
    · exact exponential_sum_equation _
  intro n
  refine ⟨coeff n (eulerSeries c), ?_⟩
  rw [← he]
  exact coeff_map _ _ _

theorem result : D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.claim := by
  intro K _ _ a ha
  obtain ⟨b, hb⟩ := integral_input_ledger a ha
  let z : ℕ → ℤ := divisorGhost b
  have hz : GaussCondition z := divisor_ghost_gauss b
  have hdiag : GaussCondition (fun n => z n ^ n) := by
    intro p hp s m hm
    exact diagonal_congruence p s m hp (z (m * p ^ s)) (z (m * p ^ (s + 1)))
      (hz p hp s m hm)
  have hout := gauss_exponential_integral (K := K) (fun n => z n ^ n) hdiag
  have harg : logarithmicInput (fun n => a n ^ n) =
      logarithmicInput (fun n => ((z n ^ n : ℤ) : K)) := by
    ext n
    by_cases hn : n = 0
    · simp [logarithmicInput, hn]
    · simp only [logarithmicInput, coeff_mk, ite_eq_right hn]
      rw [hb n (Nat.pos_of_ne_zero hn)]
      simp [z]
  have he : exponentialSum (fun n => a n ^ n) =
      exponentialSum (fun n => ((z n ^ n : ℤ) : K)) := by
    unfold exponentialSum
    rw [harg]
  rw [he]
  exact hout

end
end D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
