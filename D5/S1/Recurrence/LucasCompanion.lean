/- GID: D5/S1/Recurrence/LucasCompanion
   generality: G
   mirror-B: D5/B/S1/Recurrence/LucasCompanion
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: Companion traces have matrix periods and a dyadic positive-zero criterion. -/

import D5.S1.Recurrence.LucasEvenDescent
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false

/-!
The companion sequence is the trace of the frozen Lucas companion at integer powers.
All results are general algebraic or arithmetic theorems, with no bounded enumeration,
checker, numeric reduction, or certified instance. The bilateral sequence uses unit `q`;
`lucasVInt` extends its natural-index traces to arbitrary integer `q`. The two-adic results
allow every even integer `p` and odd integer `q`, including `p = 0`.
-/

namespace D5.S1.Recurrence.LucasCompanion

open Matrix LucasEvenDescent

variable {R : Type*} [CommRing R]

/-- The companion Lucas sequence, including negative indices. -/
def lucasV (p : R) (q : Rˣ) (n : ℤ) : R :=
  Matrix.trace (↑(companion p q ^ n) : Matrix (Fin 2) (Fin 2) R)

private def powerMatrix (p : R) (q : Rˣ) (n : ℤ) : Matrix (Fin 2) (Fin 2) R :=
  ↑(companion p q ^ n)

private theorem power_add (p : R) (q : Rˣ) (a b : ℤ) :
    powerMatrix p q (a + b) = powerMatrix p q a * powerMatrix p q b := by
  simp only [powerMatrix, _root_.zpow_add, Units.val_mul]

/-- The shape of every integer companion power, exposed from the frozen unit definition. -/
theorem companion_power_shape (p : R) (q : Rˣ) (n : ℤ) :
    powerMatrix p q n =
      !![lucasU p q (n + 1), -(q : R) * lucasU p q n;
         lucasU p q n, lucasU p q (n + 1) - p * lucasU p q n] := by
  have hc : powerMatrix p q n * (companion p q : Matrix (Fin 2) (Fin 2) R) =
      (companion p q : Matrix (Fin 2) (Fin 2) R) * powerMatrix p q n := by
    exact congrArg Units.val (Commute.zpow_self (companion p q) n).eq
  have h01 : -(powerMatrix p q n 1 0 * (q : R)) = powerMatrix p q n 0 1 := by
    simpa [companion, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 1) hc
  have h10 : powerMatrix p q n 1 0 * p + powerMatrix p q n 1 1 =
      powerMatrix p q n 0 0 := by
    simpa [companion, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0) hc
  have hone : powerMatrix p q 1 = !![p, -(q : R); 1, 0] := by
    simp [powerMatrix, companion]
  have hs : powerMatrix p q (1 + n) 1 0 = powerMatrix p q n 0 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0) (power_add p q 1 n)
    rw [hone] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hb : lucasU p q (n + 1) = powerMatrix p q n 0 0 := by
    simpa only [lucasU, powerMatrix, add_comm] using hs
  ext i j
  fin_cases i <;> fin_cases j
  · exact hb.symm
  · change _ = -(q : R) * powerMatrix p q n 1 0
    simpa [mul_comm] using h01.symm
  · rfl
  · change powerMatrix p q n 1 1 = lucasU p q (n + 1) - p * powerMatrix p q n 1 0
    rw [hb]
    linear_combination h10

/-- The determinant at every integer index. -/
theorem companion_power_det (p : R) (q : Rˣ) (n : ℤ) :
    (↑(companion p q ^ n) : Matrix (Fin 2) (Fin 2) R).det = (↑(q ^ n) : R) := by
  have hd : Units.map (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) R →* R)
      (companion p q) = q := by
    ext
    simp [companion, Matrix.det_fin_two]
  have h := congrArg Units.val
    (map_zpow (Units.map (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) R →* R))
      (companion p q) n)
  rw [hd] at h
  exact h

/-- The bridge from the companion trace to the frozen Lucas sequence. -/
theorem lucasV_eq_lucasU (p : R) (q : Rˣ) (n : ℤ) :
    lucasV p q n = 2 * lucasU p q (n + 1) - p * lucasU p q n := by
  change Matrix.trace (powerMatrix p q n) = _
  rw [companion_power_shape, Matrix.trace_fin_two_of]
  ring

/-- Initial values and recurrence at all integer indices. -/
theorem lucasV_recurrence (p : R) (q : Rˣ) :
    lucasV p q 0 = 2 ∧ lucasV p q 1 = p ∧
      ∀ n : ℤ, lucasV p q (n + 2) = p * lucasV p q (n + 1) - ↑q * lucasV p q n := by
  refine ⟨by simp [lucasV, Matrix.trace_one],
    by simp [lucasV, companion, Matrix.trace_fin_two], ?_⟩
  intro n
  simp only [lucasV_eq_lucasU]
  have h₁ := (lucas_recurrence p q).2.2 n
  have h₂ := (lucas_recurrence p q).2.2 (n + 1)
  rw [show n + 2 + 1 = n + 1 + 2 by omega, h₂]
  rw [show n + 1 + 1 = n + 2 by omega, h₁]
  ring

/-- The companion determinant identity, obtained from the matrix determinant. -/
theorem lucasV_determinant_identity (p : R) (q : Rˣ) (n : ℤ) :
    lucasV p q (n + 1) ^ 2 - p * lucasV p q n * lucasV p q (n + 1) +
      ↑q * lucasV p q n ^ 2 = -(↑(q ^ n) : R) * (p ^ 2 - 4 * ↑q) := by
  have hd := companion_power_det p q n
  change (powerMatrix p q n).det = _ at hd
  rw [companion_power_shape, Matrix.det_fin_two_of] at hd
  simp only [lucasV_eq_lucasU]
  rw [show n + 1 + 1 = n + 2 by omega, (lucas_recurrence p q).2.2 n]
  linear_combination -(p ^ 2 - 4 * ↑q) * hd

/-- Cayley--Hamilton turns a zero companion trace into a scalar double power. -/
theorem companion_double_of_lucasV_zero (p : R) (q : Rˣ) (r : ℤ)
    (hr : lucasV p q r = 0) :
    (↑(companion p q ^ (2 * r)) : Matrix (Fin 2) (Fin 2) R) =
      -(↑(q ^ r) : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  nontriviality R
  have h := Matrix.aeval_self_charpoly (powerMatrix p q r)
  rw [Matrix.charpoly_fin_two] at h
  change Matrix.trace (powerMatrix p q r) = 0 at hr
  simp only [map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    hr, map_zero, zero_mul, sub_zero] at h
  have hd := companion_power_det p q r
  change (powerMatrix p q r).det = _ at hd
  rw [hd] at h
  change powerMatrix p q (2 * r) = _
  rw [two_mul, power_add, ← sq]
  simpa [Algebra.algebraMap_eq_smul_one] using eq_neg_of_add_eq_zero_left h

/-- The matrix period is its order in the unit group. -/
noncomputable def matrixPeriod (p : R) (q : Rˣ) : ℕ := orderOf (companion p q)

/-- A matrix power is one exactly at multiples of the matrix period. -/
theorem companion_zpow_eq_one_iff (p : R) (q : Rˣ) (k : ℤ) :
    companion p q ^ k = 1 ↔ (matrixPeriod p q : ℤ) ∣ k :=
  orderOf_dvd_iff_zpow_eq_one.symm

/-- The period is positive over a finite ring. -/
theorem matrixPeriod_pos [Finite R] (p : R) (q : Rˣ) : 0 < matrixPeriod p q :=
  orderOf_pos _

/-- In particular, reduction modulo any positive modulus has positive period. -/
theorem matrixPeriod_zmod_pos (m : ℕ) (hm : 0 < m) (p : ZMod m) (q : (ZMod m)ˣ) :
    0 < matrixPeriod p q := by
  letI : NeZero m := ⟨by omega⟩
  exact matrixPeriod_pos p q

/-- Matrix periodicity passes to the companion trace. -/
theorem lucasV_periodic (p : R) (q : Rˣ) :
    Function.Periodic (lucasV p q) (matrixPeriod p q : ℤ) := by
  intro n
  simp [lucasV, matrixPeriod, zpow_add, pow_orderOf_eq_one]

/-- The least period of the entire companion sequence under translation by one. -/
noncomputable def companionPeriod (p : R) (q : Rˣ) : ℕ :=
  Function.minimalPeriod (fun f : ℤ → R => fun n => f (n + 1)) (lucasV p q)

private theorem shift_iterate (f : ℤ → R) (k : ℕ) :
    (fun g : ℤ → R => fun n => g (n + 1))^[k] f = fun n => f (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext n
    simp [Nat.cast_add, add_assoc, add_comm, add_left_comm]

/-- The least companion period characterizes all natural translation periods. -/
theorem companionPeriod_dvd_iff (p : R) (q : Rˣ) (k : ℕ) :
    companionPeriod p q ∣ k ↔ Function.Periodic (lucasV p q) (k : ℤ) := by
  rw [companionPeriod, ← Function.isPeriodicPt_iff_minimalPeriod_dvd]
  change (fun g : ℤ → R => fun n => g (n + 1))^[k] (lucasV p q) = lucasV p q ↔ _
  rw [shift_iterate, funext_iff]
  rfl

/-- The least companion period divides the matrix period: `pi_V ∣ pi_U`. -/
theorem companionPeriod_dvd_matrixPeriod (p : R) (q : Rˣ) :
    companionPeriod p q ∣ matrixPeriod p q :=
  (companionPeriod_dvd_iff p q _).mpr (lucasV_periodic p q)

/-- The companion period is genuinely the least positive sequence period over a finite ring. -/
theorem companionPeriod_spec [Finite R] (p : R) (q : Rˣ) :
    0 < companionPeriod p q ∧
      Function.Periodic (lucasV p q) (companionPeriod p q : ℤ) ∧
      ∀ k : ℕ, 0 < k → Function.Periodic (lucasV p q) (k : ℤ) → companionPeriod p q ≤ k := by
  refine ⟨Nat.pos_of_dvd_of_pos (companionPeriod_dvd_matrixPeriod p q)
    (matrixPeriod_pos p q), (companionPeriod_dvd_iff p q _).mp (dvd_refl _), ?_⟩
  intro k hk h
  exact Nat.le_of_dvd hk ((companionPeriod_dvd_iff p q k).mpr h)

/-- If two is a unit and the companion trace has a zero, its least period is the matrix order. -/
theorem companionPeriod_eq_matrixPeriod_of_lucasV_zero (p : R) (q : Rˣ)
    (h2 : IsUnit (2 : R)) (hz : ∃ r : ℤ, lucasV p q r = 0) :
    companionPeriod p q = matrixPeriod p q := by
  obtain ⟨r, hr⟩ := hz
  let t : ℤ := companionPeriod p q
  let a := lucasU p q t
  let b := lucasU p q (t + 1) - 1
  let x := lucasU p q (r + 1)
  let y := lucasU p q r
  have ht : Function.Periodic (lucasV p q) t :=
    (companionPeriod_dvd_iff p q _).mp (dvd_refl _)
  have ht0 : 2 * b - p * a = 0 := by
    have h := ht 0
    rw [zero_add, (lucasV_recurrence p q).1, lucasV_eq_lucasU] at h
    dsimp [a, b]
    linear_combination h
  have hs : powerMatrix p q t = !![1 + b, -(q : R) * a; a, 1 - b] := by
    rw [companion_power_shape]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b] at * <;> linear_combination ht0
  have hr0 : 2 * x - p * y = 0 := by
    exact (lucasV_eq_lucasU p q r).symm.trans hr
  have hrs : powerMatrix p q r = !![x, -(q : R) * y; y, -x] := by
    rw [companion_power_shape]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [x, y] at * <;> linear_combination hr0
  -- Commutation supplies the first equation of the two-by-two system.
  have hc : powerMatrix p q t * powerMatrix p q r =
      powerMatrix p q r * powerMatrix p q t := by
    rw [← power_add, ← power_add, add_comm t r]
  have hax : a * x - b * y = 0 := by
    apply h2.mul_right_eq_zero.mp
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0) hc
    rw [hs, hrs] at h
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    linear_combination h
  -- Translation at the zero supplies the second equation.
  have hbx : b * x - (q : R) * a * y = 0 := by
    apply h2.mul_right_eq_zero.mp
    have h : Matrix.trace (powerMatrix p q r * powerMatrix p q t) = 0 := by
      rw [← power_add]
      exact (ht r).trans hr
    rw [hs, hrs] at h
    simp [Matrix.trace_fin_two] at h
    linear_combination h
  have hd : x ^ 2 - (q : R) * y ^ 2 = -(↑(q ^ r) : R) := by
    have h := companion_power_det p q r
    change (powerMatrix p q r).det = _ at h
    rw [hrs, Matrix.det_fin_two_of] at h
    linear_combination -h
  have hu : IsUnit (x ^ 2 - (q : R) * y ^ 2) := by
    rw [hd]
    exact (q ^ r).isUnit.neg
  have ha : a = 0 := by
    apply hu.mul_right_eq_zero.mp
    linear_combination x * hax + y * hbx
  have hb : b = 0 := by
    apply hu.mul_right_eq_zero.mp
    linear_combination (q : R) * y * hax + x * hbx
  have hpow : companion p q ^ companionPeriod p q = 1 := by
    apply Units.ext
    have h : powerMatrix p q t = 1 := by
      rw [hs, ha, hb]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    simpa only [powerMatrix, t, zpow_natCast, Units.val_one] using h
  exact Nat.dvd_antisymm (companionPeriod_dvd_matrixPeriod p q)
    (orderOf_dvd_iff_pow_eq_one.mpr hpow)

/-- Natural companion traces for arbitrary integer parameters, including nonunit `q`. -/
def lucasVInt (p q : ℤ) (n : ℕ) : ℤ :=
  Matrix.trace ((!![p, -q; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ n)

/-- The natural integer sequence agrees with the existing bilateral sequence for unit `q`. -/
theorem lucasVInt_eq_lucasV (p : ℤ) (q : ℤˣ) (n : ℕ) :
    lucasVInt p q n = lucasV p q n := by
  simp [lucasVInt, lucasV, zpow_natCast, Units.val_pow_eq_pow_val, companion]

/-- Initial values and recurrence without the unit restriction on the integer parameter `q`. -/
theorem lucasVInt_recurrence (p q : ℤ) :
    lucasVInt p q 0 = 2 ∧ lucasVInt p q 1 = p ∧
      ∀ n : ℕ, lucasVInt p q (n + 2) =
        p * lucasVInt p q (n + 1) - q * lucasVInt p q n := by
  refine ⟨by simp [lucasVInt, Matrix.trace_one],
    by simp [lucasVInt, Matrix.trace_fin_two], ?_⟩
  intro n
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![p, -q; 1, 0]
  have hs : A ^ 2 = p • A - q • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.intCast_apply]
    ring
  change Matrix.trace (A ^ (n + 2)) =
    p * Matrix.trace (A ^ (n + 1)) - q * Matrix.trace (A ^ n)
  rw [pow_add, hs, mul_sub, mul_smul_comm, mul_smul_comm, mul_one,
    ← pow_succ, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul]
  rfl

private theorem paired_congruence (p q m : ℤ) (hpp : m ∣ p * p) (j : ℕ) :
    lucasVInt p q (2 * j) ≡ 2 * (-q) ^ j [ZMOD m] ∧
      lucasVInt p q (2 * j + 1) ≡ (2 * (j : ℤ) + 1) * p * (-q) ^ j [ZMOD m] := by
  induction j with
  | zero => simp [(lucasVInt_recurrence p q).1, (lucasVInt_recurrence p q).2.1]
  | succ j ih =>
    have he := (ih.2.mul_left p).sub (ih.1.mul_left q)
    have he' : lucasVInt p q (2 * (j + 1)) ≡ 2 * (-q) ^ (j + 1) [ZMOD m] := by
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, (lucasVInt_recurrence p q).2.2]
      apply he.trans
      rw [Int.modEq_iff_dvd]
      rw [show 2 * (-q) ^ (j + 1) -
          (p * ((2 * (j : ℤ) + 1) * p * (-q) ^ j) - q * (2 * (-q) ^ j)) =
          (p * p) * (-((2 * (j : ℤ) + 1) * (-q) ^ j)) by rw [pow_succ]; ring]
      exact dvd_mul_of_dvd_left hpp _
    refine ⟨he', ?_⟩
    have ho := (he'.mul_left p).sub (ih.2.mul_left q)
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega,
      (lucasVInt_recurrence p q).2.2,
      show 2 * j + 1 + 1 = 2 * (j + 1) by omega]
    convert ho using 1
    push_cast
    simp only [pow_succ]
    ring

/-- The simultaneous two-adic congruences; oddness of `q` is only needed for exactness. -/
theorem lucasVInt_two_adic_congruences (p q : ℤ) (hp : Even p) (j : ℕ) :
    let t := padicValInt 2 p
    lucasVInt p q (2 * j) ≡ 2 * (-q) ^ j [ZMOD (2 : ℤ) ^ (t + 1)] ∧
      lucasVInt p q (2 * j + 1) ≡ (2 * (j : ℤ) + 1) * p * (-q) ^ j
        [ZMOD (2 : ℤ) ^ (t + 1)] := by
  have hd : (2 : ℤ) ^ (padicValInt 2 p + 1) ∣ 2 * p := by
    rw [pow_succ, mul_comm]
    exact mul_dvd_mul_left 2 (padicValInt_dvd p)
  exact paired_congruence p q _ (hd.trans (mul_dvd_mul_right hp.two_dvd p)) j

private theorem paired_factorization (p q : ℤ) (hp : Even p) (hq : Odd q) (j : ℕ) :
    (∃ a : ℤ, Odd a ∧ lucasVInt p q (2 * j) = 2 * a) ∧
      (∃ b : ℤ, Odd b ∧ lucasVInt p q (2 * j + 1) = p * b) := by
  obtain ⟨he, ho⟩ := paired_congruence p q (2 * p) (mul_dvd_mul_right hp.two_dvd p) j
  obtain ⟨a, ha⟩ := Int.modEq_iff_add_fac.mp he.symm
  obtain ⟨b, hb⟩ := Int.modEq_iff_add_fac.mp ho.symm
  have hqj : Odd ((-q) ^ j) := hq.neg.pow
  constructor
  · refine ⟨(-q) ^ j + p * a, hqj.add_even (hp.mul_right a), ?_⟩
    rw [ha]
    ring
  · refine ⟨(2 * (j : ℤ) + 1) * (-q) ^ j + 2 * b,
      ((odd_two_mul_add_one (j : ℤ)).mul hqj).add_even (even_two_mul b), ?_⟩
    rw [hb]
    ring

/-- Every even-indexed companion term has exact two-adic valuation one. -/
theorem lucasVInt_even_two_adic_valuation (p q : ℤ) (hp : Even p) (hq : Odd q)
    (j : ℕ) : padicValInt 2 (lucasVInt p q (2 * j)) = 1 := by
  obtain ⟨a, ha, he⟩ := (paired_factorization p q hp hq j).1
  have hav : padicValInt 2 a = 0 :=
    padicValInt.eq_zero_of_not_dvd
      (by simpa [← even_iff_two_dvd] using (Int.not_even_iff_odd.mpr ha))
  rw [he, padicValInt.mul (by norm_num)
    (by rintro rfl; exact Int.not_odd_zero ha), hav]
  exact padicValInt.self (by norm_num : 1 < (2 : ℕ))

/-- Odd-indexed terms have the valuation of `p`, including mathlib's convention at zero. -/
theorem lucasVInt_odd_two_adic_valuation (p q : ℤ) (hp : Even p) (hq : Odd q)
    (j : ℕ) : padicValInt 2 (lucasVInt p q (2 * j + 1)) = padicValInt 2 p := by
  obtain ⟨b, hb, ho⟩ := (paired_factorization p q hp hq j).2
  rw [ho]
  by_cases hp0 : p = 0
  · simp [hp0]
  · have hbv : padicValInt 2 b = 0 :=
      padicValInt.eq_zero_of_not_dvd
        (by simpa [← even_iff_two_dvd] using (Int.not_even_iff_odd.mpr hb))
    rw [padicValInt.mul hp0 (by rintro rfl; exact Int.not_odd_zero hb), hbv, add_zero]

/-- A positive companion zero modulo `2^v`, for `v ≥ 2`, exists exactly when `2^v ∣ p`. -/
theorem lucasVInt_exists_positive_zero_iff (p q : ℤ) (hp : Even p) (hq : Odd q)
    (v : ℕ) (hv : 2 ≤ v) :
    (∃ r : ℕ, 0 < r ∧ (2 : ℤ) ^ v ∣ lucasVInt p q r) ↔ (2 : ℤ) ^ v ∣ p := by
  constructor
  · rintro ⟨r, _, hd⟩
    have hevenodd : r = 2 * (r / 2) ∨ r = 2 * (r / 2) + 1 := by omega
    rcases hevenodd with he | ho
    · rw [he] at hd
      obtain ⟨a, ha, hea⟩ := (paired_factorization p q hp hq _).1
      have hn : lucasVInt p q (2 * (r / 2)) ≠ 0 := by
        rw [hea]
        exact mul_ne_zero (by norm_num) (by rintro rfl; exact Int.not_odd_zero ha)
      have ht := ((padicValInt_dvd_iff v _).mp hd).resolve_left hn
      rw [lucasVInt_even_two_adic_valuation p q hp hq] at ht
      omega
    · rw [ho] at hd
      rcases (padicValInt_dvd_iff v _).mp hd with hz | ht
      · obtain ⟨b, hb, hob⟩ := (paired_factorization p q hp hq (r / 2)).2
        rw [hob] at hz
        have hp0 := (mul_eq_zero.mp hz).resolve_right (by rintro rfl; exact Int.not_odd_zero hb)
        simp [hp0]
      · rw [lucasVInt_odd_two_adic_valuation p q hp hq] at ht
        exact (padicValInt_dvd_iff v p).mpr (Or.inr ht)
  · intro hd
    exact ⟨1, by omega, (lucasVInt_recurrence p q).2.1.symm ▸ hd⟩

/-- In the forward direction, index one already witnesses every positive-zero existence. -/
theorem lucasVInt_positive_zero_iff_index_one (p q : ℤ) (hp : Even p) (hq : Odd q)
    (v : ℕ) (hv : 2 ≤ v) :
    (∃ r : ℕ, 0 < r ∧ (2 : ℤ) ^ v ∣ lucasVInt p q r) ↔
      (2 : ℤ) ^ v ∣ lucasVInt p q 1 := by
  rw [lucasVInt_exists_positive_zero_iff p q hp hq v hv, (lucasVInt_recurrence p q).2.1]

private theorem unit_odd (q : ℤˣ) : Odd (q : ℤ) := by
  rcases Int.units_eq_one_or q with h | h <;> rw [h] <;> norm_num

/-- The simultaneous congruences for the original bilateral companion sequence. -/
theorem lucasV_two_adic_congruences (p : ℤ) (q : ℤˣ) (hp : Even p) (j : ℕ) :
    let t := padicValInt 2 p
    lucasV p q (2 * j) ≡ 2 * (-(q : ℤ)) ^ j [ZMOD (2 : ℤ) ^ (t + 1)] ∧
      lucasV p q (2 * j + 1) ≡ (2 * j + 1) * p * (-(q : ℤ)) ^ j
        [ZMOD (2 : ℤ) ^ (t + 1)] := by
  simpa only [lucasVInt_eq_lucasV, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one] using
    lucasVInt_two_adic_congruences p q hp j

/-- Exact valuation one at even natural indices in the bilateral sequence. -/
theorem lucasV_even_two_adic_valuation (p : ℤ) (q : ℤˣ) (hp : Even p) (j : ℕ) :
    padicValInt 2 (lucasV p q (2 * j)) = 1 := by
  simpa only [lucasVInt_eq_lucasV, Nat.cast_mul, Nat.cast_ofNat] using
    lucasVInt_even_two_adic_valuation p q hp (unit_odd q) j

/-- Exact valuation of `p` at odd natural indices in the bilateral sequence. -/
theorem lucasV_odd_two_adic_valuation (p : ℤ) (q : ℤˣ) (hp : Even p) (j : ℕ) :
    padicValInt 2 (lucasV p q (2 * j + 1)) = padicValInt 2 p := by
  simpa only [lucasVInt_eq_lucasV, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one] using
    lucasVInt_odd_two_adic_valuation p q hp (unit_odd q) j

/-- The integer divisibility criterion for the original companion sequence. -/
theorem lucasV_exists_positive_zero_iff (p : ℤ) (q : ℤˣ) (hp : Even p)
    (v : ℕ) (hv : 2 ≤ v) :
    (∃ r : ℕ, 0 < r ∧ (2 : ℤ) ^ v ∣ lucasV p q r) ↔ (2 : ℤ) ^ v ∣ p := by
  simpa only [lucasVInt_eq_lucasV] using
    lucasVInt_exists_positive_zero_iff p q hp (unit_odd q) v hv

/-- Any positive zero implies that index one itself is a zero. -/
theorem lucasV_positive_zero_iff_index_one (p : ℤ) (q : ℤˣ) (hp : Even p)
    (v : ℕ) (hv : 2 ≤ v) :
    (∃ r : ℕ, 0 < r ∧ (2 : ℤ) ^ v ∣ lucasV p q r) ↔ (2 : ℤ) ^ v ∣ lucasV p q 1 := by
  rw [lucasV_exists_positive_zero_iff p q hp v hv, (lucasV_recurrence p q).2.1]

#print axioms lucasV_determinant_identity
#print axioms companion_double_of_lucasV_zero
#print axioms companionPeriod_eq_matrixPeriod_of_lucasV_zero
#print axioms lucasVInt
#print axioms lucasVInt_eq_lucasV
#print axioms lucasVInt_recurrence
#print axioms lucasVInt_two_adic_congruences
#print axioms lucasVInt_even_two_adic_valuation
#print axioms lucasVInt_odd_two_adic_valuation
#print axioms lucasVInt_exists_positive_zero_iff
#print axioms lucasVInt_positive_zero_iff_index_one
#print axioms lucasV_two_adic_congruences
#print axioms lucasV_even_two_adic_valuation
#print axioms lucasV_odd_two_adic_valuation
#print axioms lucasV_exists_positive_zero_iff
#print axioms lucasV_positive_zero_iff_index_one

end D5.S1.Recurrence.LucasCompanion
