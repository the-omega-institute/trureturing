/- GID: D5/S3/Arith/LocalDold/UnimodularObstruction
   generality: G
   mirror-B: D5/B/S3/Arith/LocalDold/UnimodularObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A controlled p-adic period shell forces unbounded prime-index local-Dold failures. -/

import Mathlib

/-! Prime-index local Dold obstructions for integral unimodular coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ArithmeticFunction.Moebius

namespace D5.S3.Arith.LocalDold.UnimodularObstruction

noncomputable section

def pPart (p n : ℕ) : ℕ := p ^ padicValNat p n

abbrev GLInt (d : ℕ) := Matrix.GeneralLinearGroup (Fin d) ℤ

private def reduceGL {d p : ℕ} (A : GLInt d) :
    Matrix.GeneralLinearGroup (Fin d) (ZMod p) :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod p)) A

private theorem gl_power_mod_eq_one {d p T : ℕ} (A : GLInt d)
    (hpow : (reduceGL A : Matrix.GeneralLinearGroup (Fin d) (ZMod p)) ^ T = 1) :
    ∀ i j : Fin d, (p : ℤ) ∣ (A.val ^ T) i j - (1 : Matrix (Fin d) (Fin d) ℤ) i j := by
  intro i j
  have hentry := congrArg (fun X : Matrix.GeneralLinearGroup (Fin d) (ZMod p) => X i j)
    hpow
  have hentry' : ((A.val ^ T) i j : ZMod p) =
      ((1 : Matrix (Fin d) (Fin d) ℤ) i j : ZMod p) := by
    rw [Units.val_pow_eq_pow_val] at hentry
    rw [show (reduceGL A).val = A.val.map (Int.castRingHom (ZMod p)) by
      ext i' j'
      exact Matrix.GeneralLinearGroup.map_apply (Int.castRingHom (ZMod p)) i' j' A]
      at hentry
    rw [← Matrix.map_pow (A.val) (Int.castRingHom (ZMod p)) T] at hentry
    change ((A.val ^ T).map (Int.castRingHom (ZMod p))) i j =
      (1 : Matrix (Fin d) (Fin d) (ZMod p)) i j at hentry
    simp only [Matrix.map_apply, Matrix.one_apply] at hentry
    change ((A.val ^ T) i j : ZMod p) = (if i = j then 1 else 0) at hentry
    simpa only [Matrix.one_apply, Int.cast_ite, Int.cast_one, Int.cast_zero] using hentry
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hentry'
  rcases hentry' with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  calc
    (A.val ^ T) i j - (1 : Matrix (Fin d) (Fin d) ℤ) i j =
        -((1 : Matrix (Fin d) (Fin d) ℤ) i j - (A.val ^ T) i j) := by ring
    _ = -((p : ℤ) * c) := by rw [hc]
    _ = (p : ℤ) * (-c) := by ring

private theorem matrix_eq_one_add_smul_of_dvd {d m : ℕ}
    {X : Matrix (Fin d) (Fin d) ℤ}
    (h : ∀ i j, (m : ℤ) ∣ X i j - (1 : Matrix (Fin d) (Fin d) ℤ) i j) :
    ∃ C, X = 1 + (m : ℤ) • C := by
  let c : Fin d → Fin d → ℤ := fun i j => Classical.choose (h i j)
  have hc : ∀ i j, X i j - (1 : Matrix (Fin d) (Fin d) ℤ) i j =
      (m : ℤ) * c i j := by
    intro i j
    exact Classical.choose_spec (h i j)
  refine ⟨c, ?_⟩
  ext i j
  have hij : X i j = (1 : Matrix (Fin d) (Fin d) ℤ) i j + (m : ℤ) * c i j := by
    have hz := hc i j
    calc
      X i j = (X i j - (1 : Matrix (Fin d) (Fin d) ℤ) i j) +
          (1 : Matrix (Fin d) (Fin d) ℤ) i j := by ring
      _ = (m : ℤ) * c i j + (1 : Matrix (Fin d) (Fin d) ℤ) i j := by rw [hz]
      _ = (1 : Matrix (Fin d) (Fin d) ℤ) i j + (m : ℤ) * c i j := by ring
  change X i j = (1 : Matrix (Fin d) (Fin d) ℤ) i j + (m : ℤ) • c i j
  simpa [smul_eq_mul] using hij

private theorem exists_mod_p_period {d p : ℕ} (A : GLInt d) (hp : p.Prime) :
    ∃ T, 0 < T ∧ (reduceGL A : Matrix.GeneralLinearGroup (Fin d) (ZMod p)) ^ T = 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (isOfFinOrder_of_finite (reduceGL A)).exists_pow_eq_one

private theorem weak_period_lift {d p T : ℕ} (A : GLInt d)
    (hmod : ∀ i j, (p : ℤ) ∣ (A.val ^ T) i j -
      (1 : Matrix (Fin d) (Fin d) ℤ) i j) :
    ∀ j, ∃ C, A.val ^ (T * p ^ j) =
      1 + (p : ℤ) ^ (j + 1) • C := by
  intro j
  obtain ⟨C, hC⟩ := matrix_eq_one_add_smul_of_dvd hmod
  let I : Ideal (Polynomial ℤ) := Ideal.span {(p : Polynomial ℤ)}
  have hpI : (p : Polynomial ℤ) ∈ I := Ideal.mem_span_singleton_self _
  have hx : (1 + (p : Polynomial ℤ) * Polynomial.X) ≡ 1 [SMOD I] := by
    apply SModEq.sub_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨Polynomial.X, by ring⟩
  have hs := SModEq.pow_pow_add_one hpI hx j
  rw [SModEq.sub_mem, one_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hs
  obtain ⟨Q, hQ⟩ := hs
  refine ⟨Polynomial.aeval C Q, ?_⟩
  have hpoly : (1 + (p : Polynomial ℤ) * Polynomial.X) ^ (p ^ j) =
      1 + (p : Polynomial ℤ) ^ (j + 1) * Q := by
    rw [← hQ]
    ring
  have hm := congrArg (Polynomial.aeval C) hpoly
  simp only [map_pow, map_add, map_one, map_mul, map_natCast, Polynomial.aeval_X] at hm
  rw [pow_mul, hC]
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using hm

private theorem matrix_vec_modEq_of_eq {d m : ℕ}
    {X Y C : Matrix (Fin d) (Fin d) ℤ} (h : X = Y + (m : ℤ) • C)
    (v : Fin d → ℤ) (i : Fin d) :
    (X.mulVec v) i ≡ (Y.mulVec v) i [ZMOD (m : ℤ)] := by
  rw [h, Matrix.add_mulVec, Matrix.smul_mulVec]
  apply Int.modEq_iff_dvd.mpr
  simp [Matrix.add_apply, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

private theorem coordinate_weak_period {d p T : ℕ}
    (A : GLInt d) (v : Fin d → ℤ) (i : Fin d)
    (hweak : ∀ j, ∃ C, A.val ^ (T * p ^ j) =
      1 + (p : ℤ) ^ (j + 1) • C)
    (a : ℕ → ℕ)
    (hcoord : ∀ n, 0 < n → (a n : ℤ) = ((A.val ^ n).mulVec v) i) :
    ∀ j n, 0 < n → (a (n + T * p ^ j) : ℤ) ≡ a n
      [ZMOD ((p : ℤ) ^ (j + 1))] := by
  intro j n
  intro hn
  obtain ⟨C, hC⟩ := hweak j
  have hstate : A.val ^ (n + T * p ^ j) =
      A.val ^ n + (p : ℤ) ^ (j + 1) • (A.val ^ n * C) := by
    rw [pow_add, hC, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hmod := matrix_vec_modEq_of_eq
    (m := p ^ (j + 1)) (X := A.val ^ (n + T * p ^ j))
    (Y := A.val ^ n) (C := A.val ^ n * C)
    (by simpa [Nat.cast_pow] using hstate) v i
  rw [hcoord _ (by omega), hcoord n hn]
  simpa [Nat.cast_pow] using hmod

private theorem int_dvd_sub_of_modEq {m x y : ℕ}
    (h : (x : ℤ) ≡ y [ZMOD (m : ℤ)]) : (m : ℤ) ∣ (x : ℤ) - y := by
  rcases h.dvd with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  calc
    (x : ℤ) - y = -((y : ℤ) - x) := by ring
    _ = -((m : ℤ) * c) := by rw [hc]
    _ = (m : ℤ) * (-c) := by ring

private theorem modEq_add_multiple {a : ℕ → ℕ} {m M r k : ℕ}
    (hr : 0 < r)
    (hstep : ∀ n, 0 < n → (a (n + M) : ℤ) ≡ a n [ZMOD (m : ℤ)]) :
    (a (r + k * M) : ℤ) ≡ a r [ZMOD (m : ℤ)] := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs := hstep (r + k * M)
        (by omega)
      have hindex : r + (k + 1) * M = (r + k * M) + M := by
        rw [Nat.succ_mul]
        omega
      rw [hindex]
      exact hs.trans ih

private theorem padicValNat_exact_of_dvd_not_dvd {p n e : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (hd : p ^ e ∣ n) (hnd : ¬ p ^ (e + 1) ∣ n) :
    padicValNat p n = e := by
  have hle : e ≤ padicValNat p n := (padicValNat_dvd_iff_le hn).mp hd
  have hnot : ¬ e + 1 ≤ padicValNat p n := by
    intro h
    exact hnd ((padicValNat_dvd_iff_le hn).mpr h)
  omega

private theorem prime_index_moebius_sum (a : ℕ → ℕ) (p q : ℕ) (hq : q.Prime) :
    ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) =
      (pPart p (a q) : ℤ) - pPart p (a 1) := by
  rw [show q = q ^ 1 by simp, Nat.divisors_prime_pow hq 1]
  norm_num [Finset.sum_range_succ]
  rw [ArithmeticFunction.moebius_apply_prime hq, Nat.div_self hq.pos,
    ArithmeticFunction.moebius_apply_one]
  ring

private theorem unbounded_prime_index_obstruction
    (a : ℕ → ℕ)
    (hpos : ∀ n, 0 < n → 0 < a n)
    (ha1 : a 1 = 1)
    (p : ℕ) (hp : p.Prime)
    (T : ℕ) (hT : 0 < T)
    (hbase : (a (p * T - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ)])
    (hlift : ∀ j n, 0 < n → (a (n + T * p ^ j) : ℤ) ≡ a n
      [ZMOD ((p : ℤ) ^ (j + 1))]) :
    ∀ H : ℕ, ∃ q > H, q.Prime ∧
      0 < ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) ∧
      (∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)) < q ∧
      ¬ (q : ℤ) ∣ ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro H
  let r := p * T - 1
  let e := padicValNat p (a r)
  let M := T * p ^ e
  have hrpos : 0 < r := by
    dsimp [r]
    have hmul : T < p * T := by
      simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hT
    have hpT : 1 < p * T := lt_of_le_of_lt (Nat.one_le_iff_ne_zero.mpr hT.ne') hmul
    exact Nat.sub_pos_of_lt hpT
  have harpos : 0 < a r := hpos r hrpos
  have hbase' : (p : ℤ) ∣ (a r : ℤ) := by
    simpa using int_dvd_sub_of_modEq hbase
  have hpdiv : p ∣ a r := by
    exact_mod_cast hbase'
  have hepos : 1 ≤ e := by
    dsimp [e]
    have hd : p ^ 1 ∣ a r := by simpa using hpdiv
    have hle := (padicValNat_dvd_iff_le harpos.ne').mp hd
    omega
  have hrltM : r < M := by
    have hppow : p ≤ p ^ e := by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos hepos
    have hmul := Nat.mul_le_mul_left T hppow
    dsimp [r, M]
    exact lt_of_lt_of_le (Nat.sub_lt (Nat.mul_pos hp.pos hT) (by decide))
      (by simpa [Nat.mul_comm] using hmul)
  have hbasepow : (p : ℤ) ^ e ∣ (a r : ℤ) := by
    exact_mod_cast ((padicValNat_dvd_iff_le harpos.ne').mpr (le_rfl : e ≤ e))
  have hnotbasepow : ¬ (p : ℤ) ^ (e + 1) ∣ (a r : ℤ) := by
    intro h
    have hnat : p ^ (padicValNat p (a r) + 1) ∣ a r := by
      exact_mod_cast h
    exact (pow_succ_padicValNat_not_dvd (p := p) harpos.ne') hnat
  have hcoprime : r.Coprime M := by
    dsimp [M, r]
    have hcop : (p * T - 1).Coprime (p * T) := by
      have h' := (Nat.coprime_add_self_right (m := p * T - 1) (n := 1)).2
        (Nat.coprime_one_right (p * T - 1))
      convert h' using 1 <;> omega
    have hpr : p.Coprime (p * T - 1) := by
      have h' : (T * p).Coprime (p * T - 1) := by simpa [Nat.mul_comm] using hcop.symm
      exact h'.coprime_mul_left
    have hpow : (p * T - 1).Coprime (p ^ e) := (hpr.symm.pow_right e)
    have hTcop : (p * T - 1).Coprime T := hcop.symm.coprime_mul_left.symm
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hTcop.mul_right hpow
  obtain ⟨q, hqH, hq, hqmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max H (max r (p ^ e - 1)))
      (q := M) (a := r) (Nat.ne_of_gt (lt_trans hrpos hrltM)) hcoprime
  have hqr : r ≤ q := by omega
  obtain ⟨k, hk⟩ : ∃ k, q = r + k * M := by
    have hqmod' := (Nat.modEq_iff_dvd' hqr).mp hqmod.symm
    rcases hqmod' with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    exact (Nat.eq_add_of_sub_eq hqr hk).trans (by ac_rfl)
  have hclass : (a q : ℤ) ≡ a r [ZMOD ((p : ℤ) ^ (e + 1))] := by
    rw [hk]
    exact modEq_add_multiple (m := p ^ (e + 1)) (M := M) (r := r) (k := k) hrpos
      (fun n => by
        intro hn
        simpa [M, Nat.cast_pow, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using
          hlift e n hn)
  have hpe_dvd_q : (p : ℤ) ^ e ∣ (a q : ℤ) := by
    have hemod : (p : ℤ) ^ e ∣ (p : ℤ) ^ (e + 1) := by
      exact pow_dvd_pow (p : ℤ) (by omega)
    exact (Int.ModEq.dvd_iff (hclass.of_dvd hemod)).mpr hbasepow
  have hpnext_not_dvd_q : ¬ (p : ℤ) ^ (e + 1) ∣ (a q : ℤ) := by
    intro hqdiv
    apply hnotbasepow
    exact (Int.ModEq.dvd_iff hclass).mp hqdiv
  have hqval : padicValNat p (a q) = e := by
    apply padicValNat_exact_of_dvd_not_dvd (hpos q (by omega)).ne'
    · exact_mod_cast hpe_dvd_q
    · intro h
      apply hpnext_not_dvd_q
      exact_mod_cast h
  have hpPart : pPart p (a q) = p ^ e := by simp [pPart, hqval]
  have hpPart1 : pPart p (a 1) = 1 := by simp [pPart, ha1]
  refine ⟨q, by omega, hq, ?_⟩
  rw [prime_index_moebius_sum a p q hq, hpPart, hpPart1]
  have hpgt : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
  have hlt : p ^ e - 1 < q := by omega
  have hspos : (0 : ℤ) < (p ^ e : ℕ) - 1 := by omega
  have hslt : ((p ^ e : ℕ) : ℤ) - 1 < q := by omega
  refine ⟨hspos, hslt, ?_⟩
  intro hd
  have hnat : q ∣ p ^ e - 1 := by
    rw [← Int.natCast_sub (by omega : 1 ≤ p ^ e)] at hd
    exact_mod_cast hd
  have hz : p ^ e - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hnat hlt
  omega

private theorem inverse_power_mul {d : ℕ} (A : GLInt d) (n : ℕ) :
    (A⁻¹).val * A.val ^ (n + 1) = A.val ^ n := by
  rw [pow_succ']
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem unimodular_coordinate_obstruction
    {d : ℕ} (A : GLInt d) (v : Fin d → ℤ) (i : Fin d)
    (hInvCoord : ((A⁻¹).val.mulVec v) i = 0)
    (a : ℕ → ℕ)
    (hcoord : ∀ n, 0 < n → (a n : ℤ) = ((A.val ^ n).mulVec v) i)
    (hpos : ∀ n, 0 < n → 0 < a n)
    (ha1 : a 1 = 1)
    (p : ℕ) (hp : p.Prime) :
    ∀ H : ℕ, ∃ q > H, q.Prime ∧
      0 < ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) ∧
      (∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)) < q ∧
      ¬ (q : ℤ) ∣ ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) := by
  obtain ⟨T, hT, hTpow⟩ := exists_mod_p_period A hp
  have hmod := gl_power_mod_eq_one A hTpow
  obtain ⟨C, hC⟩ := (weak_period_lift A hmod 1)
  let r : ℕ := p * T - 1
  have hrpos : 0 < r := by
    dsimp [r]
    have hmul : T < p * T := by
      simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hT
    exact Nat.sub_pos_of_lt (lt_of_le_of_lt (Nat.one_le_iff_ne_zero.mpr hT.ne') hmul)
  have hindex : r + 1 = T * p := by
    dsimp [r]
    rw [Nat.sub_add_cancel (by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hp.ne_zero hT.ne'))]
    ac_rfl
  have hInvPow : (A⁻¹).val * A.val ^ (r + 1) = A.val ^ r :=
    inverse_power_mul A r
  have hInvPow' : (A⁻¹).val * A.val ^ (T * p) = A.val ^ r := by
    simpa [hindex] using hInvPow
  have hbase_mat : (A⁻¹).val * A.val ^ (T * p) =
      (A⁻¹).val + (p : ℤ) • ((A⁻¹).val * ((p : ℤ) • C)) := by
    have hC' : A.val ^ (T * p) = 1 + (p : ℤ) ^ 2 • C := by
      simpa [pow_one] using hC
    rw [hC', Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    congr 1
    rw [Matrix.mul_smul, smul_smul]
    simp [pow_two]
  have hbase_vec := matrix_vec_modEq_of_eq (m := p)
    (X := (A⁻¹).val * A.val ^ (T * p)) (Y := (A⁻¹).val)
    (C := (A⁻¹).val * ((p : ℤ) • C)) hbase_mat v i
  have hbase : (a (p * T - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ)] := by
    rw [show p * T - 1 = r by rfl]
    have hleft : ((A⁻¹).val * A.val ^ (T * p)).mulVec v i =
        (A.val ^ r).mulVec v i := by
      rw [hInvPow']
    rw [hcoord r hrpos, ← hleft]
    have hinvzero : ((A⁻¹).val.mulVec v) i ≡ 0 [ZMOD (p : ℤ)] := by
      rw [hInvCoord]
    exact hbase_vec.trans hinvzero
  exact unbounded_prime_index_obstruction a hpos ha1 p hp T hT hbase
    (coordinate_weak_period A v i
      (weak_period_lift A hmod) a hcoord)


end
end D5.S3.Arith.LocalDold.UnimodularObstruction
