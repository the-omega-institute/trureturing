/- GID: D5/S1/Recurrence/Invariants/HannaShiftSquareModEight
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaShiftSquareModEight
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Hanna's A392203 conjecture: the g.f. of A(x - A(x)) = x^2 + x*A(x) is rational modulo 8. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse

open PowerSeries
namespace D5.S1.Recurrence.Invariants.HannaShiftSquareModEight
variable {R : Type*} [CommRing R]

/-- `A` solves Hanna's equation `A(x - A(x)) = x^2 + x*A(x)` with `A = O(x^2)`. -/
def IsSolution (A : PowerSeries ℤ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 0 ∧ A.subst (X - A) = X ^ 2 + X * A

/-- Hanna's conjecture for OEIS A392203, as a proposition. -/
def claim : Prop :=
  (∃ A : PowerSeries ℤ, IsSolution A) ∧
    ∀ A : PowerSeries ℤ, IsSolution A → ∀ n : ℕ, 1 ≤ n →
      coeff (2 * n) A % 8 = 1 ∧ coeff (2 * n + 1) A % 8 = 3
private def Agree (d : ℕ) (f g : PowerSeries R) : Prop := ∀ n < d, coeff n f = coeff n g
private noncomputable def T (f : PowerSeries R) : PowerSeries R :=
  X^2 + X*f - (f.subst (X-f) - f)

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 0
  | k+1 => T (approximation k)

private noncomputable def solution : PowerSeries ℤ :=
  mk (fun n => coeff n (approximation (n+1)))

private noncomputable def candidate : PowerSeries (ZMod 8) :=
  mk fun n => if n < 2 then 0 else if n % 2 = 0 then 1 else 3

theorem result :
    (∃ A : PowerSeries ℤ, IsSolution A) ∧
      ∀ A : PowerSeries ℤ, IsSolution A → ∀ n : ℕ, 1 ≤ n →
        coeff (2 * n) A % 8 = 1 ∧ coeff (2 * n + 1) A % 8 = 3 := by
  have agree_iff : ∀ {R : Type} [CommRing R] (d : ℕ) (f g : PowerSeries R),
      Agree d f g ↔ (X : PowerSeries R)^d ∣ f - g := by
    intro R _ d f g

    simp [Agree,X_pow_dvd_iff,map_sub,sub_eq_zero]
  have coeff_pow_zero : ∀ {R : Type} [CommRing R] {f : PowerSeries R}
      (h : constantCoeff f = 0) {n k : ℕ} (hn : n < k), coeff n (f ^ k) = 0 := by
    intro R _ f h n k hn
    exact X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h) k) n hn
  have agree_pow_succ : ∀ {R : Type} [CommRing R] {d : ℕ} {f g : PowerSeries R}
      (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
      (h : Agree d f g) (k : ℕ), Agree (d + 1) (f ^ (k+2)) (g ^ (k+2)) := by
    intro R _ d f g hf hg h k

    apply (agree_iff _ _ _).mpr
    obtain ⟨q, hq⟩ := (agree_iff _ _ _).mp h
    have hpow := (Commute.all f g).mul_geom_sum₂ (k+2)
    have hsum : X ∣ (∑ i ∈ Finset.range (k+2), f ^ i * g ^ (k+2-1-i)) := by
      apply Finset.dvd_sum
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        apply X_dvd_iff.mpr
        rw [← coeff_zero_eq_constantCoeff, coeff_mul]
        simp [coeff_zero_eq_constantCoeff, hg]
      · have hi1 : 1 ≤ i := by omega
        apply X_dvd_iff.mpr
        rw [← coeff_zero_eq_constantCoeff, coeff_mul]
        rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
        simp only [coeff_zero_eq_constantCoeff]
        rw [← coeff_zero_eq_constantCoeff, coeff_pow_zero hf (by omega), zero_mul]
    obtain ⟨s, hs⟩ := hsum
    refine ⟨q * s, ?_⟩
    calc
      _ = (f - g) * ∑ i ∈ Finset.range (k+2), f ^ i * g ^ (k+2-1-i) := hpow.symm
      _ = (X ^ d * q) * (X * s) := by rw [hq, hs]
      _ = X ^ (d + 1) * (q * s) := by rw [pow_succ]; ring
  have subst_agree_shift : ∀ {R : Type} [CommRing R] {d : ℕ} {f u v : PowerSeries R}
      (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 0)
      (hu0 : constantCoeff u = 0) (hv0 : constantCoeff v = 0)
      (h : Agree d u v), Agree (d+1) (f.subst u) (f.subst v) := by
    intro R _ d f u v hf0 hf1 hu0 hv0 h n hn
    rw [coeff_subst' (.of_constantCoeff_zero hu0), coeff_subst' (.of_constantCoeff_zero hv0)]
    apply finsum_congr
    intro k
    by_cases hk : k < 2
    · have hfk : coeff k f = 0 := by rcases k with _ | _ | k <;> simp_all
      simp [hfk]
    · have hp := agree_pow_succ hu0 hv0 h (k-2)
      have hpc : coeff n (u^k) = coeff n (v^k) := by
        simpa [Nat.sub_add_cancel (by omega : 2 ≤ k)] using hp n hn
      rw [hpc]
  have subst_minus_self : ∀ {R : Type} [CommRing R] {d : ℕ} {b v : PowerSeries R}
      (hv0 : constantCoeff v = 0) (hv1 : coeff 1 v = 1)
      (h : Agree d b 0), Agree (d+1) (b.subst v) b := by
    intro R _ d b v hv0 hv1 h n hn
    rw [coeff_subst' (.of_constantCoeff_zero hv0)]
    rw [finsum_eq_single _ n]
    · have hdiag : coeff n (v^n) = 1 := by
        by_cases hn0 : n = 0
        · subst n; simp
        · obtain ⟨w, hw⟩ := X_dvd_iff.mpr hv0
          have hw1 : constantCoeff w = 1 := by
            simpa [hw, coeff_X_pow_mul'] using hv1
          rw [show v = X * w by simp [hw]]
          simp [mul_pow, coeff_X_pow_mul', hw1]
      rw [hdiag, smul_eq_mul, mul_one]
    · intro k hk
      by_cases hkn : k < n
      · have hbk : coeff k b = 0 := by
          have := h k (by omega)
          simpa using this
        simp [hbk]
      · have hnk : n < k := by omega
        rw [coeff_pow_zero hv0 hnk, smul_zero]
  have T_agree : ∀ {R : Type} [CommRing R] {d : ℕ} {f g : PowerSeries R}
      (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 0)
      (hg0 : constantCoeff g = 0) (hg1 : coeff 1 g = 0)
      (h : Agree d f g), Agree (d+1) (T f) (T g) := by
    intro R _ d f g hf0 hf1 hg0 hg1 h

    have hu0 : constantCoeff (X-f) = 0 := by simp [hf0]
    have hv0 : constantCoeff (X-g) = 0 := by simp [hg0]
    have huv : Agree d (X-f) (X-g) := by
      intro n hn; simp only [map_sub]; rw [h n hn]
    have hs := subst_agree_shift hf0 hf1 hu0 hv0 huv
    have hb0 : constantCoeff (f-g) = 0 := by simp [hf0, hg0]
    have hb1 : coeff 1 (f-g) = 0 := by simp [hf1, hg1]
    have hb : Agree d (f-g) 0 := by
      intro n hn
      simp only [map_sub]
      exact sub_eq_zero.mpr (h n hn)
    have hv1 : coeff 1 (X-g) = 1 := by simp [map_sub, coeff_X, hg1]
    have hm := subst_minus_self hv0 hv1 hb
    have hxf : Agree (d+1) (X*f) (X*g) := by
      intro n hn
      by_cases hn0 : n = 0
      · subst n; simp
      · have hcf := coeff_X_pow_mul' f 1 n
        have hcg := coeff_X_pow_mul' g 1 n
        simp only [pow_one] at hcf hcg
        rw [hcf, hcg]
        rw [if_pos (by omega)] at hcf hcg
        rw [if_pos (by omega)]
        rw [if_pos (by omega)]
        exact h (n-1) (by omega)
    dsimp [T]
    intro n hn
    simp only [map_add, map_sub]
    have hcomp : coeff n (f.subst (X-g)) - coeff n (g.subst (X-g)) =
        coeff n f - coeff n g := by
      have hh := hm n hn
      have hh' : coeff n (f.subst (X-g) - g.subst (X-g)) = coeff n f - coeff n g := by
        rw [← subst_sub (.of_constantCoeff_zero hv0)]
        exact hh
      simpa only [map_sub] using hh'
    rw [hxf n hn, hs n hn]
    have hrel : coeff n (f.subst (X-g)) - coeff n f =
        coeff n (g.subst (X-g)) - coeff n g := by
      linear_combination hcomp
    exact congrArg (fun z => coeff n (X^2) + coeff n (X*g) - z) hrel
  have T_order : ∀ {R : Type} [CommRing R] {f : PowerSeries R}
      (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 0),
      constantCoeff (T f) = 0 ∧ coeff 1 (T f) = 0 := by
    intro R _ f hf0 hf1

    have hu0 : constantCoeff (X-f) = 0 := by simp [hf0]
    have hs0 : constantCoeff (f.subst (X-f)) = 0 :=
      constantCoeff_subst_eq_zero hu0 f hf0
    have hs1 : coeff 1 (f.subst (X-f)) = 0 := by
      rw [coeff_subst' (.of_constantCoeff_zero hu0)]
      apply finsum_eq_zero_of_forall_eq_zero
      intro k
      by_cases hk : k < 2
      · have hfk : coeff k f = 0 := by rcases k with _ | _ | k <;> simp_all
        simp [hfk]
      · rw [coeff_pow_zero hu0 (by omega), smul_zero]
    constructor
    · dsimp [T]
      simp [hs0, hf0]
    · dsimp [T]
      simp only [map_add, map_sub]
      rw [hs1]
      have hxf : coeff 1 (X*f) = 0 := by
        simp [coeff_zero_eq_constantCoeff, hf0]
      rw [hxf]
      simpa [coeff_X] using hf1
  have approximation_order : ∀ (k : ℕ),
      constantCoeff (approximation k) = 0 ∧ coeff 1 (approximation k) = 0 := by
    intro k

    induction k with
    | zero => simp [approximation]
    | succ k ih => exact T_order ih.1 ih.2
  have approximation_stable : ∀ {d k : ℕ}, d ≤ k →
      Agree d (approximation d) (approximation k) := by
    intro d k hdk

    induction d generalizing k with
    | zero => intro n hn; omega
    | succ d ih =>
      cases k with
      | zero => omega
      | succ k =>
        change Agree (d + 1) (T (approximation d)) (T (approximation k))
        exact T_agree (approximation_order d).1 (approximation_order d).2
          (approximation_order k).1 (approximation_order k).2 (ih (by omega))
  have solution_agree : ∀ (d : ℕ), Agree d solution (approximation d) := by
    intro d n hn
    have h := approximation_stable (d := n+1) (k := d) (by omega : n+1 ≤ d)
    simpa [solution] using h n (by omega)
  have solution_order : constantCoeff solution = 0 ∧ coeff 1 solution = 0 := by

    have h0 := solution_agree 1 0 (by omega)
    have h1 := solution_agree 2 1 (by omega)
    constructor
    · simpa [coeff_zero_eq_constantCoeff, approximation_order] using h0
    · simpa [approximation_order] using h1
  have solution_fixed : solution = T solution := by

    ext n
    have ha := solution_agree (n+2) n (by omega)
    have hs := T_agree solution_order.1 solution_order.2
        (approximation_order (n+1)).1 (approximation_order (n+1)).2 (solution_agree (n+1)) n (by omega)
    exact ha.trans hs.symm
  have candidate_identity :
      candidate * (1 - (X : PowerSeries (ZMod 8)) ^ 2) = X ^ 2 + 3 * X ^ 3 := by

    ext n
    have hc (j : ℕ) : coeff j candidate =
        if j < 2 then 0 else if j % 2 = 0 then 1 else 3 := by simp [candidate]
    have hshift : coeff n (candidate * (X : PowerSeries (ZMod 8))^2) =
        if 2 ≤ n then coeff (n - 2) candidate else 0 := by
      rw [mul_comm]
      have h := coeff_X_pow_mul' candidate 2 n
      simpa only [mul_comm] using h
    have h2 : coeff n ((X : PowerSeries (ZMod 8))^2) = if n = 2 then 1 else 0 := by
      have h := coeff_X_pow_mul' (1 : PowerSeries (ZMod 8)) 2 n
      simp only [mul_one] at h
      calc
        coeff n ((X : PowerSeries (ZMod 8))^2) =
            if 2 ≤ n then coeff (n - 2) (1 : PowerSeries (ZMod 8)) else 0 := h
        _ = if n = 2 then 1 else 0 := by
          by_cases hn : 2 ≤ n
          · simp [hn, show n - 2 = 0 ↔ n = 2 by omega]
          · simp [hn, show n ≠ 2 by omega]
    have h3 : coeff n ((X : PowerSeries (ZMod 8))^3) =
        if n = 3 then 1 else 0 := by
      have h := coeff_X_pow_mul' (1 : PowerSeries (ZMod 8)) 3 n
      simp only [mul_one] at h
      calc
        coeff n ((X : PowerSeries (ZMod 8))^3) =
            if 3 ≤ n then coeff (n - 3) (1 : PowerSeries (ZMod 8)) else 0 := h
        _ = if n = 3 then 1 else 0 := by
          by_cases hn : 3 ≤ n
          · simp [hn, show n - 3 = 0 ↔ n = 3 by omega]
          · simp [hn, show n ≠ 3 by omega]
    have h3c : coeff n (3 * (X : PowerSeries (ZMod 8))^3) =
        3 * coeff n ((X : PowerSeries (ZMod 8))^3) := by
      change coeff n (C (3 : ZMod 8) * (X : PowerSeries (ZMod 8))^3) = _
      rw [coeff_C_mul]
    rw [show candidate * (1 - (X : PowerSeries (ZMod 8))^2) =
        candidate - candidate * X^2 by ring]
    simp only [map_sub, map_add, hc, hshift, h2]
    rw [h3c]
    by_cases hn0 : n = 0
    · subst n; simp
    by_cases hn1 : n = 1
    · subst n; simp
    by_cases hn2 : n = 2
    · subst n; simp
    by_cases hn3 : n = 3
    · subst n; simp
    have hn4 : 4 ≤ n := by omega
    have hnpar : (n - 2) % 2 = n % 2 := by omega
    by_cases hp : n % 2 = 0
    · simp [hp, hnpar, show ¬n ≤ 1 by omega, show 2 ≤ n by omega,
        show ¬n ≤ 3 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
    · simp [hp, hnpar, show ¬n ≤ 1 by omega, show 2 ≤ n by omega,
        show ¬n ≤ 3 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
  have candidate_equation :
      candidate.subst ((X : PowerSeries (ZMod 8)) - candidate) =
        X ^ 2 + X * candidate := by

    let D : PowerSeries (ZMod 8) := 1 - X ^ 2
    let N : PowerSeries (ZMod 8) := X - X ^ 2 - 4 * X ^ 3
    let y : PowerSeries (ZMod 8) := X - candidate
    have hc0 : constantCoeff candidate = 0 := by simp [candidate]
    have hy0 : constantCoeff y = 0 := by simp [y, hc0]
    have hs : candidate.subst y * (1 - y ^ 2) = y ^ 2 + 3 * y ^ 3 := by
      have h := congrArg (subst y) candidate_identity
      have hsubst : HasSubst y := .of_constantCoeff_zero hy0
      have hone : subst y (1 : PowerSeries (ZMod 8)) = 1 := by
        rw [← coe_substAlgHom hsubst]
        exact map_one _
      have hthree : subst y (3 : PowerSeries (ZMod 8)) = 3 := by
        rw [← coe_substAlgHom hsubst]
        exact map_ofNat _ 3
      simpa only [subst_mul (.of_constantCoeff_zero hy0), subst_sub (.of_constantCoeff_zero hy0),
        subst_pow (.of_constantCoeff_zero hy0), subst_X (.of_constantCoeff_zero hy0),
        subst_add (.of_constantCoeff_zero hy0), subst_C, map_one, map_ofNat, hone, hthree] using h
    have hD : candidate * D = X ^ 2 + 3 * X ^ 3 := by
      simpa [D] using candidate_identity
    have hyD : y * D = N := by
      calc
        y * D = X * D - candidate * D := by dsimp [y]; ring
        _ = X * D - (X ^ 2 + 3 * X ^ 3) := by rw [hD]
        _ = N := by dsimp [D, N]; ring
    have hy2 : y ^ 2 * D ^ 2 = N ^ 2 := by
      calc
        y ^ 2 * D ^ 2 = (y * D) ^ 2 := by ring
        _ = N ^ 2 := by rw [hyD]
    have hy3 : y ^ 3 * D ^ 3 = N ^ 3 := by
      calc
        y ^ 3 * D ^ 3 = (y * D) ^ 3 := by ring
        _ = N ^ 3 := by rw [hyD]
    have hclear : candidate.subst y * D * (D ^ 2 - N ^ 2) =
        N ^ 2 * D + 3 * N ^ 3 := by
      calc
        candidate.subst y * D * (D ^ 2 - N ^ 2) =
            (candidate.subst y * (1 - y ^ 2)) * D ^ 3 := by
              rw [show N ^ 2 = y ^ 2 * D ^ 2 by symm; exact hy2]
              ring
        _ = (y ^ 2 + 3 * y ^ 3) * D ^ 3 := by rw [hs]
        _ = y ^ 2 * D ^ 3 + 3 * (y ^ 3 * D ^ 3) := by ring
        _ = N ^ 2 * D + 3 * N ^ 3 := by
          rw [show y ^ 2 * D ^ 3 = N ^ 2 * D by
            calc
              y ^ 2 * D ^ 3 = (y ^ 2 * D ^ 2) * D := by ring
              _ = N ^ 2 * D := by rw [hy2]]
          rw [hy3]
    have hpoly : N ^ 2 * D + 3 * N ^ 3 =
        (X ^ 2 * D + X ^ 3 + 3 * X ^ 4) * (D ^ 2 - N ^ 2) := by
      dsimp [D, N]
      ring_nf
      have h17 : (17 : PowerSeries (ZMod 8)) = 1 := by
        change algebraMap (ZMod 8) (PowerSeries (ZMod 8)) (17 : ZMod 8) = 1
        rw [PowerSeries.algebraMap_eq]
        have h : (17 : ZMod 8) = 1 := by decide
        rw [h]
        simp
      have h92 : (92 : PowerSeries (ZMod 8)) = 4 := by
        change algebraMap (ZMod 8) (PowerSeries (ZMod 8)) (92 : ZMod 8) = 4
        rw [PowerSeries.algebraMap_eq]
        have h : (92 : ZMod 8) = 4 := by decide
        rw [h]
        rfl
      have h100 : (100 : PowerSeries (ZMod 8)) = 4 := by
        change algebraMap (ZMod 8) (PowerSeries (ZMod 8)) (100 : ZMod 8) = 4
        rw [PowerSeries.algebraMap_eq]
        have h : (100 : ZMod 8) = 4 := by decide
        rw [h]
        rfl
      have h160 : (160 : PowerSeries (ZMod 8)) = 0 := by
        change algebraMap (ZMod 8) (PowerSeries (ZMod 8)) (160 : ZMod 8) = 0
        rw [PowerSeries.algebraMap_eq]
        have h : (160 : ZMod 8) = 0 := by decide
        rw [h]
        simp
      have h192 : (192 : PowerSeries (ZMod 8)) = 0 := by
        change algebraMap (ZMod 8) (PowerSeries (ZMod 8)) (192 : ZMod 8) = 0
        rw [PowerSeries.algebraMap_eq]
        have h : (192 : ZMod 8) = 0 := by decide
        rw [h]
        simp
      have h8 : (8 : PowerSeries (ZMod 8)) = 0 := by
        change algebraMap (ZMod 8) (PowerSeries (ZMod 8)) (8 : ZMod 8) = 0
        rw [PowerSeries.algebraMap_eq]
        have h : (8 : ZMod 8) = 0 := by decide
        rw [h]
        simp
      have h32 : (32 : PowerSeries (ZMod 8)) = 0 := by
        change algebraMap (ZMod 8) (PowerSeries (ZMod 8)) (32 : ZMod 8) = 0
        rw [PowerSeries.algebraMap_eq]
        have h : (32 : ZMod 8) = 0 := by decide
        rw [h]
        simp
      rw [h17, h92, h100, h160, h192, h8, h32]
      ring
    have htarget : (X ^ 2 + X * candidate) * D =
        X ^ 2 * D + X ^ 3 + 3 * X ^ 4 := by
      rw [add_mul, mul_assoc, hD]
      ring
    have hunitU : IsUnit (D ^ 2 - N ^ 2) := by
      apply isUnit_iff_constantCoeff.mpr
      simp [D, N]
    have hunitD : IsUnit D := by
      apply isUnit_iff_constantCoeff.mpr
      simp [D]
    have hcd : candidate.subst y * D = (X ^ 2 + X * candidate) * D := by
      apply hunitU.mul_right_cancel
      rw [hclear, hpoly, htarget]
    apply hunitD.mul_right_cancel
    exact hcd
  have unique_mod8 : ∀ {f g : PowerSeries (ZMod 8)}
      (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 0)
      (hg0 : constantCoeff g = 0) (hg1 : coeff 1 g = 0)
      (hf : f.subst (X - f) = X ^ 2 + X * f)
      (hg : g.subst (X - g) = X ^ 2 + X * g), f = g := by
    intro f g hf0 hf1 hg0 hg1 hf hg

    have hTf : T f = f := by
      dsimp [T]
      rw [hf]
      ring
    have hTg : T g = g := by
      dsimp [T]
      rw [hg]
      ring
    have hall : ∀ d, Agree d f g := by
      intro d
      induction d with
      | zero => intro n hn; omega
      | succ d ih =>
        simpa only [hTf, hTg] using T_agree hf0 hf1 hg0 hg1 ih
    ext n
    exact hall (n + 1) n (by omega)
  have candidate_order :
      constantCoeff candidate = 0 ∧ coeff 1 candidate = 0 := by

    constructor
    · simp [candidate]
    · simp [candidate]
  have hsol_eq : solution.subst (X - solution) = X ^ 2 + X * solution := by
    have h := solution_fixed
    dsimp [T] at h
    linear_combination h
  refine ⟨⟨solution, solution_order.1, solution_order.2, hsol_eq⟩, ?_⟩
  intro A hA n hn
  let hom := Int.castRingHom (ZMod 8)
  let f : PowerSeries (ZMod 8) := A.map hom
  have hf0 : constantCoeff f = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff]
    exact congrArg hom hA.1
  have hf1 : coeff 1 f = 0 := by
    rw [coeff_map]
    exact congrArg hom hA.2.1
  have harg0 : constantCoeff (X - A) = 0 := by simp [hA.1]
  have hmap := congrArg (PowerSeries.map hom) hA.2.2
  have hsubst : PowerSeries.map hom (A.subst (X - A)) =
      f.subst (X - f) := by
    have hm := map_subst (a := X - A) (h := hom) (.of_constantCoeff_zero harg0) A
    have hi : (X - A).map hom = X - f := by simp [f, hom]
    calc
      PowerSeries.map hom (A.subst (X - A)) =
          subst ((PowerSeries.map hom) (X - A)) ((PowerSeries.map hom) A) := hm
      _ = f.subst (X - f) := by rw [hi]
  rw [hsubst] at hmap
  simp only [map_add, map_mul, map_pow, map_X] at hmap
  have hfeq : f.subst (X - f) = X ^ 2 + X * f := by
    simpa [f, hom] using hmap
  have hcand : candidate.subst (X - candidate) =
      X ^ 2 + X * candidate := candidate_equation
  have heq := unique_mod8 hf0 hf1 candidate_order.1 candidate_order.2 hfeq hcand
  have heven : (coeff (2 * n) candidate : ZMod 8) = 1 := by
    simp only [candidate, coeff_mk]
    rw [if_neg (by omega), if_pos (by omega)]
  have hodd : (coeff (2 * n + 1) candidate : ZMod 8) = 3 := by
    simp only [candidate, coeff_mk]
    rw [if_neg (by omega), if_neg (by omega)]
  have hce := congrArg (coeff (2 * n)) heq
  have hco := congrArg (coeff (2 * n + 1)) heq
  have hce' : ((coeff (2 * n) A : ℤ) : ZMod 8) = 1 := by
    simpa [f, hom, coeff_map, heven] using hce
  have hco' : ((coeff (2 * n + 1) A : ℤ) : ZMod 8) = 3 := by
    simpa [f, hom, coeff_map, hodd] using hco
  have hemod := (ZMod.intCast_eq_intCast_iff' (coeff (2 * n) A) 1 8).mp hce'
  have homod := (ZMod.intCast_eq_intCast_iff' (coeff (2 * n + 1) A) 3 8).mp hco'
  have h1mod : (1 : ℤ) % 8 = 1 := by omega
  have h3mod : (3 : ℤ) % 8 = 3 := by omega
  exact ⟨by simpa [h1mod] using hemod, by simpa [h3mod] using homod⟩

end D5.S1.Recurrence.Invariants.HannaShiftSquareModEight
