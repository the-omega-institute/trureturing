/- GID: D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer coefficients of Hanna's full bivariate formal exponential. -/

/-
admission_basis: open-problem-resolution (#31340; pending independent approval).
escape_witness: none.
Every theorem is classified bind-only relative to the reused degree, formal
substitution, polynomial congruence lifting and series-valued Dwork suppliers.
The full result is an external open-problem application, not a new abstract
Dwork theorem. The result consumes diagonal_exponential,
diagonal_kronecker, kronecker_extract and weightedGhost_divisibility.
ghost_prime_power is consumed by weightedGhost_divisibility.
exponential_coefficient_support is consumed by kronecker_extract and result.
All private helpers occur on these live proof paths; no unused companion
result is supplied. Utility is none. Literature completeness and worldwide
priority remain ASSUMED-UNVERIFIED.
-/

import Mathlib.Algebra.Algebra.Hom.Rat
import D5.S3.Combinatorics.PowerSeries.LaurentSpecialization
import D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! Polynomial congruences and coefficient isolation for a formal bivariate exponential. -/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality

open PowerSeries Finset

noncomputable section

/-- The polynomial ghost, with its independent polynomial variable Y. -/
def ghost (m : ℤ) (k : ℕ) : Polynomial ℤ :=
  (Polynomial.C (m ^ k) + Polynomial.X) ^ k

/-- The zero-constant formal logarithm over Q[Y]. -/
def logarithmicInput (m : ℤ) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk fun k => (1 / (k : ℚ)) •
    (Polynomial.C ((m : ℚ) ^ k) + Polynomial.X) ^ k

/-- The literal formal exponential of the bivariate logarithmic input. -/
def exponentialSum (m : ℤ) : PowerSeries (Polynomial ℚ) :=
  (PowerSeries.exp (Polynomial ℚ)).subst (logarithmicInput m)

/-- All signed integer parameters and both independent coefficient indices. -/
def claim : Prop :=
  ∀ (m : ℤ) (n j : ℕ), ∃ z : ℤ,
    (PowerSeries.coeff n (exponentialSum m)).coeff j = (z : ℚ)

private theorem ghost_base (m : ℤ) (p n : ℕ) (hp : p.Prime) :
    (p : Polynomial ℤ) ∣
      (Polynomial.C (m ^ (p * n)) + Polynomial.X) ^ p -
        (Polynomial.C (m ^ n) + Polynomial.X ^ p) := by
  let : Fact p.Prime := ⟨hp⟩
  apply (Polynomial.C_dvd_iff_dvd_coeff (p : ℤ) _).mpr
  intro j
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have he : Polynomial.map (Int.castRingHom (ZMod p))
      ((Polynomial.C (m ^ (p * n)) + Polynomial.X) ^ p -
        (Polynomial.C (m ^ n) + Polynomial.X ^ p)) = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_C, Polynomial.map_X, map_pow]
    rw [add_pow_char]
    simp only [← Polynomial.C_pow, ZMod.pow_card]
    have hm : ((Int.castRingHom (ZMod p)) m) ^ (p * n) =
        ((Int.castRingHom (ZMod p)) m) ^ n := by
      rw [pow_mul, ZMod.pow_card]
    rw [hm, sub_self]
  have hc := congrArg (fun f : Polynomial (ZMod p) => f.coeff j) he
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, Int.coe_castRingHom] using hc

/-- The full polynomial Frobenius congruence at every prime-power level. -/
theorem ghost_prime_power (m : ℤ) (p s t : ℕ) (hp : p.Prime) :
    (p : Polynomial ℤ) ^ (s + 1) ∣
      ghost m (p * (p ^ s * t)) -
        Polynomial.expand ℤ p (ghost m (p ^ s * t)) := by
  let A : Polynomial ℤ := (Polynomial.C (m ^ (p * (p ^ s * t))) + Polynomial.X) ^ p
  let B : Polynomial ℤ := Polynomial.C (m ^ (p ^ s * t)) + Polynomial.X ^ p
  have h : (p : Polynomial ℤ) ^ (s + 1) ∣ A ^ (p ^ s) - B ^ (p ^ s) :=
    dvd_sub_pow_of_dvd_sub (ghost_base m p (p ^ s * t) hp) s
  have ht := h.trans (sub_dvd_pow_sub_pow (A ^ (p ^ s)) (B ^ (p ^ s)) t)
  simpa only [A, B, ghost, map_pow, map_add, Polynomial.expand_C, Polynomial.expand_X,
    ← pow_mul, Nat.mul_assoc] using ht

private def Cone (f : PowerSeries (Polynomial ℚ)) : Prop :=
  ∀ n, (PowerSeries.coeff n f).natDegree ≤ n

private theorem cone_one : Cone 1 := by
  intro n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

private theorem cone_mul {f g : PowerSeries (Polynomial ℚ)}
    (hf : Cone f) (hg : Cone g) : Cone (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ab hab
  exact Polynomial.natDegree_mul_le.trans
    ((Nat.add_le_add (hf ab.1) (hg ab.2)).trans (Finset.mem_antidiagonal.mp hab).le)

private theorem cone_pow {f : PowerSeries (Polynomial ℚ)} (hf : Cone f) (k : ℕ) :
    Cone (f ^ k) := by
  induction k with
  | zero => simpa using cone_one
  | succ k ih => simpa [pow_succ] using cone_mul ih hf

private theorem cone_logarithmicInput (m : ℤ) : Cone (logarithmicInput m) := by
  intro n
  simp only [logarithmicInput, coeff_mk]
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply Polynomial.natDegree_pow_le.trans
  have hd : (Polynomial.C ((m : ℚ) ^ n) + Polynomial.X).natDegree ≤ 1 := by
    exact Polynomial.natDegree_add_le_of_degree_le (by simp) (by simp)
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hd

private theorem exponential_coeff (h : PowerSeries (Polynomial ℚ))
    (hh : constantCoeff h = 0) (n : ℕ) :
    coeff n ((exp (Polynomial ℚ)).subst h) =
      ∑ k ∈ range (n + 1), (1 / (k.factorial : ℚ)) • coeff n (h ^ k) := by
  classical
  rw [coeff_subst' (.of_constantCoeff_zero hh)]
  simp only [coeff_exp]
  rw [finsum_eq_sum_of_support_subset]
  · apply sum_congr rfl
    intro k hk
    simp [Algebra.smul_def]
  · intro k hk
    by_contra hkn
    have hlt : n < k := by simp only [mem_coe, mem_range] at hkn; omega
    have hz : coeff n (h ^ k) = 0 :=
      X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hh) k) n hlt
    exact hk (by simp [hz])

/-- The Y support of the degree-n coefficient is confined to 0,...,n. -/
theorem exponential_coefficient_support (m : ℤ) (n j : ℕ) (hj : n < j) :
    (coeff n (exponentialSum m)).coeff j = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  apply lt_of_le_of_lt _ hj
  rw [exponentialSum, exponential_coeff _ (by simp [logarithmicInput])]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_smul_le _ _).trans (cone_pow (cone_logarithmicInput m) k n)

/-- Coefficientwise substitution X = T^M and Y = T. The positive M case
has only finitely many contributors to any output coefficient. -/
def kronecker (M : ℕ) (f : PowerSeries (Polynomial ℚ)) : PowerSeries ℚ :=
  PowerSeries.mk fun N => ∑ a ∈ range (N + 1),
    if M * a ≤ N then (coeff a f).coeff (N - M * a) else 0

/-- A coefficient in the support cone is isolated by the substitution
X = T^(n+1), Y = T; all other source bidegrees contribute zero. -/
theorem kronecker_extract (m : ℤ) (n j : ℕ) (hj : j ≤ n) :
    coeff ((n + 1) * n + j) (kronecker (n + 1) (exponentialSum m)) =
      (coeff n (exponentialSum m)).coeff j := by
  classical
  rw [kronecker, coeff_mk]
  rw [Finset.sum_eq_single n]
  · simp
  · intro a ha han
    by_cases hal : a < n
    · have hmul := Nat.mul_le_mul_left (n + 1) (show a + 1 ≤ n by omega)
      simp only [Nat.mul_add, Nat.mul_one] at hmul
      have hdiff : a < (n + 1) * n + j - (n + 1) * a := by omega
      split_ifs <;> simp [exponential_coefficient_support m a _ hdiff]
    · have hmul := Nat.mul_le_mul_left (n + 1) (show n + 1 ≤ a by omega)
      have htoo : ¬ (n + 1) * a ≤ (n + 1) * n + j := by
        simp only [Nat.mul_add, Nat.mul_one] at hmul
        omega
      simp [htoo]
  · intro hn
    exfalso
    apply hn
    simp only [mem_range]
    have hmul : n ≤ (n + 1) * n := by nlinarith
    omega


open scoped PowerSeries.WithPiTopology
private local instance : UniformSpace ℚ := ⊥
private local instance : DiscreteUniformity ℚ := ⟨rfl⟩
private local instance : UniformSpace (Polynomial ℚ) := ⊥
private local instance : DiscreteUniformity (Polynomial ℚ) := ⟨rfl⟩

private noncomputable def diagonal (a : ℕ) :
    PowerSeries (Polynomial ℚ) →ₐ[ℚ] PowerSeries ℚ :=
  (D5.S3.Combinatorics.PowerSeries.LaurentSpecialization.diagonal a 1).toRatAlgHom

private theorem diagonal_apply (a : ℕ) (f : PowerSeries (Polynomial ℚ)) :
    diagonal a f = PowerSeries.eval₂ (Polynomial.eval₂RingHom C X) (X^(a+1)) f := by
  simp only [diagonal, RingHom.toRatAlgHom_apply,
    D5.S3.Combinatorics.PowerSeries.LaurentSpecialization.diagonal,
    PowerSeries.coe_eval₂Hom, pow_one]

private theorem diagonal_continuous (a : ℕ) : Continuous (diagonal a) := by
  change Continuous (fun f => diagonal a f)
  simp_rw [diagonal_apply]
  exact PowerSeries.continuous_eval₂ continuous_of_discreteTopology (by
    rw [pow_succ]; exact PowerSeries.HasEval.X.mul_left _)

private theorem diagonal_coeff (a N : ℕ) (f : PowerSeries (Polynomial ℚ)) :
    coeff N (diagonal a f) = ∑ n ∈ range (N+1),
      if (a+1)*n ≤ N then (coeff n f).coeff (N-(a+1)*n) else 0 := by
  have hs := PowerSeries.hasSum_eval₂
    (φ := Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) X)
    continuous_of_discreteTopology
    (show PowerSeries.HasEval ((X : PowerSeries ℚ)^(a+1)) from by
      rw [pow_succ]; exact PowerSeries.HasEval.X.mul_left _) f
  have hh := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mp hs N
  rw [← diagonal_apply a f] at hh
  simp only [← pow_mul, coeff_mul_X_pow', Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C_X_eq_coe, Polynomial.coeff_coe] at hh
  rw [← hh.tsum_eq, tsum_eq_sum (s := range (N+1))]
  intro n hn
  have hle : n ≤ (a+1)*n := by nlinarith
  exact ite_eq_right (by have := hn; simp only [mem_range, not_lt] at this; omega)

private theorem diagonal_kronecker (a : ℕ) (f : PowerSeries (Polynomial ℚ)) :
    diagonal a f = kronecker (a+1) f := by
  ext N
  simpa only [kronecker, coeff_mk] using diagonal_coeff a N f

private theorem diagonal_subst (a : ℕ) (f : PowerSeries ℚ)
    (b : PowerSeries (Polynomial ℚ)) (hb : constantCoeff b = 0)
    (hdb : constantCoeff (diagonal a b) = 0) :
    diagonal a (subst b f) = subst (diagonal a b) f := by
  have h := MvPowerSeries.comp_subst_apply
    (R := ℚ) (S := Polynomial ℚ) (ε := diagonal a)
    (PowerSeries.HasSubst.of_constantCoeff_zero hb).const (diagonal_continuous a) f
  have hd : HasSubst (diagonal a b) := .of_constantCoeff_zero hdb
  change diagonal a (subst b f) = PowerSeries.aeval hd.hasEval f at h
  rw [← PowerSeries.substAlgHom_eq_aeval hd] at h
  simpa only [PowerSeries.coe_substAlgHom] using h

/-- The series-valued weight omits the T^r already inserted by logSum. -/
def weightedGhost (a : ℕ) (m : ℤ) (r : ℕ) : PowerSeries ℤ :=
  (ghost m r : PowerSeries ℤ) * X^(a*r)

private theorem weightedGhost_map (a : ℕ) (m : ℤ) (r : ℕ) :
    (weightedGhost a m r).map (Int.castRingHom ℚ) =
      (C ((m : ℚ)^r)+X)^r * X^(a*r) := by
  simp only [weightedGhost, ghost, Polynomial.coe_pow, Polynomial.coe_add,
    Polynomial.coe_C, Polynomial.coe_X, map_mul, map_pow, map_add, map_C, map_X,
    Int.coe_castRingHom]

private theorem diagonal_logarithm (a : ℕ) (m : ℤ) :
    diagonal a (logarithmicInput m) =
      HannaSelfSubstitutionIntegrality.logSum
        (fun r => (weightedGhost a m r).map (Int.castRingHom ℚ)) := by
  ext N
  rw [diagonal_coeff]
  simp only [HannaSelfSubstitutionIntegrality.logSum, coeff_mk, weightedGhost_map,
    coeff_mul_X_pow']
  rw [show Icc 1 N = (range (N+1)).erase 0 by ext i; simp; omega,
    sum_erase_eq_sub (by simp)]
  simp only [Nat.cast_zero, div_zero, sub_zero]
  apply sum_congr rfl
  intro r hr
  have hrN : r ≤ N := by have := mem_range.mp hr; omega
  simp only [logarithmicInput, coeff_mk, Polynomial.coeff_smul, smul_eq_mul]
  have hp : ((C ((m : ℚ)^r)+X)^r : PowerSeries ℚ) =
      ((Polynomial.C ((m : ℚ)^r)+Polynomial.X)^r : Polynomial ℚ) := by simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_X]
  rw [hp, Polynomial.coeff_coe]
  have hi : (a+1)*r ≤ N ↔ a*r ≤ N-r := by
    rw [Nat.add_mul, one_mul]; omega
  by_cases h : (a+1)*r ≤ N
  · rw [ite_eq_left h, ite_eq_left (hi.mp h)]
    rw [show N-r-a*r = N-(a+1)*r by rw [Nat.add_mul, one_mul]; omega]
    simp [div_eq_mul_inv, mul_comm]
  · rw [ite_eq_right h, ite_eq_right (mt hi.mpr h), zero_div]

private theorem diagonal_logarithm_zero (a : ℕ) (m : ℤ) :
    constantCoeff (diagonal a (logarithmicInput m)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, diagonal_coeff]
  simp [logarithmicInput]

private theorem diagonal_exponential (a : ℕ) (m : ℤ) :
    diagonal a (exponentialSum m) = (exp ℚ).subst
      (HannaSelfSubstitutionIntegrality.logSum
        (fun r => (weightedGhost a m r).map (Int.castRingHom ℚ))) := by
  have hm : (exp ℚ).map (algebraMap ℚ (Polynomial ℚ)) = exp (Polynomial ℚ) := map_exp _
  have hs : HasSubst (logarithmicInput m) := .of_constantCoeff_zero' (by simp [logarithmicInput])
  have he : exponentialSum m = subst (logarithmicInput m) (exp ℚ) := by
    rw [exponentialSum, ← hm, map_algebraMap_eq_subst_X,
      subst_comp_subst_apply HasSubst.X' hs, subst_X hs]
  rw [he, diagonal_subst a _ _ (by simp [logarithmicInput]) (diagonal_logarithm_zero a m),
    diagonal_logarithm]

private theorem weightedGhost_divisibility (a : ℕ) (m : ℤ) :
    ∀ p : ℕ, p.Prime → ∀ n : ℕ, n ≠ 0 →
      (p : PowerSeries ℤ)^padicValNat p n ∣
        weightedGhost a m n - if p ∣ n then
          (weightedGhost a m (n/p)).subst ((X : PowerSeries ℤ)^p) else 0 := by
  intro p hp n hn
  by_cases hpn : p ∣ n
  · rw [ite_eq_left hpn]
    let : Fact p.Prime := ⟨hp⟩
    let q := n/p
    have hq : q ≠ 0 := Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos)
    have hnq : n = p*q := (Nat.mul_div_cancel' hpn).symm
    let s := padicValNat p q
    let t := q / p^s
    have hqst : q = p^s*t := (Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := q))).symm
    have hv : padicValNat p n = s+1 := by
      rw [hnq, padicValNat.mul hp.ne_zero hq, padicValNat.self hp.one_lt]
      omega
    have hg := ghost_prime_power m p s t hp
    rw [← hqst, ← hnq] at hg
    have hmap := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := ℤ)) hg
    have he : (weightedGhost a m q).subst ((X : PowerSeries ℤ)^p) =
        ((Polynomial.expand ℤ p (ghost m q) : Polynomial ℤ) : PowerSeries ℤ) * X^(a*n) := by
      simp only [weightedGhost, ghost, Polynomial.coe_pow, Polynomial.coe_add,
        Polynomial.coe_C, Polynomial.coe_X, subst_mul (.X_pow hp.ne_zero),
        subst_pow (.X_pow hp.ne_zero), subst_add (.X_pow hp.ne_zero), subst_C,
        subst_X (.X_pow hp.ne_zero), map_pow, map_add, Polynomial.expand_C,
        Polynomial.expand_X]
      rw [← pow_mul]
      congr 2
      rw [hnq]
      ring
    rw [he, weightedGhost, ← sub_mul, hv]
    exact dvd_mul_of_dvd_left (by simpa only [map_pow, map_natCast,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub] using hmap) _
  · rw [ite_eq_right hpn, sub_zero, padicValNat.eq_zero_of_not_dvd hpn, pow_zero]
    exact one_dvd _

/-- Every coefficient of the full independent-variable formal exponential is integral. -/
theorem result : claim := by
  intro m n j
  by_cases hj : j ≤ n
  · have hi := HannaSelfSubstitutionIntegrality.exp_logSum_integral_of_divisibility
      (weightedGhost n m) (weightedGhost_divisibility n m)
    dsimp only at hi
    rw [← diagonal_exponential n m, diagonal_kronecker] at hi
    obtain ⟨z, hz⟩ := hi ((n+1)*n+j)
    exact ⟨z, by simpa only [kronecker_extract m n j hj] using hz⟩
  · exact ⟨0, by rw [exponential_coefficient_support m n j (by omega)]; simp⟩

end
end D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality
