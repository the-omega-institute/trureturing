/- GID: D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11
   mirror-E: none(waiver:symbolic-counting-theorem)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.claim; result=D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.result; claim=D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11.claim
   digest: Primitive radical-component exceptions satisfy a power-saving counting bound. -/

import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
import D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair
import D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
import D5.S3.Arith.Divisors.UnitaryProductBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Primitive radical-component exceptions and the relative density inside C. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11

open ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient)
open ZelinskyZhangKLPrimitive (Deficient)
open ZelinskyRadicalComponentDensity (radicalComponentSet count)
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
  (one_sub_sum_mul_prod_le_one)
open StrongPseudoperfectEulerDensity (largeSquares largeSquares_card)
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.PrimeFiberPropagation (divisorRatio divisorRatio_pos)

attribute [local instance] Classical.propDecidable

private lemma exception_large_prime {n X T : ℕ}
    (hn : 2 ≤ n) (hnX : n ≤ X) (hnot : n ∉ largeSquares X T)
    (hlarge : (T : ℝ) ^ 6 < 2 * n) (hB : n ∉ radicalComponentSet 2) :
    (2 / (T : ℝ) ^ 2) * n ≤ (largestPrime n : ℝ) ^ 2 := by
  by_contra! h
  exact hB ⟨hn, ZelinskyRadicalComponentDensity.radical_sandwich
    (by norm_num) hn hnX hnot hlarge h⟩

private lemma exception_large_prime_power {M n : ℕ} (hM : 2 ≤ M)
    (hn : M ^ 39 < n) (hnX : n ≤ M ^ 40)
    (hnot : n ∉ largeSquares (M ^ 40) M) (hB : n ∉ radicalComponentSet 2) :
    M ^ 18 < largestPrime n := by
  have hM0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  have h6 : M ^ 6 ≤ M ^ 39 := Nat.pow_le_pow_right hM0 (by decide)
  have hn2 : 2 ≤ n := by
    have := one_le_pow₀ (n := 39) hM1
    omega
  have hlarge : (M : ℝ) ^ 6 < 2 * n := by
    have hh : M ^ 6 < 2 * n := by omega
    exact_mod_cast hh
  have hb := exception_large_prime hn2 hnX hnot hlarge hB
  by_contra! hP
  have hPM : largestPrime n ^ 2 * M ^ 2 ≤ M ^ 38 := by
    calc
      _ ≤ (M ^ 18) ^ 2 * M ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hP 2)
      _ = _ := by ring
  have h38 : M ^ 38 ≤ M ^ 39 := Nat.pow_le_pow_right hM0 (by decide)
  have hPn : (largestPrime n : ℝ) ^ 2 * (M : ℝ) ^ 2 < 2 * n := by
    have hh : largestPrime n ^ 2 * M ^ 2 < 2 * n := by omega
    exact_mod_cast hh
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have he : (2 / (M : ℝ) ^ 2) * n * (M : ℝ) ^ 2 = 2 * n := by
    field_simp
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg (M : ℝ))
  rw [he] at hh
  linarith


private lemma ratio_mul {a b : ℕ} (hc : a.Coprime b) :
    divisorRatio (a * b) = divisorRatio a * divisorRatio b := by
  exact D5.S3.Arith.ExponentExchange.IntegerSwap.normalized_sigma_mul hc

private lemma ordered_narrow_fraction_impossible {s t a b D : ℕ} {c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haD : a ≤ D) (hbD : b ≤ D)
    (hc : 1 ≤ c) (hlo : 2 ≤ c * ((s : ℝ) / a))
    (hhi : c * ((t : ℝ) / b) < 2 + 1 / (D : ℝ) ^ 2)
    (hgap : s * b < t * a) : False := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hDR : (0 : ℝ) < D := by exact_mod_cast ha.trans_le haD
  have hw : (0 : ℝ) < (a : ℝ) * b := mul_pos haR hbR
  have hz : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hbound : (a : ℝ) * b ≤ (D : ℝ) ^ 2 := by
    have haDR : (a : ℝ) ≤ D := by exact_mod_cast haD
    have hbDR : (b : ℝ) ≤ D := by exact_mod_cast hbD
    nlinarith
  have hinv : (1 / (D : ℝ) ^ 2) * ((a : ℝ) * b) ≤ 1 := by
    rw [one_div_mul_eq_div]
    exact (div_le_one hz).mpr hbound
  have hcross : (s : ℝ) * b + 1 ≤ (t : ℝ) * a := by
    exact_mod_cast hgap
  have hcross' := mul_le_mul_of_nonneg_left hcross (by linarith : 0 ≤ c)
  have hlow := mul_le_mul_of_nonneg_right hlo hw.le
  have hhigh := mul_lt_mul_of_pos_right hhi hw
  have hs : (c * ((s : ℝ) / a)) * ((a : ℝ) * b) = c * (s * b) := by
    field_simp
  have ht : (c * ((t : ℝ) / b)) * ((a : ℝ) * b) = c * (t * a) := by
    field_simp
  rw [hs] at hlow
  rw [ht] at hhigh
  nlinarith

private lemma sigma_cross_eq_of_narrow {m d e D : ℕ}
    (hm : 0 < m) (hd : 0 < d) (he : 0 < e)
    (hdD : d ≤ D) (heD : e ≤ D) (hmd : m.Coprime d) (hme : m.Coprime e)
    (hCd : PrimitiveNonDeficient (m * d)) (hCe : PrimitiveNonDeficient (m * e))
    (hhd : divisorRatio (m * d) < 2 + 1 / (D : ℝ) ^ 2)
    (hhe : divisorRatio (m * e) < 2 + 1 / (D : ℝ) ^ 2) :
    ArithmeticFunction.sigma 1 d * e = ArithmeticFunction.sigma 1 e * d := by
  have hld := ZelinskyRadicalComponentConjectures.primitive_ratio_lower
    (mul_pos hm hd) hCd
  have hle := ZelinskyRadicalComponentConjectures.primitive_ratio_lower
    (mul_pos hm he) hCe
  rw [ratio_mul hmd] at hld hhd
  rw [ratio_mul hme] at hle hhe
  change 2 ≤ divisorRatio m * ((ArithmeticFunction.sigma 1 d : ℝ) / d) at hld
  change 2 ≤ divisorRatio m * ((ArithmeticFunction.sigma 1 e : ℝ) / e) at hle
  change divisorRatio m * ((ArithmeticFunction.sigma 1 d : ℝ) / d) < _ at hhd
  change divisorRatio m * ((ArithmeticFunction.sigma 1 e : ℝ) / e) < _ at hhe
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ordered_narrow_fraction_impossible hd he hdD heD
      (ZelinskyRadicalComponentConjectures.ratio_one_le hm) hld hhe hlt
  · exact ordered_narrow_fraction_impossible he hd heD hdD
      (ZelinskyRadicalComponentConjectures.ratio_one_le hm) hle hhd hlt

private lemma sigma_gt_self {a : ℕ} (ha : 1 < a) :
    a < ArithmeticFunction.sigma 1 a := by
  have hsub : ({1, a} : Finset ℕ) ⊆ a.divisors := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with h | h
    · subst d
      exact Nat.one_mem_divisors.mpr (by omega)
    · subst d
      exact Nat.mem_divisors_self a (by omega)
  have hsum := Finset.sum_le_sum_of_subset hsub (f := id)
  have hbound : 1 + a ≤ ArithmeticFunction.sigma 1 a := by
    simpa [ArithmeticFunction.sigma_one_apply, ha.ne', ha.ne] using hsum
  omega

private lemma no_nontrivial_sigma_divisor {m d a : ℕ} (hm : 1 < m)
    (hd : 0 < d) (ha : a ∣ d) (hC : PrimitiveNonDeficient (m * d))
    (hs : a ∣ ArithmeticFunction.sigma 1 a) : a = 1 := by
  have had : a ∣ m * d := dvd_trans ha (dvd_mul_left d m)
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hd
  by_contra hne
  have ha1 : 1 < a := by omega
  have hgt := sigma_gt_self ha1
  obtain ⟨k, hk⟩ := hs
  have hk2 : 2 ≤ k := by nlinarith
  have hsig : 2 * a ≤ ArithmeticFunction.sigma 1 a := by nlinarith
  have halt : a < m * d := by
    have hadle := Nat.le_of_dvd hd ha
    nlinarith
  have hdef := hC.2 a
    (Nat.mem_divisors.mpr ⟨had, (mul_pos (by omega) hd).ne'⟩) halt
  unfold Deficient at hdef
  have hsigR : (2 : ℝ) * a ≤ ArithmeticFunction.sigma 1 a := by
    exact_mod_cast hsig
  linarith

private lemma unitary_squarefree_fiber_unique {m d e D : ℕ}
    (hm : 1 < m) (hd : Squarefree d) (he : Squarefree e)
    (hdD : d ≤ D) (heD : e ≤ D) (hmd : m.Coprime d) (hme : m.Coprime e)
    (hCd : PrimitiveNonDeficient (m * d)) (hCe : PrimitiveNonDeficient (m * e))
    (hhd : divisorRatio (m * d) < 2 + 1 / (D : ℝ) ^ 2)
    (hhe : divisorRatio (m * e) < 2 + 1 / (D : ℝ) ^ 2) : d = e := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have he0 : 0 < e := Nat.pos_of_ne_zero he.ne_zero
  have hcross := sigma_cross_eq_of_narrow (by omega) hd0 he0
    hdD heD hmd hme hCd hCe hhd hhe
  let g := Nat.gcd d e
  let a := d / g
  let b := e / g
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left e hd0
  have hga : g * a = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have hgb : g * b = e := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  have ha0 : 0 < a := by nlinarith
  have hb0 : 0 < b := by nlinarith
  have hgaC : g.Coprime a := Nat.coprime_of_squarefree_mul (hga.symm ▸ hd)
  have hgbC : g.Coprime b := Nat.coprime_of_squarefree_mul (hgb.symm ▸ he)
  have hadvd : a ∣ d := by rw [← hga]; exact dvd_mul_left a g
  have hbdvd : b ∣ e := by rw [← hgb]; exact dvd_mul_left b g
  have hab : a.Coprime b :=
    (Nat.coprime_div_gcd_of_squarefree hd he.ne_zero).coprime_dvd_right hbdvd
  have hratio : divisorRatio d = divisorRatio e := by
    apply (div_eq_div_iff (by exact_mod_cast hd.ne_zero)
      (by exact_mod_cast he.ne_zero)).mpr
    exact_mod_cast hcross
  have hratio' : divisorRatio a = divisorRatio b := by
    apply mul_left_cancel₀ (divisorRatio_pos hg0.ne').ne'
    simpa only [← ratio_mul hgaC, ← ratio_mul hgbC, hga, hgb] using hratio
  have hsmall : ArithmeticFunction.sigma 1 a * b =
      ArithmeticFunction.sigma 1 b * a := by
    have h := (div_eq_div_iff (by exact_mod_cast ha0.ne')
      (by exact_mod_cast hb0.ne')).mp hratio'
    exact_mod_cast h
  have hsa : a ∣ ArithmeticFunction.sigma 1 a := by
    apply hab.dvd_of_dvd_mul_right
    rw [hsmall]
    exact dvd_mul_left a _
  have hsb : b ∣ ArithmeticFunction.sigma 1 b := by
    apply hab.symm.dvd_of_dvd_mul_right
    rw [← hsmall]
    exact dvd_mul_left b _
  have ha1 := no_nontrivial_sigma_divisor hm hd0 hadvd hCd hsa
  have hb1 := no_nontrivial_sigma_divisor hm he0 hbdvd hCe hsb
  rw [ha1, mul_one] at hga
  rw [hb1, mul_one] at hgb
  exact hga.symm.trans hgb


private lemma primitive_ratio_narrow {M n : ℕ} (hM : 2 ≤ M)
    (hn : 2 ≤ n) (hC : PrimitiveNonDeficient n) (hP : M ^ 18 < largestPrime n) :
    divisorRatio n < 2 + 1 / ((M ^ 8 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨p, hp, hpeq⟩ := n.primeFactors.exists_mem_eq_sup
    (Nat.nonempty_primeFactors.mpr (by omega)) id
  have hpP : p = largestPrime n := by
    simpa only [largestPrime, id_eq] using hpeq.symm
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hprime.pos
  have hrepr : n / p * p = n := Nat.div_mul_cancel hd
  have hstep := ZelinskyRadicalComponentConjectures.primitive_prime_step
    hm hprime (hrepr.symm ▸ hC)
  rw [hrepr] at hstep
  have hk : 1 ≤ n.factorization p :=
    hprime.factorization_pos_of_dvd (by omega) hd
  have hppow : p ≤ p ^ n.factorization p := by
    simpa using Nat.pow_le_pow_right hprime.pos hk
  have hM0 : 0 < M := by omega
  have hM2 : 2 ≤ M ^ 2 := by nlinarith
  have hM16 : 0 < M ^ 16 := pow_pos hM0 _
  have hbound : 2 * M ^ 16 ≤ p := by
    have hh : M ^ 18 < p := hpP ▸ hP
    have heq : M ^ 18 = M ^ 16 * M ^ 2 := by ring
    nlinarith
  have hden : (2 : ℝ) * ((M ^ 8 : ℕ) : ℝ) ^ 2 ≤
      (p : ℝ) ^ n.factorization p := by
    have hh : 2 * (M ^ 8) ^ 2 ≤ p ^ n.factorization p := by
      nlinarith [hppow]
    exact_mod_cast hh
  have hMR : (0 : ℝ) < ((M ^ 8 : ℕ) : ℝ) := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hfrac : 2 / (p : ℝ) ^ n.factorization p ≤
      1 / ((M ^ 8 : ℕ) : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hpR _) (sq_pos_of_pos hMR)).mpr
    simpa using hden
  linarith


private lemma subproduct_crossing (S : Finset ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hsmall : ∀ p ∈ S, p < M) (hlarge : M ≤ ∏ p ∈ S, p) :
    ∃ D ⊆ S, M ≤ ∏ p ∈ D, p ∧ (∏ p ∈ D, p) ≤ M ^ 2 := by
  classical
  by_cases hupper : (∏ p ∈ S, p) ≤ M ^ 2
  · exact ⟨S, Subset.rfl, hlarge, hupper⟩
  have hprod : 0 < ∏ p ∈ S, p := lt_of_lt_of_le (by omega) hlarge
  have hpos (p : ℕ) (hp : p ∈ S) : 0 < p :=
    Nat.pos_of_ne_zero ((prod_ne_zero_iff.mp hprod.ne') p hp)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlog (A : Finset ℕ) (hA : A ⊆ S) :
      log (∏ p ∈ A, (p : ℝ)) = ∑ p ∈ A, log (p : ℝ) :=
    log_prod (fun p hp => by exact_mod_cast (hpos p (hA hp)).ne')
  have hfull : 2 * log (M : ℝ) < ∑ p ∈ S, log (p : ℝ) := by
    calc
      2 * log (M : ℝ) = log ((M : ℝ) ^ 2) := by rw [log_pow]; norm_num
      _ < log (∏ p ∈ S, (p : ℝ)) := by
        apply log_lt_log (by positivity)
        have hh : ((M ^ 2 : ℕ) : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by
          exact_mod_cast (lt_of_not_ge hupper)
        simpa only [Nat.cast_pow, Nat.cast_prod] using hh
      _ = _ := hlog S Subset.rfl
  obtain ⟨D, hDS, hDupper, _, hDlower⟩ :=
    D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair.finite_pack
      S (fun p => log (p : ℝ))
      (d := 2 * log (M : ℝ)) (M := log (M : ℝ))
      (mul_nonneg (by norm_num) (log_nonneg (by exact_mod_cast hM)))
      hfull (fun p hp => ⟨log_nonneg (by
        exact_mod_cast (show 1 ≤ p by have := hpos p hp; omega)),
        log_le_log (by exact_mod_cast hpos p hp) (by exact_mod_cast (hsmall p hp).le)⟩)
  have hDpos : (0 : ℝ) < ∏ p ∈ D, (p : ℝ) :=
    prod_pos fun p hp => by exact_mod_cast hpos p (hDS hp)
  refine ⟨D, hDS, ?_, ?_⟩
  · have hh : (M : ℝ) ≤ ∏ p ∈ D, (p : ℝ) := by
      apply (log_le_log_iff hMR hDpos).mp
      rw [hlog D hDS]
      linarith
    have hh' : (M : ℝ) ≤ ((∏ p ∈ D, p : ℕ) : ℝ) := by
      simpa only [Nat.cast_prod] using hh
    exact_mod_cast hh'
  · have hh : (∏ p ∈ D, (p : ℝ)) ≤ (M : ℝ) ^ 2 := by
      apply (log_le_log_iff hDpos (by positivity)).mp
      rw [hlog D hDS, log_pow]
      exact hDupper
    have hh' : ((∏ p ∈ D, p : ℕ) : ℝ) ≤ ((M ^ 2 : ℕ) : ℝ) := by
      simpa only [Nat.cast_prod, Nat.cast_pow] using hh
    exact_mod_cast hh'

private lemma ratio_prime_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    divisorRatio (∏ p ∈ S, p) = ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
  rw [divisorRatio,
    ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime S hS,
    Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  rw [D5.S3.Factorization.ReciprocalSigmaThreshold.sigma_prime (hS p hp)]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
  push_cast
  field_simp

private lemma unitary_squarefree_split {a b n M : ℕ} (ha : Squarefree a)
    (hb : 0 < b) (hbM : b ≤ M) (he : b ^ 2 * a = n) :
    ∃ r t : ℕ, 0 < r ∧ r ≤ M ^ 3 ∧ Squarefree t ∧ r.Coprime t ∧ r * t = n := by
  let g := Nat.gcd a b
  let t := a / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hb
  have hat : g * t = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have ht : Squarefree t := ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left a b))
  have htg : t.Coprime g := Nat.coprime_of_squarefree_mul (by simpa [hat, mul_comm] using ha)
  have htb : t.Coprime b := Nat.coprime_div_gcd_of_squarefree ha hb.ne'
  refine ⟨b ^ 2 * g, t, by positivity, ?_, ht, ?_, ?_⟩
  · have hgM : g ≤ M := (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)).trans hbM
    calc
      b ^ 2 * g ≤ M ^ 2 * M := Nat.mul_le_mul (Nat.pow_le_pow_left hbM 2) hgM
      _ = M ^ 3 := by ring
  · exact ((htb.pow_right 2).mul_right htg).symm
  · calc
      b ^ 2 * g * t = b ^ 2 * (g * t) := by ring
      _ = n := by rw [hat, he]

private lemma unitary_subproduct {r t n : ℕ} (ht : Squarefree t)
    (hrt : r.Coprime t) (he : r * t = n) {D : Finset ℕ} (hD : D ⊆ t.primeFactors) :
    (∏ p ∈ D, p) ∣ n ∧ Squarefree (∏ p ∈ D, p) ∧
      (∏ p ∈ D, p).Coprime (n / ∏ p ∈ D, p) := by
  classical
  have hpow : (∏ p ∈ D, p ^ t.factorization p) = ∏ p ∈ D, p := by
    apply prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree ht
      (Nat.prime_of_mem_primeFactors (hD hp)) (Nat.dvd_of_mem_primeFactors (hD hp))]
    simp
  have hu := D5.S3.Arith.Divisors.UnitaryProductBridge.prime_power_product_unitary
    t ht.ne_zero D hD
  rw [hpow] at hu
  obtain ⟨hd, hcop⟩ := mem_filter.mp hu
  have hdt := Nat.dvd_of_mem_divisors hd
  refine ⟨dvd_trans hdt (he ▸ dvd_mul_left t r), ht.squarefree_of_dvd hdt, ?_⟩
  rw [← he, Nat.mul_div_assoc r hdt]
  exact (hrt.symm.coprime_dvd_left hdt).mul_right hcop

private lemma primitive_small_part_large {M n r t : ℕ} (hM : 100 ≤ M)
    (hr : 0 < r) (hrM : r ≤ M ^ 3) (ht : Squarefree t) (hrt : r.Coprime t)
    (he : r * t = n) (hnlo : M ^ 4 < n) (hnhi : n ≤ M ^ 40)
    (hC : PrimitiveNonDeficient n)
    (hgap : ∀ p ∈ t.primeFactors, ¬ (M ≤ p ∧ p ≤ M ^ 8)) :
    M ≤ ∏ p ∈ t.primeFactors with p < M, p := by
  classical
  let S := t.primeFactors.filter fun p => p < M
  let V := t.primeFactors.filter fun p => ¬ p < M
  let s := ∏ p ∈ S, p
  let v := ∏ p ∈ V, p
  have hn : 0 < n := by omega
  have hMpos : 0 < M := by omega
  have hS : S ⊆ t.primeFactors := filter_subset _ _
  have hV : V ⊆ t.primeFactors := filter_subset _ _
  have hSV : s * v = t := by
    dsimp [s, v, S, V]
    rw [prod_filter_mul_prod_filter_not, Nat.prod_primeFactors_of_squarefree ht]
  have hspos : 0 < s := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (hS hp)).pos
  have hvpos : 0 < v := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (hV hp)).pos
  have hsdt : s ∣ t := ⟨v, hSV.symm⟩
  have hvdt : v ∣ t := by rw [← hSV]; exact dvd_mul_left v s
  have hvcopr : (r * s).Coprime v := by
    have hsv : s.Coprime v := Nat.coprime_of_squarefree_mul (hSV.symm ▸ ht)
    exact (hrt.coprime_dvd_right hvdt).mul_left hsv
  have hprod : r * s * v = n := by rw [mul_assoc, hSV, he]
  have hlarge (p : ℕ) (hp : p ∈ V) : M ^ 8 < p := by
    obtain ⟨hpt, hpM⟩ := mem_filter.mp hp
    exact lt_of_not_ge (fun h => hgap p hpt ⟨by omega, h⟩)
  have hvn : v ≤ n := by nlinarith
  have hcard : V.card ≤ 40 := by
    have hp : M ^ V.card ≤ v := by
      calc
        _ = ∏ _p ∈ V, M := by simp
        _ ≤ v := Finset.prod_le_prod fun p hp => by
          have h := hlarge p hp
          have hpow := Nat.le_self_pow (by decide : 8 ≠ 0) M
          omega
    exact (pow_le_pow_iff_right₀ (by omega : 1 < M)).mp (hp.trans (hvn.trans hnhi))
  by_contra! hsM
  have huM : r * s ≤ M ^ 4 := by
    calc
      r * s ≤ M ^ 3 * M := Nat.mul_le_mul hrM hsM.le
      _ = M ^ 4 := by ring
  have hu : 0 < r * s := Nat.mul_pos hr hspos
  have hud : r * s ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨⟨v, hprod.symm⟩, hn.ne'⟩
  have hdef := hC.2 (r * s) hud (huM.trans_lt hnlo)
  have hsigN : ArithmeticFunction.sigma 1 (r * s) + 1 ≤ 2 * (r * s) := by
    have hdef' : (ArithmeticFunction.sigma 1 (r * s) : ℝ) <
        (2 * (r * s) : ℕ) := by simpa only [Deficient, Nat.cast_mul, Nat.cast_ofNat] using hdef
    exact Nat.succ_le_of_lt (by exact_mod_cast hdef')
  have hsig : (ArithmeticFunction.sigma 1 (r * s) : ℝ) ≤ 2 * (r * s : ℕ) - 1 := by
    have hc : (ArithmeticFunction.sigma 1 (r * s) : ℝ) + 1 ≤ 2 * (r * s : ℕ) :=
      by exact_mod_cast hsigN
    linarith
  let H : ℝ := (M : ℝ) ^ 8
  let U : ℝ := (r * s : ℕ)
  let A : ℝ := (ArithmeticFunction.sigma 1 (r * s) : ℝ)
  let B : ℝ := divisorRatio v
  let z : ℝ := ∑ p ∈ V, 1 / (p : ℝ)
  have hH : 0 < H := by dsimp [H]; positivity
  have hU : 0 < U := by
    dsimp only [U]
    exact_mod_cast hu
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B, divisorRatio]; positivity
  have hz0 : 0 ≤ z := sum_nonneg fun p hp => by positivity
  have hz : z ≤ 40 / H := by
    calc
      z ≤ ∑ _p ∈ V, 1 / H := sum_le_sum fun p hp =>
        one_div_le_one_div_of_le hH (by
          dsimp [H]
          exact_mod_cast (hlarge p hp).le)
      _ = (V.card : ℝ) / H := by simp [div_eq_mul_inv]
      _ ≤ 40 / H := div_le_div_of_nonneg_right (by exact_mod_cast hcard) hH.le
  have hUbound : U ≤ (M : ℝ) ^ 4 := by
    dsimp only [U]
    exact_mod_cast huM
  have hHlarge : 80 * U < H := by
    have hpowN : 80 < M ^ 4 :=
      lt_of_lt_of_le (by omega : 80 < M) (Nat.le_self_pow (by decide : 4 ≠ 0) M)
    have hpow : (80 : ℝ) < (M : ℝ) ^ 4 := by exact_mod_cast hpowN
    have heH : H = ((M : ℝ) ^ 4) ^ 2 := by dsimp [H]; ring
    rw [heH]
    nlinarith [mul_nonneg (sub_nonneg.mpr hUbound) (by norm_num : (0 : ℝ) ≤ 80)]
  have hUone : 1 ≤ U := by
    dsimp only [U]
    exact_mod_cast (show 1 ≤ r * s by omega)
  have hH40 : 40 < H := by nlinarith
  have hzlt : z < 1 := by
    apply lt_of_le_of_lt hz
    exact (div_lt_one hH).mpr hH40
  have hprodle : B * (1 - z) ≤ 1 := by
    dsimp [B, z]
    rw [ratio_prime_product V (fun p hp => Nat.prime_of_mem_primeFactors (hV hp))]
    simpa only [mul_comm] using
      one_sub_sum_mul_prod_le_one V (fun p => 1 / (p : ℝ))
          (fun p _hp => by positivity)
  have hnratio := ZelinskyRadicalComponentConjectures.primitive_ratio_lower hn hC
  have hratio : divisorRatio n = A / U * B := by
    rw [← hprod]
    exact D5.S3.Arith.ExponentExchange.IntegerSwap.normalized_sigma_mul hvcopr
  rw [hratio] at hnratio
  have hlower : 2 * U ≤ A * B := by
    apply (le_div_iff₀ hU).mp
    simpa only [div_mul_eq_mul_div] using hnratio
  have hprodA := mul_le_mul_of_nonneg_left hprodle hA
  have hlowmul := mul_le_mul_of_nonneg_right hlower (by linarith : 0 ≤ 1 - z)
  have hsmallA : A ≤ 2 * U - 1 := hsig
  have hsum : 1 ≤ 2 * U * z := by nlinarith
  have hzmul : z * H ≤ 40 := (le_div_iff₀ hH).mp hz
  have hmul := mul_le_mul_of_nonneg_left hzmul (by positivity : 0 ≤ 2 * U)
  have hpos := mul_le_mul_of_nonneg_right hsum hH.le
  nlinarith

private lemma small_unitary_factor_of_split {M n r t : ℕ} (hM : 100 ≤ M)
    (hr : 0 < r) (hrM : r ≤ M ^ 3) (ht : Squarefree t) (hrt : r.Coprime t)
    (he : r * t = n) (hnlo : M ^ 4 < n) (hnhi : n ≤ M ^ 40)
    (hC : PrimitiveNonDeficient n) :
    ∃ d : ℕ, d ∣ n ∧ Squarefree d ∧ d.Coprime (n / d) ∧ M ≤ d ∧ d ≤ M ^ 8 := by
  classical
  by_cases hmedium : ∃ p ∈ t.primeFactors, M ≤ p ∧ p ≤ M ^ 8
  · obtain ⟨p, hpt, hpM, hpH⟩ := hmedium
    have h := unitary_subproduct ht hrt he
      (show ({p} : Finset ℕ) ⊆ t.primeFactors by simpa using hpt)
    simp only [prod_singleton] at h
    exact ⟨p, h.1, h.2.1, h.2.2, hpM, hpH⟩
  · have hgap : ∀ p ∈ t.primeFactors, ¬ (M ≤ p ∧ p ≤ M ^ 8) := by
      intro p hp hh
      exact hmedium ⟨p, hp, hh⟩
    let S := t.primeFactors.filter fun p => p < M
    have hlarge := primitive_small_part_large hM hr hrM ht hrt he hnlo hnhi hC hgap
    obtain ⟨D, hDS, hlo, hhi⟩ := subproduct_crossing S M (by omega)
      (fun p hp => (mem_filter.mp hp).2) hlarge
    have hD : D ⊆ t.primeFactors := hDS.trans (filter_subset _ _)
    obtain ⟨hd, hsq, hcop⟩ := unitary_subproduct ht hrt he hD
    refine ⟨∏ p ∈ D, p, hd, hsq, hcop, hlo, hhi.trans ?_⟩
    exact Nat.pow_le_pow_right (by omega : 0 < M) (by decide : 2 ≤ 8)

private lemma small_unitary_factor {M n a b : ℕ} (hM : 100 ≤ M)
    (ha : Squarefree a) (hb : 0 < b) (hbM : b ≤ M) (he : b ^ 2 * a = n)
    (hnlo : M ^ 4 < n) (hnhi : n ≤ M ^ 40) (hC : PrimitiveNonDeficient n) :
    ∃ d : ℕ, d ∣ n ∧ Squarefree d ∧ d.Coprime (n / d) ∧ M ≤ d ∧ d ≤ M ^ 8 := by
  obtain ⟨r, t, hr, hrM, ht, hrt, hrtN⟩ := unitary_squarefree_split ha hb hbM he
  exact small_unitary_factor_of_split hM hr hrM ht hrt hrtN hnlo hnhi hC


private lemma compression_card (S : Finset ℕ) (X L D : ℕ) (hL : 0 < L)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X ∧ PrimitiveNonDeficient n ∧
      divisorRatio n < 2 + 1 / (D : ℝ) ^ 2)
    (hdiv : ∀ n ∈ S, ∃ d : ℕ, d ∣ n ∧ Squarefree d ∧
      (n / d).Coprime d ∧ L ≤ d ∧ d ≤ D ∧ d < n) :
    S.card ≤ X / L := by
  let d (n : {n // n ∈ S}) : ℕ := Classical.choose (hdiv n.val n.property)
  have hd (n : {n // n ∈ S}) := Classical.choose_spec (hdiv n.val n.property)
  change ∀ n : {n // n ∈ S}, d n ∣ n.val ∧ Squarefree (d n) ∧
    (n.val / d n).Coprime (d n) ∧ L ≤ d n ∧ d n ≤ D ∧ d n < n.val at hd
  have hcard : S.attach.card ≤ (Icc 1 (X / L)).card := by
    apply card_le_card_of_injOn (fun n => n.val / d n)
    · intro n _
      have hn := hS n.val n.property
      have hd0 : 0 < d n := Nat.pos_of_ne_zero (hd n).2.1.ne_zero
      have hrepr := Nat.div_mul_cancel (hd n).1
      apply mem_Icc.mpr
      refine ⟨Nat.div_pos (Nat.le_of_dvd hn.1 (hd n).1) hd0, ?_⟩
      apply (Nat.le_div_iff_mul_le hL).mpr
      calc
        n.val / d n * L ≤ n.val / d n * d n :=
          Nat.mul_le_mul_left _ (hd n).2.2.2.1
        _ = n.val := hrepr
        _ ≤ X := hn.2.1
    · intro n _ k _ hsame
      change n.val / d n = k.val / d k at hsame
      have hn := hS n.val n.property
      have hk := hS k.val k.property
      have hnd := hd n
      have hkd := hd k
      have hnr := Nat.div_mul_cancel hnd.1
      have hkr := Nat.div_mul_cancel hkd.1
      have hm : 1 < n.val / d n := by
        have hd0 : 0 < d n := Nat.pos_of_ne_zero hnd.2.1.ne_zero
        have hm0 := Nat.div_pos (Nat.le_of_dvd hn.1 hnd.1) hd0
        have hdlt := hnd.2.2.2.2.2
        nlinarith
      have heq : d n = d k := by
        apply unitary_squarefree_fiber_unique hm hnd.2.1 hkd.2.1
          hnd.2.2.2.2.1 hkd.2.2.2.2.1 hnd.2.2.1
        · simpa only [hsame] using hkd.2.2.1
        · simpa only [hnr] using hn.2.2.1
        · simpa only [hsame, hkr] using hk.2.2.1
        · simpa only [hnr] using hn.2.2.2
        · simpa only [hsame, hkr] using hk.2.2.2
      apply Subtype.ext
      calc
        n.val = n.val / d n * d n := hnr.symm
        _ = k.val / d k * d k := by rw [hsame, heq]
        _ = k.val := hkr
  simpa using hcard

private lemma counting_parameter {X : ℕ} (hX : 1 ≤ X) :
    ∃ M : ℕ, 100 ≤ M ∧ X ≤ M ^ 40 ∧
      (M : ℝ) ^ 39 ≤ 102 ^ 39 * (X : ℝ) ^ (39 / 40 : ℝ) := by
  let r : ℝ := (X : ℝ) ^ (1 / 40 : ℝ)
  let M : ℕ := ⌈r⌉₊ + 100
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hr : 1 ≤ r := Real.one_le_rpow hX1 (by norm_num)
  have hr0 : 0 ≤ r := by linarith
  have hceil := Nat.le_ceil r
  have hceil' := Nat.ceil_lt_add_one hr0
  have hM : (M : ℝ) ≤ 102 * r := by
    dsimp only [M]
    push_cast
    linarith
  have hr40 : r ^ 40 = (X : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X)]
    norm_num
  have hr39 : r ^ 39 = (X : ℝ) ^ (39 / 40 : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X)]
    norm_num
  refine ⟨M, by dsimp [M]; omega, ?_, ?_⟩
  · have hrM : r ≤ (M : ℝ) := by
      dsimp only [M]
      push_cast
      linarith
    have hh : (X : ℝ) ≤ (M : ℝ) ^ 40 := by
      rw [← hr40]
      exact pow_le_pow_left₀ hr0 hrM 40
    exact_mod_cast hh
  · calc
      (M : ℝ) ^ 39 ≤ (102 * r) ^ 39 :=
        pow_le_pow_left₀ (Nat.cast_nonneg M) hM 39
      _ = _ := by rw [mul_pow, hr39]

private def exceptions (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun n => PrimitiveNonDeficient n ∧ n ∉ radicalComponentSet 2

private def compressible (M : ℕ) : Finset ℕ :=
  (exceptions (M ^ 40)).filter fun n => M ^ 39 < n ∧ n ∉ largeSquares (M ^ 40) M

private lemma compressible_card {M : ℕ} (hM : 100 ≤ M) :
    (compressible M).card ≤ M ^ 39 := by
  have hM0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  have h4 : M ^ 4 ≤ M ^ 39 := Nat.pow_le_pow_right hM0 (by decide)
  have h8 : M ^ 8 ≤ M ^ 39 := Nat.pow_le_pow_right hM0 (by decide)
  have h39 : 1 ≤ M ^ 39 := one_le_pow₀ hM1
  have hcount := compression_card (compressible M) (M ^ 40) M (M ^ 8) hM0
    (by
      intro n hn
      obtain ⟨hnS, hnlo, hnnot⟩ := mem_filter.mp hn
      obtain ⟨hnI, hC, hB⟩ := mem_filter.mp hnS
      obtain ⟨hn0, hnhi⟩ := mem_Icc.mp hnI
      have hn2 : 2 ≤ n := by omega
      refine ⟨hn0, hnhi, hC, ?_⟩
      exact primitive_ratio_narrow (by omega) hn2 hC
        (exception_large_prime_power (by omega) hnlo hnhi hnnot hB))
    (by
      intro n hn
      obtain ⟨hnS, hnlo, hnnot⟩ := mem_filter.mp hn
      obtain ⟨hnI, hC, _⟩ := mem_filter.mp hnS
      obtain ⟨hn0, hnhi⟩ := mem_Icc.mp hnI
      obtain ⟨a, b, ha, hb, hbM, he⟩ :=
        ZelinskyRadicalComponentDensity.square_decomposition_small hn0 hnhi hnnot
      obtain ⟨d, hd, hsq, hcop, hdM, hd8⟩ :=
        small_unitary_factor hM ha hb hbM he (h4.trans_lt hnlo) hnhi hC
      exact ⟨d, hd, hsq, hcop.symm, hdM, hd8, (hd8.trans h8).trans_lt hnlo⟩)
  have heq : M ^ 40 / M = M ^ 39 := by
    rw [show M ^ 40 = M ^ 39 * M by ring, Nat.mul_div_left _ hM0]
  rwa [heq] at hcount

private lemma parameter_count {M : ℕ} (hM : 100 ≤ M) :
    ((exceptions (M ^ 40)).card : ℝ) ≤ 4 * (M : ℝ) ^ 39 := by
  have hcover : exceptions (M ^ 40) ⊆
      (Icc 1 (M ^ 39) ∪ largeSquares (M ^ 40) M) ∪ compressible M := by
    intro n hn
    by_cases hnlo : n ≤ M ^ 39
    · exact mem_union_left _ (mem_union_left _
        (mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hn).1).1, hnlo⟩))
    · by_cases hnlarge : n ∈ largeSquares (M ^ 40) M
      · exact mem_union_left _ (mem_union_right _ hnlarge)
      · exact mem_union_right _ (mem_filter.mpr ⟨hn, by omega, hnlarge⟩)
  have hcard : (exceptions (M ^ 40)).card ≤
      (Icc 1 (M ^ 39)).card + (largeSquares (M ^ 40) M).card +
        (compressible M).card :=
    (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hcardR : ((exceptions (M ^ 40)).card : ℝ) ≤
      (M : ℝ) ^ 39 + (largeSquares (M ^ 40) M).card + (M : ℝ) ^ 39 := by
    have hn := hcard.trans (Nat.add_le_add_left (compressible_card hM) _)
    simpa only [Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_pow] using
      (show ((exceptions (M ^ 40)).card : ℝ) ≤
        ((Icc 1 (M ^ 39)).card + (largeSquares (M ^ 40) M).card + M ^ 39 : ℕ) from
          by exact_mod_cast hn)
  have hsq := largeSquares_card (M ^ 40) M
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hsquare : (2 * ((M ^ 40 : ℕ) : ℝ)) / (M + 1) ≤ 2 * (M : ℝ) ^ 39 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < M + 1)).mpr
    push_cast
    nlinarith [pow_nonneg hM0.le 39]
  linarith

/-- A uniform power saving for the positive primitive radical-component exceptions. -/
theorem exceptional_bound : ∃ K : ℝ, 0 < K ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    (((Icc 1 X).filter fun n =>
      PrimitiveNonDeficient n ∧ n ∉ radicalComponentSet 2).card : ℝ) ≤
        K * (X : ℝ) ^ (39 / 40 : ℝ) := by
  refine ⟨4 * 102 ^ 39, by positivity, 1, ?_⟩
  intro X hX
  obtain ⟨M, hM, hXM, hbound⟩ := counting_parameter hX
  have hsub : exceptions X ⊆ exceptions (M ^ 40) := by
    intro n hn
    obtain ⟨hnI, hC⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr
      ⟨(mem_Icc.mp hnI).1, (mem_Icc.mp hnI).2.trans hXM⟩, hC⟩
  have hcard : ((exceptions X).card : ℝ) ≤ (exceptions (M ^ 40)).card := by
    exact_mod_cast card_le_card hsub
  change ((exceptions X).card : ℝ) ≤ _
  calc
    _ ≤ 4 * (M : ℝ) ^ 39 := hcard.trans (parameter_count hM)
    _ ≤ _ := by nlinarith

/-- A lower counting bound makes the primitive exceptional set negligible. -/
theorem relative_density_one (S : Set ℕ)
    (hS : ∀ n ∈ S, PrimitiveNonDeficient n)
    (hlower : ∀ᶠ X : ℕ in atTop,
      (X : ℝ) ^ (79 / 80 : ℝ) ≤ (count S X : ℝ)) :
    Tendsto (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩ S) X : ℝ) / count S X) atTop (𝓝 1) := by
  obtain ⟨K, hK, X₀, hbound⟩ := exceptional_bound
  have hzero : Tendsto (fun X : ℕ => K * (X : ℝ) ^ (-(1 / 80 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 80)).comp
        tendsto_natCast_atTop_atTop))
  have hezero : Tendsto (fun X : ℕ =>
      (count (S \ radicalComponentSet 2) X : ℝ) / count S X) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hzero
    filter_upwards [hlower, eventually_ge_atTop X₀, eventually_ge_atTop (1 : ℕ)]
      with X hlow hX₀ hX
    have hx : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hden : (0 : ℝ) < count S X := (rpow_pos_of_pos hx _).trans_le hlow
    have hsubset : count (S \ radicalComponentSet 2) X ≤
        ((Icc 1 X).filter fun n =>
          PrimitiveNonDeficient n ∧ n ∉ radicalComponentSet 2).card := by
      unfold count
      apply card_le_card
      intro n hn
      simp only [mem_filter, Set.mem_sdiff] at hn ⊢
      exact ⟨hn.1, hS n hn.2.1, hn.2.2⟩
    have hcard : (count (S \ radicalComponentSet 2) X : ℝ) ≤
        (((Icc 1 X).filter fun n =>
          PrimitiveNonDeficient n ∧ n ∉ radicalComponentSet 2).card : ℝ) := by
      exact_mod_cast hsubset
    have he : (count (S \ radicalComponentSet 2) X : ℝ) ≤
        K * (X : ℝ) ^ (39 / 40 : ℝ) := hcard.trans (hbound X hX₀)
    calc
      _ ≤ (K * (X : ℝ) ^ (39 / 40 : ℝ)) / count S X :=
        div_le_div_of_nonneg_right he hden.le
      _ ≤ (K * (X : ℝ) ^ (39 / 40 : ℝ)) / (X : ℝ) ^ (79 / 80 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (rpow_pos_of_pos hx _) hlow
      _ = K * (X : ℝ) ^ (-(1 / 80 : ℝ)) := by
        rw [mul_div_assoc, ← rpow_sub hx]
        norm_num
  have hlim := tendsto_const_nhds.sub hezero
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [hlower, eventually_ge_atTop (1 : ℕ)] with X hlow hX
  have hx : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hden : (count S X : ℝ) ≠ 0 := ne_of_gt ((rpow_pos_of_pos hx _).trans_le hlow)
  have hcard : count (radicalComponentSet 2 ∩ S) X +
      count (S \ radicalComponentSet 2) X = count S X := by
    unfold count
    rw [← card_union_of_disjoint (disjoint_left.mpr (by
      intro n hn hs
      simp only [mem_filter, Set.mem_inter_iff, Set.mem_sdiff] at hn hs
      exact hs.2.2 hn.2.1)), ← filter_or]
    congr 1
    ext n
    simp only [Set.mem_inter_iff, Set.mem_sdiff, mem_filter]
    tauto
  have hcardR : (count (radicalComponentSet 2 ∩ S) X : ℝ) +
      count (S \ radicalComponentSet 2) X = count S X := by exact_mod_cast hcard
  field_simp
  linarith

/-- Conjecture 11 in the source, with denominator C(X). -/
def claim : Prop :=
  Tendsto (fun X : ℕ =>
    (count (radicalComponentSet 2 ∩ {n | PrimitiveNonDeficient n}) X : ℝ) /
      count {n | PrimitiveNonDeficient n} X) atTop (𝓝 0)

/-- The relative density is one, contradicting Conjecture 11. -/
theorem result : ¬ claim := by
  intro hclaim
  have hlower : ∀ᶠ X : ℕ in atTop, (X : ℝ) ^ (79 / 80 : ℝ) ≤
      (count {n | PrimitiveNonDeficient n} X : ℝ) := by
    obtain ⟨X₀, hX₀⟩ := ZelinskyZhangDoublePrimitive.rough_primitive_lower_bound
      ∅ (by simp)
    filter_upwards [eventually_ge_atTop X₀] with X hX
    exact (hX₀ X hX).trans (by
      exact_mod_cast (card_le_card (show
        (Icc 1 X).filter (fun n => Odd n ∧ Squarefree n ∧ PrimitiveNonDeficient n ∧
          ∀ p ∈ (∅ : Finset ℕ), ¬ p ∣ n) ⊆
          (Icc 1 X).filter (fun n => PrimitiveNonDeficient n) from by
        intro n hn
        obtain ⟨hnI, _, _, hnC, _⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨hnI, hnC⟩)))
  have hone := relative_density_one {n | PrimitiveNonDeficient n} (fun _ hn => hn) hlower
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique hone hclaim
  norm_num at hbad

end D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture11
