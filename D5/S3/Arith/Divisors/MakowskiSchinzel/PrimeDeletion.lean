/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Prime-source deletion inequalities for minimal sigma-totient counterexamples. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.Reduction
import D5.S3.Factorization.LehmerTotientDichotomy
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators

namespace D5.S3.Arith.MakowskiSchinzel

open Finset

private theorem abundancy_mul {a b : ℕ} (h : a.Coprime b) :
    (a * b).abundancyIndex = a.abundancyIndex * b.abundancyIndex := by
  simp only [Nat.abundancyIndex, h.sum_divisors_mul, Nat.cast_mul, mul_div_mul_comm]

private theorem abundancy_prime_pow {r : ℕ} (hr : r.Prime) (k : ℕ) :
    (r ^ k).abundancyIndex = geom r k := by
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  rw [Nat.abundancyIndex, Nat.sum_divisors_prime_pow hr, Nat.cast_sum, sum_div]
  rw [← sum_range_reflect (fun i => ((r ^ i : ℕ) : ℚ) / (r ^ k : ℕ)) (k + 1)]
  unfold geom
  apply sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have := mem_range.mp hi; omega
  simp only [Nat.add_sub_cancel, Nat.cast_pow, inv_pow]
  rw [← one_div]
  apply (div_eq_div_iff (pow_ne_zero k hrq) (pow_ne_zero i hrq)).mpr
  rw [← pow_add, Nat.sub_add_cancel hik, one_mul]

/-- Prime factors whose predecessors are divisible by `r`. -/
def primeSources (n r : ℕ) : Finset ℕ := n.primeFactors.filter fun q => r ∣ q - 1

private theorem geom_abundancy_le {r a b k : ℕ} (hr : r.Prime)
    (hcop : r.Coprime a) (hb : b ≠ 0) (hdiv : r ^ k * a ∣ b) :
    geom r k * a.abundancyIndex ≤ b.abundancyIndex := by
  rw [← abundancy_prime_pow hr, ← abundancy_mul (hcop.pow_left k)]
  exact Nat.abundancyIndex_le_of_dvd hb hdiv

/-- Every totient prime source in a minimal counterexample beats its geometric factor. -/
theorem prime_deletion_necessary {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime)
    (hrphi : r ∣ m.totient) (hbad : alpha m < 1)
    (hmin : ∀ d : ℕ, d ∣ m → d < m → 1 ≤ alpha d) :
    geom r (primeSources m r).card <
      ∏ q ∈ primeSources m r, (q : ℚ) / (q - 1 : ℕ) := by
  classical
  have hsq : Squarefree m := by
    have hle : UniqueFactorizationMonoid.radical m ≤ m :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hm) UniqueFactorizationMonoid.radical_dvd_self
    have heq : UniqueFactorizationMonoid.radical m = m := by
      by_contra hne
      have hlt : UniqueFactorizationMonoid.radical m < m := by omega
      have hh := hmin _ UniqueFactorizationMonoid.radical_dvd_self hlt
      have hrad := alpha_radical_le hm
      linarith
    rw [← heq]
    exact UniqueFactorizationMonoid.squarefree_radical
  let P := m.primeFactors
  let Q := primeSources m r
  let B := P \ Q
  let d := ∏ p ∈ B, p
  have hp (p : ℕ) (hp : p ∈ P) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hsub : Q ⊆ P := filter_subset _ _
  have hd0 : d ≠ 0 := (prod_pos fun p hp' => (hp p (mem_sdiff.mp hp').1).pos).ne'
  have hdmul : d * (∏ p ∈ Q, p) = m :=
    (prod_sdiff hsub).trans (Nat.prod_primeFactors_of_squarefree hsq)
  have hddvd : d ∣ m := ⟨_, hdmul.symm⟩
  have hpd : d.primeFactors = B :=
    Nat.primeFactors_prod fun p hp' => hp p (mem_sdiff.mp hp').1
  have hphid : d.totient = ∏ p ∈ B, (p - 1) := by
    rw [D5.S3.Factorization.LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod
      hd0 (hsq.squarefree_of_dvd hddvd), hpd]
  have hphim : m.totient = ∏ p ∈ P, (p - 1) :=
    D5.S3.Factorization.LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod hm hsq
  have hnonempty : Q.Nonempty := by
    have hdiv : r ∣ ∏ p ∈ P, (p - 1) := hphim ▸ hrphi
    obtain ⟨q, hq, hrq⟩ := ((Nat.prime_iff.mp hr).dvd_finsetProd_iff _).mp hdiv
    exact ⟨q, mem_filter.mpr ⟨hq, hrq⟩⟩
  have hdlt : d < m := by
    obtain ⟨q, hq⟩ := hnonempty
    have hqle : q ≤ ∏ p ∈ Q, p := Nat.le_of_dvd
      (prod_pos fun p hp' => (hp p (hsub hp')).pos) (dvd_prod_of_mem _ hq)
    have hq2 := (hp q (hsub hq)).two_le
    have hdpos := Nat.pos_of_ne_zero hd0
    nlinarith [hdmul]
  have hcop : r.Coprime d.totient := by
    rw [hphid]
    apply Nat.Coprime.prod_right
    intro q hq
    apply hr.coprime_iff_not_dvd.mpr
    intro hrq
    exact (mem_sdiff.mp hq).2 (mem_filter.mpr ⟨(mem_sdiff.mp hq).1, hrq⟩)
  have hpowdiv : r ^ Q.card ∣ m.totient := by
    have hlocal : (∏ _q ∈ Q, r) ∣ ∏ q ∈ Q, (q - 1) :=
      prod_dvd_prod_of_dvd _ _ fun q hq => (mem_filter.mp hq).2
    simp only [prod_const] at hlocal
    rw [hphim]
    apply hlocal.trans
    refine ⟨∏ p ∈ B, (p - 1), ?_⟩
    rw [mul_comm]
    exact (prod_sdiff hsub).symm
  have hjoin : r ^ Q.card * d.totient ∣ m.totient :=
    (hcop.pow_left _).mul_dvd_of_dvd_of_dvd hpowdiv (Nat.totient_dvd_of_dvd hddvd)
  have hg := geom_abundancy_le hr hcop
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)).ne' hjoin
  have hw (q : ℕ) (hq : q ∈ P) : 0 ≤ 1 - (q : ℚ)⁻¹ := by
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (hp q hq).one_lt.le)
  have hwB : 0 ≤ ∏ p ∈ B, (1 - (p : ℚ)⁻¹) :=
    prod_nonneg fun p hp' => hw p (mem_sdiff.mp hp').1
  have hwQ : 0 ≤ ∏ p ∈ Q, (1 - (p : ℚ)⁻¹) :=
    prod_nonneg fun p hp' => hw p (hsub hp')
  have ha : geom r Q.card * alpha d * (∏ p ∈ Q, (1 - (p : ℚ)⁻¹)) ≤ alpha m := by
    rw [alpha_factorization d, alpha_factorization m, hpd,
      ← prod_sdiff hsub]
    have hh := mul_le_mul_of_nonneg_right hg (mul_nonneg hwB hwQ)
    convert hh using 1 <;> ring
  have hG : 0 ≤ geom r Q.card := by
    unfold geom
    exact sum_nonneg fun _ _ => by positivity
  have hsmall : geom r Q.card * (∏ p ∈ Q, (1 - (p : ℚ)⁻¹)) < 1 := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmin d hddvd hdlt) hG) hwQ
    simp only [mul_one] at hh
    exact (hh.trans ha).trans_lt hbad
  have hRpos : 0 < ∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ) := by
    apply prod_pos
    intro q hq
    have hq2 := (hp q (hsub hq)).two_le
    apply div_pos
    · exact_mod_cast (hp q (hsub hq)).pos
    · exact_mod_cast (show 0 < q - 1 by omega)
  have hcancel : (∏ q ∈ Q, (1 - (q : ℚ)⁻¹)) *
      (∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ)) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro q hq
    have hq2 := (hp q (hsub hq)).two_le
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hq1 : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 :=
      Nat.cast_sub (by omega)
    have hq1ne : (q : ℚ) - 1 ≠ 0 := by
      have hqrat : (2 : ℚ) ≤ q := by exact_mod_cast hq2
      linarith
    rw [hq1]
    field_simp [hq0, hq1ne]
  have hh := mul_lt_mul_of_pos_right hsmall hRpos
  rw [mul_assoc, hcancel, mul_one, one_mul] at hh
  exact hh

#print axioms prime_deletion_necessary

end D5.S3.Arith.MakowskiSchinzel
