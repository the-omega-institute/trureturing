/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/SmoothedGroups
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/SmoothedGroups
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: Finite table labels and smooth tail labels bound every actual finite prime set. -/

import D5.S3.Arith.Robin.PaddingRatio
import Mathlib.Data.Nat.MaxPrimeFac
import D5.S3.Factorization.JordanCototientRecordLimitInfinity
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.LocalGroup
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants

/-! The finite certificates and the Euler-product estimate cover unbounded actual inputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

open Finset

/-- The geometric sigma factor in the integer cross-multiplication format of `prefixOk`. -/
private theorem geom_closed {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    geom p k = ((p : ℚ) ^ (k + 1) - 1) / (((p : ℚ) - 1) * (p : ℚ) ^ k) := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (p : ℚ) ≠ 0 := by linarith
  have hp1 : (p : ℚ) - 1 ≠ 0 := by linarith
  have h1p : (1 : ℚ) - p ≠ 0 := by linarith
  have hi : (p : ℚ)⁻¹ ≠ 1 := by
    intro h
    have := inv_mul_cancel₀ hp0
    rw [h, one_mul] at this
    linarith
  rw [geom, geom_sum_eq hi]
  simp only [inv_pow, pow_succ]
  field_simp [hp0, hp1, h1p]
  <;> ring

/-- Euler-product tail allowance after the finite smooth reciprocal sum is subtracted. -/
private def tailBound (p : ℕ) (t : ℕ × ℕ × ℕ) : ℚ :=
  (t.1 : ℚ) / (t.2.1 * 2 * p) - (t.2.2 : ℚ) / scale

/-- Every successful prefix check implies the two uncapped rational product bounds. -/
private theorem prefixOk_bounds {p j L : ℕ} {t : ℕ × ℕ × ℕ}
    (hp : 2 ≤ p) (hden : 0 < t.2.1) (hc : prefixOk p j L t = true) :
    (j = 0 ∨ 1 ≤ geom p j * ((L : ℚ) / scale)) ∧
      0 ≤ 1 - tailBound p t ∧
      1 ≤ geom p (j + 1) * ((L : ℚ) / scale) * (1 - tailBound p t) := by
  let D := t.2.1 * 2 * p * scale
  let A := D + t.2.2 * t.2.1 * 2 * p
  have hchecks :
      ((j = 0 ∨ scale * (p - 1) * p ^ min j expCap ≤
        (p ^ (min j expCap + 1) - 1) * L) ∧ t.1 * scale ≤ A) ∧
      scale * (p - 1) * p ^ min (j + 1) expCap * D ≤
        (p ^ (min (j + 1) expCap + 1) - 1) * L * (A - t.1 * scale) := by
    simpa only [prefixOk, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq, decide_eq_true_eq, D, A] using hc
  have hs : (0 : ℚ) < scale := by norm_num [scale]
  have hpq : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
  have hdq : (0 : ℚ) < t.2.1 := by exact_mod_cast hden
  have hD : (0 : ℚ) < D := by dsimp [D]; push_cast; positivity
  have hgeom (k : ℕ) :
      geom p k * ((p - 1) * p ^ k : ℕ) = (p ^ (k + 1) - 1 : ℕ) := by
    have hp1 : 1 ≤ p := by omega
    have hpK : 1 ≤ p ^ (k + 1) := one_le_pow₀ hp1
    have hpne : (p : ℚ) - 1 ≠ 0 := by
      have : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
      linarith
    rw [geom_closed hp]
    push_cast [Nat.cast_sub hp1, Nat.cast_sub hpK]
    field_simp [hpne]
  have hpos (k : ℕ) : (0 : ℚ) < ((p - 1) * p ^ k : ℕ) := by
    exact_mod_cast Nat.mul_pos (show 0 < p - 1 by omega) (pow_pos (by omega) k)
  have hmono {a b : ℕ} (hab : a ≤ b) : geom p a ≤ geom p b := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [geom, Rat.cast_sum, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast,
      D5.S3.Arith.RobinExponentSwap.reciprocalGeomSum] using
      (D5.S3.Arith.Robin.PaddingRatio.geom_mono (p := p) hab)
  have hB : ((A - t.1 * scale : ℕ) : ℚ) / D = 1 - tailBound p t := by
    rw [Nat.cast_sub hchecks.1.2]
    dsimp [A, D, tailBound]
    push_cast
    field_simp
    <;> ring
  have htail : 0 ≤ 1 - tailBound p t := by
    rw [← hB]
    positivity
  have hL : (0 : ℚ) ≤ (L : ℚ) / scale := by positivity
  refine ⟨?_, htail, ?_⟩
  · rcases hchecks.1.1 with hz | hz
    · exact Or.inl hz
    · right
      have hn : (scale : ℚ) * ((p - 1) * p ^ min j expCap : ℕ) ≤
          (p ^ (min j expCap + 1) - 1 : ℕ) * (L : ℚ) := by
        exact_mod_cast (by simpa only [mul_assoc] using hz)
      rw [← hgeom] at hn
      have hb : (scale : ℚ) ≤ geom p (min j expCap) * L := by
        nlinarith [hpos (min j expCap)]
      have hb' : 1 ≤ geom p (min j expCap) * ((L : ℚ) / scale) := by
        rw [← mul_div_assoc, le_div_iff₀ hs, one_mul]
        exact hb
      exact hb'.trans (mul_le_mul_of_nonneg_right (hmono (min_le_left _ _)) hL)
  · have hn : (scale : ℚ) * ((p - 1) * p ^ min (j + 1) expCap : ℕ) * D ≤
        (p ^ (min (j + 1) expCap + 1) - 1 : ℕ) * (L : ℚ) *
          (A - t.1 * scale : ℕ) := by
      exact_mod_cast (by simpa only [mul_assoc] using hchecks.2)
    rw [← hgeom] at hn
    have hb : (scale : ℚ) * D ≤
        geom p (min (j + 1) expCap) * L * (A - t.1 * scale : ℕ) := by
      nlinarith [hpos (min (j + 1) expCap)]
    have hb' : 1 ≤ geom p (min (j + 1) expCap) *
        ((L : ℚ) / scale) * (1 - tailBound p t) := by
      rw [← hB]
      rw [show geom p (min (j + 1) expCap) * ((L : ℚ) / scale) *
        (((A - t.1 * scale : ℕ) : ℚ) / D) =
        (geom p (min (j + 1) expCap) * L * (A - t.1 * scale : ℕ)) /
          ((scale : ℚ) * D) by ring]
      rw [le_div_iff₀ (mul_pos hs hD), one_mul]
      exact hb
    exact hb'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hmono (min_le_left _ _)) hL) htail)

/-- A checked prefix and a reciprocal tail estimate control any actual finite group. -/
private theorem checked_group_bound {p L : ℕ} {t : ℕ × ℕ × ℕ}
    (hp : 2 ≤ p) (hden : 0 < t.2.1) (F T : Finset ℕ) (hdis : Disjoint F T)
    (hc : prefixOk p F.card L t = true)
    (hF : (L : ℝ) / scale ≤ ∏ q ∈ F, (1 - (q : ℝ)⁻¹))
    (hT : ∑ q ∈ T, (q : ℝ)⁻¹ ≤ (tailBound p t : ℝ)) :
    1 ≤ (geom p (F.card + T.card) : ℝ) *
      ∏ q ∈ F ∪ T, (1 - (q : ℝ)⁻¹) := by
  have hg0 (k : ℕ) : (0 : ℝ) ≤ (geom p k : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ geom p k from
      sum_nonneg fun i _ => by positivity)
  have hmono {a b : ℕ} (hab : a ≤ b) : (geom p a : ℝ) ≤ (geom p b : ℝ) := by
    simpa only [geom, Rat.cast_sum, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast,
      D5.S3.Arith.RobinExponentSwap.reciprocalGeomSum] using
      (D5.S3.Arith.Robin.PaddingRatio.geom_mono (p := p) hab)
  have hx0 (q : ℕ) : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  have hx1 (q : ℕ) : (q : ℝ)⁻¹ ≤ 1 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · apply inv_le_one_of_one_le₀
      exact_mod_cast (show 1 ≤ q by omega)
  have hPF0 : (0 : ℝ) ≤ ∏ q ∈ F, (1 - (q : ℝ)⁻¹) := by
    apply prod_nonneg
    intro q hq'
    exact sub_nonneg.mpr (hx1 q)
  have hL0 : (0 : ℝ) ≤ (L : ℝ) / scale := by positivity
  obtain ⟨hfirst, htail0, hlast⟩ := prefixOk_bounds hp hden hc
  have htail0' : (0 : ℝ) ≤ 1 - (tailBound p t : ℝ) := by exact_mod_cast htail0
  rw [prod_union hdis]
  by_cases hTempty : T = ∅
  · subst T
    simp only [card_empty, Nat.add_zero, prod_empty, mul_one]
    rcases hfirst with hz | hz
    · have hFe : F = ∅ := card_eq_zero.mp hz
      simp [hFe, geom]
    · have hz' : (1 : ℝ) ≤ (geom p F.card : ℝ) * ((L : ℝ) / scale) := by
        have hh := (Rat.cast_le (K := ℝ)).mpr hz
        simpa only [Rat.cast_one, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] using hh
      exact hz'.trans (mul_le_mul_of_nonneg_left hF (hg0 _))
  · have hTc : 1 ≤ T.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hTempty)
    have hPT : 1 - (tailBound p t : ℝ) ≤ ∏ q ∈ T, (1 - (q : ℝ)⁻¹) := by
      have hh := D5.S3.Factorization.JordanCototientRecordLimitInfinity.one_sub_prod_le_sum
        T (fun q : ℕ => (q : ℝ)⁻¹) (fun q _ => hx0 q)
        (fun q hq' => hx1 q)
      linarith
    have hb : (1 : ℝ) ≤ (geom p (F.card + 1) : ℝ) *
        ((L : ℝ) / scale) * (1 - (tailBound p t : ℝ)) := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hlast
      simpa only [Rat.cast_one, Rat.cast_mul, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_sub] using hh
    calc
      1 ≤ (geom p (F.card + 1) : ℝ) *
          ((L : ℝ) / scale) * (1 - (tailBound p t : ℝ)) := hb
      _ ≤ (geom p (F.card + T.card) : ℝ) *
          ((L : ℝ) / scale) * (1 - (tailBound p t : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hmono (by omega)) hL0) htail0'
      _ ≤ (geom p (F.card + T.card) : ℝ) *
          ((∏ q ∈ F, (1 - (q : ℝ)⁻¹)) * ∏ q ∈ T, (1 - (q : ℝ)⁻¹)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hF hPT htail0' hPF0) (hg0 _)


/-- Labelled local bounds imply the global sigma-factor inequality with actual valuations. -/
private theorem grouped_product_of_local (Q P : Finset ℕ) (label : ℕ → ℕ)
    (hQ : ∀ q ∈ Q, 2 ≤ q) (hP : ∀ p ∈ P, p.Prime)
    (hlabel : ∀ q ∈ Q, label q ∈ P ∧ label q ∣ q - 1)
    (hlocal : ∀ p ∈ P,
      1 ≤ (geom p (Q.filter (fun q => label q = p)).card : ℝ) *
        ∏ q ∈ Q.filter (fun q => label q = p), (1 - (q : ℝ)⁻¹)) :
    (∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ)) ≤
      ∏ p ∈ P, geom p (∑ q ∈ Q, (q - 1).factorization p) := by
  classical
  have hqsub (q : ℕ) (hq : q ∈ Q) : 0 < q - 1 := by
    have := hQ q hq
    omega
  have hbound (p : ℕ) (hp : p ∈ P) :
      (Q.filter (fun q => label q = p)).card ≤ ∑ q ∈ Q, (q - 1).factorization p := by
    calc
      _ = ∑ _q ∈ Q.filter (fun q => label q = p), 1 := by simp
      _ ≤ ∑ q ∈ Q.filter (fun q => label q = p), (q - 1).factorization p := by
        apply sum_le_sum
        intro q hq
        obtain ⟨hq, hl⟩ := mem_filter.mp hq
        apply (hP p hp).factorization_pos_of_dvd (hqsub q hq).ne'
        simpa only [hl] using (hlabel q hq).2
      _ ≤ ∑ q ∈ Q, (q - 1).factorization p :=
        sum_le_sum_of_subset (filter_subset _ _)
  have hmono (p : ℕ) (hp : p ∈ P) :
      geom p (Q.filter (fun q => label q = p)).card ≤
        geom p (∑ q ∈ Q, (q - 1).factorization p) := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [geom, Rat.cast_sum, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast,
      D5.S3.Arith.RobinExponentSwap.reciprocalGeomSum] using
      (D5.S3.Arith.Robin.PaddingRatio.geom_mono (p := p) (hbound p hp))
  have hlocal' (p : ℕ) (hp : p ∈ P) :
      (1 : ℚ) ≤ geom p (∑ q ∈ Q, (q - 1).factorization p) *
        ∏ q ∈ Q.filter (fun q => label q = p), (1 - (q : ℚ)⁻¹) := by
    have hh : (1 : ℚ) ≤ geom p (Q.filter (fun q => label q = p)).card *
        ∏ q ∈ Q.filter (fun q => label q = p), (1 - (q : ℚ)⁻¹) := by
      apply (Rat.cast_le (K := ℝ)).mp
      simpa only [Rat.cast_one, Rat.cast_mul, Rat.cast_prod,
        Rat.cast_sub, Rat.cast_inv, Rat.cast_natCast] using hlocal p hp
    apply hh.trans
    apply mul_le_mul_of_nonneg_right (hmono p hp)
    apply prod_nonneg
    intro q hq
    apply sub_nonneg.mpr
    apply inv_le_one_of_one_le₀
    exact_mod_cast (by have := hQ q (mem_filter.mp hq).1; omega : 1 ≤ q)
  have hprod := one_le_prod₀ hlocal'
  rw [prod_mul_distrib,
    prod_fiberwise_of_maps_to (fun q hq => (hlabel q hq).1)] at hprod
  have hcancel : (∏ q ∈ Q, (1 - (q : ℚ)⁻¹)) *
      (∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ)) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro q hq
    have hq2 := hQ q hq
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by have := hQ q hq; omega)
    have hq1 : (q : ℚ) - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ q := by exact_mod_cast hq2
      linarith
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    field_simp [hq0, hq1]
  have hR0 : (0 : ℚ) ≤ ∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ) := by positivity
  have hh := mul_le_mul_of_nonneg_right hprod hR0
  rw [one_mul, mul_assoc, hcancel, mul_one] at hh
  exact hh


/-- Every odd non-power-of-two smooth predecessor has a smooth quotient label. -/
private theorem exists_smooth_label {q : ℕ} (hq : Odd q)
    (hpow : ¬∃ k : ℕ, q - 1 = 2 ^ k) (hsm : q - 1 ∈ Nat.smoothNumbers 98) :
    ∃ p ∈ oddPrimes, p.Prime ∧ p ∣ q - 1 ∧
      (q - 1) / (2 * p) ∈ Nat.smoothNumbers (p + 1) ∧
      q = 2 * p * ((q - 1) / (2 * p)) + 1 ∧
      (bound + 1 < q → bound / (2 * p) < (q - 1) / (2 * p)) := by
  have hq2 : 2 ≤ q := by
    have := Nat.ne_zero_of_mem_smoothNumbers hsm
    omega
  have hn0 : q - 1 ≠ 0 := by omega
  have hn1 : 1 < q - 1 := by
    by_contra hn
    apply hpow
    exact ⟨0, by simp; omega⟩
  let p := (q - 1).maxPrimeFac
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt hn1
  have hpd : p ∣ q - 1 := Nat.maxPrimeFac_dvd
  have hp2 : p ≠ 2 := by
    intro he
    apply hpow
    refine ⟨(q - 1).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hn0 ?_⟩
    intro r hr hrd
    have hrp : r ≤ p := Nat.le_maxPrimeFac hn0 hr hrd
    have hr2 := hr.two_le
    omega
  have hp98 : p < 98 := Nat.mem_smoothNumbers'.mp hsm p hp hpd
  have hlist : oddPrimes.toFinset =
      (range 98).filter (fun r => r.Prime ∧ r ≠ 2) := by decide
  have hpP : p ∈ oddPrimes := by
    apply List.mem_toFinset.mp
    rw [hlist]
    exact mem_filter.mpr ⟨mem_range.mpr hp98, hp, hp2⟩
  have h2d : 2 ∣ q - 1 := by
    obtain ⟨k, hk⟩ := hq
    exact ⟨k, by omega⟩
  have hcop : Nat.Coprime 2 p :=
    (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  have hdiv : 2 * p ∣ q - 1 := hcop.mul_dvd_of_dvd_of_dvd h2d hpd
  have hden : 0 < 2 * p := by have := hp.pos; omega
  have hdecomp : 2 * p * ((q - 1) / (2 * p)) = q - 1 := Nat.mul_div_cancel' hdiv
  refine ⟨p, hpP, hp, hpd, ?_, by omega, ?_⟩
  · apply Nat.mem_smoothNumbers'.mpr
    intro r hr hrd
    have hrd' : r ∣ q - 1 := hrd.trans (Nat.div_dvd_of_dvd hdiv)
    have hrp : r ≤ p := Nat.le_maxPrimeFac hn0 hr hrd'
    omega
  · intro hlarge
    apply (Nat.div_lt_iff_lt_mul hden).mpr
    rw [mul_comm, hdecomp]
    omega


/-- Every finite candidate set with smooth predecessors obeys the grouped bound. -/
theorem smooth_group_product (E : List ℕ) (tl : List (ℕ × ℕ × ℕ))
    (fs : List (ℕ × ℕ)) (hv : E.all validEntry = true)
    (hn : (E.map entryValue).Nodup)
    (hsOrder : ∀ i, (groupValues i E).Pairwise (· ≤ ·))
    (hcount : smoothSum candidateWeight allPrimes bound 2 ≤ E.length)
    (ht : oddPrimes.map tailData = tl)
    (hrun : stepTable tl E initialState = some fs) (hfinal : finalOk tl fs = true)
    (Q : Finset ℕ)
    (hsm : ∀ q ∈ Q, q - 1 ∈ Nat.smoothNumbers 98)
    (hc : ∀ q ∈ Q,
      (q - 1 ≤ bound → candidate (q - 1) = true) ∧
      (bound < q - 1 → Odd q ∧ ¬∃ k : ℕ, q - 1 = 2 ^ k)) :
    (∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ)) ≤
      ∏ p ∈ oddPrimes.toFinset, geom p (∑ q ∈ Q, (q - 1).factorization p) := by
  classical
  have hQ (q : ℕ) (hq : q ∈ Q) : 2 ≤ q := by
    have := Nat.ne_zero_of_mem_smoothNumbers (hsm q hq)
    omega
  have hspec (q : ℕ) (hq : q ∈ Q) : ∃ p ∈ oddPrimes, p.Prime ∧ p ∣ q - 1 ∧
      (q - 1 ≤ bound → ∃ e ∈ E, entryValue e = q ∧
        oddPrimes[entryLabel e]? = some p) ∧
      (bound < q - 1 → ∃ m : ℕ, bound / (2 * p) < m ∧
        q = 2 * p * m + 1 ∧ m ∈ Nat.smoothNumbers (p + 1)) := by
    by_cases hb : q - 1 ≤ bound
    · obtain ⟨e, he, heq⟩ :=
        (prime_mem_table E hv hn hcount).mpr
          ⟨hb, (hc q hq).1 hb, hsm q hq⟩
      have hv := List.all_eq_true.mp hv e he
      cases hlook : oddPrimes[entryLabel e]? with
      | none =>
        exact (Bool.false_ne_true (by simpa only [validEntry, hlook] using hv)).elim
      | some p =>
        have hdiv : (entryValue e - 1) % p = 0 := by
          have hv' := hv
          simp only [validEntry, hlook, Bool.and_eq_true, decide_eq_true_eq,
            beq_iff_eq] at hv'
          exact hv'.2
        have hpP := List.mem_of_getElem? hlook
        have hprime : p.Prime := by
          have hall : oddPrimes.all (fun r => decide r.Prime) = true := by decide
          exact of_decide_eq_true (List.all_eq_true.mp hall p hpP)
        refine ⟨p, hpP, hprime, ?_, ?_, ?_⟩
        · rw [← heq]
          exact Nat.dvd_of_mod_eq_zero hdiv
        · intro _
          exact ⟨e, he, heq, hlook⟩
        · intro hlarge
          omega
    · obtain ⟨p, hpP, hp, hpd, hquot, heq, hlarge⟩ :=
        exists_smooth_label ((hc q hq).2 (by omega)).1
          ((hc q hq).2 (by omega)).2 (hsm q hq)
      refine ⟨p, hpP, hp, hpd, ?_, ?_⟩
      · intro hsmall
        exact (hb hsmall).elim
      · intro _
        exact ⟨(q - 1) / (2 * p), hlarge (by omega), heq, hquot⟩
  choose lab hlab using hspec
  let label : ℕ → ℕ := fun q => if hq : q ∈ Q then lab q hq else 2
  have hlabel (q : ℕ) (hq : q ∈ Q) := hlab q hq
  have hlabel_eq (q : ℕ) (hq : q ∈ Q) : label q = lab q hq := by simp [label, hq]
  have hP (p : ℕ) (hp : p ∈ oddPrimes.toFinset) : p.Prime := by
    have hall : oddPrimes.all (fun r => decide r.Prime) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hall p (List.mem_toFinset.mp hp))
  apply grouped_product_of_local Q oddPrimes.toFinset label hQ hP
  · intro q hq
    rw [hlabel_eq q hq]
    exact ⟨List.mem_toFinset.mpr (hlabel q hq).1, (hlabel q hq).2.2.1⟩
  · intro p hp
    let G := Q.filter (fun q => label q = p)
    let F := G.filter (fun q => q - 1 ≤ bound)
    let T := G.filter (fun q => bound < q - 1)
    have hG : G = F ∪ T := by
      ext q
      constructor
      · intro hq
        by_cases hb : q - 1 ≤ bound
        · exact mem_union_left _ (mem_filter.mpr ⟨hq, hb⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨hq, Nat.lt_of_not_ge hb⟩)
      · intro hq
        rcases mem_union.mp hq with hq | hq <;> exact (mem_filter.mp hq).1
    have hdis : Disjoint F T := by
      apply disjoint_left.mpr
      intro q hF hT
      exact (not_lt_of_ge (mem_filter.mp hF).2) (mem_filter.mp hT).2
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_toFinset.mp hp)
    have hFtable : ∀ q ∈ F, q ∈ groupValues i E := by
      intro q hqF
      obtain ⟨hqG, hsmall⟩ := mem_filter.mp hqF
      obtain ⟨hqQ, hql⟩ := mem_filter.mp hqG
      obtain ⟨e, he, heq, helook⟩ := (hlabel q hqQ).2.2.2.1 hsmall
      have hlp : lab q hqQ = p := (hlabel_eq q hqQ).symm.trans hql
      rw [hlp] at helook
      have hei : entryLabel e = i := by
        obtain ⟨helt, hev⟩ := List.getElem?_eq_some_iff.mp helook
        obtain ⟨hilt, hiv⟩ := List.getElem?_eq_some_iff.mp hi
        exact ((show oddPrimes.Nodup by decide).getElem_inj_iff
          (hi := helt) (hj := hilt)).mp (hev.trans hiv.symm)
      apply List.mem_map.mpr
      refine ⟨e, List.mem_filter.mpr ⟨he, by simp [hei]⟩, heq⟩
    let L := fixedProduct scale ((groupValues i E).take F.card)
    have hti : tl[i]? = some (tailData p) := by
      rw [← ht, List.getElem?_map, hi]
      rfl
    obtain ⟨hprefix, hfinite⟩ :=
      table_group_prefix_bound E tl fs (tailData p) F (hsOrder i) hrun
        (fun _ j L hj => finalOk_sound.mp hfinal i p j L _ hi hj hti) hi hti hFtable
    have hfinite' : (L : ℝ) / scale ≤ ∏ q ∈ F, (1 - (q : ℝ)⁻¹) := by
      apply hfinite.trans
      apply le_of_eq
      rw [Certificate.lowerProduct_sort, Rat.cast_prod]
      apply prod_congr rfl
      intro q hq
      have hq2 := hQ q (mem_filter.mp (mem_filter.mp hq).1).1
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_one]
      field_simp [hq0]
    have hp0 : 0 < p := (hP p hp).pos
    have htail : ∑ q ∈ T, (q : ℝ)⁻¹ ≤ (tailBound p (tailData p) : ℝ) := by
      have hmT : ∀ q ∈ T, ∃ m : ℕ, bound / (2 * p) < m ∧
          q = 2 * p * m + 1 ∧ m ∈ Nat.smoothNumbers (p + 1) := by
        intro q hqT
        obtain ⟨hqG, hlarge⟩ := mem_filter.mp hqT
        obtain ⟨hqQ, hql⟩ := mem_filter.mp hqG
        have hlp : lab q hqQ = p := (hlabel_eq q hqQ).symm.trans hql
        simpa only [hlp] using (hlabel q hqQ).2.2.2.2 hlarge
      have hfloor : ((tailData p).2.2 : ℝ) / scale ≤
          ∑ m ∈ (Icc 1 (bound / (2 * p))).filter
            (fun m => m ∈ Nat.smoothNumbers (p + 1)), 1 / (2 * (p : ℝ) * m) := by
        apply (tail_floor_sum_le p).trans
        apply sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨hmI, _, hf⟩ := mem_filter.mp hm
          refine mem_filter.mpr ⟨hmI, ?_⟩
          rw [Nat.smoothNumbers_eq_factoredNumbers_primesBelow]
          apply Nat.factoredNumbers_mono (s := (allPrimes.filter (· ≤ p)).toFinset) ?_
            (by simpa using hf)
          intro q hq
          have hqr := List.mem_filter.mp (List.mem_toFinset.mp hq)
          have hall : allPrimes.all (fun r => decide r.Prime) = true := by decide
          exact Nat.mem_primesLE.mpr ⟨of_decide_eq_true hqr.2,
            of_decide_eq_true (List.all_eq_true.mp hall q hqr.1)⟩
        · intros
          positivity
      have hh := (reciprocal_tail_bound hp0 T hmT hfloor).1
      have hp100 : p ≤ 100 := by
        have hmem := List.mem_toFinset.mp hp
        simp only [oddPrimes, List.mem_cons, List.not_mem_nil, or_false] at hmem
        omega
      rw [tail_euler_ratio.mpr hp100] at hh
      simpa only [one_div, tailBound, Rat.cast_sub, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat,
        Nat.cast_mul, Nat.cast_ofNat, div_div, mul_assoc] using hh
    have hden : 0 < (tailData p).2.1 := by
      have hps := List.mem_toFinset.mp hp
      simp only [oddPrimes, List.mem_cons, List.not_mem_nil, or_false] at hps
      rcases hps with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> decide +kernel
    have hh := checked_group_bound (hP p hp).two_le hden F T hdis hprefix hfinite' htail
    rw [← card_union_of_disjoint hdis, ← hG] at hh
    exact hh

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
