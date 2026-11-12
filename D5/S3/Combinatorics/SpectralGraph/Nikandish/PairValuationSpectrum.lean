/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairValuationSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairValuationSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd good-prime multiplicities exclude genuine low roots and actual integral graph spectra. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairLowArithmetic

/-! Source: four-prime-root-valuation, supplied PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. The coprimality here is
between the two tails. It differs from coprimality of their product
with the endpoint divisors. Valuations of signed offsets use natAbs.
All final consumers concern the actual four-prime ideal graph. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.PairValuationSpectrum
open PairedIdealIntersectionObstructions PairedIdealIntersectionLift
open IdealIntersectionSupport IdealIntersectionObstructions

theorem good_two (p : ℕ) (hp : p.Prime) (hl : 5≤p) :
    ¬(p:ℤ)∣(2:ℤ)*(2-1)*(2*2-1) := by
  intro hd
  have hn : p∣2*3 := by norm_num at hd; exact_mod_cast hd
  rcases hp.dvd_mul.mp hn with h | h
  · have hh:=Nat.le_of_dvd (by decide : 0<2) h; omega
  · have hh:=Nat.le_of_dvd (by decide : 0<3) h; omega

theorem good_three (p : ℕ) (hp : p.Prime) (hl : 7≤p) :
    ¬(p:ℤ)∣(3:ℤ)*(3-1)*(2*3-1) := by
  intro hd
  have hn : p∣(2*3)*5 := by norm_num at hd; exact_mod_cast hd
  rcases hp.dvd_mul.mp hn with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · have hh:=Nat.le_of_dvd (by decide : 0<2) h; omega
    · have hh:=Nat.le_of_dvd (by decide : 0<3) h; omega
  · have hh:=Nat.le_of_dvd (by decide : 0<5) h; omega

private theorem dvd_of_odd_valuation (p : ℕ) (z : ℤ)
    (h : Odd (padicValInt p z)) : (p:ℤ)∣z := by
  by_contra hn
  have hz:=padicValInt.eq_zero_of_not_dvd hn
  rw [hz] at h
  norm_num at h

/-- The two independent odd-multiplicity conditions exclude both
possible integer values of a genuine low restricted root. -/
theorem actual_odd_valuations (primes : Fin 4 → ℕ)
    (hp : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (a b c : ℕ) (ha : 5≤a) (hb : a≤b) (hc : a≤c)
    (hcop : Nat.Coprime b c) (p q : ℕ) (hpp : p.Prime) (hqp : q.Prime)
    (hpl : 5≤p) (hql : 7≤q)
    (hpo : Odd (padicValInt p ((a:ℤ)-1)))
    (hqo : Odd (padicValInt q ((a:ℤ)-2))) :
    ¬ActualLaplacianIntegral (modulus primes (pairExponents a b c)) := by
  intro H
  rcases PairLowArithmetic.actual_low_root primes hp hinj a b c ha hb hc H with h2 | h3
  · letI : Fact p.Prime := ⟨hpp⟩
    have hdiv : (p:ℤ)∣(a:ℤ)+1-2 := by
      convert dvd_of_odd_valuation p ((a:ℤ)-1) hpo using 1 <;> ring
    obtain ⟨hn,hv⟩:=PairRootArithmetic.root_valuation (a:ℤ) b c 2
      (by exact_mod_cast (show 0<a by omega))
      (by exact_mod_cast (show 0<b by omega))
      (by exact_mod_cast (show 0<c by omega)) (by norm_num)
      hcop.isCoprime p hdiv (good_two p hpp hpl) h2
    have he : (a:ℤ)+1-2=(a:ℤ)-1 := by ring
    rw [he] at hv
    obtain ⟨k,hk⟩:=hpo
    omega
  · letI : Fact q.Prime := ⟨hqp⟩
    have hdiv : (q:ℤ)∣(a:ℤ)+1-3 := by
      convert dvd_of_odd_valuation q ((a:ℤ)-2) hqo using 1 <;> ring
    obtain ⟨hn,hv⟩:=PairRootArithmetic.root_valuation (a:ℤ) b c 3
      (by exact_mod_cast (show 0<a by omega))
      (by exact_mod_cast (show 0<b by omega))
      (by exact_mod_cast (show 0<c by omega)) (by norm_num)
      hcop.isCoprime q hdiv (good_three q hqp hql) h3
    have he : (a:ℤ)+1-3=(a:ℤ)-2 := by ring
    rw [he] at hv
    obtain ⟨k,hk⟩:=hqo
    omega

/-- Both endpoint offsets have exactly first order on the full progression. -/
theorem progression_orders (n : ℕ) :
    padicValInt 5 (((156+2450*n : ℕ) : ℤ)-1)=1 ∧
      padicValInt 7 (((156+2450*n : ℕ) : ℤ)-2)=1 := by
  constructor
  · letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have he : ((156+2450*n:ℕ):ℤ)-1=5*(31+490*(n:ℤ)) := by push_cast; ring
    rw [he,padicValInt.mul (by norm_num) (by positivity),
      padicValInt.eq_zero_of_not_dvd (show ¬(5:ℤ)∣31+490*(n:ℤ) by omega)]
    simpa only [Nat.cast_ofNat, Nat.add_zero] using
      (padicValInt.self (p := 5) (by norm_num))
  · letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have he : ((156+2450*n:ℕ):ℤ)-2=7*(22+350*(n:ℤ)) := by push_cast; ring
    rw [he,padicValInt.mul (by norm_num) (by positivity),
      padicValInt.eq_zero_of_not_dvd (show ¬(7:ℤ)∣22+350*(n:ℤ) by omega)]
    simpa only [Nat.cast_ofNat, Nat.add_zero] using
      (padicValInt.self (p := 7) (by norm_num))


/-- Exact arithmetic progression, with no bound on the coprime tails. -/
theorem actual_progression (primes : Fin 4 → ℕ)
    (hp : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (n b c : ℕ) (hb : 156+2450*n≤b) (hc : 156+2450*n≤c)
    (hcop : Nat.Coprime b c) :
    ¬ActualLaplacianIntegral (modulus primes (pairExponents (156+2450*n) b c)) := by
  apply actual_odd_valuations primes hp hinj (156+2450*n) b c
    (by omega) hb hc hcop 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [(progression_orders n).1]; norm_num
  · rw [(progression_orders n).2]; norm_num

end D5.S3.Combinatorics.SpectralGraph.PairValuationSpectrum
