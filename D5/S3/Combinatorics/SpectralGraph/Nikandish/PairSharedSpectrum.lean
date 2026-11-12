/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairSharedSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairSharedSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared first-order tail valuations exclude actual four-prime integral spectra. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairSharedRoot
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairValuationSpectrum

/-! Source: the complete four-prime-shared-prime theorem and its unbounded
region, PR9 6d491f77b35dec808fc777b69939c56cdae5dc02. No coprimality
of the tails is assumed. Valuations are of the actual integer exponents;
the minimum is the valuation of their gcd. General Q3 remains open. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.PairSharedSpectrum
open PairedIdealIntersectionObstructions PairedIdealIntersectionLift
open IdealIntersectionSupport IdealIntersectionObstructions

/-- Both first-order endpoint obstructions, for arbitrary shared tails. -/
theorem actual_first_orders (primes : Fin 4 → ℕ)
    (hp : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (a b c : ℕ) (ha : 5 ≤ a) (hb : a ≤ b) (hc : a ≤ c)
    (p q : ℕ) (hpp : p.Prime) (hqp : q.Prime) (hpl : 5 ≤ p) (hql : 7 ≤ q)
    (he2 : padicValInt p ((a : ℤ)-1)=1)
    (he3 : padicValInt q ((a : ℤ)-2)=1)
    (hbp : min (padicValInt p (b : ℤ)) (padicValInt p (c : ℤ)) ≠ 1)
    (hbq : min (padicValInt q (b : ℤ)) (padicValInt q (c : ℤ)) ≠ 1) :
    ¬ActualLaplacianIntegral (modulus primes (pairExponents a b c)) := by
  intro H
  rcases PairLowArithmetic.actual_low_root primes hp hinj a b c ha hb hc H with h2 | h3
  · letI : Fact p.Prime := ⟨hpp⟩
    have he : padicValInt p ((a : ℤ)+1-2)=1 := by
      convert he2 using 1 <;> ring
    have hd : (p : ℤ) ∣ (a : ℤ)+1-2 := by
      have hv : (p : ℤ)^1 ∣ (a : ℤ)+1-2 := by
        apply (padicValInt_dvd_iff _ _).mpr
        exact Or.inr (by omega)
      simpa using hv
    exact hbp (PairSharedRoot.root_first_order (a : ℤ) b c 2
      (by exact_mod_cast (show 0 < a by omega))
      (by exact_mod_cast (show 0 < b by omega))
      (by exact_mod_cast (show 0 < c by omega)) p hd
      (PairValuationSpectrum.good_two p hpp hpl) he h2)
  · letI : Fact q.Prime := ⟨hqp⟩
    have he : padicValInt q ((a : ℤ)+1-3)=1 := by
      convert he3 using 1 <;> ring
    have hd : (q : ℤ) ∣ (a : ℤ)+1-3 := by
      have hv : (q : ℤ)^1 ∣ (a : ℤ)+1-3 := by
        apply (padicValInt_dvd_iff _ _).mpr
        exact Or.inr (by omega)
      simpa using hv
    exact hbq (PairSharedRoot.root_first_order (a : ℤ) b c 3
      (by exact_mod_cast (show 0 < a by omega))
      (by exact_mod_cast (show 0 < b by omega))
      (by exact_mod_cast (show 0 < c by omega)) q hd
      (PairValuationSpectrum.good_three q hqp hql) he h3)

/-- The entire source progression, with arbitrary common divisors subject
only to the two stated necessary-order failures. -/
theorem actual_progression (primes : Fin 4 → ℕ)
    (hp : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (n b c : ℕ) (hb : 156+2450*n ≤ b) (hc : 156+2450*n ≤ c)
    (h5 : min (padicValInt 5 (b : ℤ)) (padicValInt 5 (c : ℤ)) ≠ 1)
    (h7 : min (padicValInt 7 (b : ℤ)) (padicValInt 7 (c : ℤ)) ≠ 1) :
    ¬ActualLaplacianIntegral (modulus primes (pairExponents (156+2450*n) b c)) := by
  exact actual_first_orders primes hp hinj (156+2450*n) b c (by omega) hb hc
    5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (PairValuationSpectrum.progression_orders n).1
    (PairValuationSpectrum.progression_orders n).2 h5 h7

end D5.S3.Combinatorics.SpectralGraph.PairSharedSpectrum
