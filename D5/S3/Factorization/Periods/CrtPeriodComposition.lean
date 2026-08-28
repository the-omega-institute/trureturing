/- GID: D5/S3/Factorization/Periods/CrtPeriodComposition
   generality: I
   mirror-B: D5/B/S3/Factorization/Periods/CrtPeriodComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: CRT composes every nonzero modulus period; zero is the excluded case. -/

/- Library-search audit trail (2026-08-25):
   * Repository search found the exact named definition `phasePeriod m = m / Nat.gcd m 2`
     and only the fixed `phase_period_twelve` calculation, not this general theorem.
   * The imported `finite_crt_join` and `primePowerProduct` supply the finite prime-power
     decomposition; `Nat.prod_pow_primeFactors_factorization` identifies its modulus with m.
   * Pinned Mathlib supplies `Pi.addOrderOf`, `AddEquiv.addOrderOf_eq`, `Finset.lcm_image`,
     `Nat.factorization`, `Nat.gcd`, `Nat.lcm`, and `Nat.Coprime.lcm_eq_mul`.
   * `Finset.lcm_eq_prod`, `Nat.ordProj`, and `Nat.ordCompl` were found but are unnecessary
     because `Pi.addOrderOf` returns the required lcm directly from the imported CRT.
   * The searched exact name `ZMod.natCast_self_eq_zero` is absent; `ZMod.natCast_self`
     exists but is not needed. The CRT image of two follows from the generic `map_natCast`. -/

import D5.S3.Factorization.PrimePowers.FiniteCrtJoin
import D5.S3.PrimeForms.CrossingPeriodicity.PhaseObserverMinimalPeriod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Periods.CrtPeriodComposition

open D5.S3.Factorization.PrimePowers.FiniteCrtJoin
open D5.S3.PrimeForms.CrossingPeriodicity.PhaseObserverMinimalPeriod

private theorem lcm_over_subtype (S : Finset Nat) (f : Nat -> Nat) :
    (Finset.univ : Finset S).lcm (fun p => f p) = S.lcm f := by
  symm
  calc
    S.lcm f = (Finset.image (fun p : S => (p : Nat)) Finset.univ).lcm f := by
      congr 1
      ext p
      simp
    _ = (Finset.univ : Finset S).lcm
        (f ∘ fun p : S => (p : Nat)) := Finset.lcm_image _
    _ = (Finset.univ : Finset S).lcm (fun p => f p) := rfl

/-- The phase period of a nonzero modulus is the lcm of its prime-power local periods. -/
theorem phase_period_crt_composition (m : Nat) (hm : m ≠ 0) :
    phasePeriod m =
      m.primeFactors.lcm (fun p => phasePeriod (p ^ m.factorization p)) := by
  have hprime : ∀ p, p ∈ m.primeFactors → Nat.Prime p := by
    exact fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hproduct :
      primePowerProduct m.primeFactors m.factorization = m := by
    simpa [primePowerProduct] using (Nat.prod_pow_primeFactors_factorization hm).symm
  obtain ⟨crt⟩ := finite_crt_join m.primeFactors m.factorization hprime
  rw [hproduct] at crt
  have hcrt_image :
      crt (-((2 : Nat) : ZMod m)) =
        fun p : m.primeFactors =>
          -((2 : Nat) : ZMod ((p : Nat) ^ m.factorization p)) := by
    funext p
    rw [map_neg]
    simp only [Pi.neg_apply]
    rw [congrFun (map_natCast crt 2) p]
    rfl
  calc
    phasePeriod m = addOrderOf (-((2 : Nat) : ZMod m)) :=
      (phase_period_eq m (Nat.pos_of_ne_zero hm)).1.symm
    _ = addOrderOf (crt (-((2 : Nat) : ZMod m))) :=
      (AddEquiv.addOrderOf_eq crt.toAddEquiv _).symm
    _ = addOrderOf (fun p : m.primeFactors =>
        -((2 : Nat) : ZMod ((p : Nat) ^ m.factorization p))) := by
      rw [hcrt_image]
    _ = (Finset.univ : Finset m.primeFactors).lcm
        (fun p => addOrderOf
          (-((2 : Nat) : ZMod ((p : Nat) ^ m.factorization p)))) :=
      Pi.addOrderOf _
    _ = (Finset.univ : Finset m.primeFactors).lcm
        (fun p => phasePeriod ((p : Nat) ^ m.factorization p)) := by
      apply Finset.lcm_congr rfl
      intro p _
      exact
        (phase_period_eq _
          (pow_pos (Nat.prime_of_mem_primeFactors p.property).pos _)).1
    _ = m.primeFactors.lcm
        (fun p => phasePeriod (p ^ m.factorization p)) :=
      lcm_over_subtype m.primeFactors
        (fun p => phasePeriod (p ^ m.factorization p))

#print axioms phase_period_crt_composition

/-- Nonzeroness is necessary: at zero the period is zero but the empty lcm is one. -/
theorem nonzero_modulus_is_necessary :
    ¬(phasePeriod 0 =
      (Nat.primeFactors 0).lcm
        (fun p => phasePeriod (p ^ Nat.factorization 0 p))) := by
  norm_num [phasePeriod]

#print axioms nonzero_modulus_is_necessary

-- The empty factorization of one and the single factorization of two.
example : phasePeriod 1 = 1 ∧
    (Nat.primeFactors 1).lcm
      (fun p => phasePeriod (p ^ Nat.factorization 1 p)) = 1 := by
  norm_num [phasePeriod]

example : phasePeriod 2 = 1 ∧
    (Nat.primeFactors 2).lcm
      (fun p => phasePeriod (p ^ Nat.factorization 2 p)) = 1 := by
  norm_num [phasePeriod, Nat.factorization]

-- Every power of an odd prime keeps its full modulus as period.
example {p k : Nat} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    phasePeriod (p ^ k) = p ^ k := by
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  rw [phasePeriod, hodd.pow.coprime_two_right.gcd_eq_one]
  simp

-- A positive power of two loses exactly one factor of two from its period.
example (k : Nat) : phasePeriod (2 ^ (k + 1)) = 2 ^ k := by
  rw [phasePeriod, Nat.gcd_eq_right_iff_dvd.mpr]
  · rw [pow_succ]
    omega
  · exact dvd_pow_self 2 (by omega)

-- Thirty audits the squarefree case with one even and two odd prime factors.
example : Squarefree 30 ∧ phasePeriod 30 = 15 ∧
    (Nat.primeFactors 30).lcm
      (fun p => phasePeriod (p ^ Nat.factorization 30 p)) = 15 := by
  refine ⟨?_, by norm_num [phasePeriod], ?_⟩
  · rw [show 30 = 2 * (3 * 5) by norm_num]
    rw [Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
    exact ⟨by decide, Nat.prime_two.squarefree, by decide,
      Nat.prime_three.squarefree, (by decide : Nat.Prime 5).squarefree⟩
  · rw [← phase_period_crt_composition 30 (by norm_num)]
    norm_num [phasePeriod]

end D5.S3.Factorization.Periods.CrtPeriodComposition
