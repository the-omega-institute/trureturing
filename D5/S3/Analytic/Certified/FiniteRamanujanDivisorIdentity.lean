/- GID: D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity
   generality: G
   mirror-B: D5/B/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized sum of finite Ramanujan phases over the divisors of d is the indicator that d divides n. -/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex

/- Library-search audit trail (2026-09-06):
   * Repository and pinned-Mathlib searches found no `ramanujanSum`, finite
     Ramanujan expansion, or phase-coefficient declaration.
   * Pinned Mathlib supplies the separate ingredients
     `Complex.isPrimitiveRoot_iff`,
     `IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots`, and
     `IsPrimitiveRoot.pow_eq_one_iff_dvd`, but no theorem assembling the
     coprime exponential sum or the normalized divisor-indicator identity. -/

namespace D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial
open scoped BigOperators Nat Real

noncomputable section

/-- The finite Ramanujan sum, defined exactly as the sum of the phases
`exp (2 * pi * I * a * n / q)` over the coprime residues `a < q`. -/
def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ a ∈ Finset.range q with a.Coprime q,
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * n / q))

-- This is the preregistered escape witness: it constructs the finite
-- coprime-index/primitive-root bijection and transports the phase summand.
private theorem ramanujanSum_eq_primitiveRootPowerSum
    (q n : ℕ) (hq : 0 < q) :
    ramanujanSum q n = ∑ z ∈ primitiveRoots q ℂ, z ^ n := by
  let phase : ℕ → ℂ := fun a =>
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / q))
  have hphase_pow (a : ℕ) :
      phase a ^ n = Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * n / q)) := by
    dsimp [phase]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hprimitive :
      primitiveRoots q ℂ =
        ((Finset.range q).filter fun a => a.Coprime q).image phase := by
    ext z
    rw [mem_primitiveRoots hq]
    constructor
    · intro hz
      obtain ⟨a, ha, hcop, hza⟩ :=
        (Complex.isPrimitiveRoot_iff z q hq.ne').mp hz
      exact Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hcop⟩, hza⟩
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact Complex.isPrimitiveRoot_exp_of_coprime a q hq.ne'
        (Finset.mem_filter.mp ha).2
  have hroot : IsPrimitiveRoot (phase 1) q := by
    dsimp [phase]
    convert Complex.isPrimitiveRoot_exp q hq.ne' using 1
    congr 1
    ring
  have hphase (a : ℕ) : phase a = phase 1 ^ a := by
    dsimp [phase]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinj : Set.InjOn phase ((Finset.range q).filter fun a => a.Coprime q) := by
    intro a ha b hb hab
    apply hroot.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    simpa only [← hphase] using hab
  rw [ramanujanSum, hprimitive, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro a ha
  exact (hphase_pow a).symm

private theorem sum_nthRootsFinset_pow (d n : ℕ) (hd : 0 < d) :
    ∑ z ∈ nthRootsFinset d (1 : ℂ), z ^ n =
      if d ∣ n then (d : ℂ) else 0 := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)
  have hzeta : IsPrimitiveRoot zeta d := by
    exact Complex.isPrimitiveRoot_exp d hd.ne'
  have hroots :
      nthRootsFinset d (1 : ℂ) = (Finset.range d).image fun a => zeta ^ a := by
    ext z
    rw [Polynomial.mem_nthRootsFinset hd]
    constructor
    · intro hz
      obtain ⟨a, ha, hza⟩ := hzeta.eq_pow_of_pow_eq_one hz
      exact Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, hza⟩
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      rw [← pow_mul, hzeta.pow_eq_one_iff_dvd]
      exact dvd_mul_left d a
  rw [hroots, Finset.sum_image hzeta.injOn_pow]
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    obtain ⟨k, rfl⟩ := hdn
    calc
      ∑ a ∈ Finset.range d, (zeta ^ a) ^ (d * k) =
          ∑ _a ∈ Finset.range d, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← pow_mul, hzeta.pow_eq_one_iff_dvd]
        exact ⟨a * k, by ring⟩
      _ = (d : ℂ) := by simp
  · rw [if_neg hdn]
    have hne : zeta ^ n ≠ 1 := (hzeta.pow_eq_one_iff_dvd n).not.mpr hdn
    conv_lhs =>
      enter [2, a]
      rw [← pow_mul, mul_comm a n, pow_mul]
    rw [geom_sum_eq hne]
    have htop : (zeta ^ n) ^ d = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
    rw [htop, sub_self, zero_div]

private theorem sum_ramanujanSum_divisors (d n : ℕ) (hd : 0 < d) :
    ∑ q ∈ d.divisors, ramanujanSum q n =
      if d ∣ n then (d : ℂ) else 0 := by
  rw [← sum_nthRootsFinset_pow d n hd,
    IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro q hq
    exact ramanujanSum_eq_primitiveRootPowerSum q n
      (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hq).1 hd)
  · intro a ha b hb hab
    exact IsPrimitiveRoot.disjoint hab

/-- For positive `d`, the divisor indicator is the normalized sum of the
Ramanujan phases whose moduli divide `d`. This is formula (4) of the source. -/
theorem divisorIndicator_eq_normalized_sum_ramanujanSum
    (d n : ℕ) (hd : 0 < d) :
    (if d ∣ n then (1 : ℂ) else 0) =
      (d : ℂ)⁻¹ * ∑ q ∈ d.divisors, ramanujanSum q n := by
  rw [sum_ramanujanSum_divisors d n hd]
  split_ifs
  · simp [hd.ne']
  · simp

end

end D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
