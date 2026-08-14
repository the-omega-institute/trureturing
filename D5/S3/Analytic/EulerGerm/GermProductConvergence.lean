/- GID: D5/S3/Analytic/EulerGerm/GermProductConvergence
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden Euler local factors are multipliable for Re s > 1/phi^2. -/

import Mathlib
import D5.S3.Analytic.EulerGerm.GoldenLocalFactor
import D5.S3.Midline.GoldenHeatSpectrum

/- Provenance: Native proof over pinned mathlib. -/
/- SEARCH RECEIPT (2026-08-14): searched the repository D5 tree for
   `Euler product`, `tprod`, `Multipliable`, `local factor`, and germ convergence.
   The critical near-neighbor is `complex_displacement_germ_section` in
   `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.lean`:
   after unfolding `germLocalFactor`, its left side is the same prime-indexed
   product as `∏' p, germLocalFactor s p`. That theorem proves an equality
   for the value of this `tprod`, only under `1 < Real.goldenRatio * s.re`
   (equivalently `s.re > 1 / phi`). It does not by itself imply
   `Multipliable`: pinned mathlib defines `tprod` to be `1` when the family is
   not multipliable, in `Topology/Algebra/InfiniteSum/Defs.lean`, and states
   this behavior as `tprod_eq_one_of_not_multipliable`.

   No existing named declaration exposes multipliability of this family. On
   the narrower old half-plane, the public `dterm_c_summable`, coprime
   multiplicativity, and prime-power germ rewrite suffice to reconstruct it
   via `EulerProduct.eulerProduct_hasProd` and `HasProd.multipliable`; those
   inputs do not cover the new strip. This file proves `Multipliable` itself on
   the strictly larger half-plane `s.re > 1 / phi^2` (`1 / phi^2` is about
   `0.382`, while `1 / phi` is about `0.618`), adding
   `1 / phi^2 < s.re <= 1 / phi`. Other hits were the generic finite product in
   `D5/S3/Weil/EulerProduct.lean` and `multipliable_one_add_of_summable` in
   `D5/S3/Weil/ZetaGamma/GammaSeries.lean`. The shared `germLocalFactor` and
   the fact `o5Beta 0 = 0` are now provided by the same-bucket module
   `D5/S3/Analytic/EulerGerm/GoldenLocalFactor.lean`; this file imports no
   displacement module. Reused repository declarations `o5Beta`,
   `germLocalFactor`, `o5_beta_zero`, `goldenSpectrum`, and
   `golden_heat_abscissa`.

   Self-checks after the dependency refactor: the first required grep returned
   only line 16, the preserved near-neighbor path in this receipt, and no
   import line. The local-factor definition grep returned exactly
   `D5/S3/Analytic/EulerGerm/GoldenLocalFactor.lean:39`; the vacuum theorem
   definition grep returned exactly
   `D5/S3/Analytic/EulerGerm/GoldenLocalFactor.lean:43`. Thus each shared
   declaration has exactly one definition in the D5 tree.

   Searched pinned mathlib for the three variants of
   `multipliable_one_add_of_summable`: hits at
   `Analysis/SpecialFunctions/Log/Summable.lean` lines 49 (Complex), 94
   (Real), and 169 (complete normed ring); the line-169 theorem is used below.
   Searched for the complex-power norm formula: hit
   `Complex.norm_cpow_eq_rpow_re_of_pos` in
   `Analysis/SpecialFunctions/Pow/Real.lean`. Searched for prime real-power
   summability: hit `Nat.Primes.summable_rpow` in
   `NumberTheory/SumPrimeReciprocals.lean`; it is already used by the frozen
   proof of `golden_heat_abscissa`, which is reused here. Searched for product
   summability/Fubini and head-tail splitting: hits `Summable.prod`,
   `Summable.prod_factor`, `norm_tsum_le_tsum_norm`,
   `summable_nat_add_iff`, and `Summable.tsum_eq_zero_add`; all are reused.

   This S3 file deliberately does not import or reference
   `D5/X_Frontier/Hearts.lean` or `Hearts.eulerGerm`, because Hearts imports a
   module above S3. It proves the convergence property needed later to connect
   that definition; it does not redefine the germ or introduce a named germ
   product. -/

namespace D5.S3.Analytic.EulerGerm.GermProductConvergence

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Midline.GoldenHeatSpectrum
open D5.S3.Midline.UniversalHeatTrace

noncomputable section

private theorem prime_real_pos (p : Nat.Primes) : 0 < (p : ℝ) := by
  exact_mod_cast p.prop.pos

/-- Absolute summability of all excited prime modes on the golden germ
convergence half-plane. -/
theorem germ_excited_norm_summable (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    Summable (fun q : Nat.Primes × ℕ =>
      ‖(q.1 : ℂ) ^ (-s * (o5Beta (q.2 + 1) : ℂ))‖) := by
  have hheat : Summable (fun q : Nat.Primes × ℕ =>
      Real.exp (-s.re * goldenSpectrum q)) :=
    golden_heat_abscissa.1 s.re hs
  refine hheat.congr fun q => ?_
  rw [Complex.norm_natCast_cpow_of_pos q.1.prop.pos]
  rw [Real.rpow_def_of_pos (prime_real_pos q.1)]
  simp only [goldenSpectrum, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  congr 1
  ring

private theorem germ_excited_summable_at_prime (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) (p : Nat.Primes) :
    Summable (fun v : ℕ =>
      (p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))) := by
  exact ((germ_excited_norm_summable s hs).prod_factor p).of_norm

/-- On the convergence half-plane, the vacuum term of a prime-local factor is
`1`, and the remaining series consists exactly of the excited modes. -/
theorem germLocalFactor_eq_one_add (s : ℂ) (p : ℕ) (hp : p.Prime)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    germLocalFactor s p =
      1 + ∑' v : ℕ, (p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ)) := by
  let pp : Nat.Primes := ⟨p, hp⟩
  have htail : Summable (fun v : ℕ =>
      (p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))) := by
    simpa [pp] using germ_excited_summable_at_prime s hs pp
  have hall : Summable (fun v : ℕ =>
      (p : ℂ) ^ (-s * (o5Beta v : ℂ))) := by
    exact (summable_nat_add_iff
      (f := fun v : ℕ => (p : ℂ) ^ (-s * (o5Beta v : ℂ))) 1).1
        (by simpa [Nat.add_comm] using htail)
  rw [germLocalFactor, hall.tsum_eq_zero_add, o5_beta_zero]
  simp

/-- The golden Euler local factors are multipliable over the primes throughout
the full half-plane `Re s > 1 / φ²`. -/
theorem germLocalFactor_multipliable (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    Multipliable (fun p : Nat.Primes => germLocalFactor s p) := by
  let excited : Nat.Primes × ℕ → ℂ := fun q =>
    (q.1 : ℂ) ^ (-s * (o5Beta (q.2 + 1) : ℂ))
  have hnorm : Summable (fun q : Nat.Primes × ℕ => ‖excited q‖) := by
    simpa [excited] using germ_excited_norm_summable s hs
  have hnormTsum : Summable (fun p : Nat.Primes =>
      ‖∑' v : ℕ, excited (p, v)‖) := by
    refine hnorm.prod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    exact norm_tsum_le_tsum_norm (hnorm.prod_factor p)
  have hproduct : Multipliable (fun p : Nat.Primes =>
      1 + ∑' v : ℕ, excited (p, v)) :=
    multipliable_one_add_of_summable hnormTsum
  refine hproduct.congr fun p => ?_
  simpa [excited] using
    (germLocalFactor_eq_one_add s p p.prop hs).symm

end

end D5.S3.Analytic.EulerGerm.GermProductConvergence
