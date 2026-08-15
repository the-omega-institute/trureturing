/- GID: D5/S3/Analytic/EulerGerm/GermProductBound
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A constant bounds the golden Euler germ prime product on a closed half-plane. -/

import Mathlib
import D5.S3.Analytic.EulerGerm.GermProductConvergence
import D5.S3.Midline.HeatLayers.GoldenHeatLayers

/- Provenance: Native proof over pinned mathlib. -/
/- SEARCH RECEIPT (2026-08-15): searched the repository D5 tree for
   `germLocalFactor`, `germ_excited_norm_summable`,
   `germLocalFactor_eq_one_add`, `germLocalFactor_multipliable`, and norm bounds
   for the golden Euler germ. Reused all four named declarations from the
   frozen files `GoldenLocalFactor.lean` and `GermProductConvergence.lean`.
   The frozen `GermProductAnalytic.lean:45` and
   `GermProductAnalytic.lean:59` each declare a named private theorem,
   respectively `o5Beta_nonneg` and `germ_mode_norm_le`. Since private
   declarations cannot be referenced across modules, neither proof is reusable
   here. The public `o5Beta_nonneg` below does not copy the frozen proof: it is
   derived in one line from the public frozen theorems `o5_beta_strictMono` at
   `GoldenHeatLayers.lean:47` and `o5_beta_zero` at
   `GoldenLocalFactor.lean:43`. The public `germ_mode_norm_le` below is the
   closed-half-plane version with `sigma <= Re s`, published as the canonical
   API for downstream users.

   Read pinned mathlib source at
   `Mathlib/Topology/Algebra/InfiniteSum/Field.lean:31-35` for
   `Multipliable.norm` and `Multipliable.norm_tprod`, and at
   `Mathlib/Topology/Algebra/InfiniteSum/Order.lean:133-135` for
   `Multipliable.tprod_le_tprod`. Since its `IsOrderedMonoid` hypothesis is not
   available for all of `ℝ`, the ordered comparisons below are performed in
   `ℝ≥0` and transported along its closed embedding into `ℝ`. Read
   `HasProd.map`, `Multipliable.map_tprod`, and the inducing equivalence for
   `HasProd` at `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:217-253`, and
   `NNReal.isClosedEmbedding_coe` at
   `Mathlib/Topology/MetricSpace/Basic.lean:137`. Read the complete normed-ring theorem
   `multipliable_one_add_of_summable` at
   `Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:169-170`, as well as
   the directly applicable real specialization at lines 94-98. Read the
   exponent comparison
   `Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos` at
   `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:950-954`, and
   `multipliable_one` and `tprod_one` at
   `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:54-55,462-463`.
   Also checked the generic sum estimates `norm_tsum_le_tsum_norm` and
   `Summable.tsum_le_tsum`, which combine with `Summable.prod` and
   `Summable.prod_factor` already used by the frozen convergence proof. -/

namespace D5.S3.Analytic.EulerGerm.GermProductBound

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GermProductConvergence
open D5.S3.Midline.HeatLayers.GoldenHeatLayers

noncomputable section

/-- The absolute excited-mode tail at one prime, evaluated on the boundary
line `Re s = sigma`. -/
noncomputable def germExcitedTailBound (σ : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' v : ℕ, ‖(p : ℂ) ^ (-(σ : ℂ) * (o5Beta (v + 1) : ℂ))‖

/-- A constant Euler-product majorant for the golden germ on
`{s | sigma <= Re s}`. -/
noncomputable def germProductBound (σ : ℝ) : ℝ :=
  ∏' p : Nat.Primes, (1 + germExcitedTailBound σ p)

theorem o5Beta_nonneg (v : ℕ) : 0 ≤ o5Beta v := by
  simpa [o5_beta_zero] using o5_beta_strictMono.monotone (Nat.zero_le v)

theorem germ_mode_norm_le (σ : ℝ) (s : ℂ) (hs : σ ≤ s.re)
    (p : Nat.Primes) (v : ℕ) :
    ‖(p : ℂ) ^ (-s * (o5Beta v : ℂ))‖ ≤
      ‖(p : ℂ) ^ (-(σ : ℂ) * (o5Beta v : ℂ))‖ := by
  apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.prop.pos
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith [o5Beta_nonneg v]

private theorem germExcitedTailBound_summable (σ : ℝ)
    (hσ : 1 / Real.goldenRatio ^ 2 < σ) :
    Summable (germExcitedTailBound σ) := by
  have hnorm : Summable (fun q : Nat.Primes × ℕ =>
      ‖(q.1 : ℂ) ^ (-(σ : ℂ) * (o5Beta (q.2 + 1) : ℂ))‖) := by
    simpa using germ_excited_norm_summable (σ : ℂ) (by simpa using hσ)
  unfold germExcitedTailBound
  simpa only [neg_mul] using hnorm.prod

private theorem germProductBound_multipliable (σ : ℝ)
    (hσ : 1 / Real.goldenRatio ^ 2 < σ) :
    Multipliable (fun p : Nat.Primes => 1 + germExcitedTailBound σ p) :=
  Real.multipliable_one_add_of_summable
    (germExcitedTailBound_summable σ hσ)

private theorem germExcitedTailBound_nonneg (σ : ℝ) (p : Nat.Primes) :
    0 ≤ germExcitedTailBound σ p :=
  tsum_nonneg fun _ => norm_nonneg _

private noncomputable def germMajorantNN (σ : ℝ) (p : Nat.Primes) : NNReal :=
  ⟨1 + germExcitedTailBound σ p,
    add_nonneg zero_le_one (germExcitedTailBound_nonneg σ p)⟩

private theorem germMajorantNN_multipliable (σ : ℝ)
    (hσ : 1 / Real.goldenRatio ^ 2 < σ) :
    Multipliable (germMajorantNN σ) := by
  have hreal := germProductBound_multipliable σ hσ
  have hlimit_nonneg :
      0 ≤ ∏' p : Nat.Primes, (1 + germExcitedTailBound σ p) := by
    apply le_hasProd_of_le_prod hreal.hasProd
    intro t
    exact Finset.prod_nonneg fun p _ =>
      add_nonneg zero_le_one (germExcitedTailBound_nonneg σ p)
  let a : NNReal :=
    ⟨∏' p : Nat.Primes, (1 + germExcitedTailBound σ p), hlimit_nonneg⟩
  have hcoe : HasProd (NNReal.toRealHom ∘ germMajorantNN σ)
      (NNReal.toRealHom a) := by
    change HasProd (fun p : Nat.Primes => 1 + germExcitedTailBound σ p)
      (∏' p : Nat.Primes, (1 + germExcitedTailBound σ p))
    exact hreal.hasProd
  have hnn : HasProd (germMajorantNN σ) a := by
    have hind : Topology.IsInducing NNReal.toRealHom :=
      NNReal.isClosedEmbedding_coe.isInducing
    exact (hind.hasProd_iff (germMajorantNN σ) a).mp hcoe
  exact hnn.multipliable

private theorem coe_tprod_germMajorantNN (σ : ℝ)
    (hσ : 1 / Real.goldenRatio ^ 2 < σ) :
    ((∏' p : Nat.Primes, germMajorantNN σ p : NNReal) : ℝ) =
      germProductBound σ := by
  have hmap := (germMajorantNN_multipliable σ hσ).map_tprod
    NNReal.toRealHom NNReal.continuous_coe
  change ((∏' p : Nat.Primes, germMajorantNN σ p : NNReal) : ℝ) =
    ∏' p : Nat.Primes, (1 + germExcitedTailBound σ p) at hmap
  exact hmap

/-- Every prime-local factor is bounded by the boundary-line excited tail.
The right-hand side is independent of `s`. -/
theorem germLocalFactor_norm_le (σ : ℝ)
    (hσ : 1 / Real.goldenRatio ^ 2 < σ) (s : ℂ) (hs : σ ≤ s.re)
    (p : Nat.Primes) :
    ‖germLocalFactor s p‖ ≤ 1 + germExcitedTailBound σ p := by
  have hsHalf : 1 / Real.goldenRatio ^ 2 < s.re := lt_of_lt_of_le hσ hs
  have hsNorm : Summable (fun v : ℕ =>
      ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖) :=
    (germ_excited_norm_summable s hsHalf).prod_factor p
  have hσNorm : Summable (fun v : ℕ =>
      ‖(p : ℂ) ^ (-(σ : ℂ) * (o5Beta (v + 1) : ℂ))‖) := by
    simpa using ((germ_excited_norm_summable (σ : ℂ)
      (by simpa using hσ)).prod_factor p)
  rw [germLocalFactor_eq_one_add s p p.prop hsHalf]
  calc
    ‖1 + ∑' v : ℕ, (p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖ ≤
        ‖(1 : ℂ)‖ + ‖∑' v : ℕ,
          (p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖ := norm_add_le _ _
    _ ≤ 1 + ∑' v : ℕ,
        ‖(p : ℂ) ^ (-(σ : ℂ) * (o5Beta (v + 1) : ℂ))‖ := by
      rw [norm_one]
      gcongr
      exact (norm_tsum_le_tsum_norm hsNorm).trans
        (hsNorm.tsum_le_tsum
          (fun v => germ_mode_norm_le σ s hs p (v + 1)) hσNorm)
    _ = 1 + germExcitedTailBound σ p := rfl

/-- The constant majorant is at least one on the convergence half-plane. -/
theorem one_le_germProductBound (σ : ℝ)
    (hσ : 1 / Real.goldenRatio ^ 2 < σ) :
    1 ≤ germProductBound σ := by
  have hmajorant := germMajorantNN_multipliable σ hσ
  have hordered :
      (1 : NNReal) ≤ ∏' p : Nat.Primes, germMajorantNN σ p :=
    by
      simpa only [tprod_one] using
        Multipliable.tprod_le_tprod
          (fun p => by
            change (1 : ℝ) ≤ 1 + germExcitedTailBound σ p
            exact le_add_of_nonneg_right (germExcitedTailBound_nonneg σ p))
          multipliable_one hmajorant
  calc
    1 ≤ ((∏' p : Nat.Primes, germMajorantNN σ p : NNReal) : ℝ) :=
      NNReal.coe_mono hordered
    _ = germProductBound σ := coe_tprod_germMajorantNN σ hσ

/-- The golden Euler germ prime product is uniformly bounded on the closed
half-plane `sigma <= Re s` by a constant depending only on `sigma`. -/
theorem germProduct_norm_le (σ : ℝ)
    (hσ : 1 / Real.goldenRatio ^ 2 < σ) (s : ℂ) (hs : σ ≤ s.re) :
    ‖∏' p : Nat.Primes, germLocalFactor s p‖ ≤ germProductBound σ := by
  have hsHalf : 1 / Real.goldenRatio ^ 2 < s.re := lt_of_lt_of_le hσ hs
  have hlocal := germLocalFactor_multipliable s hsHalf
  have hlocalNN : Multipliable (fun p : Nat.Primes => ‖germLocalFactor s p‖₊) := by
    have hm := hlocal.map (nnnormHom : ℂ →*₀ NNReal) continuous_nnnorm
    change Multipliable (fun p : Nat.Primes => ‖germLocalFactor s p‖₊) at hm
    exact hm
  have hmajorant := germMajorantNN_multipliable σ hσ
  have hordered :
      (∏' p : Nat.Primes, ‖germLocalFactor s p‖₊) ≤
        ∏' p : Nat.Primes, germMajorantNN σ p :=
    Multipliable.tprod_le_tprod
      (fun p => by
        change ‖germLocalFactor s p‖ ≤ 1 + germExcitedTailBound σ p
        exact germLocalFactor_norm_le σ hσ s hs p)
      hlocalNN hmajorant
  have hcoeLocal := hlocalNN.map_tprod NNReal.toRealHom NNReal.continuous_coe
  calc
    ‖∏' p : Nat.Primes, germLocalFactor s p‖ =
        ∏' p : Nat.Primes, ‖germLocalFactor s p‖ := hlocal.norm_tprod
    _ = ((∏' p : Nat.Primes, ‖germLocalFactor s p‖₊ : NNReal) : ℝ) := by
      simpa only [Function.comp_apply, NNReal.coe_toRealHom, coe_nnnorm] using
        hcoeLocal.symm
    _ ≤ ((∏' p : Nat.Primes, germMajorantNN σ p : NNReal) : ℝ) :=
      NNReal.coe_mono hordered
    _ = germProductBound σ := coe_tprod_germMajorantNN σ hσ

end

end D5.S3.Analytic.EulerGerm.GermProductBound
