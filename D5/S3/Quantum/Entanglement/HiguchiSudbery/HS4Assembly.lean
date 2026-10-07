/- GID: D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: HS4Assembly for the sharp four-qubit marginal entropy bound. -/

/-
admission_basis: escape-witness
Same-delivery prerequisite: D5.S3.Quantum.Entanglement.HiguchiSudbery.EntropyReduction.
Direct frozen dependencies: repository quantum interfaces in
  D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity and
  D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber and
  D5.S3.Quantum.Information.InputInformationBalance.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.HiguchiSudbery.EntropyReduction
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber
import D5.S3.Quantum.Information.InputInformationBalance

noncomputable section
namespace D5.S3.Quantum.Entanglement.HiguchiSudbery
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def rho0_0_0 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 0 + z 1 * w 1 + z 2 * w 2 + z 3 * w 3

private def rho0_0_1 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 4 + z 1 * w 5 + z 2 * w 6 + z 3 * w 7

private def rho0_0_2 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 8 + z 1 * w 9 + z 2 * w 10 + z 3 * w 11

private def rho0_0_3 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 12 + z 1 * w 13 + z 2 * w 14 + z 3 * w 15

private def rho0_1_0 (z w : Fin 16 → ℂ) : ℂ := z 4 * w 0 + z 5 * w 1 + z 6 * w 2 + z 7 * w 3

private def rho0_1_1 (z w : Fin 16 → ℂ) : ℂ := z 4 * w 4 + z 5 * w 5 + z 6 * w 6 + z 7 * w 7

private def rho0_1_2 (z w : Fin 16 → ℂ) : ℂ := z 4 * w 8 + z 5 * w 9 + z 6 * w 10 + z 7 * w 11

private def rho0_1_3 (z w : Fin 16 → ℂ) : ℂ := z 4 * w 12 + z 5 * w 13 + z 6 * w 14 + z 7 * w 15

private def rho0_2_0 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 0 + z 9 * w 1 + z 10 * w 2 + z 11 * w 3

private def rho0_2_1 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 4 + z 9 * w 5 + z 10 * w 6 + z 11 * w 7

private def rho0_2_2 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 8 + z 9 * w 9 + z 10 * w 10 + z 11 * w 11

private def rho0_2_3 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 12 + z 9 * w 13 + z 10 * w 14 + z 11 * w 15

private def rho0_3_0 (z w : Fin 16 → ℂ) : ℂ := z 12 * w 0 + z 13 * w 1 + z 14 * w 2 + z 15 * w 3

private def rho0_3_1 (z w : Fin 16 → ℂ) : ℂ := z 12 * w 4 + z 13 * w 5 + z 14 * w 6 + z 15 * w 7

private def rho0_3_2 (z w : Fin 16 → ℂ) : ℂ := z 12 * w 8 + z 13 * w 9 + z 14 * w 10 + z 15 * w 11

private def rho0_3_3 (z w : Fin 16 → ℂ) : ℂ := z 12 * w 12 + z 13 * w 13 + z 14 * w 14 + z 15 * w 15

private def purityPair0 (z w : Fin 16 → ℂ) : ℂ := rho0_0_0 z w * rho0_0_0 z w + rho0_0_1 z w * rho0_1_0 z w + rho0_0_2 z w * rho0_2_0 z w + rho0_0_3 z w * rho0_3_0 z w + rho0_1_0 z w * rho0_0_1 z w + rho0_1_1 z w * rho0_1_1 z w + rho0_1_2 z w * rho0_2_1 z w + rho0_1_3 z w * rho0_3_1 z w + rho0_2_0 z w * rho0_0_2 z w + rho0_2_1 z w * rho0_1_2 z w + rho0_2_2 z w * rho0_2_2 z w + rho0_2_3 z w * rho0_3_2 z w + rho0_3_0 z w * rho0_0_3 z w + rho0_3_1 z w * rho0_1_3 z w + rho0_3_2 z w * rho0_2_3 z w + rho0_3_3 z w * rho0_3_3 z w

private def rho1_0_0 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 0 + z 1 * w 1 + z 4 * w 4 + z 5 * w 5

private def rho1_0_1 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 2 + z 1 * w 3 + z 4 * w 6 + z 5 * w 7

private def rho1_0_2 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 8 + z 1 * w 9 + z 4 * w 12 + z 5 * w 13

private def rho1_0_3 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 10 + z 1 * w 11 + z 4 * w 14 + z 5 * w 15

private def rho1_1_0 (z w : Fin 16 → ℂ) : ℂ := z 2 * w 0 + z 3 * w 1 + z 6 * w 4 + z 7 * w 5

private def rho1_1_1 (z w : Fin 16 → ℂ) : ℂ := z 2 * w 2 + z 3 * w 3 + z 6 * w 6 + z 7 * w 7

private def rho1_1_2 (z w : Fin 16 → ℂ) : ℂ := z 2 * w 8 + z 3 * w 9 + z 6 * w 12 + z 7 * w 13

private def rho1_1_3 (z w : Fin 16 → ℂ) : ℂ := z 2 * w 10 + z 3 * w 11 + z 6 * w 14 + z 7 * w 15

private def rho1_2_0 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 0 + z 9 * w 1 + z 12 * w 4 + z 13 * w 5

private def rho1_2_1 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 2 + z 9 * w 3 + z 12 * w 6 + z 13 * w 7

private def rho1_2_2 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 8 + z 9 * w 9 + z 12 * w 12 + z 13 * w 13

private def rho1_2_3 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 10 + z 9 * w 11 + z 12 * w 14 + z 13 * w 15

private def rho1_3_0 (z w : Fin 16 → ℂ) : ℂ := z 10 * w 0 + z 11 * w 1 + z 14 * w 4 + z 15 * w 5

private def rho1_3_1 (z w : Fin 16 → ℂ) : ℂ := z 10 * w 2 + z 11 * w 3 + z 14 * w 6 + z 15 * w 7

private def rho1_3_2 (z w : Fin 16 → ℂ) : ℂ := z 10 * w 8 + z 11 * w 9 + z 14 * w 12 + z 15 * w 13

private def rho1_3_3 (z w : Fin 16 → ℂ) : ℂ := z 10 * w 10 + z 11 * w 11 + z 14 * w 14 + z 15 * w 15

private def purityPair1 (z w : Fin 16 → ℂ) : ℂ := rho1_0_0 z w * rho1_0_0 z w + rho1_0_1 z w * rho1_1_0 z w + rho1_0_2 z w * rho1_2_0 z w + rho1_0_3 z w * rho1_3_0 z w + rho1_1_0 z w * rho1_0_1 z w + rho1_1_1 z w * rho1_1_1 z w + rho1_1_2 z w * rho1_2_1 z w + rho1_1_3 z w * rho1_3_1 z w + rho1_2_0 z w * rho1_0_2 z w + rho1_2_1 z w * rho1_1_2 z w + rho1_2_2 z w * rho1_2_2 z w + rho1_2_3 z w * rho1_3_2 z w + rho1_3_0 z w * rho1_0_3 z w + rho1_3_1 z w * rho1_1_3 z w + rho1_3_2 z w * rho1_2_3 z w + rho1_3_3 z w * rho1_3_3 z w

private def rho2_0_0 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 0 + z 2 * w 2 + z 4 * w 4 + z 6 * w 6

private def rho2_0_1 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 1 + z 2 * w 3 + z 4 * w 5 + z 6 * w 7

private def rho2_0_2 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 8 + z 2 * w 10 + z 4 * w 12 + z 6 * w 14

private def rho2_0_3 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 9 + z 2 * w 11 + z 4 * w 13 + z 6 * w 15

private def rho2_1_0 (z w : Fin 16 → ℂ) : ℂ := z 1 * w 0 + z 3 * w 2 + z 5 * w 4 + z 7 * w 6

private def rho2_1_1 (z w : Fin 16 → ℂ) : ℂ := z 1 * w 1 + z 3 * w 3 + z 5 * w 5 + z 7 * w 7

private def rho2_1_2 (z w : Fin 16 → ℂ) : ℂ := z 1 * w 8 + z 3 * w 10 + z 5 * w 12 + z 7 * w 14

private def rho2_1_3 (z w : Fin 16 → ℂ) : ℂ := z 1 * w 9 + z 3 * w 11 + z 5 * w 13 + z 7 * w 15

private def rho2_2_0 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 0 + z 10 * w 2 + z 12 * w 4 + z 14 * w 6

private def rho2_2_1 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 1 + z 10 * w 3 + z 12 * w 5 + z 14 * w 7

private def rho2_2_2 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 8 + z 10 * w 10 + z 12 * w 12 + z 14 * w 14

private def rho2_2_3 (z w : Fin 16 → ℂ) : ℂ := z 8 * w 9 + z 10 * w 11 + z 12 * w 13 + z 14 * w 15

private def rho2_3_0 (z w : Fin 16 → ℂ) : ℂ := z 9 * w 0 + z 11 * w 2 + z 13 * w 4 + z 15 * w 6

private def rho2_3_1 (z w : Fin 16 → ℂ) : ℂ := z 9 * w 1 + z 11 * w 3 + z 13 * w 5 + z 15 * w 7

private def rho2_3_2 (z w : Fin 16 → ℂ) : ℂ := z 9 * w 8 + z 11 * w 10 + z 13 * w 12 + z 15 * w 14

private def rho2_3_3 (z w : Fin 16 → ℂ) : ℂ := z 9 * w 9 + z 11 * w 11 + z 13 * w 13 + z 15 * w 15

private def purityPair2 (z w : Fin 16 → ℂ) : ℂ := rho2_0_0 z w * rho2_0_0 z w + rho2_0_1 z w * rho2_1_0 z w + rho2_0_2 z w * rho2_2_0 z w + rho2_0_3 z w * rho2_3_0 z w + rho2_1_0 z w * rho2_0_1 z w + rho2_1_1 z w * rho2_1_1 z w + rho2_1_2 z w * rho2_2_1 z w + rho2_1_3 z w * rho2_3_1 z w + rho2_2_0 z w * rho2_0_2 z w + rho2_2_1 z w * rho2_1_2 z w + rho2_2_2 z w * rho2_2_2 z w + rho2_2_3 z w * rho2_3_2 z w + rho2_3_0 z w * rho2_0_3 z w + rho2_3_1 z w * rho2_1_3 z w + rho2_3_2 z w * rho2_2_3 z w + rho2_3_3 z w * rho2_3_3 z w

private def spinPair (z : Fin 16 → ℂ) : ℂ := (1) * (z 0 * z 15) + (-1) * (z 1 * z 14) + (-1) * (z 2 * z 13) + (1) * (z 3 * z 12) + (-1) * (z 4 * z 11) + (1) * (z 5 * z 10) + (1) * (z 6 * z 9) + (-1) * (z 7 * z 8) + (-1) * (z 8 * z 7) + (1) * (z 9 * z 6) + (1) * (z 10 * z 5) + (-1) * (z 11 * z 4) + (1) * (z 12 * z 3) + (-1) * (z 13 * z 2) + (-1) * (z 14 * z 1) + (1) * (z 15 * z 0)

private def singleDiff0 (z w : Fin 16 → ℂ) : ℂ := (z 0 * w 0 + z 1 * w 1 + z 2 * w 2 + z 3 * w 3 + z 4 * w 4 + z 5 * w 5 + z 6 * w 6 + z 7 * w 7) - (z 8 * w 8 + z 9 * w 9 + z 10 * w 10 + z 11 * w 11 + z 12 * w 12 + z 13 * w 13 + z 14 * w 14 + z 15 * w 15)

private def singleOff0 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 8 + z 1 * w 9 + z 2 * w 10 + z 3 * w 11 + z 4 * w 12 + z 5 * w 13 + z 6 * w 14 + z 7 * w 15

private def singleDiff1 (z w : Fin 16 → ℂ) : ℂ := (z 0 * w 0 + z 1 * w 1 + z 2 * w 2 + z 3 * w 3 + z 8 * w 8 + z 9 * w 9 + z 10 * w 10 + z 11 * w 11) - (z 4 * w 4 + z 5 * w 5 + z 6 * w 6 + z 7 * w 7 + z 12 * w 12 + z 13 * w 13 + z 14 * w 14 + z 15 * w 15)

private def singleOff1 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 4 + z 1 * w 5 + z 2 * w 6 + z 3 * w 7 + z 8 * w 12 + z 9 * w 13 + z 10 * w 14 + z 11 * w 15

private def singleDiff2 (z w : Fin 16 → ℂ) : ℂ := (z 0 * w 0 + z 1 * w 1 + z 4 * w 4 + z 5 * w 5 + z 8 * w 8 + z 9 * w 9 + z 12 * w 12 + z 13 * w 13) - (z 2 * w 2 + z 3 * w 3 + z 6 * w 6 + z 7 * w 7 + z 10 * w 10 + z 11 * w 11 + z 14 * w 14 + z 15 * w 15)

private def singleOff2 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 2 + z 1 * w 3 + z 4 * w 6 + z 5 * w 7 + z 8 * w 10 + z 9 * w 11 + z 12 * w 14 + z 13 * w 15

private def singleDiff3 (z w : Fin 16 → ℂ) : ℂ := (z 0 * w 0 + z 2 * w 2 + z 4 * w 4 + z 6 * w 6 + z 8 * w 8 + z 10 * w 10 + z 12 * w 12 + z 14 * w 14) - (z 1 * w 1 + z 3 * w 3 + z 5 * w 5 + z 7 * w 7 + z 9 * w 9 + z 11 * w 11 + z 13 * w 13 + z 15 * w 15)

private def singleOff3 (z w : Fin 16 → ℂ) : ℂ := z 0 * w 1 + z 2 * w 3 + z 4 * w 5 + z 6 * w 7 + z 8 * w 9 + z 10 * w 11 + z 12 * w 13 + z 14 * w 15

private theorem literal_purity_identity /- proof_shape: bind-only; consumer: HS4Assembly.purity_ge_mass_sq -/ (z w : Fin 16 → ℂ) :
    2 * (purityPair0 z w + purityPair1 z w + purityPair2 z w - dotProduct z w ^ 2) =
    spinPair z * spinPair w + (singleDiff0 z w)^2 + 4*(singleOff0 z w * singleOff0 w z) + (singleDiff1 z w)^2 + 4*(singleOff1 z w * singleOff1 w z) + (singleDiff2 z w)^2 + 4*(singleOff2 z w * singleOff2 w z) + (singleDiff3 z w)^2 + 4*(singleOff3 z w * singleOff3 w z) := by
  norm_num [dotProduct, Fin.sum_univ_succ, Finset.sum_empty, Finset.univ_eq_empty, spinPair, purityPair0, purityPair1, purityPair2, rho0_0_0, rho0_0_1, rho0_0_2, rho0_0_3, rho0_1_0, rho0_1_1, rho0_1_2, rho0_1_3, rho0_2_0, rho0_2_1, rho0_2_2, rho0_2_3, rho0_3_0, rho0_3_1, rho0_3_2, rho0_3_3, rho1_0_0, rho1_0_1, rho1_0_2, rho1_0_3, rho1_1_0, rho1_1_1, rho1_1_2, rho1_1_3, rho1_2_0, rho1_2_1, rho1_2_2, rho1_2_3, rho1_3_0, rho1_3_1, rho1_3_2, rho1_3_3, rho2_0_0, rho2_0_1, rho2_0_2, rho2_0_3, rho2_1_0, rho2_1_1, rho2_1_2, rho2_1_3, rho2_2_0, rho2_2_1, rho2_2_2, rho2_2_3, rho2_3_0, rho2_3_1, rho2_3_2, rho2_3_3, singleDiff0, singleDiff1, singleDiff2, singleDiff3, singleOff0, singleOff1, singleOff2, singleOff3]
  ring!


open private squaredAmplitudeTotal from D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber
open scoped BigOperators
set_option maxHeartbeats 0

private def totalPurity (z : Fin 16 → ℂ) : ℝ :=
  (purityPair0 z (star z) + purityPair1 z (star z) + purityPair2 z (star z)).re

private lemma normPair_star /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.e3_bound_of_certificate -/ (z : Fin 16 → ℂ) : dotProduct z (star z) = (squaredAmplitudeTotal 15 z : ℂ) := by
  simp [dotProduct, squaredAmplitudeTotal, Fin.sum_univ_succ, Complex.mul_conj, Complex.ofReal_add]

private lemma spinPair_star /- proof_shape: bind-only; consumer: HS4Assembly.purity_ge_mass_sq -/ (z : Fin 16 → ℂ) : spinPair (star z) = star (spinPair z) := by
  simp [spinPair, star_add, star_mul]
  ring

private lemma singleOff_star /- proof_shape: bind-only; consumer: HS4Assembly.purity_ge_mass_sq -/ (z : Fin 16 → ℂ) :
    singleOff0 (star z) z = star (singleOff0 z (star z)) ∧
    singleOff1 (star z) z = star (singleOff1 z (star z)) ∧
    singleOff2 (star z) z = star (singleOff2 z (star z)) ∧
    singleOff3 (star z) z = star (singleOff3 z (star z)) := by
  simp [singleOff0, singleOff1, singleOff2, singleOff3, star_add, star_mul, mul_comm]

private lemma singleDiff_im /- proof_shape: bind-only; consumer: HS4Assembly.purity_ge_mass_sq -/ (z : Fin 16 → ℂ) :
    (singleDiff0 z (star z)).im = 0 ∧ (singleDiff1 z (star z)).im = 0 ∧
    (singleDiff2 z (star z)).im = 0 ∧ (singleDiff3 z (star z)).im = 0 := by
  simp [singleDiff0, singleDiff1, singleDiff2, singleDiff3, Complex.mul_conj]

private lemma purity_ge_mass_sq /- proof_shape: bind-only; consumer: HS4Assembly.purity_ge_one -/ (z : Fin 16 → ℂ) : squaredAmplitudeTotal 15 z ^ 2 ≤ totalPurity z := by
  have h := congrArg Complex.re (literal_purity_identity z (star z))
  have ho := singleOff_star z
  have hd := singleDiff_im z
  rw [normPair_star, spinPair_star, ho.1, ho.2.1, ho.2.2.1, ho.2.2.2] at h
  norm_num [pow_two, Complex.mul_re, Complex.star_def, Complex.normSq_apply,
    hd.1, hd.2.1, hd.2.2.1, hd.2.2.2] at h
  dsimp [totalPurity]
  nlinarith

private lemma purity_ge_one /- proof_shape: bind-only; consumer: HS4Assembly.total_spectral_purity_ge_one -/ (z : Fin 16 → ℂ) (hz : squaredAmplitudeTotal 15 z = 1) : 1 ≤ totalPurity z := by
  simpa [hz] using purity_ge_mass_sq z


open private squaredAmplitudeTotal from D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Information.CovarianceSumBound
set_option maxHeartbeats 0
set_option maxRecDepth 100000
-- The rows and columns list the two bits of the retained and discarded pair.

def cutIndex (c : Fin 3) : Matrix (Fin 4) (Fin 4) (Fin 16) :=
  ![!![0,1,2,3; 4,5,6,7; 8,9,10,11; 12,13,14,15],
    !![0,1,4,5; 2,3,6,7; 8,9,12,13; 10,11,14,15],
    !![0,2,4,6; 1,3,5,7; 8,10,12,14; 9,11,13,15]] c

def cutFlatten (z : Fin 16 → ℂ) (c : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun r b => z (cutIndex c r b)

def cutMatrix (z : Fin 16 → ℂ) (c : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  partialTraceRight (rankOneDensity (fun p : Fin 4 × Fin 4 => cutFlatten z c p.1 p.2))

private lemma cut_gram /- proof_shape: bind-only; consumer: HS4Assembly.cut_trace -/ (z : Fin 16 → ℂ) (c : Fin 3) :
    cutMatrix z c = cutFlatten z c * (cutFlatten z c)ᴴ := by
  ext r s
  simp [cutMatrix, partialTraceRight, rankOneDensity, Matrix.vecMulVec, Matrix.mul_apply]

private lemma cut_mass /- proof_shape: bind-only; consumer: HS4Assembly.cut_trace -/ (z : Fin 16 → ℂ) (c : Fin 3) :
    (∑ r, ∑ b, Complex.normSq (cutFlatten z c r b)) = squaredAmplitudeTotal 15 z := by
  fin_cases c <;> norm_num [cutFlatten, cutIndex, squaredAmplitudeTotal, Fin.sum_univ_succ] <;> ring!

private lemma cut_trace /- proof_shape: bind-only; consumer: HS4Assembly.cut_spectrum_sum -/ (z : Fin 16 → ℂ) (c : Fin 3) : (cutMatrix z c).trace = (squaredAmplitudeTotal 15 z : ℂ) := by
  rw [cut_gram]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, ← Complex.ofReal_sum]
  rw [cut_mass]

private lemma cut_positive /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_entropy -/ (z : Fin 16 → ℂ) (c : Fin 3) : (cutMatrix z c).PosSemidef := by
  rw [cut_gram]
  exact Matrix.posSemidef_self_mul_conjTranspose _

def cutDensity (z : Fin 16 → ℂ) (hz : squaredAmplitudeTotal 15 z = 1) (c : Fin 3) :=
  marginalRight (pureDensityState (fun p : Fin 4 × Fin 4 => cutFlatten z c p.1 p.2) (by
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type,
      Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum]
    rw [cut_mass, hz]
    simp))

private lemma totalPurity_trace /- proof_shape: bind-only; consumer: HS4Assembly.total_spectral_purity_ge_one -/ (z : Fin 16 → ℂ) :
    totalPurity z = ∑ c, ((cutMatrix z c)^2).trace.re := by
  have h0 : cutMatrix z 0 = !![rho0_0_0 z (star z), rho0_0_1 z (star z), rho0_0_2 z (star z), rho0_0_3 z (star z); rho0_1_0 z (star z), rho0_1_1 z (star z), rho0_1_2 z (star z), rho0_1_3 z (star z); rho0_2_0 z (star z), rho0_2_1 z (star z), rho0_2_2 z (star z), rho0_2_3 z (star z); rho0_3_0 z (star z), rho0_3_1 z (star z), rho0_3_2 z (star z), rho0_3_3 z (star z)] := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ, cutMatrix, partialTraceRight, rankOneDensity,
        Matrix.vecMulVec, cutFlatten, cutIndex, rho0_0_0, rho0_0_1, rho0_0_2, rho0_0_3, rho0_1_0, rho0_1_1, rho0_1_2, rho0_1_3, rho0_2_0, rho0_2_1, rho0_2_2, rho0_2_3, rho0_3_0, rho0_3_1, rho0_3_2, rho0_3_3] <;> ring
  have t0 : ((cutMatrix z 0)^2).trace = purityPair0 z (star z) := by
    rw [h0]
    norm_num [Fin.sum_univ_succ, pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, purityPair0]
    ring
  have h1 : cutMatrix z 1 = !![rho1_0_0 z (star z), rho1_0_1 z (star z), rho1_0_2 z (star z), rho1_0_3 z (star z); rho1_1_0 z (star z), rho1_1_1 z (star z), rho1_1_2 z (star z), rho1_1_3 z (star z); rho1_2_0 z (star z), rho1_2_1 z (star z), rho1_2_2 z (star z), rho1_2_3 z (star z); rho1_3_0 z (star z), rho1_3_1 z (star z), rho1_3_2 z (star z), rho1_3_3 z (star z)] := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ, cutMatrix, partialTraceRight, rankOneDensity,
        Matrix.vecMulVec, cutFlatten, cutIndex, rho1_0_0, rho1_0_1, rho1_0_2, rho1_0_3, rho1_1_0, rho1_1_1, rho1_1_2, rho1_1_3, rho1_2_0, rho1_2_1, rho1_2_2, rho1_2_3, rho1_3_0, rho1_3_1, rho1_3_2, rho1_3_3] <;> ring
  have t1 : ((cutMatrix z 1)^2).trace = purityPair1 z (star z) := by
    rw [h1]
    norm_num [Fin.sum_univ_succ, pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, purityPair1]
    ring
  have h2 : cutMatrix z 2 = !![rho2_0_0 z (star z), rho2_0_1 z (star z), rho2_0_2 z (star z), rho2_0_3 z (star z); rho2_1_0 z (star z), rho2_1_1 z (star z), rho2_1_2 z (star z), rho2_1_3 z (star z); rho2_2_0 z (star z), rho2_2_1 z (star z), rho2_2_2 z (star z), rho2_2_3 z (star z); rho2_3_0 z (star z), rho2_3_1 z (star z), rho2_3_2 z (star z), rho2_3_3 z (star z)] := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ, cutMatrix, partialTraceRight, rankOneDensity,
        Matrix.vecMulVec, cutFlatten, cutIndex, rho2_0_0, rho2_0_1, rho2_0_2, rho2_0_3, rho2_1_0, rho2_1_1, rho2_1_2, rho2_1_3, rho2_2_0, rho2_2_1, rho2_2_2, rho2_2_3, rho2_3_0, rho2_3_1, rho2_3_2, rho2_3_3] <;> ring
  have t2 : ((cutMatrix z 2)^2).trace = purityPair2 z (star z) := by
    rw [h2]
    norm_num [Fin.sum_univ_succ, pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, purityPair2]
    ring
  norm_num [totalPurity, Fin.sum_univ_succ, t0, t1, t2, Complex.add_re]
  ring


open private entropy_three_spectra from D5.S3.Quantum.Entanglement.HiguchiSudbery.EntropyReduction

open Matrix Real
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.InputInformationBalance
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

private def cutSpectrum (z : Fin 16 → ℂ) (c : Fin 3) : Fin 4 → ℝ :=
  (cut_positive z c).isHermitian.eigenvalues

def averageEntropy (z : Fin 16 → ℂ) (hz : squaredAmplitudeTotal 15 z = 1) : ℝ :=
  (∑ c, vonNeumannEntropy (cutDensity z hz c)) / (3*log 2)

private lemma cut_spectrum_sum /- proof_shape: bind-only; consumer: HS4Assembly.hs4_of_spectral_e3 -/ (z : Fin 16 → ℂ) (hz : squaredAmplitudeTotal 15 z = 1) (c : Fin 3) :
    ∑ i, cutSpectrum z c i = 1 := by
  have h := congrArg Complex.re (cut_positive z c).isHermitian.trace_eq_sum_eigenvalues
  simpa [cutSpectrum, cut_trace, hz, Complex.re_sum] using h.symm

private lemma cut_spectrum_nonneg /- proof_shape: bind-only; consumer: HS4Assembly.hs4_of_spectral_e3 -/ (z : Fin 16 → ℂ) (c : Fin 3) (i : Fin 4) :
    0 ≤ cutSpectrum z c i := (cut_positive z c).eigenvalues_nonneg i

private lemma cut_entropy_spectral /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.M4_entropy -/ (z : Fin 16 → ℂ) (hz : squaredAmplitudeTotal 15 z = 1) (c : Fin 3) :
    vonNeumannEntropy (cutDensity z hz c) = ∑ i, negMulLog (cutSpectrum z c i) := by
  rw [entropy_eq_sum]
  rfl


open Matrix
open scoped BigOperators
set_option maxHeartbeats 0

private lemma trace_power_spectral /- proof_shape: bind-only; consumer: HS4Assembly.spectralE3_trace -/ {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (k : ℕ) :
    (M^k).trace.re = ∑ i, hM.eigenvalues i ^ k := by
  conv_lhs => rw [hM.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.diagonal_pow, Matrix.trace_diagonal, Complex.re_sum]
  simp [← Complex.ofReal_pow]

private lemma spectral_newton /- proof_shape: bind-only; consumer: HS4Assembly.spectralE3_trace -/ (v : Fin 4 → ℝ) (hv : ∑ i, v i = 1) :
    (fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) v =
      (1 - 3*(fun v => dotProduct v v) v + 2*(∑ i, v i ^ 3))/6 := by
  norm_num [Fin.sum_univ_succ] at hv
  change v 0 + (v 1 + (v 2 + v 3)) = 1 at hv
  have h3 : v 3 = 1-v 0-v 1-v 2 := by linarith
  norm_num [Fin.sum_univ_succ, dotProduct, Multiset.esymm, Multiset.powersetCard, Multiset.powersetCardAux, List.sublistsLenAux]
  simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  rw [h3]
  ring

private lemma spectralE3_trace /- proof_shape: bind-only; consumer: HS4Assembly.spectrum_e3_eq_minors -/ (M : Matrix (Fin 4) (Fin 4) ℂ) (hM : M.IsHermitian)
    (htr : M.trace.re = 1) :
    (fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) hM.eigenvalues =
      (1 - 3*(M^2).trace.re + 2*(M^3).trace.re)/6 := by
  have hs : ∑ i, hM.eigenvalues i = 1 := by
    have h := congrArg Complex.re hM.trace_eq_sum_eigenvalues
    simpa [htr, Complex.re_sum] using h.symm
  rw [spectral_newton _ hs, ← trace_power_spectral M hM 3]
  simp only [dotProduct]
  have h2 := trace_power_spectral M hM 2
  have h2' : (M^2).trace.re = ∑ i, hM.eigenvalues i * hM.eigenvalues i := by
    simpa only [pow_two] using h2
  rw [← h2']


private lemma cut_spectral_purity /- proof_shape: bind-only; consumer: HS4Assembly.total_spectral_purity_ge_one -/ (z : Fin 16 → ℂ) (c : Fin 3) :
    (fun v => dotProduct v v) (cutSpectrum z c) = ((cutMatrix z c)^2).trace.re := by
  change (∑ i, (cut_positive z c).isHermitian.eigenvalues i *
      (cut_positive z c).isHermitian.eigenvalues i) = _
  simpa only [pow_two] using
    (trace_power_spectral (cutMatrix z c) (cut_positive z c).isHermitian 2).symm

private lemma total_spectral_purity_ge_one /- proof_shape: bind-only; consumer: HS4Assembly.hs4_of_spectral_e3 -/ (z : Fin 16 → ℂ) (hz : squaredAmplitudeTotal 15 z = 1) :
    1 ≤ ∑ c, (fun v => dotProduct v v) (cutSpectrum z c) := by
  simpa only [cut_spectral_purity, totalPurity_trace] using purity_ge_one z hz

private lemma hs4_of_spectral_e3 /- proof_shape: content; escape_witness: HermiteMajorant.double_contact_nonnegative; consumer: HiguchiSudberyEntropyMaximum.result -/ (z : Fin 16 → ℂ) (hz : squaredAmplitudeTotal 15 z = 1)
    (hE : (∑ c, (fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) (cutSpectrum z c)) ≤ 5/36) :
    averageEntropy z hz ≤ 1 + (1/2)*logb 2 3 := by
  have h := entropy_three_spectra (cutSpectrum z) (cut_spectrum_sum z hz)
    (cut_spectrum_nonneg z) (total_spectral_purity_ge_one z hz) hE
  simpa only [averageEntropy, cut_entropy_spectral] using h



open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private lemma matrix_newton /- proof_shape: bind-only; consumer: HS4Assembly.spectrum_e3_eq_minors -/ (M : Matrix (Fin 4) (Fin 4) ℂ) :
    6*(-(M.charpoly.coeff 1)) = M.trace^3 - 3*M.trace*(M^2).trace + 2*(M^3).trace := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  norm_num (config := {decide := true}) [Matrix.charmatrix_apply,
    Matrix.submatrix, Matrix.diagonal, Matrix.det_fin_three, Fin.sum_univ_succ,
    Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_sum,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.succAbove, Fin.succ,
    Fin.castSucc, Fin.castAdd, Matrix.trace, Matrix.diag, pow_succ, pow_two, Matrix.mul_apply]
  ring!

private lemma cauchy_binet_3_4 /- proof_shape: bind-only; consumer: HS4Assembly.principal_gram_minors -/ (M W : Matrix (Fin 3) (Fin 4) ℂ) :
    (M * Wᵀ).det = ∑ r, (M.submatrix id ((Fin.rev r).succAbove)).det *
      (W.submatrix id ((Fin.rev r).succAbove)).det := by
  norm_num [Matrix.det_fin_three, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix, Fin.rev, Fin.succAbove, Fin.sum_univ_succ]
  ring!

private lemma principal_gram_minors /- proof_shape: bind-only; consumer: HS4Assembly.gram_principalE3 -/ (M W : Matrix (Fin 4) (Fin 4) ℂ) :
    (-((M * Wᵀ).charpoly.coeff 1)) = ∑ r, ∑ c,
      (M.submatrix ((Fin.rev r).succAbove) ((Fin.rev c).succAbove)).det *
      (W.submatrix ((Fin.rev r).succAbove) ((Fin.rev c).succAbove)).det := by
  have hcoeff : (-((M * Wᵀ).charpoly.coeff 1)) =
      ∑ r, ((M * Wᵀ).submatrix ((Fin.rev r).succAbove) ((Fin.rev r).succAbove)).det := by
    rw [Matrix.charpoly, Matrix.det_succ_row_zero]
    norm_num (config := {decide := true}) [Matrix.charmatrix_apply,
      Matrix.submatrix, Matrix.diagonal, Matrix.det_fin_three, Fin.sum_univ_succ,
      Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
      Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_sum,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.succAbove, Fin.succ,
      Fin.rev, Fin.castSucc, Fin.castAdd]
    ring!
  rw [hcoeff]
  apply Finset.sum_congr rfl
  intro r _
  have h : (M * Wᵀ).submatrix ((Fin.rev r).succAbove) ((Fin.rev r).succAbove) =
      M.submatrix ((Fin.rev r).succAbove) id * (W.submatrix ((Fin.rev r).succAbove) id)ᵀ := rfl
  rw [h, cauchy_binet_3_4]
  rfl


open private squaredAmplitudeTotal from D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def literalMinor (z : Fin 16 → ℂ) (c : Fin 3) (r s : Fin 4) : ℂ :=
  ((cutFlatten z c).submatrix ((Fin.rev r).succAbove) ((Fin.rev s).succAbove)).det

private def totalMinorE3 (z : Fin 16 → ℂ) : ℝ :=
  ∑ c, ∑ r, ∑ s, Complex.normSq (literalMinor z c r s)

private lemma det_map_star_3 /- proof_shape: bind-only; consumer: HS4Assembly.gram_principalE3 -/ (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (M.map star).det = star M.det := by
  simp [Matrix.det_fin_three, star_add, star_sub, star_mul, mul_comm]

private lemma gram_principalE3 /- proof_shape: bind-only; consumer: HS4Assembly.spectrum_e3_eq_minors -/ (z : Fin 16 → ℂ) (c : Fin 3) :
    (-((cutMatrix z c).charpoly.coeff 1)) =
      ((∑ r, ∑ s, Complex.normSq (literalMinor z c r s) : ℝ) : ℂ) := by
  rw [cut_gram]
  change (-((cutFlatten z c * ((cutFlatten z c).map star)ᵀ).charpoly.coeff 1)) = _
  rw [principal_gram_minors]
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  change _ * (((cutFlatten z c).submatrix ((Fin.rev r).succAbove) ((Fin.rev s).succAbove)).map star).det = _
  rw [det_map_star_3, Complex.star_def, Complex.mul_conj]
  rfl

private lemma spectrum_e3_eq_minors /- proof_shape: bind-only; consumer: HiguchiSudberyEntropyMaximum.result -/ (z : Fin 16 → ℂ) (hz : squaredAmplitudeTotal 15 z = 1) :
    (∑ c, (fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) (cutSpectrum z c)) = totalMinorE3 z := by
  unfold totalMinorE3
  apply Finset.sum_congr rfl
  intro c _
  rw [show (fun v => (Multiset.ofList [v 0, v 1, v 2, v 3]).esymm 3) (cutSpectrum z c) =
      (1 - 3*((cutMatrix z c)^2).trace.re + 2*((cutMatrix z c)^3).trace.re)/6 from
      spectralE3_trace _ (cut_positive z c).isHermitian (by simp [cut_trace, hz])]
  have h := congrArg Complex.re (matrix_newton (cutMatrix z c))
  rw [gram_principalE3, cut_trace, hz] at h
  norm_num [Complex.mul_re, pow_succ, Complex.add_re, Complex.sub_re] at h ⊢
  linarith

end D5.S3.Quantum.Entanglement.HiguchiSudbery
