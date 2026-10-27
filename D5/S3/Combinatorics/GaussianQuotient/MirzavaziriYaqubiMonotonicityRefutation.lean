/- GID: D5/S3/Combinatorics/GaussianQuotient/MirzavaziriYaqubiMonotonicityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GaussianQuotient/MirzavaziriYaqubiMonotonicityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/GaussianQuotient/MirzavaziriYaqubiMonotonicityRefutation.claim; result=D5/S3/Combinatorics/GaussianQuotient/MirzavaziriYaqubiMonotonicityRefutation.result; claim=D5/S3/Combinatorics/GaussianQuotient/MirzavaziriYaqubiMonotonicityRefutation.claim
   digest: Weak increase of a Gaussian quotient permits an extra negative coefficient. -/

/-
Mirzavaziri--Yaqubi, arXiv:2610.19249v1, Problem 7.2, p. 16.
The polynomial equalities encode the two exact quotients over integer coefficients.
The monotonicity comparisons start at u₁ ≤ u₂, with middle index natDegree(U) / 2.
The degree in the sign pattern is natDegree(P); natural subtraction is truncated.
The existing gauss and qInteger owners are used without redefining them.
The adjacent-coefficient condition is increasingFromOne in claim; its equivalence to
MonotoneOn on the closed interval is used through a private correspondence.

proof_shape: result = bind-only; every private theorem below is bind-only.
escape_witness: none.
admission_basis: open-problem-resolution (#21322; Refuted).
Direct frozen dependencies:
  D5/S0/Certificates/Polynomials/QProductNecessityRefutation.qInteger sha256:1f34579ee25223e26a60c00621daa9d6549df95a00359f2c551a918df36f1577
  D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.gauss sha256:f926774c1dcfc4f25ac8221be84ee089ae2dae1d643c4699259ccb4d03819006
  D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_hook sha256:1033586dcebb24a93692da90f2fc18afdce643e4ce0f1d2aa281ee9cdacb7c18
  D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_symmetry sha256:b83baaa08c18e66ee406173ad88427b09c8adef06bb689ecbfd3fb286955acbf
The dependency identities are declaration statement_id values from the existing Lean report.
Consumers: smallU_degree -> small_increasing; smallP_degree, smallP_bad -> result;
small_gauss_product -> small_first_quotient; small_first_quotient,
small_second_quotient, small_increasing, adjacent_iff_monotoneOn -> result.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Combinatorics.CylindricPartition.LiUncuGaussian
import D5.S0.Certificates.Polynomials.QProductNecessityRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GaussianQuotient.MirzavaziriYaqubiMonotonicityRefutation

open Polynomial
open D5.S3.Combinatorics.CylindricPartition.LiUncuDefs (gauss)
open D5.S0.Certificates.Polynomials.QProductNecessityRefutation (qInteger)

/-- Weak increase from the coefficient of q^1 through the middle of U. -/
def increasingFromOne (U : ℤ[X]) : Prop :=
  ∀ s : ℕ, 2 ≤ s → s ≤ U.natDegree / 2 → U.coeff (s - 1) ≤ U.coeff s

/-- The only negative coefficients are -1 at q^1 and q^(D-1), D = deg P. -/
def twoExceptionSignPattern (P : ℤ[X]) : Prop :=
  P.coeff 1 = -1 ∧ P.coeff (P.natDegree - 1) = -1 ∧
    ∀ t : ℕ, t ≠ 1 → t ≠ P.natDegree - 1 → 0 ≤ P.coeff t

/-- Problem 7.2, final yes/no question, in its polynomial-quotient setting.
`gauss N k` is the existing Gaussian polynomial owner, with its q-Pascal definition.
`qInteger n` is the existing sum 1 + X + ... + X^(n-1), transported from ℕ[X] to ℤ[X].
The two multiplication identities express ordinary exact polynomial quotients.
All defined Gaussian indices 0 ≤ k ≤ N and positive a,b are retained; the numerical
screen's narrower restrictions are not added to the universal assertion. -/
def claim : Prop :=
  ∀ N k a b : ℕ, k ≤ N → 1 ≤ a → 1 ≤ b →
    ∀ U P : ℤ[X],
      gauss N k = (qInteger a).map (Nat.castRingHom ℤ) * U →
      U = (qInteger b).map (Nat.castRingHom ℤ) * P →
      increasingFromOne U →
      twoExceptionSignPattern P



set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

private noncomputable def smallU : ℤ[X] := (1) + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + (2) * X ^ 6 + (2) * X ^ 7 + (2) * X ^ 8 + (3) * X ^ 9 + (3) * X ^ 10 + (3) * X ^ 11 + (4) * X ^ 12 + (4) * X ^ 13 + (5) * X ^ 14 + (5) * X ^ 15 + (6) * X ^ 16 + (6) * X ^ 17 + (7) * X ^ 18 + (7) * X ^ 19 + (8) * X ^ 20 + (9) * X ^ 21 + (9) * X ^ 22 + (10) * X ^ 23 + (11) * X ^ 24 + (11) * X ^ 25 + (12) * X ^ 26 + (13) * X ^ 27 + (13) * X ^ 28 + (13) * X ^ 29 + (14) * X ^ 30 + (14) * X ^ 31 + (14) * X ^ 32 + (15) * X ^ 33 + (15) * X ^ 34 + (15) * X ^ 35 + (15) * X ^ 36 + (15) * X ^ 37 + (15) * X ^ 38 + (15) * X ^ 39 + (15) * X ^ 40 + (15) * X ^ 41 + (15) * X ^ 42 + (14) * X ^ 43 + (14) * X ^ 44 + (14) * X ^ 45 + (13) * X ^ 46 + (13) * X ^ 47 + (13) * X ^ 48 + (12) * X ^ 49 + (11) * X ^ 50 + (11) * X ^ 51 + (10) * X ^ 52 + (9) * X ^ 53 + (9) * X ^ 54 + (8) * X ^ 55 + (7) * X ^ 56 + (7) * X ^ 57 + (6) * X ^ 58 + (6) * X ^ 59 + (5) * X ^ 60 + (5) * X ^ 61 + (4) * X ^ 62 + (4) * X ^ 63 + (3) * X ^ 64 + (3) * X ^ 65 + (3) * X ^ 66 + (2) * X ^ 67 + (2) * X ^ 68 + (2) * X ^ 69 + X ^ 70 + X ^ 71 + X ^ 72 + X ^ 73 + X ^ 75

private noncomputable def smallP : ℤ[X] := (1) + (-1) * X + X ^ 2 + X ^ 6 + X ^ 9 + X ^ 10 + (-1) * X ^ 11 + (2) * X ^ 12 + X ^ 14 + (2) * X ^ 16 + X ^ 18 + X ^ 19 + (2) * X ^ 20 + (2) * X ^ 22 + X ^ 23 + (2) * X ^ 24 + (3) * X ^ 26 + X ^ 27 + X ^ 28 + X ^ 29 + (3) * X ^ 30 + (2) * X ^ 32 + (2) * X ^ 33 + (2) * X ^ 34 + (3) * X ^ 36 + X ^ 37 + X ^ 38 + X ^ 39 + (3) * X ^ 40 + (2) * X ^ 42 + X ^ 43 + (2) * X ^ 44 + (2) * X ^ 46 + X ^ 47 + X ^ 48 + (2) * X ^ 50 + X ^ 52 + (2) * X ^ 54 + (-1) * X ^ 55 + X ^ 56 + X ^ 57 + X ^ 60 + X ^ 64 + (-1) * X ^ 65 + X ^ 66

private theorem smallU_degree : smallU.natDegree = 75 := by
  unfold smallU
  compute_degree!

private theorem smallP_degree : smallP.natDegree = 66 := by
  unfold smallP
  compute_degree!

private theorem smallP_bad : smallP.coeff 11 = -1 := by
  norm_num [smallP, coeff_add, coeff_X_pow, coeff_one, coeff_X]


open D5.S3.Combinatorics.CylindricPartition.LiUncu

private theorem small_gauss_product :
    (1 - X) * (1 - X ^ 2) * (1 - X ^ 3) * gauss 30 3 =
      (1 - X ^ 28) * (1 - X ^ 29) * (1 - X ^ 30) := by
  have h3 : (1 - X ^ 3) * gauss 30 3 = (1 - X ^ 30) * gauss 29 2 := by
    simpa only [gauss_symmetry 30 27 (by decide), gauss_symmetry 29 27 (by decide)]
      using gauss_hook 30 27 (by decide)
  have h2 : (1 - X ^ 2) * gauss 29 2 = (1 - X ^ 29) * gauss 28 1 := by
    simpa only [gauss_symmetry 29 27 (by decide), gauss_symmetry 28 27 (by decide)]
      using gauss_hook 29 27 (by decide)
  have h1 : (1 - X) * gauss 28 1 = 1 - X ^ 28 := by
    have hh : (1 - X ^ 1) * gauss 28 1 = (1 - X ^ 28) * gauss 27 0 := by
      simpa only [gauss_symmetry 28 27 (by decide), gauss_symmetry 27 27 (by decide)]
        using gauss_hook 28 27 (by decide)
    simpa only [show gauss 27 0 = (1 : ℤ[X]) from rfl, pow_one, mul_one] using hh
  linear_combination (1-X)*(1-X^2)*h3 + (1-X)*(1-X^30)*h2 + (1-X^30)*(1-X^29)*h1

private theorem small_first_quotient :
    gauss 30 3 = (qInteger 7).map (Nat.castRingHom ℤ) * smallU := by
  apply mul_left_cancel₀ (a := (1-X)*(1-X^2)*(1-X^3))
  · have hc : ((1-X)*(1-X^2)*(1-X^3) : ℤ[X]).coeff 0 = 1 := by norm_num [coeff_mul]
    intro hz
    rw [hz, coeff_zero] at hc
    norm_num at hc
  · rw [small_gauss_product]
    norm_num [qInteger, Finset.sum_range_succ, smallU]
    ring

private theorem small_second_quotient :
    smallU = (qInteger 10).map (Nat.castRingHom ℤ) * smallP := by
  norm_num [qInteger, Finset.sum_range_succ, smallU, smallP]
  ring

private theorem adjacent_iff_monotoneOn (U : ℤ[X]) :
    (∀ s : ℕ, 2 ≤ s → s ≤ U.natDegree / 2 → U.coeff (s - 1) ≤ U.coeff s) ↔
      MonotoneOn U.coeff (Set.Icc 1 (U.natDegree / 2)) := by
  constructor
  · intro h
    apply monotoneOn_of_le_succ Set.ordConnected_Icc
    intro a _ ha hb
    have ha1 : 1 ≤ a := ha.1
    simpa only [Order.succ_eq_add_one, Nat.add_sub_cancel] using
      h (a + 1) (by omega) (by simpa only [Order.succ_eq_add_one] using hb.2)
  · intro h s hs hu
    exact h ⟨by omega, by omega⟩ ⟨by omega, hu⟩ (by omega)

private theorem small_increasing :
    MonotoneOn smallU.coeff (Set.Icc 1 (smallU.natDegree / 2)) := by
  apply monotoneOn_of_le_succ Set.ordConnected_Icc
  intro s _ hs ht
  have hs1 : 1 ≤ s := hs.1
  have hs36 : s ≤ 36 := by
    have hupper := ht.2
    rw [smallU_degree] at hupper
    change s + 1 ≤ 75 / 2 at hupper
    omega
  interval_cases s <;>
    norm_num [smallU, coeff_add, coeff_X_pow, coeff_one, coeff_X, Order.succ_eq_add_one]

theorem result : ¬ claim := by
  intro h
  have hp := h 30 3 7 10 (by decide) (by decide) (by decide)
    smallU smallP small_first_quotient small_second_quotient
    ((adjacent_iff_monotoneOn smallU).mpr small_increasing)
  have h11 := hp.2.2 11 (by decide) (by rw [smallP_degree]; decide)
  rw [smallP_bad] at h11
  norm_num at h11

end D5.S3.Combinatorics.GaussianQuotient.MirzavaziriYaqubiMonotonicityRefutation
