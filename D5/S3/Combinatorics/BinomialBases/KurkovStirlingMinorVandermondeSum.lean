/- GID: D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum
   generality: I
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Kurkov's three-parameter Stirling-minor Vandermonde sum. -/

/-
admission_basis: open-problem-resolution (#22587; Proved)
escape_witness: result uses complete_corner and elementary_corner on its live proof path.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26118
proof_shape: asc_coeff: content; consumers: first_minor_coeff
proof_shape: monic_coeff_minor: bind-only; consumers: first_minor_coeff
proof_shape: first_minor_coeff: content; consumers: elementary_corner
proof_shape: denom: bind-only; consumers: complete_coeff, complete_corner, complete_recurrence,
  denom_constant, denom_succ, elementary_corner, result, reverse_asc_denom, signed_entry
proof_shape: denom_constant: bind-only; consumers: complete_coeff, complete_recurrence, result
proof_shape: denom_succ: bind-only; consumers: complete_recurrence, reverse_asc_denom
proof_shape: complete_recurrence: bind-only; consumers: complete_coeff
proof_shape: complete_coeff: content; consumers: complete_corner
proof_shape: reverse_asc_denom: bind-only; consumers: signed_entry
proof_shape: trunc_mul: bind-only; consumers: trunc_inverse
proof_shape: trunc_one: bind-only; consumers: trunc_inverse
proof_shape: trunc_inverse: bind-only; consumers: result
proof_shape: B: bind-only; consumers: claim, elementary_corner, result
proof_shape: sourceTerm: bind-only; consumers: chain_normalization, sourceRHS, source_to_moment
proof_shape: sourceRHS: bind-only; consumers: claim, complete_corner, result, source_to_moment,
  source_to_stirling_moment
proof_shape: claim: bind-only; consumers: result
proof_shape: weight: bind-only; consumers: chain_normalization, moment_stirling, source_to_moment,
  source_to_stirling_moment
proof_shape: chain_normalization: bind-only; consumers: source_to_moment
proof_shape: source_to_moment: content; consumers: source_to_stirling_moment
proof_shape: moment_stirling: bind-only; consumers: source_to_stirling_moment
proof_shape: source_to_stirling_moment: content; consumers: complete_corner
proof_shape: sign_revQ: bind-only; consumers: complete_corner, inverse_corner_minor
proof_shape: reversal_sign_identity: bind-only; consumers: inverse_corner_minor
proof_shape: inverse_corner_minor: bind-only; consumers: result
proof_shape: signed_entry: bind-only; consumers: elementary_corner
proof_shape: elementary_corner: content; consumers: result
proof_shape: complete_corner: content; consumers: result
proof_shape: result: content; consumers: actual_positive
Direct frozen dependencies of result, with same-delivery suppliers inlined:
The identities below are declaration statement_id values from the cached base report.
  D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.Chain
    statement_id: sha256:d1554ebf9e75f36f3ced9563fb0ab2ff7d888727ca9f0e7e3aeb537668db77a5
  D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.instFintypeChain
    statement_id: sha256:a70e0af04d1a5ca13e73d1d57de375f4ef14721f5838e3ba666ade834a586c4f
  D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion
    statement_id: sha256:2508e114d7ae0d003f3f1c2ca5079a26811c8ed501add6239b68109ce2a28efb
  D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction.pronyHankel
    statement_id: sha256:702c9e73ec3c764c92bcad3aeafeec33523bc39b289e788db921b6c63ec05946
  D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction.pronyMoment
    statement_id: sha256:a6ddd7a83631464c427435a5aee6a75221000b9387ecb008b75dfcaf25e3e978
  D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction.pronyVandermonde
    statement_id: sha256:e12c8944a864291c124be15b895c8d58ce136b7d3ae4558e5c38271ce89f5509
  D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction.prony_hankel_factorization
    statement_id: sha256:d090c619a29632cd61360b3451c1507e66e116acbfcb60acb92a9612266d1fc1
  D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.det_toeplitz
    statement_id: sha256:f5f5ba18767a664eb12c453042c187f6d396cfaecb5e199d6de5f6c2931bd790
  D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.smat
    statement_id: sha256:d38827d80e6c6e11c3b023305d629177bf1b77b6eaed609423c8877f54a48958
  D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.toeplitz
    statement_id: sha256:d2f5f0d911b42db7277638704e1920a7608fd1b9606e1cf09603196ea433b710
  D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.toeplitz_mul
    statement_id: sha256:9bc9bee3ec4853ef9f5f2a2bb0e204a110bd91af57e84ea3701957bc04e06b69
  D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.weight
    statement_id: sha256:8f604afadbeee5d7bcf08d03461211f826ac79a5e58325bb0641119ce3818dd2
  D5/S3/Arith/AbsoluteValues/Heights/Duality.det_submatrix_inl_eq_mul
    statement_id: sha256:89e88692d0008f179c4377269f3e9e157b7d11da699715072bac2274077b5b6c
  D5/S3/Arith/AbsoluteValues/Heights/Duality.enumEquiv
    statement_id: sha256:e873b73d44b33d43d6e9206a79bdf5a9cb19680fcad0a4083559a7a74afa1a7a
  D5/S3/Quantum/Schatten/CompoundMatrices.cauchyBinet
    statement_id: sha256:6fb332c198d4506b8775454dff648409222d03ae0a60e7dbf5fca62ea37506df
The claim retains the literal source expressions and the original Chain carrier.
Proofs use the original private chain/subset, Toeplitz and complementary-minor declarations.
The two Duality declarations and their owning source, Scribe and pin are unchanged.
-/

import D5.S1.Recurrence.Algebraic.KurkovNestedStirlingIdentity
import D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserShiftedG
import D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk
import D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod
import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Schatten.CompoundMatrices
import D5.S3.Arith.AbsoluteValues.Heights.Duality

namespace D5.S3.Combinatorics.BinomialBases.KurkovStirlingMinorVandermondeSum

open private chainNodes chainEquiv sign_rev from
  D5.S1.Recurrence.Algebraic.KurkovNestedStirlingIdentity
open private D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk.weight from
  D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk

open Finset BigOperators Polynomial Matrix
open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
open D5.S1.Recurrence.Algebraic.KurkovNestedStirlingIdentity (Chain)

private theorem asc_coeff (n k : ℕ) :
    (ascPochhammer ℚ n).coeff k = (Nat.stirlingFirst n k : ℚ) := by
  induction n generalizing k
  case zero => cases k <;> simp [Polynomial.coeff_one]
  case succ n ih =>
    rw [ascPochhammer_succ_right, mul_add, coeff_add]
    cases k
    case zero => cases n <;> simp [ih]
    case succ k => simp [ih, Nat.stirlingFirst_succ_succ, mul_comm, add_comm]

private theorem monic_coeff_minor {d : ℕ} (p : ℚ[X]) (q : Fin d → ℚ[X])
    (index : Fin d → ℕ) (hdeg : ∀ i, (q i).natDegree = i.val)
    (hmonic : ∀ i, (q i).Monic) :
    Matrix.det (fun i j : Fin d => (p*q i).coeff (index j)) =
      Matrix.det (fun i j : Fin d => (p*X^i.val).coeff (index j)) := by
  classical
  let C : Matrix (Fin d) (Fin d) ℚ := fun i r => (q i).coeff r.val
  let T : Matrix (Fin d) (Fin d) ℚ := fun i j => (p*X^i.val).coeff (index j)
  have factor : (fun i j : Fin d => (p*q i).coeff (index j)) = C*T := by
    ext i j
    have exp : q i = ∑ r : Fin d, Polynomial.C ((q i).coeff r.val)*X^r.val := by
      rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => Polynomial.C ((q i).coeff r)*X^r) d]
      exact (q i).as_sum_range_C_mul_X_pow' (by rw [hdeg]; exact i.isLt)
    have hp : p*q i = ∑ r : Fin d, Polynomial.C ((q i).coeff r.val)*(p*X^r.val) := by
      conv_lhs => rw [exp, mul_sum]
      apply sum_congr rfl
      intro r _
      ring
    have hc := congrArg (fun f : ℚ[X] => f.coeff (index j)) hp
    change (p*q i).coeff (index j) = ∑ r : Fin d, (q i).coeff r.val *
      (p*X^r.val).coeff (index j)
    simpa only [finsetSum_coeff, coeff_C_mul] using hc
  have hC : C.det = 1 := by
    rw [← Matrix.det_transpose]
    exact Matrix.det_matrixOfPolynomials q hdeg hmonic
  rw [factor, Matrix.det_mul, hC, one_mul]

private theorem first_minor_coeff (n k m : ℕ) :
    Matrix.det (fun i j : Fin k =>
      (Nat.stirlingFirst (n+m+(i.val+1)) (n+(j.val+1)) : ℚ)) =
    Matrix.det (fun i j : Fin k =>
      ((ascPochhammer ℚ (n+m+1))*X^i.val).coeff (n+(j.val+1))) := by
  let q : Fin k → ℚ[X] := fun i =>
    (ascPochhammer ℚ i.val).comp (X + Polynomial.C ((n+m+1 : ℕ) : ℚ))
  have deg (i : Fin k) : (q i).natDegree = i.val := by
    change ((ascPochhammer ℚ i.val).comp (X+Polynomial.C ((n+m+1 : ℕ) : ℚ))).natDegree = i.val
    rw [Polynomial.natDegree_comp, ascPochhammer_natDegree, natDegree_X_add_C, mul_one]
  have monic (i : Fin k) : (q i).Monic := by
    apply (monic_ascPochhammer ℚ i.val).comp (monic_X_add_C _)
    rw [natDegree_X_add_C]
    exact Nat.one_ne_zero
  have identity (i : Fin k) : ascPochhammer ℚ (n+m+(i.val+1)) =
      ascPochhammer ℚ (n+m+1)*q i := by
    dsimp [q]
    rw [C_eq_natCast, ascPochhammer_mul]
    congr 1
    omega
  calc
    _ = Matrix.det (fun i j : Fin k =>
      (ascPochhammer ℚ (n+m+1)*q i).coeff (n+(j.val+1))) := by
        congr 1
        funext i j
        rw [← identity, asc_coeff]
    _ = _ := monic_coeff_minor _ q _ deg monic

private noncomputable def denom (N : ℕ) : PowerSeries ℚ :=
  ∏ a ∈ range N, (1-PowerSeries.C ((a+1 : ℕ) : ℚ)*PowerSeries.X)

private theorem denom_constant (N : ℕ) : PowerSeries.constantCoeff (denom N) = 1 := by
  simp [denom]

private theorem denom_succ (N : ℕ) :
    denom (N+1) = denom N*(1-PowerSeries.C ((N+1 : ℕ) : ℚ)*PowerSeries.X) := by
  exact prod_range_succ _ N

private theorem complete_recurrence (N : ℕ) :
    (1-PowerSeries.C ((N+1 : ℕ) : ℚ)*PowerSeries.X)*(denom (N+1))⁻¹ = (denom N)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [denom_constant]; norm_num :
    PowerSeries.constantCoeff (denom N) ≠ 0)).mpr
  change _*(denom N) = 1
  rw [show (1-PowerSeries.C ((N+1 : ℕ) : ℚ)*PowerSeries.X)*(denom (N+1))⁻¹*denom N =
    denom (N+1)*(denom (N+1))⁻¹ by rw [denom_succ]; ring]
  exact PowerSeries.mul_inv_cancel _ (by rw [denom_constant]; norm_num)

private theorem complete_coeff (N r : ℕ) :
    PowerSeries.coeff r ((denom N)⁻¹) = (Nat.stirlingSecond (N+r) N : ℚ) := by
  induction N generalizing r
  case zero =>
    have hz : (denom 0)⁻¹ = 1 := by simp [denom]
    rw [hz]
    cases r <;> simp
  case succ N ih =>
    induction r
    case zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, denom_constant, Nat.stirlingSecond_self]
    case succ r ihr =>
      have h := congrArg (PowerSeries.coeff (r+1)) (complete_recurrence N)
      simp only [sub_mul, one_mul, mul_assoc, map_sub,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] at h
      rw [ih, ihr] at h
      rw [show N+1+(r+1) = (N+1+r)+1 by omega, Nat.stirlingSecond_succ_succ]
      push_cast
      have hs : N+(r+1) = N+1+r := by omega
      rw [hs] at h
      push_cast at h
      linarith

private theorem reverse_asc_denom (N : ℕ) :
    PowerSeries.rescale (-1 : ℚ)
      (((ascPochhammer ℚ (N+1)).reverse : ℚ[X]) : PowerSeries ℚ) = denom N := by
  have revOne : (1 : ℚ[X]).reverse = 1 := by
    simpa only [Polynomial.C_1] using (Polynomial.reverse_C (1 : ℚ))
  have revX : (X : ℚ[X]).reverse = 1 := by
    simpa only [one_mul, revOne] using (Polynomial.reverse_mul_X (1 : ℚ[X]))
  have revlin (a : ℕ) : (X+(a : ℚ[X])).reverse = 1+Polynomial.C (a : ℚ)*X := by
    change (X+Polynomial.C (a : ℚ)).reverse = _
    simp only [Polynomial.reverse_add_C, revX, natDegree_X, pow_one]
  induction N
  case zero => simp [ascPochhammer_one, revX, denom]
  case succ N ih =>
    rw [show N+1+1 = (N+1)+1 by omega, ascPochhammer_succ_right,
      reverse_mul_of_domain, Polynomial.coe_mul, map_mul, ih, denom_succ]
    congr 1
    rw [revlin]
    simp only [Polynomial.coe_add, Polynomial.coe_one,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, map_add, map_one,
      map_mul, PowerSeries.rescale_neg_one_X]
    apply PowerSeries.ext
    intro r
    by_cases h0 : r=0
    · subst r; simp
    · simp [h0]

open Finset BigOperators Matrix
open private smat toeplitz toeplitz_mul det_toeplitz from
  D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserShiftedG

private theorem trunc_mul (d : ℕ) (f g : PowerSeries ℚ) :
    (toeplitz (f*g) d) = (toeplitz f d) * (toeplitz g d) := by
  have hx (h : PowerSeries ℚ) :
      smat (fun r => h * PowerSeries.X^r) d = (toeplitz h d) := by
    ext i j
    simp only [smat, toeplitz, PowerSeries.coeff_mul_X_pow']
  have h := toeplitz_mul f (fun r => g * PowerSeries.X^r) d
  change (toeplitz f d) * smat (fun r => g * PowerSeries.X^r) d =
    smat (fun r => f * (g * PowerSeries.X^r)) d at h
  rw [hx] at h
  have hr : smat (fun r => f * (g * PowerSeries.X^r)) d = (toeplitz (f*g) d) := by
    simpa only [mul_assoc] using hx (f*g)
  rw [hr] at h
  exact h.symm

private theorem trunc_one (d : ℕ) : (toeplitz 1 d) = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [toeplitz]
  · by_cases hji : j ≤ i
    · have hsub : i.val-j.val ≠ 0 := by
        have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
        change j.val ≤ i.val at hji
        omega
      simp [toeplitz, hji, hsub, hij]
    · simp [toeplitz, hji, hij]

private theorem trunc_inverse (d : ℕ) (f g : PowerSeries ℚ) (hfg : f*g=1) :
    (toeplitz f d) * (toeplitz g d) = 1 := by
  rw [← trunc_mul, hfg, trunc_one]

/-- The source determinant, with i,j = 1,...,k represented by Fin k plus one. -/
def B (n k m : ℕ) : ℚ :=
  Matrix.det (fun i j : Fin k =>
    (Nat.stirlingFirst (n + m + (i.val + 1)) (n + (j.val + 1)) : ℚ))

/-- The literal summand: source t = t.val+1 and 1 <= q < p <= m. -/
def sourceTerm {n m : ℕ} (k : ℕ) (j : Chain n m) : ℚ :=
  (-1 : ℚ) ^ (∑ t : Fin m, (j.val t).val) *
    (∏ q : Fin m, ∏ p ∈ Ioi q,
      (((j.val q).val : ℚ) - (j.val p).val + p.val - q.val) ^ 2) *
    ∏ t : Fin m,
      ((n + t.val).descFactorial (j.val t).val : ℚ) *
        ((n - (j.val t).val + (t.val + 1) : ℕ) : ℚ) ^ (n + k) /
          (((j.val t).val + m - (t.val + 1)).factorial : ℚ)

/-- The entire nested sum divided by the product of (n+i)! for i=0,...,m-1. -/
noncomputable def sourceRHS (n k m : ℕ) : ℚ :=
  (∑ j : Chain n m, sourceTerm k j) /
    (∏ i : Fin m, ((n + i.val).factorial : ℚ))

/-- OEIS A396563, sole FORMULA conjecture, with all natural parameters explicit. -/
def claim : Prop :=
  ∀ (n : ℕ) (k : ℕ) (m : ℕ), 1 ≤ m → B n k m = sourceRHS n k m

open Finset BigOperators Matrix
open D5.S1.Recurrence.Algebraic.KurkovNestedStirlingIdentity (Chain)
set_option maxHeartbeats 800000
private def weight (n k m l : ℕ) : ℚ :=
  - D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk.weight (n+m) (l+1) *
    ((l+1 : ℕ) : ℚ) ^ (n+k+1)

private theorem chain_normalization (n k m : ℕ) (j : Chain n m) :
    sourceTerm k j / (∏ i : Fin m, ((n+i.val).factorial : ℚ)) =
      (-1 : ℚ) ^ (n*m + m*(m-1)/2) *
        (∏ q : Fin m, ∏ p ∈ Ioi q, (((chainNodes j p).val : ℚ) - (chainNodes j q).val))^2 *
        ∏ i : Fin m, weight n k m (chainNodes j i).val := by
  have atom (i : Fin m) :
      ((n + i.val).descFactorial (j.val i).val : ℚ) *
        ((n - (j.val i).val + (i.val + 1) : ℕ) : ℚ) ^ (n+k) /
          (((j.val i).val + m - (i.val+1)).factorial : ℚ) =
      ((n+i.val).factorial : ℚ) * ((n+m).choose ((chainNodes j i).val+1) : ℚ) *
        (((chainNodes j i).val+1 : ℕ) : ℚ) ^ (n+k+1) / (n+m).factorial := by
    have hj := (j.val i).isLt
    have hi := i.isLt
    let l := (chainNodes j i).val
    have hl : l = n - (j.val i).val + i.val := rfl
    have hA : n+i.val-(j.val i).val = l := by omega
    have hC : (j.val i).val + m - (i.val+1) = n+m-(l+1) := by omega
    have hL : n-(j.val i).val+(i.val+1) = l+1 := by omega
    have hlN : l+1 ≤ n+m := by omega
    have hdesc : (l.factorial : ℚ) * (n+i.val).descFactorial (j.val i).val =
        (n+i.val).factorial := by
      exact_mod_cast (hA ▸ Nat.factorial_mul_descFactorial (show (j.val i).val ≤ n+i.val by omega))
    have hchoose : ((n+m).choose (l+1) : ℚ) *
        (l+1) * l.factorial * (n+m-(l+1)).factorial = (n+m).factorial := by
      have h := Nat.choose_mul_factorial_mul_factorial hlN
      rw [Nat.factorial_succ] at h
      exact_mod_cast (show (n+m).choose (l+1) * (l+1) * l.factorial *
        (n+m-(l+1)).factorial = (n+m).factorial by simpa only [mul_assoc] using h)
    have hfac (a : ℕ) : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
    have hdp : ((n+i.val).descFactorial (j.val i).val : ℚ) =
        (n+i.val).factorial / (l.factorial : ℚ) := by
      apply (eq_div_iff (hfac l)).2
      simpa [mul_comm] using hdesc
    have hc : ((n+m).choose (l+1) : ℚ) =
        (n+m).factorial / (((l+1 : ℕ) : ℚ) * l.factorial * (n+m-(l+1)).factorial) := by
      apply (eq_div_iff (by positivity : (((l+1 : ℕ) : ℚ) * l.factorial * (n+m-(l+1)).factorial) ≠ 0)).2
      simpa [mul_assoc] using hchoose
    change _ = (n+i.val).factorial * ((n+m).choose (l+1) : ℚ) *
      ((l+1 : ℕ) : ℚ) ^ (n+k+1) / (n+m).factorial
    rw [hdp, hC, hL, hc, pow_succ]
    field_simp
  have sign : (-1 : ℚ) ^ (∑ i, (j.val i).val) =
      (-1 : ℚ) ^ (n*m + m*(m-1)/2) *
        ∏ i : Fin m, (-1 : ℚ) ^ (chainNodes j i).val := by
    have hs : (∑ i : Fin m, (j.val i).val) +
        (∑ i : Fin m, (chainNodes j i).val) = n*m + m*(m-1)/2 := by
      rw [← sum_add_distrib]
      calc
        _ = ∑ i : Fin m, (n+i.val) := by
          apply sum_congr rfl
          intro i _
          change (j.val i).val + (n-(j.val i).val+i.val) = n+i.val
          have := (j.val i).isLt
          omega
        _ = _ := by
          simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
          rw [mul_comm m n]
          congr 1
          exact (Fin.sum_univ_eq_sum_range (fun i => i) m).trans (sum_range_id m)
    rw [prod_pow_eq_pow_sum, ← pow_add]
    conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
    conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
    congr 1
    omega
  have vand : (∏ q : Fin m, ∏ p ∈ Ioi q,
      (((j.val q).val : ℚ) - (j.val p).val + p.val - q.val)^2) =
      (∏ q : Fin m, ∏ p ∈ Ioi q, (((chainNodes j p).val : ℚ) - (chainNodes j q).val))^2 := by
    rw [← prod_pow]
    apply prod_congr rfl
    intro q _
    rw [← prod_pow]
    apply prod_congr rfl
    intro p _
    congr 1
    change _ = ((n-(j.val p).val+p.val : ℕ) : ℚ) - ((n-(j.val q).val+q.val : ℕ) : ℚ)
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (by have := (j.val p).isLt; omega),
      Nat.cast_sub (by have := (j.val q).isLt; omega)]
    ring
  have hw (l : ℕ) : weight n k m l =
      (-1 : ℚ)^l * ((n+m).choose (l+1) : ℚ) *
        ((l+1 : ℕ) : ℚ)^(n+k+1) / (n+m).factorial := by
    simp only [weight, D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk.weight,
      pow_succ]
    ring
  simp only [sourceTerm, atom, sign, vand, hw]
  simp only [prod_div_distrib, prod_mul_distrib]
  have hF : (∏ i : Fin m, ((n+i.val).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast Nat.factorial_ne_zero (n+i.val)
  field_simp

private theorem source_to_moment (n k m : ℕ) :
    sourceRHS n k m = (-1 : ℚ) ^ (n*m + m*(m-1)/2) * ((pronyHankel (n := m) (fun l : Fin (n+m) => ((l.val+1 : ℕ) : ℚ)) (fun l : Fin (n+m) => weight n k m l.val))).det := by
  classical
  let A : Matrix (Fin m) (Fin (n+m)) ℚ := fun i l => ((l.val+1 : ℕ) : ℚ)^i.val
  let BB : Matrix (Fin (n+m)) (Fin m) ℚ := fun l j =>
    weight n k m l.val * ((l.val+1 : ℕ) : ℚ)^j.val
  have factor : (pronyHankel (n := m) (fun l : Fin (n+m) => ((l.val+1 : ℕ) : ℚ)) (fun l : Fin (n+m) => weight n k m l.val)) = A * BB := by
    rw [prony_hankel_factorization, Matrix.mul_assoc]
    congr 1
    ext l j
    simp only [Matrix.diagonal_mul, Matrix.transpose_apply, pronyVandermonde, BB]
  have minor (s : {s : Finset (Fin (n + m)) // s.card = m}) :
      (A.submatrix id (s.val.orderEmbOfFin s.property)).det *
        (BB.submatrix (s.val.orderEmbOfFin s.property) id).det =
      (∏ q : Fin m, ∏ p ∈ Ioi q, (((s.val.orderEmbOfFin s.property p).val : ℚ) - (s.val.orderEmbOfFin s.property q).val))^2 *
        ∏ i : Fin m, weight n k m (s.val.orderEmbOfFin s.property i).val := by
    let l := s.val.orderEmbOfFin s.property
    let v : Fin m → ℚ := fun i => ((l i).val+1 : ℕ)
    have ha : A.submatrix id l = (Matrix.vandermonde v).transpose := rfl
    have hb : BB.submatrix l id =
        Matrix.of (fun i j => weight n k m (l i).val * Matrix.vandermonde v i j) := rfl
    have hv : (Matrix.vandermonde v).det = (∏ q : Fin m, ∏ p ∈ Ioi q, (((l p).val : ℚ) - (l q).val)) := by
      rw [Matrix.det_vandermonde]
      apply prod_congr rfl
      intro q _
      apply prod_congr rfl
      intro pp _
      simp only [v, Nat.cast_add, Nat.cast_one]
      ring
    rw [ha, hb, Matrix.det_transpose, Matrix.det_mul_column, hv]
    ring
  have reindex :
      (∑ j : Chain n m, (∏ q : Fin m, ∏ p ∈ Ioi q, (((chainNodes j p).val : ℚ) - (chainNodes j q).val))^2 *
        ∏ i : Fin m, weight n k m (chainNodes j i).val) =
      ∑ s : {s : Finset (Fin (n + m)) // s.card = m}, (∏ q : Fin m, ∏ p ∈ Ioi q, (((s.val.orderEmbOfFin s.property p).val : ℚ) - (s.val.orderEmbOfFin s.property q).val))^2 *
        ∏ i : Fin m, weight n k m (s.val.orderEmbOfFin s.property i).val := by
    apply Fintype.sum_equiv (chainEquiv n m)
    intro j
    have hs : (chainEquiv n m j).val.orderEmbOfFin (chainEquiv n m j).property =
        chainNodes j :=
      (orderEmbOfFin_unique' _ (fun i => mem_image_of_mem _ (mem_univ i))).symm
    rw [hs]
  have hminors :
      (∑ s : {s : Finset (Fin (n+m)) // s.card = m},
        (A.submatrix id (s.val.orderEmbOfFin s.property)).det *
          (BB.submatrix (s.val.orderEmbOfFin s.property) id).det) =
      ∑ s : {s : Finset (Fin (n + m)) // s.card = m}, (∏ q : Fin m, ∏ p ∈ Ioi q, (((s.val.orderEmbOfFin s.property p).val : ℚ) - (s.val.orderEmbOfFin s.property q).val))^2 *
        ∏ i : Fin m, weight n k m (s.val.orderEmbOfFin s.property i).val := by
    apply Fintype.sum_equiv (Equiv.refl _)
    intro s
    exact minor s
  rw [factor, cauchyBinet, hminors, ← reindex, mul_sum]
  unfold sourceRHS
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro j _
  simpa only [mul_assoc] using chain_normalization n k m j

private theorem moment_stirling (n k m r : ℕ) :
    pronyMoment (fun l : Fin (n+m) => ((l.val+1 : ℕ) : ℚ)) (fun l : Fin (n+m) => weight n k m l.val) r = (-1 : ℚ)^(n+m+1) *
      (Nat.stirlingSecond (n+k+1+r) (n+m) : ℚ) := by
  classical
  let N := n+m
  let R := n+k+1+r
  have hR : R ≠ 0 := by dsimp [R]; omega
  have hs := D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion R N
  have hsQ : (∑ z ∈ range (N+1), (-1 : ℚ)^(N-z) * (N.choose z : ℚ) * (z : ℚ)^R) =
      (N.factorial : ℚ) * (Nat.stirlingSecond R N : ℚ) := by
    exact_mod_cast hs.symm
  rw [sum_range_succ'] at hsQ
  simp only [Nat.cast_zero, zero_pow hR, mul_zero, add_zero] at hsQ
  have shifted : (∑ l : Fin N, (-1 : ℚ)^l.val * (N.choose (l.val+1) : ℚ) *
      ((l.val+1 : ℕ) : ℚ)^R) =
      (-1 : ℚ)^(N+1) * ((N.factorial : ℚ) * (Nat.stirlingSecond R N : ℚ)) := by
    rw [← hsQ, mul_sum,
      Fin.sum_univ_eq_sum_range (fun l : ℕ => (-1 : ℚ)^l * (N.choose (l+1) : ℚ) *
        ((l+1 : ℕ) : ℚ)^R) N]
    apply sum_congr rfl
    intro l hl
    have hlN : l+1 ≤ N := by have := mem_range.mp hl; omega
    have hsign : (-1 : ℚ)^l = (-1 : ℚ)^(N+1) * (-1 : ℚ)^(N-(l+1)) := by
      rw [← pow_add]
      conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
      conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
      congr 1
      omega
    rw [hsign]
    ring
  have expr : pronyMoment (fun l : Fin (n+m) => ((l.val+1 : ℕ) : ℚ)) (fun l : Fin (n+m) => weight n k m l.val) r =
      (∑ l : Fin N, (-1 : ℚ)^l.val * (N.choose (l.val+1) : ℚ) *
        ((l.val+1 : ℕ) : ℚ)^R) / (N.factorial : ℚ) := by
    simp only [pronyMoment, weight,
      D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk.weight,
      N, R, Finset.sum_div, pow_add, pow_succ, mul_neg_one, neg_mul, neg_div, neg_neg]
    apply sum_congr rfl
    intro l _
    ring
  rw [expr, shifted]
  have hfac : (N.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  dsimp [N, R] at *
  field_simp

private theorem source_to_stirling_moment (n k m : ℕ) :
    sourceRHS n k m = (-1 : ℚ)^(m*(m-1)/2) * Matrix.det (fun i j : Fin m => (Nat.stirlingSecond (n+k+1+i.val+j.val) (n+m) : ℚ)) := by
  have hm : (pronyHankel (n := m) (fun l : Fin (n+m) => ((l.val+1 : ℕ) : ℚ)) (fun l : Fin (n+m) => weight n k m l.val)) = (-1 : ℚ)^(n+m+1) • Matrix.of (fun i j : Fin m => (Nat.stirlingSecond (n+k+1+i.val+j.val) (n+m) : ℚ)) := by
    ext i j
    simpa only [pronyHankel, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Nat.add_assoc]
      using moment_stirling n k m (i.val+j.val)
  rw [source_to_moment, hm, Matrix.det_smul, Fintype.card_fin]
  rw [← mul_assoc]
  congr 1
  rw [← pow_mul, ← pow_add]
  rw [show n*m + m*(m-1)/2 + (n+m+1)*m =
    m*(m-1)/2 + 2*(n*m) + m*(m+1) by ring, pow_add, pow_add]
  rw [Even.neg_one_pow (even_two_mul (n*m)), Even.neg_one_pow (Nat.even_mul_succ_self m)]
  ring

open BigOperators
set_option maxHeartbeats 800000
private theorem sign_revQ (d : ℕ) :
    ((Equiv.Perm.sign (@Fin.revPerm d) : ℤˣ) : ℚ) = (-1 : ℚ)^(d*(d-1)/2) := by
  rw [sign_rev]
  simp only [Units.val_pow_eq_pow_val, Int.cast_pow, Units.val_neg, Units.val_one,
    Int.cast_neg, Int.cast_one]

private theorem reversal_sign_identity (k m : ℕ) :
    (-1 : ℚ)^(k*(k-1)/2) * (-1 : ℚ)^((k+m)*(k+m-1)/2) *
      (-1 : ℚ)^(m*(m-1)/2) = (-1 : ℚ)^(k*m) := by
  have hs : (k+m)*(k+m-1)/2 = k*(k-1)/2 + m*(m-1)/2 + k*m := by
    rw [← sum_range_id, sum_range_add]
    change (Finset.sum (range k) (fun x => x)) + (Finset.sum (range m) (fun x => k+x)) =
      k*(k-1)/2 + m*(m-1)/2 + k*m
    rw [Finset.sum_add_distrib, sum_const, card_range, smul_eq_mul]
    simp only [sum_range_id]
    ring
  have hsq (a : ℕ) : (-1 : ℚ)^a * (-1 : ℚ)^a = 1 :=
    pow_mul_pow_eq_one a (by norm_num)
  rw [hs, pow_add, pow_add]
  calc
    _ = ((-1 : ℚ)^(k*(k-1)/2) * (-1 : ℚ)^(k*(k-1)/2)) *
        ((-1 : ℚ)^(m*(m-1)/2) * (-1 : ℚ)^(m*(m-1)/2)) * (-1 : ℚ)^(k*m) := by ring
    _ = _ := by rw [hsq, hsq]; ring

/-- Jacobi comparison for the two rectangular corner minors of inverse matrices. -/
private theorem inverse_corner_minor (k m : ℕ) (A H : Matrix (Fin (k+m)) (Fin (k+m)) ℚ)
    (hAH : A*H=1) (hA : A.det=1) :
    Matrix.det (fun i j : Fin k => A ⟨m+i.val, by omega⟩ ⟨j.val, by omega⟩) =
      (-1 : ℚ)^(k*m) *
        Matrix.det (fun i j : Fin m => H ⟨k+i.val, by omega⟩ ⟨j.val, by omega⟩) := by
  classical
  let e : Fin k ⊕ Fin m ≃ Fin (k+m) := finSumFinEquiv
  let σ : Fin k ⊕ Fin m ≃ Fin (k+m) := e.trans Fin.revPerm
  let C := A.submatrix σ id
  let D := Hᵀ.submatrix σ id
  let S : Finset (Fin (k+m)) := univ.image (Fin.castAdd m : Fin k → Fin (k+m))
  have hs : S.card=k := by
    dsimp [S]
    rw [card_image_of_injective _ (Fin.castAdd_injective k m)]
    simp
  have hsc : Sᶜ.card=m := by
    rw [card_compl, Fintype.card_fin, hs]
    omega
  have first : S.orderEmbOfFin hs = Fin.castAddOrderEmb m := by
    symm
    apply orderEmbOfFin_unique' hs (f := Fin.castAddOrderEmb m)
    intro i
    exact mem_image_of_mem (Fin.castAdd m) (mem_univ i)
  have last : Sᶜ.orderEmbOfFin hsc = Fin.natAddOrderEmb k := by
    symm
    apply orderEmbOfFin_unique' hsc (f := Fin.natAddOrderEmb k)
    intro i
    rw [mem_compl]
    simp only [S, mem_image, mem_univ, true_and, not_exists]
    intro j hj
    have hv := congrArg Fin.val hj
    have := j.isLt
    change j.val = k+i.val at hv
    omega
  have en : Matrix.enumEquiv hs hsc = e := by
    apply Equiv.ext
    intro x
    cases x
    case inl i =>
      change S.orderEmbOfFin hs i = Fin.castAdd m i
      rw [first]
      rfl
    case inr i =>
      change Sᶜ.orderEmbOfFin hsc i = Fin.natAdd k i
      rw [last]
      rfl
  have hCD : C*Dᵀ=1 := by
    have hh : C*Dᵀ = (A*H).submatrix σ σ := by
      change A.submatrix σ id * H.submatrix id σ = (A*H).submatrix σ σ
      exact Matrix.submatrix_mul_equiv A H σ (Equiv.refl _) σ
    rw [hh, hAH]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.one_apply, σ.injective.eq_iff]
  have h := Matrix.det_submatrix_inl_eq_mul C D hCD hs hsc
  have hc : (C.submatrix id (Matrix.enumEquiv hs hsc)).det =
      (-1 : ℚ)^((k+m)*(k+m-1)/2) := by
    rw [en]
    have hh : C.submatrix id e = (A.submatrix Fin.revPerm id).submatrix e e := rfl
    rw [hh, Matrix.det_submatrix_equiv_self, Matrix.det_permute, sign_revQ, hA, mul_one]
  have hleft : ((C.submatrix Sum.inl id).submatrix id (S.orderEmbOfFin hs)).det =
      (-1 : ℚ)^(k*(k-1)/2) *
        Matrix.det (fun i j : Fin k => A ⟨m+i.val, by omega⟩ ⟨j.val, by omega⟩) := by
    rw [first]
    let T : Matrix (Fin k) (Fin k) ℚ := fun i j => A ⟨m+i.val, by omega⟩ ⟨j.val, by omega⟩
    have hh : (C.submatrix Sum.inl id).submatrix id (Fin.castAddOrderEmb m) =
        T.submatrix Fin.revPerm id := by
      ext i j
      dsimp [C, σ, e, T, Matrix.submatrix]
      congr 1
      apply Fin.ext
      simp only [Fin.revPerm_apply,
        Fin.val_rev, Fin.val_castAdd]
      have := i.isLt
      omega
    rw [hh, Matrix.det_permute, sign_revQ]
  have hright : ((D.submatrix Sum.inr id).submatrix id (Sᶜ.orderEmbOfFin hsc)).det =
      (-1 : ℚ)^(m*(m-1)/2) *
        Matrix.det (fun i j : Fin m => H ⟨k+i.val, by omega⟩ ⟨j.val, by omega⟩) := by
    rw [last]
    let T : Matrix (Fin m) (Fin m) ℚ := fun i j => H ⟨k+i.val, by omega⟩ ⟨j.val, by omega⟩
    have hh : (D.submatrix Sum.inr id).submatrix id (Fin.natAddOrderEmb k) =
        (T.submatrix id Fin.revPerm)ᵀ := by
      ext i j
      dsimp [D, σ, e, T, Matrix.submatrix, Matrix.transpose]
      congr 1
      apply Fin.ext
      simp only [Fin.revPerm_apply,
        Fin.val_rev, Fin.val_natAdd]
      have := i.isLt
      omega
    rw [hh, Matrix.det_transpose, Matrix.det_permute', sign_revQ]
  rw [hleft, hc, hright] at h
  have hsq : (-1 : ℚ)^(k*(k-1)/2) * (-1 : ℚ)^(k*(k-1)/2) = 1 :=
    pow_mul_pow_eq_one _ (by norm_num)
  have hh := congrArg (fun x : ℚ => (-1 : ℚ)^(k*(k-1)/2)*x) h
  rw [← mul_assoc, hsq, one_mul] at hh
  calc
    _ = ((-1 : ℚ)^(k*(k-1)/2) * (-1 : ℚ)^((k+m)*(k+m-1)/2) *
      (-1 : ℚ)^(m*(m-1)/2)) *
        Matrix.det (fun i j : Fin m => H ⟨k+i.val, by omega⟩ ⟨j.val, by omega⟩) := by
          convert hh using 1 <;> ring
    _ = _ := by rw [reversal_sign_identity]

private theorem signed_entry (n m i j : ℕ) :
    (if j ≤ m+i then PowerSeries.coeff (m+i-j) (denom (n+m)) else 0) =
      (-1 : ℚ)^(m+i+j) *
        (ascPochhammer ℚ (n+m+1)*Polynomial.X^i).coeff (n+(j+1)) := by
  have hden (r : ℕ) : PowerSeries.coeff r (denom (n+m)) =
      (-1 : ℚ)^r * (ascPochhammer ℚ (n+m+1)).coeff (Polynomial.revAt (n+m+1) r) := by
    rw [← reverse_asc_denom, PowerSeries.coeff_rescale, Polynomial.coeff_coe,
      Polynomial.coeff_reverse, ascPochhammer_natDegree]
  rw [Polynomial.coeff_mul_X_pow']
  by_cases hji : j ≤ m+i
  · rw [if_pos hji, hden]
    by_cases hi : i ≤ n+(j+1)
    · rw [if_pos hi, Polynomial.revAt_le (by omega)]
      have he : n+m+1-(m+i-j) = n+(j+1)-i := by omega
      rw [he]
      congr 1
      conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
      conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
      congr 1
      omega
    · rw [if_neg hi, mul_zero, Polynomial.revAt_eq_self_of_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [ascPochhammer_natDegree]; omega), mul_zero]
  · rw [if_neg hji, if_pos (by omega : i ≤ n+(j+1)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [ascPochhammer_natDegree]; omega), mul_zero]

private theorem elementary_corner (n k m : ℕ) :
    Matrix.det (fun i j : Fin k =>
      (toeplitz (denom (n+m)) (k+m)) ⟨m+i.val, by omega⟩ ⟨j.val, by omega⟩) =
      (-1 : ℚ)^(k*m) * B n k m := by
  let T : Matrix (Fin k) (Fin k) ℚ := fun i j =>
    (ascPochhammer ℚ (n+m+1)*Polynomial.X^i.val).coeff (n+(j.val+1))
  have entries : (fun i j : Fin k =>
      (toeplitz (denom (n+m)) (k+m)) ⟨m+i.val, by omega⟩ ⟨j.val, by omega⟩) =
      (-1 : ℚ)^m • Matrix.of (fun i j => (-1 : ℚ)^i.val *
        Matrix.of (fun i j => (-1 : ℚ)^j.val * T i j) i j) := by
    ext i j
    simpa only [toeplitz, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, T, pow_add, mul_assoc] using signed_entry n m i.val j.val
  rw [entries, Matrix.det_smul, Fintype.card_fin,
    Matrix.det_mul_column, Matrix.det_mul_row]
  have hs : (∏ i : Fin k, (-1 : ℚ)^i.val) * (∏ i : Fin k, (-1 : ℚ)^i.val) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro i _
    rw [← mul_pow]
    norm_num
  have hT : T.det = B n k m := by
    exact (first_minor_coeff n k m).symm
  calc
    _ = ((-1 : ℚ)^m)^k *
        ((∏ i : Fin k, (-1 : ℚ)^i.val) * (∏ i : Fin k, (-1 : ℚ)^i.val)) * T.det := by ring
    _ = _ := by rw [hs, mul_one, hT, ← pow_mul, Nat.mul_comm m k]

private theorem complete_corner (n k m : ℕ) :
    Matrix.det (fun i j : Fin m =>
      (toeplitz ((denom (n+m))⁻¹) (k+m)) ⟨k+i.val, by omega⟩ ⟨j.val, by omega⟩) =
      sourceRHS n k m := by
  have entries : (fun i j : Fin m =>
      (toeplitz ((denom (n+m))⁻¹) (k+m)) ⟨k+i.val, by omega⟩ ⟨j.val, by omega⟩) =
      (Matrix.of (fun i j : Fin m => (Nat.stirlingSecond (n+k+1+i.val+j.val) (n+m) : ℚ))).submatrix id Fin.revPerm := by
    ext i j
    simp only [toeplitz, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
      Fin.revPerm_apply, Fin.val_rev]
    by_cases hji : j.val ≤ k+i.val
    · rw [if_pos hji, complete_coeff]
      congr 2
      have := j.isLt
      omega
    · rw [if_neg hji]
      have hz : Nat.stirlingSecond (n+k+1+i.val+(m-(j.val+1))) (n+m) = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (by have := j.isLt; omega)
      exact_mod_cast hz.symm
  rw [entries, Matrix.det_permute', sign_revQ, source_to_stirling_moment]
  rfl

/-- The literal three-parameter OEIS A396563 identity. -/
theorem result : claim := by
  intro n k m _hm
  let A := (toeplitz (denom (n+m)) (k+m))
  let H := (toeplitz ((denom (n+m))⁻¹) (k+m))
  have hc : PowerSeries.constantCoeff (denom (n+m)) ≠ 0 := by
    rw [denom_constant]
    norm_num
  have hAH : A*H=1 :=
    trunc_inverse _ _ _ (PowerSeries.mul_inv_cancel _ hc)
  have hA : A.det=1 := by
    exact det_toeplitz _ (denom_constant _) _
  have hd := inverse_corner_minor k m A H hAH hA
  change Matrix.det (fun i j : Fin k =>
      (toeplitz (denom (n+m)) (k+m)) ⟨m+i.val, by omega⟩ ⟨j.val, by omega⟩) =
    (-1 : ℚ)^(k*m) * Matrix.det (fun i j : Fin m =>
      (toeplitz ((denom (n+m))⁻¹) (k+m)) ⟨k+i.val, by omega⟩ ⟨j.val, by omega⟩) at hd
  rw [elementary_corner, complete_corner] at hd
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℚ) ≠ 0)) hd

end D5.S3.Combinatorics.BinomialBases.KurkovStirlingMinorVandermondeSum
