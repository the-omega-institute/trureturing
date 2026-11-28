/- GID: D5/S3/Quantum/Fermionic/WuC5CommonGain
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/WuC5CommonGain
   mirror-E: none(waiver:compact-signed-matrix-inequality)
   anchors: []
   utility: none
   digest: The common occupation bias gives the sharp five-cycle rank-one gain. -/

import D5.S3.ConceptDynamics.ObservationOrder.PosteriorMomentDistance
import D5.S3.Quantum.Fermionic.WuC5TransferReflection
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
The common-field spectral bound and its rank-one variational consequence
for signed five-cycle matrices. The normalized gain uses a common real bias `x`,
with field weight `a = x / 2`. The Blueprint relates this matrix result to the
equal-temperature rank-one boundary of Wu, arXiv:2610.33686v1, (3.54).
-/

noncomputable section

open Matrix Polynomial
open scoped BigOperators ComplexOrder Matrix MatrixOrder

namespace D5.S3.Quantum.Fermionic.WuC5CommonGain

open WuC5TransferReflection
open D5.S3.HilbertOperators.WuTransferReflectionBound (transferEval firstCoeff_le_of_reflection)

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "M" => Matrix n n ℂ

@[simp] private lemma star_real (r : ℝ) : star (r : ℂ) = (r : ℂ) :=
  Complex.conj_ofReal r

private lemma sum_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ, add_assoc]

/-- The weighted independent pairs of the five-cycle have total weight at most
one quarter of the squared total site weight. -/
theorem pairWeight_le (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * w (i + 2)) ≤ (∑ i, w i) ^ 2 / 4 := by
  -- Multiplication by two modulo five sends each edge to a step-two pair.
  have h := D5.S3.ConceptDynamics.ObservationOrder.PosteriorMomentDistance.edge_bound
    (fun i ↦ w (2 * i)) (fun i ↦ hw (2 * i))
  change w 0 * w 2 + w 2 * w 4 + w 4 * w 1 + w 1 * w 3 + w 3 * w 0 ≤
    (w 0 + w 2 + w 4 + w 1 + w 3) ^ 2 / 4 at h
  rw [sum_five, sum_five]
  change w 0 * w 2 + w 1 * w 3 + w 2 * w 4 + w 3 * w 0 + w 4 * w 1 ≤
    (w 0 + w 1 + w 2 + w 3 + w 4) ^ 2 / 4
  convert h using 1 <;> ring

private lemma hermitian_noncommProd (f : Fin 5 → M) (hc : ∀ i j, Commute (f i) (f j))
    (hf : ∀ i, (f i).IsHermitian) (s : Finset (Fin 5)) :
    (s.noncommProd f (fun i _ j _ _ ↦ hc i j)).IsHermitian := by
  induction s using Finset.induction_on with
  | empty =>
    change (1 : M).IsHermitian
    exact Matrix.isHermitian_one
  | @insert i s hi ih =>
    have hm : i ∈ insert i s := Finset.mem_insert_self _ _
    rw [← Finset.mul_noncommProd_erase (insert i s) hm f (fun j _ k _ _ ↦ hc j k),
      Finset.erase_insert hi]
    exact ((hf i).commute_iff ih).1
      (Finset.noncommProd_commute s f _ (f i) fun j _ ↦ hc i j)

private lemma transfer_real_hermitian (H : SignedCycle n) (t b : Fin 5 → ℝ)
    (hB : ∀ i, (H.base i).IsHermitian) (hZ : ∀ i, (H.occupation i).IsHermitian) (x : ℝ) :
    (transfer H t b (x : ℂ)).IsHermitian := by
  let B (i : Fin 5) := (t i : ℂ) • H.base i
  let F (i : Fin 5) := (1 : M) + ((b i : ℂ) * (x : ℂ)) • H.occupation i
  have hF (i j : Fin 5) : Commute (F i) (F j) :=
    ((Commute.one_left _).add_right ((Commute.one_left _).smul_right _)).add_left
      (((Commute.one_right _).smul_left _).add_right
        (((H.occupation_comm i j).smul_left _).smul_right _))
  let P (s : Finset (Fin 5)) := s.noncommProd F (fun i _ j _ _ ↦ hF i j)
  let s : Finset (Fin 5) := Finset.univ
  have hBh (i : Fin 5) : (B i).IsHermitian := (hB i).smul (Complex.conj_ofReal _)
  have hFh (i : Fin 5) : (F i).IsHermitian :=
    Matrix.isHermitian_one.add ((hZ i).smul
      (show IsSelfAdjoint ((b i : ℂ) * (x : ℂ)) by
        rw [← Complex.ofReal_mul]; exact Complex.conj_ofReal _))
  have hP (u : Finset (Fin 5)) : (P u).IsHermitian := hermitian_noncommProd F hF hFh u
  have hBP (i : Fin 5) (u : Finset (Fin 5)) (hi : i ∉ u) : Commute (B i) (P u) := by
    refine Finset.noncommProd_commute u F _ (B i) fun j hj ↦ ?_
    exact (Commute.one_right _).add_right
      (((H.other_comm j i (fun e ↦ hi (e ▸ hj))).symm.smul_left _).smul_right _)
  have hsingle (i : Fin 5) : (B i * P (s.erase i)).IsHermitian :=
    ((hBh i).commute_iff (hP _)).1 (hBP i _ (Finset.notMem_erase _ _))
  have hpair (i : Fin 5) : (pairWord B i * P ((s.erase i).erase (i + 2))).IsHermitian := by
    have hc : cycleSign i (i + 2) = 1 := by fin_cases i <;> decide
    have hbase : Commute (H.base i) (H.base (i + 2)) := by
      change H.base i * H.base (i + 2) = H.base (i + 2) * H.base i
      simpa only [hc, one_zsmul] using H.base_sign i (i + 2)
    have hpair := ((hBh i).commute_iff (hBh (i + 2))).1
      ((hbase.smul_left (t i : ℂ)).smul_right (t (i + 2) : ℂ))
    exact (hpair.commute_iff (hP _)).1
      ((hBP i _ (fun hi ↦ Finset.notMem_erase i s (Finset.mem_of_mem_erase hi))).mul_left
        (hBP (i + 2) _ (Finset.notMem_erase _ _)))
  change (P s + ((x : ℂ) • (1 : M)) * (∑ i, B i * P (s.erase i)) +
    ((x : ℂ) • (1 : M)) ^ 2 * (∑ i, pairWord B i * P ((s.erase i).erase (i + 2)))).IsHermitian
  simp only [smul_pow, one_pow, smul_one_mul]
  have hx : IsSelfAdjoint (x : ℂ) := star_real x
  exact ((hP s).add (IsSelfAdjoint.smul hx
    (isSelfAdjoint_sum _ fun i _ ↦ (hsingle i).isSelfAdjoint))).add
      (IsSelfAdjoint.smul (hx.pow 2)
        (isSelfAdjoint_sum _ fun i _ ↦ (hpair i).isSelfAdjoint))

private lemma hermitian_coeff_of_real_eval (A : ℕ → M) (N : ℕ)
    (h : ∀ x : ℝ, (transferEval A N (x : ℂ)).IsHermitian)
    (k : ℕ) (hk : k ∈ Finset.range (N + 1)) : (A k).IsHermitian := by
  change (A k)ᴴ = A k
  apply Matrix.ext
  intro i j
  let p : Polynomial ℂ := ∑ l ∈ Finset.range (N + 1), monomial l (star (A l j i))
  let q : Polynomial ℂ := ∑ l ∈ Finset.range (N + 1), monomial l (A l i j)
  have he (x : ℝ) : p.eval (x : ℂ) = q.eval (x : ℂ) := by
    have hentry := congrArg (fun B : M ↦ B i j) (h x).eq
    simpa only [p, q, transferEval, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      star_sum, star_mul, star_pow, star_real, mul_comm] using hentry
  have hpq : p = q := Polynomial.eq_of_infinite_eval_eq p q
    ((Set.infinite_range_of_injective Complex.ofReal_injective).mono
      (by rintro _ ⟨x, rfl⟩; exact he x))
  have hcoeff := congrArg (fun P : Polynomial ℂ ↦ P.coeff k) hpq
  simpa only [p, q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', hk, if_true, Matrix.conjTranspose_apply]
    using hcoeff

/-- The centered five-cycle Hamiltonian with arbitrary real controls and common
nonnegative occupation weight, bounded in the Loewner order. -/
theorem commonField_le (H : SignedCycle n)
    (hB : ∀ i, (H.base i).IsHermitian) (hZ : ∀ i, (H.occupation i).IsHermitian)
    (t : Fin 5 → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    (∑ i, ((t i : ℂ) • H.base i + (a : ℂ) • H.occupation i)) ≤
      (3 * a + 2 * Real.sqrt (a ^ 2 + (∑ i, t i ^ 2) / 2)) • (1 : M) := by
  let S := ∑ i, t i ^ 2
  let D := ∑ i, t i ^ 2 * t (i + 2) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ sq_nonneg (t i)
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hDS : D ≤ S ^ 2 / 4 := pairWeight_le (fun i ↦ t i ^ 2) fun i ↦ sq_nonneg _
  let δ := Real.sqrt (S ^ 2 - 4 * D)
  have hδ : δ ^ 2 = S ^ 2 - 4 * D := Real.sq_sqrt (by linarith)
  have hδle : δ ≤ S :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hS).mp (by rw [hδ]; linarith)
  let r := (S + δ) / 2
  let s := (S - δ) / 2
  have hr : 0 ≤ r := div_nonneg (add_nonneg hS (Real.sqrt_nonneg _)) (by norm_num)
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr hδle) (by norm_num)
  have hrs : r + s = S := by dsimp only [r, s]; ring
  have hprod : r * s = D := by dsimp only [r, s]; nlinarith only [hδ]
  let u := Real.sqrt (a ^ 2 + r)
  let v := Real.sqrt (a ^ 2 + s)
  let w := Real.sqrt (a ^ 2 + S / 2)
  have hu : u ^ 2 = a ^ 2 + r := Real.sq_sqrt (add_nonneg (sq_nonneg _) hr)
  have hv : v ^ 2 = a ^ 2 + s := Real.sq_sqrt (add_nonneg (sq_nonneg _) hs)
  have hw : w ^ 2 = a ^ 2 + S / 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (div_nonneg hS (by norm_num)))
  have huv : u + v ≤ 2 * w :=
    (sq_le_sq₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
        (by nlinarith only [hu, hv, hw, hrs, sq_nonneg (u - v)])
  let b : Fin 5 → ℝ := ![u, v, a, a, a]
  let A := (transferPolynomial H t (fun _ ↦ a)).coeff
  have hA : ∀ k ∈ Finset.range (5 + 1), (A k).IsHermitian := by
    refine hermitian_coeff_of_real_eval A 5 (fun x ↦ ?_)
    rw [show transferEval A 5 (x : ℂ) = transfer H t (fun _ ↦ a) (x : ℂ) from
      transferEval_eq H t (fun _ ↦ a) _]
    exact transfer_real_hermitian H t (fun _ ↦ a) hB hZ x
  have hb (i : Fin 5) (_ : i ∈ Finset.univ) : 0 ≤ b i := by
    fin_cases i <;> first | exact Real.sqrt_nonneg _ | exact ha
  have hreflect (z : ℂ) : transferEval A 5 z * transferEval A 5 (-z) =
      (∏ i : Fin 5, (1 - (b i : ℂ) ^ 2 * z ^ 2)) • (1 : M) := by
    simp only [A, transferEval_eq, transfer_reflection_common]
    congr 1
    have hu' : (u : ℂ) ^ 2 = (a : ℂ) ^ 2 + (r : ℂ) := by exact_mod_cast hu
    have hv' : (v : ℂ) ^ 2 = (a : ℂ) ^ 2 + (s : ℂ) := by exact_mod_cast hv
    have hrs' : (r : ℂ) + (s : ℂ) = (S : ℂ) := by exact_mod_cast hrs
    have hp' : (r : ℂ) * (s : ℂ) = (D : ℂ) := by exact_mod_cast hprod
    rw [show (∑ i : Fin 5, (t i : ℂ) ^ 2) = (S : ℂ) by simp [S],
      show (∑ i : Fin 5, (t i : ℂ) ^ 2 * (t (i + 2) : ℂ) ^ 2) = (D : ℂ) by simp [D],
      ← hrs', ← hp']
    simp [Fin.prod_univ_succ, b, hu', hv'] <;> ring
  have hfirst := firstCoeff_le_of_reflection (A := A) (N := 5)
    (s := Finset.univ) (a := b) (by decide) hb
    (transfer_constantCoeff H t (fun _ ↦ a)) hA hreflect
  have hsum : (∑ i, b i) = u + v + 3 * a := by
    rw [sum_five]
    change u + v + a + a + a = _
    ring
  calc
    _ = A 1 := (transfer_firstCoeff H t (fun _ ↦ a)).symm
    _ ≤ (∑ i, b i) • (1 : M) := hfirst
    _ ≤ _ := by
      rw [Matrix.le_iff, ← sub_smul]
      exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr (by rw [hsum]; linarith only [huv]))

/-- The complex quadratic form of a matrix in a vector. -/
def expect (v : n → ℂ) (A : M) : ℂ := star v ⬝ᵥ (A *ᵥ v)

/-- The real expectation associated to the quadratic form. -/
def mean (v : n → ℂ) (A : M) : ℝ := (expect v A).re

private lemma expect_add (v : n → ℂ) (A B : M) :
    expect v (A + B) = expect v A + expect v B := by
  simp only [expect, Matrix.add_mulVec, dotProduct_add]

private lemma expect_star (v : n → ℂ) (A : M) :
    expect v (star A) = star (expect v A) := by
  change star v ⬝ᵥ (Aᴴ *ᵥ v) = star (star v ⬝ᵥ (A *ᵥ v))
  rw [Matrix.mulVec_conjTranspose, Matrix.star_dotProduct_star, ← Matrix.dotProduct_mulVec]

private lemma expect_smul (v : n → ℂ) (c : ℂ) (A : M) :
    expect v (c • A) = c * expect v A := by
  simp only [expect, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

private lemma mean_sum {ι : Type*} (v : n → ℂ) (s : Finset ι) (f : ι → M) :
    mean v (∑ i ∈ s, f i) = ∑ i ∈ s, mean v (f i) := by
  simp only [mean, expect, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

private lemma mean_add (v : n → ℂ) (A B : M) :
    mean v (A + B) = mean v A + mean v B := by
  simp only [mean, expect_add, Complex.add_re]

private lemma mean_sub (v : n → ℂ) (A B : M) :
    mean v (A - B) = mean v A - mean v B := by
  simp only [mean, expect, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

private lemma mean_real_smul (v : n → ℂ) (c : ℝ) (A : M) :
    mean v ((c : ℂ) • A) = c * mean v A := by
  simp only [mean, expect_smul, Complex.re_ofReal_mul]

private lemma mean_mono (v : n → ℂ) {A B : M} (h : A ≤ B) : mean v A ≤ mean v B := by
  have hp := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp h).dotProduct_mulVec_nonneg v)).1
  change 0 ≤ mean v (B - A) at hp
  exact sub_nonneg.mp (by simpa only [mean_sub] using hp)

/-- Hole probability observable for an occupation involution. -/
def hole (Z : M) : M := ((1 / 2 : ℝ) : ℂ) • (1 - Z)

/-- The unit-vector gain of Hermitian base observables at common normalized bias
`x`. The optimizing real controls for the vector are half its base means. -/
theorem realGain_le (H : SignedCycle n)
    (hB : ∀ i, (H.base i).IsHermitian) (hZ : ∀ i, (H.occupation i).IsHermitian)
    (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) (x : ℝ) (hx : 0 ≤ x) :
    (∑ i, ((mean v (H.base i) / 2) ^ 2 - x * mean v (hole (H.occupation i)))) ≤
      (1 - x) ^ 2 / 2 := by
  let t (i : Fin 5) := mean v (H.base i) / 2
  let a := x / 2
  let S := ∑ i, t i ^ 2
  let w := Real.sqrt (a ^ 2 + S / 2)
  have hone : mean v (1 : M) = 1 := by simp [mean, expect, hv]
  have hw : w ^ 2 = a ^ 2 + S / 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (div_nonneg
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (t i)) (by norm_num)))
  have hL (i : Fin 5) : t i * mean v (H.base i) = 2 * t i ^ 2 := by
    dsimp [t]
    ring
  have hmean := mean_mono v (commonField_le H hB hZ t a (div_nonneg hx (by norm_num)))
  change mean v (∑ i, ((t i : ℂ) • H.base i + (a : ℂ) • H.occupation i)) ≤
    mean v ((3 * a + 2 * w) • (1 : M)) at hmean
  have hscale : (3 * a + 2 * w) • (1 : M) = ((3 * a + 2 * w : ℝ) : ℂ) • (1 : M) :=
    RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  rw [hscale, mean_real_smul, hone, mul_one] at hmean
  simp only [mean_sum, mean_add, mean_real_smul, hL,
    Finset.sum_add_distrib, ← Finset.mul_sum] at hmean
  have hhole (i : Fin 5) : x * mean v (hole (H.occupation i)) =
      a - a * mean v (H.occupation i) := by
    simp only [hole, mean_real_smul, mean_sub, hone, a]
    ring
  change (∑ i, (t i ^ 2 - x * mean v (hole (H.occupation i)))) ≤ _
  simp only [hhole, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hconst : (∑ _ : Fin 5, a) = 5 * a := by rw [sum_five]; ring
  rw [hconst]
  change S - (5 * a - a * ∑ i, mean v (H.occupation i)) ≤ _
  change 2 * S + a * (∑ i, mean v (H.occupation i)) ≤ 3 * a + 2 * w at hmean
  have hscalar : 2 * w - 2 * a - S ≤ (1 - x) ^ 2 / 2 := by
    have hx' : x = 2 * a := by dsimp [a]; ring
    rw [hx']
    nlinarith only [hw, sq_nonneg (w - 1 / 2)]
  linarith only [hmean, hscalar]

/-- A lowering letter or its adjoint, selected by a Boolean. -/
def letter (J : Fin 5 → M) (i : Fin 5) (adjoint : Bool) : M :=
  if adjoint then star (J i) else J i

/-- The physical on-site ladder relations and all mixed off-site sign relations. -/
structure SignedLadders (n : Type*) [Fintype n] [DecidableEq n] where
  lowering : Fin 5 → Matrix n n ℂ
  nilpotent : ∀ i, lowering i * lowering i = 0
  car : ∀ i, star (lowering i) * lowering i + lowering i * star (lowering i) = 1
  sign : ∀ i j, i ≠ j → ∀ b c,
    letter lowering i b * letter lowering j c =
      cycleSign i j • (letter lowering j c * letter lowering i b)

variable (L : SignedLadders n)

private def phaseBase (u : ℂ) (i : Fin 5) : M :=
  u • L.lowering i + star u • star (L.lowering i)

/-- The centered physical occupation observable, equal to twice the number
projection minus the identity. -/
def occupation (i : Fin 5) : M :=
  star (L.lowering i) * L.lowering i - L.lowering i * star (L.lowering i)

private lemma phaseBase_hermitian (u : ℂ) (i : Fin 5) : (phaseBase L u i).IsHermitian := by
  change star (phaseBase L u i) = _
  simp only [phaseBase, star_add, star_smul, star_star, add_comm]

private lemma occupation_hermitian (i : Fin 5) : (occupation L i).IsHermitian := by
  change star (occupation L i) = _
  simp only [occupation, star_sub, star_mul, star_star]

private lemma ladderLocal (u : ℂ) (hu : u * star u = 1) (i : Fin 5) :
    phaseBase L u i ^ 2 = 1 ∧ occupation L i ^ 2 = 1 ∧
    occupation L i * phaseBase L u i = -(phaseBase L u i * occupation L i) := by
  let J := L.lowering i
  let K := star J
  let P := K * J
  let Q := J * K
  have hJ : J * J = 0 := L.nilpotent i
  have hK : K * K = 0 := by
    simpa only [K, star_mul, star_zero] using congrArg star hJ
  have hsum : P + Q = 1 := L.car i
  have hPQ : P * Q = 0 := by
    calc
      _ = K * (J * J) * K := by dsimp [P, Q]; noncomm_ring
      _ = _ := by simp [hJ]
  have hQP : Q * P = 0 := by
    calc
      _ = J * (K * K) * J := by dsimp [P, Q]; noncomm_ring
      _ = _ := by simp [hK]
  have hPJ : P * J = 0 := by simp only [P, mul_assoc, hJ, mul_zero]
  have hJQ : J * Q = 0 := by simp only [Q, ← mul_assoc, hJ, zero_mul]
  have hQK : Q * K = 0 := by simp only [Q, mul_assoc, hK, mul_zero]
  have hKP : K * P = 0 := by simp only [P, ← mul_assoc, hK, zero_mul]
  have hQJ : Q * J = J := by
    simpa only [add_mul, hPJ, zero_add, one_mul] using congrArg (· * J) hsum
  have hJP : J * P = J := by
    simpa only [mul_add, hJQ, add_zero, mul_one] using congrArg (J * ·) hsum
  have hPK : P * K = K := by
    simpa only [add_mul, hQK, add_zero, one_mul] using congrArg (· * K) hsum
  have hKQ : K * Q = K := by
    simpa only [mul_add, hKP, zero_add, mul_one] using congrArg (K * ·) hsum
  have hu' : star u * u = 1 := by rw [mul_comm, hu]
  change (u • J + star u • K) ^ 2 = 1 ∧ (P - Q) ^ 2 = 1 ∧
    (P - Q) * (u • J + star u • K) = -((u • J + star u • K) * (P - Q))
  refine ⟨?_, ?_, ?_⟩
  · simp only [pow_two, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hJ, hK, smul_zero, zero_add, add_zero, hu, hu', one_smul]
    exact hsum
  · calc
      _ = (P + Q) ^ 2 := by
        simp only [pow_two, mul_sub, sub_mul, add_mul, mul_add,
          hPQ, hQP, sub_zero, add_zero, zero_add, zero_sub, sub_neg_eq_add]
      _ = _ := by simp [hsum]
  · simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      hPJ, hJQ, hQK, hKP, hQJ, hJP, hPK, hKQ, smul_zero,
      add_zero, zero_add, sub_zero, zero_sub, smul_neg]
    rw [neg_sub, sub_eq_add_neg, add_comm]

private lemma occupation_comm_letter {i j : Fin 5} (hij : i ≠ j) (d : Bool) :
    Commute (occupation L i) (letter L.lowering j d) := by
  have hsign : cycleSign i j * cycleSign i j = 1 := by
    unfold cycleSign
    split <;> norm_num
  have hc (b c : Bool) :
      Commute (letter L.lowering i b * letter L.lowering i c) (letter L.lowering j d) := by
    let U := letter L.lowering i b
    let V := letter L.lowering i c
    let W := letter L.lowering j d
    change (U * V) * W = W * (U * V)
    have hU : U * W = cycleSign i j • (W * U) := L.sign i j hij b d
    have hV : V * W = cycleSign i j • (W * V) := L.sign i j hij c d
    rw [mul_assoc, hV, mul_smul_comm, ← mul_assoc U W, hU, smul_mul_assoc,
      smul_smul, hsign, one_zsmul, mul_assoc]
  exact (hc true false).sub_left (hc false true)

/-- Unit phases on the individual lowering operators give the same signed cycle. -/
def phaseCycle (u : Fin 5 → ℂ) (hu : ∀ i, u i * star (u i) = 1) : SignedCycle n where
  base i := phaseBase L (u i) i
  occupation := occupation L
  base_sq i := (ladderLocal L (u i) (hu i) i).1
  occupation_sq i := (ladderLocal L (u i) (hu i) i).2.1
  own_sign i := (ladderLocal L (u i) (hu i) i).2.2
  occupation_comm i j := by
    by_cases hij : i = j
    · subst j
      exact Commute.refl _
    · exact ((occupation_comm_letter L hij true).mul_right
        (occupation_comm_letter L hij false)).sub_right
        ((occupation_comm_letter L hij false).mul_right (occupation_comm_letter L hij true))
  other_comm i j hij :=
    ((occupation_comm_letter L hij false).smul_right (u j)).add_right
      ((occupation_comm_letter L hij true).smul_right (star (u j)))
  base_sign i j := by
    by_cases hij : i = j
    · subst j
      have h : cycleSign i i = 1 := by fin_cases i <;> decide
      rw [h, one_zsmul]
    let c (k : Fin 5) (b : Bool) := if b then star (u k) else u k
    let V (k : Fin 5) (b : Bool) := c k b • letter L.lowering k b
    have hs (b d : Bool) : V i b * V j d = cycleSign i j • (V j d * V i b) := by
      simp only [V, smul_mul_assoc, mul_smul_comm, smul_smul, L.sign i j hij b d]
      rw [mul_comm (c j d) (c i b), smul_comm (c i b * c j d)]
    change (V i false + V i true) * (V j false + V j true) =
      cycleSign i j • ((V j false + V j true) * (V i false + V i true))
    simp only [add_mul, mul_add, hs false false, hs false true, hs true false, hs true true,
      smul_add] <;> abel

private lemma hole_occupation (i : Fin 5) :
    hole (occupation L i) = L.lowering i * star (L.lowering i) := by
  have h : (1 : M) - occupation L i =
      (2 : ℂ) • (L.lowering i * star (L.lowering i)) := by
    unfold occupation
    rw [← L.car i]
    module
  have hhalf : (((1 / 2 : ℝ) : ℂ) * 2) = 1 := by norm_num [Complex.ofReal_div]
  rw [hole, h, smul_smul, hhalf, one_smul]

private lemma unit_factor (z : ℂ) : ∃ u : ℂ, u * star u = 1 ∧ (‖z‖ : ℂ) * u = z := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, by simp, by simp⟩
  have hr : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_eq_zero.not.mpr (norm_ne_zero_iff.mpr hz)
  let u := z / (‖z‖ : ℂ)
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hz)]
  refine ⟨u, ?_, ?_⟩
  · simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu,
      one_pow, Complex.ofReal_one]
  · exact (mul_comm _ _).trans (div_mul_cancel₀ z hr)

/-- The common-field Loewner bound for arbitrary complex ladder controls. -/
theorem ladderField_le (c : Fin 5 → ℂ) (a : ℝ) (ha : 0 ≤ a) :
    (∑ i, (c i • L.lowering i + star (c i) • star (L.lowering i) +
      (a : ℂ) • occupation L i)) ≤
      (3 * a + 2 * Real.sqrt (a ^ 2 + (∑ i, ‖c i‖ ^ 2) / 2)) • (1 : M) := by
  choose u hu hc using fun i ↦ unit_factor (c i)
  have hbase (i : Fin 5) :
      (‖c i‖ : ℂ) • phaseBase L (u i) i =
        c i • L.lowering i + star (c i) • star (L.lowering i) := by
    have hconj : (‖c i‖ : ℂ) * star (u i) = star (c i) := by
      simpa only [star_mul, star_real, mul_comm] using congrArg star (hc i)
    rw [phaseBase, smul_add, smul_smul, smul_smul, hc i, hconj]
  have h := commonField_le (phaseCycle L u hu) (fun i ↦ phaseBase_hermitian L (u i) i)
    (occupation_hermitian L) (fun i ↦ ‖c i‖) a ha
  change (∑ i, ((‖c i‖ : ℂ) • phaseBase L (u i) i + (a : ℂ) • occupation L i)) ≤ _ at h
  simpa only [hbase] using h

/-- The normalized rank-one ladder gain, with the actual hole projections. -/
def gain (v : n → ℂ) (x : ℝ) : ℝ :=
  ∑ i, (Complex.normSq (expect v (L.lowering i)) -
    x * mean v (L.lowering i * star (L.lowering i)))

/-- The sharp common-bias upper bound holds in every signed ladder representation. -/
theorem gain_le (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) (x : ℝ) (hx : 0 ≤ x) :
    gain L v x ≤ (1 - x) ^ 2 / 2 := by
  let z (i : Fin 5) := expect v (L.lowering i)
  choose u hu hc using fun i ↦ unit_factor (star (z i))
  have hnorm (i : Fin 5) : (‖z i‖ : ℂ) * u i = star (z i) := by
    simpa only [norm_star] using hc i
  have hz (i : Fin 5) : u i * z i = (‖z i‖ : ℂ) := by
    by_cases hz : z i = 0
    · simp [hz]
    have hn : (‖z i‖ : ℂ) ≠ 0 := Complex.ofReal_eq_zero.not.mpr (norm_ne_zero_iff.mpr hz)
    apply mul_left_cancel₀ hn
    rw [← mul_assoc, hnorm, ← pow_two]
    simpa only [Complex.normSq_eq_norm_sq, Complex.ofReal_pow, Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := z i)).symm
  have hmean (i : Fin 5) : mean v (phaseBase L (u i) i) / 2 = ‖z i‖ := by
    have he : expect v (phaseBase L (u i) i) = u i * z i + star (u i * z i) := by
      simp only [phaseBase, expect_add, expect_smul, expect_star, z, star_mul, mul_comm]
    simp only [mean, he, hz, star_real, Complex.add_re, Complex.ofReal_re]
    ring
  have h := realGain_le (phaseCycle L u hu) (fun i ↦ phaseBase_hermitian L (u i) i)
    (occupation_hermitian L) v hv x hx
  change (∑ i, ((mean v (phaseBase L (u i) i) / 2) ^ 2 -
    x * mean v (hole (occupation L i)))) ≤ _ at h
  simpa only [gain, hmean, hole_occupation, Complex.normSq_eq_norm_sq, z] using h

section Spin

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- The 32 occupation configurations of five sites. A true bit is occupied. -/
abbrev SpinBits := Fin 5 → Bool

local notation "SpinMat" => Matrix SpinBits SpinBits ℂ

private def flip (i : Fin 5) (s : SpinBits) : SpinBits := Function.update s i (!(s i))

@[simp] private lemma flip_same (i : Fin 5) (s : SpinBits) : flip i s i = !(s i) := by
  simp [flip]

private lemma flip_other {i j : Fin 5} (h : j ≠ i) (s : SpinBits) : flip i s j = s j := by
  simp [flip, Function.update_of_ne h]

@[simp] private lemma flip_twice (i : Fin 5) (s : SpinBits) : flip i (flip i s) = s := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · rw [flip_other h, flip_other h]

private lemma flips_commute (i j : Fin 5) (s : SpinBits) : flip j (flip i s) = flip i (flip j s) := by
  by_cases hij : i = j
  · subst j
    rfl
  funext k
  by_cases hi : k = i
  · subst k
    simp only [flip_same, flip_other hij]
  by_cases hj : k = j
  · subst k
    simp only [flip_same, flip_other (Ne.symm hij)]
  simp only [flip_other hi, flip_other hj]

private def bitSign (b : Bool) : ℂ := if b then 1 else -1

@[simp] private lemma bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> simp [bitSign]

@[simp] private lemma bitSign_star (b : Bool) : star (bitSign b) = bitSign b := by
  cases b <;> simp [bitSign]

@[simp] private lemma bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

-- The ordered strings use precisely the earlier neighbors in the cycle.
private def spinSign (i : Fin 5) (s : SpinBits) : ℂ :=
  ![1, bitSign (s 0), bitSign (s 1), bitSign (s 2), bitSign (s 0) * bitSign (s 3)] i

@[simp] private lemma spinSign_star (i : Fin 5) (s : SpinBits) :
    star (spinSign i s) = spinSign i s := by
  fin_cases i <;> simp [spinSign, star_mul', bitSign_star, mul_comm]

@[simp] private lemma spinSign_sq (i : Fin 5) (s : SpinBits) : spinSign i s ^ 2 = 1 := by
  fin_cases i <;> simp [spinSign, mul_pow, bitSign_sq]

@[simp] private lemma spinSign_own_flip (i : Fin 5) (s : SpinBits) :
    spinSign i (flip i s) = spinSign i s := by
  fin_cases i <;> simp [spinSign, flip, Function.update_apply, Fin.ext_iff]

private lemma spinSign_swap (i j : Fin 5) (s : SpinBits) :
    spinSign i s * spinSign j (flip i s) =
      (cycleSign i j : ℂ) * (spinSign j s * spinSign i (flip j s)) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [spinSign, cycleSign, flip, Function.update_apply, Fin.ext_iff,
      Fin.add_def, Fin.reduceFinMk] <;> ring

private def spinWeight (i : Fin 5) (b : Bool) (s : SpinBits) : ℂ :=
  if s i = b then spinSign i s else 0

private def weightedFlip (i : Fin 5) (f : SpinBits → ℂ) : SpinMat :=
  Matrix.of fun s t ↦ if t = flip i s then f s else 0

private lemma weightedFlip_mul (i j : Fin 5) (f g : SpinBits → ℂ) (s t : SpinBits) :
    (weightedFlip i f * weightedFlip j g) s t =
      if t = flip j (flip i s) then f s * g (flip i s) else 0 := by
  simp only [Matrix.mul_apply, weightedFlip, Matrix.of_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_ite, mul_zero]

private lemma weightedFlip_mulVec (i : Fin 5) (f v : SpinBits → ℂ) (s : SpinBits) :
    (weightedFlip i f *ᵥ v) s = f s * v (flip i s) := by
  simp [Matrix.mulVec, dotProduct, weightedFlip, ite_mul]

private def spinLetter (i : Fin 5) (b : Bool) : SpinMat := weightedFlip i (spinWeight i b)

private lemma spinLetter_star (i : Fin 5) : star (spinLetter i false) = spinLetter i true := by
  apply Matrix.ext
  intro s t
  have hflip : s = flip i t ↔ t = flip i s := by
    constructor <;> intro h <;> rw [h, flip_twice]
  simp only [Matrix.star_apply, spinLetter, weightedFlip, Matrix.of_apply, hflip]
  split_ifs with h
  · subst t
    cases hs : s i <;> simp [spinWeight, hs]
  · simp

private lemma spinLetter_own_mul (i : Fin 5) (b c : Bool) (s t : SpinBits) :
    (spinLetter i b * spinLetter i c) s t =
      if t = s ∧ s i = b ∧ c = !b then 1 else 0 := by
  simp only [spinLetter, weightedFlip_mul, flip_twice]
  have hsq : spinSign i s * spinSign i s = 1 := by
    simpa only [pow_two] using spinSign_sq i s
  cases h : s i <;> cases b <;> cases c <;> simp [spinWeight, h, hsq]

private lemma spinLetter_interchange {i j : Fin 5} (hij : i ≠ j) (b c : Bool) :
    spinLetter i b * spinLetter j c =
      cycleSign i j • (spinLetter j c * spinLetter i b) := by
  apply Matrix.ext
  intro s t
  rw [← Int.cast_smul_eq_zsmul ℂ, Matrix.smul_apply, smul_eq_mul]
  simp only [spinLetter, weightedFlip_mul, flips_commute i j s, spinWeight,
    flip_other hij, flip_other hij.symm]
  split_ifs <;> simp_all [spinSign_swap i j s]

/-- The ordered signed-spin lowering matrices on the five occupation bits. -/
def spinLadders : SignedLadders SpinBits where
  lowering i := spinLetter i false
  nilpotent i := by
    apply Matrix.ext
    intro s t
    simp [spinLetter_own_mul]
  car i := by
    rw [spinLetter_star]
    apply Matrix.ext
    intro s t
    cases h : s i <;> simp [Matrix.add_apply, spinLetter_own_mul, Matrix.one_apply, eq_comm, h]
  sign i j hij b c := by
    have h (k : Fin 5) (d : Bool) :
        letter (fun l ↦ spinLetter l false) k d = spinLetter k d := by
      cases d <;> simp [letter, spinLetter_star]
    change letter (fun l ↦ spinLetter l false) i b * letter (fun l ↦ spinLetter l false) j c =
      cycleSign i j • (letter (fun l ↦ spinLetter l false) j c *
        letter (fun l ↦ spinLetter l false) i b)
    simp only [h]
    exact spinLetter_interchange hij b c

private lemma spin_hole_mulVec (i : Fin 5) (v : SpinBits → ℂ) (s : SpinBits) :
    ((spinLadders.lowering i * star (spinLadders.lowering i)) *ᵥ v) s =
      if s i = false then v s else 0 := by
  change ((spinLetter i false * star (spinLetter i false)) *ᵥ v) s = _
  rw [spinLetter_star, Matrix.mulVec, dotProduct]
  simp only [spinLetter_own_mul, Bool.not_false, and_true, ite_mul, zero_mul, one_mul]
  by_cases h : s i = false
  · simp [h]
  · simp [h]

private def bitCoordinates :
    (Bool × Bool × Bool × Bool × Bool) ≃ SpinBits where
  toFun s := ![s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2]
  invFun s := (s 0, s 1, s 2, s 3, s 4)
  left_inv := by rintro ⟨a, b, c, d, e⟩; rfl
  right_inv s := by funext i; fin_cases i <;> rfl

private lemma sum_spin (f : SpinBits → ℂ) :
    (∑ s, f s) =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, ∑ e : Bool,
        f (![a, b, c, d, e] : SpinBits) := by
  simpa only [Fintype.sum_prod_type, bitCoordinates, Equiv.coe_fn_mk] using
    (Equiv.sum_comp bitCoordinates f).symm

-- Sites 0 and 2 carry the two superpositions. The other bits are filled.
private def spinState (p q : ℝ) (s : SpinBits) : ℂ :=
  if s 1 = true ∧ s 3 = true ∧ s 4 = true then
    (if s 0 then (p : ℂ) else q) * (if s 2 then (p : ℂ) else q)
  else 0

private lemma spinState_norm (p q : ℝ) :
    star (spinState p q) ⬝ᵥ spinState p q = (((p ^ 2 + q ^ 2) ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Pi.star_apply, sum_spin, Fintype.sum_bool, spinState,
    star_mul', star_real] <;> push_cast <;> ring

private lemma spinState_lowering (p q : ℝ) (i : Fin 5) :
    expect (spinState p q) (spinLadders.lowering i) =
      if i = 0 ∨ i = 2 then ((p * q * (p ^ 2 + q ^ 2) : ℝ) : ℂ) else 0 := by
  change expect (spinState p q) (weightedFlip i (spinWeight i false)) = _
  fin_cases i <;>
    simp [expect, dotProduct, Pi.star_apply, weightedFlip_mulVec, sum_spin, Fintype.sum_bool,
      spinState, spinWeight, spinSign, bitSign, flip, Function.update_apply, Fin.ext_iff,
      star_mul', star_real] <;> push_cast <;> ring

private lemma spinState_hole (p q : ℝ) (i : Fin 5) :
    expect (spinState p q) (spinLadders.lowering i * star (spinLadders.lowering i)) =
      if i = 0 ∨ i = 2 then ((q ^ 2 * (p ^ 2 + q ^ 2) : ℝ) : ℂ) else 0 := by
  fin_cases i <;>
    simp [expect, dotProduct, Pi.star_apply, spin_hole_mulVec, sum_spin, Fintype.sum_bool,
      spinState, Fin.ext_iff, star_mul', star_real] <;> push_cast <;> ring

/-- A physical five-mode unit vector attains the upper bound for every bias in
the common-bias range. -/
theorem spin_attains (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    ∃ v : SpinBits → ℂ, star v ⬝ᵥ v = 1 ∧ gain spinLadders v x = (1 - x) ^ 2 / 2 := by
  let p := Real.sqrt ((1 + x) / 2)
  let q := Real.sqrt ((1 - x) / 2)
  have hp : p ^ 2 = (1 + x) / 2 :=
    Real.sq_sqrt (div_nonneg (add_nonneg zero_le_one hx) (by norm_num))
  have hq : q ^ 2 = (1 - x) / 2 :=
    Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hx') (by norm_num))
  have hunit : p ^ 2 + q ^ 2 = 1 := by linarith only [hp, hq]
  refine ⟨spinState p q, by rw [spinState_norm, hunit]; simp, ?_⟩
  have hsite (i : Fin 5) :
      Complex.normSq (expect (spinState p q) (spinLadders.lowering i)) -
        x * mean (spinState p q) (spinLadders.lowering i * star (spinLadders.lowering i)) =
        if i = 0 ∨ i = 2 then (p * q) * (p * q) - x * q ^ 2 else 0 := by
    by_cases hi : i = 0 ∨ i = 2
    · simp only [mean, spinState_lowering, spinState_hole, if_pos hi, hunit, mul_one,
        Complex.normSq_ofReal, Complex.ofReal_re]
    · simp [mean, spinState_lowering, spinState_hole, hi]
  unfold gain
  simp_rw [hsite]
  rw [sum_five]
  norm_num [Fin.ext_iff]
  calc
    _ = 2 * (p ^ 2 * q ^ 2 - x * q ^ 2) := by ring
    _ = _ := by rw [hp, hq]; ring

end Spin

end D5.S3.Quantum.Fermionic.WuC5CommonGain
