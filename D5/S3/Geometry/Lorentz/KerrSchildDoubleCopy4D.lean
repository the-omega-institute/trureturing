/- GID: D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Kerr–Schild curvature on null geodesic two-jets and algebraic double copy. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.WeylNullScreen
import D5.S3.Algebra.ProjectivePolynomial
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.LinearCombination

/-! Exact curvature and stationary single copies of a Cartesian Kerr–Schild metric. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Lorentz.KerrSchildDoubleCopy4D

open Matrix
private abbrev Idx := Fin 4
private abbrev Covector (K : Type*) := Idx → K
private abbrev Matrix4 (K : Type*) := Matrix Idx Idx K

def sign (K : Type*) [Ring K] : Covector K := ![-1, 1, 1, 1]

/-- The Cartesian Minkowski metric with time index zero. -/
def eta (K : Type*) [Ring K] : Matrix4 K := diagonal (sign K)

/-- Raising a covector index with the background metric. -/
def raise {K : Type*} [Ring K] (k : Covector K) : Covector K := fun i => sign K i * k i

def ksMetric {K : Type*} [CommRing K] (φ : K) (k : Covector K) : Matrix4 K :=
  eta K + φ • vecMulVec k k

def ksInv {K : Type*} [CommRing K] (φ : K) (k : Covector K) : Matrix4 K :=
  eta K - φ • vecMulVec (raise k) (raise k)

private theorem sign_sq {K : Type*} [Ring K] (i : Idx) : sign K i * sign K i = 1 := by
  fin_cases i <;> simp [sign]

private theorem eta_sq {K : Type*} [CommRing K] : eta K * eta K = 1 := by
  rw [eta, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  exact funext sign_sq

private theorem eta_det {K : Type*} [CommRing K] : (eta K).det = -1 := by
  simp [eta, det_diagonal, Fin.prod_univ_succ, sign]

private theorem eta_raise {K : Type*} [CommRing K] (k : Covector K) :
    eta K *ᵥ raise k = k := by
  ext i
  simp [eta, raise, mulVec_diagonal, ← mul_assoc, sign_sq]

theorem ks_metric_symm {K : Type*} [CommRing K] (φ : K) (k : Covector K) :
    (ksMetric φ k)ᵀ = ksMetric φ k := by
  rw [ksMetric, transpose_add, show (eta K)ᵀ = eta K from diagonal_transpose _]
  congr 1
  ext i j
  simp [vecMulVec_apply, mul_comm (k j) (k i)]

theorem ks_metric_mul_inv {K : Type*} [CommRing K] (φ : K) (k : Covector K)
    (hn : raise k ⬝ᵥ k = 0) :
    ksMetric φ k * ksInv φ k = 1 ∧ ksInv φ k * ksMetric φ k = 1 := by
  have hleft : eta K * vecMulVec (raise k) (raise k) = vecMulVec k (raise k) := by
    rw [mul_vecMulVec, eta_raise]
  have hright : vecMulVec k k * eta K = vecMulVec k (raise k) := by
    rw [vecMulVec_mul]
    congr 1
    ext i
    rw [← mulVec_transpose, eta, diagonal_transpose, mulVec_diagonal]
    rfl
  have hzero : vecMulVec k k * vecMulVec (raise k) (raise k) = 0 := by
    rw [vecMulVec_mul_vecMulVec, dotProduct_comm k, hn, zero_smul]
    ext i j
    simp [vecMulVec_apply]
  have h : ksMetric φ k * ksInv φ k = 1 := by
    simp [ksMetric, ksInv, Matrix.mul_sub, Matrix.add_mul, eta_sq, hleft, hright, hzero]
  refine ⟨h, ?_⟩
  have hi : (ksInv φ k)ᵀ = ksInv φ k := by
    rw [ksInv, transpose_sub, show (eta K)ᵀ = eta K from diagonal_transpose _]
    congr 1
    ext i j
    simp [vecMulVec_apply, mul_comm (raise k j) (raise k i)]
  simpa only [transpose_mul, ks_metric_symm, hi, transpose_one] using congrArg transpose h

/-- The determinant formula includes non-null covectors and singular perturbations. -/
theorem ks_metric_det_formula {K : Type*} [CommRing K] (φ : K) (k : Covector K) :
    (ksMetric φ k).det = -(1 + φ * (raise k ⬝ᵥ k)) := by
  have hf : ksMetric φ k = eta K * (1 + φ • vecMulVec (raise k) k) := by
    simp [ksMetric, Matrix.mul_add, mul_vecMulVec, eta_raise]
  have hr : φ • vecMulVec (raise k) k =
      replicateCol Unit (φ • raise k) * replicateRow Unit k := by
    ext i j
    simp [Matrix.mul_apply, vecMulVec_apply, smul_eq_mul, mul_assoc]
  rw [hf, det_mul, hr, det_one_add_replicateCol_mul_replicateRow, eta_det,
    dotProduct_smul, dotProduct_comm k]
  simp

theorem ks_metric_det {K : Type*} [CommRing K] (φ : K) (k : Covector K)
    (hn : raise k ⬝ᵥ k = 0) : (ksMetric φ k).det = -1 := by
  rw [ks_metric_det_formula, hn, mul_zero, add_zero]

/-- Pointwise values and first derivatives of the scalar and lower null covector. -/
structure FirstJet (K : Type*) where
  phi : K
  k : Covector K
  dphi : Covector K
  dk : Matrix4 K

/-- Symmetric second derivatives in flat Cartesian coordinates. -/
structure Jet (K : Type*) extends FirstJet K where
  ddphi : Matrix4 K
  ddk : Idx → Matrix4 K
  ddphi_symm : ∀ a b, ddphi a b = ddphi b a
  ddk_symm : ∀ a b i, ddk a b i = ddk b a i

private def dual {K : Type*} (a b : K) : TrivSqZeroExt K K := (a, b)

@[simp] private theorem dual_fst {K : Type*} (a b : K) : (dual a b).fst = a := rfl
@[simp] private theorem dual_snd {K : Type*} (a b : K) : (dual a b).snd = b := rfl

section Ring
variable {K : Type*} [CommRing K]

/-- Nullity and both differentiated nullity equations. -/
structure Null (j : Jet K) : Prop where
  value : raise j.k ⬝ᵥ j.k = 0
  first : ∀ a, raise j.k ⬝ᵥ j.dk a = 0
  second : ∀ a b, raise j.k ⬝ᵥ j.ddk a b + raise (j.dk a) ⬝ᵥ j.dk b = 0

/-- Affinely parametrized geodesic flow and its derivative. -/
structure Geodesic (j : Jet K) : Prop where
  value : ∀ b, (∑ a, raise j.k a * j.dk a b) = 0
  first : ∀ c b, (∑ a, (raise (j.dk c) a * j.dk a b +
    raise j.k a * j.ddk c a b)) = 0

/-- The first derivative of the metric perturbation. -/
def dPerturbation (j : FirstJet K) (a i b : Idx) : K :=
  j.dphi a * j.k i * j.k b + j.phi * (j.dk a i * j.k b + j.k i * j.dk a b)

/-- The second derivative of the metric perturbation. -/
def ddPerturbation (j : Jet K) (a c i b : Idx) : K :=
  j.ddphi a c * j.k i * j.k b +
    j.dphi c * (j.dk a i * j.k b + j.k i * j.dk a b) +
    j.dphi a * (j.dk c i * j.k b + j.k i * j.dk c b) +
    j.phi * (j.ddk a c i * j.k b + j.dk c i * j.dk a b +
      j.dk a i * j.dk c b + j.k i * j.ddk a c b)

private def lowerConnection (j : FirstJet K) (a i b : Idx) : K :=
  dPerturbation j i a b + dPerturbation j b a i - dPerturbation j a i b

private def flatConnection (j : FirstJet K) (a i b : Idx) : K :=
  sign K a * lowerConnection j a i b

private def flatDerivative (j : Jet K) (c a i b : Idx) : K :=
  sign K a * (ddPerturbation j c i a b + ddPerturbation j c b a i -
    ddPerturbation j c a i b)

private def connection (j : FirstJet K) (a i b : Idx) : K :=
  ∑ r, ksInv j.phi j.k a r * lowerConnection j r i b

private theorem dual_mul_snd (x y : TrivSqZeroExt K K) :
    (x * y).snd = x.fst * y.snd + x.snd * y.fst := rfl

private def tangent (j : Jet K) (c : Idx) : FirstJet (TrivSqZeroExt K K) where
  phi := dual j.phi (j.dphi c)
  k i := dual (j.k i) (j.dk c i)
  dphi i := dual (j.dphi i) (j.ddphi c i)
  dk i b := dual (j.dk i b) (j.ddk c i b)

private def connectionDerivative (j : Jet K) (c a i b : Idx) : K :=
  (connection (tangent j c) a i b).snd

private def along (j : FirstJet K) : K := raise j.k ⬝ᵥ j.dphi

private def correction (j : FirstJet K) (a i b : Idx) : K :=
  j.phi * along j * raise j.k a * j.k i * j.k b

private theorem sum_inv (φ : K) (k f : Covector K) (i : Idx) :
    (∑ r, ksInv φ k i r * f r) = sign K i * f i - φ * raise k i * (raise k ⬝ᵥ f) := by
  simp only [ksInv, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    sub_mul, Finset.sum_sub_distrib]
  change eta K i ⬝ᵥ f - _ = _
  rw [eta, diagonal_dotProduct]
  congr 1
  rw [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

private theorem flat_trace (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0) (i : Idx) :
    (∑ a, flatConnection j a a i) = 0 := by
  have hd' := hd i
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] at hn hd'
  simp only [flatConnection, lowerConnection, dPerturbation, raise, Fin.sum_univ_succ, Fin.sum_univ_zero] at *
  linear_combination j.dphi i * hn + (2 * j.phi) * hd'

private theorem lower_contract (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0)
    (hg : ∀ b, (∑ a, raise j.k a * j.dk a b) = 0) (i b : Idx) :
    raise j.k ⬝ᵥ (fun r => lowerConnection j r i b) = -along j * j.k i * j.k b := by
  have hi := hd i
  have hb := hd b
  have hgi := hg i
  have hgb := hg b
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, raise] at hn hi hb hgi hgb
  simp only [lowerConnection, along, dPerturbation, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, raise]
  linear_combination (j.dphi i * j.k b + j.dphi b * j.k i +
    j.phi * (j.dk i b + j.dk b i)) * hn +
    j.phi * j.k b * hi + j.phi * j.k i * hb -
    j.phi * j.k b * hgi - j.phi * j.k i * hgb

private theorem connection_split (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0)
    (hg : ∀ b, (∑ a, raise j.k a * j.dk a b) = 0) (a i b : Idx) :
    connection j a i b = flatConnection j a i b + correction j a i b := by
  rw [connection, sum_inv, lower_contract j hn hd hg, flatConnection, correction]
  ring

private theorem connection_trace (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0) (i : Idx) :
    (∑ a, connection j a a i) = 0 := by
  have h : (∑ a, j.phi * raise j.k a * (raise j.k ⬝ᵥ fun r => lowerConnection j r a i)) = 0 := by
    calc
      _ = j.phi * (raise j.k ⬝ᵥ j.k) *
          (j.dphi i * (raise j.k ⬝ᵥ j.k) + 2 * j.phi * (raise j.k ⬝ᵥ j.dk i)) := by
        simp only [dotProduct, lowerConnection, dPerturbation,
          Fin.sum_univ_succ, Fin.sum_univ_zero]
        ring
      _ = 0 := by rw [hn, mul_zero, zero_mul]
  simp only [connection, sum_inv, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr ((flat_trace j hn hd i).trans h.symm)

private theorem sign_tangent (i : Idx) :
    sign (TrivSqZeroExt K K) i = dual (sign K i) 0 := by
  fin_cases i <;> apply TrivSqZeroExt.ext <;> simp [sign]

private theorem tangent_null (j : Jet K) (hn : Null j) (c : Idx) :
    raise (tangent j c).k ⬝ᵥ (tangent j c).k = 0 := by
  apply TrivSqZeroExt.ext
  · simpa [dotProduct, raise, tangent, sign_tangent, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul] using hn.value
  · have h := hn.first c
    simp only [dotProduct, raise, Fin.sum_univ_succ, Fin.sum_univ_zero] at h
    simp only [dotProduct, raise, tangent, sign_tangent, TrivSqZeroExt.snd_add,
      dual_mul_snd, TrivSqZeroExt.fst_mul, dual_fst, dual_snd, zero_mul, add_zero,
      TrivSqZeroExt.snd_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
    linear_combination 2 * h

private theorem tangent_dnull (j : Jet K) (hn : Null j) (c a : Idx) :
    raise (tangent j c).k ⬝ᵥ (tangent j c).dk a = 0 := by
  apply TrivSqZeroExt.ext
  · simpa [dotProduct, raise, tangent, sign_tangent, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul] using hn.first a
  · have h := hn.second c a
    simp only [dotProduct, raise, Fin.sum_univ_succ, Fin.sum_univ_zero] at h
    simp only [dotProduct, raise, tangent, sign_tangent, TrivSqZeroExt.snd_add,
      dual_mul_snd, TrivSqZeroExt.fst_mul, dual_fst, dual_snd, zero_mul, add_zero,
      TrivSqZeroExt.snd_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
    linear_combination h

private theorem tangent_geodesic (j : Jet K) (hg : Geodesic j) (c b : Idx) :
    (∑ a, raise (tangent j c).k a * (tangent j c).dk a b) = 0 := by
  apply TrivSqZeroExt.ext
  · simpa [raise, tangent, sign_tangent, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul] using hg.value b
  · have h := hg.first c b
    simp only [raise, Fin.sum_univ_succ, Fin.sum_univ_zero] at h
    simp only [raise, tangent, sign_tangent, TrivSqZeroExt.snd_add, dual_mul_snd,
      TrivSqZeroExt.fst_mul, dual_fst, dual_snd, zero_mul, add_zero,
      TrivSqZeroExt.snd_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
    linear_combination h

private theorem flat_tangent (j : Jet K) (c a i b : Idx) :
    (flatConnection (tangent j c) a i b).snd = flatDerivative j c a i b := by
  simp only [flatConnection, flatDerivative, lowerConnection, dPerturbation, ddPerturbation,
    tangent, sign_tangent, dual_mul_snd, TrivSqZeroExt.fst_mul,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_sub, dual_fst, dual_snd]
  ring

private def alongDerivative (j : Jet K) (c : Idx) : K :=
  raise j.k ⬝ᵥ j.ddphi c + raise (j.dk c) ⬝ᵥ j.dphi

private theorem correction_tangent (j : Jet K) (c a i b : Idx) :
    (correction (tangent j c) a i b).snd =
      (j.dphi c * along j.toFirstJet + j.phi * alongDerivative j c) *
          raise j.k a * j.k i * j.k b +
        j.phi * along j.toFirstJet * (raise (j.dk c) a * j.k i * j.k b +
          raise j.k a * j.dk c i * j.k b + raise j.k a * j.k i * j.dk c b) := by
  simp only [correction, along, alongDerivative, tangent, raise, sign_tangent, dotProduct,
    dual_mul_snd, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
    dual_fst, dual_snd, add_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring

private theorem trace_derivative (j : Jet K) (hn : Null j) (c b : Idx) :
    (∑ a, connectionDerivative j c a a b) = 0 := by
  have h := congrArg TrivSqZeroExt.snd
    (connection_trace (tangent j c) (tangent_null j hn c) (tangent_dnull j hn c) b)
  simpa only [TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_zero, connectionDerivative] using h

private theorem derivative_split (j : Jet K) (hn : Null j) (hg : Geodesic j) (c a i b : Idx) :
    connectionDerivative j c a i b =
      flatDerivative j c a i b + (correction (tangent j c) a i b).snd := by
  have h := congrArg TrivSqZeroExt.snd
    (connection_split (tangent j c) (tangent_null j hn c) (tangent_dnull j hn c)
      (tangent_geodesic j hg c) a i b)
  simpa only [TrivSqZeroExt.snd_add, flat_tangent, connectionDerivative] using h

private def twist (j : FirstJet K) : Matrix4 K :=
  fun a b => sign K a * (j.dk b a - j.dk a b)

private def symmetricTerm (j : FirstJet K) (i : Idx) : Covector K :=
  fun b => j.dphi i * j.k b + j.dphi b * j.k i + j.phi * (j.dk i b + j.dk b i)

private def twistTerm (j : FirstJet K) (i : Idx) : Covector K :=
  fun a => j.phi * twist j a i - raise j.dphi a * j.k i

private theorem flat_expansion (j : FirstJet K) (a i b : Idx) :
    flatConnection j a i b =
      raise j.k a * symmetricTerm j i b + twistTerm j i a * j.k b +
        j.phi * j.k i * twist j a b := by
  simp only [flatConnection, lowerConnection, dPerturbation,
    symmetricTerm, twistTerm, twist, raise]
  ring

private theorem twist_mul (j : FirstJet K) (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0)
    (hg : ∀ b, (∑ a, raise j.k a * j.dk a b) = 0) :
    twist j *ᵥ raise j.k = 0 ∧ j.k ᵥ* twist j = 0 := by
  constructor <;> ext i
  · have h₁ := hd i
    have h₂ := hg i
    simp only [mulVec, dotProduct, twist, raise, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Pi.zero_apply] at h₁ h₂ ⊢
    linear_combination sign K i * (h₂ - h₁)
  · have h₁ := hd i
    have h₂ := hg i
    simp only [vecMul, dotProduct, twist, raise, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Pi.zero_apply] at h₁ h₂ ⊢
    linear_combination h₁ - h₂

private theorem symmetric_contract (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0)
    (hg : ∀ b, (∑ a, raise j.k a * j.dk a b) = 0) (i : Idx) :
    symmetricTerm j i ⬝ᵥ raise j.k = along j * j.k i := by
  have hi := hd i
  have hgi := hg i
  simp only [symmetricTerm, along, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] at *
  linear_combination j.dphi i * hn + j.phi * (hi + hgi)

private theorem twistTerm_contract (j : FirstJet K) (h : j.k ᵥ* twist j = 0) (i : Idx) :
    j.k ⬝ᵥ twistTerm j i = -along j * j.k i := by
  have hi := congrFun h i
  simp only [vecMul, twistTerm, twist, along, dotProduct, raise, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Pi.zero_apply] at hi ⊢
  linear_combination j.phi * hi

private theorem trace_outer_pair (u v w x : Covector K) :
    trace (vecMulVec u v * vecMulVec w x) = (v ⬝ᵥ w) * (x ⬝ᵥ u) := by
  rw [vecMulVec_mul_vecMulVec, vecMulVec_smul, trace_smul, trace_vecMulVec,
    smul_eq_mul, dotProduct_comm u]

private theorem trace_outer_mul (u v : Covector K) (M : Matrix4 K) :
    trace (vecMulVec u v * M) = (v ᵥ* M) ⬝ᵥ u := by
  rw [vecMulVec_mul, trace_vecMulVec, dotProduct_comm]

private theorem trace_mul_outer (u v : Covector K) (M : Matrix4 K) :
    trace (M * vecMulVec u v) = v ⬝ᵥ (M *ᵥ u) := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

private def connectionMatrix (j : FirstJet K) (i : Idx) : Matrix4 K :=
  fun a b => connection j a i b

private theorem flat_last_contract (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0)
    (hg : ∀ b, (∑ a, raise j.k a * j.dk a b) = 0) (a i : Idx) :
    (∑ b, flatConnection j a i b * raise j.k b) = along j * raise j.k a * j.k i := by
  have hs := symmetric_contract j hn hd hg i
  have ht := congrFun (twist_mul j hd hg).1 a
  simp only [flat_expansion, mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Pi.zero_apply] at hs ht ⊢
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] at hn
  linear_combination raise j.k a * hs + twistTerm j i a * hn + j.phi * j.k i * ht

private theorem flat_middle_contract (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0)
    (hg : ∀ b, (∑ a, raise j.k a * j.dk a b) = 0) (a b : Idx) :
    (∑ i, flatConnection j a i b * raise j.k i) = along j * raise j.k a * j.k b := by
  have hs (i : Idx) : flatConnection j a i b = flatConnection j a b i := by
    simp only [flatConnection, lowerConnection, dPerturbation]
    ring
  simp only [hs]
  exact flat_last_contract j hn hd hg a b

private def flowDivergence (j : Jet K) : K :=
  ∑ a, (alongDerivative j a * raise j.k a + along j.toFirstJet * raise (j.dk a) a)

private theorem correction_divergence (j : Jet K) (hg : Geodesic j) (i b : Idx) :
    (∑ a, (correction (tangent j a) a i b).snd) =
      (along j.toFirstJet ^ 2 + j.phi * flowDivergence j) * j.k i * j.k b := by
  have hi := hg.value i
  have hb := hg.value b
  unfold flowDivergence
  simp only [correction_tangent, Fin.sum_univ_succ, Fin.sum_univ_zero] at hi hb ⊢
  generalize hA : along j.toFirstJet = A at *
  simp only [along, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] at hA
  linear_combination j.phi * A * (j.k b * hi + j.k i * hb) + A * j.k i * j.k b * hA

private theorem flat_tangent_value (j : Jet K) (c a i b : Idx) :
    (flatConnection (tangent j c) a i b).fst = flatConnection j.toFirstJet a i b := by
  simp only [flatConnection, lowerConnection, dPerturbation, tangent, sign_tangent,
    TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_add, dual_fst]

private theorem flat_contraction_derivative (j : Jet K) (hn : Null j) (hg : Geodesic j)
    (a b : Idx) :
    (∑ i, (flatDerivative j a a i b * raise j.k i +
        flatConnection j.toFirstJet a i b * raise (j.dk a) i)) =
      (alongDerivative j a * raise j.k a + along j.toFirstJet * raise (j.dk a) a) * j.k b +
        along j.toFirstJet * raise j.k a * j.dk a b := by
  have h := congrArg TrivSqZeroExt.snd
    (flat_middle_contract (tangent j a) (tangent_null j hn a) (tangent_dnull j hn a)
      (tangent_geodesic j hg a) a b)
  simp only [TrivSqZeroExt.snd_sum, dual_mul_snd, flat_tangent, flat_tangent_value] at h
  simp only [dual_mul_snd, TrivSqZeroExt.fst_mul, along, dotProduct, raise, tangent, sign_tangent,
    dual_fst, dual_snd, zero_mul, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
    Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  simp only [along, alongDerivative, dotProduct, raise, Fin.sum_univ_succ, Fin.sum_univ_zero]
  linear_combination h

private theorem twist_trace (j : FirstJet K) :
    trace (twist j * twist j) =
      2 * ∑ a, ∑ i, twist j a i * raise (j.dk a) i := by
  simp only [trace, diag, Matrix.mul_apply, twist, raise, Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring

private theorem flat_cross (j : Jet K) (hn : Null j) (hg : Geodesic j) (b : Idx) :
    2 * (∑ a, ∑ i, flatConnection j.toFirstJet a i b * raise (j.dk a) i) =
      j.phi * j.k b * trace (twist j.toFirstJet * twist j.toFirstJet) := by
  have hd : (∑ a, twistTerm j.toFirstJet b a * (raise j.k ⬝ᵥ j.dk a)) = 0 := by
    simp [hn.first]
  have hg' : (∑ i, sign K i * symmetricTerm j.toFirstJet b i *
      (∑ a, raise j.k a * j.dk a i)) = 0 := by simp [hg.value]
  have hs (i : Idx) : symmetricTerm j.toFirstJet i b = symmetricTerm j.toFirstJet b i := by
    simp only [symmetricTerm]
    ring
  simp only [twist_trace, flat_expansion, hs, twistTerm, dotProduct, raise,
    Fin.sum_univ_succ, Fin.sum_univ_zero] at hd hg' ⊢
  linear_combination 2 * hd + 2 * hg'

private theorem flat_divergence_contract (j : Jet K) (hn : Null j) (hg : Geodesic j) (b : Idx) :
    2 * (raise j.k ⬝ᵥ fun i => ∑ a, flatDerivative j a a i b) =
      j.k b * (2 * flowDivergence j - j.phi * trace (twist j.toFirstJet * twist j.toFirstJet)) := by
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun a (_ : a ∈ Finset.univ) => flat_contraction_derivative j hn hg a b)
  have hx := flat_cross j hn hg b
  have hg' := hg.value b
  simp only [dotProduct, flowDivergence, Fin.sum_univ_succ, Fin.sum_univ_zero] at h hx hg' ⊢
  linear_combination 2 * h - hx + (2 * along j.toFirstJet) * hg'

end Ring
section Field
variable {K : Type*} [Field K]

/-- The Christoffel symbol with its upper index raised by the exact inverse. -/
def christoffel (j : FirstJet K) (a i b : Idx) : K := connection j a i b / 2

/-- The derivative of the full Christoffel symbol, evaluated in the dual numbers. -/
def dChristoffel (j : Jet K) (c a i b : Idx) : K := connectionDerivative j c a i b / 2

/-- The covariant Ricci tensor of the metric jet. -/
def ricci (j : Jet K) (i b : Idx) : K :=
  ∑ a, (dChristoffel j a a i b - dChristoffel j b a a i +
    ∑ c, (christoffel j.toFirstJet a a c * christoffel j.toFirstJet c i b -
      christoffel j.toFirstJet a i c * christoffel j.toFirstJet c b a))

/-- The mixed Ricci tensor with the upper index raised by the full inverse. -/
def mixedRicci (j : Jet K) (i b : Idx) : K := ∑ r, ksInv j.phi j.k i r * ricci j r b

/-- The flat linear differential operator on the perturbation with zero background trace. -/
def linearRicci (j : Jet K) (i b : Idx) : K :=
  sign K i * (∑ a, flatDerivative j a a i b) / 2

theorem ks_christoffel_exact (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ i, raise j.k ⬝ᵥ j.dk i = 0)
    (hg : ∀ i, (∑ a, raise j.k a * j.dk a i) = 0) (a i b : Idx) :
    christoffel j a i b = flatConnection j a i b / 2 +
      j.phi * (raise j.k ⬝ᵥ j.dphi) * raise j.k a * j.k i * j.k b / 2 := by
  rw [christoffel, connection_split j hn hd hg, correction, add_div]
  rfl

theorem ks_christoffel_trace_zero (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ i, raise j.k ⬝ᵥ j.dk i = 0) (i : Idx) :
    (∑ a, christoffel j a a i) = 0 := by
  simp only [christoffel, div_eq_mul_inv, ← Finset.sum_mul, connection_trace j hn hd, zero_mul]

variable [CharZero K]

private theorem connection_matrix (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0)
    (hg : ∀ b, (∑ a, raise j.k a * j.dk a b) = 0) (i : Idx) :
    connectionMatrix j i =
      vecMulVec (raise j.k) (symmetricTerm j i + (j.phi * along j * j.k i) • j.k) +
        vecMulVec (twistTerm j i) j.k + (j.phi * j.k i) • twist j := by
  ext a b
  have h := ks_christoffel_exact j hn hd hg a i b
  simp only [christoffel, ← add_div] at h
  have hsplit := (div_left_inj' (by norm_num : (2 : K) ≠ 0)).mp h
  rw [connectionMatrix, hsplit, flat_expansion]
  simp only [along, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

private theorem trace_product (j : FirstJet K) (hn : raise j.k ⬝ᵥ j.k = 0)
    (hd : ∀ a, raise j.k ⬝ᵥ j.dk a = 0)
    (hg : ∀ b, (∑ a, raise j.k a * j.dk a b) = 0) (i b : Idx) :
    trace (connectionMatrix j i * connectionMatrix j b) =
      (2 * along j ^ 2 + j.phi ^ 2 * trace (twist j * twist j)) * j.k i * j.k b := by
  have ht := twist_mul j hd hg
  have hnk : j.k ⬝ᵥ raise j.k = 0 := (dotProduct_comm _ _).trans hn
  rw [connection_matrix j hn hd hg, connection_matrix j hn hd hg]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
    trace_add, trace_smul]
  have hleft (v : Covector K) : trace (vecMulVec (raise j.k) v * twist j) = 0 := by
    rw [trace_mul_comm, trace_mul_outer, ht.1, dotProduct_zero]
  have hright (u : Covector K) : trace (twist j * vecMulVec u j.k) = 0 := by
    rw [trace_mul_comm, trace_outer_mul, ht.2, zero_dotProduct]
  simp only [trace_outer_pair]
  simp only [hleft, hright, trace_outer_mul, trace_mul_outer,
    ht.1, ht.2, dotProduct_zero, zero_dotProduct, add_dotProduct,
    smul_dotProduct, hnk, add_zero, symmetric_contract j hn hd hg,
    twistTerm_contract j ht.2, zero_mul, mul_zero, smul_eq_mul]
  ring

private def scalarCurvatureCorrection (j : Jet K) : K :=
  2 * flowDivergence j - j.phi * trace (twist j.toFirstJet * twist j.toFirstJet)

private theorem covariant_ricci_split (j : Jet K) (hn : Null j) (hg : Geodesic j)
    (i b : Idx) :
    ricci j i b = (∑ a, flatDerivative j a a i b) / 2 +
      j.phi * scalarCurvatureCorrection j * j.k i * j.k b / 4 := by
  have hT : (∑ a, ∑ c, christoffel j.toFirstJet a a c *
      christoffel j.toFirstJet c i b) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ks_christoffel_trace_zero j.toFirstJet hn.value hn.first,
      zero_mul, Finset.sum_const_zero]
  have hDT := trace_derivative j hn b i
  have hprod := trace_product j.toFirstJet hn.value hn.first hg.value i b
  have hdiv := correction_divergence j hg i b
  have hsplit : (∑ a, connectionDerivative j a a i b) =
      (∑ a, flatDerivative j a a i b) + ∑ a, (correction (tangent j a) a i b).snd := by
    simp only [derivative_split j hn hg, Finset.sum_add_distrib]
  simp only [ricci, christoffel, dChristoffel, scalarCurvatureCorrection,
    Fin.sum_univ_succ, Fin.sum_univ_zero, trace, diag, Matrix.mul_apply,
    connectionMatrix] at hT hDT hprod hdiv hsplit ⊢
  linear_combination hsplit / 2 + hdiv / 2 - hDT / 2 - hprod / 4 + hT

/-- Raising the Ricci index with the full inverse cancels its covariant nonlinear term. -/
theorem ks_mixed_ricci_linear_in_phi (j : Jet K) (hn : Null j) (hg : Geodesic j) (i b : Idx) :
    mixedRicci j i b = linearRicci j i b := by
  rw [mixedRicci, sum_inv, linearRicci]
  simp only [covariant_ricci_split j hn hg]
  have h := flat_divergence_contract j hn hg b
  have hk := hn.value
  simp only [scalarCurvatureCorrection, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    raise] at h hk ⊢
  linear_combination -(j.phi * (sign K i * j.k i) / 4) * h -
    (j.phi ^ 2 * (2 * flowDivergence j -
      j.phi * trace (twist j.toFirstJet * twist j.toFirstJet)) *
      (sign K i * j.k i) * j.k b / 4) * hk

/-- Time independence and unit lower time component, through second order. -/
structure StationaryUnit (j : Jet K) : Prop where
  dphi_zero : j.dphi 0 = 0
  dk_zero : ∀ b, j.dk 0 b = 0
  ddphi_zero : ∀ b, j.ddphi 0 b = 0
  ddk_zero : ∀ a b, j.ddk 0 a b = 0
  k_time : j.k 0 = 1
  dk_time : ∀ a, j.dk a 0 = 0
  ddk_time : ∀ a b, j.ddk a b 0 = 0

def potential (j : FirstJet K) (i : Idx) : K := j.phi * j.k i

def fieldStrength (j : FirstJet K) (a b : Idx) : K :=
  j.dphi a * j.k b + j.phi * j.dk a b - (j.dphi b * j.k a + j.phi * j.dk b a)

/-- Second derivative of the single-copy potential. -/
def ddPotential (j : Jet K) (a b i : Idx) : K :=
  j.ddphi a b * j.k i + j.dphi a * j.dk b i + j.dphi b * j.dk a i + j.phi * j.ddk a b i

/-- The Cartesian divergence of the field strength with both indices raised. -/
def maxwellDivergence (j : Jet K) (i : Idx) : K :=
  ∑ a, sign K a * sign K i * (ddPotential j a a i - ddPotential j a i a)

theorem stationary_ks_ricci_maxwell_double_copy (j : Jet K) (hn : Null j) (hg : Geodesic j)
    (hs : StationaryUnit j) (i : Idx) :
    mixedRicci j i 0 = -(maxwellDivergence j i) / 2 ∧
      (mixedRicci j i 0 = 0 ↔ maxwellDivergence j i = 0) := by
  have ht (c a b : Idx) : ddPerturbation j c 0 a b = 0 := by
    simp [ddPerturbation, hs.dphi_zero, hs.dk_zero, hs.ddk_zero, hs.ddphi_zero,
      j.ddphi_symm c 0, j.ddk_symm c 0]
  have hh (c a b : Idx) : ddPerturbation j c a b 0 = ddPotential j c a b := by
    simp [ddPerturbation, ddPotential, hs.k_time, hs.dk_time, hs.ddk_time]
    ring
  have h : mixedRicci j i 0 = -(maxwellDivergence j i) / 2 := by
    rw [ks_mixed_ricci_linear_in_phi j hn hg]
    simp only [linearRicci, flatDerivative, hh, ht, add_zero, maxwellDivergence]
    congr 1
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    ring
  exact ⟨h, by rw [h]; simp⟩

theorem stationary_ks_ricci_poisson_zeroth_copy (j : Jet K) (hn : Null j) (hg : Geodesic j)
    (hs : StationaryUnit j) :
    mixedRicci j 0 0 = (j.ddphi 1 1 + j.ddphi 2 2 + j.ddphi 3 3) / 2 ∧
      (mixedRicci j 0 0 = 0 ↔ j.ddphi 1 1 + j.ddphi 2 2 + j.ddphi 3 3 = 0) := by
  have hz (a : Idx) : ddPotential j a 0 a = 0 := by
    simp [ddPotential, j.ddphi_symm a 0, j.ddk_symm a 0, hs.ddphi_zero,
      hs.dk_zero, hs.dphi_zero, hs.ddk_zero]
  have h := (stationary_ks_ricci_maxwell_double_copy j hn hg hs 0).1
  simp only [maxwellDivergence, hz, sub_zero] at h
  simp [ddPotential, hs.k_time, hs.dk_time, hs.ddk_time,
    hs.ddphi_zero, Fin.sum_univ_succ, sign] at h
  have he : mixedRicci j 0 0 = (j.ddphi 1 1 + j.ddphi 2 2 + j.ddphi 3 3) / 2 := by
    rw [h]
    ring
  exact ⟨he, by rw [he]; simp⟩

/-- The two-jet of (1, (1-t²)/(1+t²), 2t/(1+t²), 0) at t = 0. -/
def nonGeodesicJet (φ : K) : Jet K where
  phi := φ
  k := ![1, 1, 0, 0]
  dphi := 0
  dk a b := if a = 0 ∧ b = 2 then 2 else 0
  ddphi := 0
  ddk a b c := if a = 0 ∧ b = 0 ∧ c = 1 then -4 else 0
  ddphi_symm _ _ := rfl
  ddk_symm a b c := by simp [and_left_comm]

set_option maxHeartbeats 1200000 in
theorem ks_mixed_ricci_nongeodesic (φ : K) (hφ : φ ≠ 0) :
    Null (nonGeodesicJet φ) ∧ ¬Geodesic (nonGeodesicJet φ) ∧
      mixedRicci (nonGeodesicJet φ) 0 0 - linearRicci (nonGeodesicJet φ) 0 0 =
        2 * φ ^ 2 ∧ mixedRicci (nonGeodesicJet φ) 0 0 ≠ linearRicci (nonGeodesicJet φ) 0 0 := by
  have hn : Null (nonGeodesicJet φ) := by
    constructor
    · norm_num [nonGeodesicJet, raise, sign, dotProduct, Fin.sum_univ_succ]
    · intro a
      fin_cases a <;> norm_num [nonGeodesicJet, raise, sign, dotProduct, Fin.sum_univ_succ]
    · intro a b
      fin_cases a <;> fin_cases b <;>
        norm_num [nonGeodesicJet, raise, sign, dotProduct, Fin.sum_univ_succ]
  have hg : ¬Geodesic (nonGeodesicJet φ) := by
    intro hg
    have h := hg.value 2
    norm_num [nonGeodesicJet, raise, sign, Fin.sum_univ_succ] at h
  have h : mixedRicci (nonGeodesicJet φ) 0 0 - linearRicci (nonGeodesicJet φ) 0 0 =
      2 * φ ^ 2 := by
    simp only [mixedRicci, sum_inv, ricci, christoffel, dChristoffel, connectionDerivative,
      connection, linearRicci, flatDerivative, lowerConnection, dotProduct]
    simp only [ddPerturbation, dPerturbation, raise, TrivSqZeroExt.snd_sub,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sum, dual_mul_snd, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub, tangent, sign_tangent, dual_fst, dual_snd]
    norm_num [nonGeodesicJet, sign, Fin.sum_univ_succ] <;> ring
  refine ⟨hn, hg, h, fun he => ?_⟩
  rw [he, sub_self] at h
  exact (mul_ne_zero (by norm_num : (2 : K) ≠ 0) (pow_ne_zero _ hφ)) h.symm

end Field
section Weyl
open WeylNullScreen Polynomial Omega.ProjectivePolynomial

/-- A spin-one binary form in the affine chart of the two principal rays. -/
def maxwellQuadratic (a : ℂ) (r s : FutureNullRay) : ℂ[X] := a • nodalQuadratic r s

/-- Squaring the spin-one form gives a binary quartic in the Weyl chart. -/
def maxwellSquare (a : ℂ) (r s : FutureNullRay) : WeylQuartic :=
  ⟨a ^ 2 • nodalQuadratic r s ^ 2, by
    apply mem_degreeLT.mpr
    rw [smul_eq_C_mul]
    have h := (natDegree_C_mul_le (a ^ 2) (nodalQuadratic r s ^ 2)).trans
      (natDegree_pow_le_of_le 2 (nodal_degree_le r s))
    exact (natDegree_le_iff_degree_le.mp h).trans_lt (by decide)⟩

private theorem square_polynomial (a : ℂ) (r s : FutureNullRay) :
    (maxwellSquare a r s : ℂ[X]) = a ^ 2 • nodalQuadratic r s ^ 2 := rfl
private theorem tide_eq (c : Weyl4) (r : FutureNullRay) :
    complexTide c.val r = Omega.ProjectivePolynomial.eval 4 r (weylQuarticEquiv c : ℂ[X]) := by
  rw [← weylQuarticEquiv_eval]
  cases r <;> rfl

/-- The Weyl tensor of the quartic square has two double principal null directions. -/
theorem petrov_type_d_double_copy_quartic (a : ℂ) (ha : a ≠ 0) (r s t : FutureNullRay)
    (hrs : r ≠ s) (htr : t ≠ r) (hts : t ≠ s) :
    let Q := maxwellSquare a r s
    let C := weylQuarticEquiv.symm Q
    (Q : ℂ[X]) = maxwellQuadratic a r s ^ 2 ∧
      multiplicity 4 r (Q : ℂ[X]) = 2 ∧ multiplicity 4 s (Q : ℂ[X]) = 2 ∧ C ≠ 0 ∧
      complexTide C.val t = a ^ 2 * Omega.ProjectivePolynomial.eval 4 t (nodalQuadratic r s ^ 2) ∧
      ∀ D : Weyl4, D ≠ 0 → multiplicity 4 r (weylQuarticEquiv D : ℂ[X]) = 2 →
        multiplicity 4 s (weylQuarticEquiv D : ℂ[X]) = 2 →
        complexTide D.val t = complexTide C.val t → D = C := by
  dsimp only
  have hm := pow_ne_zero 2 (nodal_monic r s).ne_zero
  have he := nodal_square_eval_ne_zero r s t htr hts
  have ht : complexTide (weylQuarticEquiv.symm (maxwellSquare a r s)).val t =
      a ^ 2 * Omega.ProjectivePolynomial.eval 4 t (nodalQuadratic r s ^ 2) := by
    rw [tide_eq, LinearEquiv.apply_symm_apply, square_polynomial, Omega.ProjectivePolynomial.eval_smul]
  refine ⟨?_, ?_, ?_, fun hz => ?_, ht, fun D hD hr hs hT => ?_⟩
  · simp [square_polynomial, maxwellQuadratic, smul_eq_C_mul, mul_pow]
  · rw [square_polynomial, multiplicity_smul (pow_ne_zero 2 ha) hm, nodal_square_multiplicity r s hrs]
  · rw [square_polynomial, multiplicity_smul (pow_ne_zero 2 ha) hm, nodalQuadratic, mul_comm]
    exact nodal_square_multiplicity s r hrs.symm
  · rw [hz, tide_eq, map_zero] at ht
    apply mul_ne_zero (pow_ne_zero 2 ha) he
    cases t <;> simpa [Omega.ProjectivePolynomial.eval] using ht.symm
  · let p := weylQuarticEquiv D
    have hp : (p : ℂ[X]) ≠ 0 := by
      intro hz
      apply hD
      apply weylQuarticEquiv.injective
      rw [map_zero]
      exact Subtype.ext hz
    have hd : (p : ℂ[X]).natDegree ≤ 4 :=
      Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hp).2 (mem_degreeLT.mp p.property))
    obtain ⟨b, hb⟩ := quartic_eq_smul_nodal_square hp hd hrs hr hs
    rw [tide_eq, show (weylQuarticEquiv D : ℂ[X]) = (p : ℂ[X]) from rfl, hb,
      Omega.ProjectivePolynomial.eval_smul, ht] at hT
    apply weylQuarticEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext (by rw [square_polynomial, ← mul_right_cancel₀ he hT]; exact hb)

/-- In the radial frame the Coulomb quadratic is a multiple of X and its square a multiple of X². -/
theorem coulomb_schwarzschild_quartic (a : ℂ) :
    maxwellQuadratic a (some 0) none = a • X ∧
      (maxwellSquare a (some 0) none : ℂ[X]) = a ^ 2 • X ^ 2 ∧
      complexTide (weylQuarticEquiv.symm (maxwellSquare a (some 0) none)).val (some 1) = a ^ 2 := by
  simp [maxwellQuadratic, square_polynomial, nodalQuadratic, rayFactor, tide_eq,
    Omega.ProjectivePolynomial.eval]
end Weyl
end D5.S3.Geometry.Lorentz.KerrSchildDoubleCopy4D
