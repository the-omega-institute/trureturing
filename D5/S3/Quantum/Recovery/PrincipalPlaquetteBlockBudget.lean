/- GID: D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget
   mirror-E: none(waiver:principal-plaquette-block-budget)
   anchors: []
   utility: none
   digest: Coherent rows strengthen the one-party plaquette obstruction for native paired channels. -/


import D5.S3.Quantum.Recovery.PrincipalPlaquettePhaseDiamond
import D5.S3.Quantum.Recovery.PrincipalTrianglePhaseDiamond
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic


/-!
# Coherent block budget for the one-party plaquette obstruction

Tagged rank-one inputs bound entire rows of channel error coefficients;
the resulting Frobenius budget sharpens the isolated-entry argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Recovery.PrincipalPlaquetteBlockBudget


section

namespace RTMultiFibre

open Matrix
open scoped Matrix ComplexOrder MatrixOrder CStarAlgebra BigOperators
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Recovery.PrincipalTrianglePhase
open NativeDiamond (matrixAction)

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private theorem reference_block (channel : QuantumChannel a b)
    (X : Matrix (Fin 2 × a) (Fin 2 × a) ℂ) :
    CStarMatrix.ofMatrix.symm (referenceAction channel (CStarMatrix.ofMatrix X)) =
      RTDiamond.amplify (matrixAction channel) X := by
  ext ⟨r, p⟩ ⟨s, q⟩
  rfl

private theorem referenceError_le_two (first second : QuantumChannel a b)
    (n : ℕ) (X : DensityState (Fin n × a)) :
    referenceError first second X ≤ 2 := by
  have h := traceDistance_le_one (referenceState first X) (referenceState second X)
  change referenceError first second X / 2 ≤ 1 at h
  linarith

private theorem referenceError_le_diamond (first second : QuantumChannel a b)
    (n : ℕ) (X : DensityState (Fin n × a)) :
    referenceError first second X ≤ diamondDistance first second := by
  unfold diamondDistance
  apply le_csSup
  · refine ⟨2, ?_⟩
    intro z hz
    rcases hz with hz | ⟨k, Y, rfl⟩
    · rw [Set.mem_singleton_iff.mp hz]; norm_num
    · exact referenceError_le_two first second k Y
  · exact Or.inr ⟨n, X, rfl⟩

/-- The stabilized density-state distance bounds a single tested
rank-one coefficient with no loss from the two reference tags. -/
theorem vectorCoefficient_le_diamondDistance (first second : QuantumChannel a b)
    (u v : a → ℂ) (huv : star u ⬝ᵥ u = 1) (hvv : star v ⬝ᵥ v = 1) (p q : b) :
    ‖((matrixAction first - matrixAction second) (Matrix.vecMulVec u (star v))) p q‖ ≤
      diamondDistance first second := by
  let t : Fin 2 × a → ℂ := fun z => if z.1 = 0 then u z.2 else v z.2
  let T : Matrix (Fin 2 × a) (Fin 2 × a) ℂ :=
    (1/2 : ℂ) • Matrix.vecMulVec t (star t)
  have hT : T.PosSemidef := by
    apply (Matrix.posSemidef_vecMulVec_self_star t).smul
    exact Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩
  have htrace : T.trace = 1 := by
    unfold T Matrix.trace
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
      Pi.star_apply, t, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, ← Finset.mul_sum]
    simp_rw [mul_comm (u _) (star (u _)), mul_comm (v _) (star (v _))]
    change (1/2 : ℂ) * (star u ⬝ᵥ u) + (1/2 : ℂ) * (star v ⬝ᵥ v) = 1
    rw [huv, hvv]
    norm_num
  let X : DensityState (Fin 2 × a) := ⟨CStarMatrix.ofMatrix T,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hT.nonneg, htrace⟩
  let Y : Matrix (Fin 2 × b) (Fin 2 × b) ℂ :=
    CStarMatrix.ofMatrix.symm (referenceState first X).1 -
      CStarMatrix.ofMatrix.symm (referenceState second X).1
  have hP : (CStarMatrix.ofMatrix.symm (referenceState first X).1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin 2 × b)).symm
        (referenceState first X).2.1)
  have hQ : (CStarMatrix.ofMatrix.symm (referenceState second X).1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin 2 × b)).symm
        (referenceState second X).2.1)
  have hh : Y.IsHermitian := hP.isHermitian.sub hQ.isHermitian
  have hneq : ((0,p) : Fin 2 × b) ≠ (1,q) := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst h)
  have hu := RTTraceSwap.twice_offdiag_le_of_dual_max Y (0,p) (1,q) hneq
    (hh.apply (1,q) (0,p)).symm (traceNorm Y) (traceNorm_eq_max_re_tr_U Y)
  have he : Y (0,p) (1,q) = (1/2 : ℂ) *
      ((matrixAction first - matrixAction second) (Matrix.vecMulVec u (star v))) p q := by
    change (CStarMatrix.ofMatrix.symm
        (referenceAction first (CStarMatrix.ofMatrix (T))) -
      CStarMatrix.ofMatrix.symm
        (referenceAction second (CStarMatrix.ofMatrix (T)))) (0,p) (1,q) = _
    rw [reference_block, reference_block, ← RTDiamond.amplify_sub]
    have hc : T.submatrix (fun a => (0,a)) (fun b => (1,b)) =
        (1/2 : ℂ) • Matrix.vecMulVec u (star v) := by
      ext i j
      simp [T, t, Matrix.vecMulVec_apply, show (1 : Fin 2) ≠ 0 by decide]
    change ((matrixAction first - matrixAction second)
      (T.submatrix (fun a => (0,a)) (fun b => (1,b)))) p q = _
    rw [hc, map_smul]
    rfl
  have hn : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num [norm_div]
  rw [he, Complex.norm_mul, hn] at hu
  have hentry : ‖((matrixAction first - matrixAction second) (Matrix.vecMulVec u (star v))) p q‖ ≤
      traceNorm Y := by linarith
  exact hentry.trans (referenceError_le_diamond first second 2 X)

end RTMultiFibre

end

section

namespace RTMultiFibre

open Matrix
open scoped Matrix ComplexOrder BigOperators
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Recovery.PrincipalTrianglePhase
open NativeDiamond (matrixAction)

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- An entire matrix-unit error row at fixed output coordinates consumes
at most one squared diamond budget. -/
theorem matrixUnit_row_square_le (first second : QuantumChannel a b)
    (i : a) (p q : b) :
    ∑ j : a, ‖((matrixAction first - matrixAction second) (Matrix.single i j 1)) p q‖^2 ≤
      (diamondDistance first second)^2 := by
  let A := matrixAction first - matrixAction second
  let L : a → ℂ := fun j => A (Matrix.single i j 1) p q
  let S : ℝ := ∑ j : a, ‖L j‖^2
  change S ≤ _
  have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases h0 : S = 0
  · rw [h0]; positivity
  let R := Real.sqrt S
  have hR : 0 < R := Real.sqrt_pos.mpr (lt_of_le_of_ne hs (Ne.symm h0))
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hRs : R^2 = S := Real.sq_sqrt hs
  let u : a → ℂ := Pi.single i 1
  let v : a → ℂ := fun j => L j / (R : ℂ)
  have hu : star u ⬝ᵥ u = 1 := by simp [u, dotProduct, Pi.single_apply]
  have hp (j : a) : star (L j) * L j = ((‖L j‖^2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.sq_norm]
  have hstar (j : a) : star (L j / (R : ℂ)) = star (L j) / (R : ℂ) := by
    simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
  have hv : star v ⬝ᵥ v = 1 := by
    simp only [dotProduct, Pi.star_apply, v]
    simp_rw [hstar, div_mul_div_comm, hp, ← pow_two]
    rw [← Finset.sum_div, ← Complex.ofReal_sum, ← Complex.ofReal_pow, hRs]
    exact div_self (Complex.ofReal_ne_zero.mpr h0)
  have hmat : Matrix.vecMulVec u (star v) = ∑ j : a, star (v j) • Matrix.single i j (1:ℂ) := by
    ext k l
    simp [u, Matrix.vecMulVec_apply, Matrix.sum_apply, Pi.single_apply, Matrix.single_apply,
      ite_and, eq_comm]
  have hrow : (A (Matrix.vecMulVec u (star v))) p q = (R : ℂ) := by
    rw [hmat, map_sum]
    simp only [Matrix.sum_apply, map_smul, Matrix.smul_apply, smul_eq_mul]
    change ∑ j : a, (star (L j / (R : ℂ))) * L j = _
    simp_rw [hstar, div_mul_eq_mul_div, hp]
    rw [← Finset.sum_div, ← Complex.ofReal_sum]
    change (S : ℂ) / (R : ℂ) = (R : ℂ)
    rw [← hRs, Complex.ofReal_pow]
    field_simp
  have h := vectorCoefficient_le_diamondDistance first second u v hu hv p q
  change ‖(A (Matrix.vecMulVec u (star v))) p q‖ ≤ _ at h
  rw [hrow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at h
  rw [← hRs]
  nlinarith [sq_nonneg (diamondDistance first second - R)]

/-- Two restricted rows of raw coefficient errors pay at most two
squared diamond budgets, even when the native channels leak. -/
theorem matrixUnit_two_row_square_le (first second : QuantumChannel a b)
    (i : Fin 2 → a) (j : Fin 2 ↪ a) (p q : b) :
    (∑ k : Fin 2, ∑ l : Fin 2,
      ‖((matrixAction first - matrixAction second) (Matrix.single (i k) (j l) 1)) p q‖^2) ≤
      2 * (diamondDistance first second)^2 := by
  let f (k : Fin 2) (l : a) :=
    ‖((matrixAction first - matrixAction second) (Matrix.single (i k) l 1)) p q‖^2
  have hi (k : Fin 2) : (∑ l : Fin 2, f k (j l)) ≤ (diamondDistance first second)^2 := by
    rw [← Finset.sum_map Finset.univ j (f k)]
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (Finset.univ.map j)) (f := f k) (by intros; apply sq_nonneg)
    exact h.trans (matrixUnit_row_square_le first second (i k) p q)
  change (∑ k : Fin 2, ∑ l : Fin 2, f k (j l)) ≤ _
  rw [Fin.sum_univ_two]
  linarith only [hi 0, hi 1]

end RTMultiFibre

end

section

namespace RTWeightBudget
open scoped BigOperators

/-- Four weights in [1, 9/2] and their Frobenius budget imply the
explicit scalar lower bound. The operator witness is not asserted here. -/
theorem four_weight_lower_bound (w e : Fin 4 → ℝ) (p δ : ℝ)
    (hp : 0 < p) (_hp1 : p ≤ 1) (hd : 0 ≤ δ)
    (hl : ∀ i, 1 ≤ w i) (hu : ∀ i, w i ≤ 9/2)
    (hW : 8*p ≤ ∑ i, w i)
    (hbudget : (p/2)*(∑ i, w i)-2 ≤ ∑ i, w i * e i)
    (hF : (∑ i, e i ^ 2) ≤ 2*δ^2) :
    (12/11)*(p/2-1/(4*p)) ≤ δ := by
  let W : ℝ := ∑ i, w i
  let S : ℝ := ∑ i, w i * e i
  let A : ℝ := ∑ i, w i ^ 2
  let B : ℝ := ∑ i, e i ^ 2
  change 8*p ≤ W at hW
  change (p/2)*W-2 ≤ S at hbudget
  change B ≤ 2*δ^2 at hF
  have hA : A ≤ (11/2)*W-18 := by
    calc
      A ≤ ∑ i : Fin 4, ((11/2)*w i-9/2) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [mul_nonneg (sub_nonneg.mpr (hl i)) (sub_nonneg.mpr (hu i))]
      _ = (11/2)*W-18 := by
        simp [W, Finset.sum_sub_distrib, Finset.mul_sum]
        ring
  have hW0 : 0 ≤ W := by linarith
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
  have hs : S^2 ≤ A*B := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w e
  have hcap : 2*A ≤ ((11/12)*W)^2 := by
    nlinarith [sq_nonneg ((11/12)*W-6)]
  have hsq : S^2 ≤ (((11/12)*W)*δ)^2 := by
    calc
      S^2 ≤ A*B := hs
      _ ≤ A*(2*δ^2) := mul_le_mul_of_nonneg_left hF hA0
      _ = (2*A)*δ^2 := by ring
      _ ≤ ((11/12)*W)^2 * δ^2 := mul_le_mul_of_nonneg_right hcap (sq_nonneg δ)
      _ = (((11/12)*W)*δ)^2 := by ring
  have hs' : S ≤ ((11/12)*W)*δ := by
    have hnon : 0 ≤ ((11/12)*W)*δ := mul_nonneg (mul_nonneg (by norm_num) hW0) hd
    by_contra! hlt
    have hpos := mul_pos (sub_pos.mpr hlt) (show 0 < S+((11/12)*W)*δ by linarith)
    nlinarith
  have hrecip : 2 ≤ (1/(4*p))*W := by
    have hm := mul_le_mul_of_nonneg_left hW (show 0 ≤ 1/(4*p) by positivity)
    calc
      2 = (1/(4*p))*(8*p) := by field_simp; ring
      _ ≤ _ := hm
  have hscaled : (p/2-1/(4*p))*W ≤ ((11/12)*δ)*W := by
    calc
      (p/2-1/(4*p))*W ≤ (p/2)*W-2 := by rw [sub_mul]; linarith
      _ ≤ S := hbudget
      _ ≤ ((11/12)*δ)*W := by convert hs' using 1; ring
  have hWpos : 0 < W := by linarith
  have hfinal := le_of_mul_le_mul_right hscaled hWpos
  linarith

end RTWeightBudget

end

section

namespace RTWeightBudget
open scoped BigOperators

/-- Scalar reduction of the opposite-phase gauge. The modulus floor and
the reciprocal and second-block budgets are the operator interface. -/
theorem one_party_gauge_block_lower (r y e : Fin 4 → ℝ) (p δ : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hd : 0 ≤ δ)
    (hr : ∀ i, 1/2-δ ≤ r i ∧ r i ≤ 1)
    (hg : ∀ i, r i * y i = p/2-e i)
    (hy : (∑ i, y i) ≤ 2)
    (hW : 8*p ≤ ∑ i, 1/r i)
    (hF : (∑ i, e i ^ 2) ≤ 2*δ^2) :
    (12/11)*(p/2-1/(4*p)) ≤ δ := by
  by_cases hsmall : δ < 5/18
  · have hrpos (i : Fin 4) : 0 < r i := by linarith [(hr i).1]
    let w : Fin 4 → ℝ := fun i => 1/r i
    have hwlow (i : Fin 4) : 1 ≤ w i :=
      (le_div_iff₀ (hrpos i)).2 (by simpa using (hr i).2)
    have hwup (i : Fin 4) : w i ≤ 9/2 :=
      (div_le_iff₀ (hrpos i)).2 (by linarith [(hr i).1])
    have hpoint (i : Fin 4) : w i * e i = (p/2)*w i-y i := by
      have hi := hg i
      dsimp [w]
      field_simp [ne_of_gt (hrpos i)]
      linarith
    have hbudget : (p/2)*(∑ i, w i)-2 ≤ ∑ i, w i * e i := by
      simp_rw [hpoint]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      linarith
    exact four_weight_lower_bound w e p δ hp hp1 hd hwlow hwup hW hbudget hF
  · have hrec : (1/4 : ℝ) ≤ 1/(4*p) :=
      (le_div_iff₀ (by positivity)).2 (by linarith)
    linarith

theorem one_party_gauge_block_lower_of_sum (r y e : Fin 4 → ℝ) (p δ : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hd : 0 ≤ δ)
    (hr : ∀ i, 1/2-δ ≤ r i ∧ r i ≤ 1)
    (hg : ∀ i, r i * y i = p/2-e i)
    (hy : (∑ i, y i) ≤ 2)
    (hsum : (∑ i, r i) ≤ 2/p)
    (hF : (∑ i, e i ^ 2) ≤ 2*δ^2) :
    (12/11)*(p/2-1/(4*p)) ≤ δ := by
  by_cases hsmall : δ < 5/18
  · have hrpos (i : Fin 4) : 0 < r i := by linarith [(hr i).1]
    have hprod : (16 : ℝ) ≤ (∑ i, r i) * ∑ i, 1 / r i := by
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        (r := fun _ : Fin 4 => (1 : ℝ)) (f := r) (g := fun i => 1 / r i)
        Finset.univ
        (fun i _ => (hrpos i).le)
        (fun i _ => div_nonneg (by norm_num) (hrpos i).le)
        (fun i _ => by rw [mul_one_div_cancel (ne_of_gt (hrpos i)), one_pow])
      norm_num at hcs
      simpa only [one_div] using hcs
    have hW0 : 0 ≤ ∑ i, 1 / r i :=
      Finset.sum_nonneg (fun i _ => div_nonneg (by norm_num) (hrpos i).le)
    have hb := hprod.trans (mul_le_mul_of_nonneg_right hsum hW0)
    have hW : 8*p ≤ ∑ i, 1/r i := by
      have h := mul_le_mul_of_nonneg_right hb hp.le
      have he : (2/p)*p = 2 := div_mul_cancel₀ _ hp.ne'
      rw [mul_right_comm, he] at h
      linarith
    exact one_party_gauge_block_lower r y e p δ hp hp1 hd hr hg hy hW hF
  · have hrec : (1/4 : ℝ) ≤ 1/(4*p) :=
      (le_div_iff₀ (by positivity)).2 (by linarith)
    linarith

end RTWeightBudget

end

section

namespace RTMultiFibre

open Matrix
open scoped Matrix ComplexOrder BigOperators
open D5.S3.Quantum.Recovery.PrincipalPlaquettePhaseDiamond

private def projectedError (x y s u : ℂ) : ℝ :=
  (star (s*x*u) * ((1/2 : ℂ)-x*y)).re / ‖x‖

private theorem opposite_gauge_exact {x y s u : ℂ} {p : ℝ}
    (hx : x ≠ 0) (hs : ‖s‖ = 1) (hu : ‖u‖ = 1)
    (hre : (s*x*u).re = p*‖x‖) :
    ‖x‖ * (star s*y*star u).re = p/2-projectedError x y s u ∧
      (projectedError x y s u)^2 ≤ ‖(1/2 : ℂ)-x*y‖^2 := by
  let x' := s*x*u
  let y' := star s*y*star u
  have unit (z : ℂ) (h : ‖z‖ = 1) : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, h]; norm_num
  have hprod : x'*y' = x*y := by
    calc
      x'*y' = (s*star s)*(u*star u)*(x*y) := by dsimp [x', y']; ring
      _ = _ := by rw [unit s hs, unit u hu, one_mul, one_mul]
  have hnorm : ‖x'‖ = ‖x‖ := by simp [x', hs, hu]
  have hxs : star x' * x' = ((‖x'‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.sq_norm]
  have hfirst : (star x' * (1/2 : ℂ)).re = x'.re/2 := by
    rw [show (1/2 : ℂ) = (((1/2 : ℝ)) : ℂ) by norm_num, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.star_def, Complex.conj_re]
    ring
  have hsecond : (((‖x'‖ ^ 2 : ℝ) : ℂ)*y').re = ‖x'‖^2*y'.re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hp : (star x' * ((1/2 : ℂ)-x'*y')).re =
      x'.re/2 - ‖x'‖^2*y'.re := by
    rw [show star x' * ((1/2 : ℂ)-x'*y') = star x' * (1/2 : ℂ) -
        (star x' * x')*y' by ring, hxs, Complex.sub_re, hfirst, hsecond]
  have hp0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hn : ‖star x' * ((1/2 : ℂ)-x*y)‖ = ‖x‖ * ‖(1/2 : ℂ)-x*y‖ := by
    rw [Complex.norm_mul, norm_star, hnorm]
  change ‖x‖ * y'.re = _ ∧ _
  constructor
  · unfold projectedError
    change ‖x‖ * y'.re = p/2 - (star x' * ((1/2 : ℂ)-x*y)).re / ‖x‖
    rw [← hprod, hp, hnorm, show x'.re = p*‖x‖ from hre]
    field_simp
    ring
  · have hh := Complex.abs_re_le_norm (star x' * ((1/2 : ℂ)-x*y))
    rw [hn] at hh
    unfold projectedError
    have hq : |(star x' * ((1/2 : ℂ)-x*y)).re / ‖x‖| ≤ ‖(1/2 : ℂ)-x*y‖ := by
      rw [abs_div, abs_of_pos hp0]
      exact (div_le_iff₀ hp0).2 (by simpa only [mul_comm] using hh)
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hq |>.trans_eq' (sq_abs _)

private theorem contraction_entry_bounds {a b c d : ℂ} (h : IsTwoContraction a b c d) :
    ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖c‖ ≤ 1 ∧ ‖d‖ ≤ 1 := by
  have h0 := h 1 0
  have h1 := h 0 1
  norm_num at h0 h1
  exact ⟨(sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (by nlinarith [sq_nonneg ‖c‖]),
    (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (by nlinarith [sq_nonneg ‖d‖]),
    (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (by nlinarith [sq_nonneg ‖a‖]),
    (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (by nlinarith [sq_nonneg ‖b‖])⟩

/-- A block Frobenius error budget strengthens the one-party phase obstruction. -/
theorem improved_plaquette_of_frobenius {a b c d A B C D : ℂ} {δ : ℝ}
    (hX : IsTwoContraction a b c d) (hY : IsTwoContraction A B C D)
    (h0 : ‖(1/2 : ℂ)-a*A‖ ≤ δ) (h1 : ‖(1/2 : ℂ)-b*B‖ ≤ δ)
    (h2 : ‖(1/2 : ℂ)-c*C‖ ≤ δ) (h3 : ‖(1/2 : ℂ)-d*D‖ ≤ δ)
    (hF : ‖(1/2 : ℂ)-a*A‖^2 + ‖(1/2 : ℂ)-b*B‖^2 +
        (‖(1/2 : ℂ)-c*C‖^2 + ‖(1/2 : ℂ)-d*D‖^2) ≤ 2*δ^2) :
    let θ := plaquetteArg a b c d
    let p := Real.cos (θ/4)
    (12/11)*(p/2-1/(4*p)) ≤ δ := by
  let θ := plaquetteArg a b c d
  let p := Real.cos (θ/4)
  change (12/11)*(p/2-1/(4*p)) ≤ δ
  have hθ := plaquette_arg_abs_le_pi a b c d
  change |θ| ≤ Real.pi at hθ
  have hp0 : 0 < p := by
    change 0 < Real.cos (θ/4)
    apply Real.cos_pos_of_mem_Ioo
    constructor <;>
      linarith [le_abs_self θ, neg_abs_le θ, Real.pi_pos]
  have hp1 : p ≤ 1 := Real.cos_le_one _
  by_cases hsmall : δ < 5/18
  · obtain ⟨xa,xb,xc,xd⟩ := contraction_entry_bounds hX
    obtain ⟨ya,yb,yc,yd⟩ := contraction_entry_bounds hY
    have lower {x y : ℂ} (hb : ‖y‖ ≤ 1)
        (h : ‖(1/2 : ℂ)-x*y‖ ≤ δ) : 1/2-δ ≤ ‖x‖ := by
      exact (matrix_unit_product_floor h).trans
        (by simpa using mul_le_mul_of_nonneg_left hb (norm_nonneg x))
    have za := lower ya h0
    have zb := lower yb h1
    have zc := lower yc h2
    have zd := lower yd h3
    have nz {x : ℂ} (h : 1/2-δ ≤ ‖x‖) : x ≠ 0 :=
      norm_pos_iff.mp (by linarith)
    obtain ⟨s,t,u,v,hs,ht,hu,hv,ha,hb,hc,hd⟩ :=
      shared_checkerboard_gauge a b c d θ (plaquette_arg_angle (nz za) (nz zb) (nz zc) (nz zd))
    obtain ⟨aa,aa2⟩ := opposite_gauge_exact (nz za) hs hu ha
    obtain ⟨ab,ab2⟩ := opposite_gauge_exact (nz zb) hs hv hb
    obtain ⟨ac,ac2⟩ := opposite_gauge_exact (nz zc) ht hu hc
    obtain ⟨ad,ad2⟩ := opposite_gauge_exact (nz zd) ht hv hd
    let r : Fin 4 → ℝ := ![‖a‖,‖b‖,‖c‖,‖d‖]
    let y : Fin 4 → ℝ := ![(star s*A*star u).re, (star s*B*star v).re,
      (star t*C*star u).re, (star t*D*star v).re]
    let e : Fin 4 → ℝ := ![projectedError a A s u, projectedError b B s v,
      projectedError c C t u, projectedError d D t v]
    apply RTWeightBudget.one_party_gauge_block_lower_of_sum r y e p δ hp0 hp1
      ((norm_nonneg _).trans h0)
    · intro i
      fin_cases i <;> first | exact ⟨za,xa⟩ | exact ⟨zb,xb⟩ | exact ⟨zc,xc⟩ | exact ⟨zd,xd⟩
    · intro i
      fin_cases i <;> first | exact aa | exact ab | exact ac | exact ad
    · have h := (Complex.re_le_norm _).trans
        (contraction_flat_test hY (star s) (star t) (star u) (star v)
          (by simpa using hs) (by simpa using ht) (by simpa using hu) (by simpa using hv))
      rw [show star s*(A*star u+B*star v)+star t*(C*star u+D*star v) =
        ((star s*A*star u+star s*B*star v)+star t*C*star u)+star t*D*star v by ring] at h
      simp only [Complex.add_re] at h
      simp only [y, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero]
      simpa only [add_assoc] using h
    · have h := contraction_modulus_budget hX s t u v hs ht hu hv ha hb hc hd
      apply (le_div_iff₀ hp0).2
      simp [r, Fin.sum_univ_succ]
      nlinarith only [h]
    · simp [e, Fin.sum_univ_succ]
      linarith only [aa2,ab2,ac2,ad2,hF]
  · have hrec : (1/4 : ℝ) ≤ 1/(4*p) :=
      (le_div_iff₀ (by positivity)).2 (by linarith)
    linarith

end RTMultiFibre

end

section

namespace RTMultiFibre

open Matrix
open scoped Matrix ComplexOrder BigOperators
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Recovery.PrincipalTrianglePhase

/-- The four cross-fibre coefficient errors in the actual paired action
consume at most twice the squared native diamond distance. -/
theorem native_frobenius_budget
    {a b F e₁ e₂ : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype e₁] [Fintype e₂]
    (first second : QuantumChannel a (b × b))
    (V : Matrix (b × e₁) a ℂ) (W : Matrix (b × e₂) a ℂ)
    (pair : ∀ X, NativeDiamond.matrixAction first X =
      RTDiamond.dilationAction (RTDiamond.pairedDilation V W) X)
    (f : a → b) (pick : F × Fin 2 ↪ a) (label : F → b)
    (byFibre : ∀ p : F × Fin 2, f (pick p) = label p.1)
    (i j : F)
    (target : ∀ u v : Fin 2, NativeDiamond.matrixAction second
      (Matrix.single (pick (i,u)) (pick (j,v)) 1)
      (label i,label i) (label j,label j) = 1/2) :
    let G := (RTDiamond.forwardGram f V).submatrix pick pick
    let H := (RTDiamond.forwardGram f W).submatrix pick pick
    (∑ u : Fin 2, ∑ v : Fin 2, ‖(1/2 : ℂ) - G (i,u) (j,v)*H (i,u) (j,v)‖^2) ≤
      2 * (diamondDistance first second)^2 := by
  let G := (RTDiamond.forwardGram f V).submatrix pick pick
  let H := (RTDiamond.forwardGram f W).submatrix pick pick
  let emb (k : F) : Fin 2 ↪ a := ⟨fun t => pick (k,t), fun _ _ h =>
    congrArg Prod.snd (pick.injective h)⟩
  have h := matrixUnit_two_row_square_le first second (fun u => pick (i,u)) (emb j)
    (label i,label i) (label j,label j)
  have entry (u v : Fin 2) :
      ‖((NativeDiamond.matrixAction first - NativeDiamond.matrixAction second)
        (Matrix.single (pick (i,u)) (emb j v) 1)) (label i,label i) (label j,label j)‖ =
      ‖(1/2 : ℂ) - G (i,u) (j,v)*H (i,u) (j,v)‖ := by
    change ‖NativeDiamond.matrixAction first (Matrix.single (pick (i,u)) (pick (j,v)) 1)
        (label i,label i) (label j,label j) -
      NativeDiamond.matrixAction second (Matrix.single (pick (i,u)) (pick (j,v)) 1)
        (label i,label i) (label j,label j)‖ = _
    have actual : NativeDiamond.matrixAction first (Matrix.single (pick (i,u)) (pick (j,v)) 1)
        (label i,label i) (label j,label j) = star (G (i,u) (j,v)*H (i,u) (j,v)) := by
      rw [pair]
      simpa only [byFibre, G, H, Matrix.submatrix_apply] using
        RTDiamond.paired_channel_coefficient f V W (pick (i,u)) (pick (j,v))
    rw [actual, target]
    have he : star (G (i,u) (j,v)*H (i,u) (j,v) - (1/2 : ℂ)) =
        star (G (i,u) (j,v)*H (i,u) (j,v)) - 1/2 := by rw [star_sub]; norm_num
    rw [← he, norm_star, norm_sub_rev]
  change (∑ u : Fin 2, ∑ v : Fin 2, ‖(1/2 : ℂ) - G (i,u) (j,v)*H (i,u) (j,v)‖^2) ≤ _
  simpa only [entry] using h

end RTMultiFibre

end

section

namespace RTMultiFibre

open Matrix
open scoped Matrix ComplexOrder BigOperators
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Recovery.PrincipalTrianglePhase
open D5.S3.Quantum.Recovery.PrincipalPlaquettePhaseDiamond

private theorem native_witness
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (first second : QuantumChannel a b) (i j : a) (p q : b) (x y : ℂ)
    (actual : NativeDiamond.matrixAction first (Matrix.single i j 1) p q = star (x*y))
    (target : NativeDiamond.matrixAction second (Matrix.single i j 1) p q = 1/2) :
    ‖(1/2 : ℂ)-x*y‖ ≤ diamondDistance first second := by
  have hz := NativeDiamond.matrixUnit_le_diamondDistance first second i j p q
  change ‖NativeDiamond.matrixAction first (Matrix.single i j 1) p q -
    NativeDiamond.matrixAction second (Matrix.single i j 1) p q‖ ≤ _ at hz
  rw [actual, target] at hz
  have he : star (x*y-(1/2 : ℂ)) = star (x*y)-1/2 := by rw [star_sub]; norm_num
  rwa [← he, norm_star, norm_sub_rev] at hz


/-- Stronger one-party phase lower bound for native paired channels.
The Frobenius estimate is proved from tagged-state witnesses for full
coefficient rows, so no calibration or quotient assumption is needed. -/
theorem paired_improved_one_party_native_diamond
    {a b F e₁ e₂ : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype F] [DecidableEq F] [Fintype e₁] [Fintype e₂]
    (first second : QuantumChannel a (b × b))
    (V : Matrix (b × e₁) a ℂ) (W : Matrix (b × e₂) a ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (pair : ∀ X, NativeDiamond.matrixAction first X =
      RTDiamond.dilationAction (RTDiamond.pairedDilation V W) X)
    (f : a → b) (pick : F × Fin 2 ↪ a) (label : F → b)
    (byFibre : ∀ p : F × Fin 2, f (pick p) = label p.1)
    (i j : F) (hij : i ≠ j)
    (target : ∀ u v : Fin 2, NativeDiamond.matrixAction second
      (Matrix.single (pick (i,u)) (pick (j,v)) 1)
      (label i,label i) (label j,label j) = 1/2) :
    let G := (RTDiamond.forwardGram f V).submatrix pick pick
    let θ := plaquetteArg (G (i,0) (j,0)) (G (i,0) (j,1)) (G (i,1) (j,0)) (G (i,1) (j,1))
    let p := Real.cos (θ/4)
    (12/11)*(p/2-1/(4*p)) ≤ diamondDistance first second := by
  let G := (RTDiamond.forwardGram f V).submatrix pick pick
  let H := (RTDiamond.forwardGram f W).submatrix pick pick
  have hG : G.PosSemidef := (RTDiamond.forwardGram_psd f V).submatrix pick
  have hH : H.PosSemidef := (RTDiamond.forwardGram_psd f W).submatrix pick
  let emb (k : F) : Fin 2 ↪ a := ⟨fun t => pick (k,t), fun _ _ h =>
    congrArg Prod.snd (pick.injective h)⟩
  have dG (k : F) : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock G k).PosSemidef :=
    RTDiamond.forward_fibre_defect f V hV (emb k) (label k) (fun t => byFibre (k,t))
  have dH (k : F) : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock H k).PosSemidef :=
    RTDiamond.forward_fibre_defect f W hW (emb k) (label k) (fun t => byFibre (k,t))
  have witness (u v : Fin 2) :
      ‖(1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v)‖ ≤ diamondDistance first second := by
    apply native_witness first second (pick (i,u)) (pick (j,v))
      (label i,label i) (label j,label j) _ _ _ (target u v)
    rw [pair]
    simpa only [byFibre, G, H, Matrix.submatrix_apply] using
      RTDiamond.paired_channel_coefficient f V W (pick (i,u)) (pick (j,v))
  have hv := native_frobenius_budget first second V W pair f pick label byFibre i j target
  change (∑ u : Fin 2, ∑ v : Fin 2, ‖(1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v)‖^2) ≤ _ at hv
  simp only [Fin.sum_univ_two, add_assoc] at hv
  apply improved_plaquette_of_frobenius (native_cross_contraction G hG dG hij)
    (native_cross_contraction H hH dH hij)
    (witness 0 0) (witness 0 1) (witness 1 0) (witness 1 1)
  simpa only [add_assoc] using hv


end RTMultiFibre

end

end D5.S3.Quantum.Recovery.PrincipalPlaquetteBlockBudget
