/- GID: D5/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PrincipalPlaquetteBlockBudget
   mirror-E: none(waiver:principal-plaquette-block-budget)
   anchors: []
   utility: none
   digest: Coherent rows strengthen the one-party plaquette obstruction for native paired channels. -/


import D5.S3.Quantum.Recovery.PrincipalPlaquetteGaugeBudget
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

namespace RTMultiFibre

open Matrix
open scoped Matrix ComplexOrder BigOperators
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Recovery.PrincipalTrianglePhase

open NativeDiamond (matrixAction)

private def flatAmp : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

private theorem flatAmp_star : star flatAmp = flatAmp := by
  simp [flatAmp]

private theorem flatAmp_mul : flatAmp * flatAmp = 1/2 := by
  rw [flatAmp, ← Complex.ofReal_mul]
  have hs : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hh : (Real.sqrt (2:ℝ) / 2) * (Real.sqrt (2:ℝ) / 2) = 1/2 := by nlinarith
  rw [hh]
  norm_num

/-- A two-coordinate phase with first coefficient fixed to one. -/
def phase (s : ℂ) (i : Fin 2) : ℂ := if i = 0 then 1 else s

private theorem phase_one (i : Fin 2) : phase 1 i = 1 := by simp [phase]

private def flatTwo {a : Type*} [DecidableEq a] (i j : a) (s : ℂ) : a → ℂ :=
  Pi.single i flatAmp + Pi.single j (flatAmp*s)

private theorem flatTwo_norm {a : Type*} [Fintype a] [DecidableEq a]
    {i j : a} (h : i ≠ j) (s : ℂ) (hs : star s*s = 1) :
    star (flatTwo i j s) ⬝ᵥ flatTwo i j s = 1 := by
  simp only [flatTwo, dotProduct_add, dotProduct_single, Pi.star_apply, Pi.add_apply,
    Pi.single_apply, eq_self, ite_true, h, h.symm, ite_false, zero_add, add_zero,
    flatAmp_star, flatAmp_mul, star_mul]
  rw [show star s*flatAmp*(flatAmp*s) = (flatAmp*flatAmp)*(star s*s) by ring,
    flatAmp_mul, hs]
  norm_num

private theorem flatTwo_matrix {a : Type*} [DecidableEq a]
    (i j : Fin 2 → a) (s t : ℂ) :
    Matrix.vecMulVec (flatTwo (i 0) (i 1) s) (star (flatTwo (j 0) (j 1) t)) =
      (1/2 : ℂ) • (∑ u : Fin 2, ∑ v : Fin 2,
        (phase s u * star (phase t v)) • Matrix.single (i u) (j v) (1:ℂ)) := by
  have hcell (x y : a) (r q : ℂ) :
      Matrix.vecMulVec (Pi.single x (flatAmp*r)) (Pi.single y (flatAmp*q)) =
        (1/2 : ℂ) • ((r*q) • Matrix.single x y (1:ℂ)) := by
    ext k l
    by_cases hk : k = x
    · subst k
      by_cases hl : l = y
      · subst l
        simp [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
        rw [show flatAmp*r*(flatAmp*q) = (flatAmp*flatAmp)*(r*q) by ring, flatAmp_mul]
        ring
      · have hl' : y ≠ l := Ne.symm hl
        simp [Matrix.vecMulVec_apply, Matrix.smul_apply, hl, hl']
    · have hk' : x ≠ k := Ne.symm hk
      simp [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.single_apply, hk, hk']
  have hcell0 (x y : a) (r : ℂ) :
      Matrix.vecMulVec (Pi.single x (flatAmp*r)) (Pi.single y ((1:ℂ)*flatAmp)) =
        (1/2 : ℂ) • ((r*1) • Matrix.single x y (1:ℂ)) := by
    simpa only [one_mul, mul_one] using hcell x y r 1
  have h (x : a) : (Pi.single x flatAmp : a → ℂ) = Pi.single x (flatAmp*(1:ℂ)) := by simp
  simp only [flatTwo, h, Fin.sum_univ_two, star_add, Pi.star_single, flatAmp_star,
    Matrix.add_vecMulVec, Matrix.vecMulVec_add, smul_add, star_mul, star_one]
  simp only [show ∀ z : ℂ, star z*flatAmp = flatAmp*star z by intro; ring]
  simp only [hcell, hcell0, phase, ite_true, show (1:Fin 2) ≠ 0 by decide, ite_false, star_one]
  abel

/-- Four signed (or unit-phase-weighted) native matrix-unit coefficients
consume one full rank-one diamond test, with the explicit factor two. -/
theorem flat_phase_coeff_sum_norm
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (first second : QuantumChannel a b) (i j : Fin 2 ↪ a)
    (s t : ℂ) (hs : star s*s = 1) (ht : star t*t = 1) (p q : b) :
    ‖∑ u : Fin 2, ∑ v : Fin 2, (phase s u * star (phase t v)) *
      ((matrixAction first - matrixAction second) (Matrix.single (i u) (j v) 1)) p q‖ ≤
      2 * diamondDistance first second := by
  have hi : i 0 ≠ i 1 := fun h => (by decide : (0:Fin 2) ≠ 1) (i.injective h)
  have hj : j 0 ≠ j 1 := fun h => (by decide : (0:Fin 2) ≠ 1) (j.injective h)
  have h := vectorCoefficient_le_diamondDistance first second
    (flatTwo (i 0) (i 1) s) (flatTwo (j 0) (j 1) t)
    (flatTwo_norm hi s hs) (flatTwo_norm hj t ht) p q
  rw [flatTwo_matrix i j, map_smul, map_sum] at h
  simp only [map_sum, Matrix.sum_apply, map_smul, Matrix.smul_apply, smul_eq_mul, Complex.norm_mul] at h
  have hhalf : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num [norm_div]
  rw [hhalf] at h
  linarith only [h]

private theorem phase_star (s : ℂ) (u : Fin 2) : phase (star s) u = star (phase s u) := by
  by_cases hu : u=0 <;> simp [phase, hu]

/-- The same signed/phase witness directly on the actual paired forward
Grams. The conjugate input weights account for the original coefficient
orientation. No calibration or Gram completion is used. -/
theorem native_flat_phase_error_norm
    {a b F e₁ e₂ : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype e₁] [Fintype e₂]
    (first second : QuantumChannel a (b × b))
    (V : Matrix (b × e₁) a ℂ) (W : Matrix (b × e₂) a ℂ)
    (pair : ∀ X, matrixAction first X =
      RTDiamond.dilationAction (RTDiamond.pairedDilation V W) X)
    (f : a → b) (pick : F × Fin 2 ↪ a) (label : F → b)
    (byFibre : ∀ p : F × Fin 2, f (pick p) = label p.1)
    (i j : F) (s t : ℂ) (hs : star s*s = 1) (ht : star t*t = 1)
    (target : ∀ u v : Fin 2, matrixAction second
      (Matrix.single (pick (i,u)) (pick (j,v)) 1)
      (label i,label i) (label j,label j) = 1/2) :
    let G := (RTDiamond.forwardGram f V).submatrix pick pick
    let H := (RTDiamond.forwardGram f W).submatrix pick pick
    ‖∑ u : Fin 2, ∑ v : Fin 2, (phase s u * star (phase t v)) *
        ((1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v))‖ ≤
      2 * diamondDistance first second := by
  let G := (RTDiamond.forwardGram f V).submatrix pick pick
  let H := (RTDiamond.forwardGram f W).submatrix pick pick
  let emb (k : F) : Fin 2 ↪ a := ⟨fun t => pick (k,t), fun _ _ h =>
    congrArg Prod.snd (pick.injective h)⟩
  let E (u v : Fin 2) : ℂ := (1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v)
  have hs' : star (star s)*star s = 1 := by simpa [mul_comm] using hs
  have ht' : star (star t)*star t = 1 := by simpa [mul_comm] using ht
  have h := flat_phase_coeff_sum_norm first second (emb i) (emb j)
    (star s) (star t) hs' ht' (label i,label i) (label j,label j)
  have entry (u v : Fin 2) :
      ((matrixAction first - matrixAction second) (Matrix.single (emb i u) (emb j v) 1))
        (label i,label i) (label j,label j) = -star (E u v) := by
    change matrixAction first (Matrix.single (pick (i,u)) (pick (j,v)) 1)
        (label i,label i) (label j,label j) -
      matrixAction second (Matrix.single (pick (i,u)) (pick (j,v)) 1)
        (label i,label i) (label j,label j) = _
    have actual : matrixAction first (Matrix.single (pick (i,u)) (pick (j,v)) 1)
        (label i,label i) (label j,label j) = star (G (i,u) (j,v)*H (i,u) (j,v)) := by
      rw [pair]
      simpa only [byFibre, G, H, Matrix.submatrix_apply] using
        RTDiamond.paired_channel_coefficient f V W (pick (i,u)) (pick (j,v))
    rw [actual,target]
    have hh : star ((1/2 : ℂ)) = (1/2 : ℂ) := by norm_num
    simp only [E, star_sub, hh, neg_sub]
  simp_rw [entry, phase_star, star_star, mul_neg] at h
  have hh : (∑ u : Fin 2, ∑ v : Fin 2,
      star (phase s u) * phase t v * star (E u v)) =
      star (∑ u : Fin 2, ∑ v : Fin 2, (phase s u * star (phase t v)) * E u v) := by
    simp only [star_sum, star_mul, star_star]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  simpa only [Finset.sum_neg_distrib, hh, norm_neg, norm_star] using h

/-- A coherent rank-one test with both inputs flat on their own
two-coordinate supports bounds the complete block sum, not just a row. -/
theorem flat_coeff_sum_norm
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (first second : QuantumChannel a b) (i j : Fin 2 ↪ a) (p q : b) :
    ‖∑ u : Fin 2, ∑ v : Fin 2,
      ((matrixAction first - matrixAction second) (Matrix.single (i u) (j v) 1)) p q‖ ≤
      2 * diamondDistance first second := by
  simpa only [phase_one, star_one, one_mul] using
    flat_phase_coeff_sum_norm first second i j 1 1 (by norm_num) (by norm_num) p q

/-- Actual paired-dilation flat coherent sum witness on one selected
fibre pair, in the original unhalved diamond-distance convention. -/
theorem native_flat_coherent_sum
    {a b F e₁ e₂ : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype e₁] [Fintype e₂]
    (first second : QuantumChannel a (b × b))
    (V : Matrix (b × e₁) a ℂ) (W : Matrix (b × e₂) a ℂ)
    (pair : ∀ X, matrixAction first X =
      RTDiamond.dilationAction (RTDiamond.pairedDilation V W) X)
    (f : a → b) (pick : F × Fin 2 ↪ a) (label : F → b)
    (byFibre : ∀ p : F × Fin 2, f (pick p) = label p.1)
    (i j : F)
    (target : ∀ u v : Fin 2, matrixAction second
      (Matrix.single (pick (i,u)) (pick (j,v)) 1)
      (label i,label i) (label j,label j) = 1/2) :
    let G := (RTDiamond.forwardGram f V).submatrix pick pick
    let H := (RTDiamond.forwardGram f W).submatrix pick pick
    (∑ u : Fin 2, ∑ v : Fin 2, ((1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v)).re) ≤
      2 * diamondDistance first second := by
  let G := (RTDiamond.forwardGram f V).submatrix pick pick
  let H := (RTDiamond.forwardGram f W).submatrix pick pick
  let emb (k : F) : Fin 2 ↪ a := ⟨fun t => pick (k,t), fun _ _ h =>
    congrArg Prod.snd (pick.injective h)⟩
  let L (u v : Fin 2) : ℂ :=
    ((matrixAction first - matrixAction second) (Matrix.single (emb i u) (emb j v) 1))
      (label i,label i) (label j,label j)
  have h : ‖∑ u : Fin 2, ∑ v : Fin 2, L u v‖ ≤ 2 * diamondDistance first second :=
    flat_coeff_sum_norm first second (emb i) (emb j) (label i,label i) (label j,label j)
  have entry (u v : Fin 2) :
      ((1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v)).re = -(L u v).re := by
    change ((1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v)).re =
      -(matrixAction first (Matrix.single (pick (i,u)) (pick (j,v)) 1)
        (label i,label i) (label j,label j) -
      matrixAction second (Matrix.single (pick (i,u)) (pick (j,v)) 1)
        (label i,label i) (label j,label j)).re
    have actual : matrixAction first (Matrix.single (pick (i,u)) (pick (j,v)) 1)
        (label i,label i) (label j,label j) = star (G (i,u) (j,v)*H (i,u) (j,v)) := by
      rw [pair]
      simpa only [byFibre, G, H, Matrix.submatrix_apply] using
        RTDiamond.paired_channel_coefficient f V W (pick (i,u)) (pick (j,v))
    rw [actual,target]
    simp only [Complex.sub_re, Complex.star_def, Complex.conj_re]
    ring
  change (∑ u : Fin 2, ∑ v : Fin 2,
    ((1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v)).re) ≤ _
  simp_rw [entry, Finset.sum_neg_distrib]
  have hneg := (Complex.re_le_norm (-(∑ u : Fin 2, ∑ v : Fin 2, L u v))).trans
    (by simpa only [norm_neg] using h)
  simpa only [Complex.neg_re, Complex.re_sum] using hneg

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
    Real.sqrt 2 * (p/2-1/(4*p)) ≤ diamondDistance first second := by
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
  apply PrincipalPlaquetteGaugeBudget.RTMultiFibre.improved_plaquette_of_frobenius (native_cross_contraction G hG dG hij)
    (native_cross_contraction H hH dH hij)
    (witness 0 0) (witness 0 1) (witness 1 0) (witness 1 1)
  simpa only [add_assoc] using hv

/-- A single zero-phase plaquette forces a stronger absolute lower bound
in the original native diamond distance, even with leakage. -/
theorem paired_sharp_zero_plaquette_native_diamond
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
    (zeroPhase : let G := (RTDiamond.forwardGram f V).submatrix pick pick
      plaquetteArg (G (i,0) (j,0)) (G (i,0) (j,1))
        (G (i,1) (j,0)) (G (i,1) (j,1)) = 0)
    (target : ∀ u v : Fin 2, NativeDiamond.matrixAction second
      (Matrix.single (pick (i,u)) (pick (j,v)) 1)
      (label i,label i) (label j,label j) = 1/2) :
    Real.sqrt 2 - 1 ≤ diamondDistance first second := by
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
  have hs := native_flat_coherent_sum first second V W pair f pick label byFibre i j target
  change (∑ u : Fin 2, ∑ v : Fin 2,
    ((1 / 2 : ℂ) - G (i,u) (j,v) * H (i,u) (j,v)).re) ≤ _ at hs
  simp only [Fin.sum_univ_two] at hs
  exact PrincipalPlaquetteGaugeBudget.RTMultiFibre.sharp_zero_plaquette_of_coherent (native_cross_contraction G hG dG hij)
    (native_cross_contraction H hH dH hij) zeroPhase
    (witness 0 0) (witness 0 1) (witness 1 0) (witness 1 1)
    (by simpa only [add_assoc] using hv) hs

/-- One first-party phase in the specified sector forces a strict
quarter gap in the native paired-channel distance. -/
theorem paired_quarter_plaquette_native_diamond
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
    (phaseCutoff : let G := (RTDiamond.forwardGram f V).submatrix pick pick
      899228/1000000 ≤ Real.cos (plaquetteArg (G (i,0) (j,0)) (G (i,0) (j,1))
        (G (i,1) (j,0)) (G (i,1) (j,1)) / 4))
    (target : ∀ u v : Fin 2, NativeDiamond.matrixAction second
      (Matrix.single (pick (i,u)) (pick (j,v)) 1)
      (label i,label i) (label j,label j) = 1/2) :
    1/4 < diamondDistance first second := by
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
  let E (u v : Fin 2) : ℂ := (1/2 : ℂ)-G (i,u) (j,v)*H (i,u) (j,v)
  have hs : ‖E 0 0 + E 0 1 + (E 1 0 + E 1 1)‖ ≤ 2 * diamondDistance first second := by
    have h := native_flat_phase_error_norm first second V W pair f pick label byFibre i j
      1 1 (by norm_num) (by norm_num) target
    simpa only [Fin.sum_univ_two, phase_one, star_one, one_mul] using h
  have hsign : ‖E 0 0 - E 0 1 - E 1 0 + E 1 1‖ ≤ 2 * diamondDistance first second := by
    have h := native_flat_phase_error_norm first second V W pair f pick label byFibre i j
      (-1) (-1) (by simp) (by simp) target
    have hh : ‖E 0 0 + -E 0 1 + (-E 1 0 + E 1 1)‖ ≤ 2 * diamondDistance first second := by
      simpa only [Fin.sum_univ_two, phase, ite_true, show (1 : Fin 2) ≠ 0 by decide,
        ite_false, star_one, star_neg, one_mul, mul_one, neg_mul, neg_neg] using h
    convert hh using 2 <;> ring
  exact PrincipalPlaquetteGaugeBudget.RTMultiFibre.quarter_plaquette_of_signed_coherent (native_cross_contraction G hG dG hij)
    (native_cross_contraction H hH dH hij) phaseCutoff
    (witness 0 0) (witness 0 1) (witness 1 0) (witness 1 1)
    (by simpa only [add_assoc] using hv) hs hsign


end RTMultiFibre

end

end D5.S3.Quantum.Recovery.PrincipalPlaquetteBlockBudget
