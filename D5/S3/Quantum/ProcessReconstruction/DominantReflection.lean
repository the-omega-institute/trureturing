/- GID: D5/S3/Quantum/ProcessReconstruction/DominantReflection
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/DominantReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An amplified reflection detects an orthogonal output after partial SWAP. -/

import D5.S3.Quantum.ProcessReconstruction.PartialSwap
import D5.S3.Quantum.ProcessReconstruction.UnitarySpectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.Convex.Combination

/-! An amplified reflection detects an orthogonal output after partial SWAP. -/

noncomputable section

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteDiamondDistance

namespace UnitaryReconstruction

universe u
local notation "ℓ²" => EuclideanSpace ℂ
local notation "L" => Matrix.toEuclideanCLM (𝕜 := ℂ)

section Reflection

variable {a : Type u} [Fintype a] [DecidableEq a]

def rankOneReflection (v : ℓ² a) (hv : ‖v‖ = 1) : unitaryGroup a ℂ := by
  let P := vecMulVec v.ofLp (star v.ofLp)
  have hPt : Pᴴ = P := by simp [P, Matrix.conjTranspose_vecMulVec]
  have hPP : P * P = P := by
    unfold P
    rw [Matrix.vecMulVec_mul_vecMulVec, dot_one_of_euclidean_norm_one _ hv, one_smul]
  let R : Matrix a a ℂ := 1 - (2 : ℂ) • P
  have hRt : Rᴴ = R := by simp [R, Matrix.conjTranspose_smul, hPt]
  refine ⟨R, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  change R * Rᴴ = 1
  rw [hRt]
  simp only [R, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hPP]
  module

theorem rankOneReflection_hermitian (v : ℓ² a) (hv : ‖v‖ = 1) :
    (rankOneReflection v hv).val.IsHermitian := by
  change (1 - (2 : ℂ) • vecMulVec v.ofLp (star v.ofLp))ᴴ =
    1 - (2 : ℂ) • vecMulVec v.ofLp (star v.ofLp)
  simp [Matrix.conjTranspose_vecMulVec, Matrix.conjTranspose_smul]

theorem rankOneReflection_apply (v : ℓ² a) (hv : ‖v‖ = 1) (x : ℓ² a) :
    L (rankOneReflection v hv).val x = x - (2 * ⟪v, x⟫_ℂ) • v := by
  change L (1 - (2 : ℂ) • vecMulVec v.ofLp (star v.ofLp)) x = _
  have h : L (vecMulVec v.ofLp (star v.ofLp)) x = ⟪v, x⟫_ℂ • v := by
    apply (WithLp.ext_iff 2).2
    rw [Matrix.ofLp_toEuclideanCLM, Matrix.vecMulVec_mulVec,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm,
      op_smul_eq_smul, WithLp.ofLp_smul]
  simp only [map_sub, map_one, map_smul, _root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
    h, smul_smul]

end Reflection

section Sites

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (d : ι → Type u)
  [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

local notation:max "P" s:arg => permUnitary (swapOn d s)
local notation:max "B" W:arg => referenceUnitary (System d) W

/-- Conjugating a system observable by the SWAP of every site except `i`
places it on the reference and the retained output. -/
theorem lift_complement_swap (i : ι) (R : unitaryGroup (System d) ℂ) :
    let T := permUnitary (reducedSwap d i)
    let S : unitaryGroup (System d × d i) ℂ :=
      T * ⟨R.val ⊗ₖ (1 : Matrix (d i) (d i) ℂ), kronUnitary R 1⟩ * star T
    liftObservable (splitSite d i) S.val =
      (P (Finset.univ.erase i)).val * (B R).val * (star (P (Finset.univ.erase i))).val := by
  dsimp only
  rw [swap_star]
  ext ⟨x,y⟩ ⟨x',y'⟩
  have hT : star (permUnitary (reducedSwap d i)) = permUnitary (reducedSwap d i) :=
    Subtype.ext (perm_hermitian _ (reducedSwap d i).left_inv)
  rw [hT]
  have hfirst (x y : System d) : (swapOn d (Finset.univ.erase i) (x,y)).1 =
      (splitSite d i).symm ((splitSite d i y).1, x i) := by
    apply (splitSite d i).injective
    apply Prod.ext
    · funext j
      simp [splitSite, Equiv.piSplitAt, swapOn, j.prop]
    · simp [splitSite, Equiv.piSplitAt, swapOn]
  have hsecond (x y : System d) : (swapOn d (Finset.univ.erase i) (x,y)).2 =
      (splitSite d i).symm ((splitSite d i x).1, y i) := by
    apply (splitSite d i).injective
    apply Prod.ext
    · funext j
      simp [splitSite, Equiv.piSplitAt, swapOn, j.prop]
    · simp [splitSite, Equiv.piSplitAt, swapOn]
  have hsym (p : System d × System d) :
      (swapOn d (Finset.univ.erase i)).symm p = swapOn d (Finset.univ.erase i) p := rfl
  change (if (splitSite d i y).1 = (splitSite d i y').1 then
    ((reducedSwap d i).permMatrix ℂ * (R.val ⊗ₖ (1 : Matrix (d i) (d i) ℂ)) *
      (reducedSwap d i).permMatrix ℂ) (x,y i) (x',y' i) else 0) =
    (((swapOn d (Finset.univ.erase i)).permMatrix ℂ *
      ((1 : Matrix (System d) (System d) ℂ) ⊗ₖ R.val)) *
      (swapOn d (Finset.univ.erase i)).permMatrix ℂ) (x,y) (x',y')
  simp only [mul_perm_apply, perm_mul_apply, hsym, Matrix.kroneckerMap_apply,
    hfirst, hsecond, reducedSwap, Equiv.coe_fn_mk, Matrix.one_apply, Equiv.apply_eq_iff_eq,
    Prod.mk.injEq]
  by_cases h₁ : (splitSite d i y).1 = (splitSite d i y').1 <;>
    by_cases h₂ : x i = x' i <;> simp [h₁, h₂]

-- Matrix algebra in the two-copy basis. The unitary factors can then be
-- removed from the norm using the existing operator-norm invariances.
private theorem conjugated_commutator {n : Type u} [Fintype n] [DecidableEq n]
    (Q X R : Matrix n n ℂ) (hQ : Q * Q = 1) :
    (Q * X * Q) * R - R * (Q * X * Q) =
      Q * (X * (Q * R * Q) - (Q * R * Q) * X) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · calc
      Q * X * Q * R = Q * (X * (Q * R * 1)) := by simp [mul_assoc]
      _ = Q * (X * (Q * R * (Q * Q))) := by rw [hQ]
      _ = _ := by simp only [mul_assoc]
  · calc
      R * (Q * X * Q) = 1 * (R * (Q * X * Q)) := by rw [one_mul]
      _ = (Q * Q) * (R * (Q * X * Q)) := by rw [hQ]
      _ = _ := by simp only [mul_assoc]

theorem complement_commutator_le (W R : unitaryGroup (System d) ℂ) (i : ι)
    (hR : R.val.IsHermitian) :
    let A := partiallySwapped d (Finset.univ.erase i) W
    opNorm (A.val * (B R).val - (B R).val * A.val) ≤ localError d i W 1 := by
  let Q := P (Finset.univ.erase i)
  let T := permUnitary (reducedSwap d i)
  let S : unitaryGroup (System d × d i) ℂ :=
    T * ⟨R.val ⊗ₖ (1 : Matrix (d i) (d i) ℂ), kronUnitary R 1⟩ * star T
  let X := B W
  let K := B R
  let J := Q.val * K.val * Q.val
  have hQ : star Q = Q := swap_star d (Finset.univ.erase i)
  have hQ' : Q.valᴴ = Q.val := congrArg Subtype.val hQ
  have hQQ : Q.val * Q.val = 1 := congrArg Subtype.val
    ((congrArg (· * Q) hQ).symm.trans (Unitary.star_mul_self Q))
  have hlift : liftObservable (splitSite d i) S.val = J := by
    have hh := lift_complement_swap d i R
    change liftObservable (splitSite d i) S.val = Q.val * K.val * (star Q).val at hh
    rwa [hQ] at hh
  have hK : K.valᴴ = K.val := by
    change ((1 : Matrix (System d) (System d) ℂ) ⊗ₖ R.val)ᴴ =
      (1 : Matrix (System d) (System d) ℂ) ⊗ₖ R.val
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hR]
  have hJ : (liftObservable (splitSite d i) S.val).IsHermitian := by
    rw [hlift]
    change (Q.val * K.val * Q.val)ᴴ = Q.val * K.val * Q.val
    simp only [Matrix.conjTranspose_mul, hQ', hK, mul_assoc]
  have h := local_observable_bound (splitSite d i) W 1 S hJ
  have hlo : opNorm (X.valᴴ * J * X.val - J) ≤ localError d i W 1 := by
    have hone : (1 : unitaryGroup (System d × System d) ℂ).val =
        (1 : Matrix (System d × System d) (System d × System d) ℂ) := rfl
    simpa only [hlift, referenceUnitary_one, hone, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one, X, localError, siteChannel] using h
  have hX : X.val * X.valᴴ = 1 := Unitary.mul_star_self_of_mem X.prop
  have he : X.val * J - J * X.val = -(X.val * (X.valᴴ * J * X.val - J)) := by
    have hprod : X.val * (X.valᴴ * J * X.val) = J * X.val := calc
      _ = (X.val * X.valᴴ) * J * X.val := by simp only [mul_assoc]
      _ = _ := by rw [hX, one_mul]
    rw [Matrix.mul_sub, hprod, neg_sub]
  have hA : (partiallySwapped d (Finset.univ.erase i) W).val = Q.val * X.val * Q.val := by
    change Q.val * X.val * (star Q).val = _
    rw [hQ]
  dsimp only
  rw [hA, conjugated_commutator _ _ _ hQQ, opNorm_unitary_right, opNorm_unitary_left]
  change opNorm (X.val * J - J * X.val) ≤ _
  rw [he]
  change ‖-(X.val * _)‖ ≤ _
  rw [norm_neg]
  change opNorm (X.val * _) ≤ _
  rwa [opNorm_unitary_left]

variable [∀ i, Nonempty (d i)]

/-- The dominant-site argument tests the reflection in the hyperplane
orthogonal to the zero-overlap vector. -/
theorem no_zero_overlap_of_dominant (W : unitaryGroup (System d) ℂ) (i : ι)
    (hd : 1 ≤ localError d i W 1) (htotal : (∑ j, localError d j W 1) < 2)
    (v : ℓ² (System d)) (hv : ‖v‖ = 1) : ⟪v, L W.val v⟫_ℂ ≠ 0 := by
  classical
  intro hz
  let S := (Finset.univ : Finset ι).erase i
  let e := ∑ j ∈ S, localError d j W 1
  let δ := localError d i W 1
  have he : 0 ≤ e := Finset.sum_nonneg fun j _ => diamondDistance_nonneg' _ _
  have hsum : e + δ = ∑ j, localError d j W 1 :=
    Finset.sum_erase_add _ _ (Finset.mem_univ _)
  have he₁ : e < 1 := by linarith
  have hsmall : δ + e ^ 2 < 2 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos he (show e - 1 ≤ 0 by linarith)]
  let A := partiallySwapped d S W
  let R := rankOneReflection v hv
  let r := Classical.choice (inferInstance : Nonempty (System d))
  let a : ℓ² (System d) := EuclideanSpace.single r 1
  have ha : ‖a‖ = 1 := by simp [a, EuclideanSpace.single, PiLp.norm_single]
  let x := tensorVector a v
  let y := tensorVector a (L W.val v)
  have hx : ‖x‖ = 1 := tensorVector_norm_one ha hv
  have hy : ‖y‖ = 1 := tensorVector_norm_one ha ((unitary_euclidean_norm W v).trans hv)
  have hBx : L (B W).val x = y := by
    change L ((1 : Matrix (System d) (System d) ℂ) ⊗ₖ W.val) (tensorVector a v) = _
    simp only [kron_tensorVector, map_one, one_apply_eq_self, y]
  have hRx : L (B R).val x = -x := by
    change L ((1 : Matrix (System d) (System d) ℂ) ⊗ₖ R.val) (tensorVector a v) = _
    rw [kron_tensorVector, map_one, one_apply_eq_self, show R = rankOneReflection v hv from rfl,
      rankOneReflection_apply]
    have h : ⟪v, v⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hv]
      norm_num
    rw [h, mul_one]
    have hv' : v - (2 : ℂ) • v = -v := by module
    rw [hv']
    apply PiLp.ext
    rintro ⟨j,k⟩
    change a.ofLp j * (-v).ofLp k = (-x).ofLp (j,k)
    simp [x, tensorVector]
  have hRy : L (B R).val y = y := by
    change L ((1 : Matrix (System d) (System d) ℂ) ⊗ₖ R.val)
      (tensorVector a (L W.val v)) = _
    simp only [kron_tensorVector, map_one, one_apply_eq_self,
      show R = rankOneReflection v hv from rfl, rankOneReflection_apply, hz, mul_zero, zero_smul,
      sub_zero, y]
  have hH : (B R).valᴴ = (B R).val := by
    change ((1 : Matrix (System d) (System d) ℂ) ⊗ₖ R.val)ᴴ =
      (1 : Matrix (System d) (System d) ℂ) ⊗ₖ R.val
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, rankOneReflection_hermitian]
  have hdist : ‖y - L A.val x‖ ≤ e := by
    rw [← hBx, norm_sub_rev, ← _root_.sub_apply, ← map_sub]
    exact ((A.val - (B W).val).l2_opNorm_mulVec x).trans
      (by simpa only [hx, mul_one, opNorm] using norm_partial_displacement d W S)
  let K := A.val * (B R).val - (B R).val * A.val
  have hcoeff : ⟪y, L K x⟫_ℂ = -2 * ⟪y, L A.val x⟫_ℂ := by
    have hadj : (L (B R).val).adjoint = L (B R).val := by
      have he : (L (B R).val).adjoint = L (B R).valᴴ := (map_star L _).symm
      rw [he, hH]
    change ⟪y, L (A.val * (B R).val - (B R).val * A.val) x⟫_ℂ = _
    simp only [map_sub, map_mul, mul_apply_eq_comp, _root_.sub_apply,
      hRx, map_neg, inner_sub_right, inner_neg_right]
    rw [← ContinuousLinearMap.adjoint_inner_left (L (B R).val), hadj, hRy]
    ring
  have hupper : ‖⟪y, L K x⟫_ℂ‖ ≤ δ :=
    (norm_inner_le_norm _ _).trans (by
      rw [hy, one_mul]
      exact (K.l2_opNorm_mulVec x).trans (by
        simpa only [hx, mul_one, opNorm] using complement_commutator_le d W R i
          (rankOneReflection_hermitian v hv)))
  rw [hcoeff, norm_mul, show ‖(-2 : ℂ)‖ = 2 by norm_num] at hupper
  have hnorm : ‖L A.val x‖ = 1 := (unitary_euclidean_norm A x).trans hx
  have hsq := (sq_le_sq₀ (norm_nonneg _) he).mpr hdist
  rw [norm_sub_sq (𝕜 := ℂ), hy, hnorm] at hsq
  change 1 ^ 2 - 2 * (⟪y, L A.val x⟫_ℂ).re + 1 ^ 2 ≤ _ at hsq
  linarith [Complex.re_le_norm ⟪y, L A.val x⟫_ℂ]

end Sites


section Spectrum

variable {a : Type u} [Fintype a] [DecidableEq a]

theorem spectrum_unit_eigenvector (W : unitaryGroup a ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ W.val) :
    ∃ v : ℓ² a, ‖v‖ = 1 ∧ L W.val v = z • v := by
  obtain ⟨w, hw, hwz⟩ := spectrum_eigenvector W.val z hz
  let v : ℓ² a := WithLp.toLp 2 w
  have hv : 0 < ‖v‖ := by simpa [v, norm_pos_iff] using hw
  have he : L W.val v = z • v := by
    rw [Matrix.toEuclideanCLM_toLp, hwz, WithLp.toLp_smul]
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩
  · simp [norm_smul, hv.ne']
  · simp only [map_smul, he, smul_comm ((‖v‖⁻¹ : ℝ) : ℂ) z]

private theorem eigenvectors_inner_zero (W : unitaryGroup a ℂ) {z w : ℂ}
    (hz : z ∈ spectrum ℂ W.val) (hzw : z ≠ w) (v u : ℓ² a)
    (hv : L W.val v = z • v) (hu : L W.val u = w • u) :
    ⟪v, u⟫_ℂ = 0 := by
  have hU : L W.val ∈ unitary (ℓ² a →L[ℂ] ℓ² a) :=
    Unitary.map_mem L W.prop
  have h := ContinuousLinearMap.inner_map_map_of_mem_unitary hU v u
  rw [hv, hu, inner_smul_left, inner_smul_right] at h
  have hzz : z * star z = 1 := by
    rw [show z * star z = (‖z‖ : ℂ) ^ 2 from Complex.mul_conj' z,
      spectrum.norm_eq_one_of_unitary W.prop hz]
    norm_num
  have hprod := congrArg (z * ·) h
  change z * (star z * (w * ⟪v, u⟫_ℂ)) = z * ⟪v, u⟫_ℂ at hprod
  rw [← mul_assoc z, hzz, one_mul] at hprod
  exact (mul_eq_zero.mp (show (z - w) * ⟪v, u⟫_ℂ = 0 by
    rw [sub_mul, hprod, sub_self])).resolve_left (sub_ne_zero.mpr hzw)

theorem overlap_of_mem_spectral_hull (W : unitaryGroup a ℂ) (z : ℂ)
    (hz : z ∈ convexHull ℝ (spectrum ℂ W.val)) :
    ∃ v : ℓ² a, ‖v‖ = 1 ∧ ⟪v, L W.val v⟫_ℂ = z := by
  classical
  let s := (Matrix.finite_spectrum W.val).toFinset
  change z ∈ convexHull ℝ (spectrum ℂ W.val) at hz
  rw [← Set.Finite.coe_toFinset (Matrix.finite_spectrum W.val)] at hz
  obtain ⟨p, hp, hsum, hval⟩ := Finset.mem_convexHull'.mp hz
  have hEig (w : ℂ) : ∃ v : ℓ² a, w ∈ s → ‖v‖ = 1 ∧ L W.val v = w • v := by
    by_cases hw : w ∈ s
    · obtain ⟨v, hv, he⟩ := spectrum_unit_eigenvector W
        (by simpa only [s, Set.Finite.mem_toFinset] using hw)
      exact ⟨v, fun _ => ⟨hv, he⟩⟩
    · exact ⟨0, fun h => (hw h).elim⟩
  choose v hv using hEig
  let f (w : ℂ) : ℓ² a := (Real.sqrt (p w) : ℂ) • v w
  have horth {w w' : ℂ} (hw : w ∈ s) (hw' : w' ∈ s) (hne : w ≠ w') :
      ⟪f w, f w'⟫_ℂ = 0 := by
    have hz : w ∈ spectrum ℂ W.val := by simpa only [s, Set.Finite.mem_toFinset] using hw
    have he := eigenvectors_inner_zero W hz hne _ _ (hv w hw).2 (hv w' hw').2
    simp [f, he]
  have hdiag {w : ℂ} (hw : w ∈ s) : ⟪f w, f w⟫_ℂ = (p w : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    have hn : ‖f w‖ = Real.sqrt (p w) := by
      simp [f, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        (hv w hw).1]
    have hh := Real.sq_sqrt (hp w hw)
    rw [hn]
    exact (Complex.ofReal_pow _ _).symm.trans (congrArg Complex.ofReal hh)
  have hfe {w : ℂ} (hw : w ∈ s) : L W.val (f w) = w • f w := by
    simp only [f, map_smul, (hv w hw).2, smul_comm (Real.sqrt (p w) : ℂ) w]
  let x := ∑ w ∈ s, f w
  have hinner (w : ℂ) (hw : w ∈ s) : ⟪f w, x⟫_ℂ = (p w : ℂ) := by
    rw [show x = ∑ w' ∈ s, f w' from rfl, inner_sum]
    rw [Finset.sum_eq_single_of_mem w hw (fun w' hw' hne => horth hw hw' hne.symm)]
    exact hdiag hw
  have hxx : ⟪x, x⟫_ℂ = 1 := by
    rw [show x = ∑ w ∈ s, f w from rfl, sum_inner]
    rw [← Complex.ofReal_one, ← hsum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun w hw => hinner w hw
  have hx : ‖x‖ = 1 := by
    apply euclidean_norm_one_of_dot x.ofLp
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    exact hxx
  refine ⟨x, hx, ?_⟩
  change ⟪x, L W.val (∑ w ∈ s, f w)⟫_ℂ = z
  rw [map_sum, inner_sum, ← hval]
  apply Finset.sum_congr rfl
  intro w hw
  have hrev : ⟪x, f w⟫_ℂ = (p w : ℂ) := by
    rw [← inner_conj_symm, hinner w hw, Complex.conj_ofReal]
  rw [hfe hw, inner_smul_right, hrev, mul_comm]
  rfl

end Spectrum

end UnitaryReconstruction
