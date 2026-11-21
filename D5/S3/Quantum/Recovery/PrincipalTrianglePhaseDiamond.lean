/- GID: D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A tagged pure input turns the phase bound into a native diamond-distance bound. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Recovery.PrincipalTrianglePhaseBound
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.NormNum

/-! A native density-state witness connects the geometric bound to stabilized channel error. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Recovery.PrincipalTrianglePhase

open scoped Matrix
open Matrix
open ComplexConjugate
namespace RTTraceSwap

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def swapU (p q : n) (a s : ℂ) : Matrix n n ℂ :=
  fun i j => if Equiv.swap p q i = j then
    (if i = p then a else if i = q then star a else s) else 0

theorem swapU_unitary (p q : n) (a s : ℂ)
    (ha : star a * a = 1) (hs : star s * s = 1) :
    (swapU p q a s)ᴴ * swapU p q a s = 1 := by
  classical
  ext i j
  let e := Equiv.swap p q
  let w : n → ℂ := fun k => if k = p then a else if k = q then star a else s
  have hw (k : n) : star (w k) * w k = 1 := by
    dsimp [w]
    split_ifs <;> simp_all [mul_comm]
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.conjTranspose_apply]
    change (∑ k, star (if e k = i then w k else 0) *
      (if e k = i then w k else 0)) = _
    rw [Finset.sum_eq_single (e.symm i)]
    · simpa only [Equiv.apply_symm_apply, ite_eq_left, eq_self_iff_true] using hw (e.symm i)
    · intro k _ hk
      have hh : e k ≠ i := fun h => hk (e.injective (h.trans (e.apply_symm_apply i).symm))
      simp [hh]
    · simp
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro k _
    simp only [Matrix.conjTranspose_apply, swapU]
    by_cases hki : Equiv.swap p q k = i
    · simp [hki, hij]
    · simp [hki]

omit [Fintype n] in
theorem swapU_cancel (p q : n) (hpq : p ≠ q) (a : ℂ) :
    swapU p q a 1 + swapU p q a (-1) =
      single p q a + single q p (star a) + (single p q a + single q p (star a)) := by
  ext i j
  change swapU p q a 1 i j + swapU p q a (-1) i j =
    ((single p q a) i j + (single q p (star a)) i j) +
    ((single p q a) i j + (single q p (star a)) i j)
  by_cases hpi : i = p
  · subst i
    simp [swapU, Matrix.single, hpq.symm]
  · by_cases hqi : i = q
    · subst i
      simp [swapU, Matrix.single, hpi, hpq]
    · simp [swapU, Matrix.single, hpi, hqi, Ne.symm hpi, Ne.symm hqi]
      split_ifs <;> simp

noncomputable def unitPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem unitPhase_norm (z : ℂ) : star (unitPhase z) * unitPhase z = 1 := by
  by_cases hz : z = 0
  · simp [unitPhase,hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    simp only [unitPhase, ite_eq_right hz, map_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm]
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
    push_cast
    rw [pow_two, div_self (mul_ne_zero hn hn)]

theorem phase_pair (z : ℂ) : unitPhase z * star z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    simp only [unitPhase, ite_eq_right hz, div_mul_eq_mul_div, Complex.star_def, Complex.mul_conj,
      ← Complex.sq_norm]
    push_cast
    rw [pow_two, mul_div_cancel_right₀ _ hn]

theorem trace_cancellation (X : Matrix n n ℂ) (p q : n) (hpq : p ≠ q)
    (hh : X q p = star (X p q)) :
    let a := unitPhase (X p q)
    ((swapU p q a 1 * X).trace).re + ((swapU p q a (-1) * X).trace).re =
      4 * ‖X p q‖ := by
  dsimp only
  rw [← Complex.add_re, ← Matrix.trace_add, ← add_mul, swapU_cancel _ _ hpq, add_mul, add_mul,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul]
  have h₁ : unitPhase (X p q) * X q p = (‖X p q‖ : ℂ) := hh ▸ phase_pair (X p q)
  have h₂ : star (unitPhase (X p q)) * X p q = (‖X p q‖ : ℂ) := by
    have h := congrArg star (phase_pair (X p q))
    simpa [Complex.star_def] using h
  change ((unitPhase (X p q) * X q p + star (unitPhase (X p q)) * X p q) +
    (unitPhase (X p q) * X q p + star (unitPhase (X p q)) * X p q)).re = _
  rw [h₁, h₂]
  simp
  ring

/-- A trace-norm dual upper bound on unitary traces yields the sharp factor 2. -/
theorem twice_offdiag_le_of_dual (X : Matrix n n ℂ) (p q : n) (hpq : p ≠ q)
    (hh : X q p = star (X p q)) (T : ℝ)
    (hdual : ∀ U : Matrix n n ℂ, Uᴴ * U = 1 → ((U * X).trace).re ≤ T) :
    2 * ‖X p q‖ ≤ T := by
  let a := unitPhase (X p q)
  have hpos := hdual (swapU p q a 1) (swapU_unitary p q a 1 (unitPhase_norm _) (by simp))
  have hneg := hdual (swapU p q a (-1)) (swapU_unitary p q a (-1) (unitPhase_norm _) (by simp))
  have h := trace_cancellation X p q hpq hh
  change ((swapU p q a 1 * X).trace).re + ((swapU p q a (-1) * X).trace).re = _ at h
  linarith

/-- This premise is exactly the output of the native trace norm's dual theorem. -/
theorem twice_offdiag_le_of_dual_max (X : Matrix n n ℂ) (p q : n) (hpq : p ≠ q)
    (hh : X q p = star (X p q)) (T : ℝ)
    (hdual : IsGreatest {x : ℝ | ∃ U : Matrix.unitaryGroup n ℂ,
      Complex.re ((U.val * X).trace) = x} T) :
    2 * ‖X p q‖ ≤ T := by
  apply twice_offdiag_le_of_dual X p q hpq hh T
  intro U hu
  apply hdual.2
  exact ⟨⟨U, Matrix.mem_unitaryGroup_iff'.2 (by simpa [Matrix.star_eq_conjTranspose] using hu)⟩, rfl⟩

end RTTraceSwap

namespace RTDiamond
open scoped Matrix ComplexOrder BigOperators
variable {ι ο : Type*} [Fintype ι] [DecidableEq ι]

/-- The unnormalized vector |0,i⟩+|1,j⟩. -/
def taggedVec (i j : ι) : Fin 2 × ι → ℂ := fun p =>
  if p = (0,i) ∨ p = (1,j) then 1 else 0

/-- The pure state formed from the normalized two-tag superposition. -/
noncomputable def taggedDensity (i j : ι) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
  (1/2 : ℂ) • Matrix.vecMulVec (taggedVec i j) (star (taggedVec i j))

theorem taggedDensity_psd (i j : ι) : (taggedDensity i j).PosSemidef := by
  apply (Matrix.posSemidef_vecMulVec_self_star (taggedVec i j)).smul
  exact Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩

omit [Fintype ι] in
private theorem taggedVec_zero (i j q : ι) : taggedVec i j (0,q) = if q = i then 1 else 0 := by
  simp [taggedVec, show (0 : Fin 2) ≠ 1 by decide]

omit [Fintype ι] in
private theorem taggedVec_one (i j q : ι) : taggedVec i j (1,q) = if q = j then 1 else 0 := by
  simp [taggedVec, show (1 : Fin 2) ≠ 0 by decide]

theorem taggedDensity_trace (i j : ι) : (taggedDensity i j).trace = 1 := by
  unfold taggedDensity Matrix.trace
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.diag_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Pi.star_apply,
    taggedVec_zero, taggedVec_one]
  have norm_term (k : ι) (q : ι) :
      (1/2 : ℂ) * ((if q = k then 1 else 0) * star (if q = k then 1 else 0)) =
      if q = k then 1/2 else 0 := by split <;> simp_all
  simp_rw [norm_term]
  simp
  norm_num

omit [Fintype ι] in
/-- The (0,1) reference block is half the original matrix unit. -/
theorem taggedDensity_crossBlock (i j : ι) :
    (taggedDensity i j).submatrix (fun a => (0,a)) (fun b => (1,b)) =
      (1/2 : ℂ) • Matrix.single i j 1 := by
  ext a b
  simp only [Matrix.submatrix_apply, taggedDensity, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply, Pi.star_apply, taggedVec_zero, taggedVec_one,
    Matrix.single_apply]
  by_cases ha : i = a
  · subst a
    by_cases hb : j = b
    · subst b
      simp
    · simp [hb, Ne.symm hb]
  · by_cases hb : j = b
    · subst b
      simp [ha, Ne.symm ha]
    · simp [ha, hb, Ne.symm ha]

/-- The matrix of applying `id ⊗ Φ`, in explicit reference blocks. -/
def amplify (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (X : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) : Matrix (Fin 2 × ο) (Fin 2 × ο) ℂ :=
  fun p q => Φ (X.submatrix (fun a => (p.1,a)) (fun b => (q.1,b))) p.2 q.2

omit [Fintype ι] in
theorem amplify_taggedDensity_entry
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) (i j : ι) (a b : ο) :
    amplify Φ (taggedDensity i j) (0,a) (1,b) =
      (1/2 : ℂ) * (Φ (Matrix.single i j 1)) a b := by
  change Φ ((taggedDensity i j).submatrix (fun a => (0,a)) (fun b => (1,b))) a b = _
  rw [taggedDensity_crossBlock, map_smul]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Amplification preserves differences exactly. -/
theorem amplify_sub (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (X : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) :
    amplify (Φ - Ψ) X = amplify Φ X - amplify Ψ X := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A star-preserving map sends the Hermitian tagged density to a
Hermitian amplified output. The same applies to channel differences. -/
theorem amplify_isHermitian
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ)
    (hΦ : ∀ X, Φ Xᴴ = (Φ X)ᴴ)
    (X : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (hX : X.IsHermitian) :
    (amplify Φ X).IsHermitian := by
  ext p q
  let L := fun a : ι => (p.1,a)
  let R := fun b : ι => (q.1,b)
  have hs : (X.submatrix R L)ᴴ = X.submatrix L R := by
    ext a b
    exact hX.apply (L a) (R b)
  change star (Φ (X.submatrix R L) q.2 p.2) = Φ (X.submatrix L R) p.2 q.2
  rw [← hs, hΦ, Matrix.conjTranspose_apply]

omit [Fintype ι] in
/-- Positive tagged outputs suffice: their difference is Hermitian,
without a separate star-preservation premise. -/
theorem amplify_sub_tagged_isHermitian
    (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ) [Fintype ο] (i j : ι)
    (hΦ : (amplify Φ (taggedDensity i j)).PosSemidef)
    (hΨ : (amplify Ψ (taggedDensity i j)).PosSemidef) :
    (amplify (Φ - Ψ) (taggedDensity i j)).IsHermitian := by
  rw [amplify_sub]
  exact hΦ.isHermitian.sub hΨ.isHermitian

end RTDiamond


namespace RTDiamond
open Matrix
open scoped Matrix ComplexOrder BigOperators
set_option maxHeartbeats 1000000

variable {a b e : Type*} [Fintype a] [Fintype e] [DecidableEq a]

/-- The dilation action evaluated after tracing out the environment. -/
def dilationAction (V : Matrix (b × e) a ℂ) (X : Matrix a a ℂ) : Matrix b b ℂ :=
  fun p q => ∑ k : e, (V * X * Vᴴ) (p,k) (q,k)

/-- The Gram with the records on the labelled, correct-output fibre. -/
def forwardGram (f : a → b) (V : Matrix (b × e) a ℂ) : Matrix a a ℂ :=
  fun i j => ∑ k : e, star (V (f i,k) i) * V (f j,k) j

theorem dilationAction_matrix_unit
    (V : Matrix (b × e) a ℂ) (i j : a) (p q : b) :
    dilationAction V (Matrix.single i j 1) p q =
      ∑ k : e, V (p,k) i * star (V (q,k) j) := by
  classical
  unfold dilationAction
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply,
    Matrix.of_apply, Finset.sum_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [ite_and]

theorem correct_label_coefficient (f : a → b) (V : Matrix (b × e) a ℂ) (i j : a) :
    dilationAction V (Matrix.single i j 1) (f i) (f j) = star (forwardGram f V i j) := by
  rw [dilationAction_matrix_unit]
  simp only [forwardGram, star_sum, star_mul, star_star, mul_comm]

/-- No conjugation or factor ambiguity in the modulus of the actual
correct-output coefficient from a correlated matrix unit. -/
theorem correlated_error_norm
    {e' : Type*} [Fintype e']
    (f : a → b) (V : Matrix (b × e) a ℂ) (W : Matrix (b × e') a ℂ) (i j : a) :
    ‖(1/2 : ℂ) -
      dilationAction V (Matrix.single i j 1) (f i) (f j) *
      dilationAction W (Matrix.single i j 1) (f i) (f j)‖ =
    ‖(1/2 : ℂ) - forwardGram f V i j * forwardGram f W i j‖ := by
  rw [correct_label_coefficient, correct_label_coefficient]
  have he : (1/2 : ℂ) - star (forwardGram f V i j) * star (forwardGram f W i j) =
      star ((1/2 : ℂ) - forwardGram f V i j * forwardGram f W i j) := by
    rw [star_sub, star_mul, mul_comm]
    norm_num
  rw [he, norm_star]

end RTDiamond

namespace RTDiamond
open Matrix
open scoped Matrix ComplexOrder BigOperators
set_option maxHeartbeats 1200000
variable {a b e I : Type*} [Fintype a] [Fintype b] [Fintype e] [Fintype I]
  [DecidableEq a] [DecidableEq b] [DecidableEq I]

omit [Fintype b] [Fintype I] [DecidableEq a] [DecidableEq b] [DecidableEq I] in
theorem forwardGram_psd (f : a → b) (V : Matrix (b × e) a ℂ) :
    (forwardGram f V).PosSemidef := by
  let W : Matrix e a ℂ := fun k i => V (f i,k) i
  have h := Matrix.posSemidef_conjTranspose_mul_self W
  apply (show forwardGram f V = Wᴴ * W from rfl) ▸ h

omit [Fintype a] in
/-- A correct-output fibre is a compression of an isometry. Its exact
defect is the Gram of the discarded output coordinates. -/
theorem forward_fibre_defect
    (f : a → b) (V : Matrix (b × e) a ℂ) (hV : Vᴴ * V = 1)
    (g : I ↪ a) (y : b) (hg : ∀ i, f (g i) = y) :
    ((1 : Matrix I I ℂ) - (forwardGram f V).submatrix g g).PosSemidef := by
  let W : Matrix (b × e) I ℂ := V.submatrix id g
  let Z : Matrix (b × e) I ℂ :=
    fun p i => if p.1 = y then 0 else V p (g i)
  have hW := Matrix.posSemidef_conjTranspose_mul_self Z
  convert hW using 1
  ext i j
  have hcol : (Wᴴ * W) i j = (1 : Matrix I I ℂ) i j := by
    have h := congrFun (congrFun hV (g i)) (g j)
    simp only [one_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.submatrix_apply, id_eq]
      at h ⊢
    simpa only [g.injective.eq_iff] using h
  rw [Matrix.sub_apply, ← hcol]
  change (∑ p : b × e, star (V p (g i)) * V p (g j)) -
      (∑ k : e, star (V (f (g i),k) (g i)) * V (f (g j),k) (g j)) =
      ∑ p : b × e, star (Z p i) * Z p j
  simp only [hg,Z]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hf (z : b) (k : e) :
      star (if z = y then 0 else V (z,k) (g i)) * (if z = y then 0 else V (z,k) (g j)) =
      star (V (z,k) (g i)) * V (z,k) (g j) -
        (if z = y then star (V (y,k) (g i)) * V (y,k) (g j) else 0) := by
    by_cases hz : z = y <;> simp [hz]
  simp_rw [hf, Finset.sum_sub_distrib, Finset.sum_ite_irrel]
  simp

end RTDiamond

namespace RTDiamond
open Matrix
open scoped Matrix BigOperators
set_option maxHeartbeats 1000000

variable {a b e e' : Type*} [Fintype a] [Fintype e] [Fintype e'] [DecidableEq a]

/-- Stinespring coefficients after the correlated input encoding k ↦ (k,k).
The outputs are grouped (left/right output, left/right environment). -/
def pairedDilation (V : Matrix (b × e) a ℂ) (W : Matrix (b × e') a ℂ) :
    Matrix ((b × b) × (e × e')) a ℂ :=
  fun p i => V (p.1.1,p.2.1) i * W (p.1.2,p.2.2) i

omit [Fintype a] [DecidableEq a] in
theorem paired_forwardGram (f : a → b) (V : Matrix (b × e) a ℂ)
    (W : Matrix (b × e') a ℂ) (i j : a) :
    forwardGram (fun k => (f k,f k)) (pairedDilation V W) i j =
      forwardGram f V i j * forwardGram f W i j := by
  unfold forwardGram pairedDilation
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [star_mul]
  ring

theorem paired_channel_coefficient (f : a → b) (V : Matrix (b × e) a ℂ)
    (W : Matrix (b × e') a ℂ) (i j : a) :
    dilationAction (pairedDilation V W) (Matrix.single i j 1) (f i,f i) (f j,f j) =
      star (forwardGram f V i j * forwardGram f W i j) := by
  have h := correct_label_coefficient (fun k => (f k,f k)) (pairedDilation V W) i j
  simpa only [paired_forwardGram] using h

end RTDiamond

namespace NativeDiamond

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open scoped Matrix ComplexOrder MatrixOrder CStarAlgebra

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A native quantum channel viewed in ordinary matrix coordinates. -/
def matrixAction (channel : QuantumChannel a b) : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ :=
  (CStarMatrix.ofMatrixStarAlgEquiv (n := b)).symm.toAlgEquiv.toLinearMap.comp
    (channel.toCompletelyPositiveMap.toLinearMap.comp
      (CStarMatrix.ofMatrixStarAlgEquiv (n := a)).toAlgEquiv.toLinearMap)

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
matrix-unit coefficient with no loss from the two reference tags. -/
theorem matrixUnit_le_diamondDistance (first second : QuantumChannel a b)
    (i j : a) (p q : b) :
    ‖((matrixAction first - matrixAction second) (Matrix.single i j 1)) p q‖ ≤
      diamondDistance first second := by
  let X : DensityState (Fin 2 × a) := ⟨CStarMatrix.ofMatrix (RTDiamond.taggedDensity i j),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (RTDiamond.taggedDensity_psd i j).nonneg,
    RTDiamond.taggedDensity_trace i j⟩
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
      ((matrixAction first - matrixAction second) (Matrix.single i j 1)) p q := by
    change (CStarMatrix.ofMatrix.symm
        (referenceAction first (CStarMatrix.ofMatrix (RTDiamond.taggedDensity i j))) -
      CStarMatrix.ofMatrix.symm
        (referenceAction second (CStarMatrix.ofMatrix (RTDiamond.taggedDensity i j)))) (0,p) (1,q) = _
    rw [reference_block, reference_block, ← RTDiamond.amplify_sub]
    exact RTDiamond.amplify_taggedDensity_entry (matrixAction first - matrixAction second) i j p q
  have hn : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num [norm_div]
  rw [he, Complex.norm_mul, hn] at hu
  have hentry : ‖((matrixAction first - matrixAction second) (Matrix.single i j 1)) p q‖ ≤
      traceNorm Y := by linarith
  exact hentry.trans (referenceError_le_diamond first second 2 X)

/-- A native channel-distance application with explicit cross-fibre record
correspondence. Cross-entry dominance suffices; a common correlation
quotient is one way to establish it, not a premise of the theorem. -/
theorem near_real_diamond_lower_of_dominance (first second : QuantumChannel a b)
    (G H : Matrix RTCompletion.Coord RTCompletion.Coord ℂ)
    (hH : H.PosSemidef)
    (defect : ∀ f : Fin 3,
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock H f).PosSemidef)
    (dominates : ∀ i j : Fin 3, i ≠ j → ∀ u v : Fin 2,
      ‖G (i,u) (j,v)‖ ≤ ‖H (i,u) (j,v)‖)
    (pick : RTCompletion.Coord → a) (correct : Fin 3 → b)
    (actual : ∀ p q : RTCompletion.Coord, p.1 ≠ q.1 →
      matrixAction first (Matrix.single (pick p) (pick q) 1)
        (correct p.1) (correct q.1) = star (G p q * H p q))
    (target : ∀ p q : RTCompletion.Coord, p.1 ≠ q.1 →
      matrixAction second (Matrix.single (pick p) (pick q) 1)
        (correct p.1) (correct q.1) = 1/2)
    (η : ℝ)
    (close : ∀ u v w : Fin 2,
      |(RTPhaseCube.triangleProduct (H (0,u) (1,v)) (H (1,v) (2,w))
        (H (0,u) (2,w))).im| ≤ η) :
    1/4 - (128/27) * η^2 ≤ diamondDistance first second := by
  apply RTCompletion.near_real_error_lower_of_cross_dominance
    G H hH defect dominates _ η _ close
  intro i j hij u v
  have hz := matrixUnit_le_diamondDistance first second
    (pick (i,u)) (pick (j,v)) (correct i) (correct j)
  change ‖matrixAction first (Matrix.single (pick (i,u)) (pick (j,v)) 1)
      (correct i) (correct j) -
    matrixAction second (Matrix.single (pick (i,u)) (pick (j,v)) 1)
      (correct i) (correct j)‖ ≤ _ at hz
  rw [actual _ _ hij, target _ _ hij] at hz
  have he : star (G (i,u) (j,v) * H (i,u) (j,v) - (1/2 : ℂ)) =
      star (G (i,u) (j,v) * H (i,u) (j,v)) - 1/2 := by
    rw [star_sub]
    norm_num
  rwa [← he, norm_star, norm_sub_rev] at hz

/-- Forward records of an actual paired dilation satisfy the positivity and
within-fibre contraction hypotheses. The channel/dilation and target matrix
coefficients and cross-entry modulus comparison remain explicit premises. -/
theorem paired_near_real_diamond_lower
    {e₁ e₂ : Type*} [Fintype e₁] [Fintype e₂]
    (first second : QuantumChannel a (b × b))
    (V : Matrix (b × e₁) a ℂ) (W : Matrix (b × e₂) a ℂ)
    (hW : Wᴴ * W = 1)
    (pair : ∀ X, matrixAction first X = RTDiamond.dilationAction (RTDiamond.pairedDilation V W) X)
    (f : a → b) (pick : RTCompletion.Coord ↪ a) (label : Fin 3 → b)
    (byFibre : ∀ p : RTCompletion.Coord, f (pick p) = label p.1)
    (dominates : ∀ i j : Fin 3, i ≠ j → ∀ u v : Fin 2,
      ‖RTDiamond.forwardGram f V (pick (i,u)) (pick (j,v))‖ ≤
        ‖RTDiamond.forwardGram f W (pick (i,u)) (pick (j,v))‖)
    (target : ∀ p q : RTCompletion.Coord, p.1 ≠ q.1 →
      matrixAction second (Matrix.single (pick p) (pick q) 1)
        (label p.1,label p.1) (label q.1,label q.1) = 1/2)
    (η : ℝ)
    (close : ∀ u v w : Fin 2,
      |(RTPhaseCube.triangleProduct
        (RTDiamond.forwardGram f W (pick (0,u)) (pick (1,v)))
        (RTDiamond.forwardGram f W (pick (1,v)) (pick (2,w)))
        (RTDiamond.forwardGram f W (pick (0,u)) (pick (2,w)))).im| ≤ η) :
    1/4 - (128/27) * η^2 ≤ diamondDistance first second := by
  let G := (RTDiamond.forwardGram f V).submatrix pick pick
  let H := (RTDiamond.forwardGram f W).submatrix pick pick
  have hH : H.PosSemidef := (RTDiamond.forwardGram_psd f W).submatrix pick
  have hdef (i : Fin 3) :
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock H i).PosSemidef := by
    let g : Fin 2 ↪ a := ⟨fun t => pick (i,t), fun _ _ h =>
      congrArg Prod.snd (pick.injective h)⟩
    exact RTDiamond.forward_fibre_defect f W hW g (label i) (fun t => byFibre (i,t))
  apply near_real_diamond_lower_of_dominance first second G H hH hdef dominates
    pick (fun i => (label i,label i)) _ target η close
  intro p q _
  rw [pair]
  simpa only [byFibre, G, H, Matrix.submatrix_apply] using
    RTDiamond.paired_channel_coefficient f V W (pick p) (pick q)

end NativeDiamond
end D5.S3.Quantum.Recovery.PrincipalTrianglePhase
