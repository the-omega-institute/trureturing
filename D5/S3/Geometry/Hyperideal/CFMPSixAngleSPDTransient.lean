/-
SOURCE ONLY — UNCOMPILED — zero canonical retention.
Exact supplier/module mapping and hashes: suppliers.json in this directory.
The three packet modules must be supplied unchanged in the indicated order.
The authentic original TwoLengthAngleSum source is supplied unchanged.
This file neither installs modules nor establishes any kernel receipt.
CLAUDE §3.2: transient application only; no admission or novelty claim.
-/
import D5.S3.Geometry.Hyperideal.CFMPSixAngleJacobianTransient
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Connected.Clopen
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Matrix
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator
open OriginalSixAngleJacobianTransient
open CFMP80NativeDomainExactTransient
open D5.S3.Geometry.Hyperideal.GramDomainContraction

namespace OriginalSixAngleSPDTransient
set_option autoImplicit false

-- Access original definitions only; no supplier proof is copied or changed.
open private p opposite from D5.S3.Geometry.Hyperideal.CFMPSixAngleJacobianTransient

/-- A local, consumed continuation argument. Openness uses upstream spectrum
upper hemicontinuity; closedness uses quadratic forms and PSD + invertibility.
There is no eigenvalue/eigenbasis continuity reproof. -/
private theorem continue_posDef {T : Type*} [TopologicalSpace T]
    [PreconnectedSpace T] (F : T → M6) (hF : Continuous F)
    (hH : ∀ t, (F t).IsHermitian) (hU : ∀ t, (F t).det ≠ 0)
    (t₀ : T) (h₀ : (F t₀).PosDef) : ∀ t, (F t).PosDef := by
  let s : Set T := {t | (F t).PosDef}
  have hspec (t : T) : (F t).PosDef ↔ spectrum ℝ (F t) ⊆ Ioi 0 := by
    rw [← Matrix.isStrictlyPositive_iff_posDef]
    exact StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) (F t)
      (Matrix.isHermitian_iff_isSelfAdjoint.mp (hH t))
  have hopen : IsOpen s := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have he := (upperHemicontinuous_spectrum ℝ M6).forall_isOpen
      (F t) (Ioi 0) isOpen_Ioi ((hspec t).mp ht)
    have hp := (hF.continuousAt (x := t)).tendsto.eventually he
    filter_upwards [hp] with u hu
    exact (hspec u).mpr hu
  have heq : s = ⋂ z : V, {t | 0 ≤ star z ⬝ᵥ ((F t) *ᵥ z)} := by
    ext t
    simp only [mem_iInter, mem_setOf_eq]
    change (F t).PosDef ↔ ∀ z : V, 0 ≤ star z ⬝ᵥ ((F t) *ᵥ z)
    constructor
    · intro hp z
      exact hp.posSemidef.dotProduct_mulVec_nonneg z
    · intro hp
      have hps : (F t).PosSemidef :=
        Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hH t, hp⟩
      exact hps.posDef_iff_det_ne_zero.mpr (hU t)
  have hclosed : IsClosed s := by
    rw [heq]
    apply isClosed_iInter
    intro z
    apply isClosed_le continuous_const
    unfold dotProduct Matrix.mulVec
    fun_prop
  have hall : s = univ := (show IsClopen s from ⟨hclosed, hopen⟩).eq_univ ⟨t₀, h₀⟩
  intro t
  have ht : t ∈ s := hall ▸ mem_univ t
  exact ht

private theorem W_hermitian (x : V) : (W x).IsHermitian := by
  change (W x)ᴴ = W x
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W, Matrix.conjTranspose_apply]

/-- Full six-vector certificate, using the supplier's actual complementary
slot permutation (0 3)(1 4)(2 5), not a restriction to a symmetric direction. -/
private theorem W_center_posDef : (W (fun _ => 2)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (W_hermitian _)
  intro z hz
  have hcert : star z ⬝ᵥ (W (fun _ => 2) *ᵥ z) =
      3 * (∑ i : Fin 6, (z i)^2) +
      (3 / 2 : ℝ) * (∑ i : Fin 6, (z i - z (opposite i))^2) +
      2 * (∑ i : Fin 6, z i)^2 := by
    simp [dotProduct, Matrix.mulVec, W, p, opposite, Fin.sum_univ_succ]
    <;> ring
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    simpa only [funext_iff, Pi.zero_apply, not_forall] using hz
  have hpos : 0 < ∑ i : Fin 6, (z i)^2 :=
    Finset.sum_pos' (fun i _ => sq_nonneg (z i))
      ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have hnonneg : 0 ≤ ∑ i : Fin 6, (z i - z (opposite i))^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [hcert]
  nlinarith only [hpos, hnonneg, sq_nonneg (∑ i : Fin 6, z i)]

private theorem K_hermitian (l : V) : (K l).IsHermitian := by
  change (K l)ᴴ = K l
  have hW (i j : Fin 6) : W (xOf l) j i = W (xOf l) i j := by
    have h := congrArg (fun A : M6 => A i j) (W_hermitian (xOf l))
    simpa [Matrix.conjTranspose_apply] using h
  ext i j
  simp only [Matrix.conjTranspose_apply, K, star_trivial]
  rw [hW i j]
  ring

private theorem K_of_W_posDef (l : V) (hl : ∀ i, 0 < l i)
    (hΔ : 0 < Delta (xOf l)) (hW : (W (xOf l)).PosDef) : (K l).PosDef := by
  let S : M6 := Matrix.diagonal (sigma l)
  have hinj : Function.Injective S.mulVec := by
    intro u v huv
    funext i
    have he := congrFun huv i
    have hs : sigma l i ≠ 0 := (Real.sinh_pos_iff.mpr (hl i)).ne'
    simp only [S, Matrix.mulVec_diagonal] at he
    exact mul_left_cancel₀ hs he
  have hcong := hW.conjTranspose_mul_mul_same hinj
  have hid : K l = (Real.sqrt (Delta (xOf l)))⁻¹ • (Sᴴ * W (xOf l) * S) := by
    ext i j
    simp [S, K, Matrix.diagonal_conjTranspose, Matrix.conjTranspose_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [hid]
  exact hcong.smul (inv_pos.mpr (Real.sqrt_pos.mpr hΔ))

private theorem continuous_K : Continuous (fun l : lengthDeterminantDomain => K l.val) := by
  have hx (l : lengthDeterminantDomain) (i : Fin 6) : 1 < xOf l.val i :=
    Real.one_lt_cosh.mpr (l.property.1 i).ne'
  have hd (l : lengthDeterminantDomain) (i : Fin 6) : (xOf l.val i)^2 - 1 ≠ 0 := by
    have h := hx l i
    have hp : 0 < (xOf l.val i)^2 - 1 := by
      nlinarith only [h, sq_nonneg (xOf l.val i - 1)]
    exact hp.ne'
  have hW : Continuous (fun l : lengthDeterminantDomain => W (xOf l.val)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply continuous_iff_continuousAt.mpr
    intro l
    have h0 := hd l 0
    have h1 := hd l 1
    have h2 := hd l 2
    have h3 := hd l 3
    have h4 := hd l 4
    have h5 := hd l 5
    fin_cases i <;> fin_cases j <;> simp [W, p]
    all_goals
      unfold xOf at *
      fun_prop (disch := assumption)
  have hDelta : Continuous (fun l : lengthDeterminantDomain => Delta (xOf l.val)) := by
    unfold Delta delta gram xOf
    fun_prop
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hw : Continuous (fun l : lengthDeterminantDomain => W (xOf l.val) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hW)
  have hs (q : Fin 6) : Continuous (fun l : lengthDeterminantDomain => sigma l.val q) := by
    unfold sigma
    fun_prop
  exact (((hs i).mul hw).mul (hs j)).div hDelta.sqrt
    (fun l => (Real.sqrt_pos.mpr l.property.2).ne')

/-- The exact original full target. Only positive independent lengths and the
original positive determinant are hypotheses. All source remains uncompiled. -/
theorem original_six_angle_jacobian_posDef (l : V) (hl : ∀ i, 0 < l i)
    (hΔ : 0 < Delta (xOf l)) : Matrix.PosDef (J l) := by
  letI : ContractibleSpace lengthDeterminantDomain := lengthDeterminantDomain_contractible
  let l₀ : V := fun _ => Real.arcosh 2
  have hl₀ : ∀ i, 0 < l₀ i := fun _ => Real.arcosh_pos (by norm_num)
  have hx₀ : xOf l₀ = fun _ => 2 := by
    funext i
    exact Real.cosh_arcosh (by norm_num)
  have hΔ₀ : 0 < Delta (xOf l₀) := by
    rw [hx₀]
    exact center.property.2
  let t₀ : lengthDeterminantDomain := ⟨l₀, hl₀, hΔ₀⟩
  have hbase : (K t₀.val).PosDef := by
    apply K_of_W_posDef l₀ hl₀ hΔ₀
    rw [hx₀]
    exact W_center_posDef
  have hunit (t : lengthDeterminantDomain) : (K t.val).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse
      (original_six_angle_jacobian t.val t.property.1 t.property.2).2
  have hK : (K l).PosDef :=
    continue_posDef (fun t : lengthDeterminantDomain => K t.val) continuous_K
      (fun t => K_hermitian t.val) hunit t₀ hbase ⟨l, hl, hΔ⟩
  have hKJ := (original_six_angle_jacobian l hl hΔ).2
  have hJ : (K l)⁻¹ = J l := Matrix.inv_eq_right_inv hKJ
  rw [← hJ]
  exact hK.inv

end OriginalSixAngleSPDTransient

#check OriginalSixAngleSPDTransient.original_six_angle_jacobian_posDef
#print axioms OriginalSixAngleSPDTransient.original_six_angle_jacobian_posDef
