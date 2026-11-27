import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameCubicRank
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameOrbitSpan
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.NormNum.IsSquare
import OmegaBuild.Commands

compile_only_with_mathlib

/-! The concrete P48p frame generators have no proper nonzero rational invariant subspace. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameRationalIrreducibility

open scoped Matrix
open P48pSymmetricCommutantCertificate
open P48pFrameOrbitSpan (FrameInvariant j_commuting_frame_invariant_span)
open P48pFrameCubicRank (C)
open private tIndex tSign uIndex uSign ratCast ratCast_smul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSymmetricCommutantCertificate
open private signed_conj_entry from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameOrbitSpan

private abbrev FrameIndex := Fin 48
private abbrev FrameSpace := FrameIndex → ℚ
private abbrev FrameMatrix := Matrix FrameIndex FrameIndex ℚ

local notation "T" => tFrameMatrix.map (Int.cast : ℤ → ℚ)
local notation "U" => uFrameMatrix.map (Int.cast : ℤ → ℚ)

private theorem signed_mul_transpose (index : FrameIndex → FrameIndex)
    (sign : FrameIndex → ℤ) (hindex : Function.Injective index)
    (hsign : ∀ i, sign i * sign i = 1) :
    let O := (signedFrameMatrix index sign).map (Int.cast : ℤ → ℚ)
    O * Oᵀ = 1 := by
  dsimp only
  apply Matrix.ext
  intro i j
  have h := signed_conj_entry index sign (1 : FrameMatrix) i j
  dsimp only at h
  rw [mul_one] at h
  rw [h]
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.one_apply_eq, mul_one, Int.cast_mul, Int.cast_one] using
      congrArg (fun z : ℤ => (z : ℚ)) (hsign i)
  · have hne : index i ≠ index j := fun he => hij (hindex he)
    simp only [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij, mul_zero]

set_option maxHeartbeats 2000000 in
private theorem t_mul_transpose : T * Tᵀ = 1 := by
  apply signed_mul_transpose tIndex tSign
  · intro i
    change ∀ j : Fin 48, tIndex i = tIndex j → i = j
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

set_option maxHeartbeats 2000000 in
private theorem u_mul_transpose : U * Uᵀ = 1 := by
  apply signed_mul_transpose uIndex uSign
  · intro i
    change ∀ j : Fin 48, uIndex i = uIndex j → i = j
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

private theorem cubic_mul_transpose : C * Cᵀ = 1 := by
  have hJ : JRatᵀ = -JRat := by
    simpa only [map_neg] using congrArg ratCast J_transpose
  have hCt : Cᵀ = (1 / 6 : ℚ) • (-JRat - (3 : ℚ) • 1) := by
    simp only [C, Matrix.transpose_smul, Matrix.transpose_sub, hJ, Matrix.transpose_one]
  rw [hCt, C]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sub_mul, mul_sub,
    mul_neg, J_sq_rat, mul_one, one_mul, smul_sub, smul_neg]
  module

private theorem commutantMRat_sq : commutantMRat * commutantMRat = (621 : ℚ) • 1 := by
  simpa only [map_mul, ratCast_smul, map_one] using congrArg ratCast commutantM_sq

private theorem commutantMRat_independent :
    LinearIndependent ℚ ![(1 : FrameMatrix), commutantMRat] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  have hm : commutantMRat 0 1 = (2 : ℚ) := by decide +kernel
  have h01 : b * 2 = 0 := by
    simpa only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul,
      Matrix.one_apply_ne (by decide : (0 : FrameIndex) ≠ 1), hm, mul_zero, zero_add] using
      congrArg (fun A : FrameMatrix => A 0 1) h
  have hb : b = 0 := (mul_eq_zero.mp h01).resolve_right (by norm_num)
  have ha : a = 0 := by
    simpa only [hb, zero_smul, add_zero, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.zero_apply, smul_eq_mul, mul_one] using congrArg (fun A : FrameMatrix => A 0 0) h
  exact ⟨ha, hb⟩

/-- An idempotent symmetric matrix commuting with the three P48p frame generators
is zero or the identity. -/
theorem symmetric_idempotent_eq_zero_or_one (A : Matrix (Fin 48) (Fin 48) ℚ)
    (hsymm : Aᵀ = A) (hT : Commute A T) (hU : Commute A U) (hC : Commute A C)
    (hidem : IsIdempotentElem A) :
    A = 0 ∨ A = 1 := by
  have conjugation (O : FrameMatrix) (hO : O * Oᵀ = 1) (h : Commute A O) :
      O * A * Oᵀ = A := by
    rw [h.eq.symm, Matrix.mul_assoc, hO, mul_one]
  have hA : FrameInvariant A :=
    ⟨hsymm, conjugation T t_mul_transpose hT, conjugation U u_mul_transpose hU⟩
  have hJ : A * JRat = JRat * A := by
    have h := hC.eq
    simp only [C, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_one, one_mul] at h
    have h' := smul_right_injective FrameMatrix (by norm_num : (1 / 6 : ℚ) ≠ 0) h
    simpa only [sub_add_cancel] using
      congrArg (fun B : FrameMatrix => B + (3 : ℚ) • A) h'
  obtain ⟨a, b, hab⟩ := j_commuting_frame_invariant_span A hA hJ
  have hcoeff :
      (a * a + b * b * 621) • (1 : FrameMatrix) + (a * b + b * a) • commutantMRat =
        a • (1 : FrameMatrix) + b • commutantMRat := by
    calc
      _ = A * A := by
        rw [hab]
        simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          one_mul, mul_one, commutantMRat_sq]
        module
      _ = _ := hidem.eq.trans hab
  obtain ⟨hconstant, hlinear⟩ := commutantMRat_independent.eq_of_pair hcoeff
  by_cases hb : b = 0
  · have ha : a * (a - 1) = 0 := by simpa [hb, mul_sub, sub_eq_zero] using hconstant
    rcases mul_eq_zero.mp ha with ha | ha
    · left
      simp [hab, ha, hb]
    · right
      simp [hab, sub_eq_zero.mp ha, hb]
  · have hfactor : (2 * a - 1) * b = 0 := by
      nlinarith only [hlinear]
    have ha : a = 1 / 2 := by
      linarith only [(mul_eq_zero.mp hfactor).resolve_right hb]
    rw [ha] at hconstant
    exfalso
    have hden : (2 : ℚ) * b ≠ 0 := mul_ne_zero (by norm_num) hb
    have hsquare : IsSquare (621 : ℚ) := by
      refine ⟨1 / (2 * b), ?_⟩
      rw [div_mul_div_comm, one_mul, eq_div_iff (mul_ne_zero hden hden)]
      nlinarith only [hconstant]
    exact (by norm_num : ¬ IsSquare (621 : ℚ)) hsquare

private def standardB : LinearMap.BilinForm ℚ FrameSpace := dotProductBilin ℚ ℚ

private theorem standardB_symm : standardB.IsSymm :=
  ⟨dotProduct_comm⟩

private theorem projection_exists (W : Submodule ℚ FrameSpace) :
    ∃ P : Module.End ℚ FrameSpace,
      LinearMap.range P = W ∧ LinearMap.ker P = standardB.orthogonal W ∧
      IsIdempotentElem P ∧ standardB.IsSelfAdjoint P := by
  let Wperp := standardB.orthogonal W
  have hnondeg : (standardB.restrict W).Nondegenerate := by
    constructor <;> intro x hx <;> exact
      Subtype.ext (dotProduct_self_eq_zero.mp (hx x))
  have hcompl : IsCompl W Wperp :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      standardB_symm.isRefl hnondeg
  let P := W.projection Wperp hcompl
  let Q := Wperp.projection W hcompl.symm
  refine ⟨P, Submodule.range_projection hcompl, Submodule.ker_projection hcompl,
    Submodule.isIdempotentElem_projection hcompl, ?_⟩
  have hpair (x y : FrameSpace) : standardB (P x) y = standardB (P x) (P y) := by
    have hx : P x ∈ W := Submodule.projection_apply_mem hcompl x
    have hy : Q y ∈ Wperp := Submodule.projection_apply_mem hcompl.symm y
    calc
      standardB (P x) y = standardB (P x) (P y + Q y) :=
        congrArg (standardB (P x)) (Submodule.projection_add_projection_eq_self hcompl y).symm
      _ = standardB (P x) (P y) := by
        rw [standardB.add_right, (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) _ hx, add_zero]
  intro x y
  calc
    standardB (P x) y = standardB (P x) (P y) := hpair x y
    _ = standardB (P y) (P x) := standardB_symm.eq _ _
    _ = standardB (P y) x := (hpair y x).symm
    _ = standardB x (P y) := standardB_symm.eq _ _

private theorem projection_commutes (W : Submodule ℚ FrameSpace)
    (P : Module.End ℚ FrameSpace) (hrange : LinearMap.range P = W)
    (hker : LinearMap.ker P = standardB.orthogonal W) (hidem : IsIdempotentElem P)
    (O : FrameMatrix) (hO : O * Oᵀ = 1) (hW : ∀ x ∈ W, O *ᵥ x ∈ W) :
    Commute P.toMatrix' O := by
  have hleft : Oᵀ * O = 1 := mul_eq_one_comm.mp hO
  have hleft_apply (x : FrameSpace) : Oᵀ *ᵥ (O *ᵥ x) = x := by
    rw [← Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hpres (x y : FrameSpace) :
      standardB (O *ᵥ x) (O *ᵥ y) = standardB x y := by
    change (O *ᵥ x) ⬝ᵥ (O *ᵥ y) = x ⬝ᵥ y
    rw [dotProduct_comm (O *ᵥ x) (O *ᵥ y),
      ← Matrix.dotProduct_transpose_mulVec O x (O *ᵥ y),
      hleft_apply]
  let action : W →ₗ[ℚ] W := O.toLin'.restrict hW
  have hinj : Function.Injective action := by
    intro x y hxy
    have h : O *ᵥ (x : FrameSpace) = O *ᵥ (y : FrameSpace) :=
      congrArg Subtype.val hxy
    exact Subtype.ext ((hleft_apply x).symm.trans
      ((congrArg (fun v : FrameSpace => Oᵀ *ᵥ v) h).trans (hleft_apply y)))
  have hsurj := LinearMap.surjective_of_injective hinj
  have hperp (x : FrameSpace) (hx : x ∈ standardB.orthogonal W) :
      O *ᵥ x ∈ standardB.orthogonal W := by
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro y hy
    obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
    have hz' : O *ᵥ (z : FrameSpace) = y := congrArg Subtype.val hz
    calc
      standardB y (O *ᵥ x) = standardB (O *ᵥ (z : FrameSpace)) (O *ᵥ x) := by rw [hz']
      _ = standardB z x := hpres _ _
      _ = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) _ z.property
  have hcomm : Commute P O.toLin' := by
    apply (LinearMap.IsIdempotentElem.commute_iff hidem).mpr
    rw [hrange, hker]
    simp only [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem, Matrix.toLin'_apply]
    exact ⟨hW, hperp⟩
  change P.toMatrix' * O = O * P.toMatrix'
  simpa only [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_toLin'] using
    congrArg LinearMap.toMatrix' hcomm.eq

/-- The actual signed transvections and cubic have no proper nonzero invariant
subspace over ℚ. Forward invariance suffices because each generator restricts
to a bijection of any invariant subspace. -/
theorem invariant_submodule_eq_bot_or_top (W : Submodule ℚ (Fin 48 → ℚ))
    (hT : ∀ x ∈ W, T *ᵥ x ∈ W) (hU : ∀ x ∈ W, U *ᵥ x ∈ W)
    (hC : ∀ x ∈ W, C *ᵥ x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨P, hrange, hker, hidem, hself⟩ := projection_exists W
  let A := P.toMatrix'
  have hsymm : Aᵀ = A := by
    apply Matrix.ext
    intro i j
    have h := hself (Pi.single i 1) (Pi.single j 1)
    change P (Pi.single i 1) ⬝ᵥ Pi.single j 1 = Pi.single i 1 ⬝ᵥ P (Pi.single j 1) at h
    simpa only [A, Matrix.transpose_apply, LinearMap.toMatrix'_apply, dotProduct_single_one,
      single_one_dotProduct] using h
  have hA : IsIdempotentElem A := by
    change P.toMatrix' * P.toMatrix' = P.toMatrix'
    simpa only [LinearMap.toMatrix'_mul] using congrArg LinearMap.toMatrix' hidem.eq
  have h := symmetric_idempotent_eq_zero_or_one A hsymm
    (projection_commutes W P hrange hker hidem T t_mul_transpose hT)
    (projection_commutes W P hrange hker hidem U u_mul_transpose hU)
    (projection_commutes W P hrange hker hidem C cubic_mul_transpose hC) hA
  rcases h with hz | ho
  · left
    have hp : P = 0 := by
      simpa only [Matrix.toLin'_toMatrix', map_zero] using congrArg Matrix.toLin' hz
    rw [← hrange, hp, LinearMap.range_zero]
  · right
    have hp : P = LinearMap.id := by
      simpa only [Matrix.toLin'_toMatrix', Matrix.toLin'_one] using congrArg Matrix.toLin' ho
    rw [← hrange, hp, LinearMap.range_id]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameRationalIrreducibility
