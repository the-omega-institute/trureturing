import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBGradedModeBridge
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBMarkedLift

/-! Raw scalar-mode Jacobi and finite support for arbitrary actual HHBB states. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing

open ActualLeechHyperbolic (leechData)
open ActualEnergyRestrictedDual (maxOddWeight)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeFixedPairField (nu nu_lower_truncation)
open Orbifold.NativeMixedPairField (mu mu_lower_truncation)
open NativeMixedComplexSewing (aJointTerm)
open NativeMixedUpperProductCusp (bJointTerm)
open NativeHHBBModeResidue
  (bModes dModes aModes hhbb_graded_mode_sums hhbb_marked_coefficient_jacobi_raw)
open NativeHHBBTwoVariableRational (bJointTerm_off_total aJointTerm_off_total)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)

open private HHBBLinear aLinear aLinear_apply bLinear bLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private cast_occupation from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue

local notation "ℒ" => leechData

private theorem finite_support_of_bound {f : ℕ → ℂ} (bound : ℤ)
    (h : ∀ j : ℕ, bound < (j : ℤ) → f j = 0) : Function.HasFiniteSupport f := by
  refine (Set.finite_lt_nat (bound.toNat + 1)).subset ?_
  intro j hj
  change j < bound.toNat + 1
  by_contra! hlarge
  exact hj (h j (by omega))

/-- Inner-field lower truncation gives finite support in the binomial index for
each raw channel, with any scalar weights. -/
theorem hhbb_raw_mode_finite_support (u v : TwistedEven) (w b : TwistedOdd)
    (W q r : ℤ) (weightB weightD weightA : ℕ → ℂ) :
    Function.HasFiniteSupport
      (fun j => weightB j * bJointTerm false false v w u b 1 1 (bModes W q r j)) ∧
    Function.HasFiniteSupport
      (fun j => weightD j * bJointTerm false false u w v b 1 1 (dModes W q j)) ∧
    Function.HasFiniteSupport
      (fun j => weightA j * aJointTerm u v w b 1 1 (aModes W r j)) := by
  let U : ℤ := maxOddWeight ℒ leechUnit u.val
  let V : ℤ := maxOddWeight ℒ leechUnit v.val
  let H : ℤ := maxOddWeight ℒ leechUnit w.val
  refine ⟨finite_support_of_bound (2 * (W + q + r + 1) + V + H + 6) ?_,
    finite_support_of_bound (-2 * q + U + H + 6) ?_,
    finite_support_of_bound (-2 * (r + 1) + U + V + 6) ?_⟩
  · intro j hj
    have hz := mu_lower_truncation false v w (bModes W q r j).1
      (show (bModes W q r j).1 ≤ -V - H - 6 by dsimp only [bModes]; omega)
    unfold bJointTerm
    rw [hz]
    simp
  · intro j hj
    have hz := mu_lower_truncation false u w (dModes W q j).1
      (show (dModes W q j).1 ≤ -U - H - 6 by dsimp only [dModes]; omega)
    unfold bJointTerm
    rw [hz]
    simp
  · intro j hj
    have hz := nu_lower_truncation false u v (aModes W r j).1
      (show (aModes W r j).1 < -U - V - 6 by dsimp only [aModes]; omega)
    unfold aJointTerm
    rw [hz]
    simp

private def bWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * ((Ring.choose r j : ℤ) : ℂ)

private def dWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ (r + (j : ℤ)) * ((Ring.choose r j : ℤ) : ℂ)

private def aWeight (q : ℤ) (j : ℕ) : ℂ :=
  Ring.choose ((q : ℂ) - 1 / 2) j

private def defectTerm (W q r : ℤ) (j : ℕ) : HHBBLinear :=
  let B : HHBBLinear := (-bWeight r j) • bLinear 1 1 (bModes W q r j)
  let D : HHBBLinear := (-dWeight r j) • (bLinear 1 1 (dModes W q j)).flip
  let A : HHBBLinear := (-aWeight q j) • aLinear 1 1 (aModes W r j)
  B + D + A

private theorem defectTerm_apply (W q r : ℤ) (j : ℕ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    defectTerm W q r j u v w b =
      (-bWeight r j) * bJointTerm false false v w u b 1 1 (bModes W q r j) -
      dWeight r j * bJointTerm false false u w v b 1 1 (dModes W q j) -
      aWeight q j * aJointTerm u v w b 1 1 (aModes W r j) := by
  simp only [defectTerm, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply,
    smul_eq_mul, aLinear_apply, bLinear_apply, neg_mul, sub_eq_add_neg]

private theorem defectTerm_finite_support (W q r : ℤ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    Function.HasFiniteSupport (fun j => defectTerm W q r j u v w b) := by
  obtain ⟨hB, hD, hA⟩ := hhbb_raw_mode_finite_support u v w b W q r
    (fun j => -bWeight r j) (dWeight r) (aWeight q)
  simpa only [defectTerm_apply] using (hB.fun_sub hD).fun_sub hA

/-- The sum of the signed defect terms is linear in each external state. -/
private def hhbbRawModeDefect (W q r : ℤ) : HHBBLinear := by
  refine {
    toFun := fun u => {
      toFun := fun v => {
        toFun := fun w => {
          toFun := fun b => ∑ᶠ j, defectTerm W q r j u v w b
          map_add' := ?_
          map_smul' := ?_ }
        map_add' := ?_
        map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
    map_add' := ?_
    map_smul' := ?_ }
  all_goals
    intros
    repeat' (apply LinearMap.ext; intro)
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, LinearMap.smul_apply,
      RingHom.id_apply, map_add, map_smul]
    first
    | exact finsum_add_distrib (defectTerm_finite_support W q r _ _ _ _)
        (defectTerm_finite_support W q r _ _ _ _)
    | exact (smul_finsum _ _).symm

private theorem hhbbRawModeDefect_apply (W q r : ℤ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    hhbbRawModeDefect W q r u v w b =
      -(∑ᶠ j, bWeight r j * bJointTerm false false v w u b 1 1 (bModes W q r j)) -
      (∑ᶠ j, dWeight r j * bJointTerm false false u w v b 1 1 (dModes W q j)) -
      (∑ᶠ j, aWeight q j * aJointTerm u v w b 1 1 (aModes W r j)) := by
  obtain ⟨hB, hD, hA⟩ := hhbb_raw_mode_finite_support u v w b W q r
    (fun j => -bWeight r j) (dWeight r) (aWeight q)
  change (∑ᶠ j, defectTerm W q r j u v w b) = _
  simp only [defectTerm_apply]
  rw [finsum_sub_distrib (hB.fun_sub hD) hA, finsum_sub_distrib hB hD]
  simp only [neg_mul, finsum_neg_distrib]

private theorem hhbb_raw_mode_defect_marked {ι : Type} [Finite ι]
    (slot : ι → Puncture) (colour : ι → Fin leechData.rank) (n : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (gP gQ gR gS : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] gP)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] gQ)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] gR)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] gS)
    (W q r : ℤ) : hhbbRawModeDefect W q r u v w b = 0 := by
  let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
  let M := grade .P
  let K := grade .Q
  let L := grade .R
  let N := grade .S
  have hgrade (i : Puncture) : (grade i : ℤ) = doubledOccupation slot n l i :=
    cast_occupation slot n l i
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hgrade] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hgrade] using hpar.2.1
  have hL : (L : ℤ) % 2 = 1 := by simpa only [L, hgrade] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by simpa only [N, hgrade] using hpar.2.2.2
  have huGrade : u.val ∈ actualGrade ℒ leechUnit M := by
    rw [hu, show M = _ from occupationGrade_eq slot colour n l .P]
    exact wordAt_grade slot colour n l .P gP
  have hvGrade : v.val ∈ actualGrade ℒ leechUnit K := by
    rw [hv, show K = _ from occupationGrade_eq slot colour n l .Q]
    exact wordAt_grade slot colour n l .Q gQ
  have hwGrade : w.val ∈ actualGrade ℒ leechUnit L := by
    rw [hw, show L = _ from occupationGrade_eq slot colour n l .R]
    exact wordAt_grade slot colour n l .R gR
  have hbGrade : b.val ∈ actualGrade ℒ leechUnit N := by
    rw [hb, show N = _ from occupationGrade_eq slot colour n l .S]
    exact wordAt_grade slot colour n l .S gS
  by_cases hW : W = ((N : ℤ) - M - K - L - 6) / 2
  · subst W
    obtain ⟨hB, hD, hA⟩ := hhbb_graded_mode_sums M K L N u v w b huGrade hvGrade hwGrade
      hM hK hL hN q r (fun j => -bWeight r j) (dWeight r) (aWeight q)
    have hJacobi := (hhbb_marked_coefficient_jacobi_raw slot colour n l hl hpar
      u v w b gP gQ gR gS hu hv hw hb q 0 r).1
    rw [hhbbRawModeDefect_apply]
    simp only [neg_mul, finsum_neg_distrib] at hB
    rw [hB, hD, hA]
    simpa only [bWeight, dWeight, aWeight, neg_mul, mul_neg] using sub_eq_zero.mpr hJacobi
  · have htotal : 2 * W ≠ (N : ℤ) - M - K - L - 6 := by
      omega
    have hKL : Odd ((K : ℤ) + L) := Int.odd_iff.mpr (by omega)
    have hML : Odd ((M : ℤ) + L) := Int.odd_iff.mpr (by omega)
    have hMe : Even M := (Int.even_coe_nat M).mp (Int.even_iff.mpr hM)
    have hKe : Even K := (Int.even_coe_nat K).mp (Int.even_iff.mpr hK)
    have hB (j : ℕ) := bJointTerm_off_total M K L N u v w b
      huGrade hvGrade hwGrade hbGrade hKL 1 1 (bModes W q r j) (by dsimp only [bModes]; omega)
    have hD (j : ℕ) := bJointTerm_off_total K M L N v u w b
      hvGrade huGrade hwGrade hbGrade hML 1 1 (dModes W q j) (by dsimp only [dModes]; omega)
    have hA (j : ℕ) := aJointTerm_off_total M K L N u v w b
      huGrade hvGrade hwGrade hbGrade hMe hKe 1 1 (aModes W r j) (by dsimp only [aModes]; omega)
    simp only [hhbbRawModeDefect_apply, hB, hD, hA, mul_zero, finsum_zero, neg_zero, sub_zero]

/-- Raw scalar-mode Jacobi for the actual HHBB fields, uniformly in the four
twisted states and all integer mode selectors. The joint terms at roots one
are the literal scalar modes. -/
theorem hhbb_raw_scalar_mode_jacobi (u v : TwistedEven) (w b : TwistedOdd) (W q r : ℤ) :
    -(∑ᶠ j : ℕ, (-1 : ℂ) ^ j * ((Ring.choose r j : ℤ) : ℂ) *
        bJointTerm false false v w u b 1 1 (bModes W q r j)) -
      (∑ᶠ j : ℕ, (-1 : ℂ) ^ (r + (j : ℤ)) * ((Ring.choose r j : ℤ) : ℂ) *
        bJointTerm false false u w v b 1 1 (dModes W q j)) =
      ∑ᶠ j : ℕ, Ring.choose ((q : ℂ) - 1 / 2) j *
        aJointTerm u v w b 1 1 (aModes W r j) := by
  have h := hhbb_defect_eq_zero_of_marked (hhbbRawModeDefect W q r)
    (fun slot colour n l hl hpar u v w b gP gQ gR gS hu hv hw hb =>
      hhbb_raw_mode_defect_marked slot colour n l hl hpar u v w b gP gQ gR gS hu hv hw hb W q r)
    u v w b
  rw [hhbbRawModeDefect_apply, sub_eq_zero] at h
  exact h

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
