/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldAbsoluteQTranspose
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldAbsoluteQTranspose
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Statewise finite BPZ transposition of the original Leech orbifold BRST charge. -/

import D5.S3.Quantum.Fermionic.BcGhostBRSTHermitian
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZ
import D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose
import D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
import Batteries.Tactic.OpenPrivate

/-! The literal BRST charge transposes for the native complex-bilinear BPZ form. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open BcGhostBilinear (Bg Bg_c kappa kappa_b kappa_c)
open BcGhostBRST (cubic cubicTerm cubicTerm_finite Qg Hg_Qg)
open private cubic_eq from D5.S3.Quantum.Fermionic.BcGhostCubic
open private kappa_add kappa_smul from D5.S3.Quantum.Fermionic.BcGhostBilinear

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (Orbifold leechUnit)
open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane hyperbolicMatter)
open LatticeGeneratingFieldLocality (Carrier Charge LatticeData)
open LatticeAllStateField (Y)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open LatticePositiveEnergy (grade mem_grade_iff energy oscillatorEnergy)
open LatticeHalfFockFiniteCorrection (sourceWeight)
open HalfFockSpectralFiberSource (actualInverse_left)
open SourceMobius (gram_det_unit sugawara_pow_single)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open SourceBPZ.AllStateTranspose (sourcePairing_allState)
open LatticeActualConformalState (conformalPolynomial omega_modes)
open private conformal_polynomial_homogeneous conformal_polynomial_lowering actual_stress_transpose
  from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private plane_inverse from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private tensor_transpose from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZ

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

private theorem kappa_cubic (p q : ℤ) (x : Fock) :
    kappa (cubic p q x) = cubic p q (kappa x) := by
  by_cases h : -p-q ≤ -2 <;>
    simp only [cubic_eq, h, ite_true, ite_false, Module.End.mul_apply, kappa_b, kappa_c]

private theorem kappa_cubicTerm (pq : ℤ × ℤ) (x : Fock) :
    kappa (cubicTerm pq x) = cubicTerm pq (kappa x) := by
  have h : star ((1/2 : ℂ) * ((pq.1-pq.2 : ℤ) : ℂ)) =
      (1/2 : ℂ) * ((pq.1-pq.2 : ℤ) : ℂ) := by
    change (starRingEnd ℂ) ((1/2 : ℂ) * ((pq.1-pq.2 : ℤ) : ℂ)) = _
    rw [map_mul, map_div₀, map_one, map_ofNat, map_intCast]
  simp only [cubicTerm, LinearMap.smul_apply, kappa_smul, h, kappa_cubic]

/-- Occupation conjugation fixes the actual statewise finite, weighted cubic charge. -/
private theorem kappa_Qg (x : Fock) : kappa (Qg x) = Qg (kappa x) := by
  let K : Fock →+ Fock :=
    { toFun := kappa
      map_zero' := by
        ext S
        simp
      map_add' := kappa_add }
  change K (∑ᶠ pq : ℤ × ℤ, cubicTerm pq x) =
    ∑ᶠ pq : ℤ × ℤ, cubicTerm pq (kappa x)
  rw [K.map_finsum (cubicTerm_finite x)]
  exact finsum_congr (fun pq => kappa_cubicTerm pq x)

/-- The ordinary cubic ghost BRST transpose for the native complex-bilinear form. -/
private theorem Bg_Qg (x y : Fock) : Bg (Qg x) y = Bg x (Qg y) := by
  change BcGhostHermitian.Hg (kappa (Qg x)) y = BcGhostHermitian.Hg (kappa x) (Qg y)
  rw [kappa_Qg, Hg_Qg]

/-- The all-state lattice BPZ law on its neutral quadratic stress state.
Its Möbius sum collapses because the actual positive mode kills the state. -/
private theorem lattice_stress_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℤ) (x y : Carrier D) :
    sourcePairing D (sugawaraMode D (gramComplex D)⁻¹ n x) y =
      sourcePairing D x (sugawaraMode D (gramComplex D)⁻¹ (-n) y) := by
  classical
  let H := (gramComplex D)⁻¹
  let p := conformalPolynomial D H
  let w := LatticeActualConformalState.omega D H
  have hgrade : w ∈ grade D 2 := by
    rw [mem_grade_iff]
    intro a ha
    change ((Finsupp.single (0 : Charge D) p) a.1).coeff a.2 = 0
    by_cases h : (0 : Charge D) = a.1
    · rw [Finsupp.single_apply, ite_eq_left h]
      by_contra hc
      have hw : oscillatorEnergy a.2 = 2 := conformal_polynomial_homogeneous D H hc
      exact ha (by simp [energy, ← h, hw])
    · simp [h]
  have hG := gram_det_unit D hu
  have hone : sugawaraMode D H 1 w = 0 := by
    change sugawaraMode D H 1 (Finsupp.single 0 p) = 0
    have hp : (SourceMobius.sectorL1 D 0).toLinearMap p = 0 :=
      conformal_polynomial_lowering D H
    have h := sugawara_pow_single D H (Matrix.nonsing_inv_mul _ hG)
      (Matrix.mul_nonsing_inv _ hG) 0 p 1
    simpa only [pow_one, hp, Finsupp.single_zero] using h
  have hpower (j : ℕ) (hj : j ≠ 0) : (sugawaraMode D H 1 ^ j) w = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, hone, map_zero]
  let R := w.support.sup (fun a => MvPolynomial.weightedTotalDegree (sourceWeight D) (w a))
  have hcollapse :
      (∑ j ∈ Finset.range (R+1), (j.factorial : ℂ)⁻¹ *
        sourcePairing D x (((Y D ((sugawaraMode D H 1 ^ j) w))
          [[2*(2 : ℤ)-(j : ℤ)-(n+1)-2]]) y)) =
        sourcePairing D x (sugawaraMode D H (-n) y) := by
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero,
        Module.End.one_apply, Nat.cast_zero,
        show 2*(2 : ℤ)-0-(n+1)-2 = -n+1 by omega, w, omega_modes]
    · intro j _ hj
      rw [hpower j hj]
      simp
    · simp
  have h := sourcePairing_allState D hu 2 (n+1) w hgrade x y
  rw [hcollapse, show (-1 : ℂ)^(2 : ℤ) = 1 by norm_num, one_mul] at h
  simpa only [w, omega_modes] using h

/-- The stress coefficients of the original fixed and negative twisted sectors
transpose on the two diagonal blocks of the explicit orbifold form. -/
private theorem orbifoldPairing_mode (n : ℤ) (x y : Orbifold) :
    orbifoldPairing (ActualLeechOrbifoldMatter.mode n x) y =
      orbifoldPairing x (ActualLeechOrbifoldMatter.mode (-n) y) := by
  have hx := ActualLeechOrbifoldMatter.mode_apply n x
  have hy := ActualLeechOrbifoldMatter.mode_apply (-n) y
  have hxf := congrArg Prod.fst hx
  have hxt := congrArg Prod.snd hx
  have hyf := congrArg Prod.fst hy
  have hyt := congrArg Prod.snd hy
  dsimp only at hxf hxt hyf hyt
  have hfixed := lattice_stress_transpose leechData leechUnit n x.1.val y.1.val
  rw [Matrix.inv_eq_left_inv (actualInverse_left leechData leechUnit)] at hfixed
  have htwisted := actual_stress_transpose leechData leechUnit n x.2.val y.2.val
  rw [orbifoldPairing_apply, orbifoldPairing_apply, hxf, hxt, hyf, hyt]
  exact congrArg₂ (· + ·) hfixed htwisted

private theorem planePairing_mode (n : ℤ) (x y : Carrier hyperbolicPlane) :
    sourcePairing hyperbolicPlane (hyperbolicMatter.mode n x) y =
      sourcePairing hyperbolicPlane x (hyperbolicMatter.mode (-n) y) := by
  have hu : IsUnit hyperbolicPlane.G.det := by
    change IsUnit OrderedHyperbolicExtension.U.det
    exact Matrix.isUnit_det_of_left_inverse OrderedHyperbolicExtension.U_mul_U
  change sourcePairing hyperbolicPlane (sugawaraMode hyperbolicPlane
      (gramComplex hyperbolicPlane) n x) y =
    sourcePairing hyperbolicPlane x (sugawaraMode hyperbolicPlane
      (gramComplex hyperbolicPlane) (-n) y)
  simpa only [Matrix.inv_eq_left_inv plane_inverse] using
    lattice_stress_transpose hyperbolicPlane hu n x y

/-
proof_shape: matterPairing_mode: content
The actual lattice inversion is evaluated on the weight-two stress state, and
the resulting fixed, twisted and hyperbolic transposes are combined on the
original critical matter tensor. The stress acts diagonally on orbifold matter.
-/
/-- The actual critical matter Virasoro modes transpose by index negation. -/
theorem matterPairing_mode (n : ℤ) (x y : Matter) :
    matterPairing (matter.mode n x) y = matterPairing x (matter.mode (-n) y) := by
  let L := ActualLeechOrbifoldMatter.mode
  let U := hyperbolicMatter.mode
  let Iorb : Module.End ℂ Orbifold := LinearMap.id
  let Iplane : Module.End ℂ (Carrier hyperbolicPlane) := LinearMap.id
  change matterPairing ((TensorProduct.map (L n) Iplane +
      TensorProduct.map Iorb (U n)) x) y =
    matterPairing x ((TensorProduct.map (L (-n)) Iplane +
      TensorProduct.map Iorb (U (-n))) y)
  have hL := tensor_transpose orbifoldPairing (sourcePairing hyperbolicPlane)
    (L n) (L (-n)) Iplane Iplane (orbifoldPairing_mode n) (fun _ _ => rfl) x y
  have hU := tensor_transpose orbifoldPairing (sourcePairing hyperbolicPlane)
    Iorb Iorb (U n) (U (-n)) (fun _ _ => rfl) (planePairing_mode n) x y
  simp only [matterPairing, LinearMap.add_apply, map_add, hL, hU]

private theorem absolutePairing_summand (n : ℤ) (x y : ComplexState) :
    absolutePairing (VirasoroBRST.summand matter n x) y =
      absolutePairing x (VirasoroBRST.summand matter (-n) y) := by
  simpa only [absolutePairing, VirasoroBRST.summand, neg_neg] using
    tensor_transpose matterPairing Bg (matter.mode n) (matter.mode (-n))
      (BcGhostFock.c (-n)) (BcGhostFock.c n) (matterPairing_mode n)
      (fun u v => by simpa only [neg_neg] using Bg_c (-n) u v) x y

-- The finite reindexing follows LatticeMatterGhostHermitian.Hmg_T.
private theorem symmetric_capture (x y : ComplexState) :
    ∃ s : Finset ℤ,
      (Function.support (fun n => VirasoroBRST.summand matter n x) ⊆ (s : Set ℤ)) ∧
      (Function.support (fun n => VirasoroBRST.summand matter n y) ⊆ (s : Set ℤ)) ∧
      (∀ n ∈ s, -n ∈ s) := by
  classical
  obtain ⟨u, hu⟩ := VirasoroBRST.common_capture matter {x, y}
  let s := u ∪ u.image (fun n : ℤ => -n)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro n hn
    exact Finset.mem_union_left _ (hu x (by simp) hn)
  · intro n hn
    exact Finset.mem_union_left _ (hu y (by simp) hn)
  · intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, h, rfl⟩)
    · rcases Finset.mem_image.mp h with ⟨k, hk, hkn⟩
      rw [← hkn, neg_neg]
      exact Finset.mem_union_left _ hk

/-- The matter-c coupling transposes after reindexing a common finite capture. -/
private theorem absolutePairing_T (x y : ComplexState) :
    absolutePairing (VirasoroBRST.T matter x) y =
      absolutePairing x (VirasoroBRST.T matter y) := by
  classical
  obtain ⟨s, hx, hy, hs⟩ := symmetric_capture x y
  rw [VirasoroBRST.finite_capture matter x s hx, VirasoroBRST.finite_capture matter y s hy]
  calc
    _ = ∑ n ∈ s, absolutePairing (VirasoroBRST.summand matter n x) y :=
      map_sum (absolutePairing.flip y) _ _
    _ = ∑ n ∈ s, absolutePairing x (VirasoroBRST.summand matter (-n) y) := by
      apply Finset.sum_congr rfl
      intro n _
      exact absolutePairing_summand n x y
    _ = ∑ n ∈ s, absolutePairing x (VirasoroBRST.summand matter n y) := by
      apply Finset.sum_bij (fun n _ => -n)
      · exact hs
      · intro n _ k _ h
        exact neg_injective h
      · intro n hn
        exact ⟨-n, hs n hn, neg_neg n⟩
      · intro n _
        rfl
    _ = _ := (map_sum (absolutePairing x) _ _).symm

private theorem absolutePairing_ghostCharge (x y : ComplexState) :
    absolutePairing (VirasoroBRST.ghostCharge matter x) y =
      absolutePairing x (VirasoroBRST.ghostCharge matter y) :=
  tensor_transpose matterPairing Bg LinearMap.id LinearMap.id Qg Qg
    (fun _ _ => rfl) Bg_Qg x y

/-
proof_shape: absolutePairing_Q: content
The native matter and ghost transposes enter the sign-reversal bijection on a
common capture for both states. The independent cubic ghost charge uses the
original Hermitian adjoint with occupation coefficient conjugation removed.
-/
/-- The normalized absolute BRST charge equals its transpose on the original
Leech orbifold matter-ghost complex with the explicit bilinear BPZ form. -/
theorem absolutePairing_Q (x y : ComplexState) :
    absolutePairing (Q x) y = absolutePairing x (Q y) := by
  change absolutePairing (VirasoroBRST.T matter x + VirasoroBRST.ghostCharge matter x) y =
    absolutePairing x (VirasoroBRST.T matter y + VirasoroBRST.ghostCharge matter y)
  simp only [map_add, LinearMap.add_apply, absolutePairing_T, absolutePairing_ghostCharge]

#print axioms matterPairing_mode
#print axioms absolutePairing_Q

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ
