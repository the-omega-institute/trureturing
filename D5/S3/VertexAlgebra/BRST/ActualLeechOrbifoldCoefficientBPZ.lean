/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCoefficientBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCoefficientBPZ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient transpose for all four original Leech orbifold blocks. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZ
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMixedBPZ
import Mathlib.Data.Nat.Choose.Sum
import Batteries.Tactic.OpenPrivate

/-! BPZ transpose for the original fixed, twisted, and mixed coefficient maps. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open LatticeInvolution (FixedCarrier fixedMode)
open LatticePositiveEnergy (grade actualL0_eigen_iff_grade)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open LatticeHalfFockGradedTrace (actualTensorL0)
open LatticeHalfFockCorrectedField (correctedField)
open TwistedGround
open TwistedGround.MixedIntertwiner (originalRightCoefficient
  lowering_integer_energy integer_energy_zero twice_signed_supported_factorial_contraction)
open TwistedGround.OriginalFourMChargeCoset (originalI)
open TwistedGround.Orbifold.OriginalMixedBPZ (twistedL1 original_mixed_bpz_finite)
open TwistedGround.Orbifold.OriginalOrbifoldField (Y_fixed_ncoeff_apply Y_ncoeff_apply)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_symmetric)
open ActualChargedAdjoint (actualForm)
open private actual_homogeneous_transpose from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
open private actualInputBasis actual_input_basis_expansion actual_input_basis_energy from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private twistedL1_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMixedBPZ
open private phase_even_shift from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
open private stress from D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation

private abbrev F := FixedCarrier leechData
private abbrev M := paritySpace leechData leechUnit (-1)
private abbrev I := originalI leechData leechUnit leechPosDef
private abbrev R := originalRightCoefficient leechData leechUnit
private abbrev Bf := sourcePairing leechData
private abbrev Bt := actualForm leechData leechUnit
private abbrev Lt := twistedL1 leechData leechUnit
private abbrev Et := actualTensorL0 leechData leechUnit
private abbrev Lf := fixedMode leechData (stress leechData) 2
private abbrev orbY :=
  TwistedGround.Orbifold.OriginalOrbifoldField.Y leechData leechUnit leechPosDef
private abbrev orbL := ActualLeechOrbifoldMatter.mode
private abbrev Ls := sugawaraMode leechData (gramComplex leechData)⁻¹ 1

private theorem lowered_twisted_energy (H : ℤ) (u : M)
    (hu : Et u.val = (H : ℂ) • u.val) (j : ℕ) :
    Et ((Lt ^ j) u).val = ((H - (j : ℤ) : ℤ) : ℂ) • ((Lt ^ j) u).val := by
  rw [twistedL1_pow_val]
  exact lowering_integer_energy leechData leechUnit leech_spec.1 H u.val hu j

private theorem twisted_tail (H : ℕ) (u : M) (hu : Et u.val = (H : ℂ) • u.val)
    (j : ℕ) (hj : H - 1 ≤ j) : (Lt ^ j) u = 0 := by
  apply Subtype.ext
  have h := lowered_twisted_energy (H : ℤ) u (by simpa only [Int.cast_natCast] using hu) j
  exact integer_energy_zero leechData leechUnit leech_spec.1 ((H : ℤ) - j)
    ((Lt ^ j) u).val h (by omega)

private theorem mixed_forward (H : ℕ) (n : ℤ) (u v : M) (a : F)
    (hu : Et u.val = (H : ℂ) • u.val) :
    Bf (I n u v).val a.val =
      (-1 : ℂ) ^ (H : ℤ) * ∑ j ∈ Finset.range (H - 1),
        (j.factorial : ℂ)⁻¹ * Bt v.val (R (2 * (H : ℤ) - n - j - 2) ((Lt ^ j) u) a).val := by
  classical
  let left : M →ₗ[ℂ] ℂ :=
    ((Bf a.val).comp (LatticeInvolution.fixedSpace leechData).subtype).comp (I n u)
  let right : M →ₗ[ℂ] ℂ :=
    (-1 : ℂ) ^ (H : ℤ) • ∑ j ∈ Finset.range (H - 1),
      (j.factorial : ℂ)⁻¹ •
        ((Bt (R (2 * (H : ℤ) - n - j - 2) ((Lt ^ j) u) a).val).comp
          (paritySpace leechData leechUnit (-1)).subtype)
  have eval (w : M) :
      right w = (-1 : ℂ) ^ (H : ℤ) * ∑ j ∈ Finset.range (H - 1),
        (j.factorial : ℂ)⁻¹ * Bt w.val (R (2 * (H : ℤ) - n - j - 2) ((Lt ^ j) u) a).val := by
    simp only [right, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, smul_eq_mul]
    apply congrArg (fun q : ℂ => (-1 : ℂ) ^ (H : ℤ) * q)
    apply Finset.sum_congr rfl
    intro j _
    rw [(ActualPairingSymmetry.actualForm_symmetric leechData leechUnit).eq
      (R (2 * (H : ℤ) - n - j - 2) ((Lt ^ j) u) a).val w.val]
  rw [sourcePairing_symmetric leechData (I n u v).val a.val, ← eval]
  change left v = right v
  rw [← actual_input_basis_expansion leechData leechUnit v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [eval]
  change Bf a.val (I n u (actualInputBasis leechData leechUnit v i)).val = _
  rw [sourcePairing_symmetric leechData a.val]
  exact original_mixed_bpz_finite leechData leechUnit leechPosDef leech_spec.1 H _
    n u (actualInputBasis leechData leechUnit v i) hu
    (actual_input_basis_energy leechData leechUnit leech_spec.1 v i) a

private theorem mixed_reverse (H : ℕ) (n : ℤ) (u v : M) (a : F)
    (hu : Et u.val = (H : ℂ) • u.val) :
    Bt (R n u a).val v.val =
      (-1 : ℂ) ^ (H : ℤ) * ∑ j ∈ Finset.range (H - 1),
        (j.factorial : ℂ)⁻¹ * Bf a.val (I (2 * (H : ℤ) - n - j - 2) ((Lt ^ j) u) v).val := by
  classical
  by_cases hH : H < 2
  · have hz := twisted_tail H u hu 0 (by omega)
    simp only [pow_zero, Module.End.one_apply] at hz
    subst u
    simp
  let N := H - 1
  let f (s : ℕ) : ℂ := Bt v.val (R (n - s) ((Lt ^ s) u) a).val
  have tail (s : ℕ) (hs : N ≤ s) : f s = 0 := by
    simp [f, twisted_tail H u hu s hs]
  rw [(ActualPairingSymmetry.actualForm_symmetric leechData leechUnit).eq (R n u a).val v.val]
  have leading : f 0 = Bt v.val (R n u a).val := by simp [f]
  rw [← leading]
  have term (j : ℕ) (hj : j ∈ Finset.range N) :
      (-1 : ℂ) ^ (H : ℤ) * ((j.factorial : ℂ)⁻¹ *
        Bf a.val (I (2 * (H : ℤ) - n - j - 2) ((Lt ^ j) u) v).val) =
      ∑ k ∈ Finset.range N, ((j.factorial : ℂ)⁻¹ * (k.factorial : ℂ)⁻¹) *
        ((-1 : ℂ) ^ j * f (j + k)) := by
    have hj' : j < H - 1 := Finset.mem_range.mp hj
    let Q := H - j
    let m : ℤ := 2 * (H : ℤ) - n - j - 2
    have hQ : (Q : ℤ) = (H : ℤ) - j := by dsimp [Q]; omega
    have hE : Et ((Lt ^ j) u).val = (Q : ℂ) • ((Lt ^ j) u).val := by
      have h := lowered_twisted_energy (H : ℤ) u (by simpa only [Int.cast_natCast] using hu) j
      rw [← hQ, Int.cast_natCast] at h
      exact h
    change (-1 : ℂ) ^ (H : ℤ) * ((j.factorial : ℂ)⁻¹ *
        Bf a.val (I m ((Lt ^ j) u) v).val) = _
    rw [sourcePairing_symmetric leechData a.val,
      mixed_forward Q m ((Lt ^ j) u) v a hE]
    simp only [Finset.mul_sum]
    calc
      _ = ∑ k ∈ Finset.range (Q - 1),
          ((j.factorial : ℂ)⁻¹ * (k.factorial : ℂ)⁻¹) *
            ((-1 : ℂ) ^ j * f (j + k)) := by
        apply Finset.sum_congr rfl
        intro k _
        have hindex : 2 * (Q : ℤ) - m - k - 2 = n - ((j + k : ℕ) : ℤ) := by
          dsimp [m]
          omega
        have hpower : (Lt ^ k) ((Lt ^ j) u) = (Lt ^ (j + k)) u := by
          rw [Nat.add_comm j k, pow_add, Module.End.mul_apply]
        have hsign : (-1 : ℂ) ^ (H : ℤ) * (-1 : ℂ) ^ (Q : ℤ) = (-1 : ℂ) ^ j := by
          rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_natCast,
            show (H : ℤ) + (Q : ℤ) = (j : ℤ) + 2 * (Q : ℤ) by omega,
            phase_even_shift]
        rw [hindex, hpower]
        change (-1 : ℂ) ^ (H : ℤ) * ((j.factorial : ℂ)⁻¹ *
          ((-1 : ℂ) ^ (Q : ℤ) * ((k.factorial : ℂ)⁻¹ * f (j + k)))) = _
        rw [← hsign]
        ring
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by dsimp [Q, N]; omega))
        intro k _ hk
        have hk' := Finset.mem_range.not.mp hk
        rw [tail (j + k) (by dsimp [Q] at hk'; dsimp [N]; omega), mul_zero, mul_zero]
  symm
  rw [Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ((j.factorial : ℂ)⁻¹ * (k.factorial : ℂ)⁻¹) *
          ((-1 : ℂ) ^ j * f (j + k)) := Finset.sum_congr rfl term
    _ = ∑ s ∈ Finset.range (2 * N), ∑ j ∈ Finset.range (s + 1),
        (Ring.choose (s : ℂ) j / (s.factorial : ℂ)) * ((-1 : ℂ) ^ j * f s) := by
      rw [twice_signed_supported_factorial_contraction N (fun j k => (-1 : ℂ) ^ j * f (j + k))
        (fun j k hjk => by rw [tail (j + k) (by omega), mul_zero])]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.add_sub_of_le (by have := Finset.mem_range.mp hj; omega)]
    _ = f 0 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro s _ hs
        have halt : (∑ j ∈ Finset.range (s + 1), (-1 : ℂ) ^ j * (s.choose j : ℂ)) = 0 := by
          have haltInt := Int.alternating_sum_range_choose_of_ne hs
          simpa only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
            Int.cast_one, Int.cast_natCast, Int.cast_zero] using
            congrArg (fun q : ℤ => (q : ℂ)) haltInt
        calc
          _ = (∑ j ∈ Finset.range (s + 1), (-1 : ℂ) ^ j * (s.choose j : ℂ)) *
                ((s.factorial : ℂ)⁻¹ * f s) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Ring.choose_natCast]
            ring
          _ = 0 := by rw [halt, zero_mul]
      · intro h
        exact (h (Finset.mem_range.mpr (by dsimp [N]; omega))).elim

private theorem orbL1_apply (x : Orbifold) :
    orbL 1 x = (Lf x.1, Lt x.2) := by
  change ((orbY (stress leechData, 0))[[2]]) x = _
  rw [Y_fixed_ncoeff_apply]
  rfl

private theorem orbL1_pow (j : ℕ) (x : Orbifold) :
    (orbL 1 ^ j) x = ((Lf ^ j) x.1, (Lt ^ j) x.2) := by
  induction j with
  | zero => exact Prod.ext rfl rfl
  | succ j ih => simp only [pow_succ', Module.End.mul_apply, orbL1_apply, ih]

private theorem fixedL1_pow_val (j : ℕ) (u : F) :
    ((Lf ^ j) u).val = (Ls ^ j) u.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h := congrArg Prod.fst (ActualLeechOrbifoldMatter.mode_apply 1 ((Lf ^ j) u, 0))
    rw [orbL1_apply, ← Matrix.inv_eq_left_inv (actualInverse_left leechData leechUnit)] at h
    simpa only [pow_succ', Module.End.mul_apply, ih] using h

private theorem orbifold_bpz_finsum (h n : ℤ) (x y z : Orbifold) (N : ℕ)
    (hN : ∀ j : ℕ, N ≤ j → (orbL 1 ^ j) x = 0)
    (finite :
      orbifoldPairing (((orbY x)[[n]]) y) z =
        (-1 : ℂ) ^ h * ∑ j ∈ Finset.range N,
          (j.factorial : ℂ)⁻¹ *
            orbifoldPairing y (((orbY ((orbL 1 ^ j) x))[[2 * h - n - j - 2]]) z)) :
    orbifoldPairing (((orbY x)[[n]]) y) z =
      (-1 : ℂ) ^ h * ∑ᶠ j : ℕ, (j.factorial : ℂ)⁻¹ *
        orbifoldPairing y (((orbY ((orbL 1 ^ j) x))[[2 * h - n - j - 2]]) z) := by
  rw [finite]
  congr 1
  symm
  apply finsum_eq_sum_of_support_subset
  intro j hj
  apply Finset.mem_range.mpr
  by_contra hout
  exact hj (by simp [hN j (Nat.le_of_not_gt hout)])

set_option maxHeartbeats 4000000 in
-- Both fixed-source field realizations reduce through their coefficient maps.
private theorem fixed_bpz (h n : ℤ) (u : F) (hu : u.val ∈ grade leechData h) (y z : Orbifold) :
    orbifoldPairing (((orbY (u, 0))[[n]]) y) z =
      (-1 : ℂ) ^ h * ∑ᶠ j : ℕ, (j.factorial : ℂ)⁻¹ *
        orbifoldPairing y (((orbY ((orbL 1 ^ j) (u, 0)))[[2 * h - n - j - 2]]) z) := by
  classical
  let A := u.val.support.sup (fun a => MvPolynomial.weightedTotalDegree
    (LatticeHalfFockFiniteCorrection.sourceWeight leechData) (u.val a)) + 1
  have tail (j : ℕ) (hj : A ≤ j) : (Ls ^ j) u.val = 0 :=
    Module.End.pow_map_zero_of_le hj (SourceMobius.actual_sugawara_one_bound
      leechData leechUnit u.val)
  apply orbifold_bpz_finsum h n (u, 0) y z A
  · intro j hj
    have hz : (Lf ^ j) u = 0 := Subtype.ext ((fixedL1_pow_val j u).trans (tail j hj))
    simp only [orbL1_pow, hz, map_zero]
    rfl
  have hfixed (k : ℤ) (a b : F) :
      (fixedMode leechData a k b).val = ((LatticeAllStateField.Y leechData a.val)[[k]]) b.val := rfl
  have htwisted (k : ℤ) (a : F) (b : M) :
      (((fixedParitySlice leechData leechUnit (-1) a)[[k]]) b).val =
        (correctedField leechData leechUnit a.val).coeff (-2 * k - 2) b.val := by
    change (correctedField leechData leechUnit a.val).coeff (2 * (-k - 1)) b.val = _
    rw [show 2 * (-k - 1) = -2 * k - 2 by ring]
  have ff := SourceBPZ.AllStateTranspose.sourcePairing_allState leechData leechUnit
    h n u.val hu y.1.val z.1.val
  have ff' :
      Bf (fixedMode leechData u n y.1).val z.1.val =
        (-1 : ℂ) ^ h * ∑ j ∈ Finset.range A, (j.factorial : ℂ)⁻¹ *
          Bf y.1.val (fixedMode leechData ((Lf ^ j) u) (2 * h - n - j - 2) z.1).val := by
    simp_rw [show ∀ j : ℕ, 2 * h - (j : ℤ) - n - 2 = 2 * h - n - j - 2 from
      fun j => by ring] at ff
    simpa only [A, hfixed, fixedL1_pow_val] using ff
  let g (j : ℕ) : ℂ :=
    ((-1 : ℂ) ^ h / (j.factorial : ℂ)) *
      Bt y.2.val ((correctedField leechData leechUnit ((Ls ^ j) u.val)).coeff
        (-(-2 * n - 2) - 4 * h + 2 * (j : ℤ)) z.2.val)
  have gsupport : Function.support g ⊆ (Finset.range A : Set ℕ) := by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hout
    exact hj (by simp [g, tail j (Nat.le_of_not_gt hout)])
  have ft := actual_homogeneous_transpose leechData leechUnit
    h (-2 * n - 2) u.val hu y.2.val z.2.val
  change _ = ∑ᶠ j : ℕ, g j at ft
  rw [finsum_eq_sum_of_support_subset g gsupport] at ft
  have ft' :
      Bt (((fixedParitySlice leechData leechUnit (-1) u)[[n]]) y.2).val z.2.val =
        (-1 : ℂ) ^ h * ∑ j ∈ Finset.range A, (j.factorial : ℂ)⁻¹ *
          Bt y.2.val (((fixedParitySlice leechData leechUnit (-1) ((Lf ^ j) u))
            [[2 * h - n - j - 2]]) z.2).val := by
    rw [htwisted, ft, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [htwisted, fixedL1_pow_val]
    dsimp only [g]
    rw [show -(-2 * n - 2) - 4 * h + 2 * (j : ℤ) =
      -2 * (2 * h - n - (j : ℤ) - 2) - 2 by ring]
    ring
  simp only [orbL1_pow, map_zero, Y_fixed_ncoeff_apply, orbifoldPairing_apply,
    mul_add, Finset.sum_add_distrib, ff', ft']

set_option maxHeartbeats 4000000 in
-- Elaborating the literal odd coefficient maps requires their subtype coercions.
private theorem twisted_bpz (H : ℕ) (n : ℤ) (u : M) (hu : Et u.val = (H : ℂ) • u.val)
    (y z : Orbifold) :
    orbifoldPairing (((orbY (0, u))[[n]]) y) z =
      (-1 : ℂ) ^ (H : ℤ) * ∑ᶠ j : ℕ, (j.factorial : ℂ)⁻¹ *
        orbifoldPairing y (((orbY ((orbL 1 ^ j) (0, u)))[[2 * (H : ℤ) - n - j - 2]]) z) := by
  apply orbifold_bpz_finsum (H : ℤ) n (0, u) y z (H - 1)
  · intro j hj
    simp only [orbL1_pow, map_zero, twisted_tail H u hu j hj]
    rfl
  have coeff (k : ℤ) (a : M) (b : Orbifold) :
      ((orbY (0, a))[[k]]) b = (I k a b.2, R k a b.1) := by
    rw [Y_ncoeff_apply]
    rw [show (fixedMode leechData 0 k) = 0 by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change ((LatticeAllStateField.Y leechData 0)[[k]]) v.val = 0
      simp]
    simp only [LinearMap.zero_apply, zero_add]
    have hz : (((fixedParitySlice leechData leechUnit (-1) (0 : F))[[k]]) b.2) = 0 := by
      apply Subtype.ext
      change (correctedField leechData leechUnit 0).coeff (2 * (-k - 1)) b.2.val = 0
      simp
    rw [hz, zero_add]
  simp only [orbL1_pow, map_zero, coeff, orbifoldPairing_apply, mul_add, Finset.sum_add_distrib]
  rw [mixed_forward H n u y.2 z.1 hu, mixed_reverse H n u z.2 y.1 hu]
  ring

/-
proof_shape: orbifoldPairing_coefficient_transpose: content

The literal stress powers act separately on the two sectors. The coefficient
identity uses the source all-state transpose, the corrected adjoint, and the
two mutually inverse mixed transposes on the actual sector carrier.
-/
set_option maxHeartbeats 4000000 in
-- Finite support and sector splitting compare the original coefficient maps.
/-- The original orbifold coefficient transposes on the concrete BPZ form.
The source is any integer (L_0) eigenstate, and both other slots are arbitrary. -/
theorem orbifoldPairing_coefficient_transpose (h n : ℤ) (x y z : Orbifold)
    (hx : ActualLeechOrbifoldMatter.mode 0 x = (h : ℂ) • x) :
    orbifoldPairing (((orbY x)[[n]]) y) z =
      (-1 : ℂ) ^ h * ∑ᶠ j : ℕ, (j.factorial : ℂ)⁻¹ *
        orbifoldPairing y (((orbY ((ActualLeechOrbifoldMatter.mode 1 ^ j) x))
          [[2 * h - n - j - 2]]) z) := by
  classical
  have hmode := ActualLeechOrbifoldMatter.mode_apply 0 x
  rw [hx] at hmode
  have hf := (congrArg Prod.fst hmode).symm
  change sugawaraMode leechData (actualInverse leechData) 0 x.1.val = (h : ℂ) • x.1.val at hf
  have hg : x.1.val ∈ grade leechData h :=
    (actualL0_eigen_iff_grade leechData _ (actualInverse_left leechData leechUnit)
      (HalfFockSpectralFiberSource.actualInverse_right leechData leechUnit) h x.1.val).mp hf
  have ht := (congrArg Prod.snd hmode).symm
  change Et x.2.val = (h : ℂ) • x.2.val at ht
  have fo := fixed_bpz h n x.1 hg y z
  have twisted :
      orbifoldPairing (((orbY (0, x.2))[[n]]) y) z =
        (-1 : ℂ) ^ h * ∑ᶠ j : ℕ, (j.factorial : ℂ)⁻¹ *
          orbifoldPairing y (((orbY ((orbL 1 ^ j) (0, x.2)))[[2 * h - n - j - 2]]) z) := by
    by_cases hh : 0 ≤ h
    · have he : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh
      have hE : Et x.2.val = (h.toNat : ℂ) • x.2.val := by
        rw [← he, Int.cast_natCast] at ht
        exact ht
      simpa only [he] using twisted_bpz h.toNat n x.2 hE y z
    · have hz : x.2 = 0 := Subtype.ext
        (integer_energy_zero leechData leechUnit leech_spec.1 h x.2.val ht (by omega))
      rw [hz, show ((0, 0) : Orbifold) = 0 from rfl]
      simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, mul_zero, finsum_zero]
  let term (w : Orbifold) (j : ℕ) : ℂ :=
    (j.factorial : ℂ)⁻¹ * orbifoldPairing y (((orbY ((orbL 1 ^ j) w))[[2 * h - n - j - 2]]) z)
  have finite (w : Orbifold) (N : ℕ) (tail : ∀ j : ℕ, N ≤ j → (orbL 1 ^ j) w = 0) :
      Function.HasFiniteSupport (term w) := by
    apply (Finset.range N).finite_toSet.subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hN
    exact hj (by simp [term, tail j (Nat.le_of_not_gt hN)])
  let A := x.1.val.support.sup (fun a => MvPolynomial.weightedTotalDegree
    (LatticeHalfFockFiniteCorrection.sourceWeight leechData) (x.1.val a)) + 1
  have ffinite : Function.HasFiniteSupport (term ((x.1, 0) : Orbifold)) := by
    apply finite _ A
    intro j hj
    have hz : (Lf ^ j) x.1 = 0 := by
      apply Subtype.ext
      rw [fixedL1_pow_val]
      exact Module.End.pow_map_zero_of_le hj (SourceMobius.actual_sugawara_one_bound
        leechData leechUnit x.1.val)
    simp only [orbL1_pow, hz, map_zero]
    rfl
  have tfinite : Function.HasFiniteSupport (term ((0, x.2) : Orbifold)) := by
    apply finite _ h.toNat
    intro j hj
    have hz : (Lt ^ j) x.2 = 0 := Subtype.ext
      (integer_energy_zero leechData leechUnit leech_spec.1 (h - (j : ℤ))
        ((Lt ^ j) x.2).val (lowered_twisted_energy h x.2 ht j) (by omega))
    simp only [orbL1_pow, hz, map_zero]
    rfl
  let a : Orbifold := (x.1, 0)
  let b : Orbifold := (0, x.2)
  have hab : a + b = x := by ext <;> simp [a, b]
  rw [← hab]
  have hmodeadd : ((orbY (a + b))[[n]]) y = ((orbY a)[[n]]) y + ((orbY b)[[n]]) y := by
    change (VertexOperator.ncoeff (orbY (a + b)) n) y = _
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
  rw [hmodeadd, map_add orbifoldPairing, LinearMap.add_apply, fo, twisted, ← mul_add]
  change _ * ((∑ᶠ j : ℕ, term a j) + ∑ᶠ j : ℕ, term b j) = _ * ∑ᶠ j : ℕ, term (a + b) j
  rw [← finsum_add_distrib ffinite tfinite]
  congr 1
  apply finsum_congr
  intro j
  change _ = term (a + b) j
  simp only [term, a, b, map_add, Pi.add_apply, LinearMap.add_apply, mul_add]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ
