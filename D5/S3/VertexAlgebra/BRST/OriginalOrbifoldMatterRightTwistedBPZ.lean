/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterRightTwistedBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterRightTwistedBPZ
   mirror-E: none(waiver:algebraic-original-matter-field)
   anchors: []
   utility: none
   digest: Reverse mixed BPZ adjunction by finite inversion on the original Leech orbifold. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterTwistedBPZ

/-! Applying the forward mixed adjunction after each lowering gives a
factorial-weighted sum along the diagonals of the two lowering indices. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldMatterRightTwistedBPZ

open ActualLeechHyperbolic (leechData leech_spec)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockGradedTrace (actualTensorL0)
open OriginalOrbifoldCriticalMatter (Orbifold orbifoldMode orbifoldVertexAlgebra)
open OriginalOrbifoldMatterBPZ
open OriginalOrbifoldMatterTwistedBPZ (original_twisted_twisted_bpz)
open TwistedGround.MixedIntertwiner (fixedGrade lowering_integer_energy integer_energy_zero)

open private lowered lowered_pair lowered_val from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterTwistedBPZ
open private phase_even_shift from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube

private theorem orbifold_pairing_comm (x y : Orbifold) : orbifoldBPZ x y = orbifoldBPZ y x :=
  congrArg₂ (· + ·) (fixedBPZ_symmetric.eq x.1 y.1) (negativeBPZ_symmetric.eq x.2 y.2)

private theorem alternating_lowering (R : ℕ) (hR : 0 < R) (f : ℕ → ℂ) :
    (∑ q ∈ Finset.range R, ∑ p ∈ Finset.range (R - q),
      (-1 : ℂ) ^ q * (q.factorial : ℂ)⁻¹ * (p.factorial : ℂ)⁻¹ * f (q + p)) = f 0 := by
  rw [← Finset.sum_range_diag_flip]
  calc
    _ = ∑ k ∈ Finset.range R, ((-1 : ℂ) + 1) ^ k * (k.factorial : ℂ)⁻¹ * f k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [add_pow, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      have hqk : q ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
      have hfac : (k.choose q : ℂ) * (q.factorial : ℂ) * ((k - q).factorial : ℂ) =
          (k.factorial : ℂ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hqk
      have hq0 : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
      have hp0 : ((k - q).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - q)
      have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      rw [Nat.add_sub_of_le hqk, one_pow, mul_one]
      congr 1
      field_simp [hq0, hp0, hk0]
      rw [← hfac]
      ring
    _ = f 0 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro k _ hk
        simp [zero_pow hk]
      · exact fun h => (h (Finset.mem_range.mpr hR)).elim

set_option maxHeartbeats 4000000 in
-- Rewriting the two nested fields compares the literal orbifold mode carriers.
/-- The original twisted-on-fixed field against a twisted detector is BPZ adjoint
to the original two-twisted field of the finitely lowered source. -/
theorem original_right_twisted_bpz (H K : ℕ) (m d : ℤ)
    (u v : paritySpace leechData leech_spec.2.1 (-1))
    (huH : actualTensorL0 leechData leech_spec.2.1 u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 leechData leech_spec.2.1 v.val = (K : ℂ) • v.val)
    (a : fixedGrade leechData d) :
    let U : Orbifold := (0, u)
    let V : Orbifold := (0, v)
    let F : Orbifold := (⟨a.val, a.property.2⟩, 0)
    orbifoldBPZ (((orbifoldVertexAlgebra.stateField U)[[m]]) F) V =
      (-1 : ℂ) ^ (H : ℤ) * ∑ q ∈ Finset.range (H - 1),
        (q.factorial : ℂ)⁻¹ * orbifoldBPZ F
          (((orbifoldVertexAlgebra.stateField ((orbifoldMode 1 ^ q) U))[[
            2 * (H : ℤ) - (q : ℤ) - m - 2]]) V) := by
  by_cases hH : 2 ≤ H
  swap
  · have hu : u = 0 := Subtype.ext
      (integer_energy_zero leechData leech_spec.2.1 leech_spec.1 (H : ℤ) u.val
        (by simpa only [Int.cast_natCast] using huH) (by omega))
    dsimp only
    simp only [hu, show ((0, 0) : Orbifold) = 0 by rfl, show H - 1 = 0 by omega,
      map_zero, Pi.zero_apply, LinearMap.zero_apply, Finset.sum_range_zero, mul_zero]
  by_cases hK : 2 ≤ K
  swap
  · have hv : v = 0 := Subtype.ext
      (integer_energy_zero leechData leech_spec.2.1 leech_spec.1 (K : ℤ) v.val
        (by simpa only [Int.cast_natCast] using hvK) (by omega))
    dsimp only
    simp only [hv, show ((0, 0) : Orbifold) = 0 by rfl,
      map_zero, mul_zero, Finset.sum_const_zero]
  intro U V F
  let pairing (k : ℕ) : ℂ := orbifoldBPZ
    (((orbifoldVertexAlgebra.stateField ((orbifoldMode 1 ^ k) U))[[m - (k : ℤ)]]) F) V
  have hzero : pairing 0 = orbifoldBPZ (((orbifoldVertexAlgebra.stateField U)[[m]]) F) V := by
    simp [pairing, Module.End.one_apply]
  rw [← hzero]
  symm
  calc
    _ = ∑ q ∈ Finset.range (H - 1), ∑ p ∈ Finset.range (H - 1 - q),
        (-1 : ℂ) ^ q * (q.factorial : ℂ)⁻¹ * (p.factorial : ℂ)⁻¹ * pairing (q + p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hq' := Finset.mem_range.mp hq
      let n : ℤ := 2 * (H : ℤ) - (q : ℤ) - m - 2
      have hshift : (H : ℤ) - (q : ℤ) = ((H - q : ℕ) : ℤ) := by omega
      have huLower : actualTensorL0 leechData leech_spec.2.1 (lowered q u).val =
          ((H - q : ℕ) : ℂ) • (lowered q u).val := by
        simpa only [lowered_val, hshift, Int.cast_natCast] using
          (lowering_integer_energy leechData leech_spec.2.1 leech_spec.1 (H : ℤ) u.val
            (by simpa only [Int.cast_natCast] using huH) q)
      have forward := original_twisted_twisted_bpz (H - q) K n d
        (lowered q u) v huLower hvK a
      dsimp only at forward
      change (-1 : ℂ) ^ (H : ℤ) * ((q.factorial : ℂ)⁻¹ *
        orbifoldBPZ F (((orbifoldVertexAlgebra.stateField ((orbifoldMode 1 ^ q) U))[[n]]) V)) = _
      have hU : (orbifoldMode 1 ^ q) U = (0, lowered q u) := lowered_pair q u
      rw [hU, orbifold_pairing_comm F, forward]
      simp only [Finset.mul_sum, show H - q - 1 = H - 1 - q by omega]
      apply Finset.sum_congr rfl
      intro p _
      have hmode : 2 * ((H - q : ℕ) : ℤ) - (p : ℤ) - n - 2 = m - ((q + p : ℕ) : ℤ) := by
        rw [← hshift]
        dsimp only [n]
        omega
      have hlowering : (orbifoldMode 1 ^ p) ((0, lowered q u) : Orbifold) =
          (orbifoldMode 1 ^ (q + p)) U := by
        rw [← hU, ← Module.End.mul_apply, ← pow_add, Nat.add_comm p q]
      have hphase : (-1 : ℂ) ^ (H : ℤ) * (-1 : ℂ) ^ ((H - q : ℕ) : ℤ) = (-1 : ℂ) ^ q := by
        rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← hshift,
          show (H : ℤ) + ((H : ℤ) - (q : ℤ)) = (q : ℤ) + 2 * ((H : ℤ) - (q : ℤ)) by ring,
          phase_even_shift, zpow_natCast]
      rw [hmode, hlowering, orbifold_pairing_comm V]
      change _ = (-1 : ℂ) ^ q * (q.factorial : ℂ)⁻¹ * (p.factorial : ℂ)⁻¹ * pairing (q + p)
      rw [← hphase]
      dsimp only [pairing]
      ring
    _ = pairing 0 := alternating_lowering (H - 1) (by omega) pairing

#print axioms original_right_twisted_bpz

open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockFiniteCorrection (sourceWeight)
open LatticeInvolution (fixedSpace)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open TwistedGround
open TwistedGround.ActualChargedAdjoint (actualForm)
open TwistedGround.ActualPairingSymmetry (actualForm_symmetric)

open private originalL1 from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private actual_homogeneous_transpose from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi

private theorem fixed_lowering (j : ℕ) (a : fixedSpace leechData) :
    let F : Orbifold := (a, 0)
    (((orbifoldMode 1 ^ j) F).1.val = (originalL1 leechData ^ j) a.val) ∧
      (((orbifoldMode 1 ^ j) F).2.val = 0) := by
  dsimp only
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply]
      constructor
      · refine (OriginalOrbifoldConformal.L_fixed_apply leechData leech_spec.2.1
          leech_spec.2.2.1 1 _).trans ?_
        have hinv : actualInverse leechData = (gramComplex leechData)⁻¹ :=
          (Matrix.inv_eq_left_inv (actualInverse_left leechData leech_spec.2.1)).symm
        rw [hinv, ih.1]
      · refine (OriginalOrbifoldConformal.L_twisted_apply leechData leech_spec.2.1
          leech_spec.2.2.1 1 _).trans ?_
        rw [ih.2, map_zero]

set_option maxHeartbeats 2000000 in
-- Unfolding the restricted coefficient compares the native parity carriers.
private theorem fixed_field_pairing (m : ℤ) (a : fixedSpace leechData)
    (u v : paritySpace leechData leech_spec.2.1 (-1)) :
    orbifoldBPZ (((orbifoldVertexAlgebra.stateField (a, 0))[[m]]) (0, u)) (0, v) =
      actualForm leechData leech_spec.2.1
        ((correctedField leechData leech_spec.2.1 a.val).coeff (2 * (-m - 1)) u.val) v.val := by
  have field : ((orbifoldVertexAlgebra.stateField (a, 0))[[m]]) ((0, u) : Orbifold) =
      (LatticeInvolution.fixedMode leechData a m 0,
        ((fixedParitySlice leechData leech_spec.2.1 (-1) a)[[m]]) u) :=
    OriginalOrbifoldField.Y_fixed_ncoeff_apply leechData leech_spec.2.1 leech_spec.2.2.1 m a (0, u)
  rw [field, orbifoldBPZ_apply]
  simp only [Submodule.coe_zero, map_zero, zero_add, fixedParitySlice,
    VertexOperator.ncoeff_of_coeff, LinearMap.coe_restrict_apply]

set_option maxHeartbeats 4000000 in
-- The raw coefficient equalities use the underlying half-Fock carriers of the parity submodule.
/-- A homogeneous fixed source acts on the actual twisted sector with the finite
BPZ transpose given by its fixed-sector lowering powers. -/
theorem original_fixed_twisted_bpz (m d : ℤ) (a : fixedGrade leechData d)
    (u v : paritySpace leechData leech_spec.2.1 (-1)) :
    let U : Orbifold := (0, u)
    let V : Orbifold := (0, v)
    let F : Orbifold := (⟨a.val, a.property.2⟩, 0)
    let R := a.val.support.sup
      (fun c => MvPolynomial.weightedTotalDegree (sourceWeight leechData) (a.val c)) + 1
    orbifoldBPZ (((orbifoldVertexAlgebra.stateField F)[[m]]) U) V =
      (-1 : ℂ) ^ d * ∑ j ∈ Finset.range R,
        (j.factorial : ℂ)⁻¹ * orbifoldBPZ U
          (((orbifoldVertexAlgebra.stateField ((orbifoldMode 1 ^ j) F))[[
            2 * d - (j : ℤ) - m - 2]]) V) := by
  classical
  intro U V F R
  let e : ℤ := 2 * (-m - 1)
  let pairing (j : ℕ) : ℂ := actualForm leechData leech_spec.2.1 u.val
    ((correctedField leechData leech_spec.2.1 ((originalL1 leechData ^ j) a.val)).coeff
      (-e - 4 * d + 2 * (j : ℤ)) v.val)
  rw [fixed_field_pairing m (⟨a.val, a.property.2⟩ : fixedSpace leechData) u v,
    actual_homogeneous_transpose leechData leech_spec.2.1 d e a.val a.property.1, Finset.mul_sum]
  change (∑ᶠ j : ℕ, (((-1 : ℂ) ^ d) / (j.factorial : ℂ)) * pairing j) = _
  calc
    _ = ∑ j ∈ Finset.range R, (((-1 : ℂ) ^ d) / (j.factorial : ℂ)) * pairing j := by
      apply finsum_eq_sum_of_support_subset
      intro j hj
      by_contra outside
      have hRj : R ≤ j := Nat.le_of_not_gt
        (Finset.mem_range.not.mp (show j ∉ Finset.range R from outside))
      have hR : (originalL1 leechData ^ R) a.val = 0 :=
        SourceMobius.actual_sugawara_one_bound leechData leech_spec.2.1 a.val
      have tail : (originalL1 leechData ^ j) a.val = 0 := by
        rw [show j = (j - R) + R by omega, pow_add, Module.End.mul_apply, hR, map_zero]
      apply hj
      simp only [pairing, tail, map_zero, Pi.zero_apply, LinearMap.zero_apply, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      let Fj := (orbifoldMode 1 ^ j) F
      have hFj : (orbifoldMode 1 ^ j) F = (Fj.1, 0) :=
        Prod.ext rfl (Subtype.ext (fixed_lowering j F.1).2)
      have hmode : 2 * (-(2 * d - (j : ℤ) - m - 2) - 1) = -e - 4 * d + 2 * (j : ℤ) := by
        dsimp only [e]
        ring
      rw [orbifold_pairing_comm U, hFj, fixed_field_pairing, hmode, (fixed_lowering j F.1).1]
      dsimp only [pairing]
      rw [← (actualForm_symmetric leechData leech_spec.2.1).eq u.val, div_eq_mul_inv, mul_assoc]

#print axioms original_fixed_twisted_bpz

end D5.S3.VertexAlgebra.OriginalOrbifoldMatterRightTwistedBPZ
