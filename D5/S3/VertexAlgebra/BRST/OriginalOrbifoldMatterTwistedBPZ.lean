/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterTwistedBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterTwistedBPZ
   mirror-E: none(waiver:algebraic-original-matter-field)
   anchors: []
   utility: none
   digest: BPZ adjunction of the original two-negative-twisted field against a fixed state. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterBPZ
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
import Batteries.Tactic.OpenPrivate

/-! The fixed-source inverse pairing and the right skew expansion give the
same finite contraction on the original Leech orbifold. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldMatterTwistedBPZ

open ActualLeechHyperbolic (leechData leech_spec)
open OriginalOrbifoldCriticalMatter (Orbifold orbifoldMode orbifoldVertexAlgebra)
open OriginalOrbifoldMatterBPZ (orbifoldBPZ orbifoldBPZ_apply)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open SourceBPZ.SourcePairingLaws (sourcePairing_grade)
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open LatticeHalfFock (tensorL)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualTensorL0)
open TwistedGround
open ActualChargedAdjoint (actualForm)
open MixedIntertwiner
open OriginalFourMChargeCoset (originalI originalI_homogeneous)

open private sourceGradePairingEquiv sourceGradePairingEquiv_evaluation from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
open private phase_even_shift from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
open private actual_stress_transpose from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

private abbrev Negative := paritySpace leechData leech_spec.2.1 (-1)

private abbrev loweringMode :=
  tensorL leechData (ActualGround leechData leech_spec.2.1)
    (HalfFockSpectralFiberSource.actualInverse leechData) 1

private def lowered (q : ℕ) (u : Negative) : Negative :=
  ((orbifoldMode 1 ^ q) ((0, u) : Orbifold)).2

private theorem lowered_val (q : ℕ) (u : Negative) :
    (lowered q u).val = (loweringMode ^ q) u.val := by
  induction q with
  | zero => rfl
  | succ q ih =>
    unfold lowered
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    refine (OriginalOrbifoldConformal.L_twisted_apply leechData leech_spec.2.1
      leech_spec.2.2.1 1 _).trans ?_
    change loweringMode (lowered q u).val = loweringMode ((loweringMode ^ q) u.val)
    rw [ih]

private theorem lowered_pair (q : ℕ) (u : Negative) :
    (orbifoldMode 1 ^ q) ((0, u) : Orbifold) = (0, lowered q u) := by
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    change ((orbifoldMode 1 ^ q) ((0, u) : Orbifold)).1.val = 0
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [pow_succ', Module.End.mul_apply]
      refine (OriginalOrbifoldConformal.L_fixed_apply leechData leech_spec.2.1
        leech_spec.2.2.1 1 _).trans ?_
      rw [ih, map_zero]
  · rfl

set_option maxHeartbeats 12000000 in
-- Kernel checking the finite skew formula compares the raw and restricted half-Fock modes.
private theorem right_pairing (H K : ℕ) (m d : ℤ) (u v : Negative)
    (huH : actualTensorL0 leechData leech_spec.2.1 u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 leechData leech_spec.2.1 v.val = (K : ℂ) • v.val)
    (hK : 2 ≤ K) (a : fixedGrade leechData d) (q : ℕ) (hq : q < H - 1) :
    let n : ℤ := 2 * (H : ℤ) - (q : ℤ) - m - 2
    actualForm leechData leech_spec.2.1 v.val
        (originalRightCoefficient leechData leech_spec.2.1 n (lowered q u)
          ⟨a.val, a.property.2⟩).val =
      if d = (H : ℤ) + (K : ℤ) - m - 1 then
        ∑ p ∈ Finset.range (K - 1),
          ((-1 : ℂ) ^ (n + (p : ℤ) + 1) * (p.factorial : ℂ)⁻¹) *
            actualForm leechData leech_spec.2.1 ((loweringMode ^ p) v.val)
              ((correctedField leechData leech_spec.2.1 a.val).coeff
                (2 * (-(n + (p : ℤ)) - 1)) ((loweringMode ^ q) u.val))
      else 0 := by
  let n : ℤ := 2 * (H : ℤ) - (q : ℤ) - m - 2
  let E : ℤ := d + m + 1 - (H : ℤ)
  have hshift : (H : ℤ) - (q : ℤ) = ((H - q : ℕ) : ℤ) := by omega
  have hLower : actualTensorL0 leechData leech_spec.2.1 (lowered q u).val =
      ((H - q : ℕ) : ℂ) • (lowered q u).val := by
    simpa only [lowered_val, hshift, Int.cast_natCast] using
      (lowering_integer_energy leechData leech_spec.2.1 leech_spec.1 (H : ℤ) u.val
        (by simpa only [Int.cast_natCast] using huH) q)
  have skew := original_right_skew_finite leechData leech_spec.2.1 leech_spec.1
    (H - q) d n ⟨a.val, a.property.2⟩ a.property.1 (lowered q u) hLower v.val
  -- The lowering of the source and the shift of the right mode cancel in E.
  have hEnergy : ((H - q : ℕ) : ℤ) + d - n - 1 = E := by
    rw [← hshift]
    dsimp [n, E]
    omega
  dsimp only at skew ⊢
  rw [hEnergy] at skew
  split_ifs with hd
  · have eK : E = (K : ℤ) := by dsimp [E]; omega
    rw [eK] at skew
    have cutoff : ((K : ℤ) - 1).toNat = K - 1 := by omega
    have pairing := (skew.2.2 (by omega)).2.2.2.1
    rw [cutoff] at pairing
    rw [pairing]
    apply Finset.sum_congr rfl
    intro p _
    simp only [fixedParitySlice, VertexOperator.ncoeff_of_coeff]
    change _ * actualForm leechData leech_spec.2.1 ((loweringMode ^ p) v.val)
      ((correctedField leechData leech_spec.2.1 a.val).coeff
        (2 * (-(n + (p : ℤ)) - 1)) (lowered q u).val) = _
    rw [lowered_val]
  · by_cases hE : 2 ≤ E
    · let r := originalRightCoefficient leechData leech_spec.2.1 n (lowered q u)
        ⟨a.val, a.property.2⟩
      have hr : actualTensorL0 leechData leech_spec.2.1 r.val = (E : ℂ) • r.val :=
        (skew.2.2 hE).2.2.1
      have ht := actual_stress_transpose leechData leech_spec.2.1 0 v.val r.val
      change actualForm leechData leech_spec.2.1
          (actualTensorL0 leechData leech_spec.2.1 v.val) r.val =
        actualForm leechData leech_spec.2.1 v.val
          (actualTensorL0 leechData leech_spec.2.1 r.val) at ht
      have hpair : (K : ℂ) * actualForm leechData leech_spec.2.1 v.val r.val =
          (E : ℂ) * actualForm leechData leech_spec.2.1 v.val r.val := by
        simpa only [hvK, hr, map_smul, LinearMap.smul_apply, smul_eq_mul] using ht
      have hne : (K : ℂ) ≠ (E : ℂ) := by
        exact_mod_cast (show (K : ℤ) ≠ E by dsimp [E]; omega)
      have hzero : ((K : ℂ) - (E : ℂ)) * actualForm leechData leech_spec.2.1 v.val r.val = 0 := by
        rw [sub_mul, hpair, sub_self]
      exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)
    · have hzero := (skew.2.1 (by omega)).2
      exact (congrArg (fun z : Negative =>
        actualForm leechData leech_spec.2.1 v.val z.val) hzero).trans
        ((actualForm leechData leech_spec.2.1 v.val).map_zero)

set_option maxHeartbeats 4000000 in
-- The inverse source pairing and the twisted contraction share dependent grade carriers.
private theorem coefficient_pairing (H K : ℕ) (m d : ℤ) (u v : Negative)
    (huH : actualTensorL0 leechData leech_spec.2.1 u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 leechData leech_spec.2.1 v.val = (K : ℂ) • v.val)
    (a : fixedGrade leechData d) :
    sourcePairing leechData (originalI leechData leech_spec.2.1 leech_spec.2.2.1 m u v).val
        a.val =
      (-1 : ℂ) ^ (H : ℤ) * ∑ q ∈ Finset.range (H - 1),
        (q.factorial : ℂ)⁻¹ * actualForm leechData leech_spec.2.1 v.val
          (originalRightCoefficient leechData leech_spec.2.1
            (2 * (H : ℤ) - (q : ℤ) - m - 2) (lowered q u) ⟨a.val, a.property.2⟩).val := by
  classical
  by_cases hH : 2 ≤ H
  swap
  · have hu : u = 0 := Subtype.ext
      (integer_energy_zero leechData leech_spec.2.1 leech_spec.1 (H : ℤ) u.val
        (by simpa only [Int.cast_natCast] using huH) (by omega))
    simp [hu, show H - 1 = 0 by omega]
  by_cases hK : 2 ≤ K
  swap
  · have hv : v = 0 := Subtype.ext
      (integer_energy_zero leechData leech_spec.2.1 leech_spec.1 (K : ℤ) v.val
        (by simpa only [Int.cast_natCast] using hvK) (by omega))
    subst v
    simp
  rw [originalI_homogeneous leechData leech_spec.2.1 leech_spec.2.2.1 leech_spec.1
    H K m u v huH hvK]
  by_cases hd : d = (H : ℤ) + (K : ℤ) - m - 1
  · subst d
    change sourcePairing leechData
      ((sourceGradePairingEquiv leechData leech_spec.2.1 leech_spec.2.2.1 _).symm
        (normalizedCoefficient leechData leech_spec.2.1 m u v _)).val a.val = _
    rw [sourceGradePairingEquiv_evaluation,
      normalizedCoefficient_pairing leechData leech_spec.2.1 leech_spec.1 H K m u v huH hvK]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [right_pairing H K m _ u v huH hvK hK a q (Finset.mem_range.mp hq), ite_eq_left rfl,
      Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    let n : ℤ := 2 * (H : ℤ) - (q : ℤ) - m - 2
    let s : ℤ := m + 1 - (p : ℤ) - 2 * (H : ℤ) + (q : ℤ)
    -- The same physical mode is read at raw half-Fock exponent 2*s.
    have hs : s = -(n + (p : ℤ)) - 1 := by dsimp [s, n]; omega
    have phase : (-1 : ℂ) ^ ((H : ℤ) + s) =
        (-1 : ℂ) ^ (H : ℤ) * (-1 : ℂ) ^ (n + (p : ℤ) + 1) := calc
      _ = (-1 : ℂ) ^ ((H : ℤ) + (n + (p : ℤ) + 1) + 2 * s) := by congr 1; omega
      _ = (-1 : ℂ) ^ ((H : ℤ) + (n + (p : ℤ) + 1)) := phase_even_shift _ _
      _ = _ := zpow_add₀ (by norm_num) _ _
    change (-1 : ℂ) ^ ((H : ℤ) + s) / ((p.factorial : ℂ) * (q.factorial : ℂ)) *
      actualForm leechData leech_spec.2.1 ((loweringMode ^ p) v.val)
        ((correctedField leechData leech_spec.2.1 a.val).coeff (2 * s)
          ((loweringMode ^ q) u.val)) = _
    rw [phase, hs]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · let w := (sourceGradePairingEquiv leechData leech_spec.2.1 leech_spec.2.2.1
        ((H : ℤ) + (K : ℤ) - m - 1)).symm
      (normalizedCoefficient leechData leech_spec.2.1 m u v ((H : ℤ) + (K : ℤ) - m - 1))
    change sourcePairing leechData w.val a.val = _
    rw [sourcePairing_grade leechData _ _ (Ne.symm hd) w.val a.val w.property.1 a.property.1]
    symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro q hq
    rw [right_pairing H K m d u v huH hvK hK a q (Finset.mem_range.mp hq), ite_eq_right hd,
      mul_zero]

private theorem twisted_field (n : ℤ) (u : Negative) (x : Orbifold) :
    ((orbifoldVertexAlgebra.stateField (0, u))[[n]]) x =
      (originalI leechData leech_spec.2.1 leech_spec.2.2.1 n u x.2,
        originalRightCoefficient leechData leech_spec.2.1 n u x.1) :=
  OriginalOrbifoldField.Y_twisted_ncoeff_apply leechData leech_spec.2.1 leech_spec.2.2.1 n u x

/-- The original two-twisted field against a fixed detector is BPZ adjoint
to the original twisted-on-fixed field of the finitely lowered source. -/
theorem original_twisted_twisted_bpz (H K : ℕ) (m d : ℤ)
    (u v : paritySpace leechData leech_spec.2.1 (-1))
    (huH : actualTensorL0 leechData leech_spec.2.1 u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 leechData leech_spec.2.1 v.val = (K : ℂ) • v.val)
    (a : fixedGrade leechData d) :
    let U : Orbifold := (0, u)
    let V : Orbifold := (0, v)
    let F : Orbifold := (⟨a.val, a.property.2⟩, 0)
    orbifoldBPZ (((orbifoldVertexAlgebra.stateField U)[[m]]) V) F =
      (-1 : ℂ) ^ (H : ℤ) * ∑ q ∈ Finset.range (H - 1),
        (q.factorial : ℂ)⁻¹ * orbifoldBPZ V
          (((orbifoldVertexAlgebra.stateField ((orbifoldMode 1 ^ q) U))[[
            2 * (H : ℤ) - (q : ℤ) - m - 2]]) F) := by
  dsimp only
  simp only [lowered_pair, twisted_field, orbifoldBPZ_apply, Submodule.coe_zero,
    map_zero, add_zero, zero_add]
  exact coefficient_pairing H K m d u v huH hvK a

#print axioms original_twisted_twisted_bpz

end D5.S3.VertexAlgebra.OriginalOrbifoldMatterTwistedBPZ
