/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMMSkew
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMMSkew
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed skew symmetry of the original two-twisted-input intertwiner. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSkewAdjoints
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
import Batteries.Tactic.OpenPrivate

/-!
The original normalized coefficient is evaluated on the entire target grade.
After transposition its finite ranges are permuted from p,q,j to j,q,p.
The original grade inverse and BPZ establish skew on homogeneous states.
The original parity basis and mode truncation extend it bilinearly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMMSkew

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeHalfFock LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace
open LatticeSugawaraCurrents LatticeInvolution HalfFock.ActualEnergyCovariance
open HalfFock.LatticeHalfFockParityField ActualChargedAdjoint MixedIntertwiner
open OriginalFourMChargeCoset (originalI originalI_homogeneous originalI_truncation)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open OriginalSkewAdjoints
open private original_l1_grade original_l1_fixed T from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private sourceGradePairingEquiv from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
open private originalI_sharp from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
open private actualInputBasis actual_input_basis_expansion actual_input_basis_energy from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite

section
variable (D : LatticeData) (hu : IsUnit D.G.det)
  (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
local notation "M" => paritySpace D hu (-1)
local notation "V" => FixedCarrier D
local notation "I" => originalI D hu hD
local notation "A" => sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1
local notation "S" => fixedTranslation D
local notation "eps" => StateFieldResidueReconstruction.epsilon

private theorem originalI_pairing (h24 : D.rank = 24) (H K : ℕ) (n : ℤ)
    (u v : M)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (a : fixedGrade D ((H : ℤ) + K - n - 1)) :
    sourcePairing D (I n u v).val a.val =
      normalizedCoefficient D hu n u v ((H : ℤ) + K - n - 1) a := by
  rw [originalI_homogeneous D hu hD h24 H K n u v huH hvK]
  exact sourceGradePairingEquiv_evaluation D hu hD _ _ a

include hD in
private theorem source_translation_grade (u : V) (d : ℤ)
    (huG : u.val ∈ grade D d) (j : ℕ) :
    ((S ^ j) u).val ∈ grade D (d + j) := by
  have hv : vacuum D ∈ grade D 0 := by
    rw [grade_zero D hD]
    exact Submodule.subset_span (Set.mem_singleton _)
  induction j with
  | zero => simpa using huG
  | succ j ih =>
    rw [pow_succ' S, Module.End.mul_apply]
    change LatticeSugawaraConformal.translation D ((S ^ j) u).val ∈ grade D _
    rw [LatticeActualVertexAlgebra.translation_as_mode]
    have hm := positive_actual_mode_grade D hD (d + j) 0 (-2)
      ((S ^ j) u).val (vacuum D) ih hv
    rwa [show d + (j : ℤ) + 0 - (-2) - 1 = d + (↑(j + 1) : ℤ) by omega] at hm

private theorem pairing_skew (h24 : D.rank = 24) (H K : ℕ) (n : ℤ)
    (u v : M)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (a : fixedGrade D ((H : ℤ) + K - n - 1)) :
    sourcePairing D (I n u v).val a.val =
      ∑ j ∈ Finset.range (((H : ℤ) + K - n - 1).toNat + 1),
        (eps (n + j + 1) / (j.factorial : ℂ)) *
          sourcePairing D ((S ^ j) (I (n + j) v u)).val a.val := by
  classical
  let d := (H : ℤ) + K - n - 1
  let J := Finset.range (d.toNat + 1)
  let P := Finset.range (K - 1)
  let Q := Finset.range (H - 1)
  let s := fun p q : ℕ => n + 1 - (p : ℤ) - 2*(H : ℤ) + q
  let t := fun p q j : ℕ => n + (j : ℤ) + 1 - (q : ℤ) - 2*(K : ℤ) + p
  let b (j : ℕ) : fixedGrade D ((K : ℤ) + H - (n + j) - 1) :=
    ⟨(A ^ j) a.val, ⟨by
      rw [show (K : ℤ) + H - (n + j) - 1 = d - j by dsimp [d]; omega]
      exact original_l1_grade D hu d a.val a.property.1 j,
      (mem_fixedSpace D _).mpr (original_l1_fixed D hu a.val a.property.2 j)⟩⟩
  let f := fun p q j : ℕ =>
    (eps (n + j + 1) / (j.factorial : ℂ)) *
      ((eps ((K : ℤ) + t p q j) / ((q.factorial : ℂ) * (p.factorial : ℂ))) *
        actualForm D hu ((T D hu ^ q) u.val)
          ((correctedField D hu (b j).val).coeff (2 * t p q j) ((T D hu ^ p) v.val)))
  have sign (p q j : ℕ) :
      eps ((H : ℤ) + s p q + d) = eps (n + j + 1) * eps ((K : ℤ) + t p q j) := by
    have he : (H : ℤ) + s p q + d - (n + j + 1 + K + t p q j) =
        2 * ((K : ℤ) - p + q - n - j - 1) := by
      dsimp [s, t, d]
      ring
    rw [show (H : ℤ) + s p q + d = (n + j + 1) + ((K : ℤ) + t p q j) +
          2 * ((K : ℤ) - p + q - n - j - 1) by omega]
    simp only [StateFieldResidueReconstruction.epsilon]
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul (-1 : ℂ) 2]
    norm_num
  calc
    _ = ∑ p ∈ P, ∑ q ∈ Q, ∑ j ∈ J, f p q j := by
      rw [originalI_pairing D hu hD h24 H K n u v huH hvK,
        normalizedCoefficient_pairing D hu h24 H K n u v huH hvK d a]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      let x := (T D hu ^ q) u.val
      let y := (T D hu ^ p) v.val
      change (eps ((H : ℤ) + s p q) / ((p.factorial : ℂ) * (q.factorial : ℂ))) *
        actualForm D hu y ((correctedField D hu a.val).coeff (2 * s p q) x) =
        ∑ j ∈ J, f p q j
      rw [(ActualPairingSymmetry.actualForm_symmetric D hu).eq y _,
        actual_corrected_grade_adjoint D hu hD d (2 * s p q) a,
        ← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have he : -s p q - 2*d + (j : ℤ) = t p q j := by
        dsimp [s, t, d]
        ring
      rw [show -(2 * s p q) - 4*d + 2*(j : ℤ) = 2 * t p q j by omega]
      have hs : eps ((H : ℤ) + s p q) * eps d =
          eps (n + j + 1) * eps ((K : ℤ) + t p q j) :=
        (zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) _ _).symm.trans (sign p q j)
      change ((eps ((H : ℤ) + s p q) / ((p.factorial : ℂ) * (q.factorial : ℂ))) * eps d) *
          ((j.factorial : ℂ)⁻¹ * actualForm D hu x
            ((correctedField D hu (b j).val).coeff (2 * t p q j) y)) =
        f p q j
      dsimp only [f, x, y]
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        _ = (eps ((H : ℤ) + s p q) * eps d) *
            ((p.factorial : ℂ)⁻¹ * (q.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹ *
              actualForm D hu ((T D hu ^ q) u.val)
                ((correctedField D hu (b j).val).coeff (2 * t p q j) ((T D hu ^ p) v.val))) := by
          ring
        _ = _ := by rw [hs]; ring
    _ = ∑ j ∈ J, ∑ q ∈ Q, ∑ p ∈ P, f p q j := by
      calc
        _ = ∑ p ∈ P, ∑ j ∈ J, ∑ q ∈ Q, f p q j := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.sum_comm]
        _ = ∑ j ∈ J, ∑ p ∈ P, ∑ q ∈ Q, f p q j := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [sourcePairing_fixedTranslation_pow D hu]
      change (∑ q ∈ Q, ∑ p ∈ P, f p q j) =
        (eps (n + j + 1) / (j.factorial : ℂ)) * sourcePairing D (I (n + j) v u).val (b j).val
      rw [originalI_pairing D hu hD h24 K H (n + j) v u hvK huH,
        normalizedCoefficient_pairing D hu h24 K H (n + j) v u hvK huH _ (b j),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum] <;> rfl

private def skewTerm (n : ℤ) (u v : M) (j : ℕ) : V :=
  (eps (n + j + 1) / (j.factorial : ℂ)) • (S ^ j) (I (n + j) v u)

private theorem homogeneous_skew (h24 : D.rank = 24) (H K : ℕ) (n : ℤ)
    (u v : M)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    I n u v = ∑ᶠ j, skewTerm D hu hD n u v j := by
  classical
  let d := (H : ℤ) + K - n - 1
  by_cases hd : d < 0
  · rw [originalI_sharp D hu hD h24 H K n u v huH hvK (by dsimp [d] at hd; omega)]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    simp [skewTerm, originalI_sharp D hu hD h24 K H (n + j) v u hvK huH
      (by dsimp [d] at hd; omega)]
  have hcut : Function.support (skewTerm D hu hD n u v) ⊆
      (Finset.range (d.toNat + 1) : Set ℕ) := by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra! hj'
    apply hj
    simp [skewTerm, originalI_sharp D hu hD h24 K H (n + j) v u hvK huH
      (by dsimp [d] at hj'; omega)]
  rw [finsum_eq_sum_of_support_subset _ hcut]
  have gradeI (H' K' : ℕ) (m : ℤ) (x y : M)
      (hx : actualTensorL0 D hu x.val = (H' : ℂ) • x.val)
      (hy : actualTensorL0 D hu y.val = (K' : ℂ) • y.val) :
      (I m x y).val ∈ grade D ((H' : ℤ) + K' - m - 1) := by
    rw [originalI_homogeneous D hu hD h24 H' K' m x y hx hy]
    exact ((sourceGradePairingEquiv D hu hD _).symm
      (normalizedCoefficient D hu m x y _)).property.1
  let rhs : V := ∑ j ∈ Finset.range (d.toNat + 1), skewTerm D hu hD n u v j
  have hright : rhs.val ∈ grade D d := by
    simp only [rhs, Submodule.coe_sum]
    apply (grade D d).sum_mem
    intro j _
    simp only [skewTerm, Submodule.coe_smul]
    apply (grade D d).smul_mem
    have ht := source_translation_grade D hD (I (n + j) v u) _
      (gradeI K H (n + j) v u hvK huH) j
    rwa [show (K : ℤ) + H - (n + j) - 1 + j = d by dsimp [d]; omega] at ht
  let leftGrade : fixedGrade D d := ⟨(I n u v).val, gradeI H K n u v huH hvK,
    (I n u v).property⟩
  let rightGrade : fixedGrade D d := ⟨rhs.val, hright, rhs.property⟩
  apply Subtype.ext
  change leftGrade.val = rightGrade.val
  apply congrArg (fun x : fixedGrade D d => x.val)
  apply (sourceGradePairingEquiv D hu hD d).injective
  apply LinearMap.ext
  intro a
  have evaluate (x : fixedGrade D d) :
      sourceGradePairingEquiv D hu hD d x a = sourcePairing D x.val a.val := by
    simpa only [LinearEquiv.symm_apply_apply] using
      (sourceGradePairingEquiv_evaluation D hu hD d
        (sourceGradePairingEquiv D hu hD d x) a).symm
  simp only [evaluate]
  change sourcePairing D (I n u v).val a.val = sourcePairing D rhs.val a.val
  simpa only [rhs, Submodule.coe_sum, skewTerm, Submodule.coe_smul, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using
      pairing_skew D hu hD h24 H K n u v huH hvK a

private theorem skewTerm_finite (n : ℤ) (u v : M) :
    Function.HasFiniteSupport (skewTerm D hu hD n u v) := by
  let W := fun x : M => (ActualEnergyRestrictedDual.maxOddWeight D hu x.val : ℤ)
  let N := (W u + W v + 4 - n).toNat
  apply (Finset.range N).finite_toSet.subset
  intro j hj
  apply Finset.mem_range.mpr
  by_contra! hj'
  apply hj
  have hk : W v + W u + 3 < n + (j : ℤ) := by dsimp [N] at hj'; omega
  simp [skewTerm, originalI_truncation D hu hD v u (n + j) hk]

private def skewSum (n : ℤ) : M →ₗ[ℂ] M →ₗ[ℂ] V where
  toFun u :=
    { toFun := fun v => ∑ᶠ j, skewTerm D hu hD n u v j
      map_add' := fun v w => by
        simp only [skewTerm, map_add, LinearMap.add_apply, smul_add]
        exact finsum_add_distrib (skewTerm_finite D hu hD n u v)
          (skewTerm_finite D hu hD n u w)
      map_smul' := fun c v => by
        simpa only [skewTerm, map_smul, LinearMap.smul_apply, RingHom.id_apply,
          smul_smul, mul_comm] using (smul_finsum c (skewTerm D hu hD n u v)).symm }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change (∑ᶠ j, skewTerm D hu hD n (u + v) w j) =
      (∑ᶠ j, skewTerm D hu hD n u w j) + ∑ᶠ j, skewTerm D hu hD n v w j
    simp only [skewTerm, map_add, smul_add]
    exact finsum_add_distrib (skewTerm_finite D hu hD n u w)
      (skewTerm_finite D hu hD n v w)
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    change (∑ᶠ j, skewTerm D hu hD n (c • u) v j) = c • ∑ᶠ j, skewTerm D hu hD n u v j
    simpa only [skewTerm, map_smul, smul_smul, mul_comm] using
      (smul_finsum c (skewTerm D hu hD n u v)).symm

/-- Signed skew of every original two-twisted-input coefficient.
The native truncation gives finite support of its translation sum. -/
theorem originalI_skew (h24 : D.rank = 24) (n : ℤ) (u v : M) :
    I n u v = ∑ᶠ j : ℕ,
      (eps (n + j + 1) / (j.factorial : ℂ)) • (S ^ j) (I (n + j) v u) := by
  classical
  change I n u v = skewSum D hu hD n u v
  -- Keep the original supports fixed during bilinear expansion.
  let us := ∑ i ∈ ((actualAmbientBasis D hu).repr u.val).support.attach,
    ((actualAmbientBasis D hu).repr u.val i.val) • actualInputBasis D hu u i
  let vs := ∑ i ∈ ((actualAmbientBasis D hu).repr v.val).support.attach,
    ((actualAmbientBasis D hu).repr v.val i.val) • actualInputBasis D hu v i
  have huExp : us = u := actual_input_basis_expansion D hu u
  have hvExp : vs = v := actual_input_basis_expansion D hu v
  calc
    I n u v = I n us vs := congrArg₂ (fun x y => I n x y) huExp.symm hvExp.symm
    _ = skewSum D hu hD n us vs := by
      dsimp only [us, vs]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [homogeneous_skew D hu hD h24 _ _ n
        (actualInputBasis D hu u i) (actualInputBasis D hu v k)
        (actual_input_basis_energy D hu h24 u i) (actual_input_basis_energy D hu h24 v k)] <;>
        rfl
    _ = skewSum D hu hD n u v := congrArg₂ (fun x y => skewSum D hu hD n x y) huExp hvExp

end
end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMMSkew
