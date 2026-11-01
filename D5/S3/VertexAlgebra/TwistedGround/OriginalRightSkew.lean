/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalRightSkew
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalRightSkew
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Finprod]
   utility: none
   digest: Original finite right coefficients with integer support and stress contraction. -/
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
import D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
import Mathlib.Algebra.BigOperators.Finprod
import Batteries.Tactic.OpenPrivate

/-! The original M-by-fixed-source right coefficient. Translation acts on the
negative parity tensor, and its transpose acts on the original tensor detector. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator
namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open ActualChargedAdjoint LatticeSugawaraCurrents LatticeSugawaraVirasoro
open HalfFock.LatticeHalfFockParityField
open private mixedMode mixed_mode_tail
  from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private phase_even_shift
  from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
open private raising raising_weight translation_val actual_stress_transpose
  from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

private def rightTerm (D : LatticeData) (hu : IsUnit D.G.det) (s : ℤ)
    (u : paritySpace D hu (-1)) (a : FixedCarrier D) (ell : ℕ) :
    paritySpace D hu (-1) :=
  ((-1 : ℂ)^(s+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹) •
    (translation D hu ^ ell) (mixedMode D hu (s+(ell : ℤ)) a u)

private theorem rightTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℤ) (u : paritySpace D hu (-1)) (a : FixedCarrier D) :
    Function.HasFiniteSupport (rightTerm D hu s u a) := by
  classical
  obtain ⟨N, hN⟩ := mixed_mode_tail D hu s a u
  apply (Finset.range N).finite_toSet.subset
  intro ell hell
  by_contra outside
  apply hell
  simp only [rightTerm, hN ell (by simpa using outside), map_zero, smul_zero]

/-- Coefficients of exp(z L(-1)) rho(-z), on the original polynomial carriers. -/
def originalRightCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (s : ℤ) :
    paritySpace D hu (-1) →ₗ[ℂ] FixedCarrier D →ₗ[ℂ] paritySpace D hu (-1) where
  toFun u := {
    toFun a := ∑ᶠ ell : ℕ, rightTerm D hu s u a ell
    map_add' a b := by
      simp only [rightTerm, map_add, LinearMap.add_apply, smul_add]
      exact finsum_add_distrib (rightTerm_finite D hu s u a)
        (rightTerm_finite D hu s u b)
    map_smul' z a := by
      simpa only [rightTerm, map_smul, LinearMap.smul_apply, RingHom.id_apply,
        smul_smul, mul_comm] using
        (smul_finsum z (rightTerm D hu s u a)).symm }
  map_add' u v := by
    apply LinearMap.ext
    intro a
    change (∑ᶠ ell : ℕ, rightTerm D hu s (u+v) a ell) =
      (∑ᶠ ell : ℕ, rightTerm D hu s u a ell) +
        (∑ᶠ ell : ℕ, rightTerm D hu s v a ell)
    simp only [rightTerm, map_add, smul_add]
    exact finsum_add_distrib (rightTerm_finite D hu s u a)
      (rightTerm_finite D hu s v a)
  map_smul' z u := by
    apply LinearMap.ext
    intro a
    change (∑ᶠ ell : ℕ, rightTerm D hu s (z • u) a ell) =
      z • (∑ᶠ ell : ℕ, rightTerm D hu s u a ell)
    simpa only [LinearMap.smul_apply, rightTerm, map_smul, RingHom.id_apply,
      smul_smul, mul_comm] using
      (smul_finsum z (rightTerm D hu s u a)).symm

private theorem right_raw_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (h s : ℤ) (a : FixedCarrier D) (ha : a.val ∈ grade D h)
    (u : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val) (ell : ℕ) :
    actualTensorL0 D hu (mixedMode D hu (s+(ell : ℤ)) a u).val =
      (((H : ℤ)+h-s-1-(ell : ℤ) : ℤ) : ℂ) •
        (mixedMode D hu (s+(ell : ℤ)) a u).val := by
  have energy := original_mode_integer_energy D hu h (H : ℤ)
    (s+(ell : ℤ)) a.val ha u.val huH
  change actualTensorL0 D hu
      ((correctedField D hu a.val).coeff (2*(-(s+(ell : ℤ))-1)) u.val) =
    (((H : ℤ)+h-s-1-(ell : ℤ) : ℤ) : ℂ) •
      ((correctedField D hu a.val).coeff (2*(-(s+(ell : ℤ))-1)) u.val)
  rw [show 2*(-(s+(ell : ℤ))-1) = -2*(s+(ell : ℤ))-2 by ring,
    show (H : ℤ)+h-s-1-(ell : ℤ) = (H : ℤ)+h-(s+(ell : ℤ))-1 by ring]
  exact energy

private theorem translation_power_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (W : ℕ) (x : paritySpace D hu (-1))
    (hx : actualTensorL0 D hu x.val = (W : ℂ) • x.val) (ell : ℕ) :
    actualTensorL0 D hu ((translation D hu ^ ell) x).val =
      ((W+ell : ℕ) : ℂ) • ((translation D hu ^ ell) x).val := by
  induction ell with
  | zero => simpa using hx
  | succ ell ih =>
    rw [pow_succ', Module.End.mul_apply, translation_val]
    simpa only [Nat.add_succ] using raising_weight D hu (W+ell)
      ((translation D hu ^ ell) x).val ih

private theorem translation_power_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (ell : ℕ) (d : ActualTensor D hu) (x : paritySpace D hu (-1)) :
    actualForm D hu d ((translation D hu ^ ell) x).val =
      actualForm D hu
        ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1
          ^ ell) d) x.val := by
  induction ell generalizing d with
  | zero => rfl
  | succ ell ih =>
    rw [pow_succ', Module.End.mul_apply, translation_val]
    rw [show actualForm D hu d (raising D hu ((translation D hu ^ ell) x).val) =
      actualForm D hu
        (tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 d)
        ((translation D hu ^ ell) x).val by
      exact (actual_stress_transpose D hu 1 d
        ((translation D hu ^ ell) x).val).symm]
    rw [ih, pow_succ, Module.End.mul_apply]

/- proof_shape: content
   admission_basis: escape-witness
   escape_witness: translation_power_pairing and translation_power_energy establish
   the iterated actual stress transport used on the finite right coefficient.
   rightTerm_finite and right_raw_energy are consumed bind-only helpers. -/
/-- Exact integer zero branch, sharp spectral upper support, energy and ordered
stress contraction of the original right coefficient. -/
theorem original_right_skew_finite
    (D : LatticeData) (hu : IsUnit D.G.det) (h24 : D.rank = 24)
    (H : ℕ) (h s : ℤ) (a : FixedCarrier D) (ha : a.val ∈ grade D h)
    (u : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (d : ActualTensor D hu) :
    let E : ℤ := (H : ℤ)+h-s-1
    let C : Module.End ℂ (ActualTensor D hu) :=
      tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1
    let raw : ℕ → paritySpace D hu (-1) := fun ell =>
      (((fixedParitySlice D hu (-1) a)[[s+(ell : ℤ)]]) u)
    let term : ℕ → paritySpace D hu (-1) := fun ell =>
      ((-1 : ℂ)^(s+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹) •
        (translation D hu ^ ell) (raw ell)
    let R := originalRightCoefficient D hu s u a
    Set.Finite (Function.support term) ∧
    (E < 2 → (∀ ell : ℕ, raw ell = 0) ∧ R = 0) ∧
    (2 ≤ E →
      (∀ ell : ℕ, (E-1).toNat ≤ ell → raw ell = 0) ∧
      R = (∑ ell ∈ Finset.range (E-1).toNat, term ell) ∧
      actualTensorL0 D hu R.val = (E : ℂ) • R.val ∧
      (actualForm D hu d R.val =
        ∑ ell ∈ Finset.range (E-1).toNat,
          ((-1 : ℂ)^(s+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹) *
            actualForm D hu ((C ^ ell) d) (raw ell).val) ∧
      (∀ (m r : ℤ) (j : ℕ), s = m+r-(j : ℤ) →
        ((-1 : ℂ)^(j : ℤ) * Ring.choose (r : ℂ) j) * actualForm D hu d R.val =
          ∑ ell ∈ Finset.range (E-1).toNat,
            Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) *
              (ell.factorial : ℂ)⁻¹ * actualForm D hu ((C ^ ell) d) (raw ell).val) ∧
      (∀ (n r : ℤ) (j : ℕ), s = n+r-(j : ℤ) →
        ((-1 : ℂ)^((j : ℤ)+r) * Ring.choose (r : ℂ) j) * actualForm D hu d R.val =
          ∑ ell ∈ Finset.range (E-1).toNat,
            Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) *
              (ell.factorial : ℂ)⁻¹ * actualForm D hu ((C ^ ell) d) (raw ell).val)) := by
  classical
  dsimp only
  let E : ℤ := (H : ℤ)+h-s-1
  let raw := fun ell : ℕ => mixedMode D hu (s+(ell : ℤ)) a u
  have energy (ell : ℕ) : actualTensorL0 D hu (raw ell).val =
      ((E-(ell : ℤ) : ℤ) : ℂ) • (raw ell).val :=
    right_raw_energy D hu H h s a ha u huH ell
  have vanish (ell : ℕ) (he : E-(ell : ℤ) < 2) : raw ell = 0 := by
    apply Subtype.ext
    exact integer_energy_zero D hu h24 _ _ (energy ell) he
  refine ⟨rightTerm_finite D hu s u a, ?_, ?_⟩
  · intro hE
    have zero (ell : ℕ) : raw ell = 0 := vanish ell (by omega)
    refine ⟨zero, ?_⟩
    change (∑ᶠ ell : ℕ, rightTerm D hu s u a ell) = 0
    apply finsum_eq_zero_of_forall_eq_zero
    intro ell
    simp only [rightTerm, show mixedMode D hu (s+(ell : ℤ)) a u = 0 from zero ell,
      map_zero, smul_zero]
  · intro hE
    have tail (ell : ℕ) (he : (E-1).toNat ≤ ell) : raw ell = 0 :=
      vanish ell (by omega)
    have finite : originalRightCoefficient D hu s u a =
        ∑ ell ∈ Finset.range (E-1).toNat, rightTerm D hu s u a ell := by
      apply finsum_eq_sum_of_support_subset
      intro ell hell
      by_contra outside
      apply hell
      simp only [rightTerm, show mixedMode D hu (s+(ell : ℤ)) a u = 0 from
        tail ell (by simpa using outside), map_zero, smul_zero]
    refine ⟨tail, finite, ?_, ?_⟩
    · rw [finite]
      simp only [Submodule.coe_sum, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      have nonneg : 0 ≤ E-(ell : ℤ) := by
        have := Finset.mem_range.mp hell
        omega
      have castW : (((E-(ell : ℤ)).toNat : ℕ) : ℂ) = ((E-(ell : ℤ) : ℤ) : ℂ) := by
        exact_mod_cast Int.toNat_of_nonneg nonneg
      have hx : actualTensorL0 D hu (raw ell).val =
          (((E-(ell : ℤ)).toNat : ℕ) : ℂ) • (raw ell).val := by
        rw [castW]
        exact energy ell
      have raised := translation_power_energy D hu (E-(ell : ℤ)).toNat (raw ell) hx ell
      have scalar : (((E-(ell : ℤ)).toNat+ell : ℕ) : ℂ) = (E : ℂ) := by
        exact_mod_cast (show (((E-(ell : ℤ)).toNat+ell : ℕ) : ℤ) = E by omega)
      dsimp only [rightTerm]
      simp only [Submodule.coe_smul, map_smul]
      rw [raised, scalar]
      exact smul_comm _ _ _
    · have pairing : actualForm D hu d (originalRightCoefficient D hu s u a).val =
          ∑ ell ∈ Finset.range (E-1).toNat,
            ((-1 : ℂ)^(s+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹) *
              actualForm D hu
                ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D)
                  1 ^ ell) d) (raw ell).val := by
        rw [finite]
        simp only [Submodule.coe_sum, map_sum]
        apply Finset.sum_congr rfl
        intro ell hell
        simp only [rightTerm, Submodule.coe_smul, map_smul, smul_eq_mul,
          translation_power_pairing] <;> rfl
      refine ⟨pairing, ?_, ?_⟩
      · intro m r j hs
        rw [pairing, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ell hell
        have sign : (-1 : ℂ)^(j : ℤ) * (-1 : ℂ)^(s+(ell : ℤ)+1) =
            (-1 : ℂ)^(m+r+(ell : ℤ)+1) := by
          rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hs]
          congr 1
          ring
        let b : ℂ := actualForm D hu
          ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D)
            1 ^ ell) d) (raw ell).val
        change ((-1 : ℂ)^(j : ℤ) * Ring.choose (r : ℂ) j) *
          (((-1 : ℂ)^(s+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹) * b) =
            Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) *
              (ell.factorial : ℂ)⁻¹ * b
        linear_combination (Ring.choose (r : ℂ) j * (ell.factorial : ℂ)⁻¹ * b) * sign
      · intro n r j hs
        rw [pairing, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ell hell
        have sign : (-1 : ℂ)^((j : ℤ)+r) * (-1 : ℂ)^(s+(ell : ℤ)+1) =
            (-1 : ℂ)^(n+(ell : ℤ)+1) := by
          rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hs,
            show ((j : ℤ)+r)+(n+r-(j : ℤ)+(ell : ℤ)+1) =
              (n+(ell : ℤ)+1)+2*r by ring, phase_even_shift]
        let b : ℂ := actualForm D hu
          ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D)
            1 ^ ell) d) (raw ell).val
        change ((-1 : ℂ)^((j : ℤ)+r) * Ring.choose (r : ℂ) j) *
          (((-1 : ℂ)^(s+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹) * b) =
            Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) *
              (ell.factorial : ℂ)⁻¹ * b
        linear_combination (Ring.choose (r : ℂ) j * (ell.factorial : ℂ)⁻¹ * b) * sign

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
