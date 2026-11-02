/- GID: D5/S3/VertexAlgebra/Lattice/LatticeQuartetEnergyPreservation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeQuartetEnergyPreservation
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Original quartet operators preserve literal relative constraints. -/

import D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard

/-! Preservation of fixed original charge, actual b0 and unshifted totalL0. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeLightConeCoordinates
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock (b c)
open D5.S3.VertexAlgebra.LatticeQuartetContraction

open private M_eq_number chargeProject_diagonal from
  D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation

variable {D : LatticeData}

/- The two tensor maps in the literal total-energy operator have a useful
   commutator decomposition.  The proof is on pure tensors and therefore does
   not introduce any completion or transported representation. -/
private theorem tensor_commutator_sum
    (A a : Module.End ℂ (Carrier D)) (G g : Module.End ℂ Fock) :
    (tp A (1 : Module.End ℂ Fock) +
        tp (1 : Module.End ℂ (Carrier D)) G) * tp a g -
      tp a g * (tp A (1 : Module.End ℂ Fock) +
        tp (1 : Module.End ℂ (Carrier D)) G) =
      tp (A * a - a * A) g + tp a (G * g - g * G) := by
  apply TensorProduct.ext'
  intro v w
  simp only [tp, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    map_add, TensorProduct.map_tmul, Module.End.one_apply, TensorProduct.sub_tmul,
    TensorProduct.tmul_sub]
  abel

private theorem tensor_scalar_cancel
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (z : ℂ) (A : Module.End ℂ V) (G : Module.End ℂ W) :
    TensorProduct.map ((-z) • A) G + TensorProduct.map A (z • G) = 0 := by
  rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    neg_smul, neg_add_cancel]

/- Bilinear extension from the neutral-mode commutator supplied by the actual
   Sugawara implementation. -/
private theorem sugawaraMode_a_commutator
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (u : E D) (m q : ℤ) :
    sugawaraMode D H m * a u q - a u q * sugawaraMode D H m =
      -(q : ℂ) • a u (m + q) := by
  classical
  calc
    sugawaraMode D H m * a u q - a u q * sugawaraMode D H m =
        ∑ i : Fin D.rank, u i •
          (sugawaraMode D H m * neutralMode D i q -
            neutralMode D i q * sugawaraMode D H m) := by
      simp only [a, Finset.sum_mul, Finset.mul_sum,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      rw [← Finset.sum_sub_distrib]
      simp_rw [← smul_sub]
    _ = ∑ i : Fin D.rank, u i •
          (-(q : ℂ) • neutralMode D i (m + q)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sugawaraMode_current_commutator D H hHG hGH i m q]
    _ = -(q : ℂ) • a u (m + q) := by
      simp only [a, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      ring

private theorem ghost_zero_c (n : ℤ) :
    D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0 * c (-n) -
        c (-n) * D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0 =
      (n : ℂ) • c (-n) := by
  simpa using (D5.S3.Quantum.Fermionic.BcGhostVirasoro.ward_c 0 (-n))

private theorem ghost_zero_b (n : ℤ) :
    D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0 * b n -
        b n * D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0 =
      (-(n : ℂ)) • b n := by
  simpa using (D5.S3.Quantum.Fermionic.BcGhostVirasoro.ward_b 0 n)

/- The exact accepted operator, written as the literal matter-plus-ghost sum. -/
private def originalEnergy (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) :=
  D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.matterMode D H 0 +
    D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.ghostVirasoro D 0

private theorem originalEnergy_dm
    (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (n : ℤ) :
    originalEnergy D H * dm F n - dm F n * originalEnergy D H = 0 := by
  change
    (tp (sugawaraMode D H 0) (1 : Module.End ℂ Fock) +
        tp (1 : Module.End ℂ (Carrier D))
          (D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0)) *
        tp (a F.eMinus n) (c (-n)) -
      tp (a F.eMinus n) (c (-n)) *
        (tp (sugawaraMode D H 0) (1 : Module.End ℂ Fock) +
          tp (1 : Module.End ℂ (Carrier D))
            (D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0)) = 0
  rw [tensor_commutator_sum,
    sugawaraMode_a_commutator D H hHG hGH F.eMinus 0 n, ghost_zero_c]
  simpa only [tp, zero_add] using
    (tensor_scalar_cancel (n : ℂ) (a F.eMinus n) (c (-n)))

private theorem originalEnergy_rr
    (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (n : ℤ) :
    originalEnergy D H * rr F n - rr F n * originalEnergy D H = 0 := by
  change
    (tp (sugawaraMode D H 0) (1 : Module.End ℂ Fock) +
        tp (1 : Module.End ℂ (Carrier D))
          (D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0)) *
        tp (a F.ePlus (-n)) (b n) -
      tp (a F.ePlus (-n)) (b n) *
        (tp (sugawaraMode D H 0) (1 : Module.End ℂ Fock) +
          tp (1 : Module.End ℂ (Carrier D))
            (D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0)) = 0
  rw [tensor_commutator_sum,
    sugawaraMode_a_commutator D H hHG hGH F.ePlus 0 (-n), ghost_zero_b]
  simpa only [tp, zero_add, Int.cast_neg, neg_neg] using
    (tensor_scalar_cancel (-(n : ℂ)) (a F.ePlus (-n)) (b n))

private theorem originalEnergy_dTerm
    (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (r : ℕ) :
    originalEnergy D H * dTerm F r = dTerm F r * originalEnergy D H := by
  have h₁ := sub_eq_zero.mp (originalEnergy_dm F H hHG hGH ((r : ℤ) + 1))
  have h₂ := sub_eq_zero.mp
    (originalEnergy_dm F H hHG hGH (-((r : ℤ) + 1)))
  rw [dTerm, mul_add, add_mul, h₁, h₂]

private theorem originalEnergy_rTerm
    (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (r : ℕ) :
    originalEnergy D H * rTerm F r = rTerm F r * originalEnergy D H := by
  have h₁ := sub_eq_zero.mp (originalEnergy_rr F H hHG hGH ((r : ℤ) + 1))
  have h₂ := sub_eq_zero.mp
    (originalEnergy_rr F H hHG hGH (-((r : ℤ) + 1)))
  simp only [rTerm, mul_add, add_mul, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, smul_add, h₁, h₂]

private theorem originalEnergy_unscaledD
    (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) :
    originalEnergy D H * unscaledD F = unscaledD F * originalEnergy D H := by
  apply Family.total_commutes_fixed
  intro r
  exact originalEnergy_dTerm F H hHG hGH r

private theorem originalEnergy_unscaledR
    (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) :
    originalEnergy D H * unscaledR F = unscaledR F * originalEnergy D H := by
  apply Family.total_commutes_fixed
  intro r
  exact originalEnergy_rTerm F H hHG hGH r

private theorem originalEnergy_d0
    (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (p : Charge D) :
    originalEnergy D H * d0 F p = d0 F p * originalEnergy D H := by
  simp only [d0, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    originalEnergy_unscaledD F H hHG hGH]

private theorem originalEnergy_R
    (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (p : Charge D) :
    originalEnergy D H * R F p = R F p * originalEnergy D H := by
  simp only [R, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    originalEnergy_unscaledR F H hHG hGH]

/- The contraction gives energy commutation with M without any pPlus ≠ 0
   hypothesis. -/
private theorem originalEnergy_M
    (F : NullFrame D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) :
    originalEnergy D H * M F = M F * originalEnergy D H := by
  have hD := originalEnergy_unscaledD F H hHG hGH
  have hR := originalEnergy_unscaledR F H hHG hGH
  calc
    originalEnergy D H * M F =
        originalEnergy D H * ac (unscaledD F) (unscaledR F) := by
      rw [unscaled_contraction F]
    _ = (originalEnergy D H * unscaledD F) * unscaledR F +
        (originalEnergy D H * unscaledR F) * unscaledD F := by
      unfold ac
      noncomm_ring
    _ = (unscaledD F * originalEnergy D H) * unscaledR F +
        (unscaledR F * originalEnergy D H) * unscaledD F := by
      rw [hD, hR]
    _ = ac (unscaledD F) (unscaledR F) * originalEnergy D H := by
      simp only [ac, add_mul, mul_assoc, hD, hR]
    _ = M F * originalEnergy D H := by
      rw [unscaled_contraction F]

private theorem originalEnergy_invM
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) :
    invM F B * originalEnergy D H = originalEnergy D H * invM F B := by
  have hnumber : number (actualBasis F B) totalCount * originalEnergy D H =
      originalEnergy D H * number (actualBasis F B) totalCount := by
    simpa only [M_eq_number F B] using
      (originalEnergy_M F H hHG hGH).symm
  have hfun := commutes_function (actualBasis F B) totalCount
    (originalEnergy D H) hnumber
    (fun n => if n = 0 then 0 else (n : ℂ)⁻¹)
  exact hfun

/- Charge projection and inverse count are diagonal in the same actual basis.
   This is the required genuine charge commutation, rather than a preservation
   hypothesis. -/
private theorem chargeProject_number_commutes
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (p : Charge D) :
    number (actualBasis F B) totalCount * chargeProject p =
      chargeProject p * number (actualBasis F B) totalCount := by
  simp only [chargeProject_diagonal F B p]
  apply (actualBasis F B).ext
  intro i
  simp only [Module.End.mul_apply, number, diagonal_basis, map_smul, smul_smul]
  congr 1
  exact mul_comm _ _

private theorem invM_commutes_chargeProject
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (p : Charge D) :
    invM F B * chargeProject p = chargeProject p * invM F B := by
  have hfun := commutes_function (actualBasis F B) totalCount
    (chargeProject p) (chargeProject_number_commutes F B p)
    (fun n => if n = 0 then 0 else (n : ℂ)⁻¹)
  exact hfun

private theorem chargeProject_h
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (p q : Charge D) :
    chargeProject p * h F B q = h F B q * chargeProject p := by
  change chargeProject p * (R F q * invM F B) =
    (R F q * invM F B) * chargeProject p
  calc
    chargeProject p * (R F q * invM F B) =
        (chargeProject p * R F q) * invM F B := by noncomm_ring
    _ = (R F q * chargeProject p) * invM F B := by
      rw [chargeProject_R F p q]
    _ = R F q * (chargeProject p * invM F B) := by noncomm_ring
    _ = R F q * (invM F B * chargeProject p) := by
      rw [(invM_commutes_chargeProject F B p).symm]
    _ = (R F q * invM F B) * chargeProject p := by noncomm_ring

private theorem fixed_constraint_preserved
    (P A : Module.End ℂ (State D))
    (hPA : P * A = A * P) (x : State D) (hx : P x = x) :
    P (A x) = A x := by
  have hh := LinearMap.congr_fun hPA x
  change P (A x) = A (P x) at hh
  rw [hx] at hh
  exact hh

private theorem ac_kernel_preserved
    (B A : Module.End ℂ (State D))
    (hBA : ac B A = 0) (x : State D) (hx : B x = 0) :
    B (A x) = 0 := by
  have hh := LinearMap.congr_fun hBA x
  change B (A x) + A (B x) = 0 at hh
  rw [hx, map_zero, add_zero] at hh
  exact hh

private theorem commuting_kernel_preserved
    (E A : Module.End ℂ (State D))
    (hEA : E * A = A * E) (x : State D) (hx : E x = 0) :
    E (A x) = 0 := by
  have hh := LinearMap.congr_fun hEA x
  change E (A x) = A (E x) at hh
  rw [hx, map_zero] at hh
  exact hh

/- The literal relative constraints are preserved by the actual d0.  The two
   charge parameters are independent: p labels the fixed integral sector and
   q is the parameter of d0, so pPlus q may be zero. -/
theorem d0_preserves_original_relative_constraints
    (F : NullFrame D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (p q : Charge D) (x : State D)
    (hxCharge : chargeProject p x = x)
    (hxB0 : ghostB0 (D := D) x = 0)
    (hxEnergy :
      (D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.matterMode D H 0 +
        D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.ghostVirasoro D 0) x = 0) :
    chargeProject p (d0 F q x) = d0 F q x ∧
      ghostB0 (D := D) (d0 F q x) = 0 ∧
      (D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.matterMode D H 0 +
        D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.ghostVirasoro D 0)
        (d0 F q x) = 0 := by
  have hCharge := fixed_constraint_preserved
    (chargeProject p) (d0 F q) (chargeProject_d0 F p q) x hxCharge
  have hB0 := ac_kernel_preserved
    (ghostB0 (D := D)) (d0 F q) (b0_d0 F q) x hxB0
  have hEnergy := commuting_kernel_preserved
    (originalEnergy D H) (d0 F q)
    (originalEnergy_d0 F H hHG hGH q) x hxEnergy
  exact ⟨hCharge, hB0, hEnergy⟩

/- The same literal triple is preserved by the actual inverse-count homotopy.
   No nonzero-pPlus assumption is needed: h is defined with the original
   signed inverse scalar and the actual inverse-count operator. -/
theorem h_preserves_original_relative_constraints
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (p q : Charge D) (x : State D)
    (hxCharge : chargeProject p x = x)
    (hxB0 : ghostB0 (D := D) x = 0)
    (hxEnergy :
      (D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.matterMode D H 0 +
        D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.ghostVirasoro D 0) x = 0) :
    chargeProject p (h F B q x) = h F B q x ∧
      ghostB0 (D := D) (h F B q x) = 0 ∧
      (D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.matterMode D H 0 +
        D5.S3.VertexAlgebra.LatticeMatterGhostCoupling.ghostVirasoro D 0)
        (h F B q x) = 0 := by
  have hCharge := fixed_constraint_preserved
    (chargeProject p) (h F B q) (chargeProject_h F B p q) x hxCharge
  have hB0 := ac_kernel_preserved
    (ghostB0 (D := D)) (h F B q) (b0_h F B q) x hxB0
  have hEnergy := commuting_kernel_preserved
    (originalEnergy D H) (h F B q)
    (by
      change originalEnergy D H * (R F q * invM F B) =
        (R F q * invM F B) * originalEnergy D H
      have hR := originalEnergy_R F H hHG hGH q
      have hInv := originalEnergy_invM F B H hHG hGH
      calc
        originalEnergy D H * (R F q * invM F B) =
            (originalEnergy D H * R F q) * invM F B := by noncomm_ring
        _ = (R F q * originalEnergy D H) * invM F B := by rw [hR]
        _ = R F q * (originalEnergy D H * invM F B) := by noncomm_ring
        _ = R F q * (invM F B * originalEnergy D H) := by rw [hInv.symm]
        _ = (R F q * invM F B) * originalEnergy D H := by noncomm_ring)
    x hxEnergy
  exact ⟨hCharge, hB0, hEnergy⟩

end D5.S3.VertexAlgebra.LatticeQuartetEnergyPreservation
