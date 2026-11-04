/- GID: D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTGround
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTGround
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Original relative-shell energy constraints and exact-energy ground target. -/

import D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeShellDegreeBounds
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullOriginalRaising
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTRelativeZeroMode
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare
import D5.S3.HomologicalAlgebra.FinitePerturbation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
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


noncomputable section

namespace D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology.Energy

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
private theorem d0_preserves_original_relative_constraints
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
private theorem h_preserves_original_relative_constraints
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

end D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology.Energy

namespace D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology.Ground

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraConformal LatticePositiveEnergy
open LatticeLightConeCoordinates LatticeQuartetContraction
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open LatticeRelativeMassShell MvPolynomial
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open scoped BigOperators TensorProduct

variable {D : LatticeData}

/- The contraction's charge projector on the shell's ORIGINAL monomial basis. -/
private theorem chargeProject_original_basis (p : Charge D)
    (i : LatticeRelativeMassShell.TensorLabel D) :
    chargeProject p (LatticeRelativeMassShell.tensorBasis D i) =
      (if i.1.1 = p then (1 : ℂ) else 0) •
        LatticeRelativeMassShell.tensorBasis D i := by
  classical
  rw [LatticeRelativeMassShell.tensorBasis_apply]
  by_cases hi : i.1.1 = p
  · simp [chargeProject, chargeMatter, tp, hi]
  · simp [chargeProject, chargeMatter, tp, hi, Ne.symm hi]

private theorem chargeProject_original_diagonal (p : Charge D) :
    chargeProject p = diagonal (LatticeRelativeMassShell.tensorBasis D)
      (fun i => if i.1.1 = p then 1 else 0) := by
  apply (LatticeRelativeMassShell.tensorBasis D).ext
  intro i
  rw [chargeProject_original_basis, diagonal_basis]

private theorem chargeProject_original_coeff (p : Charge D) (x : State D)
    (i : LatticeRelativeMassShell.TensorLabel D) :
    LatticeRelativeMassShell.coeff D (chargeProject p x) i =
      if i.1.1 = p then LatticeRelativeMassShell.coeff D x i else 0 := by
  classical
  rw [chargeProject_original_diagonal]
  change (LatticeRelativeMassShell.tensorBasis D).repr
      (diagonal (LatticeRelativeMassShell.tensorBasis D)
        (fun j => if j.1.1 = p then 1 else 0) x) i = _
  rw [diagonal_coefficient]
  by_cases hi : i.1.1 = p
  · simp [hi, LatticeRelativeMassShell.coeff, LatticeRelativeMassShell.tensorCoeffEquiv]
  · simp [hi]

/- Identify the original charge condition, without substituting a new shell. -/
private theorem mem_fixedMomentum_iff_chargeProject (p : Charge D) (x : State D) :
    x ∈ LatticeRelativeMassShell.fixedMomentum D p ↔ chargeProject p x = x := by
  classical
  constructor
  · intro hx
    apply (LatticeRelativeMassShell.tensorCoeffEquiv D).injective
    ext i
    change LatticeRelativeMassShell.coeff D (chargeProject p x) i =
      LatticeRelativeMassShell.coeff D x i
    rw [chargeProject_original_coeff]
    by_cases hi : i.1.1 = p
    · simp [hi]
    · simp [hi, (LatticeRelativeMassShell.mem_fixedMomentum_iff D p x).mp hx i hi]
  · intro hx
    apply (LatticeRelativeMassShell.mem_fixedMomentum_iff D p x).mpr
    intro i hi
    have hc := congrArg (fun y : State D => LatticeRelativeMassShell.coeff D y i) hx
    rw [chargeProject_original_coeff] at hc
    simpa [hi] using hc.symm

/- The original zero-count projector preserves the literal relative shell. -/
private theorem P0_mem_shell
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (x : State D) (hx : x ∈ relativeMassShell D H p) :
    P0 F B x ∈ relativeMassShell D H p := by
  rcases hx with ⟨⟨hc, hb⟩, hL⟩
  have hcharge : chargeProject p x = x :=
    (mem_fixedMomentum_iff_chargeProject p x).mp hc
  have hcp : chargeProject p * P0 F B = P0 F B * chargeProject p := by
    rw [chargeProject_diagonal F B p]
    apply (actualBasis F B).ext
    intro i
    simp only [P0, projectZero, Module.End.mul_apply, diagonal_basis, map_smul, smul_smul]
    congr 1
    exact mul_comm _ _
  have hn : number (actualBasis F B) totalCount * totalL0 D H =
      totalL0 D H * number (actualBasis F B) totalCount := by
    simpa only [M_eq_number F B, LatticeRelativeBRSTCohomology.Energy.originalEnergy] using
      (LatticeRelativeBRSTCohomology.Energy.originalEnergy_M F H hHG hGH).symm
  have hep : P0 F B * totalL0 D H = totalL0 D H * P0 F B :=
    commutes_function (actualBasis F B) totalCount (totalL0 D H) hn
      (fun n => if n = 0 then 1 else 0)
  refine ⟨⟨(mem_fixedMomentum_iff_chargeProject p _).mpr ?_, ?_⟩, ?_⟩
  · simpa only [Module.End.mul_apply, hcharge] using LinearMap.congr_fun hcp x
  · change ghostB0 (P0 F B x) = 0
    change ghostB0 x = 0 at hb
    simpa only [Module.End.mul_apply, hb, map_zero] using
      LinearMap.congr_fun (P0_commutes_b0 F B).symm x
  · change totalL0 D H (P0 F B x) = 0
    change totalL0 D H x = 0 at hL
    simpa only [Module.End.mul_apply, hL, map_zero] using
      (LinearMap.congr_fun hep x).symm

namespace GRE
export D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
  (L_zero_ket energy siteEnergy_one)
end GRE

abbrev Polynomial (t : ℕ) := MvPolynomial (Fin t × ℕ) ℂ
abbrev Exponent (t : ℕ) := (Fin t × ℕ) →₀ ℕ

/- Actual positive oscillator frequencies, with multiplicity. -/
def weight {t : ℕ} (nu : Exponent t) : ℕ :=
  Finsupp.weight (fun x : Fin t × ℕ => x.2 + 1) nu

/- Independent coefficient definition; no cutoff, P0, or shell in the definition. -/
def energyTarget (D : LatticeData) (t : ℕ) (p : Charge D) :
    Submodule ℂ (Polynomial t) where
  carrier := {f | ∀ nu, (weight nu : ℤ) + chargeEnergy D p ≠ 1 → f.coeff nu = 0}
  zero_mem' := by intro nu hnu; simp
  add_mem' := by
    intro f g hf hg nu hnu
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      hf nu hnu, hg nu hnu, add_zero]
  smul_mem' := by
    intro z f hf nu hnu
    simp [hf nu hnu]

variable (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

/- Independent literal target, the genuine image of energy-restricted polynomials. -/
def target (p : Charge D) : Submodule ℂ (State D) :=
  (energyTarget D t p).map (groundMap F B p)

private def groundIndex (p : Charge D) (nu : Exponent t) : StateIndex D t :=
  (⟨p, nu.mapDomain transverseVariable⟩, {1})

private theorem groundIndex_injective (p : Charge D) :
    Function.Injective (groundIndex (t := t) p) := by
  intro nu mu he
  apply Finsupp.mapDomain_injective transverseVariable_injective
  exact congrArg (fun i : StateIndex D t => i.1.2) he

/- Recover every polynomial coefficient in the supplied actual basis. -/
private theorem groundMap_coefficient (p : Charge D) (f : Polynomial t) (nu : Exponent t) :
    (actualBasis F B).repr (groundMap F B p f) (groundIndex p nu) = f.coeff nu := by
  classical
  let read : State D →ₗ[ℂ] ℂ := (actualBasis F B).coord (groundIndex p nu)
  have he : read.comp (groundMap F B p) = MvPolynomial.lcoeff ℂ nu := by
    apply (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ).ext
    intro mu
    change (actualBasis F B).repr (groundMap F B p (monomial mu 1))
      (groundIndex p nu) = (monomial mu (1 : ℂ)).coeff nu
    rw [groundMap_monomial]
    change (actualBasis F B).repr (actualBasis F B (groundIndex p mu))
      (groundIndex p nu) = _
    rw [(actualBasis F B).repr_self]
    by_cases hm : mu = nu
    · subst mu; simp
    · have hi : groundIndex (D := D) p mu ≠ groundIndex p nu :=
        fun h => hm (groundIndex_injective p h)
      simp [hi, hm]
  exact LinearMap.congr_fun he f

theorem groundMap_injective (p : Charge D) : Function.Injective (groundMap F B p) := by
  intro f g he
  ext nu
  have hc := congrArg (fun x : State D => (actualBasis F B).repr x (groundIndex p nu)) he
  simpa only [groundMap_coefficient] using hc

/- q-1 is an integer scalar; -1 comes from the original ket {1}. -/
private def energyOperator (p : Charge D) : Module.End ℂ (Polynomial t) :=
  diagonal (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ)
    (fun nu => (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ))

private theorem energyOperator_coefficient (p : Charge D) (f : Polynomial t) (nu : Exponent t) :
    (energyOperator p f).coeff nu =
      (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) * f.coeff nu := by
  change (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ).repr
      (energyOperator p f) nu = _
  exact diagonal_coefficient (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ) _ f nu

private theorem energyOperator_monomial (p : Charge D) (nu : Exponent t) :
    energyOperator p (monomial nu 1) =
      (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) • monomial nu 1 := by
  change energyOperator p ((MvPolynomial.basisMonomials (Fin t × ℕ) ℂ) nu) = _
  exact diagonal_basis (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ) _ nu

private theorem energyOperator_zero_iff (p : Charge D) (f : Polynomial t) :
    energyOperator p f = 0 ↔ f ∈ energyTarget D t p := by
  constructor
  · intro he nu hnu
    have hz : (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (weight nu : ℤ) + chargeEnergy D p - 1 ≠ 0 by omega)
    have hc := congrArg (fun g : Polynomial t => g.coeff nu) he
    rw [energyOperator_coefficient] at hc
    exact (mul_eq_zero.mp hc).resolve_left hz
  · intro hf
    ext nu
    change (energyOperator p f).coeff nu = 0
    rw [energyOperator_coefficient]
    by_cases he : (weight nu : ℤ) + chargeEnergy D p = 1
    · have hz : (weight nu : ℤ) + chargeEnergy D p - 1 = 0 := by omega
      simp [hz]
    · rw [hf nu he, mul_zero]

/- Frequency is unchanged by the transverse variable injection. -/
private theorem frequencyWeight_mapDomain (nu : Exponent t) :
    Finsupp.weight frequencyWeight (nu.mapDomain transverseVariable) = weight nu := by
  simp only [Finsupp.weight_apply, weight, smul_eq_mul]
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)

private theorem ghost_ground_energy : GRE.energy ({1} : Finset ℕ) = -1 := by
  simp [D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.energy, GRE.siteEnergy_one]

/- The actual L0 calculation, using the supplied inverse coordinate grading. -/
private theorem totalL0_groundMap_monomial
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (nu : Exponent t) :
    totalL0 D H (groundMap F B p (monomial nu 1)) =
      (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) •
        groundMap F B p (monomial nu 1) := by
  let Q : PolynomialCoordinates (NullFrame.Label t) :=
    monomial (nu.mapDomain transverseVariable) 1
  have hQ : IsWeightedHomogeneous frequencyWeight Q (weight nu) := by
    apply isWeightedHomogeneous_monomial
    exact frequencyWeight_mapDomain nu
  have hP : IsWeightedHomogeneous (oscillatorWeight D)
      ((F.coordinateEquiv B).symm Q) (weight nu) :=
    (F.frequency_grading B _ _).mp (by simpa only [AlgEquiv.apply_symm_apply] using hQ)
  have hL := sugawaraMode_weighted_homogeneous D H hHG hGH p
    ((F.coordinateEquiv B).symm Q) (weight nu) hP
  simp only [groundMap_sector, rename_monomial]
  change (sugawaraMode D H 0 (Finsupp.single p ((F.coordinateEquiv B).symm Q))
      ⊗ₜ[ℂ] ket {1}) +
    (Finsupp.single p ((F.coordinateEquiv B).symm Q) ⊗ₜ[ℂ]
      D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0 (ket {1})) = _
  rw [hL, GRE.L_zero_ket, ghost_ground_energy, TensorProduct.tmul_smul]
  simp only [TensorProduct.smul_tmul', Int.cast_neg, Int.cast_one]
  change ((weight nu : ℂ) + (bilinear D p p : ℂ) / 2) •
      sector F B p Q (ket {1}) + (-1 : ℂ) • sector F B p Q (ket {1}) =
    (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) • sector F B p Q (ket {1})
  rw [← add_smul]
  congr 1
  rw [← chargeEnergy_complex_half D p]
  push_cast; ring

/- Exact all-polynomial intertwining, before imposing an energy condition. -/
private theorem totalL0_groundMap
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) :
    (totalL0 D H).comp (groundMap F B p) =
      (groundMap F B p).comp (energyOperator p) := by
  apply (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ).ext
  intro nu
  change totalL0 D H (groundMap F B p (monomial nu 1)) =
    groundMap F B p (energyOperator p (monomial nu 1))
  rw [totalL0_groundMap_monomial F B H hHG hGH]
  rw [energyOperator_monomial, map_smul]

private theorem groundMap_mem_shell_iff
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (f : Polynomial t) :
    groundMap F B p f ∈ relativeMassShell D H p ↔ f ∈ energyTarget D t p := by
  have ids := groundMap_identities F B p
  have hb : ghostB0 (groundMap F B p f) = 0 := LinearMap.congr_fun ids.2.1 f
  have hc : chargeProject p (groundMap F B p f) = groundMap F B p f :=
    LinearMap.congr_fun ids.2.2 f
  have hmom : groundMap F B p f ∈ fixedMomentum D p :=
    (mem_fixedMomentum_iff_chargeProject p _).mpr hc
  have henergy := LinearMap.congr_fun (totalL0_groundMap F B H hHG hGH p) f
  change totalL0 D H (groundMap F B p f) = groundMap F B p (energyOperator p f) at henergy
  constructor
  · intro hx
    apply (energyOperator_zero_iff p f).mp
    apply groundMap_injective F B p
    rw [map_zero, ← henergy]
    exact hx.2
  · intro hf
    refine ⟨⟨hmom, hb⟩, ?_⟩
    change totalL0 D H (groundMap F B p f) = 0
    rw [henergy, (energyOperator_zero_iff p f).mpr hf, map_zero]

/- The target was defined without P0. This theorem identifies the literal kernels. -/
private theorem target_eq_shell_inf_ker
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) :
    target F B p = relativeMassShell D H p ⊓ LinearMap.ker (M F) := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨(groundMap_mem_shell_iff F B H hHG hGH p f).mpr hf,
      LinearMap.congr_fun (groundMap_identities F B p).1 f⟩
  · rintro ⟨hx, hm⟩
    have hb : ghostB0 x = 0 := hx.1.2
    have hc : chargeProject p x = x :=
      (mem_fixedMomentum_iff_chargeProject p x).mp hx.1.1
    obtain ⟨f, hf⟩ := (literal_relative_ground F B p x).mp ⟨hm, hb, hc⟩
    have he : groundMap F B p f = x := (hf.trans (groundMap_apply F B p f).symm).symm
    refine ⟨f, ?_, he⟩
    apply (groundMap_mem_shell_iff F B H hHG hGH p f).mp
    rwa [he]

theorem target_projection_fix (p : Charge D) (u : target F B p) : P0 F B u = u := by
  have hm : M F (u : State D) = 0 := by
    rcases u.property with ⟨f, hf, he⟩
    rw [← he]
    exact LinearMap.congr_fun (groundMap_identities F B p).1 f
  -- Use the actual inverse-count identity invM*M=1-P0 on this ground image.
  have hs := LinearMap.congr_fun (spectral_projection_inverse F B).2.1 (u : State D)
  have hz : (u : State D) - P0 F B u = 0 := by
    simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      hm, map_zero] using hs.symm
  exact (sub_eq_zero.mp hz).symm

section ShellMaps

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (p : Charge D)

/- Literal inclusion into the SAME original relativeMassShell. -/
def inclusion : target F B p →ₗ[ℂ] relativeMassShell D H p where
  toFun u := ⟨u, ((target_eq_shell_inf_ker F B H hHG hGH p).le u.property).1⟩
  map_add' u v := Subtype.ext rfl
  map_smul' z u := Subtype.ext rfl

/- Genuine stability is supplied here, not an additional endpoint hypothesis. -/
private def shellP0 : Module.End ℂ (relativeMassShell D H p) where
  toFun x := ⟨P0 F B x,
    P0_mem_shell F B H hHG hGH p x x.property⟩
  map_add' _x _y := Subtype.ext (map_add _ _ _)
  map_smul' _z _x := Subtype.ext (map_smul _ _ _)

def shellD0 : Module.End ℂ (relativeMassShell D H p) where
  toFun x := ⟨d0 F p x,
    by
      have hx := x.property
      obtain ⟨hc, hb, he⟩ :=
        LatticeRelativeBRSTCohomology.Energy.d0_preserves_original_relative_constraints
          F H hHG hGH p p x
          ((mem_fixedMomentum_iff_chargeProject p x).mp hx.1.1) hx.1.2 hx.2
      exact ⟨⟨(mem_fixedMomentum_iff_chargeProject p _).mpr hc, hb⟩, he⟩⟩
  map_add' _x _y := Subtype.ext (map_add _ _ _)
  map_smul' _z _x := Subtype.ext (map_smul _ _ _)

def shellH : Module.End ℂ (relativeMassShell D H p) where
  toFun x := ⟨h F B p x,
    by
      have hx := x.property
      obtain ⟨hc, hb, he⟩ :=
        LatticeRelativeBRSTCohomology.Energy.h_preserves_original_relative_constraints
          F B H hHG hGH p p x
          ((mem_fixedMomentum_iff_chargeProject p x).mp hx.1.1) hx.1.2 hx.2
      exact ⟨⟨(mem_fixedMomentum_iff_chargeProject p _).mpr hc, hb⟩, he⟩⟩
  map_add' _x _y := Subtype.ext (map_add _ _ _)
  map_smul' _z _x := Subtype.ext (map_smul _ _ _)

/- P0 with its actual codomain restricted by the proved target identification. -/
def projection : relativeMassShell D H p →ₗ[ℂ] target F B p where
  toFun x := ⟨P0 F B x, by
    rw [target_eq_shell_inf_ker F B H hHG hGH p]
    refine ⟨(shellP0 F B H hHG hGH p x).property, ?_⟩
    exact LinearMap.congr_fun (spectral_projection_inverse F B).2.2.2.1 x⟩
  map_add' _x _y := Subtype.ext (map_add _ _ _)
  map_smul' _z _x := Subtype.ext (map_smul _ _ _)

theorem projection_inclusion :
    (projection F B H hHG hGH p).comp (inclusion F B H hHG hGH p) = LinearMap.id := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact target_projection_fix F B p u

theorem shell_d0_square :
    shellD0 F H hHG hGH p * shellD0 F H hHG hGH p = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change d0 F p (d0 F p x) = 0
  exact LinearMap.congr_fun (d0_square F p) x

theorem shell_d0_inclusion :
    (shellD0 F H hHG hGH p).comp (inclusion F B H hHG hGH p) = 0 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  change d0 F p u = 0
  rw [← target_projection_fix F B p u]
  exact LinearMap.congr_fun (d0_mul_P0 F B p) u

theorem projection_shell_d0 :
    (projection F B H hHG hGH p).comp (shellD0 F H hHG hGH p) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change P0 F B (d0 F p x) = 0
  exact LinearMap.congr_fun (P0_mul_d0 F B p) x

/- This is the ONLY endpoint needing nonzero pPlus. -/
theorem shell_contraction (hp : F.pPlus p ≠ 0) :
    shellD0 F H hHG hGH p * shellH F B H hHG hGH p +
      shellH F B H hHG hGH p * shellD0 F H hHG hGH p =
    1 - (inclusion F B H hHG hGH p).comp (projection F B H hHG hGH p) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change d0 F p (h F B p x) + h F B p (d0 F p x) = x - P0 F B x
  exact LinearMap.congr_fun (homotopy_contraction F B p hp) x

theorem shell_h_square : shellH F B H hHG hGH p * shellH F B H hHG hGH p = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change h F B p (h F B p x) = 0
  exact LinearMap.congr_fun (homotopy_square F B p) x

theorem shell_h_inclusion :
    (shellH F B H hHG hGH p).comp (inclusion F B H hHG hGH p) = 0 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  change h F B p u = 0
  rw [← target_projection_fix F B p u]
  exact LinearMap.congr_fun (h_mul_P0 F B p) u

theorem projection_shell_h :
    (projection F B H hHG hGH p).comp (shellH F B H hHG hGH p) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change P0 F B (h F B p x) = 0
  exact LinearMap.congr_fun (P0_mul_h F B p) x

end ShellMaps

end D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology.Ground
