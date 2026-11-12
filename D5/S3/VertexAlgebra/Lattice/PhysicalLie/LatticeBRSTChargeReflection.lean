/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTChargeReflection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTChargeReflection
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Literal semilinear charge reflection on the original matter-ghost tensor. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing
import Batteries.Tactic.OpenPrivate

/-!
SOURCE ONLY, UNCOMPILED. This file makes no native, Reg, or descent claim.
The matter reflection and its coefficient conjugation are the existing
LatticeInvolution and OriginalMatterHermitian maps. The tensor extension
below conjugates ghost coefficients in the ACTUAL occupation basis.

Attribution: the imported lattice/BRST constructions retain the Bakalov--Kac,
Carnahan, Kytölä, Becchi--Rouet--Stora--Tyutin, Kato--Ogawa and Lian--Zuckerman
attribution of their suppliers; tensor and finite-support algebra is Mathlib.
There is no positivity, unimodularity, charge cut, or replacement differential.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private slices slices_tmul_ket from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian
open private cubic_eq from D5.S3.Quantum.Fermionic.BcGhostCubic
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeReflection

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField (occurrences)
open LatticeSugawaraCurrents LatticeInvolution LatticeMatterGhostCoupling
open SourceBPZ.OriginalMatterHermitian
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostHermitian (phase_real)

variable {D : LatticeData}

private def matterC : Carrier D →ₛₗ[starRingEnd ℂ] Carrier D where
  toFun v := theta D (kappaCarrier v)
  map_add' v w := by simp only [kappaCarrier_add, map_add]
  map_smul' a v := by simp only [kappaCarrier_smul, map_smul]; rfl

private theorem matterC_square (v : Carrier D) : matterC (matterC v) = v := by
  simp only [matterC, LinearMap.coe_mk, AddHom.coe_mk,
    kappaCarrier_theta, kappaCarrier_involutive, theta_square]

private def ghostC : Fock →ₛₗ[starRingEnd ℂ] Fock where
  toFun g := g.mapRange (starRingEnd ℂ) (map_zero _)
  map_add' g h := by ext S; simp
  map_smul' a g := by ext S; simp

@[simp] private theorem ghostC_apply (g : Fock) (S : Finset ℕ) :
    ghostC g S = star (g S) := rfl

@[simp] private theorem ghostC_ket (S : Finset ℕ) : ghostC (ket S) = ket S := by
  classical
  ext T
  by_cases h : S = T <;> simp [ghostC_apply, ket, h]

/-- The semilinear involution C on the literal State D. In the ghost-slice
coordinates it is theta(kappaCarrier(-)) on each original matter coefficient.
Thus it conjugates a tensor coefficient once, rather than twice. -/
def conjugation (D : LatticeData) : State D →ₛₗ[starRingEnd ℂ] State D where
  toFun x := (slices D).symm
    (((slices D) x).mapRange matterC (map_zero _))
  map_add' x y := by
    apply (slices D).injective
    ext S
    simp
  map_smul' a x := by
    apply (slices D).injective
    ext S
    simp

@[simp] private theorem slices_conjugation (x : State D) (S : Finset ℕ) :
    (slices D) (conjugation D x) S = matterC ((slices D x) S) := by
  simp only [conjugation, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]

@[simp] private theorem conjugation_tmul_ket (v : Carrier D) (S : Finset ℕ) :
    conjugation D (v ⊗ₜ[ℂ] ket S) = matterC v ⊗ₜ[ℂ] ket S := by
  apply (slices D).injective
  ext T
  simp only [slices_conjugation, slices_tmul_ket]
  by_cases h : S = T <;> simp [Finsupp.single_apply, h]

private theorem conjugation_tmul (v : Carrier D) (g : Fock) :
    conjugation D (v ⊗ₜ[ℂ] g) = matterC v ⊗ₜ[ℂ] ghostC g := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp only [TensorProduct.tmul_add, map_add, hg, hh]
  | single S a =>
      have ha : Finsupp.single S a = a • ket S := by simp [ket]
      simp only [ha, TensorProduct.tmul_smul, map_smulₛₗ,
        conjugation_tmul_ket, ghostC_ket]

/-- C really is an involution on every original finite tensor state. -/
theorem conjugation_involutive (x : State D) :
    conjugation D (conjugation D x) = x := by
  apply (slices D).injective
  ext S
  simp only [slices_conjugation, matterC_square]

/-- Exact original basis formula, with oscillator NUMBER rather than energy
in the sign. Charges and modes have no sign or nonzero restrictions. -/
example (p : Charge D) (e : Index D →₀ ℕ) (S : Finset ℕ)
    (a : ℂ) :
    conjugation D
        (a • (Finsupp.single p (MvPolynomial.monomial e 1) ⊗ₜ[ℂ] ket S)) =
      (star a * (-1 : ℂ) ^ (occurrences D e).length) •
        (Finsupp.single (-p) (MvPolynomial.monomial e 1) ⊗ₜ[ℂ] ket S) := by
  rw [map_smulₛₗ, conjugation_tmul_ket]
  change star a •
    (thetaLinear D (Finsupp.single p
      (kappaOsc (MvPolynomial.monomial e 1))) ⊗ₜ[ℂ] ket S) = _
  have hk : kappaOsc (MvPolynomial.monomial e 1 : Oscillator D) =
      MvPolynomial.monomial e 1 := by simp [kappaOsc]
  rw [hk, theta_single, sigma_monomial]
  simp only [← Finsupp.smul_single, TensorProduct.smul_tmul', smul_smul]

private theorem ghostC_create (j : ℕ) (g : Fock) :
    ghostC (create j g) = create j (ghostC g) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp only [map_add, hg, hh]
  | single S a =>
      have ha : Finsupp.single S a = a • ket S := by simp [ket]
      by_cases hj : j ∈ S <;>
        simp [ha, create_ket, hj, map_smulₛₗ, phase_real]

private theorem ghostC_annihilate (j : ℕ) (g : Fock) :
    ghostC (annihilate j g) = annihilate j (ghostC g) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp only [map_add, hg, hh]
  | single S a =>
      have ha : Finsupp.single S a = a • ket S := by simp [ket]
      by_cases hj : j ∈ S <;>
        simp [ha, annihilate_ket, hj, map_smulₛₗ, phase_real]

private theorem ghostC_b (m : ℤ) (g : Fock) :
    ghostC (BcGhostFock.b m g) = BcGhostFock.b m (ghostC g) := by
  unfold BcGhostFock.b
  split_ifs <;> first | exact ghostC_create _ _ | exact ghostC_annihilate _ _

private theorem ghostC_c (m : ℤ) (g : Fock) :
    ghostC (BcGhostFock.c m g) = BcGhostFock.c m (ghostC g) := by
  unfold BcGhostFock.c
  split_ifs <;> first | exact ghostC_create _ _ | exact ghostC_annihilate _ _

private theorem tensor_covariance
    (A : Module.End ℂ (Carrier D)) (G : Module.End ℂ Fock)
    (hA : ∀ v, matterC (A v) = A (matterC v))
    (hG : ∀ g, ghostC (G g) = G (ghostC g)) (x : State D) :
    conjugation D (TensorProduct.map A G x) =
      TensorProduct.map A G (conjugation D x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v g => simp only [TensorProduct.map_tmul, conjugation_tmul, hA, hG]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem matterC_neutral (i : Fin D.rank) (m : ℤ) (v : Carrier D) :
    matterC (neutralMode D i m v) = -neutralMode D i m (matterC v) := by
  exact (congrArg (theta D) (kappaCarrier_neutralMode i m v)).trans
    (theta_neutralMode D i m (kappaCarrier v))

private theorem matterC_normal (i j : Fin D.rank) (k l : ℤ) (v : Carrier D) :
    matterC (normalSummand D i j k l v) =
      normalSummand D i j k l (matterC v) := by
  unfold normalSummand
  split_ifs <;>
    simp only [Module.End.mul_apply, matterC_neutral, map_neg, neg_neg]

private theorem matterC_sugawara
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m : ℤ) (v : Carrier D) :
    matterC (sugawaraMode D H m v) = sugawaraMode D H m (matterC v) := by
  have hH (i j : Fin D.rank) : star (H i j) = H i j :=
    congrFun (congrFun (conjugateH_eq_H H hHG hGH) i) j
  rw [sugawaraMode_finsum, map_smulₛₗ, map_sum, sugawaraMode_finsum]
  simp only [map_inv₀, map_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smulₛₗ, hH, map_finsum matterC.toAddMonoidHom
    (normalSummand_finite D i j m v)]
  congr 1
  apply finsum_congr
  intro k
  exact matterC_normal i j k (m-k) v

private theorem ghostC_cubic (p q : ℤ) (g : Fock) :
    ghostC (BcGhostBRST.cubic p q g) = BcGhostBRST.cubic p q (ghostC g) := by
  simp only [cubic_eq]
  split_ifs <;> simp only [Module.End.mul_apply, ghostC_b, ghostC_c]

private theorem ghostC_cubicTerm (pq : ℤ × ℤ) (g : Fock) :
    ghostC (BcGhostBRST.cubicTerm pq g) =
      BcGhostBRST.cubicTerm pq (ghostC g) := by
  simp only [BcGhostBRST.cubicTerm, LinearMap.smul_apply, map_smulₛₗ,
    map_mul, map_div₀, map_ofNat, map_intCast, ghostC_cubic]

private theorem ghostC_Qg (g : Fock) :
    ghostC (BcGhostBRST.Qg g) = BcGhostBRST.Qg (ghostC g) := by
  change ghostC (∑ᶠ pq : ℤ × ℤ, BcGhostBRST.cubicTerm pq g) =
    ∑ᶠ pq : ℤ × ℤ, BcGhostBRST.cubicTerm pq (ghostC g)
  rw [map_finsum ghostC.toAddMonoidHom (BcGhostBRST.cubicTerm_finite g)]
  exact finsum_congr fun pq => ghostC_cubicTerm pq g

private theorem conjugation_summand
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m : ℤ) (x : State D) :
    conjugation D (summand D H m x) = summand D H m (conjugation D x) :=
  tensor_covariance (sugawaraMode D H m) (BcGhostFock.c (-m))
    (matterC_sugawara H hHG hGH m) (ghostC_c (-m)) x

private theorem conjugation_T
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) :
    conjugation D (T D H x) = T D H (conjugation D x) := by
  change conjugation D (∑ᶠ m : ℤ, summand D H m x) =
    ∑ᶠ m : ℤ, summand D H m (conjugation D x)
  rw [map_finsum (conjugation D).toAddMonoidHom (summand_finite D H x)]
  exact finsum_congr fun m => conjugation_summand H hHG hGH m x

/-- Commutation with the original global Q, from its actual finite cubic
and Sugawara summands. Both inverse-Gram equations are retained. -/
theorem conjugation_totalCharge
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) :
    conjugation D (LatticeBRST.totalCharge D H x) =
      LatticeBRST.totalCharge D H (conjugation D x) := by
  have hg := tensor_covariance (LinearMap.id : Module.End ℂ (Carrier D))
    BcGhostBRST.Qg (fun _ => rfl) ghostC_Qg x
  simpa only [LatticeBRST.totalCharge, LinearMap.add_apply, map_add,
    conjugation_T H hHG hGH, LatticeBRST.ghostCharge] using
    congrArg (fun z => T D H (conjugation D x) + z) hg

/-- The original b modes commute with C; this includes the relative b0. -/
theorem conjugation_ghostB (m : ℤ) (x : State D) :
    conjugation D (LatticeMatterGhostCoupling.ghostB D m x) =
      LatticeMatterGhostCoupling.ghostB D m (conjugation D x) :=
  tensor_covariance LinearMap.id (BcGhostFock.b m) (fun _ => rfl) (ghostC_b m) x

/-- The original c modes commute with C; in particular the insertion remains c0. -/
theorem conjugation_ghostC (m : ℤ) (x : State D) :
    conjugation D (LatticeMatterGhostCoupling.ghostC D m x) =
      LatticeMatterGhostCoupling.ghostC D m (conjugation D x) :=
  tensor_covariance LinearMap.id (BcGhostFock.c m) (fun _ => rfl) (ghostC_c m) x

private theorem ghostC_number (g : Fock) :
    ghostC (BcGhostCharge.ghostNumber g) = BcGhostCharge.ghostNumber (ghostC g) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp only [map_add, hg, hh]
  | single S a =>
      have ha : Finsupp.single S a = a • ket S := by simp [ket]
      simp only [ha, map_smul, map_smulₛₗ, number_ket, ghostC_ket, map_intCast]

private theorem conjugation_number (x : State D) :
    conjugation D (LatticeMatterGhostDegree.tensorNumber D x) =
      LatticeMatterGhostDegree.tensorNumber D (conjugation D x) :=
  tensor_covariance LinearMap.id BcGhostCharge.ghostNumber
    (fun _ => rfl) ghostC_number x

private theorem conjugation_totalL0
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) :
    conjugation D (LatticeBRSTZeroEnergyReduction.totalL0 D H x) =
      LatticeBRSTZeroEnergyReduction.totalL0 D H (conjugation D x) := by
  have hw (z : State D) : LatticeBRSTZeroEnergyReduction.totalL0 D H z =
      LatticeBRST.totalCharge D H (LatticeMatterGhostCoupling.ghostB D 0 z) +
        LatticeMatterGhostCoupling.ghostB D 0 (LatticeBRST.totalCharge D H z) :=
    (LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0) z).symm
  rw [hw, map_add, conjugation_totalCharge H hHG hGH,
    conjugation_ghostB, conjugation_ghostB, conjugation_totalCharge H hHG hGH,
    hw]

/-- All four literal physical equations are preserved. Rank 26 is kept in
the original standing scope; no integral determinant-unit assumption is used. -/
theorem conjugation_physical
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H) :
    conjugation D (x : State D) ∈ D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← conjugation_totalCharge H hHG hGH, x.property.1, map_zero]
  · rw [← conjugation_ghostB, x.property.2.1, map_zero]
  · rw [← conjugation_number, x.property.2.2.1]
  · rw [← conjugation_totalL0 H hHG hGH, x.property.2.2.2, map_zero]

-- The inverse equations over C do NOT supply the integer determinant-unit
-- premise of the canonical all-field endpoint. This anonymous exact matrix
-- countercheck uses the permitted G=2I, H=I/2 in the original rank 26.
example : ∃ G : Matrix (Fin 26) (Fin 26) ℤ,
    ∃ H : Matrix (Fin 26) (Fin 26) ℂ,
      H * G.map (Int.castRingHom ℂ) = 1 ∧
        G.map (Int.castRingHom ℂ) * H = 1 ∧ ¬IsUnit G.det := by
  let G : Matrix (Fin 26) (Fin 26) ℤ := (2 : ℤ) • 1
  let H : Matrix (Fin 26) (Fin 26) ℂ := (2 : ℂ)⁻¹ • 1
  have hG : G.map (Int.castRingHom ℂ) = (2 : ℂ) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [G, Matrix.one_apply, hij]
  refine ⟨G, H, ?_, ?_, ?_⟩
  · rw [hG]
    norm_num [H, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  · rw [hG]
    norm_num [H, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  · norm_num [G, Matrix.det_smul, Int.isUnit_iff]

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeReflection
