/- GID: D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete actual twisted first-grade spectral projectors and multiplicities. -/

/-
Classical twisted lattice construction: Frenkel--Lepowsky--Meurman;
Dong--Nagatomo, math/9808088, section 3.2;
Bakalov--Kac, math/0402315, section 4.
The existing suppliers retain their respective copyright and attribution.
-/

import D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Batteries.Tactic.OpenPrivate

/-! Complete spectral projectors for the actual norm-four twisted field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open private oddWeight_one_iff ground_square
  from D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades
open private charge_pairing from D5.S3.VertexAlgebra.LatticeSugawaraConformal

namespace D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient TwistedGround.OperatorAlgebra
open D5.S3.VertexAlgebra.HalfFock.NormFourLowestGrades MvPolynomial
open LatticeHalfFockParityT HalfFock.LatticeHalfFockParityField
open LatticeInvolution LatticeSugawaraConformal
open _root_.D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

/- Evenness forces nonzero mod-two reduction of a norm-four charge, and hence
   nonzero charge in the actual quotient used by the ground representation. -/
private theorem norm_four_reduction_ne_zero (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : reduceCharge D a ≠ 0 := by
  classical
  intro hz
  have he : ∀ i : Fin D.rank, Even (a i) := by
    intro i
    have hi := congrFun hz i
    change (a i : ZMod 2) = 0 at hi
    exact ZMod.intCast_eq_zero_iff_even.mp hi
  choose b hb using he
  have scaled : bilinear D a a = 4 * bilinear D b b := by
    unfold bilinear
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hb i, hb j]
    ring
  have norm_b : bilinear D b b = 1 := by omega
  have parity := integral_cocycle_symmetrization D b b
  omega

private theorem norm_four_quotient_charge_ne_zero (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : quotientCharge D (groundLift D a) ≠ 0 := by
  have hred : quotientEquiv D (groundLift D a) =
      (⟨0, reduceCharge D a⟩ : ReducedExtension D) := by
    change reduction D (⟨0, a⟩ : Extension D) = _
    rfl
  change (quotientEquiv D (groundLift D a)).charge ≠ 0
  rw [hred]
  exact norm_four_reduction_ne_zero D a ha

private theorem ground_action_trace_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) :
    LinearMap.trace ℂ (ActualGround D hu) (groundAction D hu a) = 0 := by
  exact actual_quotient_charge_ground_trace_zero D hu (groundLift D a)
    (norm_four_quotient_charge_ne_zero D a ha)

private theorem rank_pos (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : 0 < D.rank := by
  by_contra hn
  have hr : D.rank = 0 := Nat.eq_zero_of_not_pos hn
  have hb : bilinear D a a = 0 := by simp [bilinear, hr]
  omega

private theorem ground_action_square (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) :
    groundAction D hu a * groundAction D hu a = 1 := by
  exact ground_square D hu a ha

/- The coordinate space below is NOT assumed to be the grade. Its tensor
   product is proved isomorphic to the complete production L0 eigengrade,
   using the production finite basis and the parent's weight-one proof. -/
abbrev FirstOscillator (D : LatticeData) := Fin D.rank → ℂ
abbrev FirstTensor (D : LatticeData) (hu : IsUnit D.G.det) :=
  FirstOscillator D ⊗[ℂ] ActualGround D hu

private def firstMonomial (D : LatticeData) (i : Fin D.rank) : OddFiber D 1 :=
  ⟨Finsupp.single (i, 0) 1, (oddWeight_one_iff D _).mpr ⟨i, rfl⟩⟩

private def firstMonomialEquiv (D : LatticeData) : Fin D.rank ≃ OddFiber D 1 :=
  Equiv.ofBijective (firstMonomial D) (by
    constructor
    · intro i j hij
      have h := congrArg Subtype.val hij
      have h' : (i, (0 : ℕ)) = (j, 0) :=
        (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h
      exact congrArg Prod.fst h'
    · rintro ⟨d, hd⟩
      obtain ⟨i, hi⟩ := (oddWeight_one_iff D d).mp hd
      exact ⟨i, Subtype.ext hi.symm⟩)

private def firstGradeBasis (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.Basis (Fin D.rank × Half (groundRank D hu)) ℂ (actualGrade D hu 1) :=
  (actualGradeBasis D hu 1).reindex
    ((firstMonomialEquiv D).symm.prodCongr (Equiv.refl _))

private theorem firstGradeBasis_coe (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (b : Half (groundRank D hu)) :
    (firstGradeBasis D hu (i, b) : ActualTensor D hu) =
      (X (i, 0) : Oscillator D) ⊗ₜ[ℂ] Pi.single b (1 : ℂ) := by
  simpa [firstGradeBasis, Module.Basis.reindex_apply, firstMonomialEquiv,
    firstMonomial, actualGradeVector, actual_basis_apply, MvPolynomial.X] using
    actualGradeBasis_coe D hu 1 (firstMonomial D i, b)

private def nativeBasis (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.Basis (Fin D.rank × Half (groundRank D hu)) ℂ (FirstTensor D hu) :=
  (Pi.basisFun ℂ (Fin D.rank)).tensorProduct (Pi.basisFun ℂ (Half (groundRank D hu)))

private theorem nativeBasis_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (b : Half (groundRank D hu)) :
    nativeBasis D hu (i, b) =
      Pi.single i (1 : ℂ) ⊗ₜ[ℂ] Pi.single b (1 : ℂ) := by
  simp [nativeBasis, Pi.basisFun_apply]

/-- A constructed equivalence with the complete actual grade. -/
def nativeGradeEquiv (D : LatticeData) (hu : IsUnit D.G.det) :
    FirstTensor D hu ≃ₗ[ℂ] actualGrade D hu 1 :=
  (nativeBasis D hu).repr.trans (firstGradeBasis D hu).repr.symm

private theorem nativeGradeEquiv_basis (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (b : Half (groundRank D hu)) :
    nativeGradeEquiv D hu (nativeBasis D hu (i, b)) = firstGradeBasis D hu (i, b) := by
  apply (firstGradeBasis D hu).repr.injective
  simp [nativeGradeEquiv]

private theorem nativeGradeEquiv_single_coe (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (u : ActualGround D hu) :
    (nativeGradeEquiv D hu (Pi.single i (1 : ℂ) ⊗ₜ[ℂ] u) : ActualTensor D hu) =
      (X (i, 0) : Oscillator D) ⊗ₜ[ℂ] u := by
  classical
  have expand : u = ∑ b, u b • Pi.single b (1 : ℂ) := pi_eq_sum_univ' u
  calc
    _ = (nativeGradeEquiv D hu (Pi.single i (1 : ℂ) ⊗ₜ[ℂ]
        (∑ b, u b • Pi.single b (1 : ℂ))) : ActualTensor D hu) := by rw [← expand]
    _ = _ := by
      simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul,
        Submodule.coe_sum, Submodule.coe_smul, ← nativeBasis_apply,
        nativeGradeEquiv_basis, firstGradeBasis_coe]
      simp_rw [← TensorProduct.tmul_smul]
      rw [← TensorProduct.tmul_sum, ← expand]

private theorem nativeGradeEquiv_tmul_coe (D : LatticeData) (hu : IsUnit D.G.det)
    (x : FirstOscillator D) (u : ActualGround D hu) :
    (nativeGradeEquiv D hu (x ⊗ₜ[ℂ] u) : ActualTensor D hu) =
      ∑ i : Fin D.rank, x i • ((X (i, 0) : Oscillator D) ⊗ₜ[ℂ] u) := by
  classical
  have expand : x = ∑ i, x i • Pi.single i (1 : ℂ) := pi_eq_sum_univ' x
  calc
    _ = (nativeGradeEquiv D hu ((∑ i, x i • Pi.single i (1 : ℂ)) ⊗ₜ[ℂ] u) :
        ActualTensor D hu) := by rw [← expand]
    _ = _ := by
      simp only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', map_sum, map_smul,
        Submodule.coe_sum, Submodule.coe_smul, nativeGradeEquiv_single_coe]

private def chargeCoordinates (D : LatticeData) (a : Charge D) : FirstOscillator D :=
  fun i => (a i : ℂ)

private theorem nativeGradeEquiv_charge_coe (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (u : ActualGround D hu) :
    (nativeGradeEquiv D hu (chargeCoordinates D a ⊗ₜ[ℂ] u) : ActualTensor D hu) =
      chargePolynomial D a ⊗ₜ[ℂ] u := by
  rw [nativeGradeEquiv_tmul_coe]
  simp only [chargeCoordinates, chargePolynomial, TensorProduct.sum_tmul,
    ← TensorProduct.smul_tmul']

/- P(x)=B(a,x)a on the first oscillator space. P/4 is the charge-line
   projection. These are ordinary linear maps, not a new spectral framework. -/
private def chargeFunctional (D : LatticeData) (a : Charge D) :
    FirstOscillator D →ₗ[ℂ] ℂ where
  toFun x := ∑ i, x i * (bilinear D a (unitCharge D i) : ℂ)
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc]

private theorem chargeFunctional_charge (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : chargeFunctional D a (chargeCoordinates D a) = 4 := by
  have h : (∑ i : Fin D.rank, (a i : ℂ) *
      (bilinear D a (unitCharge D i) : ℂ)) = (bilinear D a a : ℂ) := by
    exact_mod_cast charge_pairing D a a
  simpa [chargeFunctional, chargeCoordinates, ha] using h

@[simp] private theorem chargeFunctional_single (D : LatticeData) (a : Charge D)
    (i : Fin D.rank) :
    chargeFunctional D a (Pi.single i (1 : ℂ)) = (bilinear D a (unitCharge D i) : ℂ) := by
  classical
  simp [chargeFunctional, Pi.single_apply]

private def chargeRankOne (D : LatticeData) (a : Charge D) :
    Module.End ℂ (FirstOscillator D) :=
  (chargeFunctional D a).smulRight (chargeCoordinates D a)

private def chargeProjector (D : LatticeData) (a : Charge D) :
    Module.End ℂ (FirstOscillator D) := (1 / 4 : ℂ) • chargeRankOne D a

private theorem chargeProjector_idempotent (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : IsIdempotentElem (chargeProjector D a) := by
  change chargeProjector D a * chargeProjector D a = chargeProjector D a
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, chargeProjector, chargeRankOne,
    LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
    chargeFunctional_charge D a ha, smul_eq_mul, smul_smul]
  module

private theorem chargeProjector_trace (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) :
    LinearMap.trace ℂ (FirstOscillator D) (chargeProjector D a) = 1 := by
  rw [chargeProjector, map_smul, chargeRankOne, LinearMap.trace_smulRight,
    chargeFunctional_charge D a ha]
  norm_num

private def groundPlus (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) : Module.End ℂ (ActualGround D hu) :=
  (1 / 2 : ℂ) • (1 + s • groundAction D hu a)

private def groundMinus (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) : Module.End ℂ (ActualGround D hu) :=
  1 - groundPlus D hu a s

private theorem groundMinus_formula (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) :
    groundMinus D hu a s = (1 / 2 : ℂ) • (1 - s • groundAction D hu a) := by
  apply LinearMap.ext
  intro u
  simp only [groundMinus, groundPlus, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  module

private theorem groundPlus_idempotent (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    IsIdempotentElem (groundPlus D hu a s) := by
  let J : Module.End ℂ (ActualGround D hu) := s • groundAction D hu a
  have square : J * J = 1 := by
    dsimp [J]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ground_action_square D hu a ha,
      ← pow_two, hs, one_smul]
  have JJ (u : ActualGround D hu) : J (J u) = u := by
    exact LinearMap.congr_fun square u
  change ((1 / 2 : ℂ) • (1 + J)) * ((1 / 2 : ℂ) • (1 + J)) =
    ((1 / 2 : ℂ) • (1 + J))
  apply LinearMap.ext
  intro u
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, map_add, map_smul, JJ]
  module

private theorem groundPlus_trace (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) :
    LinearMap.trace ℂ (ActualGround D hu) (groundPlus D hu a s) =
      ((2 ^ (D.rank / 2) : ℕ) : ℂ) / 2 := by
  simp only [groundPlus, map_smul, map_add, LinearMap.trace_one,
    actual_ground_finrank, ground_action_trace_zero D hu a ha, smul_eq_mul,
    mul_zero, add_zero]
  ring

private theorem groundMinus_trace (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) :
    LinearMap.trace ℂ (ActualGround D hu) (groundMinus D hu a s) =
      ((2 ^ (D.rank / 2) : ℕ) : ℂ) / 2 := by
  rw [groundMinus, map_sub, LinearMap.trace_one, actual_ground_finrank,
    groundPlus_trace D hu a ha s]
  ring

private def nativeZero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) : Module.End ℂ (FirstTensor D hu) :=
  TensorProduct.map (1 - chargeProjector D a) (groundMinus D hu a s)

private def nativeSixteen (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) : Module.End ℂ (FirstTensor D hu) :=
  TensorProduct.map 1 (groundPlus D hu a s)

private def nativeHalf (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) : Module.End ℂ (FirstTensor D hu) :=
  TensorProduct.map (chargeProjector D a) (groundMinus D hu a s)

def nativeL (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) : Module.End ℂ (FirstTensor D hu) :=
  (1 / 16 : ℂ) • nativeSixteen D hu a s + (1 / 2 : ℂ) • nativeHalf D hu a s

private theorem native_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) :
    nativeZero D hu a s + nativeSixteen D hu a s + nativeHalf D hu a s = 1 := by
  apply TensorProduct.ext'
  intro x u
  simp only [nativeZero, nativeSixteen, nativeHalf, groundMinus,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    TensorProduct.map_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  module

private theorem native_eigenrelations (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    nativeL D hu a s * nativeZero D hu a s = 0 ∧
    nativeZero D hu a s * nativeL D hu a s = 0 ∧
    nativeL D hu a s * nativeSixteen D hu a s = (1 / 16 : ℂ) • nativeSixteen D hu a s ∧
    nativeSixteen D hu a s * nativeL D hu a s = (1 / 16 : ℂ) • nativeSixteen D hu a s ∧
    nativeL D hu a s * nativeHalf D hu a s = (1 / 2 : ℂ) • nativeHalf D hu a s ∧
    nativeHalf D hu a s * nativeL D hu a s = (1 / 2 : ℂ) • nativeHalf D hu a s := by
  have hR := chargeProjector_idempotent D a ha
  have hQ := groundPlus_idempotent D hu a ha s hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [nativeL, nativeZero, nativeSixteen, nativeHalf, groundMinus,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, ← TensorProduct.map_mul,
      hR.eq, hQ.eq, hR.one_sub.eq, hQ.one_sub.eq,
      hR.mul_one_sub_self, hR.one_sub_mul_self, hQ.mul_one_sub_self, hQ.one_sub_mul_self]

private theorem nativeL_single (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) (i : Fin D.rank) (u : ActualGround D hu) :
    nativeL D hu a s (Pi.single i (1 : ℂ) ⊗ₜ[ℂ] u) =
      (1 / 32 : ℂ) • (Pi.single i (1 : ℂ) ⊗ₜ[ℂ] u) +
      ((bilinear D a (unitCharge D i) : ℂ) / 16) • (chargeCoordinates D a ⊗ₜ[ℂ] u) +
      (s / 32) • (Pi.single i (1 : ℂ) ⊗ₜ[ℂ] groundAction D hu a u) -
      (s * (bilinear D a (unitCharge D i) : ℂ) / 16) •
        (chargeCoordinates D a ⊗ₜ[ℂ] groundAction D hu a u) := by
  simp only [nativeL, nativeSixteen, nativeHalf, groundMinus_formula, groundPlus,
    chargeProjector, chargeRankOne, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, Module.End.one_apply,
    TensorProduct.map_tmul, chargeFunctional_single, TensorProduct.tmul_add,
    TensorProduct.tmul_sub, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
    smul_add, smul_sub, smul_smul]
  module

/- Transport is constructed from the proven complete-grade equivalence. -/
def actualTransport (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (FirstTensor D hu) ≃ₐ[ℂ] Module.End ℂ (actualGrade D hu 1) :=
  (nativeGradeEquiv D hu).conjAlgEquiv ℂ

/-- This binds the tensor formula to the actual corrected field,
    not merely to an abstract endomorphism satisfying the same cubic. -/
theorem actualZeroMode_transport (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) :
    actualGradeOneZeroMode D hu a ha s = actualTransport D hu (nativeL D hu a s) := by
  let e := nativeGradeEquiv D hu
  have intertwine : (actualGradeOneZeroMode D hu a ha s).comp e.toLinearMap =
      e.toLinearMap.comp (nativeL D hu a s) := by
    apply (nativeBasis D hu).ext
    rintro ⟨i, b⟩
    apply Subtype.ext
    change zeroMode D hu a s (e (nativeBasis D hu (i, b)) : ActualTensor D hu) =
      (e (nativeL D hu a s (nativeBasis D hu (i, b))) : ActualTensor D hu)
    rw [nativeBasis_apply, nativeGradeEquiv_single_coe, nativeL_single,
      zeroMode_X D hu a ha s]
    simp only [e, map_add, map_sub, map_smul, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_smul, nativeGradeEquiv_single_coe, nativeGradeEquiv_charge_coe,
      TensorProduct.add_tmul, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul',
      smul_add, smul_sub, smul_smul]
    module
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := e.surjective v
  change actualGradeOneZeroMode D hu a ha s (e w) =
    e (nativeL D hu a s (e.symm (e w)))
  rw [e.symm_apply_apply]
  exact LinearMap.congr_fun intertwine w

def actualProjectorZero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) : Module.End ℂ (actualGrade D hu 1) :=
  actualTransport D hu (nativeZero D hu a s)

def actualProjectorSixteen (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) : Module.End ℂ (actualGrade D hu 1) :=
  actualTransport D hu (nativeSixteen D hu a s)

def actualProjectorHalf (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) : Module.End ℂ (actualGrade D hu 1) :=
  actualTransport D hu (nativeHalf D hu a s)

private theorem actual_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) :
    actualProjectorZero D hu a s + actualProjectorSixteen D hu a s +
      actualProjectorHalf D hu a s = 1 := by
  simpa only [map_add, map_one, actualProjectorZero, actualProjectorSixteen,
    actualProjectorHalf] using congrArg (actualTransport D hu) (native_sum D hu a s)

private theorem actual_eigenrelations (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    actualGradeOneZeroMode D hu a ha s * actualProjectorZero D hu a s = 0 ∧
    actualProjectorZero D hu a s * actualGradeOneZeroMode D hu a ha s = 0 ∧
    actualGradeOneZeroMode D hu a ha s * actualProjectorSixteen D hu a s =
      (1 / 16 : ℂ) • actualProjectorSixteen D hu a s ∧
    actualProjectorSixteen D hu a s * actualGradeOneZeroMode D hu a ha s =
      (1 / 16 : ℂ) • actualProjectorSixteen D hu a s ∧
    actualGradeOneZeroMode D hu a ha s * actualProjectorHalf D hu a s =
      (1 / 2 : ℂ) • actualProjectorHalf D hu a s ∧
    actualProjectorHalf D hu a s * actualGradeOneZeroMode D hu a ha s =
      (1 / 2 : ℂ) • actualProjectorHalf D hu a s := by
  obtain ⟨h0l, h0r, h16l, h16r, hhl, hhr⟩ := native_eigenrelations D hu a ha s hs
  rw [actualZeroMode_transport D hu a ha s]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [actualProjectorZero] using congrArg (actualTransport D hu) h0l
  · simpa [actualProjectorZero] using congrArg (actualTransport D hu) h0r
  · simpa [actualProjectorSixteen] using congrArg (actualTransport D hu) h16l
  · simpa [actualProjectorSixteen] using congrArg (actualTransport D hu) h16r
  · simpa [actualProjectorHalf] using congrArg (actualTransport D hu) hhl
  · simpa [actualProjectorHalf] using congrArg (actualTransport D hu) hhr

/- A single scalar cancellation helper, used for all six off-eigenvalue
   vanishings in the following actual IsProj proof. -/
private theorem actual_projector_vanishes (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ)
    (p : Module.End ℂ (actualGrade D hu 1)) (μ lam : ℂ)
    (hp : p * actualGradeOneZeroMode D hu a ha s = μ • p)
    (hμlam : μ ≠ lam) (v : actualGrade D hu 1)
    (hv : actualGradeOneZeroMode D hu a ha s v = lam • v) : p v = 0 := by
  have h : μ • p v = lam • p v := by
    calc
      _ = p (actualGradeOneZeroMode D hu a ha s v) :=
        (LinearMap.congr_fun hp v).symm
      _ = _ := by rw [hv, map_smul]
  have hz : (μ - lam) • p v = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hμlam)

/-- All three projectors project onto the full actual eigenspaces.
    IsProj supplies idempotence, range equality and trace=dimension. -/
private theorem actual_projectors_isProj (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    LinearMap.IsProj (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) 0)
      (actualProjectorZero D hu a s) ∧
    LinearMap.IsProj (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 16))
      (actualProjectorSixteen D hu a s) ∧
    LinearMap.IsProj (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 2))
      (actualProjectorHalf D hu a s) := by
  obtain ⟨h0l, h0r, h16l, h16r, hhl, hhr⟩ := actual_eigenrelations D hu a ha s hs
  have total (v : actualGrade D hu 1) :
      actualProjectorZero D hu a s v + actualProjectorSixteen D hu a s v +
        actualProjectorHalf D hu a s v = v :=
    LinearMap.congr_fun (actual_sum D hu a s) v
  have off := actual_projector_vanishes D hu a ha s
  have h0r' : actualProjectorZero D hu a s * actualGradeOneZeroMode D hu a ha s =
      (0 : ℂ) • actualProjectorZero D hu a s := by simpa using h0r
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro v
    rw [Module.End.mem_eigenspace_iff]
    simpa using LinearMap.congr_fun h0l v
  · intro v hv
    have he := Module.End.mem_eigenspace_iff.mp hv
    have h16 := off _ (1 / 16) 0 h16r (by norm_num) v he
    have hh := off _ (1 / 2) 0 hhr (by norm_num) v he
    simpa [h16, hh] using total v
  · intro v
    rw [Module.End.mem_eigenspace_iff]
    exact LinearMap.congr_fun h16l v
  · intro v hv
    have he := Module.End.mem_eigenspace_iff.mp hv
    have h0 := off _ 0 (1 / 16) h0r' (by norm_num) v he
    have hh := off _ (1 / 2) (1 / 16) hhr (by norm_num) v he
    simpa [h0, hh] using total v
  · intro v
    rw [Module.End.mem_eigenspace_iff]
    exact LinearMap.congr_fun hhl v
  · intro v hv
    have he := Module.End.mem_eigenspace_iff.mp hv
    have h0 := off _ 0 (1 / 2) h0r' (by norm_num) v he
    have h16 := off _ (1 / 16) (1 / 2) h16r (by norm_num) v he
    simpa [h0, h16] using total v

theorem actual_projectors_complete (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (actualProjectorZero D hu a s + actualProjectorSixteen D hu a s +
      actualProjectorHalf D hu a s = 1) ∧
    (LinearMap.IsProj (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) 0)
      (actualProjectorZero D hu a s) ∧
    LinearMap.IsProj (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 16))
      (actualProjectorSixteen D hu a s) ∧
    LinearMap.IsProj (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 2))
      (actualProjectorHalf D hu a s)) ∧
    (LinearMap.range (actualProjectorZero D hu a s) =
      Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) 0 ∧
    LinearMap.range (actualProjectorSixteen D hu a s) =
      Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 16) ∧
    LinearMap.range (actualProjectorHalf D hu a s) =
      Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 2)) := by
  obtain ⟨h0, h16, hh⟩ := actual_projectors_isProj D hu a ha s hs
  exact ⟨actual_sum D hu a s, ⟨h0, h16, hh⟩, h0.range, h16.range, hh.range⟩

private theorem actualTransport_trace (D : LatticeData) (hu : IsUnit D.G.det)
    (f : Module.End ℂ (FirstTensor D hu)) :
    LinearMap.trace ℂ (actualGrade D hu 1) (actualTransport D hu f) =
      LinearMap.trace ℂ (FirstTensor D hu) f := by
  change LinearMap.trace ℂ (actualGrade D hu 1) ((nativeGradeEquiv D hu).conj f) = _
  exact LinearMap.trace_conj' f (nativeGradeEquiv D hu)

/-- These are traces on the complete native grade. -/
theorem actual_projectors_traces (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) :
    LinearMap.trace ℂ (actualGrade D hu 1) (actualProjectorZero D hu a s) =
      ((D.rank : ℂ) - 1) * ((2 ^ (D.rank / 2) : ℕ) : ℂ) / 2 ∧
    LinearMap.trace ℂ (actualGrade D hu 1) (actualProjectorSixteen D hu a s) =
      (D.rank : ℂ) * ((2 ^ (D.rank / 2) : ℕ) : ℂ) / 2 ∧
    LinearMap.trace ℂ (actualGrade D hu 1) (actualProjectorHalf D hu a s) =
      ((2 ^ (D.rank / 2) : ℕ) : ℂ) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [actualProjectorZero, actualTransport_trace, nativeZero,
      LinearMap.trace_tensorProduct', map_sub, LinearMap.trace_one,
      chargeProjector_trace D a ha, groundMinus_trace D hu a ha s]
    simp only [FirstOscillator, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    ring
  · rw [actualProjectorSixteen, actualTransport_trace, nativeSixteen,
      LinearMap.trace_tensorProduct', LinearMap.trace_one, groundPlus_trace D hu a ha s]
    simp only [FirstOscillator, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    ring
  · rw [actualProjectorHalf, actualTransport_trace, nativeHalf,
      LinearMap.trace_tensorProduct', chargeProjector_trace D a ha,
      groundMinus_trace D hu a ha s, one_mul]

/-- Integral multiplicities, without a division convention,
    for either sign s with s^2=1, on the COMPLETE actual first grade. -/
theorem actual_first_grade_eigenspace_multiplicities
    (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    2 * Module.finrank ℂ
        (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) 0) =
      (D.rank - 1) * 2 ^ (D.rank / 2) ∧
    2 * Module.finrank ℂ
        (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 16)) =
      D.rank * 2 ^ (D.rank / 2) ∧
    2 * Module.finrank ℂ
        (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 2)) =
      2 ^ (D.rank / 2) := by
  obtain ⟨p0, p16, ph⟩ := (actual_projectors_complete D hu a ha s hs).2.1
  obtain ⟨t0, t16, th⟩ := actual_projectors_traces D hu a ha s
  rw [p0.trace] at t0
  rw [p16.trace] at t16
  rw [ph.trace] at th
  have hr : 1 ≤ D.rank := rank_pos D a ha
  have cast_sub : ((D.rank - 1 : ℕ) : ℂ) = (D.rank : ℂ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℂ) hr)
  refine ⟨?_, ?_, ?_⟩
  · have h : (2 : ℂ) * (Module.finrank ℂ
        (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) 0) : ℂ) =
        ((D.rank - 1 : ℕ) : ℂ) * ((2 ^ (D.rank / 2) : ℕ) : ℂ) := by
      rw [t0, cast_sub]
      ring
    exact_mod_cast h
  · have h : (2 : ℂ) * (Module.finrank ℂ
        (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 16)) : ℂ) =
        (D.rank : ℂ) * ((2 ^ (D.rank / 2) : ℕ) : ℂ) := by
      rw [t16]
      ring
    exact_mod_cast h
  · have h : (2 : ℂ) * (Module.finrank ℂ
        (Module.End.eigenspace (actualGradeOneZeroMode D hu a ha s) (1 / 2)) : ℂ) =
        ((2 ^ (D.rank / 2) : ℕ) : ℂ) := by
      rw [th]
      ring
    exact_mod_cast h

/- The target parity is independent of the scalar sign in the source state. -/
private theorem normFourSource_fixed (D : LatticeData) (a : Charge D) (s : ℂ) :
    vector D a s ∈ fixedSpace D := by
  have hp : sigma D (chargePolynomial D a) = -chargePolynomial D a := by
    simp [chargePolynomial, map_sum, Finset.sum_neg_distrib]
  apply (mem_fixedSpace D _).mpr
  change thetaLinear D (vector D a s) = vector D a s
  simp [vector, quadraticState, chargedState, theta_single, hp, map_pow, add_comm]

/-- The actual theta-fixed source, with arbitrary scalar sign. -/
def normFourFixedSource (D : LatticeData) (a : Charge D) (s : ℂ) : FixedCarrier D :=
  ⟨vector D a s, normFourSource_fixed D a s⟩

/-- The full ambient intersection, without a chosen basis or dimension premise. -/
def parityMinusEnergyTwo (D : LatticeData) (hu : IsUnit D.G.det) :
    Submodule ℂ (ActualTensor D hu) :=
  paritySpace D hu (-1) ⊓ (actualTensorL0 D hu).eigenspace (2 : ℂ)

theorem actual_grade_one_eq_parity_minus_energy_two
    (D : LatticeData) (hu : IsUnit D.G.det) (h24 : D.rank = 24) :
    actualGrade D hu 1 = parityMinusEnergyTwo D hu := by
  have henergy := (actual_rank24_grade_one_finrank_98304 D hu h24).1
  apply le_antisymm
  · intro v hv
    refine ⟨?_, ?_⟩
    · have hp := actualParity_on_actualGrade D hu 1 ⟨v, hv⟩
      change actualParity D hu v - (-1 : ℂ) • v = 0
      rw [hp]
      simp
    · change v ∈ (actualTensorL0 D hu).eigenspace (2 : ℂ)
      rw [Module.End.eigenspace_def]
      exact henergy ▸ hv
  · intro v hv
    rw [henergy]
    have he := hv.2
    rw [Module.End.eigenspace_def] at he
    exact he

/-- Coefficient -4 is exactly physical mode 1 on the target parity minus space. -/
private theorem fixedParitySlice_zeroMode_coe (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (s : ℂ) (v : paritySpace D hu (-1)) :
    (((fixedParitySlice D hu (-1) (normFourFixedSource D a s))[[1]]) v :
      ActualTensor D hu) = zeroMode D hu a s (v : ActualTensor D hu) := by
  simp only [fixedParitySlice, VertexOperator.ncoeff_of_coeff]
  rfl

/-- Literal physical mode restricted to the whole parity-minus energy-two space. -/
def parityMinusEnergyTwoZeroMode (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) :
    Module.End ℂ (parityMinusEnergyTwo D hu) where
  toFun v := ⟨zeroMode D hu a s v, by
    have hgrade := (actual_grade_one_eq_parity_minus_energy_two D hu h24).ge v.property
    exact (actual_grade_one_eq_parity_minus_energy_two D hu h24).le
      (actualGradeOneZeroMode D hu a ha s ⟨v, hgrade⟩).property⟩
  map_add' v w := Subtype.ext (map_add (zeroMode D hu a s) v.val w.val)
  map_smul' c v := Subtype.ext (map_smul (zeroMode D hu a s) c v.val)

private theorem parity_minus_energy_two_physical_mode
    (D : LatticeData) (hu : IsUnit D.G.det) (h24 : D.rank = 24)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ)
    (v : parityMinusEnergyTwo D hu) :
    (parityMinusEnergyTwoZeroMode D hu h24 a ha s v : ActualTensor D hu) =
      (((fixedParitySlice D hu (-1) (normFourFixedSource D a s))[[1]])
        ⟨v, v.property.1⟩ : ActualTensor D hu) := by
  change zeroMode D hu a s (v : ActualTensor D hu) = _
  exact (fixedParitySlice_zeroMode_coe D hu a s ⟨v.val, v.property.1⟩).symm

private def energyTwoEigenspaceEquiv
    (D : LatticeData) (hu : IsUnit D.G.det) (h24 : D.rank = 24)
    (a : Charge D) (ha : bilinear D a a = 4) (s lam : ℂ) :
    (actualGradeOneZeroMode D hu a ha s).eigenspace lam ≃ₗ[ℂ]
      (parityMinusEnergyTwoZeroMode D hu h24 a ha s).eigenspace lam where
  toFun v := ⟨⟨v.val.val,
    actual_grade_one_eq_parity_minus_energy_two D hu h24 ▸ v.val.property⟩, by
    have he := Module.End.mem_eigenspace_iff.mp v.property
    have he' := congrArg (fun x : actualGrade D hu 1 => (x : ActualTensor D hu)) he
    rw [Module.End.mem_eigenspace_iff]
    apply Subtype.ext
    exact he'⟩
  invFun v := ⟨⟨v.val.val,
    (actual_grade_one_eq_parity_minus_energy_two D hu h24).symm ▸ v.val.property⟩, by
    have he := Module.End.mem_eigenspace_iff.mp v.property
    have he' := congrArg (fun x : parityMinusEnergyTwo D hu => (x : ActualTensor D hu)) he
    rw [Module.End.mem_eigenspace_iff]
    apply Subtype.ext
    exact he'⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' c v := rfl

/-- The three multiplicities of the literal fixed-source physical mode on the
entire actual parity-minus ambient energy-two space at rank twenty-four. -/
theorem actual_parity_minus_energy_two_multiplicities
    (D : LatticeData) (hu : IsUnit D.G.det) (h24 : D.rank = 24)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (∀ v : parityMinusEnergyTwo D hu,
      (parityMinusEnergyTwoZeroMode D hu h24 a ha s v : ActualTensor D hu) =
        (((fixedParitySlice D hu (-1) (normFourFixedSource D a s))[[1]])
          ⟨v, v.property.1⟩ : ActualTensor D hu)) ∧
    Module.finrank ℂ (parityMinusEnergyTwo D hu) = 98304 ∧
    Module.finrank ℂ
      ((parityMinusEnergyTwoZeroMode D hu h24 a ha s).eigenspace 0) = 47104 ∧
    Module.finrank ℂ
      ((parityMinusEnergyTwoZeroMode D hu h24 a ha s).eigenspace (1 / 16)) = 49152 ∧
    Module.finrank ℂ
      ((parityMinusEnergyTwoZeroMode D hu h24 a ha s).eigenspace (1 / 2)) = 2048 := by
  refine ⟨parity_minus_energy_two_physical_mode D hu h24 a ha s, ?_, ?_⟩
  · rw [← actual_grade_one_eq_parity_minus_energy_two D hu h24]
    exact (actual_rank24_grade_one_finrank_98304 D hu h24).2.1
  · have dims := actual_first_grade_eigenspace_multiplicities D hu a ha s hs
    have transfer (lam : ℂ) :=
      (energyTwoEigenspaceEquiv D hu h24 a ha s lam).finrank_eq
    rw [transfer 0, transfer (1 / 16), transfer (1 / 2), h24] at dims
    norm_num at dims
    omega

end
end D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum
