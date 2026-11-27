/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldNativeBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldNativeBPZ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Leech and hyperbolic BPZ coefficients with the relative ghost insertion. -/

import D5.S3.Quantum.Fermionic.BcGhostBilinear
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealRootBracket
import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
import D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! The complex-bilinear BPZ pairing on the original relative BRST carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (Orbifold leechUnit)
open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane)
open LatticeGeneratingFieldLocality (Carrier Charge Oscillator)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeQuartetContraction (chargeMatter chargeProject)
open SourceBPZ.OriginalSourcePairing
open TwistedGround TwistedGround.Orbifold
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket phase)
open BcGhostFock (b c ghost_mixed_car)
open BcGhostCharge (charge ghostNumber)
open BcGhostHermitian (relativeEps relativePartner charge_relativePartner
  annihilate_coefficient ghostNumber_coefficient b_zero)
open BcGhostBilinear

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

private def fixedProjection : Orbifold →ₗ[ℂ] Carrier leechData :=
  (LatticeInvolution.fixedSpace leechData).subtype.comp (LinearMap.fst ℂ _ _)

private def twistedProjection : Orbifold →ₗ[ℂ] ActualTensor leechData leechUnit :=
  (paritySpace leechData leechUnit (-1)).subtype.comp (LinearMap.snd ℂ _ _)

/-- The sum of the original fixed and negative twisted BPZ restrictions. -/
def orbifoldPairing : LinearMap.BilinForm ℂ Orbifold :=
  (sourcePairing leechData).compl₁₂ fixedProjection fixedProjection +
    (ActualChargedAdjoint.actualForm leechData leechUnit).compl₁₂
      twistedProjection twistedProjection

theorem orbifoldPairing_apply (x y : Orbifold) :
    orbifoldPairing x y = sourcePairing leechData x.1.val y.1.val +
      ActualChargedAdjoint.actualForm leechData leechUnit x.2.val y.2.val := rfl

theorem orbifoldPairing_symmetric (x y : Orbifold) :
    orbifoldPairing x y = orbifoldPairing y x := by
  rw [orbifoldPairing_apply, orbifoldPairing_apply,
    sourcePairing_symmetric leechData x.1.val y.1.val,
    (ActualPairingSymmetry.actualForm_symmetric leechData leechUnit).eq x.2.val y.2.val]

/-- The hyperbolic factor uses the lattice BPZ form with opposite charges. -/
def matterPairing : LinearMap.BilinForm ℂ Matter :=
  orbifoldPairing.tmul (sourcePairing hyperbolicPlane)

/-- Absolute BPZ pairing on the actual three-factor BRST carrier. -/
def absolutePairing : LinearMap.BilinForm ℂ ComplexState := matterPairing.tmul Bg

private abbrev c0 : Module.End ℂ ComplexState := VirasoroBRST.ghostC matter 0

/-- The native relative formula evaluated in the original state space. -/
def relativePairing : LinearMap.BilinForm ℂ ComplexState := absolutePairing.compl₂ c0

private theorem tensor_pairing_tmul {U V : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (A : LinearMap.BilinForm ℂ U) (B : LinearMap.BilinForm ℂ V)
    (u u' : U) (v v' : V) :
    A.tmul B (u ⊗ₜ[ℂ] v) (u' ⊗ₜ[ℂ] v') = B v v' * A u u' := rfl

theorem relativePairing_tmul (a d : Matter) (x y : Fock) :
    relativePairing (a ⊗ₜ[ℂ] x) (d ⊗ₜ[ℂ] y) =
      Bg x (c 0 y) * matterPairing a d := rfl

private theorem tensor_transpose {U V : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (A : LinearMap.BilinForm ℂ U) (B : LinearMap.BilinForm ℂ V)
    (S S' : Module.End ℂ U) (T T' : Module.End ℂ V)
    (hS : ∀ u u', A (S u) u' = A u (S' u'))
    (hT : ∀ v v', B (T v) v' = B v (T' v'))
    (x y : U ⊗[ℂ] V) :
    A.tmul B (TensorProduct.map S T x) y = A.tmul B x (TensorProduct.map S' T' y) := by
  have h : (A.tmul B).comp (TensorProduct.map S T) =
      (A.tmul B).compl₂ (TensorProduct.map S' T') := by
    apply TensorProduct.ext'
    intro u v
    apply TensorProduct.ext'
    intro u' v'
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, TensorProduct.map_tmul,
      tensor_pairing_tmul, hS, hT]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

theorem absolutePairing_ghostB (n : ℤ) (x y : ComplexState) :
    absolutePairing (VirasoroBRST.ghostB matter n x) y =
      absolutePairing x (VirasoroBRST.ghostB matter (-n) y) :=
  tensor_transpose matterPairing Bg LinearMap.id LinearMap.id (b n) (b (-n))
    (fun _ _ => rfl) (Bg_b n) x y

theorem absolutePairing_ghostC (n : ℤ) (x y : ComplexState) :
    absolutePairing (VirasoroBRST.ghostC matter n x) y =
      absolutePairing x (VirasoroBRST.ghostC matter (-n) y) :=
  tensor_transpose matterPairing Bg LinearMap.id LinearMap.id (c n) (c (-n))
    (fun _ _ => rfl) (Bg_c n) x y

/-- The absolute form vanishes between two inputs in the original b₀ kernel. -/
theorem absolutePairing_b0_kernel {x y : ComplexState} (hx : b0 x = 0)
    (hy : b0 y = 0) : absolutePairing x y = 0 := by
  let lift := Module.End.lTensorAlgHom ℂ Fock Matter
  have hGhost : b 0 * c 0 + c 0 * b 0 = (1 : Module.End ℂ Fock) := by
    simpa using ghost_mixed_car 0 0
  have hCAR : b0 * c0 + c0 * b0 = 1 := by
    change lift (b 0) * lift (c 0) + lift (c 0) * lift (b 0) = 1
    simpa only [map_add, map_mul, map_one] using congrArg lift hGhost
  have hIns : b0 (c0 y) = y := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
      hy, map_zero, add_zero] using LinearMap.congr_fun hCAR y
  calc
    absolutePairing x y = absolutePairing x (b0 (c0 y)) := by rw [hIns]
    _ = absolutePairing (b0 x) (c0 y) := by
      simpa only [neg_zero] using (absolutePairing_ghostB 0 x (c0 y)).symm
    _ = 0 := by rw [hx, map_zero, LinearMap.zero_apply]

private theorem absolutePairing_symmetric (x y : ComplexState) :
    absolutePairing x y = absolutePairing y x := by
  have hOrb : LinearMap.IsSymm orbifoldPairing := ⟨orbifoldPairing_symmetric⟩
  have hPlane : LinearMap.IsSymm (sourcePairing hyperbolicPlane) :=
    ⟨sourcePairing_symmetric hyperbolicPlane⟩
  have hGhost : LinearMap.IsSymm Bg := ⟨Bg_symmetric⟩
  exact ((hOrb.tmul hPlane).tmul hGhost).eq x y

theorem relativePairing_symmetric (x y : ComplexState) :
    relativePairing x y = relativePairing y x := by
  change absolutePairing x (c0 y) = absolutePairing y (c0 x)
  rw [absolutePairing_symmetric x (c0 y)]
  simpa only [neg_zero] using absolutePairing_ghostC 0 y x

/-- The actual finite matter coefficients indexed by ghost occupations. -/
def ghostSlices : ComplexState ≃ₗ[ℂ] ((Finset ℕ) →₀ Matter) :=
  TensorProduct.finsuppScalarRight ℂ ℂ Matter (Finset ℕ)

private theorem ghostSlices_tmul (a : Matter) (x : Fock) (S : Finset ℕ) :
    ghostSlices (a ⊗ₜ[ℂ] x) S = x S • a :=
  TensorProduct.finsuppScalarRight_apply_tmul_apply a x S

private theorem ghostSlices_expand (x : ComplexState) :
    x = ∑ S ∈ (ghostSlices x).support, ghostSlices x S ⊗ₜ[ℂ] ket S := by
  classical
  calc
    x = ghostSlices.symm (ghostSlices x) := (ghostSlices.symm_apply_apply x).symm
    _ = ghostSlices.symm (∑ S ∈ (ghostSlices x).support,
        Finsupp.single S (ghostSlices x S)) :=
      congrArg ghostSlices.symm (Finsupp.sum_single (ghostSlices x)).symm
    _ = _ := by
      rw [← LinearEquiv.coe_coe, map_sum]
      apply Finset.sum_congr rfl
      intro S _
      exact TensorProduct.finsuppScalarRight_symm_apply_single S (ghostSlices x S)

private theorem ghostSlices_b0 (x : ComplexState) (S : Finset ℕ) :
    ghostSlices (b0 x) S =
      if 3 ∈ S then 0 else phase 3 S • ghostSlices x (insert 3 S) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change ghostSlices (a ⊗ₜ[ℂ] b 0 x) S = _
    rw [ghostSlices_tmul, b_zero, annihilate_coefficient, ghostSlices_tmul]
    split_ifs <;> simp [mul_smul]
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]
    split_ifs <;> simp [smul_add]

private theorem three_notMem_of_ghostSlice {x : ComplexState} {S : Finset ℕ}
    (hx : b0 x = 0) (hS : ghostSlices x S ≠ 0) : 3 ∉ S := by
  intro hthree
  have hzero : ghostSlices (b0 x) (S.erase 3) = 0 := by
    rw [hx, ghostSlices.map_zero, Finsupp.zero_apply]
  have h : phase 3 (S.erase 3) • ghostSlices x S = 0 := by
    simpa only [ghostSlices_b0, ite_eq_right (Finset.notMem_erase _ _),
      Finset.insert_erase hthree] using hzero
  exact hS ((smul_eq_zero_iff_right (M := Matter)
    (BcGhostHermitian.phase_ne_zero _ _)).mp h)

private theorem relativePairing_ket (a : Matter) (S : Finset ℕ) (hS : 3 ∉ S)
    (y : ComplexState) :
    relativePairing (a ⊗ₜ[ℂ] ket S) y =
      relativeEps S * matterPairing a (ghostSlices y (relativePartner S)) := by
  induction y using TensorProduct.inductionOn with
  | tmul d y =>
    rw [relativePairing_tmul, Bg_c0_ket_coefficient S hS, ghostSlices_tmul, map_smul]
    simp only [smul_eq_mul, mul_assoc]
  | add y z hy hz =>
    simp only [map_add, Finsupp.add_apply, hy, hz, mul_add]

/-- Relative BPZ is a finite sum over the actual matter-valued ghost slices. -/
theorem relativePairing_signed_coefficient (x y : ComplexState) (hx : b0 x = 0) :
    relativePairing x y = ∑ S ∈ (ghostSlices x).support,
      relativeEps S * matterPairing (ghostSlices x S) (ghostSlices y (relativePartner S)) := by
  classical
  conv_lhs => rw [ghostSlices_expand x]
  rw [map_sum]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro S hS
  exact relativePairing_ket _ S
    (three_notMem_of_ghostSlice hx (Finsupp.mem_support_iff.mp hS)) y

private theorem ghostSlices_number (x : ComplexState) (S : Finset ℕ) :
    ghostSlices (VirasoroBRST.N matter x) S = (charge S : ℂ) • ghostSlices x S := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    change ghostSlices (a ⊗ₜ[ℂ] ghostNumber x) S = _
    rw [ghostSlices_tmul, ghostNumber_coefficient, ghostSlices_tmul, mul_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, smul_add]

private theorem charge_of_ghostSlice {g : ℤ} {x : ComplexState} {S : Finset ℕ}
    (hx : RelativeBracket.Degree g x) (hS : ghostSlices x S ≠ 0) : charge S = g := by
  have h := congrArg (fun z : ComplexState => ghostSlices z S) hx
  simp only [ghostSlices_number, map_smul, Finsupp.smul_apply] at h
  have hc : (charge S : ℂ) = (g : ℂ) :=
    smul_left_injective ℂ hS h
  exact_mod_cast hc

theorem relativePairing_degree_selection {g h : ℤ} {x y : ComplexState}
    (hb : b0 x = 0) (hx : RelativeBracket.Degree g x) (hy : RelativeBracket.Degree h y)
    (hgh : g + h ≠ 2) : relativePairing x y = 0 := by
  classical
  rw [relativePairing_signed_coefficient x y hb]
  apply Finset.sum_eq_zero
  intro S hS
  have hxS : ghostSlices x S ≠ 0 := Finsupp.mem_support_iff.mp hS
  have hthree := three_notMem_of_ghostSlice hb hxS
  have hz : ghostSlices y (relativePartner S) = 0 := by
    by_contra hyS
    have hp := charge_relativePartner S hthree
    rw [charge_of_ghostSlice hx hxS, charge_of_ghostSlice hy hyS] at hp
    exact hgh hp
  simp [hz]

private theorem planePairing_project (p : Charge hyperbolicPlane)
    (u v : Carrier hyperbolicPlane) :
    sourcePairing hyperbolicPlane (chargeMatter p u) v =
      sourcePairing hyperbolicPlane u (chargeMatter (-p) v) := by
  classical
  let A := sourcePairing hyperbolicPlane
  have h : LinearMap.comp A (chargeMatter p) = A.compl₂ (chargeMatter (-p)) := by
    apply Finsupp.lhom_ext
    intro q a
    apply LinearMap.ext
    intro w
    change sourcePairing hyperbolicPlane
        (Finsupp.single p (Finsupp.single q a p)) w =
      sourcePairing hyperbolicPlane (Finsupp.single q a) (Finsupp.single (-p) (w (-p)))
    rw [sourcePairing_single, sourcePairing_single]
    by_cases hqp : q = p
    · subst q
      simp
    · have hn : -p ≠ -q := fun he => hqp (neg_injective he.symm)
      simp [Ne.symm hqp, Ne.symm hn]
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) v

private abbrev planeProject (p : Charge hyperbolicPlane) : Module.End ℂ ComplexState :=
  TensorProduct.map (TensorProduct.map LinearMap.id (chargeMatter p)) LinearMap.id

private theorem reassoc_planeProject (p : Charge hyperbolicPlane) (x : ComplexState) :
    reassoc (planeProject p x) = rightLift (chargeProject p) (reassoc x) := by
  have h : reassoc.toLinearMap.comp (planeProject p) =
      (rightLift (chargeProject p)).comp reassoc.toLinearMap := by
    apply TensorProduct.ext'
    intro a s
    induction a using TensorProduct.inductionOn with
    | tmul v u => rfl
    | add a d ha hd =>
      simp only [TensorProduct.add_tmul, map_add] at ha hd ⊢
      rw [ha, hd]
  exact LinearMap.congr_fun h x

private theorem planeProject_mul_eq_zero (p q : Charge hyperbolicPlane) (h : p ≠ q) :
    planeProject p * planeProject q = 0 := by
  have hplane : chargeMatter p * chargeMatter q = 0 := by
    apply LinearMap.ext
    intro u
    change Finsupp.single p (Finsupp.single q (u q) p) = 0
    simp [h]
  change TensorProduct.map (TensorProduct.map (1 : Module.End ℂ Orbifold) (chargeMatter p))
      (1 : Module.End ℂ Fock) *
    TensorProduct.map (TensorProduct.map (1 : Module.End ℂ Orbifold) (chargeMatter q))
      (1 : Module.End ℂ Fock) = 0
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, hplane,
    TensorProduct.map_zero_right, TensorProduct.map_zero_left]

private theorem absolutePairing_planeProject (p : Charge hyperbolicPlane) (x y : ComplexState) :
    absolutePairing (planeProject p x) y = absolutePairing x (planeProject (-p) y) :=
  tensor_transpose matterPairing Bg
    (TensorProduct.map LinearMap.id (chargeMatter p))
    (TensorProduct.map LinearMap.id (chargeMatter (-p))) LinearMap.id LinearMap.id
    (tensor_transpose orbifoldPairing (sourcePairing hyperbolicPlane)
      LinearMap.id LinearMap.id (chargeMatter p) (chargeMatter (-p))
      (fun _ _ => rfl) (planePairing_project p))
    (fun _ _ => rfl) x y

private theorem planeProject_c0 (p : Charge hyperbolicPlane) (y : ComplexState) :
    planeProject p (c0 y) = c0 (planeProject p y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a s => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The fixed-point condition is that of the original plane momentum projector. -/
theorem relativePairing_momentum_selection {p q : Charge hyperbolicPlane} {x y : ComplexState}
    (hx : RelativeBracket.Momentum p x) (hy : RelativeBracket.Momentum q y)
    (hpq : q ≠ -p) : relativePairing x y = 0 := by
  have hx' : planeProject p x = x := reassoc.injective ((reassoc_planeProject p x).trans hx)
  have hy' : planeProject q y = y := reassoc.injective ((reassoc_planeProject q y).trans hy)
  have hz : planeProject (-p) y = 0 := by
    calc
      planeProject (-p) y = (planeProject (-p) * planeProject q) y :=
        congrArg (planeProject (-p)) hy'.symm
      _ = 0 := by rw [planeProject_mul_eq_zero _ _ (Ne.symm hpq), LinearMap.zero_apply]
  change absolutePairing x (c0 y) = 0
  rw [← hx', absolutePairing_planeProject, planeProject_c0, hz, map_zero, map_zero]

private abbrev orbVac := OriginalOrbifoldField.vacuumState leechData leechUnit

private theorem orbifoldPairing_vacuum : orbifoldPairing orbVac orbVac = 1 := by
  rw [orbifoldPairing_apply]
  change sourcePairing leechData (LatticeAllStateField.vacuum leechData)
    (LatticeAllStateField.vacuum leechData) +
      ActualChargedAdjoint.actualForm leechData leechUnit 0 0 = 1
  simp [sourcePairing_vacuum]

private theorem planeWick_one : integerWick hyperbolicPlane 1 1 = 1 := by
  simpa only [LatticeAllStateField.vacuum, sourcePairing_single_single, neg_zero, ite_eq_left]
    using sourcePairing_vacuum hyperbolicPlane

/-- The unshifted c₀ form is +1 on opposite literal plane grounds and zero otherwise. -/
theorem relativePairing_psi (p q : Charge hyperbolicPlane) :
    relativePairing (RealRootBracket.psi p) (RealRootBracket.psi q) =
      if q = -p then 1 else 0 := by
  classical
  simp only [RealRootBracket.psi, relativePairing_tmul, Bg_c0_ket_one, one_mul]
  change sourcePairing hyperbolicPlane (Finsupp.single p (1 : Oscillator hyperbolicPlane))
      (Finsupp.single q 1) * orbifoldPairing orbVac orbVac = _
  rw [orbifoldPairing_vacuum, mul_one, sourcePairing_single_single, planeWick_one]

/-- Evaluation of the normalized sign on the chosen representatives of e and f. -/
theorem normalized_root_representatives_pair :
    -relativePairing (RealRootBracket.psi RealRootBracket.positiveRoot)
      (-RealRootBracket.psi (-RealRootBracket.positiveRoot)) = 1 := by
  rw [map_neg, neg_neg, relativePairing_psi, ite_eq_left rfl]

/-- The original current representatives give the negative hyperbolic Gram matrix. -/
theorem relativePairing_cartan (i j : Fin 2) :
    relativePairing (RelativeZeroMomentum.u i) (RelativeZeroMomentum.u j) =
      -(hyperbolicPlane.G i j : ℂ) := by
  simp only [RelativeZeroMomentum.u, relativePairing_tmul, Bg_c0_ket_one, one_mul]
  change sourcePairing hyperbolicPlane
    (Finsupp.single 0 (MvPolynomial.X (i, 0)))
    (Finsupp.single 0 (MvPolynomial.X (j, 0))) * orbifoldPairing orbVac orbVac = _
  rw [orbifoldPairing_vacuum, mul_one, sourcePairing_single_single]
  simp only [neg_zero, ite_eq_left]
  rw [← mul_one (MvPolynomial.X (i, 0) : Oscillator hyperbolicPlane),
    integerWick_creation, LatticeActualAnnihilation.annihilate_X]
  simp only [ite_true, Nat.cast_zero, zero_add, neg_one_smul, map_neg, map_smul,
    smul_eq_mul, planeWick_one, mul_one]

/-- Evaluation of the normalized sign on the actual Cartan representative of h. -/
theorem normalized_cartan_representative_pair :
    -relativePairing (RelativeZeroMomentum.u 0 + RelativeZeroMomentum.u 1)
      (RelativeZeroMomentum.u 0 + RelativeZeroMomentum.u 1) = 2 := by
  simp only [map_add, LinearMap.add_apply, relativePairing_cartan]
  change -((-((0 : ℤ) : ℂ) + -((1 : ℤ) : ℂ)) +
    (-((1 : ℤ) : ℂ) + -((0 : ℤ) : ℂ))) = 2
  norm_num

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ
