/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative BRST cohomology at the norm-two momentum on the actual Leech orbifold. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
import D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Basic

/-! The two orbifold summands are read in their original ambient bases.
The tensor coefficients use the standalone hyperbolic lattice and the native
finite-occupation ghost representation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativeNormTwo

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane hyperbolicMatter)
open ActualLeechOrbifoldBRST (ComplexState Q E b0)
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open LatticeSugawaraVirasoro LatticeInvolution LatticeHalfFockGradedTrace
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open TwistedGround.Orbifold
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open BcGhostRelativeEnergy (relativeEnergy relativeEnergy_nonneg)

open private plane_inverse tensorMode
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private Q_commutes_energy from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST

/-- The positive norm-two charge in the standalone hyperbolic plane. -/
def momentum : Charge hyperbolicPlane := fun _ => 1

private abbrev Plane := Carrier hyperbolicPlane
private abbrev Fixed := FixedCarrier leechData
private abbrev Twisted := ↥(paritySpace leechData leechUnit (-1))
private abbrev AmbientTwisted := ActualTensor leechData leechUnit

private def chargeProjection : Module.End ℂ Plane :=
  (Finsupp.lsingle momentum).comp (Finsupp.lapply momentum)

private def matterProjection : Module.End ℂ Matter :=
  TensorProduct.map LinearMap.id chargeProjection

/-- The charge projection on the literal three-factor state space. -/
def momentumProjection : Module.End ℂ ComplexState :=
  TensorProduct.map matterProjection LinearMap.id

private def fixedInclusion : Fixed →ₗ[ℂ] Carrier leechData :=
  (fixedSpace leechData).subtype

private def twistedInclusion : Twisted →ₗ[ℂ] AmbientTwisted :=
  (paritySpace leechData leechUnit (-1)).subtype

private def fixedProjection : Orbifold →ₗ[ℂ] Carrier leechData :=
  fixedInclusion.comp (LinearMap.fst ℂ Fixed Twisted)

private def twistedProjection : Orbifold →ₗ[ℂ] AmbientTwisted :=
  twistedInclusion.comp (LinearMap.snd ℂ Fixed Twisted)

private def ambientMap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Orbifold →ₗ[ℂ] V) :
    ComplexState →ₗ[ℂ] ((V ⊗[ℂ] Plane) ⊗[ℂ] Fock) :=
  TensorProduct.map (TensorProduct.map f LinearMap.id) LinearMap.id

private def ghostBasis : Module.Basis (Finset ℕ) ℂ Fock :=
  Finsupp.basisSingleOne

private def coordinates {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (basis : Module.Basis ι ℂ V) (f : Orbifold →ₗ[ℂ] V)
    (i : ι) (l : Label hyperbolicPlane) (S : Finset ℕ) : ComplexState →ₗ[ℂ] ℂ :=
  (((basis.tensorProduct (carrierBasis hyperbolicPlane)).tensorProduct ghostBasis).coord
    ((i, l), S)).comp (ambientMap f)

private abbrev fixedCoord :=
  coordinates (carrierBasis leechData) fixedProjection

private abbrev twistedCoord :=
  coordinates (actualAmbientBasis leechData leechUnit) twistedProjection

private theorem coordinates_tmul {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (basis : Module.Basis ι ℂ V) (f : Orbifold →ₗ[ℂ] V)
    (i : ι) (l : Label hyperbolicPlane) (S : Finset ℕ) (v : Orbifold) (u : Plane) (g : Fock) :
    coordinates basis f i l S ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] g) =
      basis.repr (f v) i * carrierCoeffEquiv hyperbolicPlane u l * g S := by
  simp only [coordinates, ambientMap, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, Module.Basis.coord_apply, Module.Basis.tensorProduct_repr_tmul_apply,
    smul_eq_mul]
  change g S * (carrierCoeffEquiv hyperbolicPlane u l * basis.repr (f v) i) = _
  ring

private def splitState : ComplexState ≃ₗ[ℂ]
    (((Fixed ⊗[ℂ] Plane) ⊗[ℂ] Fock) × ((Twisted ⊗[ℂ] Plane) ⊗[ℂ] Fock)) :=
  TensorProduct.congr (TensorProduct.prodLeft ℂ ℂ Fixed Twisted Plane)
      (LinearEquiv.refl ℂ Fock) ≪≫ₗ
    TensorProduct.prodLeft ℂ ℂ (Fixed ⊗[ℂ] Plane) (Twisted ⊗[ℂ] Plane) Fock

private theorem ambientMap_eq_projection {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Orbifold →ₗ[ℂ] V) (projection :
      (((Fixed ⊗[ℂ] Plane) ⊗[ℂ] Fock) × ((Twisted ⊗[ℂ] Plane) ⊗[ℂ] Fock)) →ₗ[ℂ]
        ((V ⊗[ℂ] Plane) ⊗[ℂ] Fock))
    (h : ∀ (v : Orbifold) (u : Plane) (g : Fock),
      projection (((v.1 ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] g), ((v.2 ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] g)) =
        (f v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] g) :
    ambientMap f = projection.comp splitState.toLinearMap := by
  apply TensorProduct.ext'
  intro y g
  induction y using TensorProduct.inductionOn with
  | tmul v u => exact (h v u g).symm
  | add y z hy hz => simp only [TensorProduct.add_tmul, map_add, hy, hz]

private theorem tensorInclusion_zero {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W) (hf : Function.Injective f)
    (x : (V ⊗[ℂ] Plane) ⊗[ℂ] Fock)
    (hx : TensorProduct.map
      (TensorProduct.map f (LinearMap.id : Plane →ₗ[ℂ] Plane))
      (LinearMap.id : Fock →ₗ[ℂ] Fock) x = 0) : x = 0 := by
  let lift := TensorProduct.map (TensorProduct.map f (LinearMap.id : Plane →ₗ[ℂ] Plane))
    (LinearMap.id : Fock →ₗ[ℂ] Fock)
  have hinj : Function.Injective lift :=
    TensorProduct.map_injective_of_flat_flat _ _
      (TensorProduct.map_injective_of_flat_flat _ _ hf Function.injective_id)
      Function.injective_id
  apply hinj
  rw [map_zero]
  exact hx

private theorem ambientMap_separates {x : ComplexState}
    (hf : ambientMap fixedProjection x = 0) (ht : ambientMap twistedProjection x = 0) :
    x = 0 := by
  rw [ambientMap_eq_projection fixedProjection
    ((TensorProduct.map (TensorProduct.map fixedInclusion LinearMap.id) LinearMap.id).comp
      (LinearMap.fst ℂ _ _)) (fun _ _ _ => rfl)] at hf
  rw [ambientMap_eq_projection twistedProjection
    ((TensorProduct.map (TensorProduct.map twistedInclusion LinearMap.id) LinearMap.id).comp
      (LinearMap.snd ℂ _ _)) (fun _ _ _ => rfl)] at ht
  apply splitState.injective
  rw [splitState.map_zero]
  apply Prod.ext
  · exact tensorInclusion_zero fixedInclusion (fixedSpace leechData).subtype_injective _ hf
  · exact tensorInclusion_zero twistedInclusion
      (paritySpace leechData leechUnit (-1)).subtype_injective _ ht

private theorem ambientMap_zero_of_coordinates {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (f : Orbifold →ₗ[ℂ] V) (x : ComplexState)
    (h : ∀ i l S, coordinates b f i l S x = 0) : ambientMap f x = 0 := by
  let basis := (b.tensorProduct (carrierBasis hyperbolicPlane)).tensorProduct ghostBasis
  apply basis.repr.injective
  rw [map_zero]
  apply Finsupp.ext
  rintro ⟨⟨i, l⟩, S⟩
  exact h i l S

private theorem coordinates_separate {x : ComplexState}
    (hf : ∀ i l S, fixedCoord i l S x = 0)
    (ht : ∀ i l S, twistedCoord i l S x = 0) : x = 0 :=
  ambientMap_separates
    (ambientMap_zero_of_coordinates (carrierBasis leechData) fixedProjection x hf)
    (ambientMap_zero_of_coordinates (actualAmbientBasis leechData leechUnit)
      twistedProjection x ht)

private theorem matter_mode_tmul (n : ℤ) (v : Orbifold) (u : Plane) :
    matter.mode n (v ⊗ₜ[ℂ] u) =
      ActualLeechOrbifoldMatter.mode n v ⊗ₜ[ℂ] u +
        v ⊗ₜ[ℂ] hyperbolicMatter.mode n u := by
  change tensorMode ActualLeechOrbifoldMatter.matter hyperbolicMatter n _ = _
  simp only [tensorMode, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  rfl

private theorem plane_energy_coordinate (u : Plane) (l : Label hyperbolicPlane) :
    carrierCoeffEquiv hyperbolicPlane (hyperbolicMatter.mode 0 u) l =
      (LatticePositiveEnergy.energy hyperbolicPlane l : ℂ) *
        carrierCoeffEquiv hyperbolicPlane u l :=
  actualL0_coeff hyperbolicPlane _ plane_inverse plane_inverse u l

private theorem coordinates_energy {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (basis : Module.Basis ι ℂ V) (f : Orbifold →ₗ[ℂ] V)
    (i : ι) (l : Label hyperbolicPlane) (S : Finset ℕ) (w : ℂ)
    (h : ∀ v, basis.repr (f (ActualLeechOrbifoldMatter.mode 0 v)) i =
      w * basis.repr (f v) i) (x : ComplexState) :
    coordinates basis f i l S (E x) =
      (w + (LatticePositiveEnergy.energy hyperbolicPlane l : ℂ) +
        (BcGhostRelativeEnergy.energy S : ℂ)) * coordinates basis f i l S x := by
  induction x using TensorProduct.inductionOn with
  | tmul y g =>
    induction y using TensorProduct.inductionOn with
    | tmul v u =>
      change coordinates basis f i l S
        ((matter.mode 0 (v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] g) +
          ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] BcGhostVirasoro.L 0 g)) = _
      rw [matter_mode_tmul, TensorProduct.add_tmul]
      simp only [map_add, coordinates_tmul, h, plane_energy_coordinate,
        BcGhostRelativeEnergy.L_zero_coefficient]
      ring
    | add y z hy hz =>
      simp only [TensorProduct.add_tmul, map_add, hy, hz, mul_add]
  | add y z hy hz =>
    simp only [map_add, hy, hz, mul_add]

private def fixedWeight (i : Label leechData) : ℂ :=
  LatticePositiveEnergy.energy leechData i

private def twistedWeight (i : OddMonomial leechData) : ℂ :=
  (leechData.rank : ℂ) / 16 + (oddWeight leechData i : ℂ) / 2

private theorem fixedCoord_energy (i : Label leechData) (l : Label hyperbolicPlane)
    (S : Finset ℕ) (x : ComplexState) :
    fixedCoord i l S (E x) = (fixedWeight i +
      (LatticePositiveEnergy.energy hyperbolicPlane l : ℂ) +
      (BcGhostRelativeEnergy.energy S : ℂ)) * fixedCoord i l S x := by
  apply coordinates_energy
  intro v
  change carrierCoeffEquiv leechData (ActualLeechOrbifoldMatter.mode 0 v).1.val i = _
  have hm : (ActualLeechOrbifoldMatter.mode 0 v).1.val =
      sugawaraMode leechData (actualInverse leechData) 0 v.1.val :=
    congrArg Prod.fst (ActualLeechOrbifoldMatter.mode_apply 0 v)
  rw [hm]
  exact actualL0_coeff leechData _ (actualInverse_left leechData leechUnit)
    (actualInverse_right leechData leechUnit) v.1.val i

private theorem twistedCoord_energy (i : OddMonomial leechData × _)
    (l : Label hyperbolicPlane) (S : Finset ℕ) (x : ComplexState) :
    twistedCoord i l S (E x) = (twistedWeight i.1 +
      (LatticePositiveEnergy.energy hyperbolicPlane l : ℂ) +
      (BcGhostRelativeEnergy.energy S : ℂ)) * twistedCoord i l S x := by
  apply coordinates_energy
  intro v
  change (actualAmbientBasis leechData leechUnit).repr
    (ActualLeechOrbifoldMatter.mode 0 v).2.val i = _
  have hm : (ActualLeechOrbifoldMatter.mode 0 v).2.val =
      actualTensorL0 leechData leechUnit v.2.val :=
    congrArg Prod.snd (ActualLeechOrbifoldMatter.mode_apply 0 v)
  rw [hm]
  exact actualTensorL0_repr leechData leechUnit v.2.val i

private theorem plane_projection_coordinate (u : Plane) (l : Label hyperbolicPlane) :
    carrierCoeffEquiv hyperbolicPlane (chargeProjection u) l =
      (if l.1 = momentum then 1 else 0) * carrierCoeffEquiv hyperbolicPlane u l := by
  classical
  change ((Finsupp.single momentum (u momentum) : Plane) l.1).coeff l.2 =
    (if l.1 = momentum then 1 else 0) * (u l.1).coeff l.2
  by_cases h : l.1 = momentum <;> simp [h]

private theorem coordinates_momentum {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (basis : Module.Basis ι ℂ V) (f : Orbifold →ₗ[ℂ] V)
    (i : ι) (l : Label hyperbolicPlane) (S : Finset ℕ) (x : ComplexState) :
    coordinates basis f i l S (momentumProjection x) =
      (if l.1 = momentum then 1 else 0) * coordinates basis f i l S x := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul y g =>
    induction y using TensorProduct.inductionOn with
    | tmul v u =>
      change coordinates basis f i l S ((v ⊗ₜ[ℂ] chargeProjection u) ⊗ₜ[ℂ] g) = _
      simp only [coordinates_tmul, plane_projection_coordinate]
      ring
    | add y z hy hz =>
      simp only [TensorProduct.add_tmul, map_add, hy, hz, mul_add]
  | add y z hy hz =>
    simp only [map_add, hy, hz, mul_add]


private def momentumDifference : Module.End ℂ ComplexState where
  toFun x := momentumProjection x - x
  map_add' x y := by
    rw [map_add]
    exact add_sub_add_comm (momentumProjection x) (momentumProjection y) x y
  map_smul' a x := by
    rw [map_smul]
    exact (smul_sub a (momentumProjection x) x).symm

/-- The fixed-momentum absolute shell for the actual total L₀. -/
def absoluteShell : Submodule ℂ ComplexState :=
  LinearMap.ker momentumDifference ⊓ LinearMap.ker E

/-- The fixed-momentum zero-energy relative shell cut out by the actual b₀. -/
def C : Submodule ℂ ComplexState := absoluteShell ⊓ LinearMap.ker b0

private theorem mem_absoluteShell (x : ComplexState) :
    x ∈ absoluteShell ↔ momentumProjection x = x ∧ E x = 0 := by
  simp only [absoluteShell, momentumDifference, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.coe_mk, AddHom.coe_mk, sub_eq_zero]

private def groundState (g : Fock) : ComplexState :=
  (OriginalOrbifoldField.vacuumState leechData leechUnit ⊗ₜ[ℂ]
    Finsupp.single momentum 1) ⊗ₜ[ℂ] g

/-- The actual orbifold vacuum with the momentum ground and c(1) applied to the ghost vacuum. -/
def ψ : ComplexState := groundState (BcGhostFock.c 1 CountableOccupationFock.vacuum)

/-- The second absolute state, with ghost occupation at sites 1 and 3. -/
def ψ₁₃ : ComplexState := groundState (ket {1, 3})

private theorem psi_eq : ψ = groundState (ket {1}) := by
  rw [ψ, BcGhostFock.ghost_vacuum.2.2.1]

private theorem plane_chargeEnergy : chargeEnergy hyperbolicPlane momentum = 1 := by
  change (∑ i : Fin 2, ∑ j : Fin 2, OrderedHyperbolicExtension.U i j) / 2 = 1
  norm_num [OrderedHyperbolicExtension.U, Fin.sum_univ_two]

private theorem plane_weight_at_momentum (d : Exponent hyperbolicPlane) (S : Finset ℕ) :
    (LatticePositiveEnergy.energy hyperbolicPlane (momentum, d) : ℂ) +
      (BcGhostRelativeEnergy.energy S : ℂ) =
        (oscillatorEnergy d : ℂ) + (relativeEnergy S : ℂ) := by
  simp only [LatticePositiveEnergy.energy, plane_chargeEnergy,
    relativeEnergy, Int.cast_add, Int.cast_natCast, Int.cast_one]
  ring

private theorem relativeEnergy_zero_iff (S : Finset ℕ) :
    relativeEnergy S = 0 ↔ S = {1} ∨ S = {1, 3} := by
  classical
  constructor
  · intro h
    rw [BcGhostRelativeEnergy.relativeEnergy_split] at h
    have pos (j : ℕ) (hj : j ∈ (S.erase 1).erase 3) :
        0 < BcGhostRelativeEnergy.siteEnergy j :=
      BcGhostRelativeEnergy.siteEnergy_pos_of_ne_one_three
        (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1 (Finset.mem_erase.mp hj).1
    have nonneg := Finset.sum_nonneg (fun j hj => (pos j hj).le)
    have h1 : 1 ∈ S := by
      by_contra hn
      have hh : 1 + ∑ j ∈ (S.erase 1).erase 3, BcGhostRelativeEnergy.siteEnergy j = 0 := by
        simpa only [hn, not_false_eq_true, ite_true] using h
      omega
    have hsum : ∑ j ∈ (S.erase 1).erase 3, BcGhostRelativeEnergy.siteEnergy j = 0 := by
      simpa only [h1, not_true_eq_false, ite_false, zero_add] using h
    have hsites (j : ℕ) (hj : j ∈ S) : j = 1 ∨ j = 3 := by
      by_contra hn
      push Not at hn
      have hj' : j ∈ (S.erase 1).erase 3 := by simp [Finset.mem_erase, hj, hn.1, hn.2]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => (pos k hk).le)).mp hsum j hj'
      exact (pos j hj').ne' hz
    by_cases h3 : 3 ∈ S
    · right
      ext j
      simpa using show j ∈ S ↔ j = 1 ∨ j = 3 from
        ⟨hsites j, fun hj => hj.elim (fun e => e ▸ h1) (fun e => e ▸ h3)⟩
    · left
      ext j
      simpa using show j ∈ S ↔ j = 1 from
        ⟨fun hj => (hsites j hj).resolve_right (fun e => h3 (e ▸ hj)), fun e => e ▸ h1⟩
  · rintro (rfl | rfl) <;> norm_num [relativeEnergy, BcGhostRelativeEnergy.energy,
      BcGhostRelativeEnergy.siteEnergy_one, BcGhostRelativeEnergy.siteEnergy_three]

private theorem fixedWeight_nonneg (i : Label leechData) :
    0 ≤ (fixedWeight i).re := by
  change 0 ≤ ((LatticePositiveEnergy.energy leechData i : ℤ) : ℂ).re
  rw [Complex.intCast_re]
  have h : 0 ≤ LatticePositiveEnergy.energy leechData i :=
    add_nonneg (chargeEnergy_nonneg leechData leechPosDef i.1) (Int.natCast_nonneg _)
  exact_mod_cast h

private theorem fixedWeight_eq_zero (i : Label leechData) :
    (fixedWeight i).re = 0 ↔ i = (0, 0) := by
  rw [← energy_eq_zero_iff leechData leechPosDef]
  simp [fixedWeight]

private theorem twistedWeight_pos (i : OddMonomial leechData) :
    0 < (twistedWeight i).re := by
  have h : 0 ≤ (oddWeight leechData i : ℝ) := Nat.cast_nonneg _
  have hw : twistedWeight i =
      ((24 / 16 + (oddWeight leechData i : ℝ) / 2 : ℝ) : ℂ) := by
    simp [twistedWeight, leech_spec.1]
  rw [hw, Complex.ofReal_re]
  linarith

private theorem coordinates_off_momentum {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (basis : Module.Basis ι ℂ V) (f : Orbifold →ₗ[ℂ] V)
    (i : ι) (l : Label hyperbolicPlane) (S : Finset ℕ) {x : ComplexState}
    (hx : momentumProjection x = x) (hl : l.1 ≠ momentum) :
    coordinates basis f i l S x = 0 := by
  simpa only [hx, ite_eq_right hl, zero_mul] using coordinates_momentum basis f i l S x

private theorem fixedCoord_supported {x : ComplexState} (hx : x ∈ absoluteShell)
    (i : Label leechData) (l : Label hyperbolicPlane) (S : Finset ℕ)
    (h : fixedCoord i l S x ≠ 0) :
    i = (0, 0) ∧ l = (momentum, 0) ∧ (S = {1} ∨ S = {1, 3}) := by
  obtain ⟨hp, he⟩ := (mem_absoluteShell x).mp hx
  obtain ⟨a, d⟩ := l
  have ha : a = momentum := by
    by_contra hne
    exact h (coordinates_off_momentum _ _ i (a, d) S hp hne)
  subst a
  have hweight := fixedCoord_energy i (momentum, d) S x
  rw [he, map_zero, add_assoc, plane_weight_at_momentum] at hweight
  have hz := congrArg Complex.re ((mul_eq_zero.mp hweight.symm).resolve_right h)
  simp only [Complex.add_re, Complex.natCast_re, Complex.intCast_re, Complex.zero_re] at hz
  have hO := fixedWeight_nonneg i
  have hU : 0 ≤ (oscillatorEnergy d : ℝ) := Nat.cast_nonneg _
  have hG : 0 ≤ (relativeEnergy S : ℝ) := by exact_mod_cast relativeEnergy_nonneg S
  have hd : oscillatorEnergy d = 0 := by
    exact_mod_cast (show (oscillatorEnergy d : ℝ) = 0 by linarith)
  have hS : relativeEnergy S = 0 := by exact_mod_cast (show (relativeEnergy S : ℝ) = 0 by linarith)
  exact ⟨(fixedWeight_eq_zero i).mp (by linarith),
    Prod.ext rfl ((oscillatorEnergy_eq_zero_iff hyperbolicPlane d).mp hd),
    (relativeEnergy_zero_iff S).mp hS⟩

private theorem twistedCoord_vanishes {x : ComplexState} (hx : x ∈ absoluteShell)
    (i : OddMonomial leechData × _) (l : Label hyperbolicPlane) (S : Finset ℕ) :
    twistedCoord i l S x = 0 := by
  obtain ⟨hp, he⟩ := (mem_absoluteShell x).mp hx
  obtain ⟨a, d⟩ := l
  by_cases ha : a = momentum
  · subst a
    have hweight := twistedCoord_energy i (momentum, d) S x
    rw [he, map_zero, add_assoc, plane_weight_at_momentum] at hweight
    apply (mul_eq_zero.mp hweight.symm).resolve_left
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.natCast_re, Complex.intCast_re, Complex.zero_re] at hr
    have hO := twistedWeight_pos i.1
    have hU : 0 ≤ (oscillatorEnergy d : ℝ) := Nat.cast_nonneg _
    have hG : 0 ≤ (relativeEnergy S : ℝ) := by exact_mod_cast relativeEnergy_nonneg S
    linarith
  · exact coordinates_off_momentum _ _ i (a, d) S hp ha

private theorem fixedCoord_groundState (i : Label leechData) (l : Label hyperbolicPlane)
    (S : Finset ℕ) (g : Fock) :
    fixedCoord i l S (groundState g) =
      Finsupp.single (0, 0) (1 : ℂ) i *
        Finsupp.single (momentum, 0) (1 : ℂ) l * g S := by
  rw [groundState, coordinates_tmul]
  have h (D : LatticeData) (a : Charge D) :
      carrierBasis D (a, 0) = Finsupp.single a 1 := by simp
  change carrierCoeffEquiv leechData (Finsupp.single 0 1) i *
    carrierCoeffEquiv hyperbolicPlane (Finsupp.single momentum 1) l * g S = _
  rw [← h leechData 0, ← h hyperbolicPlane momentum, carrierCoeffEquiv_basis,
    carrierCoeffEquiv_basis]

private theorem twistedCoord_groundState (i : OddMonomial leechData × _)
    (l : Label hyperbolicPlane) (S : Finset ℕ) (g : Fock) :
    twistedCoord i l S (groundState g) = 0 := by
  rw [groundState, coordinates_tmul]
  change (actualAmbientBasis leechData leechUnit).repr 0 i * _ * _ = _
  simp

/-- The coefficient at the relative shell generator. -/
def ρ : ComplexState →ₗ[ℂ] ℂ := fixedCoord (0, 0) (momentum, 0) {1}

/-- The coefficient at the second absolute-shell generator. -/
def σ : ComplexState →ₗ[ℂ] ℂ := fixedCoord (0, 0) (momentum, 0) {1, 3}

private theorem groundState_mem_absoluteShell (T : Finset ℕ) (hT : relativeEnergy T = 0) :
    groundState (ket T) ∈ absoluteShell := by
  classical
  apply (mem_absoluteShell _).mpr
  constructor
  · change ((_ ⊗ₜ[ℂ] chargeProjection (Finsupp.single momentum 1)) ⊗ₜ[ℂ] _) = _
    simp [groundState, chargeProjection]
  · apply coordinates_separate
    · intro i l S
      rw [fixedCoord_energy, fixedCoord_groundState]
      by_cases hi : i = (0, 0)
      · by_cases hl : l = (momentum, 0)
        · by_cases hs : S = T
          · subst i l S
            rw [add_assoc, plane_weight_at_momentum, hT]
            simp [fixedWeight, (energy_eq_zero_iff leechData leechPosDef _).mpr rfl]
          · simp [ket, Finsupp.single_apply, Ne.symm hs]
        · simp [Ne.symm hl]
      · simp [Ne.symm hi]
    · intro i l S
      rw [twistedCoord_energy, twistedCoord_groundState, mul_zero]

private theorem psi_mem_absoluteShell : ψ ∈ absoluteShell := by
  rw [psi_eq]
  exact groundState_mem_absoluteShell _ ((relativeEnergy_zero_iff _).mpr (Or.inl rfl))

private theorem psi13_mem_absoluteShell : ψ₁₃ ∈ absoluteShell :=
  groundState_mem_absoluteShell _ ((relativeEnergy_zero_iff _).mpr (Or.inr rfl))

/-- The whole absolute shell has precisely the two displayed occupation coordinates. -/
theorem mem_absoluteShell_iff (x : ComplexState) :
    x ∈ absoluteShell ↔ x = ρ x • ψ + σ x • ψ₁₃ := by
  classical
  constructor
  · intro hx
    apply sub_eq_zero.mp
    apply coordinates_separate
    · intro i l S
      simp only [map_sub, map_add, map_smul, smul_eq_mul, psi_eq, ψ₁₃,
        fixedCoord_groundState]
      by_cases hs : i = (0, 0) ∧ l = (momentum, 0) ∧ (S = {1} ∨ S = {1, 3})
      · have hghost : ({1} : Finset ℕ) ≠ {1, 3} := by decide
        obtain ⟨rfl, rfl, rfl | rfl⟩ := hs <;>
          change fixedCoord _ _ _ x - _ = 0 <;>
          simp [ρ, σ, ket, Finsupp.single_apply, hghost, Ne.symm hghost]
      · have hz : fixedCoord i l S x = 0 := by
          by_contra hne
          exact hs (fixedCoord_supported hx i l S hne)
        rw [hz]
        by_cases hi : i = (0, 0)
        · by_cases hl : l = (momentum, 0)
          · have hS : S ≠ {1} ∧ S ≠ {1, 3} := by simpa [hi, hl] using hs
            simp [ket, Ne.symm hS.1, Ne.symm hS.2]
          · simp [Ne.symm hl]
        · simp [Ne.symm hi]
    · intro i l S
      simp only [map_sub, map_add, map_smul, psi_eq, ψ₁₃, twistedCoord_groundState,
        twistedCoord_vanishes hx, smul_zero, add_zero, sub_zero]
  · intro hx
    exact hx ▸ absoluteShell.add_mem (absoluteShell.smul_mem (ρ x) psi_mem_absoluteShell)
      (absoluteShell.smul_mem (σ x) psi13_mem_absoluteShell)

private theorem ground_coordinates_momentum (x : ComplexState) :
    ρ (momentumProjection x) = ρ x ∧ σ (momentumProjection x) = σ x := by
  constructor <;>
    simpa only [ρ, σ, Prod.fst, ite_true, one_mul] using
      coordinates_momentum (carrierBasis leechData) fixedProjection (0, 0) (momentum, 0) _ x

private theorem ground_coordinates_energy (x : ComplexState) : ρ (E x) = 0 ∧ σ (E x) = 0 := by
  have h (S : Finset ℕ) (hs : relativeEnergy S = 0) : fixedCoord (0, 0) (momentum, 0) S (E x) = 0 := by
    rw [fixedCoord_energy, add_assoc, plane_weight_at_momentum, hs]
    simp [fixedWeight, (energy_eq_zero_iff leechData leechPosDef _).mpr rfl]
  exact ⟨h _ ((relativeEnergy_zero_iff _).mpr (Or.inl rfl)),
    h _ ((relativeEnergy_zero_iff _).mpr (Or.inr rfl))⟩

/-- The absolute-shell projection takes the two surviving occupation coefficients. -/
def absoluteProjection : Module.End ℂ ComplexState where
  toFun x := ρ x • ψ + σ x • ψ₁₃
  map_add' x y := by
    simp only [map_add, add_smul]
    exact add_add_add_comm (ρ x • ψ) (ρ y • ψ) (σ x • ψ₁₃) (σ y • ψ₁₃)
  map_smul' a x := by
    simp only [map_smul, smul_add, smul_smul, smul_eq_mul, RingHom.id_apply]

/-- The absolute-shell projection preserves the selected momentum and is killed by total L₀. -/
theorem absoluteProjection_eq (x : ComplexState) :
    absoluteProjection x = x ↔ x ∈ absoluteShell :=
  ⟨fun h => (mem_absoluteShell_iff x).mpr h.symm,
    fun h => ((mem_absoluteShell_iff x).mp h).symm⟩

/-- The two-coordinate projection is idempotent and total L₀ annihilates it on either side. -/
theorem absoluteProjection_actions (x : ComplexState) :
    absoluteProjection (absoluteProjection x) = absoluteProjection x ∧
      E (absoluteProjection x) = 0 ∧ absoluteProjection (E x) = 0 ∧
      absoluteProjection (momentumProjection x) = absoluteProjection x := by
  have h : absoluteProjection x ∈ absoluteShell :=
    absoluteShell.add_mem (absoluteShell.smul_mem (ρ x) psi_mem_absoluteShell)
      (absoluteShell.smul_mem (σ x) psi13_mem_absoluteShell)
  refine ⟨(absoluteProjection_eq _).mpr h, ((mem_absoluteShell _).mp h).2, ?_, ?_⟩
  · change ρ (E x) • ψ + σ (E x) • ψ₁₃ = 0
    obtain ⟨hr, hs⟩ := ground_coordinates_energy x
    rw [hr, hs, zero_smul, zero_smul, add_zero]
  · change ρ (momentumProjection x) • ψ + σ (momentumProjection x) • ψ₁₃ =
      ρ x • ψ + σ x • ψ₁₃
    obtain ⟨hr, hs⟩ := ground_coordinates_momentum x
    rw [hr, hs]

private theorem rho_psi : ρ ψ = 1 := by
  rw [ψ, BcGhostFock.ghost_vacuum.2.2.1, ρ, fixedCoord_groundState]
  simp [ket]

private theorem b0_psi : b0 ψ = 0 := by
  rw [psi_eq]
  change _ ⊗ₜ[ℂ] BcGhostFock.b 0 (ket {1}) = _
  rw [BcGhostRelativeEnergy.b_zero_down, TensorProduct.tmul_zero]

private theorem ghost_b0_up : BcGhostFock.b 0 (ket {1, 3}) = -ket {1} := by
  change CountableOccupationFock.annihilate 3 (ket {1, 3}) = _
  have hc : CountableOccupationFock.lowerCount 3 {1, 3} = 1 := by decide
  have he : ({1, 3} : Finset ℕ).erase 3 = {1} := by decide
  rw [CountableOccupationFock.annihilate_ket]
  simp [CountableOccupationFock.phase, hc, he]

private theorem ghost_b0_coefficient (g : Fock) :
    (BcGhostFock.b 0 g) {1} = -g {1, 3} := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, neg_add]
  | single T a =>
    have h (T : Finset ℕ) : (BcGhostFock.b 0 (ket T)) {1} = -(ket T) {1, 3} := by
      by_cases hT : T = {1, 3}
      · subst T
        rw [ghost_b0_up]
        simp [ket]
      · change (CountableOccupationFock.annihilate 3 (ket T)) {1} = _
        rw [CountableOccupationFock.annihilate_ket]
        by_cases h3 : 3 ∈ T
        · have he : T.erase 3 ≠ {1} := by
            intro he
            apply hT
            rw [← Finset.insert_erase h3, he]
            decide
          simp [h3, ket, he, hT]
        · simp [h3, ket, hT]
    have ha : Finsupp.single T a = a • ket T := by simp [ket]
    rw [ha, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, h]
    simp [smul_eq_mul]

/-- Applying the actual b₀ feeds the second absolute coefficient into the first with sign −1. -/
theorem rho_b0 (x : ComplexState) : ρ (b0 x) = -σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul m g =>
    induction m using TensorProduct.inductionOn with
    | tmul v u =>
      change ρ ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] BcGhostFock.b 0 g) = -σ ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] g)
      simp only [ρ, σ, coordinates_tmul, ghost_b0_coefficient, mul_neg]
    | add y z hy hz =>
      simp only [TensorProduct.add_tmul, map_add, hy, hz, neg_add]
  | add y z hy hz =>
    simp only [map_add, hy, hz, neg_add]

private theorem psi_mem_C : ψ ∈ C := ⟨psi_mem_absoluteShell, b0_psi⟩

private theorem relative_coordinates {x : ComplexState} (hx : x ∈ C) : x = ρ x • ψ := by
  have habs := (mem_absoluteShell_iff x).mp hx.1
  have hb : b0 x = 0 := hx.2
  have hs : σ x = 0 := by
    have hc := rho_b0 x
    rw [hb, map_zero] at hc
    exact neg_eq_zero.mp hc.symm
  calc
    x = ρ x • ψ + σ x • ψ₁₃ := habs
    _ = ρ x • ψ := by simp [hs]

private theorem relative_span : C = Submodule.span ℂ ({ψ} : Set ComplexState) := by
  apply le_antisymm
  · intro x hx
    exact Submodule.mem_span_singleton.mpr ⟨ρ x, (relative_coordinates hx).symm⟩
  · exact (Submodule.span_singleton_le_iff_mem ψ C).mpr psi_mem_C

#print axioms mem_absoluteShell_iff
#print axioms absoluteProjection_actions
#print axioms rho_b0


/-- Ghost number on the same three-factor carrier. -/
abbrev N : Module.End ℂ ComplexState := VirasoroBRST.N matter

private theorem chargeProjection_single (a : Charge hyperbolicPlane)
    (u : Oscillator hyperbolicPlane) :
    chargeProjection (Finsupp.single a u) =
      if a = momentum then Finsupp.single a u else 0 := by
  classical
  by_cases h : a = momentum <;> simp [chargeProjection, h]

private theorem plane_mode_commutes_momentum (n : ℤ) (u : Plane) :
    chargeProjection (hyperbolicMatter.mode n u) =
      hyperbolicMatter.mode n (chargeProjection u) := by
  have h : chargeProjection.comp (hyperbolicMatter.mode n) =
      (hyperbolicMatter.mode n).comp chargeProjection := by
    apply Finsupp.lhom_ext
    intro a v
    change chargeProjection (hyperbolicMatter.mode n (Finsupp.single a v)) =
      hyperbolicMatter.mode n (chargeProjection (Finsupp.single a v))
    have action (w : Oscillator hyperbolicPlane) :
        hyperbolicMatter.mode n (Finsupp.single a w) =
          Finsupp.single a
            (sectorSugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane) a n w) :=
      sugawaraMode_single_sector hyperbolicPlane _ a n w
    rw [action, chargeProjection_single, chargeProjection_single]
    split_ifs <;> simp only [action, map_zero]
  exact LinearMap.congr_fun h u

private theorem momentum_matter_mode (n : ℤ) (x : Matter) :
    matterProjection (matter.mode n x) = matter.mode n (matterProjection x) := by
  have h : matterProjection.comp (matter.mode n) =
      (matter.mode n).comp matterProjection := by
    apply TensorProduct.ext'
    intro v u
    simp only [LinearMap.comp_apply, matter_mode_tmul, matterProjection, map_add,
      TensorProduct.map_tmul, LinearMap.id_apply, plane_mode_commutes_momentum]
  exact LinearMap.congr_fun h x

private theorem momentum_summand (n : ℤ) (x : ComplexState) :
    momentumProjection (VirasoroBRST.summand matter n x) =
      VirasoroBRST.summand matter n (momentumProjection x) := by
  have h : momentumProjection.comp (VirasoroBRST.summand matter n) =
      (VirasoroBRST.summand matter n).comp momentumProjection := by
    apply TensorProduct.ext'
    intro v u
    simp only [LinearMap.comp_apply, momentumProjection, VirasoroBRST.summand,
      TensorProduct.map_tmul, LinearMap.id_apply, momentum_matter_mode]
  exact LinearMap.congr_fun h x

private theorem momentum_ghostCharge (x : ComplexState) :
    momentumProjection (VirasoroBRST.ghostCharge matter x) =
      VirasoroBRST.ghostCharge matter (momentumProjection x) := by
  have h : momentumProjection.comp (VirasoroBRST.ghostCharge matter) =
      (VirasoroBRST.ghostCharge matter).comp momentumProjection := by
    apply TensorProduct.ext'
    intro v u
    rfl
  exact LinearMap.congr_fun h x

private theorem momentum_Q (x : ComplexState) :
    momentumProjection (Q x) = Q (momentumProjection x) := by
  change momentumProjection
      ((∑ᶠ n : ℤ, VirasoroBRST.summand matter n x) + VirasoroBRST.ghostCharge matter x) =
    (∑ᶠ n : ℤ, VirasoroBRST.summand matter n (momentumProjection x)) +
      VirasoroBRST.ghostCharge matter (momentumProjection x)
  rw [map_add, momentum_ghostCharge]
  have h := momentumProjection.toAddMonoidHom.map_finsum (VirasoroBRST.summand_finite matter x)
  change momentumProjection (∑ᶠ n : ℤ, VirasoroBRST.summand matter n x) =
    ∑ᶠ n : ℤ, momentumProjection (VirasoroBRST.summand matter n x) at h
  rw [h]
  simp only [momentum_summand]

private theorem Q_mem_C {x : ComplexState} (hx : x ∈ C) : Q x ∈ C := by
  obtain ⟨hp, he⟩ := (mem_absoluteShell x).mp hx.1
  have hb : b0 x = 0 := hx.2
  refine ⟨(mem_absoluteShell _).mpr ⟨by rw [momentum_Q, hp], ?_⟩, ?_⟩
  · have h : Q (E x) = E (Q x) := LinearMap.congr_fun Q_commutes_energy x
    rw [he, map_zero] at h
    exact h.symm
  · change b0 (Q x) = 0
    have h : Q (b0 x) + b0 (Q x) = E x :=
      LinearMap.congr_fun (VirasoroBRST.Q_ward_b matter 0) x
    simpa only [he, hb, map_zero, zero_add] using h

private theorem N_psi : N ψ = ψ := by
  rw [psi_eq]
  change _ ⊗ₜ[ℂ] BcGhostCharge.ghostNumber (ket {1}) = groundState (ket {1})
  have h : BcGhostCharge.ghostNumber (ket {1}) = ket {1} := by
    simp only [BcGhostCharge.ghostNumber, CountableOccupationFock.ket, Finsupp.lsum_single,
      LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]
    have hcharge : BcGhostCharge.charge {1} = 1 := by decide
    rw [hcharge, Int.cast_one, one_smul]
  rw [h]
  rfl

private theorem N_on_C {x : ComplexState} (hx : x ∈ C) : N x = x := by
  have h := relative_coordinates hx
  conv_lhs => rw [h]
  rw [map_smul, N_psi, ← h]

private theorem Q_on_C {x : ComplexState} (hx : x ∈ C) : Q x = 0 := by
  have h := LinearMap.congr_fun (VirasoroBRST.N_Q matter) x
  change N (Q x) - Q (N x) = Q x at h
  rwa [N_on_C (Q_mem_C hx), N_on_C hx, sub_self, eq_comm] at h

/-- The actual relative shell is the vacuum momentum line in degree one, with zero differential. -/
theorem normTwo_relative_shell :
    C = Submodule.span ℂ ({ψ} : Set ComplexState) ∧ N ψ = ψ ∧ ∀ x ∈ C, Q x = 0 :=
  ⟨relative_span, N_psi, fun _ hx => Q_on_C hx⟩

#print axioms normTwo_relative_shell

end D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativeNormTwo
