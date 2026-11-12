/-
SOURCE CANDIDATE. No elaboration, kernel, type-report or axiom-report claim.

Classification is the independently accepted sealed final export. Hom,
postcomposition, scalar probes and Ward are terminal SOURCE suppliers pending
native76935. The import LatticeDualCosetTransport is a PUBLIC SIGNATURE
DEPENDENCY ONLY: its sealed predecessor proof is REJECTED. Before compiling
this file, replace that module by the repaired and accepted supplier of
transport_all_modes, transportLinearEquiv, transport_single, transport_vacuum
and the normalized transportInverse definition. Repair29394 is independent;
none of its sources or artifacts was inspected here.

The reconstruction takes one actual finite tensor contraction. It does not
infer groundness from positive Ward, assume a minimum Hahn exponent, or use
representability in a bidual. The original scalar rigidity and the finite
source-coordinate tensor separation are reused, not reproved for a new target.
The only target is the original FullJacobiLatticeModule, in any universe.

Attribution: the original lattice/cocycle conventions are Bakalov--Kac,
math/0402315v1, section 4.1; the imported residue and conformal suppliers retain
Scott Carnahan's and Kalle Kytölä's attributions. The finite-contraction route
is the sealed completed normalized-transport Pro answer, Part B.
-/
import D5.S3.VertexAlgebra.Sectors.ActualWeakTargetWard
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleScalarProbes
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetTransport
import D5.S3.VertexAlgebra.Lattice.ActualZhuMinimum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullFusion

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField
open LatticeSugawaraCurrents LatticeActualConformalState LatticeDualCosetModule
open LatticeDiscriminantTheta LatticeDualCosetTransport
open Modules.FullJacobiCurrentTransport (FullJacobiLatticeModule)
open Modules.FullJacobiIntertwiner (ModuleHom ModuleIso)
open Modules.ActualWeakModuleSectorCoordinates (Model Sector Multiplicity weightIndex)
open Modules.ActualWeakModuleClassification (inverseGram classificationEquiv)
open Modules.ActualWeakModuleScalarProbes (contract component scalarProbe)
open Modules.ActualWeakModuleHom (homSpace recordEquiv)
open ActualWeakTargetFullIntertwiner

universe u v w
variable {D : LatticeData}
variable {M : Type u} {N : Type v}
variable [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

local instance : DecidableEq (Discriminant D) := Classical.decEq _

private theorem gram_left (positiveG : (gramReal D).PosDef) :
    inverseGram positiveG * gramComplex D = 1 :=
  (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D positiveG)).1

private theorem gram_right (positiveG : (gramReal D).PosDef) :
    gramComplex D * inverseGram positiveG = 1 :=
  (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D positiveG)).2

/-- All full original module maps; this is the supplier's faithful Hom submodule. -/
abbrev Hom (d : Charge D) (J : FullJacobiLatticeModule D M) :=
  homSpace (scalarModule D d) J

/-- All lawful rational Hahn fields, with the inverse Gram constructed internally. -/
abbrev FullFields (positiveG : (gramReal D).PosDef) (a b : Charge D)
    (J : FullJacobiLatticeModule D M) :=
  operatorSpace D a b (inverseGram positiveG) J

/-- The distinguished exponent is the literal scalar supplier's raw exponent. -/
def q0 (a b : Charge D) : ℚ :=
  LatticeDualCosetIntertwiner.groundPower D (dualVector D a) (dualVector D b) 0 0

theorem q0_pairing (a b : Charge D) :
    q0 a b = LatticeDualCosetEnergy.pairing D (dualVector D a) (dualVector D b) := by
  simp only [q0, LatticeDualCosetIntertwiner.groundPower,
    LatticeDualCosetEnergy.pairing, Pi.zero_apply, Int.cast_zero, zero_add]

/-- The literal B=id canonical field, in the actual scalar target. -/
def canonical (positiveG : (gramReal D).PosDef) (a b : Charge D) :
    FullFields positiveG a b (scalarModule D (a+b)) :=
  (scalarReadback D a b (inverseGram positiveG)).symm
    (LatticeDualCosetFusion.canonicalOperator D positiveG a b (inverseGram positiveG)
      (gram_left positiveG) (gram_right positiveG))

@[simp] theorem canonical_val (positiveG : (gramReal D).PosDef) (a b : Charge D) :
    (canonical positiveG a b).val =
      LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b := rfl

private def scalarCoordinate' (positiveG : (gramReal D).PosDef) (a b : Charge D) :=
  scalarCoordinate D positiveG a b (inverseGram positiveG)
    (gram_left positiveG) (gram_right positiveG) (dualVector D a) (dualVector D b)
    (Lattice.ActualZhuMinimum.dualVector_hDual D positiveG a)
    (Lattice.ActualZhuMinimum.dualVector_hDual D positiveG b)

private theorem canonical_coordinate (positiveG : (gramReal D).PosDef)
    (a b : Charge D) : scalarCoordinate' positiveG a b (canonical positiveG a b) = 1 := by
  exact LatticeDualCosetFusion.canonical_groundEvaluation D positiveG a b
    (inverseGram positiveG) (gram_left positiveG) (gram_right positiveG)
    (dualVector D a) (dualVector D b)
    (Lattice.ActualZhuMinimum.dualVector_hDual D positiveG a)
    (Lattice.ActualZhuMinimum.dualVector_hDual D positiveG b)

/-- The vector normalization, not merely a nonzero scalar coordinate. -/
theorem canonical_vacuum_coefficient (positiveG : (gramReal D).PosDef)
    (a b : Charge D) :
    ((canonical positiveG a b).val (vacuum D)).coeff (q0 a b) (vacuum D) = vacuum D := by
  have h := LatticeDualCosetIntertwiner.ground_leading D a b (inverseGram positiveG)
    (canonical positiveG a b).val
    ((scalar_lawful_iff D a b (inverseGram positiveG) _).mp
      (canonical positiveG a b).property)
    (gram_left positiveG) (gram_right positiveG) (dualVector D a) (dualVector D b)
    (Lattice.ActualZhuMinimum.dualVector_hDual D positiveG a)
    (Lattice.ActualZhuMinimum.dualVector_hDual D positiveG b) 0 0
  have hc := canonical_coordinate positiveG a b
  change LatticeDualCosetIntertwiner.groundScalar D
    (canonical positiveG a b).val (dualVector D a) (dualVector D b) 0 0 = 1 at hc
  simpa only [hc, one_smul, zero_add, q0, LatticeDualCosetIntertwiner.ground,
    vacuum] using h

private theorem scalar_reconstruction (positiveG : (gramReal D).PosDef)
    (a b : Charge D) (I : FullFields positiveG a b (scalarModule D (a+b))) :
    I = scalarCoordinate' positiveG a b I • canonical positiveG a b := by
  apply (scalarCoordinate' positiveG a b).injective
  rw [map_smul, canonical_coordinate, smul_eq_mul, mul_one]

/-- The genuine ModuleIso adapter uses only the desired public all-mode theorem.
No OriginalModule, ModeTarget, ModeHom or predecessor cyclicity is consumed. -/
def normalizedTransportIso (β n : Charge D) :
    ModuleIso (scalarModule D (shiftedCharge D β n)) (scalarModule D β) where
  linearEquiv := transportLinearEquiv D β n
  intertwines h m x := transport_all_modes D β n h x m

/-- The inverse is the actual normalized inverse, including epsilon(-n,n)^-1. -/
theorem normalizedTransport_inverse (β n : Charge D) (x : Carrier D) :
    (normalizedTransportIso β n).linearEquiv.symm x =
      (epsilon D (-n) n)⁻¹ • transport D (shiftedCharge D β n) (-n) x := rfl

private abbrev matchingClass (positiveG : (gramReal D).PosDef) (a b : Charge D) :=
  (weightIndex positiveG (a+b)).1

private abbrev matchingShift (positiveG : (gramReal D).PosDef) (a b : Charge D) :=
  (weightIndex positiveG (a+b)).2

private theorem matching_charge (positiveG : (gramReal D).PosDef) (a b : Charge D) :
    shiftedCharge D (representative D (matchingClass positiveG a b))
      (matchingShift positiveG a b) = a+b := by
  exact Modules.ActualWeakModuleSectorCoordinates.weightIndex_spec positiveG (a+b)

private def matchingIso (positiveG : (gramReal D).PosDef) (a b : Charge D) :
    ModuleIso (scalarModule D (a+b))
      (scalarModule D (representative D (matchingClass positiveG a b))) where
  linearEquiv := transportLinearEquiv D
    (representative D (matchingClass positiveG a b)) (matchingShift positiveG a b)
  intertwines h m x := by
    change transport D (representative D (matchingClass positiveG a b))
        (matchingShift positiveG a b) (((action D (a+b) h)[[m]]) x) =
      ((action D (representative D (matchingClass positiveG a b)) h)[[m]])
        (transport D (representative D (matchingClass positiveG a b))
          (matchingShift positiveG a b) x)
    rw [← matching_charge positiveG a b]
    exact transport_all_modes D
      (representative D (matchingClass positiveG a b))
      (matchingShift positiveG a b) h x m

private theorem matchingIso_single (positiveG : (gramReal D).PosDef)
    (a b l : Charge D) (P : Oscillator D) :
    (matchingIso positiveG a b).linearEquiv (Finsupp.single l P) =
      epsilon D l (matchingShift positiveG a b) •
        Finsupp.single (l + matchingShift positiveG a b) P :=
  transport_single D (representative D (matchingClass positiveG a b))
    (matchingShift positiveG a b) l P

private theorem matchingIso_vacuum (positiveG : (gramReal D).PosDef)
    (a b : Charge D) :
    (matchingIso positiveG a b).linearEquiv (vacuum D) =
      Finsupp.single (matchingShift positiveG a b) 1 :=
  transport_vacuum D (representative D (matchingClass positiveG a b))
    (matchingShift positiveG a b)

section FiniteContraction
variable {W : Type w} [AddCommGroup W] [Module ℂ W]

/-- A finite left contraction on the actual algebraic tensor product. -/
private def leftContract (e : Carrier D →ₗ[ℂ] ℂ) : Carrier D ⊗[ℂ] W →ₗ[ℂ] W :=
  (TensorProduct.lid ℂ W).toLinearMap.comp (TensorProduct.map e LinearMap.id)

private theorem leftContract_tmul (e : Carrier D →ₗ[ℂ] ℂ) (x : Carrier D) (z : W) :
    leftContract e (x ⊗ₜ[ℂ] z) = e x • z := by
  simp only [leftContract, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul]

/-- Commutation of two contractions on ONE tensor. No bidual or common support. -/
private theorem contraction_commutes (e : Carrier D →ₗ[ℂ] ℂ)
    (A : Module.End ℂ (Carrier D)) (ell : W →ₗ[ℂ] ℂ)
    (x : Carrier D ⊗[ℂ] W) :
    ell (leftContract e (TensorProduct.map A LinearMap.id x)) =
      e (A (contract ell x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul y z =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      leftContract_tmul, Modules.ActualWeakModuleScalarProbes.contract_tmul,
      map_smul, smul_eq_mul]
    exact mul_comm _ _
  | add x y hx hy => simp only [map_add, hx, hy]

end FiniteContraction

private def vacuumCoordinate : Carrier D →ₗ[ℂ] ℂ :=
  Modules.ActualWeakModuleScalarProbes.coordinate D (0, 0)

@[simp] private theorem vacuumCoordinate_apply (x : Carrier D) :
    vacuumCoordinate x = MvPolynomial.constantCoeff (x 0) := rfl

variable (positiveG : (gramReal D).PosDef) (a b : Charge D)
variable (J : FullJacobiLatticeModule D M)

private def probe (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ) :
    ModuleHom J (scalarModule D (representative D c)) :=
  Modules.ActualWeakModuleScalarProbes.scalarProbeHom J positiveG c ell

private def probeField (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ)
    (I : FullFields positiveG a b J) :
    FullFields positiveG a b (scalarModule D (representative D c)) :=
  post a b (inverseGram positiveG) (probe positiveG J c ell) I

private def matchingField (ell : Multiplicity J (matchingClass positiveG a b) →ₗ[ℂ] ℂ)
    (I : FullFields positiveG a b J) :
    FullFields positiveG a b (scalarModule D (a+b)) :=
  post a b (inverseGram positiveG) (matchingIso positiveG a b).inv
    (probeField positiveG a b J (matchingClass positiveG a b) ell I)

private def classificationIso :
    ModuleIso (Modules.ActualWeakModuleClassification.canonicalModule J) J where
  linearEquiv := classificationEquiv J positiveG
  intertwines := Modules.ActualWeakModuleClassification.classification J positiveG

/-- The full field is first transported by the literal classification inverse.
Its two translations and three finite supports are supplied by lawful post. -/
private def modelField (I : FullFields positiveG a b J) :
    FullFields positiveG a b (Modules.ActualWeakModuleClassification.canonicalModule J) :=
  post a b (inverseGram positiveG) (classificationIso positiveG J).inv I

private theorem wrong_probe (c : Discriminant D) (ell : Multiplicity J c →ₗ[ℂ] ℂ)
    (I : FullFields positiveG a b J) (hc : c ≠ matchingClass positiveG a b)
    (s t : Carrier D) (q : ℚ) :
    scalarProbe J positiveG c ell ((I.val s).coeff q t) = 0 := by
  have h := eq_zero_of_wrong_representative
    (probeField positiveG a b J c ell I).property positiveG hc
  have he := congrArg (fun K : Fields D (Carrier D) => (K s).coeff q t) h
  change (probe positiveG J c ell).linearMap ((I.val s).coeff q t) = 0
  change (probe positiveG J c ell).linearMap ((I.val s).coeff q t) = 0 at he
  simpa only [probeField, post_coeff] using he

/-- One actual vector is read from the original field; no ground assertion. -/
def distinguishedCoefficient (I : FullFields positiveG a b J) : M :=
  (I.val (vacuum D)).coeff (q0 a b) (vacuum D)

/-- An actual multiplicity vector extracted before proving any groundness.
The order is pr_c, U tensor id, e tensor id, then C tensor N = N. -/
def multiplicityVector (I : FullFields positiveG a b J) :
    Multiplicity J (matchingClass positiveG a b) :=
  leftContract vacuumCoordinate
    (TensorProduct.map (matchingIso positiveG a b).linearEquiv.symm.toLinearMap LinearMap.id
      (component J (matchingClass positiveG a b)
        (distinguishedCoefficient positiveG a b
          (Modules.ActualWeakModuleClassification.canonicalModule J)
          (modelField positiveG a b J I))))

theorem multiplicityVector_add (I K : FullFields positiveG a b J) :
    multiplicityVector positiveG a b J (I+K) =
      multiplicityVector positiveG a b J I + multiplicityVector positiveG a b J K := by
  change leftContract vacuumCoordinate
    (TensorProduct.map (matchingIso positiveG a b).linearEquiv.symm.toLinearMap LinearMap.id
      (component J (matchingClass positiveG a b)
        ((classificationEquiv J positiveG).symm
          (((I+K).val (vacuum D)).coeff (q0 a b) (vacuum D))))) = _
  change leftContract vacuumCoordinate
    (TensorProduct.map (matchingIso positiveG a b).linearEquiv.symm.toLinearMap LinearMap.id
      (component J (matchingClass positiveG a b)
        ((classificationEquiv J positiveG).symm
          (((I.val + K.val) (vacuum D)).coeff (q0 a b) (vacuum D))))) = _
  simp only [multiplicityVector, Pi.add_apply, LinearMap.add_apply, map_add]
  rfl

theorem multiplicityVector_smul (c : ℂ) (I : FullFields positiveG a b J) :
    multiplicityVector positiveG a b J (c • I) =
      c • multiplicityVector positiveG a b J I := by
  change leftContract vacuumCoordinate
    (TensorProduct.map (matchingIso positiveG a b).linearEquiv.symm.toLinearMap LinearMap.id
      (component J (matchingClass positiveG a b)
        ((classificationEquiv J positiveG).symm
          (((c • I).val (vacuum D)).coeff (q0 a b) (vacuum D))))) = _
  change leftContract vacuumCoordinate
    (TensorProduct.map (matchingIso positiveG a b).linearEquiv.symm.toLinearMap LinearMap.id
      (component J (matchingClass positiveG a b)
        ((classificationEquiv J positiveG).symm
          (((c • I.val) (vacuum D)).coeff (q0 a b) (vacuum D))))) = _
  simp only [multiplicityVector, Pi.smul_apply, LinearMap.smul_apply, map_smul,
    RingHom.id_apply]
  rfl

private theorem scalar_is_contraction
    (ell : Multiplicity J (matchingClass positiveG a b) →ₗ[ℂ] ℂ)
    (I : FullFields positiveG a b J) :
    scalarCoordinate' positiveG a b (matchingField positiveG a b J ell I) =
      ell (multiplicityVector positiveG a b J I) := by
  rw [multiplicityVector, contraction_commutes]
  change LatticeDualCosetIntertwiner.groundScalar D
    (matchingField positiveG a b J ell I).val (dualVector D a) (dualVector D b) 0 0 = _
  change MvPolynomial.constantCoeff
    (((matchingIso positiveG a b).linearEquiv.symm
      (scalarProbe J positiveG (matchingClass positiveG a b) ell
        ((I.val (vacuum D)).coeff (q0 a b) (vacuum D)))) 0) = _
  rfl

private theorem matching_probe
    (ell : Multiplicity J (matchingClass positiveG a b) →ₗ[ℂ] ℂ)
    (I : FullFields positiveG a b J) (s t : Carrier D) (q : ℚ) :
    scalarProbe J positiveG (matchingClass positiveG a b) ell ((I.val s).coeff q t) =
      ell (multiplicityVector positiveG a b J I) •
        (matchingIso positiveG a b).linearEquiv
          (((canonical positiveG a b).val s).coeff q t) := by
  have h := scalar_reconstruction positiveG a b (matchingField positiveG a b J ell I)
  rw [scalar_is_contraction] at h
  have he := congrArg
    (fun K : FullFields positiveG a b (scalarModule D (a+b)) => (K.val s).coeff q t) h
  change (matchingIso positiveG a b).linearEquiv.symm
      (scalarProbe J positiveG (matchingClass positiveG a b) ell ((I.val s).coeff q t)) =
    ell (multiplicityVector positiveG a b J I) •
      (((canonical positiveG a b).val s).coeff q t) at he
  have ht := congrArg (matchingIso positiveG a b).linearEquiv he
  simpa only [LinearEquiv.apply_symm_apply, map_smul] using ht

private def tensorInsert {W : Type w} [AddCommGroup W] [Module ℂ W]
    (z : W) : Carrier D →ₗ[ℂ] Carrier D ⊗[ℂ] W :=
  (TensorProduct.mk ℂ (Carrier D) W).flip z

/-- The actual full original morphism Theta(lof_c(T(x) tensor z)). -/
def reconstructionHom (z : Multiplicity J (matchingClass positiveG a b)) :
    ModuleHom (scalarModule D (a+b)) J where
  linearMap := (classificationEquiv J positiveG).toLinearMap.comp
    ((DirectSum.lof ℂ (Discriminant D) (Sector J) (matchingClass positiveG a b)).comp
      ((tensorInsert z).comp (matchingIso positiveG a b).linearEquiv.toLinearMap))
  intertwines h m x := by
    change classificationEquiv J positiveG
      (DirectSum.lof ℂ (Discriminant D) (Sector J) (matchingClass positiveG a b)
        ((matchingIso positiveG a b).linearEquiv
          (Modules.FullJacobiCurrentTransport.mode (scalarModule D (a+b)) h m x) ⊗ₜ[ℂ] z)) = _
    rw [(matchingIso positiveG a b).intertwines]
    have hD' : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)) := by
      simpa [LatticeDiscriminantTheta.gramReal] using positiveG
    have hc := Modules.ActualWeakModuleClassification.classification J hD' h m
      (DirectSum.lof ℂ (Discriminant D) (Sector J) (matchingClass positiveG a b)
        (((matchingIso positiveG a b).linearEquiv x) ⊗ₜ[ℂ] z))
    convert hc using 1 <;>
      simp [LatticeDiscriminantTheta.gramReal,
        Modules.FullJacobiCurrentTransport.mode, scalarModule,
        Modules.ActualWeakModuleClassification.canonicalModule,
        Modules.FullJacobiDirectSum.directSumModule_mode,
        DirectSum.lmap_lof, Modules.FullJacobiTensorModule.tensorModule_mode,
        TensorProduct.map_tmul, tensorInsert]

private theorem reconstructionHom_probe_same
    (z : Multiplicity J (matchingClass positiveG a b))
    (ell : Multiplicity J (matchingClass positiveG a b) →ₗ[ℂ] ℂ) (x : Carrier D) :
    scalarProbe J positiveG (matchingClass positiveG a b) ell
      ((reconstructionHom positiveG a b J z).linearMap x) =
      ell z • (matchingIso positiveG a b).linearEquiv x := by
  exact Modules.ActualWeakModuleScalarProbes.scalarProbe_classification_lof_tmul
    J positiveG (matchingClass positiveG a b) ell _ z

private theorem reconstructionHom_probe_wrong
    (z : Multiplicity J (matchingClass positiveG a b)) (c : Discriminant D)
    (ell : Multiplicity J c →ₗ[ℂ] ℂ) (hc : c ≠ matchingClass positiveG a b)
    (x : Carrier D) :
    scalarProbe J positiveG c ell ((reconstructionHom positiveG a b J z).linearMap x) = 0 := by
  exact Modules.ActualWeakModuleScalarProbes.scalarProbe_classification_lof_ne
    J positiveG c (matchingClass positiveG a b) ell (Ne.symm hc) _

/-- Every original source/input/rational coefficient is reconstructed.
Separation is applied to this individual coefficient, with no common support. -/
theorem reconstruction_coefficient (I : FullFields positiveG a b J)
    (s t : Carrier D) (q : ℚ) :
    (reconstructionHom positiveG a b J (multiplicityVector positiveG a b J I)).linearMap
      (((canonical positiveG a b).val s).coeff q t) = (I.val s).coeff q t := by
  apply Modules.ActualWeakModuleScalarProbes.scalarProbe_ext J positiveG
  intro c ell
  by_cases hc : c = matchingClass positiveG a b
  · subst c
    rw [reconstructionHom_probe_same, matching_probe]
  · rw [reconstructionHom_probe_wrong positiveG a b J _ c ell hc,
      wrong_probe positiveG a b J c ell I hc]

/-- The forward map is literally postcomposition of canonical B=id. -/
def forward : Hom (a+b) J →ₗ[ℂ] FullFields positiveG a b J where
  toFun f := post a b (inverseGram positiveG)
    ((recordEquiv (scalarModule D (a+b)) J).symm f) (canonical positiveG a b)
  map_add' f g := by
    apply Subtype.ext
    exact rawPost_add f.val g.val (canonical positiveG a b).val
  map_smul' c f := by
    apply Subtype.ext
    exact rawPost_smul c f.val (canonical positiveG a b).val

@[simp] theorem forward_coefficient (f : Hom (a+b) J) (s t : Carrier D) (q : ℚ) :
    (((forward positiveG a b J f).val s).coeff q t) =
      f.val (((canonical positiveG a b).val s).coeff q t) := rfl

/-- The explicitly constructed inverse, using the already existing Hom carrier. -/
def inverse (I : FullFields positiveG a b J) : Hom (a+b) J :=
  recordEquiv (scalarModule D (a+b)) J
    (reconstructionHom positiveG a b J (multiplicityVector positiveG a b J I))

theorem forward_inverse (I : FullFields positiveG a b J) :
    forward positiveG a b J (inverse positiveG a b J I) = I := by
  apply Subtype.ext
  apply fields_ext
  intro s t q
  exact reconstruction_coefficient positiveG a b J I s t q

/-- Correct charged generation: the mode depends on the physical sector
charge. In particular it is not uniformly -1. -/
private theorem charged_vacuum_generation (d n : Charge D) :
    Modules.FullJacobiCurrentTransport.mode (scalarModule D d)
      (Finsupp.single n (1 : Oscillator D)) (-(∑ i, n i * d i)-1) (vacuum D) =
        Finsupp.single n 1 := by
  simpa [Modules.FullJacobiCurrentTransport.mode, scalarModule,
    LatticeDualCosetIntertwiner.ground, LatticeDualCosetIntertwiner.chargedPower,
    vacuum, bilinear, epsilon, lowerCocycleExponent, paritySign] using
      LatticeDualCosetIntertwiner.charged_ground_leading D d n 0

private theorem negative_current_generation (d n : Charge D) (P : Oscillator D)
    (i : Fin D.rank) (k : ℕ) :
    Modules.FullJacobiCurrentTransport.mode (scalarModule D d) (currentState D i)
      (-(k : ℤ)-1) (Finsupp.single n P) =
        Finsupp.single n (MvPolynomial.X (i,k) * P) := by
  change ((action D d (currentState D i))[[-(k : ℤ)-1]]) (Finsupp.single n P) = _
  rw [currentState, action_current_coefficients]
  simp only [shiftedCurrentPolynomial, show -(k : ℤ)-1 < 0 by omega, if_pos,
    LinearMap.mulLeft_apply, show (-(-(k : ℤ)-1)-1).toNat = k by omega]

/-- A direct original-module cyclicity proof, independent of the rejected
predecessor's fixed-mode lemma and of the pending Hom correspondence. -/
theorem fullHom_ext_vacuum {d : Charge D}
    (f g : ModuleHom (scalarModule D d) J)
    (h0 : f.linearMap (vacuum D) = g.linearMap (vacuum D)) : f = g := by
  have hg (n : Charge D) :
      f.linearMap (Finsupp.single n (1 : Oscillator D)) =
        g.linearMap (Finsupp.single n (1 : Oscillator D)) := by
    rw [← charged_vacuum_generation d n, f.intertwines, g.intertwines, h0]
  have hp (n : Charge D) (P : Oscillator D) :
      f.linearMap (Finsupp.single n P) = g.linearMap (Finsupp.single n P) := by
    induction P using MvPolynomial.induction_on with
    | C c =>
      have hc : (MvPolynomial.C c : Oscillator D) = c • 1 :=
        MvPolynomial.C_eq_smul_one
      rw [hc, ← Finsupp.smul_single, map_smul, map_smul, hg]
    | add P Q hP hQ =>
      simp only [Finsupp.single_add, map_add, hP, hQ]
    | mul_X P x hP =>
      have hs : Finsupp.single n (P * MvPolynomial.X x) =
          Modules.FullJacobiCurrentTransport.mode (scalarModule D d) (currentState D x.1)
            (-(x.2 : ℤ)-1) (Finsupp.single n P) := by
        rw [negative_current_generation]
        rw [mul_comm]
      rw [hs, f.intertwines, g.intertwines, hP]
  apply (recordEquiv (scalarModule D d) J).injective
  apply Subtype.ext
  apply Finsupp.lhom_ext
  intro n P
  exact hp n P

private theorem hom_ext_vacuum {d : Charge D} (f g : Hom d J)
    (h0 : f.val (vacuum D) = g.val (vacuum D)) : f = g := by
  have h := fullHom_ext_vacuum J
    ((recordEquiv (scalarModule D d) J).symm f)
    ((recordEquiv (scalarModule D d) J).symm g) h0
  exact (recordEquiv (scalarModule D d) J).symm.injective h

@[simp] theorem distinguishedCoefficient_forward (f : Hom (a+b) J) :
    distinguishedCoefficient positiveG a b J (forward positiveG a b J f) =
      f.val (vacuum D) := by
  change f.val (((canonical positiveG a b).val (vacuum D)).coeff
    (q0 a b) (vacuum D)) = _
  rw [canonical_vacuum_coefficient]

theorem inverse_vacuum (I : FullFields positiveG a b J) :
    (inverse positiveG a b J I).val (vacuum D) =
      distinguishedCoefficient positiveG a b J I := by
  have h := congrArg (distinguishedCoefficient positiveG a b J)
    (forward_inverse positiveG a b J I)
  simpa only [distinguishedCoefficient_forward] using h

theorem forward_injective : Function.Injective (forward positiveG a b J) := by
  intro f g h
  apply hom_ext_vacuum J f g
  have he := congrArg (distinguishedCoefficient positiveG a b J) h
  simpa only [distinguishedCoefficient_forward] using he

theorem inverse_forward (f : Hom (a+b) J) :
    inverse positiveG a b J (forward positiveG a b J f) = f := by
  apply forward_injective positiveG a b J
  exact forward_inverse positiveG a b J (forward positiveG a b J f)

/-- Linearity is also forced by the proved coefficient reconstruction and
cyclicity, with no choice of classification coordinates in the conclusion. -/
def inverseLinear : FullFields positiveG a b J →ₗ[ℂ] Hom (a+b) J where
  toFun := inverse positiveG a b J
  map_add' I K := by
    apply forward_injective positiveG a b J
    rw [map_add, forward_inverse, forward_inverse, forward_inverse]
  map_smul' c I := by
    apply forward_injective positiveG a b J
    calc
      forward positiveG a b J (inverse positiveG a b J (c • I)) = c • I :=
        forward_inverse positiveG a b J (c • I)
      _ = c • forward positiveG a b J (inverse positiveG a b J I) := by
        rw [forward_inverse]
      _ = forward positiveG a b J (c • inverse positiveG a b J I) := by
        symm
        exact (forward positiveG a b J).map_smul c
          (inverse positiveG a b J I)

/-- The original full arbitrary-target fusion equivalence. Its only inputs
are the original positiveG, two integral dual labels and the original weak J.
The forward field is the literal postcomposition of canonical B=id. -/
def fusionEquiv : Hom (a+b) J ≃ₗ[ℂ] FullFields positiveG a b J where
  toLinearMap := forward positiveG a b J
  invFun := inverse positiveG a b J
  left_inv := inverse_forward positiveG a b J
  right_inv := forward_inverse positiveG a b J

@[simp] theorem fusionEquiv_coefficient (f : Hom (a+b) J)
    (s t : Carrier D) (q : ℚ) :
    (((fusionEquiv positiveG a b J f).val s).coeff q t) =
      f.val ((LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ)
        a b s).coeff q t) := rfl

/-- The finite-contraction inverse on EVERY charge and oscillator polynomial.
There is exactly one forward epsilon, the scalar in the prescribed T formula. -/
theorem inverse_single (I : FullFields positiveG a b J)
    (l : Charge D) (P : Oscillator D) :
    (inverse positiveG a b J I).val (Finsupp.single l P) =
      epsilon D l (matchingShift positiveG a b) •
        classificationEquiv J positiveG
          (DirectSum.lof ℂ (Discriminant D) (Sector J) (matchingClass positiveG a b)
            (Finsupp.single (l + matchingShift positiveG a b) P ⊗ₜ[ℂ]
              multiplicityVector positiveG a b J I)) := by
  change classificationEquiv J positiveG
    (DirectSum.lof ℂ (Discriminant D) (Sector J) (matchingClass positiveG a b)
      ((matchingIso positiveG a b).linearEquiv (Finsupp.single l P) ⊗ₜ[ℂ]
        multiplicityVector positiveG a b J I)) = _
  rw [matchingIso_single, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    map_smul, map_smul]

/-- Only after reconstruction do all coefficients acquire one sector and
one actual multiplicity vector. This is a consequence, not a field predicate. -/
theorem classification_inverse_coefficient (I : FullFields positiveG a b J)
    (s t : Carrier D) (q : ℚ) :
    (classificationEquiv J positiveG).symm ((I.val s).coeff q t) =
      DirectSum.lof ℂ (Discriminant D) (Sector J) (matchingClass positiveG a b)
        ((matchingIso positiveG a b).linearEquiv
          (((canonical positiveG a b).val s).coeff q t) ⊗ₜ[ℂ]
            multiplicityVector positiveG a b J I) := by
  have hr := reconstruction_coefficient positiveG a b J I s t q
  change classificationEquiv J positiveG
      (DirectSum.lof ℂ (Discriminant D) (Sector J) (matchingClass positiveG a b)
        ((matchingIso positiveG a b).linearEquiv
          (((canonical positiveG a b).val s).coeff q t) ⊗ₜ[ℂ]
            multiplicityVector positiveG a b J I)) =
      (I.val s).coeff q t at hr
  have hs := congrArg (classificationEquiv J positiveG).symm hr
  simpa only [LinearEquiv.symm_apply_apply] using hs.symm

/-- No minimum-exponent or positive-current inference precedes this equality. -/
theorem classification_inverse_distinguishedCoefficient (I : FullFields positiveG a b J) :
    (classificationEquiv J positiveG).symm (distinguishedCoefficient positiveG a b J I) =
      DirectSum.lof ℂ (Discriminant D) (Sector J) (matchingClass positiveG a b)
        (Finsupp.single (matchingShift positiveG a b) (1 : Oscillator D) ⊗ₜ[ℂ]
          multiplicityVector positiveG a b J I) := by
  rw [distinguishedCoefficient, classification_inverse_coefficient,
    canonical_vacuum_coefficient, matchingIso_vacuum]

variable {K : FullJacobiLatticeModule D N}

/-- Composition on the existing faithful Hom submodule. -/
def targetHomMap (g : ModuleHom J K) : Hom (a+b) J →ₗ[ℂ] Hom (a+b) K where
  toFun f := ⟨g.linearMap.comp f.val, by
    intro h m x
    simp only [LinearMap.comp_apply, f.property h m x, g.intertwines]⟩
  map_add' f f' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change g.linearMap (f.val x + f'.val x) =
      (g.linearMap.comp f.val) x + (g.linearMap.comp f'.val) x
    simp only [LinearMap.comp_apply, map_add]
  map_smul' c f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change g.linearMap (c • f.val x) = c • (g.linearMap.comp f.val) x
    simp only [LinearMap.comp_apply, map_smul, RingHom.id_apply]

theorem forward_natural (g : ModuleHom J K) (f : Hom (a+b) J) :
    forward positiveG a b K (targetHomMap a b J g f) =
      post a b (inverseGram positiveG) g (forward positiveG a b J f) := by
  apply Subtype.ext
  apply fields_ext
  intro s t q
  rfl

/-- Arbitrary original target maps, with independent codomain universe. -/
theorem inverse_natural (g : ModuleHom J K) (I : FullFields positiveG a b J) :
    inverse positiveG a b K (post a b (inverseGram positiveG) g I) =
      targetHomMap a b J g (inverse positiveG a b J I) := by
  apply forward_injective positiveG a b K
  rw [forward_inverse, forward_natural, forward_inverse]

theorem fusionEquiv_natural (g : ModuleHom J K) (f : Hom (a+b) J) :
    fusionEquiv positiveG a b K (targetHomMap a b J g f) =
      post a b (inverseGram positiveG) g (fusionEquiv positiveG a b J f) :=
  forward_natural positiveG a b J g f

theorem fusionEquiv_symm_natural (g : ModuleHom J K) (I : FullFields positiveG a b J) :
    (fusionEquiv positiveG a b K).symm (post a b (inverseGram positiveG) g I) =
      targetHomMap a b J g ((fusionEquiv positiveG a b J).symm I) :=
  inverse_natural positiveG a b J g I

/-- In the additive target the identity gives exactly the normalized canonical field. -/
theorem fusionEquiv_identity :
    fusionEquiv positiveG a b (scalarModule D (a+b))
      (recordEquiv (scalarModule D (a+b)) (scalarModule D (a+b))
        (ModuleHom.id (scalarModule D (a+b)))) = canonical positiveG a b := by
  apply Subtype.ext
  apply fields_ext
  intro s t q
  rfl

theorem fusionEquiv_symm_canonical :
    (fusionEquiv positiveG a b (scalarModule D (a+b))).symm (canonical positiveG a b) =
      recordEquiv (scalarModule D (a+b)) (scalarModule D (a+b))
        (ModuleHom.id (scalarModule D (a+b))) := by
  apply (fusionEquiv positiveG a b (scalarModule D (a+b))).injective
  rw [LinearEquiv.apply_symm_apply, fusionEquiv_identity]

end D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullFusion
