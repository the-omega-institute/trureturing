/- SOURCE ONLY: no elaboration, kernel check, or native acceptance was run.
The full VOA/CFT/anomaly/fusion/string/AdS objective remains incomplete.
This consumes the supplied actual unit, finite-duality, braid and twist maps.
Their source-only status is unchanged. Pro advice is untrusted input only.
The scalar is extracted from the actual composite after its full map calculation.
No pivotal comparison, dual twist, hexagon, or analytic trace is asserted.
Attribution and the original cocycle conventions are inherited from the sealed
lattice/module suppliers; ordinary finite trace is Mathlib's LinearMap.trace.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleDuality
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleBalancing
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator Matrix

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonTrace

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open LatticeChargedTransport LatticeActualGeneratorLocality
open LatticeChargedQuotientScalar (carry carry_equation zeroCarry
  representative_zero carry_zero_left carry_zero_right unitCharacter)
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleHom (restrict)
open ActualWeakModuleUniversalField (P PairSector targetModule tag)
open ActualWeakModuleAssociator (F)
open ActualWeakModuleProductNaturality (productHom productHom_pair)
open ActualWeakModuleUnits (I eta0 etaCoefficient etaCoefficient_eta0)
open ActualWeakModuleDuality
open ActualWeakModuleBalancing (theta thetaScalar restrict_theta)

open private shift_pair from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws
open private pairRaw_symm pairRaw_add_right pairRaw_gram_right from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private gram_dot_exponent sign_twice from
  D5.S3.VertexAlgebra.Sectors.LatticeChargedQuotientScalar
open private exp_pi_parity restrict_identity from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence

universe u
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Scalars
variable (hD : (gramReal D).PosDef)

private theorem carry_symm (c d : Discriminant D) :
    carry D hD c d = carry D hD d c := by
  unfold carry
  rw [add_comm]

private theorem opposite_representatives (c : Discriminant D) :
    representative D c + representative D (-c) =
      gramMap D (zeroCarry D hD + carry D hD c (-c)) := by
  rw [map_add, ← representative_zero D hD]
  simpa only [add_neg_cancel] using carry_equation D hD c (-c)

/-- The exact forward phase, including its diagonal sign. -/
private theorem braid_phase_exp (c d : Discriminant D) :
    ActualWeakModuleBraiding.phase c d =
      Complex.exp (Real.pi * Complex.I *
        (pairRaw D (representative D c) (representative D d) : ℂ)) := by
  change Complex.exp (Real.pi * Complex.I *
    (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ)
      (representative D c) (representative D d) : ℂ)) = _
  rw [shift_pair, Matrix.one_mulVec, Matrix.one_mulVec, pairRaw_symm]

private theorem theta_eq_diagonal (c : Discriminant D) :
    thetaScalar c = ActualWeakModuleBraiding.phase c c := by
  change LatticeDiscriminantTheta.phase
    ((pairRaw D (representative D c) (representative D c) / 2 : ℚ) : QmodZ) = _
  rw [phase_mk, braid_phase_exp]
  congr 1
  push_cast
  ring

/-- Literal cap/cup/braid/twist cancellation for the unnormalized section.
The epsilon factors cancel because they agree and are nonzero. The last
integer exponent is even by the original half-diagonal Gram cocycle. -/
theorem ribbon_closure_factor (c : Discriminant D) :
    unitCharacter D hD (-c) * F hD (-c) c (-c) *
      ActualWeakModuleBraiding.phase c (-c) * thetaScalar c = 1 := by
  let m : Charge D := zeroCarry D hD + carry D hD c (-c)
  have hrep : representative D c + representative D (-c) = gramMap D m :=
    opposite_representatives hD c
  have hF : F hD (-c) c (-c) =
      chi D (representative D (-c)) (carry D hD c (-c)) := by
    change LatticeChargedQuotientScalar.associator D hD (-c) c (-c) = _
    simp only [LatticeChargedQuotientScalar.associator, add_neg_cancel,
      neg_add_cancel, carry_zero_left, carry_zero_right]
    rw [carry_symm hD (-c) c]
    exact (div_eq_iff (epsilon_nonzero D _ _)).mpr rfl
  have huF : unitCharacter D hD (-c) * F hD (-c) c (-c) =
      paritySign (representative D (-c) ⬝ᵥ m) := by
    rw [hF]
    change paritySign (representative D (-c) ⬝ᵥ zeroCarry D hD) *
      paritySign (representative D (-c) ⬝ᵥ carry D hD c (-c)) = _
    rw [← paritySign_add]
    simp only [m, dotProduct_add]
  have hRt : ActualWeakModuleBraiding.phase c (-c) * thetaScalar c =
      paritySign (representative D c ⬝ᵥ m) := by
    rw [theta_eq_diagonal, braid_phase_exp, braid_phase_exp, ← Complex.exp_add]
    calc
      _ = Complex.exp (Real.pi * Complex.I *
          (pairRaw D (representative D c)
            (representative D c + representative D (-c)) : ℂ)) := by
        rw [pairRaw_add_right]
        congr 1
        push_cast
        ring
      _ = paritySign (representative D c ⬝ᵥ m) := by
        rw [hrep, pairRaw_gram_right D hD, dotProduct_comm m (representative D c)]
        simpa using exp_pi_parity (representative D c ⬝ᵥ m)
  calc
    _ = (unitCharacter D hD (-c) * F hD (-c) c (-c)) *
        (ActualWeakModuleBraiding.phase c (-c) * thetaScalar c) := by ring
    _ = 1 := by
      rw [huF, hRt, ← paritySign_add, ← add_dotProduct,
        add_comm (representative D (-c)) (representative D c), hrep,
        gram_dot_exponent, ← two_mul, sign_twice]

end Scalars

section Closure
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X)
variable (hD : (gramReal D).PosDef)

/-- A calculation of the final three actual arrows on one cup basis tensor.
Both inverse transports are still present in the input. -/
private theorem ribbon_summand (f : ModuleHom A A) (c : Discriminant D)
    (x : Multiplicity A c) (φ : Module.Dual ℂ (Multiplicity A c)) (v : Carrier D) :
    F hD (-c) c (-c) • (evaluation A hD).linearMap
      (ActualWeakModuleBraiding.braid A (dualModule A)
        ((productHom hD ((theta A hD).hom.comp f)
          (ModuleHom.id (dualModule A))).linearMap
            (DirectSum.lof ℂ _ (PairSector A (dualModule A)) (c,-c)
              (transportInverse D (representative D 0) (carry D hD c (-c))
                (transportInverse D 0 (zeroCarry D hD) v) ⊗ₜ[ℂ]
                  (x ⊗ₜ[ℂ] dualIota A c φ))))) =
      φ (restrict f c x) • v := by
  have hr : restrict ((theta A hD).hom.comp f) c x =
      thetaScalar c • restrict f c x := by
    have hc : restrict ((theta A hD).hom.comp f) c x =
        restrict (theta A hD).hom c (restrict f c x) := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    rw [hc, restrict_theta]
  rw [productHom_pair, TensorProduct.map_tmul, hr, restrict_identity]
  change F hD (-c) c (-c) • (evaluation A hD).linearMap
    (ActualWeakModuleBraiding.braid A (dualModule A)
      (tag A (dualModule A) c (-c) (thetaScalar c • restrict f c x)
        (dualIota A c φ)
        (transportInverse D (representative D 0) (carry D hD c (-c))
          (transportInverse D 0 (zeroCarry D hD) v)))) = _
  rw [ActualWeakModuleBraiding.braid_tag, map_smul, evaluation_pair]
  have hc := LinearMap.congr_fun
    (transportInverse_right D (representative D 0) (carry D hD c (-c)))
      (transportInverse D 0 (zeroCarry D hD) v)
  have h0 := LinearMap.congr_fun (transportInverse_right D 0 (zeroCarry D hD)) v
  dsimp only [LinearMap.comp_apply, LinearMap.id_apply] at hc h0
  rw [carry_symm hD (-c) c, hc, h0]
  simp only [map_smul, smul_eq_mul, smul_smul]
  calc
    _ = (unitCharacter D hD (-c) * F hD (-c) c (-c) *
        ActualWeakModuleBraiding.phase c (-c) * thetaScalar c *
          φ (restrict f c x)) • v := by
      congr 1
      ring
    _ = _ := by rw [ribbon_closure_factor, one_mul]

variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]

/-- The literal original ModuleHom composite; both braid and theta are forward. -/
def ribbonClosure (f : ModuleHom A A) : ModuleHom (I D) (I D) :=
  (evaluation A hD).comp
    ((ActualWeakModuleBraiding.braidIso A (dualModule A)).hom.comp
      ((productHom hD ((theta A hD).hom.comp f)
        (ModuleHom.id (dualModule A))).comp (coevaluation A hD)))

private theorem ribbonClosure_apply_aux (f : ModuleHom A A) (v : Carrier D) :
    (ribbonClosure A hD f).linearMap v =
      (∑ c ∈ discriminantSupport hD,
        LinearMap.trace ℂ (Multiplicity A c) (restrict f c)) • v := by
  classical
  change (evaluation A hD).linearMap
    (ActualWeakModuleBraiding.braid A (dualModule A)
      ((productHom hD ((theta A hD).hom.comp f)
        (ModuleHom.id (dualModule A))).linearMap
          ((coevaluation A hD).linearMap v))) = _
  rw [coevaluation_carrier]
  simp only [map_sum, map_smul]
  calc
    _ = ∑ c ∈ discriminantSupport hD,
        ∑ i : Module.Basis.ofVectorSpaceIndex ℂ (Multiplicity A c),
          (Module.Basis.ofVectorSpace ℂ (Multiplicity A c)).coord i
            (restrict f c (Module.Basis.ofVectorSpace ℂ (Multiplicity A c) i)) • v := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [cupTensor_basis]
      simp only [TensorProduct.tmul_sum, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact ribbon_summand A hD f c _ _ v
    _ = ∑ c ∈ discriminantSupport hD,
        LinearMap.trace ℂ (Multiplicity A c) (restrict f c) • v := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_smul]
      congr 1
      symm
      rw [LinearMap.trace_eq_matrix_trace ℂ
        (Module.Basis.ofVectorSpace ℂ (Multiplicity A c))]
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
        Module.Basis.coord_apply]
    _ = _ := by rw [Finset.sum_smul]

/-- Principal consumer: equality of the FULL underlying linear maps on the
original unit carrier. Only the actual multiplicity spaces are finite. -/
theorem ribbonClosure_linearMap (f : ModuleHom A A) :
    (ribbonClosure A hD f).linearMap =
      (∑ c ∈ discriminantSupport hD,
        LinearMap.trace ℂ (Multiplicity A c) (restrict f c)) •
          (LinearMap.id : Carrier D →ₗ[ℂ] Carrier D) := by
  apply LinearMap.ext
  intro v
  exact ribbonClosure_apply_aux A hD f v

/-- Readback at every original charge/oscillator vector, including zero. -/
theorem ribbonClosure_apply (f : ModuleHom A A) (v : Carrier D) :
    (ribbonClosure A hD f).linearMap v =
      (∑ c ∈ discriminantSupport hD,
        LinearMap.trace ℂ (Multiplicity A c) (restrict f c)) • v := by
  simpa only [LinearMap.smul_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (ribbonClosure_linearMap A hD f) v

/-- Extracted from the actual closure at the actual eta0 = [zeroCarry]1. -/
def ribbonTrace (f : ModuleHom A A) : ℂ :=
  etaCoefficient hD (restrict (ribbonClosure A hD f) 0 (eta0 hD))

theorem ribbonTrace_eq_sum (f : ModuleHom A A) :
    ribbonTrace A hD f =
      ∑ c ∈ discriminantSupport hD,
        LinearMap.trace ℂ (Multiplicity A c) (restrict f c) := by
  have hr : restrict (ribbonClosure A hD f) 0 (eta0 hD) =
      (∑ c ∈ discriminantSupport hD,
        LinearMap.trace ℂ (Multiplicity A c) (restrict f c)) • eta0 hD := by
    apply Subtype.ext
    apply Subtype.ext
    change (ribbonClosure A hD f).linearMap (eta0 hD).val.val = _
    exact ribbonClosure_apply A hD f (eta0 hD).val.val
  unfold ribbonTrace
  rw [hr, map_smul, etaCoefficient_eta0, smul_eq_mul, mul_one]

end Closure
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonTrace
