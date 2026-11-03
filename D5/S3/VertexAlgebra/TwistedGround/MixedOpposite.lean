/- GID: D5/S3/VertexAlgebra/TwistedGround/MixedOpposite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/MixedOpposite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite source-linear opposite action on the actual fixed restricted dual. -/
import D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
import Batteries.Tactic.OpenPrivate

/-! The opposite source action uses the existing finite source L1 bound.
The full mixed Jacobi identity is not a premise of this construction. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators DirectSum VertexOperator
namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open LatticeHalfFockFiniteCorrection (sourceWeight)
open private originalL0 originalL1 theta_omega_fixed oppositePull
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

private def oppositeTermLinear (D : LatticeData)
    (d m : ℤ) (ell : ℕ) (b : Carrier D) : Carrier D →ₗ[ℂ] Carrier D where
  toFun a := (((-1 : ℂ)^d)/(ell.factorial : ℂ)) •
    ((Y D ((originalL1 D ^ ell) a))[[2*d-(ell : ℤ)-m-2]]) b
  map_add' a c := by simp [map_add, smul_add]
  map_smul' z a := by
    simp only [map_smul, VertexOperator.ncoeff,
      LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

private theorem oppositeTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (d m : ℤ) (a b : Carrier D) :
    Function.HasFiniteSupport (fun ell : ℕ => oppositeTermLinear D d m ell b a) := by
  classical
  let R := a.support.sup (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a c))+1
  apply (Finset.range R).finite_toSet.subset
  intro ell hell
  by_contra outside
  have bound : R ≤ ell := by simpa using outside
  have killed : (originalL1 D ^ R) a = 0 := SourceMobius.actual_sugawara_one_bound D hu a
  have tail : (originalL1 D ^ ell) a = 0 := by
    rw [show ell = (ell-R)+R by omega, pow_add, Module.End.mul_apply, killed, map_zero]
  apply hell
  simp [oppositeTermLinear, tail]

private theorem oppositeMode_finsum (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (a : fixedGrade D d) (e : ℤ) (b : fixedGrade D e) :
    (oppositeMode D hu hD d m a e b).val =
      ∑ᶠ ell : ℕ, oppositeTermLinear D d m ell b.val a.val := by
  classical
  change (∑ ell ∈ Finset.range
    (a.val.support.sup (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c))+1),
      oppositeTermLinear D d m ell b.val a.val) = _
  symm
  apply finsum_eq_sum_of_support_subset
  intro ell hell
  by_contra outside
  let R := a.val.support.sup
    (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c))+1
  have bound : R ≤ ell := by simpa [R] using outside
  have killed : (originalL1 D ^ R) a.val = 0 :=
    SourceMobius.actual_sugawara_one_bound D hu a.val
  have tail : (originalL1 D ^ ell) a.val = 0 := by
    rw [show ell = (ell-R)+R by omega, pow_add, Module.End.mul_apply, killed, map_zero]
  apply hell
  simp [oppositeTermLinear, tail]

private theorem oppositeMode_source_add (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (a c : fixedGrade D d) (e : ℤ) :
    oppositeMode D hu hD d m (a+c) e =
      oppositeMode D hu hD d m a e + oppositeMode D hu hD d m c e := by
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  simp only [LinearMap.add_apply, Submodule.coe_add, oppositeMode_finsum, map_add]
  exact finsum_add_distrib
    (oppositeTerm_finite D hu d m a.val b.val)
    (oppositeTerm_finite D hu d m c.val b.val)

private theorem oppositeMode_source_smul (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (z : ℂ) (a : fixedGrade D d) (e : ℤ) :
    oppositeMode D hu hD d m (z • a) e = z • oppositeMode D hu hD d m a e := by
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  simp only [LinearMap.smul_apply, Submodule.coe_smul, oppositeMode_finsum, map_smul,
    RingHom.id_apply]
  exact (smul_finsum _ _).symm

private theorem oppositeDual_source_add (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (a c : fixedGrade D d) (e : ℤ) :
    oppositeDualMode D hu hD d m (a+c) e =
      oppositeDualMode D hu hD d m a e + oppositeDualMode D hu hD d m c e := by
  ext f b
  change f (oppositePull D hu hD d m (a+c) e b) =
    f (oppositePull D hu hD d m a e b) + f (oppositePull D hu hD d m c e b)
  rw [← map_add]
  congr 1
  apply Subtype.ext
  change (oppositeMode D hu hD d m (a+c) (e+d-m-1) b).val = _
  rw [oppositeMode_source_add]
  rfl

private theorem oppositeDual_source_smul (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (z : ℂ) (a : fixedGrade D d) (e : ℤ) :
    oppositeDualMode D hu hD d m (z • a) e = z • oppositeDualMode D hu hD d m a e := by
  ext f b
  change f (oppositePull D hu hD d m (z • a) e b) = z • f (oppositePull D hu hD d m a e b)
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  change (oppositeMode D hu hD d m (z • a) (e+d-m-1) b).val = _
  rw [oppositeMode_source_smul]
  rfl

/-- Homogeneous opposite action, linear in the actual fixed source and the full
restricted-dual input. Its output degree is E+d-m-1. -/
def oppositeHomogeneous (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) : fixedGrade D d →ₗ[ℂ] Module.End ℂ (FixedRestrictedDual D) where
  toFun a := DirectSum.toModule ℂ ℤ (FixedRestrictedDual D)
    (fun e => (DirectSum.lof ℂ ℤ (fun f => Module.Dual ℂ (fixedGrade D f))
      (e+d-m-1)).comp (oppositeDualMode D hu hD d m a e))
  map_add' a c := by
    apply DirectSum.linearMap_ext
    intro e
    apply LinearMap.ext
    intro f
    simp only [DirectSum.toModule_lof, LinearMap.comp_apply,
      LinearMap.add_comp, LinearMap.add_apply, oppositeDual_source_add, map_add]
  map_smul' z a := by
    apply DirectSum.linearMap_ext
    intro e
    apply LinearMap.ext
    intro f
    simp only [DirectSum.toModule_lof, LinearMap.comp_apply,
      LinearMap.smul_comp, LinearMap.smul_apply, oppositeDual_source_smul, map_smul,
      RingHom.id_apply]

private theorem theta_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (d : ℤ) (v : Carrier D) (hv : v ∈ grade D d) : theta D v ∈ grade D d := by
  let H := (LatticeSugawaraCurrents.gramComplex D)⁻¹
  have hHG := Matrix.nonsing_inv_mul _ (SourceMobius.gram_det_unit D hu)
  have hGH := Matrix.mul_nonsing_inv _ (SourceMobius.gram_det_unit D hu)
  apply (actualL0_eigen_iff_grade D H hHG hGH d _).mp
  have eigen := (actualL0_eigen_iff_grade D H hHG hGH d v).mpr hv
  have hc := stateField_theta D (LatticeActualConformalState.omega D H) v 1
  rw [theta_omega_fixed] at hc
  have modes := LatticeActualConformalState.omega_modes D H 0
  norm_num only at modes
  rw [modes, eigen, map_smul] at hc
  exact hc.symm

private def fixedProjection (D : LatticeData) (hu : IsUnit D.G.det)
    (d : ℤ) : FixedCarrier D →ₗ[ℂ] fixedGrade D d where
  toFun a := ⟨(2 : ℂ)⁻¹ • (gradeProjection D d a.val + theta D (gradeProjection D d a.val)), by
    constructor
    · exact (grade D d).smul_mem _ ((grade D d).add_mem
        (gradeProjection_mem D d a.val) (theta_grade D hu d _ (gradeProjection_mem D d a.val)))
    · apply (mem_fixedSpace D _).mpr
      rw [map_smul, map_add]
      change (2 : ℂ)⁻¹ • (theta D (gradeProjection D d a.val) +
        thetaLinear D (thetaLinear D (gradeProjection D d a.val))) = _
      rw [theta_involutive]
      congr 1
      exact add_comm _ _⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add, smul_add]
    module
  map_smul' z a := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul, smul_add, smul_smul, RingHom.id_apply]
    module

private theorem fixedProjection_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (a : FixedCarrier D) : Function.HasFiniteSupport (fun d => (fixedProjection D hu d a).val) := by
  classical
  apply (stateEnergies D a.val).finite_toSet.subset
  intro d hd
  by_contra outside
  have hz : gradeProjection D d a.val = 0 := by
    apply (carrierCoeffEquiv D).injective
    ext i
    rw [gradeProjection_coeff, map_zero, Finsupp.zero_apply]
    split_ifs with hi
    · by_contra nonzero
      apply outside
      exact Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr nonzero, hi⟩
    · rfl
  apply hd
  change (2 : ℂ)⁻¹ • (gradeProjection D d a.val + theta D (gradeProjection D d a.val)) = 0
  rw [hz, map_zero, add_zero, smul_zero]

private theorem oppositeSource_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m : ℤ) (a : FixedCarrier D) :
    Function.HasFiniteSupport (fun d => oppositeHomogeneous D hu hD d m (fixedProjection D hu d a)) := by
  apply (fixedProjection_finite D hu a).subset
  intro d hd
  by_contra outside
  apply hd
  change oppositeHomogeneous D hu hD d m (fixedProjection D hu d a) = 0
  rw [show fixedProjection D hu d a = 0 from Subtype.ext (not_not.mp outside), map_zero]

/-- The opposite standard mode for an arbitrary actual fixed source. Both
finite homogeneous extension and linearity are proved on the actual carriers. -/
def oppositeAction (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m : ℤ) : FixedCarrier D →ₗ[ℂ] Module.End ℂ (FixedRestrictedDual D) where
  toFun a := ∑ᶠ d : ℤ, oppositeHomogeneous D hu hD d m (fixedProjection D hu d a)
  map_add' a b := by
    simp only [map_add]
    exact finsum_add_distrib (oppositeSource_finite D hu hD m a)
      (oppositeSource_finite D hu hD m b)
  map_smul' z a := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum _ _).symm

private theorem fixedProjection_homogeneous_value (D : LatticeData) (hu : IsUnit D.G.det)
    (d e : ℤ) (a : fixedGrade D d) :
    (fixedProjection D hu e (⟨a.val,a.property.2⟩ : FixedCarrier D)).val =
      if e = d then a.val else 0 := by
  classical
  have projection : gradeProjection D e a.val = if e = d then a.val else 0 := by
    apply (carrierCoeffEquiv D).injective
    ext i
    rw [gradeProjection_coeff]
    by_cases hc : carrierCoeffEquiv D a.val i = 0
    · split_ifs <;> simp_all
    · have energy : energy D i = d := by
        by_contra outside
        exact hc ((mem_grade_iff D d a.val).mp a.property.1 i outside)
      by_cases he : e = d
      · simp [he, energy]
      · simp [he, energy, Ne.symm he]
  change (2 : ℂ)⁻¹ • (gradeProjection D e a.val + theta D (gradeProjection D e a.val)) = _
  rw [projection]
  by_cases he : e = d
  · simp only [if_pos he, (mem_fixedSpace D a.val).mp a.property.2]
    module
  · simp [he]

/-- The full source-linear action extends the original typed opposite map on
every homogeneous fixed source, without choosing new grade coordinates. -/
theorem oppositeAction_homogeneous (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (a : fixedGrade D d) :
    oppositeAction D hu hD m (⟨a.val,a.property.2⟩ : FixedCarrier D) =
      oppositeHomogeneous D hu hD d m a := by
  classical
  change (∑ᶠ e : ℤ, oppositeHomogeneous D hu hD e m
    (fixedProjection D hu e (⟨a.val,a.property.2⟩ : FixedCarrier D))) = _
  rw [finsum_eq_single _ d]
  · have self : fixedProjection D hu d (⟨a.val,a.property.2⟩ : FixedCarrier D) = a := by
      apply Subtype.ext
      simpa using fixedProjection_homogeneous_value D hu d d a
    rw [self]
  · intro e he
    have zero : fixedProjection D hu e (⟨a.val,a.property.2⟩ : FixedCarrier D) = 0 := by
      apply Subtype.ext
      simpa [he] using fixedProjection_homogeneous_value D hu d e a
    rw [zero, map_zero]

private theorem negative_fixed_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d : ℤ) (hd : d < 0) (a : fixedGrade D d) : a = 0 := by
  apply Subtype.ext
  apply (carrierCoeffEquiv D).injective
  ext i
  change (carrierCoeffEquiv D a.val) i = 0
  have positive : 0 ≤ energy D i := by
    have hc := chargeEnergy_nonneg D hD i.1
    change 0 ≤ chargeEnergy D i.1 + (oscillatorEnergy i.2 : ℤ)
    omega
  exact (mem_grade_iff D d a.val).mp a.property.1 i (by omega)

private theorem oppositeHomogeneous_lof_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m e : ℤ) (a : fixedGrade D d) (f : Module.Dual ℂ (fixedGrade D e))
    (hm : e+d-m-1 < 0) :
    oppositeHomogeneous D hu hD d m a
      (DirectSum.lof ℂ ℤ (fun h => Module.Dual ℂ (fixedGrade D h)) e f) = 0 := by
  change DirectSum.toModule ℂ ℤ (FixedRestrictedDual D) _ _ = 0
  rw [DirectSum.toModule_lof]
  have hz : oppositeDualMode D hu hD d m a e f = 0 := by
    ext b
    rw [negative_fixed_zero D hD (e+d-m-1) hm b]
    simp
  rw [LinearMap.comp_apply, hz, map_zero]

private def dualUpper (D : LatticeData) (f : FixedRestrictedDual D) : ℕ := by
  classical
  exact f.support.sup Int.toNat

private def sourceUpper (D : LatticeData) (a : FixedCarrier D) : ℕ :=
  (stateEnergies D a.val).sup Int.toNat

private theorem oppositeHomogeneous_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (a : fixedGrade D d) (f : FixedRestrictedDual D)
    (hm : d + (dualUpper D f : ℤ) < m) :
    oppositeHomogeneous D hu hD d m a f = 0 := by
  classical
  rw [← DirectSum.sum_support_of f, map_sum]
  apply Finset.sum_eq_zero
  intro e he
  have hb : e.toNat ≤ dualUpper D f := Finset.le_sup he
  change oppositeHomogeneous D hu hD d m a
    (DirectSum.lof ℂ ℤ (fun h => Module.Dual ℂ (fixedGrade D h)) e (f e)) = 0
  apply oppositeHomogeneous_lof_zero D hu hD d m e a (f e)
  have he' : e ≤ (e.toNat : ℤ) := by omega
  omega

/-- Explicit all-vector standard-mode truncation of the opposite action.
The bounds use the finite actual source and restricted-dual supports. -/
theorem oppositeAction_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m : ℤ) (a : FixedCarrier D) (f : FixedRestrictedDual D)
    (hm : (sourceUpper D a : ℤ) +
      (dualUpper D f : ℤ) < m) : oppositeAction D hu hD m a f = 0 := by
  classical
  have term (d : ℤ) : oppositeHomogeneous D hu hD d m (fixedProjection D hu d a) f = 0 := by
    by_cases hd : fixedProjection D hu d a = 0
    · rw [hd, map_zero, LinearMap.zero_apply]
    · have member : d ∈ stateEnergies D a.val := by
        by_contra outside
        have hz : gradeProjection D d a.val = 0 := by
          apply (carrierCoeffEquiv D).injective
          ext i
          rw [gradeProjection_coeff, map_zero, Finsupp.zero_apply]
          split_ifs with hi
          · by_contra nonzero
            apply outside
            exact Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr nonzero, hi⟩
          · rfl
        apply hd
        apply Subtype.ext
        change (2 : ℂ)⁻¹ • (gradeProjection D d a.val + theta D (gradeProjection D d a.val)) = 0
        rw [hz, map_zero, add_zero, smul_zero]
      have bound : d.toNat ≤ sourceUpper D a := Finset.le_sup member
      apply oppositeHomogeneous_truncation D hu hD d m _ f
      have hd' : d ≤ (d.toNat : ℤ) := by omega
      omega
  change (∑ᶠ d : ℤ, oppositeHomogeneous D hu hD d m (fixedProjection D hu d a)) f = 0
  change (LinearMap.applyₗ f) (∑ᶠ d : ℤ, oppositeHomogeneous D hu hD d m (fixedProjection D hu d a)) = 0
  rw [map_finsum (LinearMap.applyₗ f) (oppositeSource_finite D hu hD m a)]
  simp only [LinearMap.applyₗ_apply_apply, term, finsum_zero]

/-- An actual opposite formal field on the full fixed restricted dual. -/
def oppositeField (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : FixedCarrier D) :
    VertexOperator ℂ (FixedRestrictedDual D) :=
  HVertexOperator.of_coeff (fun e => oppositeAction D hu hD (-e-1) a) (by
    intro f
    have bound : BddBelow (Function.support (fun e : ℤ => oppositeAction D hu hD (-e-1) a f)) := by
      refine ⟨-((sourceUpper D a : ℤ) +
        (dualUpper D f : ℤ)+2), ?_⟩
      intro e he
      by_contra outside
      exact he (oppositeAction_truncation D hu hD (-e-1) a f (by omega))
    exact bound.isWF.isPWO)

#print axioms oppositeAction_truncation
end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
