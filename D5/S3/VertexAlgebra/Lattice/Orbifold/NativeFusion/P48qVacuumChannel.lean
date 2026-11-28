/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/NativeFusion/P48qVacuumChannel
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vacuum reconstruction of lower-truncated P48q right intertwiners. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion.P48qOppositeVertexInverse
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeSectorHom

/-! The mixed Jacobi identity with the fixed vacuum recovers a fixed-field
module map and determines an integral right intertwiner from that map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion

open scoped BigOperators DirectSum VertexOperator
open P48qFixedSourceBPZ (fixedGrade)
open P48qNativeConformalSector
  (fixedStates fixedField fixedField_conformal_zero fixedOmega fixedProduct fixedVacuum sector)
open P48qNativeFixedRightInsertion (rightInsertion rightInsertion_translation
  rightInsertion_vacuum_coeff sectorTranslation)
open P48qNativeFixedRightJacobi (rightInsertion_borcherds)
open P48qNativeOppositeVacuum (exponent gradeProjection ground)
open P48qNativeRestrictedDualField (GradeDual)
open P48qNativeSectorHom (sectorHomSpace scalarHomEquiv)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private rightMode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
open private fixedGradeInclusion from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation

noncomputable section

local notation "C" => HVertexOperator.coeff

/-- The integral modes of a bilinear right intertwiner on the ground sector. -/
abbrev RightModes := ℤ → sector 0 →ₗ[ℂ] fixedStates →ₗ[ℂ] sector 0

/-- Lower truncation, first-input translation and the mixed Borcherds law,
in the same mode convention as the actual right insertion. -/
structure RightIntertwinerLaws (R : RightModes) : Prop where
  truncation (u : sector 0) (b : fixedStates) : ∃ N : ℤ, ∀ n ≥ N, R n u b = 0
  translation (n : ℤ) (u : sector 0) (b : fixedStates) :
    R n (sectorTranslation 0 u) b = (-(n : ℂ)) • R (n - 1) u b
  jacobi (a b : fixedStates) (u : sector 0) (p q r : ℤ) :
    let left : ℕ → sector 0 := fun i =>
      integerBinomial p i • R (p + q - i) (((fixedField 0 a)[[r + i]]) u) b
    let first : ℕ → sector 0 := fun i =>
      ((-1 : ℂ) ^ i * integerBinomial r i) • ((fixedField 0 a)[[p + r - i]]) (R (q + i) u b)
    let second : ℕ → sector 0 := fun i =>
      ((-1 : ℂ) ^ i * integerBinomial r i) •
        (epsilon r • R (q + r - i) u (fixedProduct a b (p + i)))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
      (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * integerBinomial r i) •
        (((fixedField 0 a)[[p + r - i]]) (R (q + i) u b) -
          epsilon r • R (q + r - i) u (fixedProduct a b (p + i)))

private theorem source_vacuum_nonnegative (a : fixedStates) (n : ℤ) (hn : 0 ≤ n) :
    fixedProduct a fixedVacuum n = 0 :=
  Subtype.ext (LatticeAllStateField.stateField_creativity lattice a.val n hn)

private theorem source_vacuum_creation (a : fixedStates) : fixedProduct a fixedVacuum (-1) = a :=
  Subtype.ext (LatticeAllStateField.stateField_creation lattice a.val)

private theorem binomial_at_zero (p : ℤ) : integerBinomial p 0 = 1 := by
  simp [integerBinomial]

private theorem binomial_zero_of_ne (i : ℕ) (hi : i ≠ 0) : integerBinomial 0 i = 0 := by
  simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem iterate_at_p_zero {R : RightModes} (a : fixedStates) (u : sector 0) (q r : ℤ) :
    (∑ᶠ i : ℕ, integerBinomial 0 i • R (0 + q - i)
        (((fixedField 0 a)[[r + i]]) u) fixedVacuum) =
      R q (((fixedField 0 a)[[r]]) u) fixedVacuum := by
  rw [finsum_eq_single _ 0]
  · simp [binomial_at_zero]
  · intro i hi
    rw [binomial_zero_of_ne i hi, zero_smul]

private theorem vacuum_translation {R : RightModes} (hR : RightIntertwinerLaws R)
    (u : sector 0) (q : ℤ) :
    sectorTranslation 0 (R q u fixedVacuum) = (-(q : ℂ)) • R (q - 1) u fixedVacuum := by
  have h := (hR.jacobi fixedOmega fixedVacuum u 0 q 0).2.2.2
  dsimp only at h
  rw [iterate_at_p_zero, finsum_eq_single _ 0] at h
  · simp only [binomial_at_zero, pow_zero, one_mul, one_smul, Nat.cast_zero, add_zero,
      sub_zero, source_vacuum_nonnegative _ 0 le_rfl, map_zero, smul_zero] at h
    change R q (sectorTranslation 0 u) fixedVacuum =
      sectorTranslation 0 (R q u fixedVacuum) at h
    exact h.symm.trans (hR.translation q u fixedVacuum)
  · intro i hi
    rw [binomial_zero_of_ne i hi, mul_zero, zero_smul]

private theorem vacuum_regular {R : RightModes} (hR : RightIntertwinerLaws R)
    (u : sector 0) (q : ℤ) (hq : 0 ≤ q) : R q u fixedVacuum = 0 := by
  by_contra hne
  have hprop (j : ℕ) : R (q + j) u fixedVacuum ≠ 0 := by
    induction j with
    | zero => simpa using hne
    | succ j ih =>
      intro hz
      have ht := vacuum_translation hR u (q + (j + 1 : ℕ))
      rw [hz, map_zero, show q + ((j + 1 : ℕ) : ℤ) - 1 = q + (j : ℤ) by omega] at ht
      have hscalar : (-(↑(q + ((j + 1 : ℕ) : ℤ)) : ℂ)) ≠ 0 := by
        exact neg_ne_zero.mpr (Int.cast_ne_zero.mpr (by omega))
      exact ih ((smul_eq_zero.mp ht.symm).resolve_left hscalar)
  obtain ⟨N, hN⟩ := hR.truncation u fixedVacuum
  exact hprop (N - q).toNat (hN _ (by omega))

/-- The constant coefficient against the fixed vacuum commutes with every
coefficient of every actual fixed-source field. -/
def vacuumEndpoint (R : RightModes) (hR : RightIntertwinerLaws R) : sectorHomSpace 0 0 :=
  ⟨(R (-1)).flip fixedVacuum, by
    intro a k u
    let r := -k - 1
    have h := (hR.jacobi a fixedVacuum u 0 (-1) r).2.2.2
    dsimp only at h
    rw [iterate_at_p_zero, finsum_eq_single _ 0] at h
    · simp only [binomial_at_zero, pow_zero, one_mul, one_smul, Nat.cast_zero, add_zero,
        zero_add, sub_zero, source_vacuum_nonnegative _ 0 le_rfl, map_zero, smul_zero] at h
      have hk : -r - 1 = k := by dsimp [r]; omega
      change R (-1) (C (fixedField 0 a) (-r - 1) u) fixedVacuum =
        C (fixedField 0 a) (-r - 1) (R (-1) u fixedVacuum) at h
      rw [hk] at h
      exact h
    · intro i hi
      have hi' : 0 ≤ (-1 : ℤ) + (i : ℤ) := by omega
      simp only [zero_add, vacuum_regular hR u _ hi', map_zero,
        source_vacuum_nonnegative _ _ (Int.natCast_nonneg i), smul_zero, sub_zero]⟩

private theorem same_vacuum_coefficients {R S : RightModes}
    (hR : RightIntertwinerLaws R) (hS : RightIntertwinerLaws S)
    (he : vacuumEndpoint R hR = vacuumEndpoint S hS) (u : sector 0) (q : ℤ) :
    R q u fixedVacuum = S q u fixedVacuum := by
  by_cases hq : 0 ≤ q
  · rw [vacuum_regular hR u q hq, vacuum_regular hS u q hq]
  have hneg (j : ℕ) : R (-1 - j) u fixedVacuum = S (-1 - j) u fixedVacuum := by
    induction j with
    | zero =>
      simpa only [Nat.cast_zero, sub_zero, vacuumEndpoint, LinearMap.flip_apply] using
        congrArg (fun f : sectorHomSpace 0 0 => f.val u) he
    | succ j ih =>
      have h := congrArg (sectorTranslation 0) ih
      rw [vacuum_translation hR, vacuum_translation hS] at h
      have hn : (-(↑((-1 : ℤ) - (j : ℤ)) : ℂ)) ≠ 0 :=
        neg_ne_zero.mpr (Int.cast_ne_zero.mpr (by omega))
      rw [show (-1 : ℤ) - (j : ℤ) - 1 = -1 - ((j + 1 : ℕ) : ℤ) by omega] at h
      exact (smul_right_injective _ hn) h
  simpa only [show (-1 : ℤ) - ((-1 - q).toNat : ℤ) = q by omega] using hneg (-1 - q).toNat

private theorem right_eq_of_endpoint {R S : RightModes}
    (hR : RightIntertwinerLaws R) (hS : RightIntertwinerLaws S)
    (he : vacuumEndpoint R hR = vacuumEndpoint S hS) : R = S := by
  funext q
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro b
  have specialize (A : RightModes) (hA : RightIntertwinerLaws A) :
      (∑ᶠ i : ℕ, integerBinomial (-1) i •
        A (-1 + q - i) (((fixedField 0 b)[[(i : ℤ)]]) u) fixedVacuum) =
        ((fixedField 0 b)[[-1]]) (A q u fixedVacuum) - A q u b := by
    have h := (hA.jacobi b fixedVacuum u (-1) q 0).2.2.2
    dsimp only at h
    conv at h =>
      rhs
      rw [finsum_eq_single _ 0 (fun i hi => by
        rw [binomial_zero_of_ne i hi, mul_zero, zero_smul])]
    simpa only [binomial_at_zero, pow_zero, one_mul, one_smul, Nat.cast_zero, add_zero,
      zero_add, sub_zero, epsilon, zpow_zero, source_vacuum_creation] using h
  have hEq : ((fixedField 0 b)[[-1]]) (R q u fixedVacuum) - R q u b =
      ((fixedField 0 b)[[-1]]) (S q u fixedVacuum) - S q u b := by
    rw [← specialize R hR, ← specialize S hS]
    exact finsum_congr fun i => congrArg (integerBinomial (-1) i • ·)
      (same_vacuum_coefficients hR hS he _ _)
  rw [same_vacuum_coefficients hR hS he u q] at hEq
  apply neg_injective
  exact add_left_cancel (by simpa only [sub_eq_add_neg] using hEq)

/-- Precompose the actual right insertion with a map of fixed-source modules. -/
def rightModesFromHom : sectorHomSpace 0 0 →ₗ[ℂ] RightModes where
  toFun f n := (rightMode 0 n).comp f.val
  map_add' f g := by
    funext n
    exact LinearMap.comp_add f.val g.val (rightMode 0 n)
  map_smul' c f := by
    funext n
    exact LinearMap.comp_smul (rightMode 0 n) c f.val

private theorem rightModesFromHom_apply (f : sectorHomSpace 0 0) (n : ℤ)
    (u : sector 0) (a : fixedStates) :
    rightModesFromHom f n u a = (rightInsertion 0 (f.val u) a).coeff (-n - 1) := rfl

private theorem rightModesFromHom_laws (f : sectorHomSpace 0 0) :
    RightIntertwinerLaws (rightModesFromHom f) := by
  constructor
  · intro u b
    let A := rightInsertion 0 (f.val u) b
    refine ⟨-A.order, fun n hn => ?_⟩
    change A.coeff (-n - 1) = 0
    by_contra hz
    have := HahnSeries.order_le_of_coeff_ne_zero hz
    omega
  · intro n u b
    change (rightInsertion 0 (f.val (sectorTranslation 0 u)) b).coeff (-n - 1) = _
    have ht : f.val (sectorTranslation 0 u) = sectorTranslation 0 (f.val u) :=
      f.property fixedOmega (-1) u
    rw [ht, rightInsertion_translation, sub_add_cancel, Int.cast_neg]
    change (-(n : ℂ)) • (rightInsertion 0 (f.val u) b).coeff (-n) =
      (-(n : ℂ)) • (rightInsertion 0 (f.val u) b).coeff (-(n - 1) - 1)
    rw [show -(n - 1) - 1 = -n by omega]
  · intro a b u p q r
    have hcomm (n : ℤ) : f.val (((fixedField 0 a)[[n]]) u) =
        ((fixedField 0 a)[[n]]) (f.val u) := f.property a (-n - 1) u
    simpa only [rightModesFromHom_apply, hcomm]
      using rightInsertion_borcherds 0 a b (f.val u) p q r

private theorem endpoint_fromHom (f : sectorHomSpace 0 0) :
    vacuumEndpoint (rightModesFromHom f) (rightModesFromHom_laws f) = f := by
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  change (rightInsertion 0 (f.val u) fixedVacuum).coeff (-(-1) - 1) = f.val u
  norm_num [rightInsertion_vacuum_coeff, dividedTranslation]

/-- Every lower-truncated integral right intertwiner with the stated laws
is obtained from a unique fixed-source module endomorphism. -/
theorem rightModes_classify (R : RightModes) (hR : RightIntertwinerLaws R) :
    ∃! f : sectorHomSpace 0 0, rightModesFromHom f = R := by
  refine ⟨vacuumEndpoint R hR, ?_, ?_⟩
  · exact right_eq_of_endpoint (rightModesFromHom_laws _) hR (endpoint_fromHom _)
  · intro f hf
    subst R
    exact (endpoint_fromHom f).symm

/-- The submodule of lawful integral right modes has multiplicity one.
Membership in the range is exactly lower truncation, translation and mixed Jacobi. -/
theorem rightModes_multiplicity :
    (∀ R : RightModes, R ∈ LinearMap.range rightModesFromHom ↔ RightIntertwinerLaws R) ∧
      Module.finrank ℂ (LinearMap.range rightModesFromHom) = 1 := by
  constructor
  · intro R
    constructor
    · rintro ⟨f, rfl⟩
      exact rightModesFromHom_laws f
    · intro hR
      obtain ⟨f, hf, _⟩ := rightModes_classify R hR
      exact ⟨f, hf⟩
  · have hinj : Function.Injective rightModesFromHom := by
      intro f g hfg
      obtain ⟨F, _, hunique⟩ := rightModes_classify _ (rightModesFromHom_laws g)
      exact (hunique f hfg).trans (hunique g rfl).symm
    exact (LinearEquiv.ofInjective rightModesFromHom hinj).finrank_eq.symm.trans
      (scalarHomEquiv.finrank_eq.symm.trans (Module.finrank_self ℂ))

/-- The ground readout is the scalar of the fixed-source module map.
This scalar determines every coefficient of an arbitrary lawful right intertwiner. -/
theorem rightModes_ground_scalar (R : RightModes) (hR : RightIntertwinerLaws R) :
    ∃! c : ℂ, R = rightModesFromHom (scalarHomEquiv c) ∧
      R (-1) ground fixedVacuum = c • ground := by
  obtain ⟨f, hf, hUnique⟩ := rightModes_classify R hR
  let c := scalarHomEquiv.symm f
  have hc : scalarHomEquiv c = f := scalarHomEquiv.apply_symm_apply f
  refine ⟨c, ⟨hf.symm.trans (congrArg rightModesFromHom hc.symm), ?_⟩, ?_⟩
  · rw [← hf]
    change (vacuumEndpoint _ (rightModesFromHom_laws f)).val ground = c • ground
    rw [endpoint_fromHom, ← hc]
    rfl
  · intro d hd
    apply scalarHomEquiv.injective
    exact (hUnique _ hd.1.symm).trans hc.symm

/-- The BPZ opposite vertex with the extracted module map recovers the
coefficients of the original right intertwiner on every homogeneous grade. -/
theorem vacuumEndpoint_oppositeVertex_inverse (R : RightModes) (hR : RightIntertwinerLaws R)
    (h : ℤ) (u : sector 0) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (d : ℤ) (a : fixedGrade d) (m : ℤ) :
    let v := (vacuumEndpoint R hR).val u
    (∑ j ∈ Finset.range (((h - 16) / 9).toNat + 1),
      ((-1 : ℂ) ^ j *
        (Complex.exp ((Real.pi : ℂ) * Complex.I * (((h - 9 * (j : ℤ) : ℤ) : ℂ) / 9)))⁻¹) *
        sourcePairing lattice
          (C (oppositeVertex 0 (dividedTranslation (C (fixedField 0 fixedOmega) (-3)) j v))
            (exponent (h - 9 * (j : ℤ)) (-m - (j : ℤ)))
            (DirectSum.lof ℂ ℝ GradeDual w f)).val a.val) =
      f (gradeProjection (w : ℂ) (R (-m - 1) u (fixedGradeInclusion d a)).val) := by
  let F := vacuumEndpoint R hR
  have hM : rightModesFromHom F = R :=
    right_eq_of_endpoint (rightModesFromHom_laws F) hR (endpoint_fromHom F)
  have hu' : C (fixedField 0 fixedOmega) (-2) u = ((h : ℂ) / 9) • u :=
    Subtype.ext ((fixedField_conformal_zero 0 u).trans hu)
  have hF := (F.property fixedOmega (-2) u).symm
  rw [hu', map_smul] at hF
  have hv : totalLZero (F.val u).val = ((h : ℂ) / 9) • (F.val u).val :=
    (fixedField_conformal_zero 0 (F.val u)).symm.trans (congrArg Subtype.val hF)
  dsimp only
  rw [oppositeVertex_inverse 0 h (F.val u) hv w f d a m, ← hM]
  have hindex : -(-m - 1) - 1 = m := by omega
  rw [rightModesFromHom_apply, hindex]

/-- In the BPZ family induced by fixed-source module maps, the ground vacuum
coefficient reads out the scalar with the actual physical phase. -/
theorem oppositeVertex_hom_ground_vacuum (f : sectorHomSpace 0 0) :
    C (oppositeVertex 0 (f.val ground)) (-32 / 9)
      (DirectSum.lof ℂ ℝ GradeDual (16 / 9) groundDual) =
      (scalarHomEquiv.symm f * Complex.exp (16 * (Real.pi : ℂ) * Complex.I / 9)) •
        fixedVacuum := by
  have hf : f.val ground = scalarHomEquiv.symm f • ground := by
    conv_lhs => rw [← scalarHomEquiv.apply_symm_apply f]
    rfl
  rw [hf, map_smul]
  change scalarHomEquiv.symm f • C (oppositeVertex 0 ground) (-32 / 9)
    (DirectSum.lof ℂ ℝ GradeDual (16 / 9) groundDual) = _
  rw [oppositeVertex_ground_vacuum.1, smul_smul]

/-- This physical coefficient separates the BPZ channels induced by fixed-source
module maps. Equality at this coefficient gives equality of the module maps. -/
theorem oppositeVertex_hom_ground_injective :
    Function.Injective (fun f : sectorHomSpace 0 0 =>
      C (oppositeVertex 0 (f.val ground)) (-32 / 9)
        (DirectSum.lof ℂ ℝ GradeDual (16 / 9) groundDual)) := by
  intro f g h
  dsimp only at h
  rw [oppositeVertex_hom_ground_vacuum, oppositeVertex_hom_ground_vacuum] at h
  have hVac : fixedVacuum ≠ 0 := by
    intro hzero
    apply oppositeVertex_ground_vacuum.2
    rw [oppositeVertex_ground_vacuum.1, hzero, smul_zero]
  apply scalarHomEquiv.symm.injective
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) ((smul_left_injective ℂ hVac) h)

#print axioms vacuumEndpoint
#print axioms rightModes_classify
#print axioms rightModes_multiplicity
#print axioms rightModes_ground_scalar
#print axioms vacuumEndpoint_oppositeVertex_inverse
#print axioms oppositeVertex_hom_ground_vacuum
#print axioms oppositeVertex_hom_ground_injective

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion
