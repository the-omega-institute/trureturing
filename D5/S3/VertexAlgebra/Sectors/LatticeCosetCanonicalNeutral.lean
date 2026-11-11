/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalNeutral
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalNeutral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full charged neutral action preserves every injected dual-coset state. -/

/-
proof_shape: neutral_action_invariance: content;
compressed_neutral: bind-only, consumed by mixed_integer.
escape_witness: The full native charged ground action and polynomial source
recursion identify the actual injected action before projection for every
source and target. The external creation family collapses at neutral charge;
no charge restriction is placed on the original acting state.
consumers: neutral_action_invariance -> compressed_neutral, mixed_integer.
Private neutral_pairing -> neutral_translation, neutral_ground;
neutral_sign -> neutral_ground; neutral_creation_series -> neutral_creation;
neutral_creation -> neutral_ground; neutral_translation -> neutral_ground;
neutral_ground, current_auxiliary -> neutral_action_invariance;
projection_injection -> neutral_action_invariance, compressed_neutral.
These private coefficient, rename and projection transports are consumed
bind-only helpers; the all-state induction is the content witness.
admission_basis: escape-witness.

Classical lattice-field conventions: Bakalov--Kac, math/0402315v1,
section 4.1. Native residue and Sugawara suppliers retain their Scott
Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical
realization, categorical completion or string completion is claimed.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalIntertwiner

/-! The complete neutral action preserves injected dual-coset sectors before projection. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeFiniteNegativeGeneration
open LatticeCosetCompression LatticeCosetInnerExpansion LatticeDiscriminantTheta
open LatticeSugawaraCurrents FieldNormalProduct MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

open private injection_single polynomialProjection_injection from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
open private projection_lift_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetGroundReconstruction
open private derivative_injection compressedField_modes current from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetInnerExpansion
open private mixedState_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation
open private high_modes_finite from D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation

variable (D : LatticeData) {e : ℕ} (B : Matrix (Fin D.rank) (Fin e) ℤ)

private theorem neutral_pairing (d : Fin e → ℤ) (n ell : Charge D) :
    bilinear (ambient D e B 0 zeroSymm zeroEven)
      (liftCharge D B 0 zeroSymm zeroEven 0 n)
      (liftCharge D B 0 zeroSymm zeroEven d ell) =
      bilinear D n ell + ∑ i, n i * Matrix.mulVec B d i := by
  simp only [bilinear, Fin.sum_univ_add, ambient, liftCharge,
    Fin.addCases_left, Fin.addCases_right, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add, Finset.sum_add_distrib]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

private theorem neutral_sign (d : Fin e → ℤ) (n ell : Charge D) :
    epsilon (ambient D e B 0 zeroSymm zeroEven)
      (liftCharge D B 0 zeroSymm zeroEven 0 n)
      (liftCharge D B 0 zeroSymm zeroEven d ell) = epsilon D n ell := by
  classical
  have hne (i : Fin D.rank) (j : Fin e) : ¬ j.natAdd D.rank < i.castAdd e := by
    change ¬ D.rank + (j : ℕ) < (i : ℕ)
    have := i.isLt
    omega
  have hoo (i j : Fin D.rank) : i.castAdd e < j.castAdd e ↔ i < j := Iff.rfl
  unfold epsilon lowerCocycleExponent
  congr 1
  simp [hoo, Finset.sum_filter, Fin.sum_univ_add, halfDiagonal, ambient, liftCharge, hne]

private theorem neutral_creation_series (n : Charge D) :
    PowerSeries.map (polynomialInjection D B 0 zeroSymm zeroEven).toRingHom
      (creationSeries D n) =
      creationSeries (ambient D e B 0 zeroSymm zeroEven)
        (liftCharge D B 0 zeroSymm zeroEven 0 n) := by
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_map]
  by_cases hk : k = 0
  · simp [creationSeries, hk]
  · simp [creationSeries, hk, Fin.sum_univ_add, liftCharge,
      polynomialInjection, map_sum, map_smul]

private theorem neutral_creation (n : Charge D) (k : ℤ) :
    creationCoeff (ambient D e B 0 zeroSymm zeroEven)
      (liftCharge D B 0 zeroSymm zeroEven 0 n) k =
      polynomialInjection D B 0 zeroSymm zeroEven (creationCoeff D n k) := by
  have hA : PowerSeries.constantCoeff (creationSeries D n) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h : PowerSeries.map (polynomialInjection D B 0 zeroSymm zeroEven).toRingHom
      (creationExponential D n) =
      creationExponential (ambient D e B 0 zeroSymm zeroEven)
        (liftCharge D B 0 zeroSymm zeroEven 0 n) := by
    unfold creationExponential
    have hm := PowerSeries.map_subst
      (h := (polynomialInjection D B 0 zeroSymm zeroEven).toRingHom)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hA) (PowerSeries.exp (Oscillator D))
    change PowerSeries.map (polynomialInjection D B 0 zeroSymm zeroEven).toRingHom
      ((PowerSeries.exp (Oscillator D)).subst (creationSeries D n)) =
      (PowerSeries.map (polynomialInjection D B 0 zeroSymm zeroEven).toRingHom
        (PowerSeries.exp (Oscillator D))).subst
        (PowerSeries.map (polynomialInjection D B 0 zeroSymm zeroEven).toRingHom
          (creationSeries D n)) at hm
    rw [hm, PowerSeries.map_exp, neutral_creation_series]
  by_cases hk : k < 0
  · simp [creationCoeff, hk]
  · simpa only [creationCoeff, dite_eq_right hk, PowerSeries.coeff_map,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
      (congrArg (PowerSeries.coeff k.toNat) h).symm

private theorem neutral_translation (n : Charge D) (p : Oscillator D) :
    translatedPolynomial (ambient D e B 0 zeroSymm zeroEven)
      (liftCharge D B 0 zeroSymm zeroEven 0 n)
      (polynomialInjection D B 0 zeroSymm zeroEven p) =
      Polynomial.map (polynomialInjection D B 0 zeroSymm zeroEven).toRingHom
        (translatedPolynomial D n p) := by
  let I := polynomialInjection D B 0 zeroSymm zeroEven
  have h : ((aeval (fun x : Index (ambient D e B 0 zeroSymm zeroEven) =>
      translationVariable _ (liftCharge D B 0 zeroSymm zeroEven 0 n) x.1 x.2)).comp I) =
      (Polynomial.mapAlgHom I).comp (aeval (fun x : Index D => translationVariable D n x.1 x.2)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i,k⟩
    have hu : unitCharge (ambient D e B 0 zeroSymm zeroEven) (i.castAdd e) =
        liftCharge D B 0 zeroSymm zeroEven 0 (unitCharge D i) := by
      funext j
      induction j using Fin.addCases with
      | left j => simp [unitCharge, liftCharge]
      | right j =>
        have hj : j.natAdd D.rank ≠ i.castAdd e := by
          intro h
          have hv := congrArg Fin.val h
          have hi := i.isLt
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
          omega
        simp [unitCharge, liftCharge, hj]
    simp [I, polynomialInjection, translationVariable, hu, neutral_pairing, map_smul]
  exact DFunLike.congr_fun h p

private theorem neutral_ground (d : Fin e → ℤ) (n : Charge D) (v : Carrier D) (m : ℤ) :
    ((Y (ambient D e B 0 zeroSymm zeroEven)
      (injection D B 0 zeroSymm zeroEven 0 (Finsupp.single n 1)))[[m]])
        (injection D B 0 zeroSymm zeroEven d v) =
      injection D B 0 zeroSymm zeroEven d
        (((LatticeDualCosetModule.action D (Matrix.mulVec B d) (Finsupp.single n 1))[[m]]) v) := by
  have he : (((Y (ambient D e B 0 zeroSymm zeroEven)
      (injection D B 0 zeroSymm zeroEven 0 (Finsupp.single n 1)))[[m]])).comp
        (injection D B 0 zeroSymm zeroEven d) =
      (injection D B 0 zeroSymm zeroEven d).comp
        (((LatticeDualCosetModule.action D (Matrix.mulVec B d) (Finsupp.single n 1))[[m]])) := by
    apply Finsupp.lhom_ext
    intro ell p
    classical
    have hinj : Function.Injective (polynomialInjection D B 0 zeroSymm zeroEven) := by
      intro p q hpq
      have := congrArg (polynomialProjection D B 0 zeroSymm zeroEven) hpq
      simpa only [polynomialProjection_injection] using this
    simp only [LinearMap.comp_apply, injection_single, map_one, stateField_ground,
      actualField, VertexOperator.ncoeff_of_coeff]
    rw [(actual_creation_coefficient_transport (ambient D e B 0 zeroSymm zeroEven)
      (liftCharge D B 0 zeroSymm zeroEven 0 n)
      (liftCharge D B 0 zeroSymm zeroEven 0 n)).2.2.1,
      LatticeDualCosetModule.action_ground_coefficients]
    rw [rawSingle, neutral_sign, neutral_translation,
      Polynomial.support_map_of_injective _ hinj]
    simp only [Polynomial.coeff_map, neutral_pairing,
      LatticeDualCosetModule.shiftedRawSingle, map_smul, injection_single, map_sum]
    have hc : liftCharge D B 0 zeroSymm zeroEven 0 n +
        liftCharge D B 0 zeroSymm zeroEven d ell =
        liftCharge D B 0 zeroSymm zeroEven d (n+ell) := by
      funext i
      induction i using Fin.addCases <;> simp [liftCharge]
    rw [hc]
    congr 2
    apply Finset.sum_congr rfl
    intro k hk
    simp only [smul_eq_mul, map_mul, ← neutral_creation]
    congr 2
    omega
  exact DFunLike.congr_fun he v

private theorem projection_injection (d : Fin e → ℤ) (v : Carrier D) :
    projection D B 0 zeroSymm zeroEven d (injection D B 0 zeroSymm zeroEven d v) = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single n p => rw [injection_single, projection_lift_single, polynomialProjection_injection]

open private LatticeDualCosetModule.injection_single compress_modes current_single_lift
  from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule

private theorem current_auxiliary (d : Fin e → ℤ) (i : Fin D.rank) :
    current D B d i = LatticeDualCosetModule.compress D (Matrix.mulVec B d) 1
      (neutralField (LatticeDualCosetModule.auxiliary D (Matrix.mulVec B d)) i.castSucc) := by
  apply HVertexOperator.coeff_inj
  funext k
  apply Finsupp.lhom_ext
  intro n p
  simp only [VertexOperator.coeff_eq_ncoeff, current,
    LatticeDualCosetModule.action_current_coefficients, compress_modes,
    neutralField_ncoeff, current_single_lift, LatticeDualCosetModule.retraction_injection]

/-- Every original state acts within the full injected sector before projection. -/
theorem neutral_action_invariance (hD : (gramReal D).PosDef)
    (d : Fin e → ℤ) (h v : Carrier D) (m : ℤ) :
    ((Y (ambient D e B 0 zeroSymm zeroEven)
      (injection D B 0 zeroSymm zeroEven 0 h))[[m]])
        (injection D B 0 zeroSymm zeroEven d v) =
      injection D B 0 zeroSymm zeroEven d
        (((LatticeDualCosetModule.action D (Matrix.mulVec B d) h)[[m]]) v) := by
  have word (n : Charge D) (w : List (Index D)) :
      compressedField D B 0 zeroSymm zeroEven 0 d
        (Finsupp.single n (w.map (fun x => (X x : Oscillator D))).prod) =
      LatticeDualCosetModule.shiftedWord D (Matrix.mulVec B d) n w := by
    induction w with
    | nil =>
      apply HVertexOperator.coeff_inj
      funext k
      apply LinearMap.ext
      intro g
      simp only [List.map_nil, List.prod_nil, VertexOperator.coeff_eq_ncoeff, compressedField_modes]
      change projection D B 0 zeroSymm zeroEven (0+d) _ = _
      simp only [LinearMap.comp_apply]
      rw [neutral_ground]
      simp only [zero_add, projection_injection]
      change ((LatticeDualCosetModule.compress D (Matrix.mulVec B d) 1
        (Y _ (LatticeDualCosetModule.injection D (Matrix.mulVec B d) 0
          (Finsupp.single n 1))))[[-k-1]]) g = _
      rw [LatticeDualCosetModule.injection_single, map_one, stateField_ground]
      rfl
    | cons x w ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [compressed_multiplication_recursion D B 0 zeroSymm zeroEven hD, ih, current_auxiliary]
      rfl
  have hc (h : Carrier D) : compressedField D B 0 zeroSymm zeroEven 0 d h =
      LatticeDualCosetModule.action D (Matrix.mulVec B d) h := by
    induction h using Finsupp.induction_linear with
    | zero =>
      apply HVertexOperator.coeff_inj
      funext k
      apply LinearMap.ext
      intro g
      simp [VertexOperator.coeff_eq_ncoeff, compressedField_modes, compressed]
    | add h h' hh hh' =>
      apply HVertexOperator.coeff_inj
      funext k
      apply LinearMap.ext
      intro g
      have h1 := congrArg (fun F => HVertexOperator.coeff F k g) hh
      have h2 := congrArg (fun F => HVertexOperator.coeff F k g) hh'
      simp only [VertexOperator.coeff_eq_ncoeff, compressedField_modes] at h1 h2 ⊢
      simpa only [compressed, LinearMap.comp_apply, map_add, Pi.add_apply,
        LinearMap.add_apply] using congrArg₂ (·+·) h1 h2
    | single n p =>
      induction p using MvPolynomial.induction_on' with
      | add p q hp hq =>
        apply HVertexOperator.coeff_inj
        funext k
        apply LinearMap.ext
        intro g
        have hp' := congrArg (fun F => HVertexOperator.coeff F k g) hp
        have hq' := congrArg (fun F => HVertexOperator.coeff F k g) hq
        simp only [VertexOperator.coeff_eq_ncoeff, compressedField_modes] at hp' hq' ⊢
        simpa [compressed, Finsupp.single_add, map_add] using congrArg₂ (·+·) hp' hq'
      | monomial t z =>
        have ht : compressedField D B 0 zeroSymm zeroEven 0 d
            (Finsupp.single n (monomial t 1)) =
            LatticeDualCosetModule.action D (Matrix.mulVec B d)
              (Finsupp.single n (monomial t 1)) := by
          rw [LatticeDualCosetModule.action_monomial, ← occurrences_product, word]
        apply HVertexOperator.coeff_inj
        funext k
        apply LinearMap.ext
        intro g
        have ht' := congrArg (fun F => HVertexOperator.coeff F k g) ht
        simp only [VertexOperator.coeff_eq_ncoeff, compressedField_modes] at ht' ⊢
        have hz : monomial t z = z • (monomial t 1 : Oscillator D) := by
          simp [smul_monomial]
        rw [hz, ← Finsupp.smul_single]
        simpa only [compressed, LinearMap.comp_apply, map_smul, Pi.smul_apply,
          LinearMap.smul_apply, RingHom.id_apply] using congrArg (fun v => z • v) ht'
  rw [LatticeCosetOperatorCorrection.inner_creation_expansion D B 0 zeroSymm zeroEven hD]
  have hz : creationExponential (LatticeCosetCreationSeparation.externalLattice
      (0 : Matrix (Fin e) (Fin e) ℤ) zeroSymm zeroEven) (0 : Fin e → ℤ) = 1 := by
    have hs : creationSeries (LatticeCosetCreationSeparation.externalLattice
        (0 : Matrix (Fin e) (Fin e) ℤ) zeroSymm zeroEven) (0 : Fin e → ℤ) = 0 := by
      ext k
      simp [creationSeries]
    rw [creationExponential, hs, PowerSeries.subst_zero_eq_C_constantCoeff]
    simp
  have hmz : LatticeCosetSeparation.mixedState D B 0 zeroSymm zeroEven d 0 = 0 := by
    apply Finsupp.lhom_ext
    intro n p
    simp [mixedState_single, LatticeCosetSeparation.transversePolynomial]
  rw [finsum_eq_single _ 0]
  · simp only [hz, PowerSeries.coeff_one, ite_true, zero_add, add_zero]
    have hmix : LatticeCosetSeparation.mixedState D B 0 zeroSymm zeroEven d 1 =
        injection D B 0 zeroSymm zeroEven d := by
      apply Finsupp.lhom_ext
      intro n p
      simp [LatticeCosetSeparation.mixedState, injection]
    rw [hmix, ← compressedField_modes, hc]
    simp
  · intro j hj
    simp [hz, PowerSeries.coeff_one, hj, hmz]

/-- Neutral compression is the prescribed dual-coset action. -/
theorem compressed_neutral (hD : (gramReal D).PosDef)
    (d : Fin e → ℤ) (h v : Carrier D) (m : ℤ) :
    compressed D B 0 zeroSymm zeroEven 0 d h m v =
      ((LatticeDualCosetModule.action D (Matrix.mulVec B d) h)[[m]]) v := by
  change projection D B 0 zeroSymm zeroEven (0+d) _ = _
  simp only [LinearMap.comp_apply]
  rw [neutral_action_invariance D B hD, zero_add, projection_injection]

end
end D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner
