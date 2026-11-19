/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual conformal translation and both full rational Hahn derivative laws. -/

/-
proof_shape: projection_translation, translation_injection,
source_derivative, target_derivative: content.
escape_witness: Projection intertwines literal conformal translation on the
FULL ambient carrier, including all external-charge fibers. Injected source
translation retains its transverse summand. Native normal ordering gives
the source correction +schur(b,a), while moving a transverse input across
the field gives -schur(a,b). These exact signs produce the rational-mode
derivative coefficient, with off-coset modes zero in each family.
consumers: projection_translation -> target_derivative_integer;
translation_injection -> source_derivative_integer, target_derivative_integer;
source_derivative, target_derivative -> LatticeDualCosetFusion.canonical_lawful.
Private momentum_dual -> projection_translation, translation_injection;
projection_derivation, projection_charge -> projection_translation;
injection_derivation, injected_charge -> translation_injection;
transverseField_negative, transverseField_injection -> transverse_source;
transverse_partial_injection -> transverseField_injection;
transverse_source, multiply_transverseCharge -> source_transverseCharge;
source_transverseCharge -> source_derivative_integer;
target_transverseCharge -> target_derivative_integer;
shift_pair -> shift_symmetric, LatticeDualCosetFusion.shift_eq_groundPower;
shift_symmetric -> source_derivative_integer;
schur_shift -> source_derivative_integer, target_derivative_integer;
source_derivative_integer -> source_derivative;
target_derivative_integer -> target_derivative.
The inverse-pair and scalar normalization helpers are bind-only; the
arbitrary-polynomial derivation and transverse-mode inductions carry content.
admission_basis: escape-witness.

Classical lattice-field conventions: Bakalov--Kac, math/0402315v1,
section 4.1. Native residue and Sugawara suppliers retain their Scott
Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical
realization, categorical completion or string completion is claimed.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalJacobi

/-! Actual conformal translations and both derivative laws for the complete rational Hahn field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeFiniteNegativeGeneration
open LatticeCosetCompression LatticeCosetTransverse LatticeCosetSeparation
open LatticeCosetProjectedAction LatticeCosetInnerExpansion LatticeDiscriminantTheta
open LatticeSugawaraConformal LatticeDualCosetConformal MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

open private gram_longitudinal_complex injection_single projection_single from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression

variable (D : LatticeData) {e : ℕ} (B : Matrix (Fin D.rank) (Fin e) ℤ)

/-- The actual fractional longitudinal momentum of an external sector. -/
def momentum (d : Fin e → ℤ) (i : Fin D.rank) : ℂ :=
  ∑ j, (longitudinal D B i j : ℂ) * (d j : ℂ)

private theorem momentum_dual (hD : (gramReal D).PosDef) (d : Fin e → ℤ)
    (i : Fin D.rank) :
    ∑ k, (D.G i k : ℂ) * momentum D B d k = ((Matrix.mulVec B d i : ℤ) : ℂ) := by
  simp only [momentum, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, gram_longitudinal_complex D B hD]
  simp [Matrix.mulVec, dotProduct]

private theorem projection_derivation
    (p : Oscillator (ambient D e B 0 zeroSymm zeroEven)) :
    polynomialProjection D B 0 zeroSymm zeroEven
      (oscillatorDerivation (ambient D e B 0 zeroSymm zeroEven) p) =
    oscillatorDerivation D (polynomialProjection D B 0 zeroSymm zeroEven p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C z => simp [oscillatorDerivation, polynomialProjection]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    have hx : polynomialProjection D B 0 zeroSymm zeroEven
        (oscillatorDerivation (ambient D e B 0 zeroSymm zeroEven) (X x)) =
        oscillatorDerivation D (polynomialProjection D B 0 zeroSymm zeroEven (X x)) := by
      rcases x with ⟨j,k⟩
      induction j using Fin.addCases with
      | left i => simp [oscillatorDerivation, polynomialProjection, projectionVariable]
      | right j =>
        simp [oscillatorDerivation, polynomialProjection, projectionVariable,
          Finset.smul_sum, smul_smul, mul_comm]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hx]

private theorem injection_derivation (p : Oscillator D) :
    oscillatorDerivation (ambient D e B 0 zeroSymm zeroEven)
        (polynomialInjection D B 0 zeroSymm zeroEven p) =
      polynomialInjection D B 0 zeroSymm zeroEven (oscillatorDerivation D p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C z => simp [oscillatorDerivation, polynomialInjection]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    have hx : oscillatorDerivation (ambient D e B 0 zeroSymm zeroEven)
        (polynomialInjection D B 0 zeroSymm zeroEven (X x)) =
        polynomialInjection D B 0 zeroSymm zeroEven (oscillatorDerivation D (X x)) := by
      simp [oscillatorDerivation, polynomialInjection]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hx]

private theorem projection_charge
    (n : Charge (ambient D e B 0 zeroSymm zeroEven)) :
    polynomialProjection D B 0 zeroSymm zeroEven
        (chargePolynomial (ambient D e B 0 zeroSymm zeroEven) n) =
      ∑ i, ((oldCharge D B 0 zeroSymm zeroEven n i : ℂ) +
        momentum D B (externalCharge D B 0 zeroSymm zeroEven n) i) • X (i,0) := by
  classical
  unfold chargePolynomial
  change polynomialProjection D B 0 zeroSymm zeroEven
    (∑ j : Fin (D.rank+e), _) = _
  rw [Fin.sum_univ_add]
  simp only [map_add, map_sum, map_smul, polynomialProjection, aeval_X,
    projectionVariable, Fin.addCases_left, Fin.addCases_right, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin e)))]
  simp only [momentum, oldCharge, externalCharge, add_smul, Finset.sum_add_distrib,
    Finset.sum_smul, mul_comm]

/-- Compression intertwines the literal conformal translation on every ambient state. -/
theorem projection_translation (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (d : Fin e → ℤ) (v : Carrier (ambient D e B 0 zeroSymm zeroEven)) :
    projection D B 0 zeroSymm zeroEven d
        (translation (ambient D e B 0 zeroSymm zeroEven) v) =
      moduleL D (Matrix.mulVec B d) H (-1)
        (projection D B 0 zeroSymm zeroEven d v) := by
  have he : (projection D B 0 zeroSymm zeroEven d).comp
      (translation (ambient D e B 0 zeroSymm zeroEven)) =
      (moduleL D (Matrix.mulVec B d) H (-1)).comp
        (projection D B 0 zeroSymm zeroEven d) := by
    apply Finsupp.lhom_ext
    intro n p
    simp only [LinearMap.comp_apply, translation_single, projection_single]
    by_cases hn : externalCharge D B 0 zeroSymm zeroEven n = d
    · simp only [hn, ↓reduceIte]
      rw [moduleL_minus_one_single D (Matrix.mulVec B d) H hHG hGH
        (momentum D B d) (momentum_dual D B hD d)]
      rw [map_add, map_mul, projection_derivation, projection_charge, hn]
    · simp [hn]
  exact DFunLike.congr_fun he v

/-- The transverse charge oscillator appearing in ambient translation. -/
def transverseCharge (d : Fin e → ℤ) :
    Oscillator (ambient D e B 0 zeroSymm zeroEven) :=
  ∑ j, (d j : ℂ) • transverse D B 0 zeroSymm zeroEven j 0

private theorem injected_charge (d : Fin e → ℤ) (n : Charge D) :
    chargePolynomial (ambient D e B 0 zeroSymm zeroEven)
        (liftCharge D B 0 zeroSymm zeroEven d n) =
      polynomialInjection D B 0 zeroSymm zeroEven
        (∑ i, ((n i : ℂ)+momentum D B d i) • X (i,0)) + transverseCharge D B d := by
  classical
  unfold chargePolynomial
  change (∑ j : Fin (D.rank+e), _) = _
  rw [Fin.sum_univ_add]
  simp only [liftCharge, Fin.addCases_left, Fin.addCases_right, map_sum, map_smul,
    polynomialInjection, rename_X, transverseCharge, transverse, smul_sub,
    Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib,
    momentum, Finset.sum_smul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin D.rank)))]
  simp only [map_add, map_sum, map_smul, rename_X, mul_comm]
  abel

open private multiply_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation

/-- Ambient translation of every injected source retains its transverse summand. -/
theorem translation_injection (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (d : Fin e → ℤ) (v : Carrier D) :
    translation (ambient D e B 0 zeroSymm zeroEven)
        (injection D B 0 zeroSymm zeroEven d v) =
      injection D B 0 zeroSymm zeroEven d (moduleL D (Matrix.mulVec B d) H (-1) v) +
      multiply _ (transverseCharge D B d) (injection D B 0 zeroSymm zeroEven d v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]; abel
  | single n p =>
    rw [injection_single, translation_single, moduleL_minus_one_single D (Matrix.mulVec B d)
      H hHG hGH (momentum D B d) (momentum_dual D B hD d), injection_single,
      multiply_single, injection_derivation, injected_charge]
    simp only [map_add, map_mul, add_mul, Finsupp.single_add]
    abel

open LatticeSugawaraCurrents FieldNormalProduct
open private transverse_pairing schur_eq_pair from D5.S3.VertexAlgebra.Sectors.LatticeCosetTransverse
open private projection_transverse_mul polynomialMode_monomial from D5.S3.VertexAlgebra.Sectors.LatticeCosetProjectedAction
open private high_modes_finite from D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation

private def transverseField (j : Fin e) :
    VertexOperator ℂ (Carrier (ambient D e B 0 zeroSymm zeroEven)) :=
  neutralField (ambient D e B 0 zeroSymm zeroEven) (j.natAdd D.rank) -
    ∑ i, (longitudinal D B i j : ℂ) •
      neutralField (ambient D e B 0 zeroSymm zeroEven) (i.castAdd e)

private theorem transverseField_negative (j : Fin e) (m : ℤ) (hm : m < 0)
    (v : Carrier (ambient D e B 0 zeroSymm zeroEven)) :
    ((transverseField D B j)[[m]]) v =
      multiply _ (transverse D B 0 zeroSymm zeroEven j (-m-1).toNat) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single n p =>
    simp [transverseField, neutralField_ncoeff, neutralMode_single,
      neutralPolynomialMode, hm, multiply_single, transverse, sub_mul,
      Finset.sum_mul, smul_mul_assoc, Finsupp.single_sub, Finsupp.single_finsetSum,
      Finsupp.smul_single]

private theorem transverse_partial_injection (hD : (gramReal D).PosDef)
    (j : Fin e) (r : ℕ) (p : Oscillator D) :
    weightedPartial (ambient D e B 0 zeroSymm zeroEven) (j.natAdd D.rank) r
        (polynomialInjection D B 0 zeroSymm zeroEven p) =
      ∑ i, (longitudinal D B i j : ℂ) •
        weightedPartial (ambient D e B 0 zeroSymm zeroEven) (i.castAdd e) r
          (polynomialInjection D B 0 zeroSymm zeroEven p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C z => simp [weightedPartial, polynomialInjection]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p x hp =>
    have hx : weightedPartial (ambient D e B 0 zeroSymm zeroEven) (j.natAdd D.rank) r
        (polynomialInjection D B 0 zeroSymm zeroEven (X x)) =
        ∑ i, (longitudinal D B i j : ℂ) •
          weightedPartial (ambient D e B 0 zeroSymm zeroEven) (i.castAdd e) r
            (polynomialInjection D B 0 zeroSymm zeroEven (X x)) := by
      rcases x with ⟨i,k⟩
      rw [show polynomialInjection D B 0 zeroSymm zeroEven (X (i,k)) =
        X (i.castAdd e,k) from (by simp [polynomialInjection])]
      rw [LatticeActualAnnihilation.annihilate_X (ambient D e B 0 zeroSymm zeroEven)
        (j.natAdd D.rank) (i.castAdd e) r k]
      simp_rw [LatticeActualAnnihilation.annihilate_X (ambient D e B 0 zeroSymm zeroEven)]
      by_cases hr : r = k
      · simp only [hr, ↓reduceIte, ambient, Fin.addCases_left, Fin.addCases_right,
          smul_smul, ← Finset.sum_smul]
        congr 1
        simpa only [D.symmetric, mul_comm] using
          (gram_longitudinal_complex D B hD i j).symm
      · simp [hr]
    simp only [map_mul, LatticeActualAnnihilation.annihilate_mul, hp, hx,
      smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm]

private theorem transverseField_injection (hD : (gramReal D).PosDef)
    (d : Fin e → ℤ) (j : Fin e) (m : ℤ) (hm : 0 ≤ m) (v : Carrier D) :
    ((transverseField D B j)[[m]]) (injection D B 0 zeroSymm zeroEven d v) =
      if m = 0 then (transversePair D B 0 d j : ℂ) •
        injection D B 0 zeroSymm zeroEven d v else 0 := by
  have he : (((transverseField D B j)[[m]])).comp
      (injection D B 0 zeroSymm zeroEven d) =
      (if m = 0 then (transversePair D B 0 d j : ℂ) •
        injection D B 0 zeroSymm zeroEven d else 0) := by
    apply Finsupp.lhom_ext
    intro n p
    simp only [LinearMap.comp_apply, injection_single]
    by_cases hz : m = 0
    · subst m
      have hp : (bilinear (ambient D e B 0 zeroSymm zeroEven)
          (unitCharge _ (j.natAdd D.rank))
          (liftCharge D B 0 zeroSymm zeroEven d n) : ℂ) -
          ∑ i, (longitudinal D B i j : ℂ) *
            (bilinear (ambient D e B 0 zeroSymm zeroEven)
              (unitCharge _ (i.castAdd e))
              (liftCharge D B 0 zeroSymm zeroEven d n) : ℂ) =
            (transversePair D B 0 d j : ℂ) := by
        have hq := transverse_pairing D B 0 zeroSymm zeroEven hD d n j
        simp_rw [bilinear_symmetric (ambient D e B 0 zeroSymm zeroEven)
          (liftCharge D B 0 zeroSymm zeroEven d n)] at hq
        exact_mod_cast hq
      simp only [transverseField, map_sub, map_sum, map_smul, Pi.sub_apply, Finset.sum_apply,
        Pi.smul_apply, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        neutralField_ncoeff, neutralMode_single, neutralPolynomialMode, LinearMap.id_apply, lt_self_iff_false,
        ↓reduceIte, Finsupp.smul_single, ← Finsupp.single_finsetSum, ← Finsupp.single_sub,
        smul_smul, ← Finset.sum_smul, ← sub_smul]
      rw [hp]
      simp only [injection_single, Finsupp.smul_single]
    · have hmode (i : Fin (D.rank+e)) :
          neutralMode (ambient D e B 0 zeroSymm zeroEven) i m
            (Finsupp.single (liftCharge D B 0 zeroSymm zeroEven d n)
              (polynomialInjection D B 0 zeroSymm zeroEven p)) =
          Finsupp.single (liftCharge D B 0 zeroSymm zeroEven d n)
            ((m : ℂ) • weightedPartial (ambient D e B 0 zeroSymm zeroEven) i
              (m-1).toNat (polynomialInjection D B 0 zeroSymm zeroEven p)) := by
        rw [neutralMode_single]
        have hmEq : m = ((m-1).toNat : ℤ)+1 := by omega
        have hpEq := neutralPolynomialMode_positive (ambient D e B 0 zeroSymm zeroEven)
          i (liftCharge D B 0 zeroSymm zeroEven d n) (m-1).toNat
        rw [← hmEq] at hpEq
        rw [hpEq, LinearMap.smul_apply]
        congr 2
        exact_mod_cast hmEq.symm
      simp only [transverseField, map_sub, map_sum, map_smul, Pi.sub_apply,
        Finset.sum_apply, Pi.smul_apply, LinearMap.sub_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, neutralField_ncoeff]
      simp only [hmode, hz, ↓reduceIte, LinearMap.zero_apply]
      rw [transverse_partial_injection D B hD]
      simp only [Finset.smul_sum, Finsupp.single_finsetSum, Finsupp.smul_single,
        smul_comm (m : ℂ), sub_self]
  by_cases hz : m = 0 <;> simpa [hz] using DFunLike.congr_fun he v

private theorem transverse_source (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (u v : Carrier D) (j : Fin e) (m : ℤ) :
    projection D B 0 zeroSymm zeroEven (a+b)
      (((Y (ambient D e B 0 zeroSymm zeroEven)
        (multiply _ (transverse D B 0 zeroSymm zeroEven j 0)
          (injection D B 0 zeroSymm zeroEven a u)))[[m]])
        (injection D B 0 zeroSymm zeroEven b v)) =
      (transversePair D B 0 b j : ℂ) •
        compressed D B 0 zeroSymm zeroEven a b u (m-1) v := by
  let E := ambient D e B 0 zeroSymm zeroEven
  let U := injection D B 0 zeroSymm zeroEven a u
  let V := injection D B 0 zeroSymm zeroEven b v
  let P := projection D B 0 zeroSymm zeroEven (a+b)
  have hy : Y E (Finsupp.single (0 : Charge E) (transverse D B 0 zeroSymm zeroEven j 0)) =
      transverseField D B j := by
    have hcurr (i : Fin E.rank) : Y E (Finsupp.single 0 (X (i,0))) = neutralField E i :=
      LatticeActualConformalState.current_state_field E i
    simp [transverse, Finsupp.single_sub, Finsupp.single_finsetSum,
      ← Finsupp.smul_single, map_sub, map_sum, map_smul, hcurr, transverseField]
    rfl
  have hrec : Y E (multiply E (transverse D B 0 zeroSymm zeroEven j 0) U) =
      (normalMinusOne (transverseField D B j) (Y E U)).1 := by
    have h := LatticeActualStateFieldCalculus.minus_one_product_field E
      (Finsupp.single 0 (transverse D B 0 zeroSymm zeroEven j 0)) U
    change Y E (((Y E _)[[-1]]) U) = _ at h
    rw [hy, transverseField_negative D B j (-1) (by norm_num)] at h
    simpa using h
  change P (((Y E (multiply E _ U))[[m]]) V) = _
  rw [hrec, (normalMinusOne _ _).2, map_add,
    map_finsum P (high_modes_finite (Y E U)
      (fun k => ((transverseField D B j)[[-(k : ℤ)-1]])) m V),
    map_finsum P (by simpa only [zero_add] using
      high_modes_finite (transverseField D B j) (fun k => (Y E U)[[m-k-1]]) 0 V)]
  have hfirst (k : ℕ) : P (((transverseField D B j)[[-(k : ℤ)-1]])
      (((Y E U)[[m+k]]) V)) = 0 := by
    rw [transverseField_negative D B j _ (by omega)]
    exact projection_transverse_mul D B 0 zeroSymm zeroEven (a+b) j _ _
  rw [finsum_eq_zero_of_forall_eq_zero hfirst, zero_add, finsum_eq_single _ 0]
  · simp only [Nat.cast_zero, sub_zero]
    dsimp only [V]
    rw [transverseField_injection D B hD b j 0 (by omega), if_pos rfl,
      map_smul, map_smul]
    rfl
  · intro k hk
    rw [transverseField_injection D B hD b j k (by positivity),
      ite_eq_right (by exact_mod_cast hk), map_zero, map_zero]

private theorem multiply_transverseCharge (d : Fin e → ℤ)
    (v : Carrier (ambient D e B 0 zeroSymm zeroEven)) :
    multiply _ (transverseCharge D B d) v =
      ∑ j, (d j : ℂ) • multiply _ (transverse D B 0 zeroSymm zeroEven j 0) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, smul_add, Finset.sum_add_distrib]
  | single n p => simp [multiply_single, transverseCharge, Finset.sum_mul,
      smul_mul_assoc, Finsupp.smul_single, Finsupp.single_finsetSum]

private theorem source_transverseCharge (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (u v : Carrier D) (m : ℤ) :
    projection D B 0 zeroSymm zeroEven (a+b)
      (((Y (ambient D e B 0 zeroSymm zeroEven)
        (multiply _ (transverseCharge D B a) (injection D B 0 zeroSymm zeroEven a u)))[[m]])
        (injection D B 0 zeroSymm zeroEven b v)) =
      (schur D B 0 b a : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v := by
  rw [multiply_transverseCharge]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [transverse_source D B hD, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  exact_mod_cast (schur_eq_pair D B 0 b a).symm


open private pairRaw_symm from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

private theorem shift_pair (a b : Fin e → ℤ) :
    shift D B a b = pairRaw D (Matrix.mulVec B b) (Matrix.mulVec B a) := by
  have hv (d : Fin e → ℤ) : dualVector D (Matrix.mulVec B d) =
      Matrix.mulVec (longitudinal D B) (fun j => (d j : ℚ)) := by
    unfold dualVector longitudinal
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  simp only [shift, pairRaw, hv, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem shift_symmetric (a b : Fin e → ℤ) : shift D B a b = shift D B b a := by
  rw [shift_pair, shift_pair, pairRaw_symm]

private theorem schur_shift (a b : Fin e → ℤ) : schur D B 0 a b = -shift D B a b := by
  simp [schur, shift, mul_neg, neg_mul]

private theorem target_transverseCharge (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (u v : Carrier D) (m : ℤ) :
    projection D B 0 zeroSymm zeroEven (a+b)
      (((Y (ambient D e B 0 zeroSymm zeroEven)
        (injection D B 0 zeroSymm zeroEven a u))[[m]])
        (multiply _ (transverseCharge D B b) (injection D B 0 zeroSymm zeroEven b v))) =
      -(schur D B 0 a b : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v := by
  classical
  have hj (j : Fin e) : projection D B 0 zeroSymm zeroEven (a+b)
      (((Y (ambient D e B 0 zeroSymm zeroEven)
        (injection D B 0 zeroSymm zeroEven a u))[[m]])
        (multiply _ (transverse D B 0 zeroSymm zeroEven j 0)
          (injection D B 0 zeroSymm zeroEven b v))) =
      -(transversePair D B 0 a j : ℂ) •
        compressed D B 0 zeroSymm zeroEven a b u (m-1) v := by
    have h := projected_transverse_polynomial D B 0 zeroSymm zeroEven hD a (a+b) u
      (X (j,0)) m (injection D B 0 zeroSymm zeroEven b v)
    simp only [transversePolynomial, aeval_X, scalarTranslation, Nat.zero_add] at h
    rw [show -Polynomial.C (transversePair D B 0 a j : ℂ) * Polynomial.X^1 =
      Polynomial.monomial 1 (-(transversePair D B 0 a j : ℂ)) by
        rw [← map_neg, Polynomial.C_mul_X_pow_eq_monomial],
      polynomialMode_monomial] at h
    exact h
  rw [multiply_transverseCharge]
  simp only [map_sum, map_smul]
  simp_rw [hj, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  rw [schur_eq_pair]
  push_cast
  simp [mul_neg, Finset.sum_neg_distrib]

/-- Actual source translation differentiates the integer compressed modes. -/
private theorem source_derivative_integer (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Fin e → ℤ) (u v : Carrier D) (m : ℤ) :
    compressed D B 0 zeroSymm zeroEven a b
      (moduleL D (Matrix.mulVec B a) H (-1) u) m v =
      -(((m : ℚ)-shift D B a b) : ℂ) •
        compressed D B 0 zeroSymm zeroEven a b u (m-1) v := by
  let E := ambient D e B 0 zeroSymm zeroEven
  let J := injection D B 0 zeroSymm zeroEven
  let P := projection D B 0 zeroSymm zeroEven (a+b)
  have h := congrArg (fun A => P (A (J b v)))
    (LatticeActualStateDerivative.state_derivative_modes E (J a u) m)
  rw [translation_injection D B hD H hHG hGH] at h
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply] at h
  rw [source_transverseCharge D B hD] at h
  change compressed D B 0 zeroSymm zeroEven a b
      (moduleL D (Matrix.mulVec B a) H (-1) u) m v +
      (schur D B 0 b a : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v =
      -(m : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v at h
  calc
    _ = -(m : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v -
        (schur D B 0 b a : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v :=
      eq_sub_iff_add_eq.mpr h
    _ = _ := by
      rw [← sub_smul, schur_shift, shift_symmetric D B b a]
      congr 1
      push_cast
      ring

/-- Actual input and output conformal translations give target differentiation. -/
private theorem target_derivative_integer (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Fin e → ℤ) (u v : Carrier D) (m : ℤ) :
    moduleL D (Matrix.mulVec B a + Matrix.mulVec B b) H (-1)
      (compressed D B 0 zeroSymm zeroEven a b u m v) -
      compressed D B 0 zeroSymm zeroEven a b u m
        (moduleL D (Matrix.mulVec B b) H (-1) v) =
      -(((m : ℚ)-shift D B a b) : ℂ) •
        compressed D B 0 zeroSymm zeroEven a b u (m-1) v := by
  let E := ambient D e B 0 zeroSymm zeroEven
  let J := injection D B 0 zeroSymm zeroEven
  let P := projection D B 0 zeroSymm zeroEven (a+b)
  have h := congrArg (fun A => P (A (J b v))) (stateField_covariance E (J a u) m)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul] at h
  rw [projection_translation D B hD H hHG hGH,
    translation_injection D B hD H hHG hGH] at h
  simp only [map_add] at h
  rw [target_transverseCharge D B hD] at h
  simp only [Matrix.mulVec_add] at h
  change moduleL D (Matrix.mulVec B a + Matrix.mulVec B b) H (-1)
      (compressed D B 0 zeroSymm zeroEven a b u m v) -
      (compressed D B 0 zeroSymm zeroEven a b u m
        (moduleL D (Matrix.mulVec B b) H (-1) v) +
        -(schur D B 0 a b : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v) =
      -(m : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v at h
  have hh : moduleL D (Matrix.mulVec B a + Matrix.mulVec B b) H (-1)
      (compressed D B 0 zeroSymm zeroEven a b u m v) -
      compressed D B 0 zeroSymm zeroEven a b u m
        (moduleL D (Matrix.mulVec B b) H (-1) v) =
      -(m : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v -
        (schur D B 0 a b : ℂ) • compressed D B 0 zeroSymm zeroEven a b u (m-1) v := by
    rw [neg_smul, sub_add_eq_sub_sub, sub_neg_eq_add] at h
    exact eq_sub_iff_add_eq.mpr h
  rw [hh, ← sub_smul, schur_shift]
  congr 1
  push_cast
  ring

open private mode_off from D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalJacobi

/-- The source derivative holds on all rational modes and all source and target states. -/
theorem source_derivative (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Fin e → ℤ) (u v : Carrier D) (tau : ℚ) :
    mode D B a b (moduleL D (Matrix.mulVec B a) H (-1) u) tau v =
      -(tau : ℂ) • mode D B a b u (tau-1) v := by
  by_cases ht : ∃ m : ℤ, tau = (m : ℚ)-shift D B a b
  · obtain ⟨m,rfl⟩ := ht
    rw [show (m : ℚ)-shift D B a b-1 = ((m-1 : ℤ) : ℚ)-shift D B a b by push_cast; ring,
      mode_integer, mode_integer]
    simpa only [Rat.cast_sub, Rat.cast_intCast] using
      source_derivative_integer D B hD H hHG hGH a b u v m
  · have hs : ¬ ∃ m : ℤ, tau-1 = (m : ℚ)-shift D B a b := by
      rintro ⟨m,hm⟩
      apply ht
      refine ⟨m+1,?_⟩
      push_cast
      linarith
    rw [mode_off D B _ _ _ _ _ ht, mode_off D B _ _ _ _ _ hs, smul_zero]

/-- The target derivative uses the literal original-omega actions in both sectors. -/
theorem target_derivative (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Fin e → ℤ) (u v : Carrier D) (tau : ℚ) :
    moduleL D (Matrix.mulVec B a + Matrix.mulVec B b) H (-1)
      (mode D B a b u tau v) -
      mode D B a b u tau (moduleL D (Matrix.mulVec B b) H (-1) v) =
      -(tau : ℂ) • mode D B a b u (tau-1) v := by
  by_cases ht : ∃ m : ℤ, tau = (m : ℚ)-shift D B a b
  · obtain ⟨m,rfl⟩ := ht
    rw [show (m : ℚ)-shift D B a b-1 = ((m-1 : ℤ) : ℚ)-shift D B a b by push_cast; ring]
    simp only [mode_integer]
    simpa only [Rat.cast_sub, Rat.cast_intCast] using
      target_derivative_integer D B hD H hHG hGH a b u v m
  · have hs : ¬ ∃ m : ℤ, tau-1 = (m : ℚ)-shift D B a b := by
      rintro ⟨m,hm⟩
      apply ht
      refine ⟨m+1,?_⟩
      push_cast
      linarith
    rw [mode_off D B _ _ _ _ _ ht, mode_off D B _ _ _ _ _ ht,
      mode_off D B _ _ _ _ _ hs, map_zero, sub_zero, smul_zero]

end
end D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner
