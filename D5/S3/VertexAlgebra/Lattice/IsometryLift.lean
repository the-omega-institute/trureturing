/- GID: D5/S3/VertexAlgebra/Lattice/IsometryLift
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/IsometryLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Additive lattice isometries lift to every actual all-state integer mode. -/

import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra
import D5.S3.VertexAlgebra.OriginalCurrentMetric
import D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
import Batteries.Tactic.OpenPrivate

/-!
The form is integral, symmetric and even on the diagonal. No positivity,
nondegeneracy or finite-order condition is required. Charge and every creation
variable are transformed together.

proof_shape: lift_compatible: content
admission_basis: escape-witness
escape_witness: The intertwining states are closed under every integer product
by the actual finite iterate identity. Opposite charged grounds then recover
every neutral current, whose negative modes generate all mixed polynomials.
Charged transport is extended to every actual state without a field-law premise.

The lift context is classical (Bakalov--Kac, math/0402315v1, section 4.1;
Frenkel--Lepowsky--Meurman). The existing finite residue reconstruction retains
Matsuo--Nagatomo, hep-th/9706118v1, and Scott Carnahan's vertexAlg Apache-2.0
attribution in the owning sources. No literature novelty, coherent isometry-group
action, standard fixed-space normalization or finite lift order is asserted.
-/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.IsometryLift
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeActualGeneratorLocality LatticeActualProductKernel
open LatticeActualOrderedProducts MvPolynomial
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators VertexOperator
noncomputable section

open private lift_phase_nonzero lift_phase_cocycle from
  D5.S3.VertexAlgebra.LatticeTwistedGroundRealization


open private neutral_negative_single from
  D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private creation_one from
  D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

private def compatibleStates (D : LatticeData) (U : Module.End ℂ (Carrier D)) :
    Submodule ℂ (Carrier D) where
  carrier := {a | ∀ n b, U (((Y D a)[[n]]) b) =
    ((Y D (U a))[[n]]) (U b)}
  zero_mem' := by
    intro n b
    simp
  add_mem' := by
    intro a b ha hb n c
    simp only [map_add, VertexOperator.ncoeff, Pi.add_apply, LinearMap.add_apply]
    exact congrArg₂ (· + ·) (ha n c) (hb n c)
  smul_mem' := by
    intro z a ha n b
    simp only [map_smul, VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply]
    exact congrArg (z • ·) (ha n b)

private theorem compatible_product (D : LatticeData) (U : Module.End ℂ (Carrier D))
    (a b : Carrier D) (ha : a ∈ compatibleStates D U)
    (hb : b ∈ compatibleStates D U) (r : ℤ) :
    mu D a r b ∈ compatibleStates D U := by
  intro n c
  change ∀ n c, U (((Y D a)[[n]]) c) =
    ((Y D (U a))[[n]]) (U c) at ha
  change ∀ n c, U (((Y D b)[[n]]) c) =
    ((Y D (U b))[[n]]) (U c) at hb
  have source := stateField_iterate D a b c r n
  have target := stateField_iterate D (U a) (U b) (U c) r n
  change U (((Y D (((Y D a)[[r]]) b))[[n]]) c) =
    ((Y D (U (((Y D a)[[r]]) b)))[[n]]) (U c)
  rw [ha r b, source.2.2, map_sub, map_smul,
    map_finsum U source.1, map_finsum U source.2.1, target.2.2]
  simp only [map_smul, ha, hb]

private theorem ground_current_product (D : LatticeData) (a : Charge D) :
    mu D (Finsupp.single a 1) (bilinear D a a - 2)
      (Finsupp.single (-a) 1) =
    epsilon D a (-a) • Finsupp.single 0 (chargePolynomial D a) := by
  rw [mu, stateField_ground, actual_modes, raw_ground,
    bilinear_neg_right]
  have h : -(bilinear D a a - 2) - 1 - -bilinear D a a = 1 := by omega
  rw [h, add_neg_cancel, creation_one]

private theorem current_field (D : LatticeData) (i : Fin D.rank) :
    Y D (Finsupp.single 0 (X (i, 0) : Oscillator D)) =
      neutralField D i := by
  have hs : ((neutralField D i)[[-1]]) (vacuum D) =
      Finsupp.single 0 (X (i, 0) : Oscillator D) := by
    simpa only [vacuum, Nat.cast_zero, neg_zero, zero_sub, mul_one] using
      neutral_negative_single D i 0 0 1
  simpa only [hs] using stateField_current D i

private theorem all_state_of_ground (D : LatticeData) (U : Module.End ℂ (Carrier D))
    (hground : ∀ a : Charge D, Finsupp.single a 1 ∈ compatibleStates D U) :
    ∀ a : Carrier D, a ∈ compatibleStates D U := by
  classical
  let W := compatibleStates D U
  have hc (i : Fin D.rank) :
      Finsupp.single 0 (X (i, 0) : Oscillator D) ∈ W := by
    have h := compatible_product D U _ _ (hground (unitCharge D i))
      (hground (-unitCharge D i)) (bilinear D (unitCharge D i) (unitCharge D i) - 2)
    rw [ground_current_product] at h
    have hs := W.smul_mem (epsilon D (unitCharge D i) (-unitCharge D i)) h
    simpa [smul_smul, epsilon, paritySign_square, chargePolynomial, unitCharge,
      apply_ite, ite_smul] using hs
  have hp (a : Charge D) (p : Oscillator D) : Finsupp.single a p ∈ W := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      simpa [← Finsupp.single_smul, smul_eq_C_mul] using W.smul_mem c (hground a)
    | add p q hp hq =>
      simpa only [Finsupp.single_add] using W.add_mem hp hq
    | mul_X p x hp =>
      have h := compatible_product D U _ _ (hc x.1) hp (-(x.2 : ℤ) - 1)
      change ((Y D (Finsupp.single 0 (X (x.1, 0) : Oscillator D)))[[-(x.2 : ℤ)-1]])
        (Finsupp.single a p) ∈ W at h
      rw [current_field, neutral_negative_single] at h
      simpa only [Prod.mk.eta, mul_comm] using h
  intro a
  have h := W.sum_mem (fun b (_ : b ∈ a.support) => hp b (a b))
  change a.sum (fun b p => Finsupp.single b p) ∈ W at h
  simpa only [Finsupp.sum_single] using h

private theorem charge_expansion (D : LatticeData) (a : Charge D) :
    (∑ i : Fin D.rank, a i • unitCharge D i) = a := by
  classical
  ext j
  simp [unitCharge, Finset.sum_apply, mul_ite]

private theorem additive_expansion (D : LatticeData) {A : Type*} [AddCommGroup A]
    (f : Charge D →+ A) (a : Charge D) :
    f a = ∑ i : Fin D.rank, a i • f (unitCharge D i) := by
  conv_lhs => rw [← charge_expansion D a]
  simp only [map_sum, map_zsmul]

private def mixingMatrix (D : LatticeData) (g : Charge D ≃+ Charge D) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  fun j i => (g (unitCharge D i) j : ℂ)

private theorem charge_coordinates (D : LatticeData) (g : Charge D ≃+ Charge D)
    (a : Charge D) (j : Fin D.rank) :
    (g a j : ℂ) = ∑ i : Fin D.rank, (a i : ℂ) * mixingMatrix D g j i := by
  have h := congrArg (fun v : Charge D => (v j : ℂ))
    (additive_expansion D g.toAddMonoidHom a)
  simpa [mixingMatrix, Finset.sum_apply, zsmul_eq_mul] using h

private theorem mixing_inverse (D : LatticeData) (g h : Charge D ≃+ Charge D)
    (hinv : ∀ a, g (h a) = a) :
    mixingMatrix D g * mixingMatrix D h = 1 := by
  classical
  ext j i
  have hh := charge_coordinates D g (h (unitCharge D i)) j
  rw [hinv] at hh
  simpa only [mixingMatrix, Matrix.mul_apply, Matrix.one_apply,
    unitCharge, apply_ite, Int.cast_one, Int.cast_zero, mul_comm] using hh.symm

/-- All oscillator colours are mixed at the same frequency. -/
def oscillator (D : LatticeData) (g : Charge D ≃+ Charge D) :
    Oscillator D ≃ₐ[ℂ] Oscillator D :=
  OriginalCurrentMetric.substitutionEquiv (fun _ => mixingMatrix D g)
    (fun _ => mixingMatrix D g.symm)
    (fun _ => mixing_inverse D g g.symm g.apply_symm_apply)
    (fun _ => mixing_inverse D g.symm g g.symm_apply_apply)

private theorem oscillator_X (D : LatticeData) (g : Charge D ≃+ Charge D)
    (x : Index D) :
    oscillator D g (X x) =
      ∑ j : Fin D.rank, mixingMatrix D g j x.1 • X (j, x.2) :=
  OriginalCurrentMetric.substitution_X _ x

private def defect (D : LatticeData) (g : Charge D ≃+ Charge D) :
    Charge D →+ Charge D →+ F₂ where
  toFun a := ((integralCocycle D (g a)).comp g.toAddMonoidHom) + integralCocycle D a
  map_zero' := by ext b; simp
  map_add' a b := by ext c; simp [map_add, add_assoc, add_left_comm, add_comm]

private def defectMatrix (D : LatticeData) (g : Charge D ≃+ Charge D) :
    Matrix (Fin D.rank) (Fin D.rank) F₂ :=
  fun i j => defect D g (unitCharge D i) (unitCharge D j)

private theorem defect_symmetric (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b) :
    (defectMatrix D g).IsSymm := by
  have hsym (a b : Charge D) :
      integralCocycle D a b + integralCocycle D b a = (bilinear D a b : F₂) := by
    change (lowerCocycleExponent D a b : F₂) +
      (lowerCocycleExponent D b a : F₂) = _
    rw [← Int.cast_add, integral_cocycle_symmetrization]
  have hs (a b : Charge D) : defect D g a b = defect D g b a := by
    have h1 := hsym (g a) (g b)
    have h2 := hsym a b
    rw [hg] at h1
    change integralCocycle D (g a) (g b) + integralCocycle D a b =
      integralCocycle D (g b) (g a) + integralCocycle D b a
    apply CharTwo.add_eq_zero.mp
    rw [add_add_add_comm, h1, h2, CharTwo.add_self_eq_zero]
  exact Matrix.IsSymm.ext (fun i j => hs _ _)

private theorem defect_pairing (D : LatticeData) (g : Charge D ≃+ Charge D)
    (a b : Charge D) :
    Matrix.toBilin' (defectMatrix D g) (reduceCharge D a) (reduceCharge D b) =
      defect D g a b := by
  have ha : defect D g a b =
      ∑ i : Fin D.rank, a i • defect D g (unitCharge D i) b := by
    have h := congrArg (fun f : Charge D →+ F₂ => f b)
      (additive_expansion D (defect D g) a)
    simpa using h
  symm
  rw [ha, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [additive_expansion D (defect D g (unitCharge D i)) b]
  simp only [Finset.smul_sum, zsmul_eq_mul, defectMatrix, reduceCharge]
  apply Finset.sum_congr rfl
  intro j _
  change (a i : F₂) * ((b j : F₂) * defect D g (unitCharge D i) (unitCharge D j)) =
    (a i : F₂) * defect D g (unitCharge D i) (unitCharge D j) * (b j : F₂)
  ring

/-- A unit-valued phase of the literal lower-triangular cocycle defect. -/
def phase (D : LatticeData) (g : Charge D ≃+ Charge D) (a : Charge D) : ℂˣ :=
  Units.mk0 (liftPhase (defectMatrix D g) (reduceCharge D a))
    (lift_phase_nonzero _ _)

private theorem phase_zero (D : LatticeData) (g : Charge D ≃+ Charge D) :
    phase D g 0 = 1 := by
  apply Units.ext
  simp [phase, liftPhase, diagonalPhase, normalExponent, complexSign, reduceCharge]

private theorem phase_law (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b) (a b : Charge D) :
    (phase D g (a + b) : ℂ) * epsilon D a b =
      (phase D g a : ℂ) * (phase D g b : ℂ) * epsilon D (g a) (g b) := by
  have h := lift_phase_cocycle (defectMatrix D g) (defect_symmetric D g hg)
    (reduceCharge D a) (reduceCharge D b)
  rw [← map_add, defect_pairing] at h
  change (phase D g a : ℂ) * (phase D g b : ℂ) =
    complexSign (defect D g a b) * (phase D g (a + b) : ℂ) at h
  have hs : complexSign (defect D g a b) =
      epsilon D (g a) (g b) * epsilon D a b := by
    change complexSign ((lowerCocycleExponent D (g a) (g b) : F₂) +
      (lowerCocycleExponent D a b : F₂)) = _
    rw [complexSign_add, complexSign_integral, complexSign_integral]
    rfl
  rw [hs] at h
  calc
    _ = (epsilon D (g a) (g b) * epsilon D (g a) (g b)) *
        ((phase D g (a + b) : ℂ) * epsilon D a b) := by
          simp only [epsilon, paritySign_square, one_mul]
    _ = (epsilon D (g a) (g b) * epsilon D a b *
        (phase D g (a + b) : ℂ)) * epsilon D (g a) (g b) := by ring
    _ = _ := by rw [← h]

private theorem oscillator_charge (D : LatticeData) (g : Charge D ≃+ Charge D)
    (a : Charge D) (n : ℕ) :
    oscillator D g (∑ i : Fin D.rank, (a i : ℂ) • (X (i, n) : Oscillator D)) =
      ∑ j : Fin D.rank, (g a j : ℂ) • (X (j, n) : Oscillator D) := by
  classical
  simp only [map_sum, map_smul, oscillator_X, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_smul, ← charge_coordinates]

private theorem oscillator_smul (D : LatticeData) (g : Charge D ≃+ Charge D)
    (z : ℂ) (p : Oscillator D) :
    (oscillator D g).toRingHom (z • p) = z • oscillator D g p :=
  map_smul (oscillator D g) z p

private theorem oscillator_series (D : LatticeData) (g : Charge D ≃+ Charge D)
    (a : Charge D) :
    PowerSeries.map (oscillator D g).toRingHom (creationSeries D a) =
      creationSeries D (g a) := by
  ext q
  simp only [PowerSeries.coeff_map, creationSeries, PowerSeries.coeff_mk]
  split_ifs <;> simp only [map_zero, oscillator_smul, oscillator_charge]

private theorem oscillator_exponential (D : LatticeData) (g : Charge D ≃+ Charge D)
    (a : Charge D) :
    PowerSeries.map (oscillator D g).toRingHom (creationExponential D a) =
      creationExponential D (g a) := by
  have h : PowerSeries.HasSubst (creationSeries D a) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])
  have hm := PowerSeries.map_subst (h := (oscillator D g).toRingHom) h
    (PowerSeries.exp (Oscillator D))
  change PowerSeries.map (oscillator D g).toRingHom (creationExponential D a) =
    (PowerSeries.map (oscillator D g).toRingHom (PowerSeries.exp (Oscillator D))).subst
      (PowerSeries.map (oscillator D g).toRingHom (creationSeries D a)) at hm
  rw [hm, PowerSeries.map_exp, oscillator_series]
  rfl

private theorem oscillator_coefficient (D : LatticeData) (g : Charge D ≃+ Charge D)
    (a : Charge D) (k : ℤ) :
    oscillator D g (creationCoeff D a k) = creationCoeff D (g a) k := by
  unfold creationCoeff
  split_ifs
  · exact map_zero _
  · change (oscillator D g).toRingHom
      (PowerSeries.coeff k.toNat (creationExponential D a)) = _
    rw [← PowerSeries.coeff_map, oscillator_exponential]

private theorem contraction_coordinates (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (a : Charge D) (i : Fin D.rank) :
    (∑ j : Fin D.rank, mixingMatrix D g j i *
      (bilinear D (g a) (unitCharge D j) : ℂ)) =
        (bilinear D a (unitCharge D i) : ℂ) := by
  let f : Charge D →+ ℤ := (Matrix.toBilin' D.G (g a)).toAddMonoidHom
  have hf (b : Charge D) : f b = bilinear D (g a) b := by
    change Matrix.toBilin' D.G (g a) b = _
    exact Matrix.toBilin'_apply D.G (g a) b
  have h := additive_expansion D f (g (unitCharge D i))
  simp_rw [hf, zsmul_eq_mul] at h
  rw [hg] at h
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  simpa [mixingMatrix] using hc.symm

private theorem translated_naturality (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (a : Charge D) (p : Oscillator D) :
    Polynomial.map (oscillator D g).toRingHom (translatedPolynomial D a p) =
      translatedPolynomial D (g a) (oscillator D g p) := by
  classical
  let T (b : Charge D) : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D) :=
    MvPolynomial.aeval (fun x : Index D => translationVariable D b x.1 x.2)
  have h : (Polynomial.mapAlgHom (oscillator D g).toAlgHom).comp (T a) =
      (T (g a)).comp (oscillator D g).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro x
    have hC : (∑ j : Fin D.rank, mixingMatrix D g j x.1 •
        (Polynomial.C (X (j, x.2)) : Polynomial (Oscillator D))) =
        Polynomial.C (∑ j : Fin D.rank,
          mixingMatrix D g j x.1 • (X (j, x.2) : Oscillator D)) := by
      simp only [Polynomial.smul_C, map_sum]
    have hB : (∑ j : Fin D.rank, mixingMatrix D g j x.1 •
        (Polynomial.C ((bilinear D (g a) (unitCharge D j) : ℂ) • (1 : Oscillator D)) *
          (Polynomial.X : Polynomial (Oscillator D)) ^ (x.2 + 1))) =
        Polynomial.C ((bilinear D a (unitCharge D x.1) : ℂ) • (1 : Oscillator D)) *
          (Polynomial.X : Polynomial (Oscillator D)) ^ (x.2 + 1) := by
      simp only [← smul_mul_assoc]
      rw [← Finset.sum_mul]
      congr 1
      simp only [Polynomial.smul_C, smul_smul]
      rw [← map_sum Polynomial.C, ← Finset.sum_smul, contraction_coordinates D g hg]
    simp only [AlgHom.comp_apply, T, MvPolynomial.aeval_X, AlgEquiv.coe_toAlgHom]
    change Polynomial.map (oscillator D g).toRingHom (translationVariable D a x.1 x.2) =
      (T (g a)) (oscillator D g (X x))
    rw [oscillator_X]
    simp only [map_sum, map_smul, T, MvPolynomial.aeval_X]
    have hx : (oscillator D g).toRingHom (X (x.1, x.2)) =
        ∑ j : Fin D.rank, mixingMatrix D g j x.1 • X (j, x.2) :=
      oscillator_X D g (x.1, x.2)
    simp only [translationVariable, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, oscillator_smul,
      map_one, hx, smul_sub, Finset.sum_sub_distrib]
    rw [hC, hB]
  exact AlgHom.congr_fun h p

private def sectorMap (D : LatticeData) (g : Charge D ≃+ Charge D)
    (S : Oscillator D ≃ₐ[ℂ] Oscillator D) (eta : Charge D → ℂˣ) :
    Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun a =>
    (eta a : ℂ) • (Finsupp.lsingle (g a)).comp S.toLinearMap)

private theorem sectorMap_single (D : LatticeData) (g : Charge D ≃+ Charge D)
    (S : Oscillator D ≃ₐ[ℂ] Oscillator D) (eta : Charge D → ℂˣ)
    (a : Charge D) (p : Oscillator D) :
    sectorMap D g S eta (Finsupp.single a p) =
      (eta a : ℂ) • Finsupp.single (g a) (S p) := by
  simp [sectorMap]

/-- Charge reindexing, polynomial substitution, and the nonzero defect phase. -/
def lift (D : LatticeData) (g : Charge D ≃+ Charge D) :
    Carrier D ≃ₗ[ℂ] Carrier D where
  toLinearMap := sectorMap D g (oscillator D g) (phase D g)
  invFun := sectorMap D g.symm (oscillator D g).symm
    (fun b => (phase D g (g.symm b))⁻¹)
  left_inv := by
    have h : (sectorMap D g.symm (oscillator D g).symm
        (fun b => (phase D g (g.symm b))⁻¹)).comp
        (sectorMap D g (oscillator D g) (phase D g)) = LinearMap.id := by
      apply Finsupp.lhom_ext
      intro a p
      simp [LinearMap.comp_apply, sectorMap_single, map_smul, smul_smul]
    exact LinearMap.congr_fun h
  right_inv := by
    have h : (sectorMap D g (oscillator D g) (phase D g)).comp
        (sectorMap D g.symm (oscillator D g).symm
        (fun b => (phase D g (g.symm b))⁻¹)) = LinearMap.id := by
      apply Finsupp.lhom_ext
      intro a p
      simp [LinearMap.comp_apply, sectorMap_single, map_smul, smul_smul]
    exact LinearMap.congr_fun h

/-- The charge is transformed by g and each oscillator by the corresponding column. -/
theorem lift_single (D : LatticeData) (g : Charge D ≃+ Charge D)
    (a : Charge D) (p : Oscillator D) :
    lift D g (Finsupp.single a p) =
      (phase D g a : ℂ) • Finsupp.single (g a) (oscillator D g p) :=
  sectorMap_single D g (oscillator D g) (phase D g) a p

private theorem lift_vacuum (D : LatticeData) (g : Charge D ≃+ Charge D) :
    lift D g (vacuum D) = vacuum D := by
  simp [vacuum, lift_single, phase_zero]

private theorem lift_rawSingle (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (a : Charge D) (k : ℤ) (b : Charge D) (p : Oscillator D) :
    lift D g (rawSingle D a k b p) =
      ((phase D g a : ℂ) * (phase D g b : ℂ)) •
        rawSingle D (g a) k (g b) (oscillator D g p) := by
  classical
  have hs : (translatedPolynomial D (g a) (oscillator D g p)).support =
      (translatedPolynomial D a p).support := by
    rw [← translated_naturality D g hg]
    exact Polynomial.support_map_of_injective _ (oscillator D g).injective
  have hc (d : ℕ) :
      (translatedPolynomial D (g a) (oscillator D g p)).coeff d =
        oscillator D g ((translatedPolynomial D a p).coeff d) := by
    rw [← translated_naturality D g hg, Polynomial.coeff_map]
    rfl
  have hp : oscillator D g
      (∑ d ∈ (translatedPolynomial D a p).support,
        (translatedPolynomial D a p).coeff d • creationCoeff D a
          (k - bilinear D a b + d)) =
      ∑ d ∈ (translatedPolynomial D (g a) (oscillator D g p)).support,
        (translatedPolynomial D (g a) (oscillator D g p)).coeff d •
          creationCoeff D (g a) (k - bilinear D (g a) (g b) + d) := by
    simp only [hs, hc, hg, smul_eq_mul, map_sum, map_mul, oscillator_coefficient]
  simp only [rawSingle, map_smul, lift_single, map_add, hp, smul_smul]
  congr 1
  have h := phase_law D g hg a b
  calc
    epsilon D a b * (phase D g (a + b) : ℂ) =
        (phase D g (a + b) : ℂ) * epsilon D a b := mul_comm _ _
    _ = _ := h

private theorem lift_rawCoeff (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (a : Charge D) (k : ℤ) (v : Carrier D) :
    lift D g (rawCoeff D a k v) =
      (phase D g a : ℂ) • rawCoeff D (g a) k (lift D g v) := by
  have h : (lift D g).toLinearMap.comp (rawCoeff D a k) =
      (phase D g a : ℂ) •
        (rawCoeff D (g a) k).comp (lift D g).toLinearMap := by
    apply Finsupp.lhom_ext
    intro b p
    change lift D g (rawCoeff D a k (Finsupp.single b p)) =
      (phase D g a : ℂ) • rawCoeff D (g a) k (lift D g (Finsupp.single b p))
    rw [(actual_creation_coefficient_transport D a a).2.2.1,
      lift_single, map_smul,
      (actual_creation_coefficient_transport D (g a) (g a)).2.2.1]
    simpa only [smul_smul] using lift_rawSingle D g hg a k b p
  exact LinearMap.congr_fun h v

/--
Every additive isometry preserves the actual vacuum, charged coefficients, all
integer state products, and translation. The phase and oscillator inverse are
constructed, without a field compatibility premise.
-/
theorem lift_compatible (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b) :
    lift D g (vacuum D) = vacuum D ∧
    (∀ (a : Charge D) (k : ℤ) (v : Carrier D),
      lift D g (rawCoeff D a k v) =
        (phase D g a : ℂ) • rawCoeff D (g a) k (lift D g v)) ∧
    (∀ (a : Carrier D) (n : ℤ) (b : Carrier D),
      lift D g (((Y D a)[[n]]) b) =
        ((Y D (lift D g a))[[n]]) (lift D g b)) ∧
    (∀ v : Carrier D, lift D g (translation D v) = translation D (lift D g v)) := by
  have hground (a : Charge D) :
      Finsupp.single a 1 ∈ compatibleStates D (lift D g).toLinearMap := by
    intro n v
    change lift D g (((Y D (Finsupp.single a 1))[[n]]) v) =
      ((Y D (lift D g (Finsupp.single a 1)))[[n]]) (lift D g v)
    rw [lift_single, map_one, map_smul, stateField_ground, stateField_ground,
      actual_modes]
    rw [map_smul, Pi.smul_apply, LinearMap.smul_apply, actual_modes]
    exact lift_rawCoeff D g hg a (-n - 1) v
  have hall (a : Carrier D) (n : ℤ) (b : Carrier D) :
      lift D g (((Y D a)[[n]]) b) =
        ((Y D (lift D g a))[[n]]) (lift D g b) :=
    all_state_of_ground D (lift D g).toLinearMap hground a n b
  refine ⟨lift_vacuum D g, lift_rawCoeff D g hg, hall, ?_⟩
  intro v
  rw [LatticeActualVertexAlgebra.translation_as_mode, hall, lift_vacuum,
    ← LatticeActualVertexAlgebra.translation_as_mode]

end
end D5.S3.VertexAlgebra.Lattice.IsometryLift
