/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native creation exponentials separate into longitudinal and transverse factors. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation
import D5.S3.VertexAlgebra.Sectors.LatticeCosetProjectedAction

/-! Creation polynomials depend on the integral charge and oscillator
variables, without requiring an inverse or positive ambient Gram form.
Bakalov--Kac, math/0402315v1, section 4.1, fixes the exponential convention. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetCreationSeparation

open LatticeGeneratingFieldLocality LatticeCosetCompression LatticeCosetTransverse
open LatticeCosetSeparation MvPolynomial
open LatticeCosetProjectedAction LatticeDiscriminantTheta
open scoped BigOperators

noncomputable section

open private derivative_map solution_unique from
  D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open private exponential_derivative from D5.S3.VertexAlgebra.LatticeSugawaraConformal

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- The given external block, used only for its native creation polynomials. -/
abbrev externalLattice : LatticeData := ⟨e, C, hC, hCe⟩

/-- A longitudinal ambient polynomial is obtained by projecting and reinjecting. -/
def longitudinalPolynomial : Oscillator (ambient D e B C hC hCe) →ₐ[ℂ]
    Oscillator (ambient D e B C hC hCe) :=
  (polynomialInjection D B C hC hCe).comp (polynomialProjection D B C hC hCe)

private theorem creationSeries_separation (b : Fin e → ℤ) (n : Charge D) :
    creationSeries (ambient D e B C hC hCe) (liftCharge D B C hC hCe b n) =
      PowerSeries.map (longitudinalPolynomial D B C hC hCe).toRingHom
        (creationSeries (ambient D e B C hC hCe) (liftCharge D B C hC hCe b n)) +
      PowerSeries.map (transversePolynomial D B C hC hCe).toRingHom
        (creationSeries (externalLattice C hC hCe) b) := by
  classical
  apply PowerSeries.ext
  intro q
  rw [map_add, PowerSeries.coeff_map, PowerSeries.coeff_map]
  by_cases hq : q = 0
  · simp [creationSeries, hq]
  · simp only [creationSeries, PowerSeries.coeff_mk, dite_eq_right hq]
    change (q : ℂ)⁻¹ • (∑ i, _) =
      longitudinalPolynomial D B C hC hCe ((q : ℂ)⁻¹ • (∑ i, _)) +
        transversePolynomial D B C hC hCe ((q : ℂ)⁻¹ • (∑ i, _))
    rw [map_smul, map_smul]
    rw [← smul_add]
    congr 1
    change (∑ i : Fin (D.rank+e), _) = _
    rw [Fin.sum_univ_add]
    simp only [liftCharge, Fin.addCases_left, Fin.addCases_right,
      longitudinalPolynomial, AlgHom.comp_apply, polynomialProjection, aeval_X,
      projectionVariable, polynomialInjection, rename_X, map_smul, map_sum,
      map_add, transversePolynomial, transverse, smul_sub, Finset.sum_sub_distrib]
    abel

/-- The complete native creation exponential splits in the actual ambient
polynomial ring. The transverse factor has no old-charge dependence. -/
theorem creationExponential_separation (b : Fin e → ℤ) (n : Charge D) :
    creationExponential (ambient D e B C hC hCe) (liftCharge D B C hC hCe b n) =
      PowerSeries.map (longitudinalPolynomial D B C hC hCe).toRingHom
        (creationExponential (ambient D e B C hC hCe) (liftCharge D B C hC hCe b n)) *
      PowerSeries.map (transversePolynomial D B C hC hCe).toRingHom
        (creationExponential (externalLattice C hC hCe) b) := by
  let F := ambient D e B C hC hCe
  let A := liftCharge D B C hC hCe b n
  let L := (longitudinalPolynomial D B C hC hCe).toRingHom
  let T := (transversePolynomial D B C hC hCe).toRingHom
  let f := creationExponential F A
  let g := PowerSeries.map L f
  let h := PowerSeries.map T (creationExponential (externalLattice C hC hCe) b)
  let S := creationSeries F A
  let S₀ := PowerSeries.map L S
  let S₁ := PowerSeries.map T (creationSeries (externalLattice C hC hCe) b)
  have hs : S = S₀+S₁ := creationSeries_separation D B C hC hCe b n
  have hf : PowerSeries.derivative (R := Oscillator F) f =
      f * PowerSeries.derivative (R := Oscillator F) S := exponential_derivative F A
  have hg : PowerSeries.derivative (R := Oscillator F) g =
      g * PowerSeries.derivative (R := Oscillator F) S₀ := by
    dsimp only [g, S₀]
    rw [derivative_map, hf, map_mul, derivative_map]
  have hh : PowerSeries.derivative (R := Oscillator F) h =
      h * PowerSeries.derivative (R := Oscillator F) S₁ := by
    dsimp only [h, S₁]
    rw [derivative_map, exponential_derivative (externalLattice C hC hCe) b,
      map_mul, derivative_map]
  have hgh : PowerSeries.derivative (R := Oscillator F) (g*h) =
      (g*h) * PowerSeries.derivative (R := Oscillator F) S := by
    have hd := (PowerSeries.derivative (R := Oscillator F)).leibniz' g h
    change PowerSeries.derivative (R := Oscillator F) (g*h) =
      g * PowerSeries.derivative (R := Oscillator F) h +
        h * PowerSeries.derivative (R := Oscillator F) g at hd
    rw [hd, hg, hh, hs, map_add]
    ring
  apply solution_unique f (g*h) _ hf hgh
  have hcF := LatticeSugawaraConformal.exponential_constant F A
  have hcE := LatticeSugawaraConformal.exponential_constant (externalLattice C hC hCe) b
  have hg0 : PowerSeries.coeff 0 g = 1 := by
    change L (PowerSeries.coeff 0 f) = 1
    rw [show PowerSeries.coeff 0 f = 1 from hcF, map_one]
  have hh0 : PowerSeries.coeff 0 h = 1 := by
    change T (PowerSeries.coeff 0 (creationExponential (externalLattice C hC hCe) b)) = 1
    rw [hcE, map_one]
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    hg0, hh0, one_mul]
  exact hcF

private theorem creationCoeff_separation (b : Fin e → ℤ) (n : Charge D) (t : ℤ) :
    creationCoeff (ambient D e B C hC hCe) (liftCharge D B C hC hCe b n) t =
      ∑ᶠ j : ℕ, longitudinalPolynomial D B C hC hCe
          (creationCoeff (ambient D e B C hC hCe) (liftCharge D B C hC hCe b n) (t-j)) *
        transversePolynomial D B C hC hCe
          (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) b)) := by
  classical
  let F := ambient D e B C hC hCe
  let β := liftCharge D B C hC hCe b n
  let L := longitudinalPolynomial D B C hC hCe
  let T := transversePolynomial D B C hC hCe
  let g := creationExponential (externalLattice C hC hCe) b
  change creationCoeff F β t = ∑ᶠ j : ℕ, L (creationCoeff F β (t-j)) * T (PowerSeries.coeff j g)
  by_cases ht : t < 0
  · rw [creationCoeff, dite_eq_left ht]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    simp [creationCoeff, show t-(j : ℤ) < 0 by omega]
  · have hsub : Function.support (fun j : ℕ =>
        L (creationCoeff F β (t-j)) * T (PowerSeries.coeff j g)) ⊆
          Finset.range (t.toNat+1) := by
      intro j hj
      apply Finset.mem_range.mpr
      by_contra hn
      exact hj (by simp [creationCoeff, show t-(j : ℤ) < 0 by omega])
    rw [finsum_eq_sum_of_support_subset _ hsub, creationCoeff, dite_eq_right ht]
    rw [creationExponential_separation D B C hC hCe b n, PowerSeries.coeff_mul]
    rw [← Finset.Nat.sum_antidiagonal_swap]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro j hj
    have hjt : (j : ℤ) ≤ t := by
      have := Finset.mem_range.mp hj
      omega
    have hnat : (t-(j : ℤ)).toNat = t.toNat-j := by omega
    simp only [PowerSeries.coeff_map, creationCoeff, show ¬ t-(j : ℤ) < 0 by omega,
      ↓reduceDIte, hnat]
    rfl

private theorem translated_longitudinal
    (A : Charge (ambient D e B C hC hCe)) :
    (translatedProjection D B C hC hCe A).comp
        (longitudinalPolynomial D B C hC hCe) =
      longitudinalTranslation D B C hC hCe A := by
  have hold : (translatedProjection D B C hC hCe A).comp
      (polynomialInjection D B C hC hCe) =
      aeval (fun x : Index D => Polynomial.C (X x : Oscillator D) -
        Polynomial.C ((bilinear (ambient D e B C hC hCe) A
          (unitCharge _ (x.1.castAdd e)) : ℂ) • 1) * Polynomial.X^(x.2+1)) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [translatedProjection, polynomialInjection, polynomialProjection,
      projectionVariable, translationVariable]
  change ((translatedProjection D B C hC hCe A).comp
    (polynomialInjection D B C hC hCe)).comp (polynomialProjection D B C hC hCe) = _
  rw [hold]
  rfl

private theorem translated_transverse_hom (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) :
    (translatedProjection D B C hC hCe (liftCharge D B C hC hCe a n)).comp
        (transversePolynomial D B C hC hCe) =
      (Polynomial.mapAlgHom (Algebra.ofId ℂ (Oscillator D))).comp
        (scalarTranslation D B C a) := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [AlgHom.comp_apply, transversePolynomial, aeval_X]
  rw [transverse_translation D B C hC hCe hD]
  simp [scalarTranslation, MvPolynomial.smul_eq_C_mul]

set_option maxRecDepth 4096 in
/-- Each actual transverse creation coefficient contracts to exactly one
inverse field power with the rational Schur binomial coefficient. -/
theorem transverse_creation_coefficient (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (j : ℕ) :
    scalarTranslation D B C a
        (PowerSeries.coeff j (creationExponential (externalLattice C hC hCe) b)) =
      correction D B C a b j • (Polynomial.X^j : Polynomial ℂ) := by
  let F := ambient D e B C hC hCe
  let α := liftCharge D B C hC hCe a 0
  let β := liftCharge D B C hC hCe b 0
  let T := translatedProjection D B C hC hCe α
  let L := longitudinalTranslation D B C hC hCe α
  let R := Polynomial.mapAlgHom (Algebra.ofId ℂ (Oscillator D))
  let f := creationExponential F β
  let g := creationExponential (externalLattice C hC hCe) b
  let K := PowerSeries.rescale (-Polynomial.X : Polynomial (Oscillator D))
    (PowerSeries.binomialSeries (R := ℚ) (Polynomial (Oscillator D)) (schur D B C a b))
  have hs := congrArg (PowerSeries.map T.toRingHom)
    (creationExponential_separation D B C hC hCe b 0)
  rw [map_mul] at hs
  have hs' : PowerSeries.map T.toRingHom f =
    PowerSeries.map (T.comp (longitudinalPolynomial D B C hC hCe)).toRingHom f *
      PowerSeries.map (T.comp (transversePolynomial D B C hC hCe)).toRingHom g := by
    convert hs using 1 <;>
      first | rfl | (congr 1 <;> apply PowerSeries.ext <;> intro i <;> rfl)
  rw [translated_longitudinal D B C hC hCe,
    translated_transverse_hom D B C hC hCe hD] at hs'
  have hk := creationExponential_factorization D B C hC hCe hD a b 0 0
  change PowerSeries.map T.toRingHom f = PowerSeries.map L.toRingHom f * K at hk
  have hu : IsUnit (PowerSeries.map L.toRingHom f) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    have hc : PowerSeries.coeff 0 (PowerSeries.map L.toRingHom f) = 1 := by
      rw [PowerSeries.coeff_map, LatticeSugawaraConformal.exponential_constant F β, map_one]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
    exact isUnit_one
  have hm := hu.mul_left_cancel (hs'.symm.trans hk)
  let ev : Oscillator D →ₐ[ℂ] ℂ := aeval (fun _ : Index D => (0 : ℂ))
  have hret (q : Polynomial ℂ) : Polynomial.map ev.toRingHom (R q) = q := by
    apply Polynomial.ext
    intro i
    simp [R, ev, Polynomial.coeff_map, MvPolynomial.algebraMap_apply]
  have hj := congrArg (Polynomial.map ev.toRingHom) (congrArg (PowerSeries.coeff j) hm)
  change Polynomial.map ev.toRingHom
      (R (scalarTranslation D B C a (PowerSeries.coeff j g))) =
    Polynomial.map ev.toRingHom (PowerSeries.coeff j K) at hj
  rw [hret, show PowerSeries.coeff j K = (-Polynomial.X)^j *
      algebraMap ℚ (Polynomial (Oscillator D)) (Ring.choose (schur D B C a b) j) by
        simp [K, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
          Algebra.smul_def]] at hj
  have hrat (r : ℚ) : Polynomial.map ev.toRingHom
      (algebraMap ℚ (Polynomial (Oscillator D)) r) = Polynomial.C (r : ℂ) := by
    change (Polynomial.mapRingHom ev.toRingHom)
      (algebraMap ℚ (Polynomial (Oscillator D)) r) = _
    rw [RingHom.map_rat_algebraMap]
    exact RingHom.congr_fun (Subsingleton.elim
      (algebraMap ℚ (Polynomial ℂ)) (Polynomial.C.comp (algebraMap ℚ ℂ))) r
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_X, hrat] at hj
  rw [hj]
  rw [correction, Polynomial.smul_eq_C_mul]
  change (-Polynomial.X : Polynomial ℂ)^j *
      Polynomial.C ((Ring.choose (schur D B C a b) j : ℚ) : ℂ) =
    Polynomial.C ((-1 : ℂ)^j * ((Ring.choose (schur D B C a b) j : ℚ) : ℂ)) * Polynomial.X^j
  rw [Polynomial.C_mul, Polynomial.C_pow]
  have hneg : Polynomial.C (-1 : ℂ) = (-1 : Polynomial ℂ) := map_neg Polynomial.C 1
  rw [hneg, neg_pow]
  ring

end
end D5.S3.VertexAlgebra.LatticeCosetCreationSeparation
