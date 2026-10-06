/- GID: D5/S3/VertexAlgebra/CollisionRationalExpansions
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/CollisionRationalExpansions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Injective ordered rational expansions and supported residue fibres. -/

/-
Injective ordered rational expansions and supported residue fibres.

The proof uses the native mathlib Hahn/Laurent and polynomial kernels.
LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio;
HahnSeries: Aaron Anderson; partial fractions: Kevin Buzzard, Sidharth Hariharan,
Aaron Liu. These library sources are released under Apache 2.0.
Actual HVertexOperator and VertexOperator composition: Scott Carnahan, Apache 2.0.
The imported normal-product supplier attributes its adaptation to Carnahan's
vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea (Apache 2.0).
No actual Monster carrier or fused-state identification is asserted.
-/

import D5.S3.VertexAlgebra.CollisionLaurentKernels
import D5.S3.VertexAlgebra.SupportedFieldWords
import Mathlib.Tactic.Abel

noncomputable section
namespace D5.S3.VertexAlgebra

section
namespace CollisionRationalExpansions.RationalCoefficientCollision
open CollisionLaurentKernels.LaurentCollision CollisionLaurentKernels.RationalFusedResidue CollisionLaurentKernels.SeparatedResidue CollisionLaurentKernels.ResidueBaseChange
open scoped RatFunc
variable (K : Type*) [Field K]

def xPolynomial : Polynomial K →+* Rational K :=
  (algebraMap (Bivariate K) (Rational K)).comp Polynomial.C

lemma xPolynomial_injective : Function.Injective (xPolynomial K) :=
  (IsFractionRing.injective (Bivariate K) (Rational K)).comp Polynomial.C_injective

/-- The coefficient rational function h(x) is independent of z. -/
def rationalX : RatFunc K →+* Rational K := IsFractionRing.lift (xPolynomial_injective K)

lemma polyXZ_C (p : Polynomial K) :
    polyXZ K (Polynomial.C p) = HahnSeries.C (algebraMap (Polynomial K) (LaurentSeries K) p) := by
  simp [polyXZ, Polynomial.algebraMap_hahnSeries_apply]

lemma coefficientPoly_C :
    (algebraMap (Polynomial K) (LaurentSeries K)).comp Polynomial.C =
      (HahnSeries.C : K →+* LaurentSeries K) := by
  ext a
  simp [Polynomial.algebraMap_hahnSeries_apply]

lemma polyZX_C (p : Polynomial K) :
    polyZX K (Polynomial.C p) = outerSeries K
      (algebraMap (Polynomial K) (LaurentSeries K) p) := by
  change polyXZ K (Polynomial.Bivariate.swap (Polynomial.C p)) = _
  rw [Polynomial.Bivariate.swap_C]
  unfold outerSeries
  rw [seriesMap_polynomial]
  change algebraMap (Polynomial (LaurentSeries K)) (ZX K)
    ((p.map Polynomial.C).map (algebraMap (Polynomial K) (LaurentSeries K))) = _
  rw [Polynomial.map_map, coefficientPoly_C]

lemma polyFused_C (p : Polynomial K) :
    fusedPoly K (Polynomial.C p) = HahnSeries.C
      (algebraMap (Polynomial K) (LaurentSeries K) p) := by
  change polyXZ K ((Polynomial.algEquivAevalXAddC Polynomial.X) (Polynomial.C p)) = _
  simp [Polynomial.algEquivAevalXAddC_apply, polyXZ_C]

theorem rationalX_ZX (h : RatFunc K) :
    iotaZX K (rationalX K h) = outerSeries K (expandX K h) := by
  have eqmaps : (iotaZX K).comp (rationalX K) =
      (seriesMap (HahnSeries.C : K →+* LaurentSeries K)).comp (expandX K) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial K)
    intro p
    simp only [RingHom.comp_apply, rationalX, IsFractionRing.lift_algebraMap,
      xPolynomial, RingHom.comp_apply, iotaZX, IsFractionRing.lift_algebraMap]
    unfold expandX
    rw [← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
    exact polyZX_C K p
  exact RingHom.congr_fun eqmaps h

theorem rationalX_XZ (h : RatFunc K) :
    iotaXZ K (rationalX K h) = HahnSeries.C (expandX K h) := by
  have eqmaps : (iotaXZ K).comp (rationalX K) =
      (HahnSeries.C : LaurentSeries K →+* XZ K).comp (expandX K) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial K)
    intro p
    simp only [RingHom.comp_apply, rationalX, IsFractionRing.lift_algebraMap,
      xPolynomial, RingHom.comp_apply, iotaXZ, IsFractionRing.lift_algebraMap]
    unfold expandX
    rw [← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
    exact polyXZ_C K p
  exact RingHom.congr_fun eqmaps h

theorem rationalX_fused (h : RatFunc K) :
    iotaFused K (rationalX K h) = HahnSeries.C (expandX K h) := by
  have eqmaps : (iotaFused K).comp (rationalX K) =
      (HahnSeries.C : LaurentSeries K →+* XZ K).comp (expandX K) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial K)
    intro p
    simp only [RingHom.comp_apply, rationalX, IsFractionRing.lift_algebraMap,
      xPolynomial, RingHom.comp_apply, iotaFused, IsFractionRing.lift_algebraMap]
    unfold expandX
    rw [← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
    exact polyFused_C K p
  exact RingHom.congr_fun eqmaps h

/-- Full diagonal partial-fraction compatibility over the rational coefficient
field K(x), all polynomial degrees, all pole orders and all integer weights. -/
theorem rational_coefficient_collision (h : RatFunc K) (m p : ℕ) (r : ℤ) :
    let R := rationalX K h * (z K ^ m * diagonal K ^ (r-p))
    expandX K (localResidue K R) =
      resZ_ZX K (iotaZX K R) - resZ_XZ K (iotaXZ K R) := by
  dsimp only
  rw [← fused_residue_commutes]
  simp only [map_mul]
  rw [rationalX_ZX, rationalX_XZ, rationalX_fused,
    residue_outerSeries_mul, CollisionLaurentKernels.PolynomialCollision.resXZ_inner_scalar,
    CollisionLaurentKernels.PolynomialCollision.resXZ_inner_scalar, ← mul_sub]
  congr 1
  simpa only [map_mul] using (rational_monomial_jump K m p r).symm

end CollisionRationalExpansions.RationalCoefficientCollision
end

section
namespace CollisionRationalExpansions.SpectatorPole
open CollisionLaurentKernels.LaurentCollision CollisionLaurentKernels.RationalFusedResidue CollisionRationalExpansions.RationalCoefficientCollision
open CollisionLaurentKernels.SeparatedResidue CollisionLaurentKernels.ResidueBaseChange
open scoped RatFunc PowerSeries
variable (K : Type*) [Field K]

def zPolynomial : Polynomial K →+* Rational K :=
  (algebraMap (Bivariate K) (Rational K)).comp (Polynomial.mapRingHom Polynomial.C)

lemma zPolynomial_injective : Function.Injective (zPolynomial K) :=
  (IsFractionRing.injective (Bivariate K) (Rational K)).comp
    (Polynomial.map_injective Polynomial.C Polynomial.C_injective)

def rationalZ : RatFunc K →+* Rational K := IsFractionRing.lift (zPolynomial_injective K)

lemma rationalZ_ZX (g : RatFunc K) :
    iotaZX K (rationalZ K g) = HahnSeries.C (expandX K g) := by
  have eqmaps : (iotaZX K).comp (rationalZ K) =
      (HahnSeries.C : LaurentSeries K →+* ZX K).comp (expandX K) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial K)
    intro p
    simp only [RingHom.comp_apply, rationalZ, IsFractionRing.lift_algebraMap,
      zPolynomial, RingHom.comp_apply, iotaZX, IsFractionRing.lift_algebraMap]
    change polyXZ K (Polynomial.Bivariate.swap (p.map Polynomial.C)) = _
    rw [Polynomial.Bivariate.swap_map_C, polyXZ_C]
    unfold expandX
    rw [← IsScalarTower.algebraMap_apply]
  exact RingHom.congr_fun eqmaps g

lemma rationalZ_XZ (g : RatFunc K) :
    iotaXZ K (rationalZ K g) = outerSeries K (expandX K g) := by
  have eqmaps : (iotaXZ K).comp (rationalZ K) =
      (seriesMap (HahnSeries.C : K →+* LaurentSeries K)).comp (expandX K) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial K)
    intro p
    simp only [RingHom.comp_apply, rationalZ, IsFractionRing.lift_algebraMap,
      zPolynomial, RingHom.comp_apply, iotaXZ, IsFractionRing.lift_algebraMap]
    unfold expandX
    rw [← IsScalarTower.algebraMap_apply]
    have hp := polyZX_C K p
    change polyXZ K (Polynomial.Bivariate.swap (Polynomial.C p)) = _ at hp
    rw [Polynomial.Bivariate.swap_C] at hp
    exact hp
  exact RingHom.congr_fun eqmaps g

lemma translatedZ_constant (p : Polynomial K) :
    (translatedPoly K (p.map Polynomial.C)).coeff 0 =
      algebraMap (Polynomial K) (CoefficientField K) p := by
  have eqmaps :
      (Polynomial.evalRingHom (0 : CoefficientField K)).comp
        ((translatedPoly K).comp (Polynomial.mapRingHom Polynomial.C)) =
      algebraMap (Polynomial K) (CoefficientField K) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [translatedPoly, toCoefficientPoly, Polynomial.algEquivAevalXAddC_apply,
        ← IsScalarTower.algebraMap_apply]
    · simp [translatedPoly, toCoefficientPoly, Polynomial.algEquivAevalXAddC_apply]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact RingHom.congr_fun eqmaps p

lemma regular_rational_residue {E : Type*} [Field E] (P Q : Polynomial E)
    (hQ : Q.coeff 0 ≠ 0) :
    (algebraMap (RatFunc E) (LaurentSeries E)
      (algebraMap (Polynomial E) (RatFunc E) P /
       algebraMap (Polynomial E) (RatFunc E) Q)).coeff (-1) = 0 := by
  let psQ : PowerSeries E := Q
  have hconst : PowerSeries.constantCoeff psQ ≠ 0 := by
    simpa [psQ, ← PowerSeries.coeff_zero_eq_constantCoeff] using hQ
  have inverse : (HahnSeries.ofPowerSeries ℤ E psQ)⁻¹ =
      HahnSeries.ofPowerSeries ℤ E psQ⁻¹ := by
    have hmul := congrArg (HahnSeries.ofPowerSeries ℤ E)
      (PowerSeries.mul_inv_cancel psQ hconst)
    simp only [map_mul, map_one] at hmul
    exact inv_eq_of_mul_eq_one_right hmul
  rw [map_div₀,
    ← IsScalarTower.algebraMap_apply (Polynomial E) (RatFunc E) (LaurentSeries E),
    ← IsScalarTower.algebraMap_apply (Polynomial E) (RatFunc E) (LaurentSeries E),
    Polynomial.algebraMap_hahnSeries_apply, Polynomial.algebraMap_hahnSeries_apply]
  change (HahnSeries.ofPowerSeries ℤ E (P : PowerSeries E) /
    HahnSeries.ofPowerSeries ℤ E psQ).coeff (-1) = 0
  rw [div_eq_mul_inv, inverse, ← map_mul]
  simp only [PowerSeries.coeff_coe, show (-1 : ℤ) < 0 by omega, ↓reduceIte]

lemma localRational_z_polynomial (p : Polynomial K) :
    localRational K (rationalZ K (algebraMap (Polynomial K) (RatFunc K) p)) =
    algebraMap (Polynomial (CoefficientField K)) (RatFunc (CoefficientField K))
      (translatedPoly K (p.map Polynomial.C)) := by
  rw [rationalZ, IsFractionRing.lift_algebraMap, zPolynomial, RingHom.comp_apply,
    localRational, IsFractionRing.lift_algebraMap]
  rfl

/-- The separated z-rational term is regular at z=x: q(x) is nonzero because
x is transcendental, even when g has arbitrary poles in z. -/
theorem rationalZ_localResidue_zero (g : RatFunc K) :
    localResidue K (rationalZ K g) = 0 := by
  induction g using RatFunc.induction_on with
  | f p q hq =>
    change (algebraMap (RatFunc (CoefficientField K)) (LaurentSeries (CoefficientField K))
      (localRational K (rationalZ K
        (algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q)))).coeff (-1) = 0
    rw [map_div₀, map_div₀, localRational_z_polynomial, localRational_z_polynomial]
    apply regular_rational_residue
    rw [translatedZ_constant]
    exact RatFunc.algebraMap_ne_zero hq

/-- All separated non-diagonal partial-fraction terms cancel under adjacent
swap, and their rational fused residue vanishes. K is a fixed coefficient field. -/
theorem separated_rational_collision (g h : RatFunc K) :
    let R := rationalX K h * rationalZ K g
    expandX K (localResidue K R) =
      resZ_ZX K (iotaZX K R) - resZ_XZ K (iotaXZ K R) := by
  dsimp only
  rw [← fused_residue_commutes]
  simp only [map_mul]
  rw [rationalX_ZX, rationalX_XZ, rationalX_fused,
    rationalZ_ZX, rationalZ_XZ, mul_comm (outerSeries K (expandX K h)),
    separated_residue_cancel, sub_self, CollisionLaurentKernels.PolynomialCollision.resXZ_inner_scalar]
  rw [fused_residue_commutes, rationalZ_localResidue_zero, map_zero, mul_zero]

end CollisionRationalExpansions.SpectatorPole
end

section
/- The residue theorem for an algebraic partial-fraction normal form. The
normal-form equality is algebraic data, never an assumed residue jump. -/
namespace CollisionRationalExpansions.PartialFractionCollision
open CollisionLaurentKernels.LaurentCollision CollisionLaurentKernels.RationalFusedResidue CollisionRationalExpansions.RationalCoefficientCollision
open CollisionRationalExpansions.SpectatorPole
variable (K : Type*) [Field K]

def Compatible (R : Rational K) : Prop :=
    resZ_ZX K (iotaZX K R) - resZ_XZ K (iotaXZ K R) =
      resZ_XZ K (iotaFused K R)

lemma compatible_zero : Compatible K 0 := by
  simp only [Compatible, map_zero, resZ_ZX, resZ_XZ]
  ext n
  simp [HahnSeries.map_coeff]

lemma compatible_add {R S : Rational K} (hR : Compatible K R) (hS : Compatible K S) :
    Compatible K (R+S) := by
  unfold Compatible at *
  rw [map_add, map_add, map_add, resZX_add, resXZ_add, resXZ_add, ← hR, ← hS]
  ring

lemma compatible_sum {I : Type*} (s : Finset I) (F : I → Rational K)
    (hF : ∀ i ∈ s, Compatible K (F i)) : Compatible K (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using compatible_zero K
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact compatible_add K (hF i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- This normal form contains arbitrary K(x) coefficients, arbitrary diagonal
pole orders, arbitrary polynomial z-numerators, and arbitrary separated
spectator z-poles. There is no positivity restriction on the residue weight r. -/
theorem weighted_normal_form_collision {I J : Type*} (s : Finset I) (t : Finset J)
    (h : I → RatFunc K) (m p : I → ℕ) (g h' : J → RatFunc K)
    (R : Rational K) (r : ℤ)
    (decomposition : diagonal K ^ r * R =
      (∑ i ∈ s, rationalX K (h i) * (z K ^ m i * diagonal K ^ (-(p i : ℤ)))) +
      (∑ j ∈ t, rationalX K (h' j) * rationalZ K (g j))) :
    expandX K (localResidue K (diagonal K ^ r * R)) =
      resZ_ZX K (iotaZX K (diagonal K ^ r * R)) -
      resZ_XZ K (iotaXZ K (diagonal K ^ r * R)) := by
  rw [decomposition, ← fused_residue_commutes]
  apply Eq.symm
  apply compatible_add K
  · apply compatible_sum K
    intro i hi
    have hp := rational_coefficient_collision K (h i) (m i) (p i) 0
    dsimp only at hp
    rw [← fused_residue_commutes] at hp
    simpa only [Compatible, zero_sub] using hp.symm
  · apply compatible_sum K
    intro j hj
    have hs := separated_rational_collision K (g j) (h' j)
    dsimp only at hs
    rw [← fused_residue_commutes] at hs
    simpa only [Compatible] using hs.symm

end CollisionRationalExpansions.PartialFractionCollision
end

section
namespace CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution SupportedFieldWords.FiniteConvolution
variable (K : Type*) [Field K]

abbrev LabelledPolynomial (n : ℕ) := AddMonoidAlgebra K (Fin n → ℤ)
abbrev CommonRational (n : ℕ) := FractionRing (LabelledPolynomial K n)

lemma scalarPolynomial_injective {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] :
    Function.Injective (scalarPolynomial (Γ := Γ) (K := K)) := by
  intro P Q h
  ext e
  rw [← scalarPolynomial_coeff, ← scalarPolynomial_coeff, h]

/-- Order has been chosen by assigning field labels to positions 0,...,n-1.
A permutation of labels changes the embedding, never the common rational field. -/
def orderedPolynomial (n : ℕ) : LabelledPolynomial K n →ₐ[K] HahnSeries (Indices n) K :=
  (scalarPolynomial (Γ := Indices n) (K := K)).comp
    (AddMonoidAlgebra.domCongr K K (exponentAddEquiv n)).toAlgHom

lemma orderedPolynomial_injective (n : ℕ) : Function.Injective (orderedPolynomial K n) :=
  (scalarPolynomial_injective K).comp
    (AddMonoidAlgebra.domCongr K K (exponentAddEquiv n)).injective

/-- Actual common rational field -> scalar field of the chosen ordered support.
This is a fraction-field lift, so every nonzero clearing polynomial is a unit. -/
def orderedRational (n : ℕ) : CommonRational K n →+* HahnSeries (Indices n) K :=
  IsFractionRing.lift (orderedPolynomial_injective K n)

def labelPermutation (n : ℕ) (sigma : Equiv.Perm (Fin n)) :
    (Fin n → ℤ) ≃+ (Fin n → ℤ) where
  toFun e := fun i => e (sigma i)
  invFun e := fun i => e (sigma.symm i)
  left_inv e := by funext i; simp
  right_inv e := by funext i; simp
  map_add' _ _ := rfl

def orderExponents (n : ℕ) (sigma : Equiv.Perm (Fin n)) :
    (Fin n → ℤ) ≃+ Indices n :=
  (labelPermutation n sigma).trans (exponentAddEquiv n)

def orderedPolynomialFor (n : ℕ) (sigma : Equiv.Perm (Fin n)) :
    LabelledPolynomial K n →ₐ[K] HahnSeries (Indices n) K :=
  (scalarPolynomial (Γ := Indices n) (K := K)).comp
    (AddMonoidAlgebra.domCongr K K (orderExponents n sigma)).toAlgHom

lemma orderedPolynomialFor_injective (n : ℕ) (sigma : Equiv.Perm (Fin n)) :
    Function.Injective (orderedPolynomialFor K n sigma) :=
  (scalarPolynomial_injective K).comp
    (AddMonoidAlgebra.domCongr K K (orderExponents n sigma)).injective

/-- Every ordering uses the same fixed-labelled common rational field, with
an explicit coordinate permutation before its support embedding. -/
def orderedRationalFor (n : ℕ) (sigma : Equiv.Perm (Fin n)) :
    CommonRational K n →+* HahnSeries (Indices n) K :=
  IsFractionRing.lift (orderedPolynomialFor_injective K n sigma)


variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Coefficient embedding of the supported vector carrier into the native
labelled coefficient-function target. -/
def labelledCoefficients (n : ℕ) (F : HahnModule (Indices n) K V) : (Fin n → ℤ) → V :=
  fun e => coefficients F (exponentAddEquiv n e)

lemma labelledCoefficients_injective (n : ℕ) :
    Function.Injective (labelledCoefficients K (V := V) n) := by
  intro F G h
  apply HahnModule.ext
  funext g
  have he := congrFun h ((exponentAddEquiv n).symm g)
  simpa only [labelledCoefficients, coefficients, AddEquiv.apply_symm_apply] using he

/-- Precise original finite-word support obligation; it is a theorem of the
actual generic field carrier, with no new uniform operator truncation axiom. -/
theorem actual_word_supported (n : ℕ) (A : Fin n → VertexOperator K V) (c : V) :
    ∃ F : HahnModule (Indices n) K V,
      labelledCoefficients K n F = fun e => actualWord n A e c := by
  refine ⟨ordered n A c, ?_⟩
  funext e
  exact ordered_coeff n A e c

end CollisionRationalExpansions.OrderedRationalExpansion
end

section
/- Fixed-exponent fibers of the actual reverse-lex ordered-word Hahn carrier.
The construction restricts an already expanded global series; it never extracts
spectator coefficients from a polynomial before division. -/
namespace CollisionRationalExpansions.HahnFiberResidue
open SupportedFieldWords.OrderedWords
set_option backward.isDefEq.respectTransparency false

/-- Insert a fixed exponent after `inner` word positions and before `outer`
positions. The unchanged outer positions retain their lex priority. -/
def insertIndex (inner : ℕ) : (outer : ℕ) → ℤ →
    Indices (inner + outer) → Indices ((inner + 1) + outer)
  | 0, t, g => toLex (t, g)
  | outer + 1, t, g =>
      toLex ((ofLex g).1, insertIndex inner outer t (ofLex g).2)

theorem insertIndex_le_iff (inner outer : ℕ) (t : ℤ)
    (g h : Indices (inner + outer)) :
    insertIndex inner outer t g ≤ insertIndex inner outer t h ↔ g ≤ h := by
  induction outer with
  | zero =>
    change (toLex (t, g) : ℤ ×ₗ Indices inner) ≤ toLex (t, h) ↔ g ≤ h
    rw [Prod.Lex.le_iff]
    simp
  | succ outer ih =>
    change (toLex ((ofLex g).1, insertIndex inner outer t (ofLex g).2) :
      ℤ ×ₗ Indices ((inner + 1) + outer)) ≤
      toLex ((ofLex h).1, insertIndex inner outer t (ofLex h).2) ↔
      (show ℤ ×ₗ Indices (inner + outer) from g) ≤ h
    rw [Prod.Lex.le_iff, Prod.Lex.le_iff]
    simp only [ofLex_toLex, ih]
    rfl

def insertEmbedding (inner outer : ℕ) (t : ℤ) :
    Indices (inner + outer) ↪o Indices ((inner + 1) + outer) :=
  OrderEmbedding.ofMapLEIff (insertIndex inner outer t) (insertIndex_le_iff inner outer t)

variable {Γ Δ R : Type*} [PartialOrder Γ] [PartialOrder Δ] [Zero R]

/-- Pull back to an order embedded fiber. Support is proved from the full
Hahn support, rather than postulated for a coefficient distribution. -/
def pullFiber (f : Γ ↪o Δ) (F : HahnSeries Δ R) : HahnSeries Γ R where
  coeff g := F.coeff (f g)
  isPWO_support' := by
    intro a
    obtain ⟨m, n, hmn, hle⟩ := F.isPWO_support'
      (fun i => ⟨f (a i).val, (a i).property⟩)
    exact ⟨m, n, hmn, f.le_iff_le.mp hle⟩

@[simp] theorem pullFiber_coeff (f : Γ ↪o Δ) (F : HahnSeries Δ R) (g : Γ) :
    (pullFiber f F).coeff g = F.coeff (f g) := rfl

def fiber (inner outer : ℕ) (t : ℤ)
    (F : HahnSeries (Indices ((inner + 1) + outer)) R) :
    HahnSeries (Indices (inner + outer)) R :=
  pullFiber (insertEmbedding inner outer t) F

/-- Residue in an arbitrary word slot, with every other exponent unchanged. -/
def residue (inner outer : ℕ)
    (F : HahnSeries (Indices ((inner + 1) + outer)) R) :
    HahnSeries (Indices (inner + outer)) R := fiber inner outer (-1) F

@[simp] theorem residue_coeff (inner outer : ℕ)
    (F : HahnSeries (Indices ((inner + 1) + outer)) R)
    (g : Indices (inner + outer)) :
    (residue inner outer F).coeff g = F.coeff (insertIndex inner outer (-1) g) := rfl

variable {S : Type*} [AddCommGroup S]
def fiberAddHom (inner outer : ℕ) (t : ℤ) :
    HahnSeries (Indices ((inner + 1) + outer)) S →+
      HahnSeries (Indices (inner + outer)) S where
  toFun := fiber inner outer t
  map_zero' := by ext g; rfl
  map_add' F G := by ext g; rfl


end CollisionRationalExpansions.HahnFiberResidue
end

section
namespace CollisionRationalExpansions.HahnFiberScalar
open CollisionRationalExpansions.HahnFiberResidue SupportedFieldWords.OrderedWords HahnSeries
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem insertIndex_zero (inner outer : ℕ) : insertIndex inner outer 0 0 = 0 := by
  induction outer with
  | zero => rfl
  | succ outer ih =>
    change toLex (0, insertIndex inner outer 0 0) = 0
    rw [ih]
    rfl

theorem insertIndex_add (inner outer : ℕ) (t : ℤ)
    (g h : Indices (inner + outer)) :
    insertIndex inner outer 0 g + insertIndex inner outer t h =
      insertIndex inner outer t (g + h) := by
  induction outer with
  | zero => change toLex (0 + t, g + h) = toLex (t, g + h); simp
  | succ outer ih =>
    change toLex ((ofLex g).1 + (ofLex h).1,
      insertIndex inner outer 0 (ofLex g).2 + insertIndex inner outer t (ofLex h).2) = _
    rw [ih]
    rfl

def zeroInsert (inner outer : ℕ) :
    Indices (inner + outer) →+ Indices ((inner + 1) + outer) where
  toFun := insertIndex inner outer 0
  map_zero' := insertIndex_zero inner outer
  map_add' g h := (insertIndex_add inner outer 0 g h).symm

/-- The remaining full ordered Hahn field enters either adjacent ordering by
putting exponent zero in the removed z-slot. -/
def embedRemaining {K : Type*} [Field K] (inner outer : ℕ) :
    HahnSeries (Indices (inner + outer)) K →+*
      HahnSeries (Indices ((inner + 1) + outer)) K :=
  HahnSeries.embDomainRingHom (zeroInsert inner outer)
    (insertEmbedding inner outer 0).injective (insertIndex_le_iff inner outer 0)

variable {Γ Δ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ] [Field K]

/-- Compatibility for a translated subgroup fiber. The proof compares actual
finite Hahn convolution antidiagonals, including their support conditions. -/
theorem pullFiber_mul (f : Γ ↪o Δ) (ft : Γ ↪o Δ)
    (hadd : ∀ g h, f g + ft h = ft (g + h))
    (A : HahnSeries Γ K) (F : HahnSeries Δ K) :
    pullFiber ft (HahnSeries.embDomain f A * F) = A * pullFiber ft F := by
  classical
  ext g
  simp only [pullFiber_coeff, HahnSeries.coeff_mul]
  symm
  trans ∑ ij ∈ (Finset.antidiagonal A.isPWO_support
      (pullFiber ft F).isPWO_support g).map
      (f.toEmbedding.prodMap ft.toEmbedding),
    (HahnSeries.embDomain f A).coeff ij.1 * F.coeff ij.2
  · simp
  apply Finset.sum_subset
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_map, Finset.mem_antidiagonal,
      Function.Embedding.coe_prodMap, HahnSeries.mem_support, Prod.exists] at hij
    obtain ⟨i, j, ⟨hi, hj, hij⟩, rfl, rfl⟩ := hij
    apply Finset.mem_antidiagonal.mpr
    change (HahnSeries.embDomain f A).coeff (f i) ≠ 0 ∧ F.coeff (ft j) ≠ 0 ∧
      f i + ft j = ft g
    rw [HahnSeries.embDomain_coeff]
    exact ⟨hi, hj, (hadd i j).trans (congrArg ft hij)⟩
  · rintro ⟨i, j⟩ hfull hnot
    by_contra hnonzero
    obtain ⟨i', hi', rfl⟩ := HahnSeries.support_embDomain_subset
      (ne_zero_and_ne_zero_of_mul hnonzero).1
    have hsum : f i' + j = ft g := (Finset.mem_antidiagonal.mp hfull).2.2
    have hj : j = ft (g - i') := by
      apply add_left_cancel (a := f i')
      rw [hsum, hadd]
      congr 1
      abel
    subst j
    apply hnot
    apply Finset.mem_map.mpr
    refine ⟨(i', g - i'), ?_, rfl⟩
    apply Finset.mem_antidiagonal.mpr
    exact ⟨hi', (ne_zero_and_ne_zero_of_mul hnonzero).2, by
      rw [add_comm i', sub_add_cancel]⟩

/-- Full-order residue is linear over the remaining Hahn field. In particular
the scalar may contain arbitrary pre/post spectator denominators. -/
theorem residue_mul_remaining (inner outer : ℕ)
    (A : HahnSeries (Indices (inner + outer)) K)
    (F : HahnSeries (Indices ((inner + 1) + outer)) K) :
    residue inner outer (embedRemaining inner outer A * F) =
      A * residue inner outer F := by
  exact pullFiber_mul (insertEmbedding inner outer 0) (insertEmbedding inner outer (-1))
    (insertIndex_add inner outer (-1)) A F

end CollisionRationalExpansions.HahnFiberScalar
end

section
namespace CollisionRationalExpansions.HahnSlotCoordinates
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.HahnFiberResidue
set_option backward.isDefEq.respectTransparency false

def splitIndex (inner : ℕ) : (outer : ℕ) →
    Indices ((inner + 1) + outer) → ℤ × Indices (inner + outer)
  | 0, g => ofLex g
  | outer + 1, g =>
    let p := splitIndex inner outer (ofLex g).2
    (p.1, toLex ((ofLex g).1, p.2))

theorem splitIndex_insert (inner outer : ℕ) (t : ℤ) (g : Indices (inner + outer)) :
    splitIndex inner outer (insertIndex inner outer t g) = (t, g) := by
  induction outer with
  | zero => rfl
  | succ outer ih =>
    simp only [insertIndex, splitIndex, ofLex_toLex, ih]
    rfl

theorem insert_splitIndex (inner outer : ℕ) (g : Indices ((inner + 1) + outer)) :
    insertIndex inner outer (splitIndex inner outer g).1 (splitIndex inner outer g).2 = g := by
  induction outer with
  | zero => rfl
  | succ outer ih =>
    change toLex ((ofLex g).1,
      insertIndex inner outer (splitIndex inner outer (ofLex g).2).1
        (splitIndex inner outer (ofLex g).2).2) = g
    rw [ih]
    rfl

theorem insertIndex_add_general (inner outer : ℕ) (t u : ℤ)
    (g h : Indices (inner + outer)) :
    insertIndex inner outer (t + u) (g + h) =
      insertIndex inner outer t g + insertIndex inner outer u h := by
  induction outer with
  | zero => rfl
  | succ outer ih =>
    change toLex ((ofLex g).1 + (ofLex h).1,
      insertIndex inner outer (t + u) ((ofLex g).2 + (ofLex h).2)) = _
    rw [ih]
    rfl

def joinIndex (inner outer : ℕ) :
    (ℤ × Indices (inner + outer)) ≃+ Indices ((inner + 1) + outer) where
  toFun p := insertIndex inner outer p.1 p.2
  invFun := splitIndex inner outer
  left_inv p := splitIndex_insert inner outer p.1 p.2
  right_inv g := insert_splitIndex inner outer g
  map_add' p q := insertIndex_add_general inner outer p.1 q.1 p.2 q.2

end CollisionRationalExpansions.HahnSlotCoordinates

namespace CollisionRationalExpansions.FullOrderSpectatorPole
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.HahnFiberScalar CollisionRationalExpansions.HahnSlotCoordinates
set_option backward.isDefEq.respectTransparency false

/-- Insert the first of two adjacent variables while retaining the second.
The arbitrary suffix remains the outer lex block. -/
def firstInsert (pre : ℕ) : (post : ℕ) → ℤ →
    Indices ((pre + 1) + post) → Indices ((pre + 2) + post)
  | 0, t, g => toLex ((ofLex g).1, toLex (t, (ofLex g).2))
  | post + 1, t, g => toLex ((ofLex g).1, firstInsert pre post t (ofLex g).2)

theorem firstInsert_le_iff (pre post : ℕ) (t : ℤ)
    (g h : Indices ((pre + 1) + post)) :
    firstInsert pre post t g ≤ firstInsert pre post t h ↔ g ≤ h := by
  induction post with
  | zero =>
    change (toLex ((ofLex g).1, toLex (t, (ofLex g).2)) : ℤ ×ₗ (ℤ ×ₗ Indices pre)) ≤
      toLex ((ofLex h).1, toLex (t, (ofLex h).2)) ↔ (show ℤ ×ₗ Indices pre from g) ≤ h
    rw [Prod.Lex.le_iff, Prod.Lex.le_iff]
    simp only [ofLex_toLex]
    rw [Prod.Lex.le_iff]
    simp
  | succ post ih =>
    change (toLex ((ofLex g).1, firstInsert pre post t (ofLex g).2) :
      ℤ ×ₗ Indices ((pre + 2) + post)) ≤
      toLex ((ofLex h).1, firstInsert pre post t (ofLex h).2) ↔
      (show ℤ ×ₗ Indices ((pre + 1) + post) from g) ≤ h
    rw [Prod.Lex.le_iff, Prod.Lex.le_iff]
    simp only [ofLex_toLex, ih]
    rfl

def firstEmbedding (pre post : ℕ) (t : ℤ) :
    Indices ((pre + 1) + post) ↪o Indices ((pre + 2) + post) :=
  OrderEmbedding.ofMapLEIff (firstInsert pre post t) (firstInsert_le_iff pre post t)

def firstValue (pre : ℕ) : (post : ℕ) → Indices ((pre + 2) + post) → ℤ
  | 0, g => (ofLex (ofLex g).2).1
  | post + 1, g => firstValue pre post (ofLex g).2

theorem firstValue_insert (pre post : ℕ) (t : ℤ) (g : Indices ((pre + 1) + post)) :
    firstValue pre post (firstInsert pre post t g) = t := by
  induction post with
  | zero => rfl
  | succ post ih => exact ih _

theorem adjacent_insertions (pre post : ℕ) (a b : ℤ) (g : Indices (pre + post)) :
    firstInsert pre post a (insertIndex pre post b g) =
      insertIndex (pre + 1) post b (insertIndex pre post a g) := by
  induction post with
  | zero => rfl
  | succ post ih =>
    change toLex ((ofLex g).1, firstInsert pre post a (insertIndex pre post b (ofLex g).2)) = _
    rw [ih]
    rfl

/-- An arbitrary supported rational spectator-pole expansion independent of x
has the same z-residue in pre,z,x,post and pre,x,z,post. This compares the full
orders, with no projection of spectators before division. -/
theorem nonadjacent_pole_residue_cancel {K : Type*} [Field K] (pre post : ℕ)
    (F : HahnSeries (Indices ((pre + 1) + post)) K) :
    pullFiber (firstEmbedding pre post (-1))
      (HahnSeries.embDomain (insertEmbedding (pre + 1) post 0) F) =
    residue (pre + 1) post (HahnSeries.embDomain (firstEmbedding pre post 0) F) := by
  classical
  ext g
  let t := (splitIndex pre post g).1
  let h := (splitIndex pre post g).2
  have hg : g = insertIndex pre post t h := (insert_splitIndex pre post g).symm
  rw [hg]
  change (HahnSeries.embDomain (insertEmbedding (pre + 1) post 0) F).coeff
      (firstInsert pre post (-1) (insertIndex pre post t h)) =
    (HahnSeries.embDomain (firstEmbedding pre post 0) F).coeff
      (insertIndex (pre + 1) post (-1) (insertIndex pre post t h))
  conv_lhs => rw [adjacent_insertions pre post (-1) t]
  conv_rhs => rw [← adjacent_insertions pre post t (-1)]
  by_cases ht : t = 0
  · rw [ht]
    change (HahnSeries.embDomain (insertEmbedding (pre + 1) post 0) F).coeff
      (insertEmbedding (pre + 1) post 0 (insertIndex pre post (-1) h)) =
      (HahnSeries.embDomain (firstEmbedding pre post 0) F).coeff
        (firstEmbedding pre post 0 (insertIndex pre post (-1) h))
    rw [HahnSeries.embDomain_coeff, HahnSeries.embDomain_coeff]
  · rw [HahnSeries.embDomain_of_notMem_range, HahnSeries.embDomain_of_notMem_range]
    · rintro ⟨a, ha⟩
      have hv := congrArg (firstValue pre post) ha
      exact ht ((firstValue_insert pre post 0 a).symm.trans
        (hv.trans (firstValue_insert pre post t _))).symm
    · rintro ⟨a, ha⟩
      have hv := congrArg (fun b => (splitIndex (pre + 1) post b).1) ha
      exact ht ((congrArg Prod.fst (splitIndex_insert (pre + 1) post 0 a)).symm.trans
        (hv.trans (congrArg Prod.fst (splitIndex_insert (pre + 1) post t _)))).symm

end CollisionRationalExpansions.FullOrderSpectatorPole
end

section
/- Cancellation of a nonadjacent spectator factor after full-order expansion,
with arbitrary coefficients in x and every retained spectator. -/
namespace CollisionRationalExpansions.FullOrderSpectatorScalar
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.HahnFiberScalar CollisionRationalExpansions.FullOrderSpectatorPole
set_option backward.isDefEq.respectTransparency false

theorem firstInsert_add (pre post : ℕ) (t : ℤ)
    (g h : Indices ((pre + 1) + post)) :
    firstInsert pre post 0 g + firstInsert pre post t h =
      firstInsert pre post t (g + h) := by
  induction post with
  | zero =>
    change toLex ((ofLex g).1 + (ofLex h).1,
      toLex (0 + t, (ofLex g).2 + (ofLex h).2)) = _
    simp only [zero_add]
    rfl
  | succ post ih =>
    change toLex ((ofLex g).1 + (ofLex h).1,
      firstInsert pre post 0 (ofLex g).2 + firstInsert pre post t (ofLex h).2) = _
    rw [ih]
    rfl

theorem firstInsert_zero (pre post : ℕ) : firstInsert pre post 0 0 = 0 := by
  induction post with
  | zero => rfl
  | succ post ih =>
    change toLex (0, firstInsert pre post 0 0) = 0
    rw [ih]
    rfl

def firstZeroInsert (pre post : ℕ) :
    Indices ((pre + 1) + post) →+ Indices ((pre + 2) + post) where
  toFun := firstInsert pre post 0
  map_zero' := firstInsert_zero pre post
  map_add' g h := (firstInsert_add pre post 0 g h).symm

def firstEmbed {K : Type*} [Field K] (pre post : ℕ) :
    HahnSeries (Indices ((pre + 1) + post)) K →+*
      HahnSeries (Indices ((pre + 2) + post)) K :=
  HahnSeries.embDomainRingHom (firstZeroInsert pre post)
    (firstEmbedding pre post 0).injective (firstInsert_le_iff pre post 0)

variable {K : Type*} [Field K]

theorem first_residue_mul_remaining (pre post : ℕ)
    (A : HahnSeries (Indices ((pre + 1) + post)) K)
    (F : HahnSeries (Indices ((pre + 2) + post)) K) :
    pullFiber (firstEmbedding pre post (-1)) (firstEmbed pre post A * F) =
      A * pullFiber (firstEmbedding pre post (-1)) F :=
  pullFiber_mul (firstEmbedding pre post 0) (firstEmbedding pre post (-1))
    (firstInsert_add pre post (-1)) A F

/-- `F` is an actual full-order expansion in pre,z,post of a rational
spectator pole (or any series independent of x); `A` is the full fused-order
expansion in pre,x,post of its rational coefficient. Both products are formed
in their true full orders before any residue coefficient is extracted. -/
theorem nonadjacent_spectator_factor_cancel (pre post : ℕ)
    (A F : HahnSeries (Indices ((pre + 1) + post)) K) :
    pullFiber (firstEmbedding pre post (-1))
      (firstEmbed pre post A * embedRemaining (pre + 1) post F) -
    residue (pre + 1) post
      (embedRemaining (pre + 1) post A * firstEmbed pre post F) = 0 := by
  rw [first_residue_mul_remaining, residue_mul_remaining]
  change A * pullFiber (firstEmbedding pre post (-1))
      (HahnSeries.embDomain (insertEmbedding (pre + 1) post 0) F) -
    A * residue (pre + 1) post (HahnSeries.embDomain (firstEmbedding pre post 0) F) = 0
  rw [nonadjacent_pole_residue_cancel, sub_self]

end CollisionRationalExpansions.FullOrderSpectatorScalar
end

end D5.S3.VertexAlgebra
