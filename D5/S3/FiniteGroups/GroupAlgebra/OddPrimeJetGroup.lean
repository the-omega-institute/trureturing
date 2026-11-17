/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.SemidirectProduct]
   utility: none
   digest: Coherent original-label lifts and the full odd-prime jet automorphism group. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
import D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! The full group retains the original labels and all prime-field-linear operators. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup
open Polynomial Module OddPrimeJetDeformation OddPrimeJetDerivationRigidity
open OddPrimeJetPairClassification OddPrimeJetCommutant FiniteJetClassification FiniteJetCoefficients
open scoped BigOperators
universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Algebra (ZMod p) K]
local notation "𝔽" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "E" => Multiplicative K
local notation "D" => derivativeEnd (p := p) (K := K)
local instance : NeZero (p-1) := ⟨by have hp : 2 < p := Fact.out; omega⟩

/-- Pairs of actual invertible 𝔽-linear operators and arbitrary original labels. -/
def originalGroup (q : K →ₗ[𝔽] K) : Subgroup ((V ≃ₗ[𝔽] V) × (E ≃* E)) where
  carrier := {z | ∀ g v, z.1 (originalRepresentation q g v) =
    originalRepresentation q (z.2 g) (z.1 v)}
  one_mem' := by intro g v; rfl
  mul_mem' := by
    intro x y hx hy g v
    change x.1 (y.1 (originalRepresentation q g v)) = _
    rw [hy, hx]
    rfl
  inv_mem' := by
    intro x hx g v
    apply x.1.injective
    change x.1 (x.1.symm (originalRepresentation q g v)) =
      x.1 (originalRepresentation q (x.2.symm g) (x.1.symm v))
    rw [LinearEquiv.apply_symm_apply, hx, MulEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]

/-- Projection retains the actual original additive-group automorphism. -/
def labelProjection (q : K →ₗ[𝔽] K) : originalGroup q →* (E ≃* E) :=
  (MonoidHom.snd _ _).comp (originalGroup q).subtype

/-- The actual labels occurring in original intertwiner pairs. -/
def labelGroup (q : K →ₗ[𝔽] K) : Subgroup (E ≃* E) := (labelProjection q).range

def project (q : K →ₗ[𝔽] K) : originalGroup q →* labelGroup q :=
  (labelProjection q).rangeRestrict

variable [Fintype K] {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n)
variable (A : Fin (n - 1) → K)
local notation "q" => Q (p := p) n A
local notation "𝒮" => labelGroup q

include hn hK in
private theorem label_data (g : 𝒮) :
    ∃ (c : Kˣ) (σ : K ≃ₐ[𝔽] K),
      (∀ a : K, Multiplicative.toAdd (g.val (Multiplicative.ofAdd a)) = (c : K)*σ a) ∧
      ∀ i, A i = ((c⁻¹ : Kˣ) : K) ^ weight p n i * σ (A i) := by
  obtain ⟨z, hz⟩ := g.property
  apply (fixed_automorphism_coefficients_iff hn hK A A g.val).mp
  refine ⟨z.val.1, ?_⟩
  intro a v
  have h := z.property a v
  change labelProjection q z = g.val at hz
  change z.val.2 = g.val at hz
  simpa only [hz] using h

def labelScalar (g : 𝒮) : Kˣ := (label_data hn hK A g).choose
def labelSigma (g : 𝒮) : K ≃ₐ[𝔽] K := (label_data hn hK A g).choose_spec.choose
theorem label_formula (g : 𝒮) (a : K) :
    Multiplicative.toAdd (g.val (Multiplicative.ofAdd a)) =
      (labelScalar hn hK A g : K) * labelSigma hn hK A g a :=
  (label_data hn hK A g).choose_spec.choose_spec.1 a
private theorem label_fixed (g : 𝒮) (i : Fin (n-1)) :
    A i = (((labelScalar hn hK A g)⁻¹ : Kˣ) : K) ^ weight p n i *
      labelSigma hn hK A g (A i) :=
  (label_data hn hK A g).choose_spec.choose_spec.2 i

private theorem labelScalar_one : (labelScalar hn hK A 1 : K) = 1 := by
  simpa using (label_formula hn hK A 1 1).symm
private theorem labelSigma_one : labelSigma hn hK A 1 = 1 := by
  ext a
  have h := label_formula hn hK A 1 a
  simpa [labelScalar_one hn hK A] using h.symm
private theorem labelScalar_mul (g h : 𝒮) :
    (labelScalar hn hK A (g*h) : K) =
      (labelScalar hn hK A g : K) * labelSigma hn hK A g (labelScalar hn hK A h) := by
  calc
    (labelScalar hn hK A (g*h) : K) =
        Multiplicative.toAdd (g.val (h.val (Multiplicative.ofAdd 1))) := by
      simpa using (label_formula hn hK A (g*h) 1).symm
    _ = (labelScalar hn hK A g : K) * labelSigma hn hK A g
        (Multiplicative.toAdd (h.val (Multiplicative.ofAdd 1))) :=
      label_formula hn hK A g _
    _ = _ := by rw [label_formula hn hK A h 1]; simp

private theorem labelSigma_mul (g h : 𝒮) :
    labelSigma hn hK A (g*h) = labelSigma hn hK A g * labelSigma hn hK A h := by
  ext a
  apply mul_left_cancel₀ (labelScalar hn hK A (g*h)).ne_zero
  rw [← label_formula, labelScalar_mul]
  have H := label_formula hn hK A g
    (Multiplicative.toAdd (h.val (Multiplicative.ofAdd a)))
  change Multiplicative.toAdd (g.val (h.val (Multiplicative.ofAdd a))) = _ at H
  rw [label_formula hn hK A h a, map_mul] at H
  change Multiplicative.toAdd (g.val (h.val (Multiplicative.ofAdd a))) =
    (labelScalar hn hK A g : K) * labelSigma hn hK A g (labelScalar hn hK A h) *
      labelSigma hn hK A g (labelSigma hn hK A h a)
  simpa only [mul_assoc] using H

/-- The degree lift acts on the actual polynomial carrier, in K's original universe. -/
def degreeLift (g : 𝒮) : V ≃ₗ[𝔽] V :=
  (coefficientAutomorphism (labelSigma hn hK A g)).trans
    ((diagonalScale (labelScalar hn hK A g : K)⁻¹
      (inv_ne_zero (labelScalar hn hK A g).ne_zero)).restrictScalars 𝔽)

private theorem degreeLift_coeff (g : 𝒮) (v : V) (i : Fin p) :
    (degreeLift hn hK A g v : K[X]).coeff i =
      (labelScalar hn hK A g : K)⁻¹ ^ i.val *
        labelSigma hn hK A g ((v : K[X]).coeff i) := by
  change (diagonalScale (labelScalar hn hK A g : K)⁻¹
    (inv_ne_zero (labelScalar hn hK A g).ne_zero)
    (coefficientAutomorphism (labelSigma hn hK A g) v) : K[X]).coeff i = _
  rw [diagonalScale_coeff, coefficientAutomorphism_coeff]

private theorem degreeLift_one : degreeLift hn hK A 1 = 1 := by
  ext v : 1
  apply (degreeLTEquiv K p).injective
  funext i
  change (degreeLift hn hK A 1 v : K[X]).coeff i = (v : K[X]).coeff i
  rw [degreeLift_coeff, labelScalar_one, labelSigma_one]
  simp

private theorem degreeLift_mul (g h : 𝒮) :
    degreeLift hn hK A (g*h) = degreeLift hn hK A g * degreeLift hn hK A h := by
  ext v : 1
  apply (degreeLTEquiv K p).injective
  funext i
  change (degreeLift hn hK A (g*h) v : K[X]).coeff i =
    (degreeLift hn hK A g (degreeLift hn hK A h v) : K[X]).coeff i
  simp only [degreeLift_coeff, labelScalar_mul, labelSigma_mul,
    AlgEquiv.mul_apply, mul_inv_rev, mul_pow, map_mul, map_pow, map_inv₀]
  ring

/-- A single fixed shear, rather than independently chosen intertwiners. -/
def canonicalShear : V ≃ₗ[𝔽] V :=
  (shear (p := p) (-(∑ i, A i))).restrictScalars 𝔽

/-- Conjugating the genuine degree action kills the groupoid cocycle. -/
def coherentLift (g : 𝒮) : V ≃ₗ[𝔽] V :=
  (canonicalShear A).trans ((degreeLift hn hK A g).trans (canonicalShear A).symm)

private theorem coherentLift_one : coherentLift hn hK A 1 = 1 := by
  ext v
  simp [coherentLift, degreeLift_one]

private theorem coherentLift_mul (g h : 𝒮) :
    coherentLift hn hK A (g*h) = coherentLift hn hK A g * coherentLift hn hK A h := by
  ext v
  simp [coherentLift, degreeLift_mul]

private theorem normalized_relation (g : 𝒮) (a : K) :
    q ((labelScalar hn hK A g : K) * labelSigma hn hK A g a) +
      (∑ i, A i) * ((labelScalar hn hK A g : K) * labelSigma hn hK A g a) =
    (labelScalar hn hK A g : K)^(p-1) *
      labelSigma hn hK A g (q a + (∑ i, A i)*a) := by
  have hc := (scalar_coefficients_iff A A (labelScalar hn hK A g)
    (labelSigma hn hK A g)).mpr (label_fixed hn hK A g)
  have he (x : K) : q x + (∑ i, A i)*x =
      ∑ i, A i * x^(p^(i.val+1)) := by
    simp only [Q, coefficientMap_apply, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, he, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow, map_mul, map_pow]
  calc
    _ = ((labelScalar hn hK A g : K)^(p^(i.val+1)) * A i) *
        (labelSigma hn hK A g a)^(p^(i.val+1)) := by ring
    _ = _ := by rw [hc]; ring

private theorem degreeLift_operator (g : 𝒮) (x y : K) (v : V) :
    degreeLift hn hK A g (x • D v + y • (D^(p-1)) v) =
      ((labelScalar hn hK A g : K)*labelSigma hn hK A g x) •
        D (degreeLift hn hK A g v) +
      ((labelScalar hn hK A g : K)^(p-1)*labelSigma hn hK A g y) •
        (D^(p-1)) (degreeLift hn hK A g v) := by
  simp only [degreeLift, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [map_add, coefficientAutomorphism_smul, coefficientAutomorphism_smul,
    coefficientAutomorphism_derivative,
    OddPrimeJetPairClassification.commutes_pow _ (coefficientAutomorphism_derivative _)]
  rw [map_add, map_smul, map_smul, diagonalScale_derivative, diagonalScale_pow,
    smul_smul, smul_smul, inv_inv]
  congr 1 <;> congr 1 <;> simp [inv_pow, mul_comm]

/-- The coherent lift intertwines all actual original representation operators. -/
theorem coherentLift_intertwines (g : 𝒮) (a : E) (v : V) :
    coherentLift hn hK A g (originalRepresentation q a v) =
      originalRepresentation q (g.val a) (coherentLift hn hK A g v) := by
  apply finiteExp_intertwining (coherentLift hn hK A g).toLinearMap
    (jetOperator q (Multiplicative.toAdd a))
    (jetOperator q (automorphismLinear (p := p) g.val (Multiplicative.toAdd a)))
  intro w
  apply (canonicalShear A).injective
  change canonicalShear A ((canonicalShear A).symm
      (degreeLift hn hK A g (canonicalShear A (jetOperator q (Multiplicative.toAdd a) w)))) =
    canonicalShear A (jetOperator q (automorphismLinear (p := p) g.val (Multiplicative.toAdd a))
      ((canonicalShear A).symm (degreeLift hn hK A g (canonicalShear A w))))
  rw [LinearEquiv.apply_symm_apply]
  have hs (x : K) (z : V) : canonicalShear A (jetOperator q x z) =
      x • D (canonicalShear A z) +
        (q x + (∑ i, A i)*x) • (D^(p-1)) (canonicalShear A z) := by
    simpa only [canonicalShear, LinearEquiv.restrictScalars_apply, jetOperator,
      LinearMap.add_apply, LinearMap.smul_apply, neg_mul, sub_neg_eq_add] using
        shear_operator (-(∑ i, A i)) x (q x) z
  rw [hs, degreeLift_operator, hs]
  simp only [coherentLift, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [show automorphismLinear (p := p) g.val (Multiplicative.toAdd a) =
      (labelScalar hn hK A g : K) * labelSigma hn hK A g (Multiplicative.toAdd a) from
        label_formula hn hK A g _]
  rw [normalized_relation]

/-- A genuine homomorphism section of the actual original-label projection. -/
def sectionHom : 𝒮 →* originalGroup q where
  toFun g := ⟨(coherentLift hn hK A g, g.val), coherentLift_intertwines hn hK A g⟩
  map_one' := by
    apply Subtype.ext
    exact Prod.ext (coherentLift_one hn hK A) rfl
  map_mul' g h := by
    apply Subtype.ext
    exact Prod.ext (coherentLift_mul hn hK A g h) rfl

@[simp] theorem project_section (g : 𝒮) :
    project q (sectionHom hn hK A g) = g := rfl

/-- The kernel consists of actual commutant units, as a subgroup of original pairs. -/
abbrev commutantUnits := (project q).ker

/-- Conjugation by the coherent section on the full, unrestricted kernel. -/
def kernelAction : 𝒮 →* MulAut (commutantUnits (p := p) A) :=
  (project q).ker.normalizerMonoidHom.comp
    ((sectionHom hn hK A).codRestrict (Subgroup.normalizer ((project q).ker : Set (originalGroup q))) (by
      intro g
      rw [Subgroup.normalizer_eq_top]
      trivial))

private def factorHom : commutantUnits (p := p) A ⋊[kernelAction hn hK A] 𝒮 →* originalGroup q :=
  SemidirectProduct.lift (project q).ker.subtype (sectionHom hn hK A) (by
    intro g
    apply MonoidHom.ext
    intro x
    rfl)

private theorem factorHom_bijective : Function.Bijective (factorHom hn hK A) := by
  constructor
  · intro x y hxy
    have hr : x.right = y.right := by
      have h := congrArg (project q) hxy
      simpa [factorHom, SemidirectProduct.lift, map_mul,
        (show project q x.left.val = 1 from x.left.property),
        (show project q y.left.val = 1 from y.left.property)] using h
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change x.left.val = y.left.val
      change x.left.val * sectionHom hn hK A x.right =
        y.left.val * sectionHom hn hK A y.right at hxy
      rw [hr] at hxy
      exact mul_right_cancel hxy
    · exact hr
  · intro z
    let k : commutantUnits (p := p) A := ⟨z * (sectionHom hn hK A (project q z))⁻¹, by
      change project q (z * (sectionHom hn hK A (project q z))⁻¹) = 1
      simp⟩
    refine ⟨⟨k, project q z⟩, ?_⟩
    change (z * (sectionHom hn hK A (project q z))⁻¹) *
      sectionHom hn hK A (project q z) = z
    group

/-- Every actual pair has a unique kernel-times-section decomposition. -/
theorem unique_factorization (z : originalGroup q) :
    ∃! x : commutantUnits (p := p) A × 𝒮,
      x.1.val * sectionHom hn hK A x.2 = z := by
  obtain ⟨x, hx⟩ := (factorHom_bijective hn hK A).surjective z
  refine ⟨(x.left, x.right), hx, ?_⟩
  rintro ⟨k, s⟩ he
  have h : (⟨k,s⟩ : commutantUnits (p := p) A ⋊[kernelAction hn hK A] 𝒮) = x :=
    (factorHom_bijective hn hK A).injective (he.trans hx.symm)
  exact congrArg (fun t : commutantUnits (p := p) A ⋊[kernelAction hn hK A] 𝒮 => (t.left,t.right)) h

/-- The full original-pair group, not merely its scalar or label quotient. -/
def semidirectEquiv : originalGroup q ≃* commutantUnits (p := p) A ⋊[kernelAction hn hK A] 𝒮 :=
  (MulEquiv.ofBijective (factorHom hn hK A) (factorHom_bijective hn hK A)).symm

include hn hK in
/-- The full group count includes the actual label stabilizer. -/
theorem full_card_factorization :
    Nat.card (originalGroup q) = Nat.card (commutantUnits (p := p) A) * Nat.card 𝒮 := by
  rw [Nat.card_congr (semidirectEquiv hn hK A).toEquiv,
    Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]

private abbrev UnitCoordinates :=
  {c : Fin p → K // c 0 = 0 ∧ c (leadingIndex (p := p)) ≠ 0} × (K →ₗ[𝔽] K)

private def kernelOfCoordinates (x : UnitCoordinates (p := p) (K := K)) :
    commutantUnits (p := p) A := by
  let f := toeplitzDegree (p := p) x.1.val x.2
  have hf : IsUnit f := (toeplitzDegree_isUnit_iff _ _).mpr x.1.property.2
  let P := LinearMap.GeneralLinearGroup.toLinearEquiv hf.unit
  have hP : P.toLinearMap = f := by
    change (hf.unit : V →ₗ[𝔽] V) = f
    exact hf.unit_spec
  refine ⟨⟨(P, 1), ?_⟩, rfl⟩
  intro g v
  change P.toLinearMap (originalRepresentation q g v) = originalRepresentation q g (P.toLinearMap v)
  rw [hP]
  exact (actual_commutant_normal_form q (coefficientMap (p := p) n A).property f).mpr
    ⟨x.1.val, x.2, x.1.property.1, rfl⟩ g v

private theorem kernelOfCoordinates_bijective :
    Function.Bijective (kernelOfCoordinates (p := p) A) := by
  have hmap (x : UnitCoordinates (p := p) (K := K)) :
      (kernelOfCoordinates A x).val.val.1.toLinearMap = toeplitzDegree x.1.val x.2 := by
    exact ((toeplitzDegree_isUnit_iff x.1.val x.2).mpr x.1.property.2).unit_spec
  constructor
  · intro x y h
    have hh := congrArg (fun z : commutantUnits (p := p) A => z.val.val.1.toLinearMap) h
    rw [hmap, hmap] at hh
    have he := toeplitzDegree_injective _ _ x.1.property.1 y.1.property.1 _ _ hh
    exact Prod.ext (Subtype.ext he.1) he.2
  · intro z
    have hz : z.val.val.2 = 1 := congrArg Subtype.val z.property
    have hc : commutesOriginal q z.val.val.1.toLinearMap := by
      intro g v
      have H := z.val.property g v
      rw [hz] at H
      exact H
    obtain ⟨c,T,hc0,he⟩ :=
      (actual_commutant_normal_form q (coefficientMap (p := p) n A).property _).mp hc
    have hu : IsUnit z.val.val.1.toLinearMap :=
      ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv z.val.val.1, rfl⟩
    have hlead : c (leadingIndex (p := p)) ≠ 0 :=
      (toeplitzDegree_isUnit_iff c T).mp (he ▸ hu)
    refine ⟨(⟨c, hc0, hlead⟩,T), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply LinearEquiv.toLinearMap_injective
      exact (hmap _).trans he.symm
    · exact hz.symm

private def scalarCoordinatesEquiv :
    {c : Fin p → K // c 0 = 0 ∧ c (leadingIndex (p := p)) ≠ 0} ≃
      {a : K // a ≠ 0} × (Fin (p-2) → K) where
  toFun c := (⟨c.val (leadingIndex (p := p)), c.property.2⟩,
    fun i => c.val ⟨i.val+1, by have hp : 2 < p := Fact.out; omega⟩)
  invFun x := ⟨fun j => if hj0 : j = 0 then 0 else if hjt : j = leadingIndex (p := p) then x.1.val
    else x.2 ⟨j.val-1, by
      have hp : 2 < p := Fact.out
      have hj := j.isLt
      have h0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      have ht : j.val ≠ p-1 := fun h => hjt (Fin.ext h)
      omega⟩, by
    constructor
    · simp
    · have ht : leadingIndex (p := p) ≠ (0 : Fin p) := by
        intro h
        have hp : 2 < p := Fact.out
        have := congrArg Fin.val h
        simp only [leadingIndex, Fin.val_zero] at this
        omega
      simpa [ht] using x.1.property⟩
  left_inv c := by
    apply Subtype.ext
    funext j
    dsimp
    split_ifs with h0 ht
    · simpa only [h0] using c.property.1.symm
    · exact congrArg c.val ht.symm
    · apply congrArg c.val
      apply Fin.ext
      have hj : j.val ≠ 0 := fun h => h0 (Fin.ext h)
      simp only [Fin.val_mk]
      omega
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      split_ifs with h
      · have hp : 2 < p := Fact.out
        have := congrArg Fin.val h
        simp only [leadingIndex, Fin.val_zero] at this
        omega
      · rfl
      · contradiction
    · funext i
      have h0 : (⟨i.val+1, by have hp : 2 < p := Fact.out; omega⟩ : Fin p) ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      have ht : (⟨i.val+1, by have hp : 2 < p := Fact.out; omega⟩ : Fin p) ≠
          leadingIndex (p := p) := by
        intro h
        have hi := i.isLt
        have := congrArg Fin.val h
        dsimp [leadingIndex] at this
        omega
      dsimp
      simp [h0, ht]

include hn hK in
/-- Every unrestricted 𝔽-linear top map contributes n squared prime-field coordinates. -/
theorem commutant_cardinality :
    Nat.card (commutantUnits (p := p) A) = (p^n-1)*p^(n*(p-2)+n*n) := by
  let e : commutantUnits (p := p) (n := n) A ≃ UnitCoordinates (p := p) (K := K) :=
    (Equiv.ofBijective (kernelOfCoordinates (p := p) (n := n) A)
      (kernelOfCoordinates_bijective (p := p) (n := n) A)).symm
  have hdim : finrank 𝔽 K = n :=
    Nat.pow_right_injective (Fact.out : p.Prime).one_lt
      ((FiniteField.pow_finrank_eq_card p K).trans hK)
  have htop : Nat.card (K →ₗ[𝔽] K) = p^(n*n) := by
    rw [Module.natCard_eq_pow_finrank (K := 𝔽),
      Module.finrank_linearMap (R := 𝔽) (S := 𝔽), hdim,
      Nat.card_eq_fintype_card (α := 𝔽), ZMod.card]
  have hunit : Nat.card {a : K // a ≠ 0} = p^n-1 := by
    rw [Nat.card_congr (unitsEquivNeZero (G₀ := K)).symm,
      Nat.card_units, Nat.card_eq_fintype_card (α := K), hK]
  have hscalar : Nat.card {c : Fin p → K // c 0 = 0 ∧ c (leadingIndex (p := p)) ≠ 0} =
      (p^n-1)*(p^n)^(p-2) := by
    rw [Nat.card_congr (scalarCoordinatesEquiv (p := p) (K := K) (n := n)),
      Nat.card_prod, hunit, Nat.card_fun, Nat.card_fin (p-2),
      Nat.card_eq_fintype_card (α := K), hK]
  calc
    _ = Nat.card (UnitCoordinates (p := p) (K := K)) := Nat.card_congr e
    _ = ((p^n-1)*(p^n)^(p-2))*p^(n*n) := by
      rw [Nat.card_prod, hscalar, htop]
    _ = _ := by rw [← Nat.pow_mul, Nat.pow_add, Nat.mul_assoc]

include hn hK in
/-- The true full-group count includes its entire weighted label stabilizer. -/
theorem full_cardinality :
    Nat.card (originalGroup q) = (p^n-1)*p^(n*(p-2)+n*n)*Nat.card 𝒮 := by
  rw [full_card_factorization hn hK A, commutant_cardinality hn hK A]

section WeightedTransport
variable {L : Type} [Field L] [Fintype L] [Algebra (ZMod p) L]
variable (e : K ≃ₐ[ZMod p] L)

private def originalLabelMap : WeightedSemilinear.Group (ZMod p) L →* (E ≃* E) where
  toFun g := parameterAutomorphism (Units.map e.symm.toMonoidHom g.left)
    (e.trans (g.right.trans e.symm))
  map_one' := by
    ext x
    apply Multiplicative.toAdd.injective
    change e.symm (1 : L) * e.symm (e (Multiplicative.toAdd x)) = Multiplicative.toAdd x
    simp
  map_mul' g h := by
    ext x
    apply Multiplicative.toAdd.injective
    change e.symm ((g*h).left : L) * e.symm ((g*h).right (e (Multiplicative.toAdd x))) =
      e.symm (g.left : L) * e.symm (g.right
        (e (e.symm (h.left : L) * e.symm (h.right (e (Multiplicative.toAdd x))))))
    simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      WeightedSemilinear.unitsAut, map_mul, mul_assoc]

private theorem originalLabelMap_apply (g : WeightedSemilinear.Group (ZMod p) L) (x : K) :
    Multiplicative.toAdd (originalLabelMap e g (Multiplicative.ofAdd x)) =
      e.symm (g.left : L) * e.symm (g.right (e x)) := rfl

private theorem originalLabelMap_injective : Function.Injective (originalLabelMap e) := by
  intro g h he
  have hf (x : K) : e.symm (g.left : L) * e.symm (g.right (e x)) =
      e.symm (h.left : L) * e.symm (h.right (e x)) :=
    congrArg (fun φ : E ≃* E => Multiplicative.toAdd (φ (Multiplicative.ofAdd x))) he
  have hc : g.left = h.left := by
    apply Units.ext
    apply e.symm.injective
    simpa using hf 1
  apply SemidirectProduct.ext hc
  ext x
  apply e.symm.injective
  have H := hf (e.symm x)
  simp only [AlgEquiv.apply_symm_apply, hc] at H
  exact mul_left_cancel₀ (fun h0 => h.left.ne_zero
    (e.symm.injective (h0.trans (map_zero e.symm).symm))) H

/-- The native weighted stabilizer, transported from the original field. -/
def weightedStabilizer : Subgroup (WeightedSemilinear.Group (ZMod p) L) :=
  letI := WeightedSemilinear.weightedAction (F := ZMod p) (K := L) (weight p n);
  MulAction.stabilizer (WeightedSemilinear.Group (ZMod p) L) (fun i => e (A i))

include hn hK in
private theorem weighted_mem (g : WeightedSemilinear.Group (ZMod p) L) :
    g ∈ weightedStabilizer A e ↔ originalLabelMap e g ∈ 𝒮 := by
  constructor
  · intro hg
    change WeightedSemilinear.act (weight p n) g (fun i => e (A i)) =
      (fun i => e (A i)) at hg
    have hi (i : Fin (n-1)) := congrArg (fun B => e.symm (B i)) hg
    have hrel : Intertwines q q (originalLabelMap e g) := by
      apply (fixed_automorphism_coefficients_iff hn hK A A _).mpr
      refine ⟨Units.map e.symm.toMonoidHom g.left, e.trans (g.right.trans e.symm),
        fun _ => rfl, ?_⟩
      intro i
      simpa [WeightedSemilinear.act, map_mul, map_pow] using (hi i).symm
    obtain ⟨P,hP⟩ := hrel
    exact ⟨⟨(P,originalLabelMap e g),hP⟩,rfl⟩
  · intro hg
    let s : 𝒮 := ⟨originalLabelMap e g,hg⟩
    have hf := label_formula hn hK A s
    have hc : (labelScalar hn hK A s : K) = e.symm (g.left : L) := by
      have H := hf 1
      change Multiplicative.toAdd (originalLabelMap e g (Multiplicative.ofAdd 1)) =
        (labelScalar hn hK A s : K) * labelSigma hn hK A s 1 at H
      rw [originalLabelMap_apply e g 1] at H
      simpa only [map_one, mul_one] using H.symm
    have hs (x : K) : labelSigma hn hK A s x = e.symm (g.right (e x)) := by
      apply mul_left_cancel₀ (labelScalar hn hK A s).ne_zero
      rw [← hf, hc]
      rfl
    change WeightedSemilinear.act (weight p n) g (fun i => e (A i)) =
      (fun i => e (A i))
    funext i
    apply e.symm.injective
    have H := label_fixed hn hK A s i
    rw [hs, show (((labelScalar hn hK A s)⁻¹ : Kˣ) : K) =
      (e.symm (g.left : L))⁻¹ from by simpa only [Units.val_inv_eq_inv_val] using congrArg Inv.inv hc] at H
    simpa [WeightedSemilinear.act, map_mul, map_pow, map_inv] using H.symm

/-- A faithful equivalence with the existing native weighted stabilizer. -/
def weightedStabilizerEquiv : weightedStabilizer A e ≃* 𝒮 := by
  let f : weightedStabilizer A e →* 𝒮 :=
    ((originalLabelMap e).comp (weightedStabilizer A e).subtype).codRestrict 𝒮
      (fun g => (weighted_mem hn hK A e g.val).mp g.property)
  apply MulEquiv.ofBijective f
  constructor
  · intro g h he
    apply Subtype.ext
    exact originalLabelMap_injective e (congrArg Subtype.val he)
  · intro s
    let g : WeightedSemilinear.Group (ZMod p) L :=
      ⟨Units.map e.toMonoidHom (labelScalar hn hK A s),
        e.symm.trans ((labelSigma hn hK A s).trans e)⟩
    have he : originalLabelMap e g = s.val := by
      ext x
      apply Multiplicative.toAdd.injective
      change e.symm (g.left : L) * e.symm (g.right (e (Multiplicative.toAdd x))) =
        Multiplicative.toAdd (s.val (Multiplicative.ofAdd (Multiplicative.toAdd x)))
      rw [label_formula hn hK A s]
      simp [g]
    refine ⟨⟨g, (weighted_mem hn hK A e g).mpr (he ▸ s.property)⟩, ?_⟩
    exact Subtype.ext he
end WeightedTransport

private theorem degreeLift_smul (g : 𝒮) (a : K) (v : V) :
    degreeLift hn hK A g (a • v) = labelSigma hn hK A g a • degreeLift hn hK A g v := by
  simp only [degreeLift, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    coefficientAutomorphism_smul, map_smul]

private theorem degreeLift_power (g : 𝒮) (r : ℕ) (v : V) :
    degreeLift hn hK A g ((D^r) v) =
      (labelScalar hn hK A g : K)^r • (D^r) (degreeLift hn hK A g v) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    have hd (w : V) : degreeLift hn hK A g (D w) =
        (labelScalar hn hK A g : K) • D (degreeLift hn hK A g w) := by
      simpa only [pow_zero, Module.End.one_apply, zero_smul, add_zero,
        map_zero, mul_zero, map_one, one_smul, mul_one] using degreeLift_operator hn hK A g 1 0 w
    rw [hd, ih, map_smul, smul_smul, pow_succ', Module.End.mul_apply]

theorem degreeLift_constant (g : 𝒮) (x : K) :
    degreeLift hn hK A g (constantLinear x) = constantLinear (labelSigma hn hK A g x) := by
  apply (degreeLTEquiv K p).injective
  funext i
  change (degreeLift hn hK A g (constantLinear x) : K[X]).coeff i =
    (constantLinear (p := p) (labelSigma hn hK A g x) : K[X]).coeff i
  rw [degreeLift_coeff]
  by_cases hi : i.val = 0
  · simp [constantLinear, Polynomial.coeff_C, hi]
  · simp [constantLinear, Polynomial.coeff_C, hi]

private theorem topMap_apply (T : K →ₗ[𝔽] K) (v : V) :
    topMap (p := p) T v = constantLinear (T (coefficientZero ((D^(p-1)) v))) := by
  change constantLinear (T (coefficientZero ((((D).restrictScalars 𝔽)^(p-1)) v))) = _
  rw [restricted_derivative_pow_local]

/-- The scalar is applied to the INPUT of the unrestricted top map. -/
def transformedTop (g : 𝒮) (T : K →ₗ[𝔽] K) : K →ₗ[𝔽] K :=
  (labelSigma hn hK A g).toLinearMap.comp (T.comp
    ((labelSigma hn hK A g).symm.toLinearMap.comp
      (fieldScalar ((labelScalar hn hK A g : K)^(p-1)))))

private theorem degreeLift_top (g : 𝒮) (T : K →ₗ[𝔽] K) (v : V) :
    degreeLift hn hK A g (topMap T v) =
      topMap (transformedTop hn hK A g T) (degreeLift hn hK A g v) := by
  rw [topMap_apply, degreeLift_constant, topMap_apply]
  have hc := congrArg (coefficientZero (p := p) (K := K))
    (degreeLift_power hn hK A g (p-1) v)
  have hz (z : V) : coefficientZero (degreeLift hn hK A g z) =
      labelSigma hn hK A g (coefficientZero z) := by
    simpa only [coefficientZero, LinearMap.comp_apply, Submodule.subtype_apply,
      lcoeff_apply, Fin.val_zero, pow_zero, one_mul] using
        degreeLift_coeff hn hK A g z (0 : Fin p)
  rw [hz, map_smul, smul_eq_mul] at hc
  change constantLinear (labelSigma hn hK A g (T (coefficientZero ((D^(p-1)) v)))) =
    constantLinear (labelSigma hn hK A g (T ((labelSigma hn hK A g).symm
      ((labelScalar hn hK A g : K)^(p-1) *
        coefficientZero ((D^(p-1)) (degreeLift hn hK A g v))))))
  rw [← hc, AlgEquiv.symm_apply_apply]

/-- Actual normalized conjugation, with every T in End_F(K) retained. -/
theorem normalized_conjugation (g : 𝒮) (a : Fin (p-1) → K)
    (T : K →ₗ[𝔽] K) (v : V) :
    degreeLift hn hK A g (toeplitz a T v) =
      toeplitz (fun r => (labelScalar hn hK A g : K)^r.val *
        labelSigma hn hK A g (a r)) (transformedTop hn hK A g T)
        (degreeLift hn hK A g v) := by
  simp only [toeplitz, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    scalarMap_apply, map_add, map_sum, degreeLift_smul, degreeLift_power,
    restricted_derivative_pow_local, smul_smul, degreeLift_top]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_comm]

private theorem shear_apply (s : K) (v : V) : shear (p := p) s v = v + s • topShear v := rfl

private theorem topMap_scalar (x : K) (v : V) :
    topMap (p := p) (fieldScalar x) v = x • (D^(p-1)) v := by
  rw [topMap_apply]
  change constantLinear (x * coefficientZero ((D^(p-1)) v)) = _
  rw [← smul_eq_mul, map_smul, ← top_derivative]

private theorem topShear_power (r : ℕ) (hr : 0 < r) (v : V) :
    topShear ((D^r) v) = 0 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [pow_succ', Module.End.mul_apply, topShear_derivative]

private theorem power_topShear (r : ℕ) (hr : 2 ≤ r) (v : V) :
    (D^r) (topShear v) = 0 := by
  have he : r = (r-2)+2 := by omega
  rw [he, pow_add, Module.End.mul_apply]
  have hz : (D^2) (topShear v) = 0 := by
    rw [pow_two, Module.End.mul_apply, derivative_topShear]
    rw [← Module.End.mul_apply, ← pow_succ',
      Nat.sub_add_cancel (by have hp : 2 < p := Fact.out; omega), derivative_pow_prime]
    rfl
  rw [hz, map_zero]

private theorem topShear_toeplitz (a : Fin (p-1) → K) (T : K →ₗ[𝔽] K) (v : V) :
    topShear (toeplitz a T v) = a 0 • topShear v := by
  simp only [toeplitz, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    scalarMap_apply, restricted_derivative_pow_local, map_add, map_sum, map_smul]
  have ht : topShear (topMap T v) = 0 := by
    rw [topMap_apply]
    change dividedMonomial 1 _ (coefficientZero ((D^(p-1)) (constantLinear _))) = 0
    rw [OddPrimeJetDeformation.pow_constant (p-1)
      (by have hp : 2 < p := Fact.out; omega), map_zero, map_zero]
  rw [ht, add_zero]
  rw [Finset.sum_eq_single (0 : Fin (p-1))]
  · simp
  · intro r hr hr0
    rw [topShear_power r.val (by
      have hv : r.val ≠ 0 := fun h => hr0 (Fin.ext h)
      omega), smul_zero]
  · simp

private theorem toeplitz_topShear (a : Fin (p-1) → K) (T : K →ₗ[𝔽] K) (v : V) :
    toeplitz a T (topShear v) =
      a 0 • topShear v + a 1 • (D^(p-1)) v := by
  simp only [toeplitz, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    scalarMap_apply, restricted_derivative_pow_local]
  have ht : topMap T (topShear v) = 0 := by
    rw [topMap_apply, top_topShear, map_zero, map_zero, map_zero]
  rw [ht, add_zero]
  calc
    _ = ∑ r : Fin (p-1),
        ((if r = 0 then a 0 • topShear v else 0) +
          (if r = 1 then a 1 • (D^(p-1)) v else 0)) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h0 : r = 0
      · subst r
        have h01 : (0 : Fin (p-1)) ≠ 1 := by
          intro h
          have hp : 2 < p := Fact.out
          have h' := congrArg Fin.val h
          simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < p-1)] using h'
        simp [h01]
      · by_cases h1 : r = 1
        · subst r
          have hi : (1 : Fin (p-1)).val = 1 := by
            have hp : 2 < p := Fact.out
            change 1 % (p-1) = 1
            exact Nat.mod_eq_of_lt (by omega)
          have hp : 2 < p := Fact.out
          simp only [ite_eq_right h0, ite_eq_left rfl, zero_add]
          change a 1 • (D^(1 % (p-1))) (topShear v) = _
          rw [Nat.mod_eq_of_lt (by omega : 1 < p-1), pow_one, derivative_topShear]
          simp only [ite_true]
        · rw [if_neg h0, if_neg h1, zero_add, power_topShear, smul_zero]
          have hp : 2 < p := Fact.out
          have hv0 : r.val ≠ 0 := fun h => h0 (Fin.ext h)
          have hv1 : r.val ≠ 1 := by
            intro h
            apply h1
            apply Fin.ext
            simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < p-1)] using h
          omega
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Changing the fixed shear changes only the unrestricted top coefficient. -/
theorem shear_conjugation (s : K) (a : Fin (p-1) → K) (T : K →ₗ[𝔽] K) (v : V) :
    shear (-s) (toeplitz a T v) =
      toeplitz a (T + fieldScalar (s*a 1)) (shear (-s) v) := by
  have hadd (U W : K →ₗ[𝔽] K) (z : V) :
      topMap (U+W) z = topMap U z + topMap W z := by
    simp [topMap_apply]
  have he (z : V) : toeplitz a (T + fieldScalar (s*a 1)) z =
      toeplitz a T z + (s*a 1) • (D^(p-1)) z := by
    simp only [toeplitz, LinearMap.add_apply, hadd]
    rw [topMap_scalar]
    abel
  have hS (b : K) : toeplitz a T (b • topShear v) =
      b • (a 0 • topShear v + a 1 • (D^(p-1)) v) := by
    rw [← (topShear (p := p) (K := K)).map_smul, toeplitz_topShear,
      map_smul, map_smul]
    module
  rw [shear_apply, he, shear_apply, topShear_toeplitz, map_add, hS,
    map_add, map_smul, top_topShear, smul_zero, add_zero]
  module

include hn hK in
/-- A unit coordinate at the second jet level kills every weighted label
stabilizer: the first coordinate fixes the scalar and the primitive second
coordinate fixes the field automorphism. -/
theorem labelGroup_subsingleton_of_primitive_coordinates
    (hn3 : 3 ≤ n)
    (hA0 : A (⟨0, by omega⟩ : Fin (n - 1)) = 1)
    (hprimitive : ∀ x : Kˣ, ∃ m : ℕ,
      A (⟨1, by omega⟩ : Fin (n - 1)) ^ m = (x : K)) :
    Subsingleton 𝒮 := by
  let i0 : Fin (n - 1) := ⟨0, by omega⟩
  let i1 : Fin (n - 1) := ⟨1, by omega⟩
  have hA0' : A i0 = 1 := by simpa [i0] using hA0
  have hprimitive' : ∀ x : Kˣ, ∃ m : ℕ, A i1 ^ m = (x : K) := by
    simpa [i1] using hprimitive
  have htriv (g : 𝒮) : g = 1 := by
    have hinv : (labelScalar hn hK A g : K)⁻¹ = 1 := by
      have h := label_fixed hn hK A g i0
      have hi0 : weight p n i0 = 1 := by simp [i0, weight]
      simpa only [hA0', hi0, map_one, pow_one, mul_one,
        Units.val_inv_eq_inv_val] using h.symm
    have hc : labelScalar hn hK A g = 1 := by
      apply Units.ext
      change (labelScalar hn hK A g : K) = 1
      simpa only [inv_inv, inv_one] using
        congrArg (fun z : K => z⁻¹) hinv
    have hfix : labelSigma hn hK A g (A i1) = A i1 := by
      simpa [hc] using (label_fixed hn hK A g i1).symm
    have hsigma : labelSigma hn hK A g = 1 := by
      apply AlgEquiv.ext
      intro a
      by_cases ha : a = 0
      · subst a
        exact map_zero _
      · obtain ⟨m, hm⟩ := hprimitive' (Units.mk0 a ha)
        change A i1 ^ m = a at hm
        calc
          labelSigma hn hK A g a =
              labelSigma hn hK A g (A i1 ^ m) :=
            congrArg (labelSigma hn hK A g) hm.symm
          _ = A i1 ^ m := by rw [map_pow, hfix]
          _ = a := hm
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change
      Multiplicative.toAdd
          (g.val (Multiplicative.ofAdd (Multiplicative.toAdd x))) =
        Multiplicative.toAdd x
    simpa [hc, hsigma] using
      label_formula hn hK A g (Multiplicative.toAdd x)
  exact ⟨fun g h => (htriv g).trans (htriv h).symm⟩

include hn hK in
/-- No chosen coefficient model restricts the scope: every normalized original q has this group. -/
theorem normalized_group_structure (q₀ : K →ₗ[𝔽] K) (hq₀ : q₀ 1 = 0) :
    ∃ α : labelGroup q₀ →* MulAut (project q₀).ker,
      Nonempty (originalGroup q₀ ≃* (project q₀).ker ⋊[α] labelGroup q₀) ∧
      Nat.card (project q₀).ker = (p^n-1)*p^(n*(p-2)+n*n) ∧
      Nat.card (originalGroup q₀) = (p^n-1)*p^(n*(p-2)+n*n)*Nat.card (labelGroup q₀) := by
  obtain ⟨B,hB⟩ := (coefficientMap_bijective hn hK).surjective ⟨q₀,hq₀⟩
  have he : Q (p := p) n B = q₀ := congrArg Subtype.val hB
  subst q₀
  exact ⟨kernelAction hn hK B, ⟨semidirectEquiv hn hK B⟩,
    commutant_cardinality hn hK B, full_cardinality hn hK B⟩

/-- The prime-field full count includes its nontrivial scalar-label factor. -/
theorem prime_field_cardinality (hK₁ : Fintype.card K = p) :
    Nat.card (originalGroup (p := p) (0 : K →ₗ[𝔽] K)) = (p-1)^2*p^(p-1) := by
  let L := Shrink.{0} K
  let e : K ≃ₐ[𝔽] L :=
    (@Shrink.algEquiv 𝔽 K (inferInstance : Small.{0} K) _ _ _).symm
  let B : Fin (1-1) → K := fun i => Fin.elim0 i
  have hcard : Fintype.card K = p^1 := by simpa using hK₁
  have hL : Fintype.card L = p := by simpa [L] using hK₁
  have he : Q (p := p) 1 B = 0 := by
    apply LinearMap.ext
    intro x
    change (coefficientMap (p := p) 1 B).val x = 0
    rw [coefficientMap_apply]
    simp
  have htop : weightedStabilizer (p := p) B e = ⊤ := by
    apply top_unique
    intro g hg
    change WeightedSemilinear.act (weight p 1) g (fun i => e (B i)) = (fun i => e (B i))
    funext i
    exact Fin.elim0 i
  have hs : Nat.card (labelGroup (p := p) (0 : K →ₗ[𝔽] K)) = p-1 := by
    calc
      _ = Nat.card (weightedStabilizer (p := p) B e) := by
        rw [← he]
        exact Nat.card_congr (weightedStabilizerEquiv (p := p) (by omega) hcard B e).symm.toEquiv
      _ = Nat.card (WeightedSemilinear.Group 𝔽 L) := by
        rw [htop]
        exact Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = (p-1)*finrank 𝔽 L := by
        rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
          Nat.card_units, Nat.card_eq_fintype_card (α := L), hL,
          IsGalois.card_aut_eq_finrank]
      _ = p-1 := by
        have hd : finrank 𝔽 L = 1 := by
          apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
          simpa only [pow_one] using (FiniteField.pow_finrank_eq_card p L).trans hL
        rw [hd, mul_one]
  have h := full_cardinality (p := p) (by omega : 1 ≤ 1) hcard B
  rw [he, hs] at h
  have hp : 2 < p := Fact.out
  have hexp : 1*(p-2)+1*1 = p-1 := by omega
  rw [hexp, pow_one] at h
  rw [h, pow_two]
  ring

#print axioms semidirectEquiv
#print axioms normalized_group_structure
#print axioms prime_field_cardinality
#print axioms labelGroup_subsingleton_of_primitive_coordinates
#print axioms normalized_conjugation
#print axioms shear_conjugation
end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup
