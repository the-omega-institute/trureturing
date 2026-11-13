/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPrincipalSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.GroupExtension.Basic, mathlib/module/Mathlib.GroupTheory.SemidirectProduct]
   utility: none
   digest: Actual principal-unit complement and scalar-label split of the odd-prime jet group. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadicalGroup
import Mathlib.GroupTheory.GroupExtension.Basic

/-! The actual principal-unit complement of the normalized odd-prime jet group. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPrincipalSplitting

open Polynomial Module OddPrimeJetDeformation OddPrimeJetCommutant
open OddPrimeJetPairClassification OddPrimeJetRadical OddPrimeJetRadicalGroup
open OddPrimeJetGroup FiniteJetClassification FiniteJetCoefficients
open scoped BigOperators

universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p

private theorem constant_injective :
    Function.Injective (constantLinear (p := p) (K := K)) := by
  intro a b h
  have he := congrArg (coefficientZero (p := p) (K := K)) h
  simpa [coefficientZero, constantLinear] using he

/-- The genuine scalar operators belong to the actual commutant because the
original representation, before restriction of scalars, is K-linear. This is
a ring section, not a map into the center of the commutant. -/
def scalarRingSection (q : K →ₗ[F] K) : K →+* commutantAlgebra (p := p) q where
  toFun a := ⟨scalarMap (p := p) a, by
    intro g v
    change a • (finiteExp (jetOperator q (Multiplicative.toAdd g))) v =
      (finiteExp (jetOperator q (Multiplicative.toAdd g))) (a • v)
    exact (map_smul (finiteExp (jetOperator q (Multiplicative.toAdd g))) a v).symm⟩
  map_one' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change (1 : K) • v = v
    exact one_smul K v
  map_zero' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change (0 : K) • v = 0
    exact zero_smul K v
  map_add' a b := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change (a + b) • v = a • v + b • v
    exact add_smul a b v
  map_mul' a b := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change (a * b) • v = a • (b • v)
    exact (smul_smul a b v).symm

private theorem leading_scalar (q : K →ₗ[F] K) (hq : q 1 = 0) (a : K) :
    leadingHom q hq (scalarRingSection q a) = a := by
  change coefficientZero (scalarMap (p := p) a (constantLinear 1)) = a
  simp [scalarMap_apply, map_smul, coefficientZero, constantLinear]

/-- Scalar units embedded in the actual original-label kernel, via the native
algebra-units/kernel equivalence. -/
def scalarKernel (q : K →ₗ[F] K) : Kˣ →* (project (p := p) q).ker :=
  (commutantUnitsEquiv q).toMonoidHom.comp
    (Units.map (scalarRingSection q).toMonoidHom)

/-- The actual leading unit, read through the native commutant-units equivalence. -/
def kernelLeading (q : K →ₗ[F] K) (hq : q 1 = 0) :
    (project (p := p) q).ker →* Kˣ :=
  (Units.map (leadingHom q hq).toMonoidHom).comp
    (commutantUnitsEquiv q).symm.toMonoidHom

private theorem kernelLeading_scalar (q : K →ₗ[F] K) (hq : q 1 = 0) (a : Kˣ) :
    kernelLeading q hq (scalarKernel q a) = a := by
  apply Units.ext
  change leadingHom q hq
    (((commutantUnitsEquiv q).symm
      (commutantUnitsEquiv q (Units.map (scalarRingSection q).toMonoidHom a))).val) =
    (a : K)
  rw [MulEquiv.symm_apply_apply]
  exact leading_scalar q hq (a : K)

private theorem kernel_constant (q : K →ₗ[F] K) (hq : q 1 = 0)
    (k : (project (p := p) q).ker) (a : K) :
    k.val.val.1 (constantLinear a) =
      constantLinear ((kernelLeading q hq k : K) * a) := by
  obtain ⟨w, rfl⟩ := (commutantUnitsEquiv q).surjective k
  change w.val.val (constantLinear a) =
    constantLinear (leadingHom q hq
      (((commutantUnitsEquiv q).symm (commutantUnitsEquiv q w)).val) * a)
  rw [MulEquiv.symm_apply_apply]
  exact constant_action q hq w.val a

private theorem actualPrincipal_iff (q : K →ₗ[F] K) (hq : q 1 = 0)
    (k : (project (p := p) q).ker) :
    k ∈ actualPrincipalUnits q hq ↔ kernelLeading q hq k = 1 := by
  constructor
  · rintro ⟨w, hw, he⟩
    rw [← he]
    change Units.map (leadingHom q hq).toMonoidHom
      ((commutantUnitsEquiv q).symm (commutantUnitsEquiv q w)) = 1
    rw [MulEquiv.symm_apply_apply]
    exact hw
  · intro hk
    exact ⟨(commutantUnitsEquiv q).symm k, hk,
      (commutantUnitsEquiv q).apply_symm_apply k⟩

/-- The inclusion used in the extension is exactly the two native subtype maps. -/
def principalInclusion (q : K →ₗ[F] K) (hq : q 1 = 0) :
    actualPrincipalUnits (p := p) q hq →* originalGroup q :=
  (project q).ker.subtype.comp (actualPrincipalUnits q hq).subtype

private theorem principalInclusion_injective (q : K →ₗ[F] K) (hq : q 1 = 0) :
    Function.Injective (principalInclusion (p := p) q hq) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact h

section Coefficients

variable [Fintype K] {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n)
variable (A : Fin (n - 1) → K)
local notation "qA" => Q (p := p) n A
local notation "L" => labelGroup qA

private theorem qA_zero (n : ℕ) (A : Fin (n - 1) → K) :
    Q (p := p) n A 1 = 0 := by
  change (coefficientMap (p := p) n A).val 1 = 0
  exact (coefficientMap (p := p) n A).property

local notation "hqA" => qA_zero (p := p) (K := K) n A

/-- The label's field automorphism is multiplicative. Only the public label
formula is used; the private labelSigma_one/mul lemmas are not referenced. -/
def fieldAction : L →* (K ≃ₐ[F] K) where
  toFun := labelSigma hn hK A
  map_one' := by
    ext a
    have hc : (labelScalar hn hK A 1 : K) = 1 := by
      simpa using (label_formula hn hK A 1 1).symm
    have he := label_formula hn hK A 1 a
    simpa [hc] using he.symm
  map_mul' g h := by
    have hc : (labelScalar hn hK A (g * h) : K) =
        (labelScalar hn hK A g : K) *
          labelSigma hn hK A g (labelScalar hn hK A h) := by
      calc
        (labelScalar hn hK A (g * h) : K) =
            Multiplicative.toAdd (g.val (h.val (Multiplicative.ofAdd 1))) := by
          simpa using (label_formula hn hK A (g * h) 1).symm
        _ = (labelScalar hn hK A g : K) * labelSigma hn hK A g
            (Multiplicative.toAdd (h.val (Multiplicative.ofAdd 1))) :=
          label_formula hn hK A g _
        _ = _ := by rw [label_formula hn hK A h 1]; simp
    ext a
    change labelSigma hn hK A (g * h) a =
      labelSigma hn hK A g (labelSigma hn hK A h a)
    apply mul_left_cancel₀ (labelScalar hn hK A (g * h)).ne_zero
    rw [← label_formula hn hK A (g * h) a, hc]
    have he := label_formula hn hK A g
      (Multiplicative.toAdd (h.val (Multiplicative.ofAdd a)))
    change Multiplicative.toAdd (g.val (h.val (Multiplicative.ofAdd a))) = _ at he
    rw [label_formula hn hK A h a, map_mul] at he
    change Multiplicative.toAdd (g.val (h.val (Multiplicative.ofAdd a))) = _
    simpa only [mul_assoc] using he

/-- The induced action on K's units stays in K's arbitrary universe.
WeightedSemilinear.unitsAut has Type-valued field parameters; Units.mapEquiv
is the universe-polymorphic native construction used here. -/
def scalarAction : L →* MulAut Kˣ where
  toFun g := Units.mapEquiv (fieldAction hn hK A g).toMulEquiv
  map_one' := by
    apply MulEquiv.ext
    intro a
    apply Units.ext
    change fieldAction hn hK A 1 (a : K) = (a : K)
    simp only [map_one, AlgEquiv.one_apply]
  map_mul' g h := by
    apply MulEquiv.ext
    intro a
    apply Units.ext
    change fieldAction hn hK A (g * h) (a : K) =
      fieldAction hn hK A g (fieldAction hn hK A h (a : K))
    simp only [map_mul, AlgEquiv.mul_apply]

private theorem canonicalShear_constant (a : K) :
    canonicalShear (p := p) A (constantLinear a) = constantLinear a := by
  change constantLinear a + (-(∑ i, A i)) • topShear (constantLinear a) =
    constantLinear a
  have hz : topShear (p := p) (constantLinear (p := p) (K := K) a) = 0 := by
    simp only [topShear, LinearMap.comp_apply,
      pow_constant (p - 1) (by have hp : 2 < p := Fact.out; omega), map_zero]
  rw [hz, smul_zero, add_zero]

/-- The fixed shear is K-linear, so the coherent section itself is semilinear.
This assertion is about the chosen section; arbitrary full-group operators
and arbitrary commutant top maps are not asserted to be semilinear. -/
theorem coherentLift_semilinear (g : L) (a : K) (v : V) :
    coherentLift hn hK A g (a • v) =
      labelSigma hn hK A g a • coherentLift hn hK A g v := by
  let S : V ≃ₗ[K] V := shear (p := p) (-(∑ i, A i))
  change S.symm (degreeLift hn hK A g (S (a • v))) =
    labelSigma hn hK A g a • S.symm (degreeLift hn hK A g (S v))
  rw [map_smul]
  have hd : degreeLift hn hK A g (a • S v) =
      labelSigma hn hK A g a • degreeLift hn hK A g (S v) := by
    simp only [degreeLift, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      coefficientAutomorphism_smul, map_smul]
  rw [hd, map_smul]

private theorem section_constant (g : L) (a : K) :
    coherentLift hn hK A g (constantLinear a) =
      constantLinear (labelSigma hn hK A g a) := by
  have hi (b : K) : (canonicalShear (p := p) A).symm (constantLinear b) =
      constantLinear b := by
    apply (canonicalShear (p := p) A).injective
    rw [LinearEquiv.apply_symm_apply, canonicalShear_constant]
  change (canonicalShear A).symm
    (degreeLift hn hK A g (canonicalShear A (constantLinear a))) = _
  rw [canonicalShear_constant, degreeLift_constant, hi]

/-- Coherent scalar covariance in the actual original-pair group. -/
theorem scalar_covariance (g : L) (a : Kˣ) :
    sectionHom hn hK A g * (scalarKernel qA a).val * (sectionHom hn hK A g)⁻¹ =
      (scalarKernel qA (scalarAction hn hK A g a)).val := by
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro v
    change coherentLift hn hK A g ((a : K) • (coherentLift hn hK A g).symm v) =
      labelSigma hn hK A g (a : K) • v
    rw [coherentLift_semilinear, LinearEquiv.apply_symm_apply]
  · change g.val * 1 * g.val⁻¹ = 1
    simp

private theorem leading_equivariant (g : L) (k : (project qA).ker) :
    kernelLeading qA hqA (kernelAction hn hK A g k) =
      scalarAction hn hK A g (kernelLeading qA hqA k) := by
  have hf : coherentLift hn hK A g (constantLinear (p := p) (K := K) 1) =
      constantLinear 1 := by
    rw [section_constant, map_one]
  have hi : (coherentLift hn hK A g).symm (constantLinear 1) = constantLinear 1 := by
    apply (coherentLift hn hK A g).injective
    rw [LinearEquiv.apply_symm_apply, hf]
  apply Units.ext
  apply constant_injective (p := p) (K := K)
  calc
    constantLinear ((kernelLeading qA hqA (kernelAction hn hK A g k) : K)) =
        (kernelAction hn hK A g k).val.val.1 (constantLinear 1) := by
      simpa only [mul_one] using
        (kernel_constant qA hqA
          (kernelAction hn hK A g k) 1).symm
    _ = coherentLift hn hK A g
        (k.val.val.1 ((coherentLift hn hK A g).symm (constantLinear 1))) := rfl
    _ = coherentLift hn hK A g (k.val.val.1 (constantLinear 1)) := by rw [hi]
    _ = coherentLift hn hK A g
        (constantLinear ((kernelLeading qA hqA k : K) * 1)) := by rw [kernel_constant]
    _ = constantLinear (labelSigma hn hK A g (kernelLeading qA hqA k : K)) := by
      rw [mul_one, section_constant]
    _ = constantLinear ((scalarAction hn hK A g (kernelLeading qA hqA k) : K)) := rfl

private theorem full_coordinates_factor (k : (project qA).ker) (g : L) :
    semidirectEquiv hn hK A (k.val * sectionHom hn hK A g) =
      (⟨k, g⟩ : (project qA).ker ⋊[kernelAction hn hK A] L) := by
  exact (semidirectEquiv hn hK A).apply_symm_apply ⟨k, g⟩

private theorem leading_map_compat :
    ∀ g : L,
      (kernelLeading qA hqA).comp (kernelAction hn hK A g).toMonoidHom =
        (scalarAction hn hK A g).toMonoidHom.comp (kernelLeading qA hqA) := by
  intro g
  apply MonoidHom.ext
  intro k
  exact leading_equivariant hn hK A g k

/-- The quotient keeps every actual label and applies the equivariant leading
unit map to the full commutant factor. -/
def quotientHom : originalGroup qA →* Kˣ ⋊[scalarAction hn hK A] L :=
  (SemidirectProduct.map (φ₁ := kernelAction hn hK A) (φ₂ := scalarAction hn hK A)
    (kernelLeading qA hqA) (MonoidHom.id L) (leading_map_compat hn hK A)).comp
      (semidirectEquiv hn hK A).toMonoidHom

private theorem quotient_factor (k : (project qA).ker) (g : L) :
    quotientHom hn hK A (k.val * sectionHom hn hK A g) =
      (⟨kernelLeading qA hqA k, g⟩ : Kˣ ⋊[scalarAction hn hK A] L) := by
  unfold quotientHom
  change SemidirectProduct.map (kernelLeading qA hqA) (MonoidHom.id L)
      (leading_map_compat hn hK A)
      (semidirectEquiv hn hK A (k.val * sectionHom hn hK A g)) = _
  rw [full_coordinates_factor]
  rfl

/-- Scalar times coherent label is a homomorphism on the native semidirect
product, whose multiplication is (a,g)(b,h)=(a sigma(g)(b),gh). -/
def complementHom : Kˣ ⋊[scalarAction hn hK A] L →* originalGroup qA :=
  SemidirectProduct.lift (φ := scalarAction hn hK A)
    ((project qA).ker.subtype.comp (scalarKernel qA)) (sectionHom hn hK A) (by
      intro g
      apply MonoidHom.ext
      intro a
      exact (scalar_covariance hn hK A g a).symm)

/-- This is an explicit homomorphic right inverse, with no choice of
representatives for the principal-unit quotient. -/
theorem quotient_complement (x : Kˣ ⋊[scalarAction hn hK A] L) :
    quotientHom hn hK A (complementHom hn hK A x) = x := by
  obtain ⟨a, g⟩ := x
  change quotientHom hn hK A ((scalarKernel qA a).val * sectionHom hn hK A g) =
    (⟨a, g⟩ : Kˣ ⋊[scalarAction hn hK A] L)
  rw [quotient_factor, kernelLeading_scalar]

private theorem complement_scalar (a : Kˣ) :
    complementHom hn hK A (SemidirectProduct.inl a) = (scalarKernel qA a).val := by
  change (scalarKernel qA a).val * sectionHom hn hK A 1 = _
  rw [map_one, mul_one]

private theorem quotient_labels :
    (SemidirectProduct.rightHom : Kˣ ⋊[scalarAction hn hK A] L →* L).comp
      (quotientHom hn hK A) = project qA := by
  apply MonoidHom.ext
  intro z
  let x := semidirectEquiv hn hK A z
  have hf := (semidirectEquiv hn hK A).symm_apply_apply z
  change x.left.val * sectionHom hn hK A x.right = z at hf
  change x.right = project qA z
  rw [← hf, map_mul, project_section,
    show project qA x.left.val = 1 from x.left.property, one_mul]

/-- The kernel is precisely the native actualPrincipalUnits, mapped into the
original group by the native label-kernel subtype. -/
theorem quotient_kernel :
    (quotientHom hn hK A).ker =
      (actualPrincipalUnits qA hqA).map (project qA).ker.subtype := by
  ext z
  constructor
  · intro hz
    change quotientHom hn hK A z = 1 at hz
    let x := semidirectEquiv hn hK A z
    have hl : kernelLeading qA hqA x.left = 1 :=
      congrArg (fun y : Kˣ ⋊[scalarAction hn hK A] L => y.left) hz
    have hr : x.right = 1 :=
      congrArg (fun y : Kˣ ⋊[scalarAction hn hK A] L => y.right) hz
    have hf := (semidirectEquiv hn hK A).symm_apply_apply z
    change x.left.val * sectionHom hn hK A x.right = z at hf
    have hx : x.left.val = z := by simpa only [hr, map_one, mul_one] using hf
    exact ⟨x.left, (actualPrincipal_iff qA hqA x.left).mpr hl, hx⟩
  · rintro ⟨k, hk, rfl⟩
    change quotientHom hn hK A k.val = 1
    have hf : quotientHom hn hK A k.val =
        (⟨kernelLeading qA hqA k, 1⟩ : Kˣ ⋊[scalarAction hn hK A] L) := by
      simpa only [map_one, mul_one] using quotient_factor hn hK A k 1
    rw [hf]
    apply SemidirectProduct.ext
    · exact (actualPrincipal_iff qA hqA k).mp hk
    · rfl

/-- The substantive split extension uses the actual principal-unit subgroup,
the original group, and the scalar/actual-label semidirect product. -/
def principalExtension :
    GroupExtension (actualPrincipalUnits qA hqA) (originalGroup qA)
      (Kˣ ⋊[scalarAction hn hK A] L) where
  inl := principalInclusion qA hqA
  rightHom := quotientHom hn hK A
  inl_injective := principalInclusion_injective qA hqA
  range_inl_eq_ker_rightHom := by
    rw [quotient_kernel]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨k, hk, hz⟩
      exact ⟨⟨k, hk⟩, hz⟩
  rightHom_surjective := fun x => ⟨complementHom hn hK A x, quotient_complement hn hK A x⟩

/-- Native GroupExtension.Splitting, with the explicit coherent complement. -/
def principalSplitting : (principalExtension hn hK A).Splitting where
  __ := complementHom hn hK A
  rightInverse_rightHom := quotient_complement hn hK A

/-- Every actual element has a unique principal-unit times scalar-times-label
factorization. The generic split-extension equivalence is reused directly. -/
theorem unique_principal_factorization (z : originalGroup qA) :
    ∃! x : actualPrincipalUnits qA hqA × (Kˣ ⋊[scalarAction hn hK A] L),
      principalInclusion qA hqA x.1 * complementHom hn hK A x.2 = z := by
  let s := principalSplitting hn hK A
  let e := s.semidirectProductMulEquiv
  obtain ⟨x, hx⟩ := e.surjective z
  refine ⟨(x.left, x.right), hx, ?_⟩
  rintro ⟨a, c⟩ he
  have hh : (⟨a, c⟩ : actualPrincipalUnits qA hqA ⋊[s.conjAct]
      (Kˣ ⋊[scalarAction hn hK A] L)) = x :=
    e.injective (he.trans hx.symm)
  exact congrArg (fun t : actualPrincipalUnits qA hqA ⋊[s.conjAct]
    (Kˣ ⋊[scalarAction hn hK A] L) => (t.left, t.right)) hh

end Coefficients

/-! The full splitting specification is named as a proposition so the public
theorem below has a compact statement-material representation. Unfolding this
definition recovers exactly the displayed existential data; no conclusion is
weakened or hidden behind an axiom. -/
def normalizedPrincipalSplittingSpec [Fintype K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n)
    (q : K →ₗ[F] K) (hq : q 1 = 0) : Prop :=
    ∃ (σ : labelGroup q →* MulAut Kˣ)
      (S : GroupExtension (actualPrincipalUnits q hq) (originalGroup q)
        (Kˣ ⋊[σ] labelGroup q)) (s : S.Splitting),
      S.inl = principalInclusion q hq ∧
      S.rightHom.ker = (actualPrincipalUnits q hq).map (project q).ker.subtype ∧
      (SemidirectProduct.rightHom : Kˣ ⋊[σ] labelGroup q →* labelGroup q).comp
        S.rightHom = project q ∧
      (∀ a : Kˣ, s (SemidirectProduct.inl a) = (scalarKernel q a).val) ∧
      (∀ z : originalGroup q,
        ∃! x : actualPrincipalUnits q hq × (Kˣ ⋊[σ] labelGroup q),
          principalInclusion q hq x.1 * s x.2 = z)

/-! Every normalized prime-field-linear q has the actual principal-unit
splitting. The theorem proves the named specification above; unfolding it
recovers the exact native extension, section, kernel, label projection, scalar
section, and unique principal/scalar/label factorization. -/
theorem normalized_principal_splitting [Fintype K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n)
    (q : K →ₗ[F] K) (hq : q 1 = 0) :
    normalizedPrincipalSplittingSpec (p := p) hn hK q hq := by
  obtain ⟨A, hA⟩ := (coefficientMap_bijective hn hK).surjective ⟨q, hq⟩
  have he : Q (p := p) n A = q := congrArg Subtype.val hA
  subst q
  refine ⟨scalarAction hn hK A, principalExtension hn hK A,
    principalSplitting hn hK A, rfl, quotient_kernel hn hK A,
    quotient_labels hn hK A, ?_, ?_⟩
  · exact complement_scalar hn hK A
  · exact unique_principal_factorization hn hK A

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPrincipalSplitting
