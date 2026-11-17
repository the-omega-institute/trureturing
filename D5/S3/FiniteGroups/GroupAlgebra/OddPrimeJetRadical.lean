/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Ideal.Operations]
   utility: none
   digest: The actual leading-zero commutant ideal and its principal units. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
import Mathlib.RingTheory.Ideal.Operations

/-! The ideal and unit group are subobjects of the actual endomorphism algebra.
The scalar coordinates are divided degrees, with leading index p-1. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical
open Polynomial Module OddPrimeJetDeformation OddPrimeJetCommutant
open scoped BigOperators
universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "D" => derivativeEnd (p := p) (K := K)

/-- The actual prime-field-linear commutant, with composition as multiplication. -/
def commutantAlgebra (q : K →ₗ[F] K) : Subalgebra F (Module.End F V) where
  carrier := {X | commutesOriginal q X}
  zero_mem' := by intro g v; simp
  one_mem' := by intro g v; rfl
  add_mem' := by intro X Y hX hY g v; simp [hX g v, hY g v]
  mul_mem' := by intro X Y hX hY g v; exact (congrArg X (hY g v)).trans (hX g (Y v))
  algebraMap_mem' := by intro a g v; simp


def leadingScalar (q : K →ₗ[F] K) (x : commutantAlgebra (p := p) (K := K) q) : K := coefficientZero (p := p) (K := K) (x.val (constantLinear (p := p) (K := K) 1))



theorem constant_action (q : K →ₗ[F] K) (hq : q 1 = 0) (X : (commutantAlgebra (p := p) (K := K) q)) (z : K) :
    X.val (constantLinear (p := p) (K := K) z) = constantLinear (p := p) (K := K) (leadingScalar (p := p) (K := K) q X * z) := by
  obtain ⟨c,T,hc,he⟩ := (actual_commutant_normal_form (p := p) (K := K) q hq X.val).mp X.property
  have hlead : leadingScalar (p := p) (K := K) q X = c (leadingIndex (p := p)) := by
    simp only [leadingScalar, he, toeplitzDegree_constant]
    simp [coefficientZero, constantLinear]
  rw [he, toeplitzDegree_constant (p := p) (K := K), hlead]

/-- Restriction to the constant line gives the actual leading ring homomorphism. -/
def leadingHom (q : K →ₗ[F] K) (hq : q 1 = 0) : (commutantAlgebra (p := p) (K := K) q) →+* K where
  toFun := leadingScalar (p := p) (K := K) q
  map_one' := by simp [leadingScalar, coefficientZero, constantLinear]
  map_zero' := by simp [leadingScalar]
  map_add' X Y := by simp [leadingScalar]
  map_mul' X Y := by
    change coefficientZero (p := p) (K := K) (X.val (Y.val (constantLinear (p := p) (K := K) 1))) = _
    rw [constant_action (p := p) q hq Y, mul_one, constant_action (p := p) q hq X]
    simp [coefficientZero, constantLinear]

/-- The leading-zero ideal of the actual commutant. -/
def radical (q : K →ₗ[F] K) (hq : q 1 = 0) : Ideal (commutantAlgebra (p := p) (K := K) q) := RingHom.ker (leadingHom (p := p) (K := K) q hq)

private theorem radical_constants (q : K →ₗ[F] K) (hq : q 1 = 0) (X : (commutantAlgebra (p := p) (K := K) q)) (hX : X ∈ radical (p := p) (K := K) q hq) (z : K) :
    X.val (constantLinear (p := p) (K := K) z) = 0 := by
  rw [constant_action (p := p) q hq]
  change leadingScalar (p := p) (K := K) q X = 0 at hX
  simp [hX]

private theorem commutes_derivative (q : K →ₗ[F] K) (hq : q 1 = 0) (X : (commutantAlgebra (p := p) (K := K) q)) (v : V) : X.val (D v) = D (X.val v) :=
  ((actual_commutant_generated_bridge (p := p) (K := K) q hq X.val).mp X.property).1 v

private theorem radical_normal_form (q : K →ₗ[F] K) (hq : q 1 = 0) (X : (commutantAlgebra (p := p) (K := K) q)) (hX : X ∈ radical (p := p) (K := K) q hq) :
    ∃ (c : Fin p → K) (T : K →ₗ[F] K), c 0 = 0 ∧
      c (leadingIndex (p := p)) = 0 ∧ X.val = toeplitzDegree (p := p) (K := K) c T := by
  obtain ⟨c,T,hc,he⟩ := (actual_commutant_normal_form (p := p) (K := K) q hq X.val).mp X.property
  refine ⟨c,T,hc,?_,he⟩
  change leadingScalar (p := p) (K := K) q X = 0 at hX
  simp only [leadingScalar, he, toeplitzDegree_constant] at hX
  simpa [coefficientZero, constantLinear] using hX

/-- The leading-zero ideal is commutative even though its ambient algebra need not be. -/
theorem radical_commute (q : K →ₗ[F] K) (hq : q 1 = 0) (X Y : (commutantAlgebra (p := p) (K := K) q)) (hX : X ∈ radical (p := p) (K := K) q hq) (hY : Y ∈ radical (p := p) (K := K) q hq) :
    Commute X Y := by
  obtain ⟨c,T,hc,hcl,heX⟩ := radical_normal_form (p := p) q hq X hX
  obtain ⟨d,U,hd,hdl,heY⟩ := radical_normal_form (p := p) q hq Y hY
  change X * Y = Y * X
  apply Subtype.ext
  change X.val * Y.val = Y.val * X.val
  rw [heX, heY, toeplitzDegree_mul (p := p) (K := K), toeplitzDegree_mul (p := p) (K := K)]
  have hf : productFamily c d = productFamily d c := by
    funext j
    unfold productFamily
    rw [Finset.sum_comm]
    simp only [add_comm, mul_comm]
  have ht : topConvolution c d = topConvolution d c := by
    unfold topConvolution
    rw [Finset.sum_comm]
    simp only [add_comm, mul_comm]
  have hs : fieldScalar (p := p) (0 : K) = 0 := by ext z; simp [fieldScalar]
  simp only [productTop, hcl, hdl, hs, LinearMap.zero_comp, LinearMap.comp_zero,
    zero_add, add_zero, hf, ht]

/-- Each actual radical element is p-nilpotent, using the derivative-filtration supplier. -/
theorem radical_element_pow (q : K →ₗ[F] K) (hq : q 1 = 0) (X : (commutantAlgebra (p := p) (K := K) q)) (hX : X ∈ radical (p := p) (K := K) q hq) : X ^ p = 0 := by
  apply Subtype.ext
  exact nilpotent_of_constants_zero (p := p) (K := K) X.val (commutes_derivative (p := p) q hq X)
    (radical_constants (p := p) q hq X hX)

private def vanishingIdeal (q : K →ₗ[F] K) (r : ℕ) : Ideal (commutantAlgebra (p := p) (K := K) q) where
  carrier := {X | ∀ v : V, (D ^ r) v = 0 → X.val v = 0}
  zero_mem' := by intro v hv; rfl
  add_mem' := by intro X Y hX hY v hv; simp [hX v hv, hY v hv]
  smul_mem' := by intro X Y hY v hv; change X.val (Y.val v) = 0; rw [hY v hv, map_zero]

private theorem radical_pow_vanish (q : K →ₗ[F] K) (hq : q 1 = 0) (r : ℕ) :
    radical (p := p) (K := K) q hq ^ r ≤ vanishingIdeal (p := p) q r := by
  letI : (radical (p := p) (K := K) q hq).IsTwoSided :=
    inferInstanceAs (RingHom.ker (leadingHom (p := p) (K := K) q hq)).IsTwoSided
  induction r with
  | zero =>
      intro X hX
      change ∀ v : V, (D ^ 0) v = 0 → X.val v = 0
      intro v hv
      change v = 0 at hv
      rw [hv, map_zero]
  | succ r ih =>
      rw [Ideal.IsTwoSided.pow_succ]
      apply Ideal.mul_le.mpr
      intro X hX Y hY
      change ∀ v : V, (D ^ (r + 1)) v = 0 → X.val (Y.val v) = 0
      intro v hv
      have hYv : D (Y.val v) = 0 := by
        rw [← commutes_derivative (p := p) q hq Y]
        apply ih hY
        simpa only [pow_succ, Module.End.mul_apply] using hv
      have he : Y.val v = constantLinear (p := p) (K := K) ((Y.val v : K[X]).coeff 0) :=
        Subtype.ext (derivative_kernel _ hYv)
      change X.val (Y.val v) = 0
      rw [he, radical_constants (p := p) q hq X hX]

/-- Joint ideal-power nilpotence, rather than only elementwise p-nilpotence. -/
theorem radical_pow_eq_bot (q : K →ₗ[F] K) (hq : q 1 = 0) : radical (p := p) (K := K) q hq ^ p = ⊥ := by
  apply le_antisymm _ bot_le
  intro X hX
  change X = 0
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  apply radical_pow_vanish (p := p) q hq p hX
  rw [derivative_pow_prime]
  rfl


#print axioms radical_commute
#print axioms radical_element_pow
#print axioms radical_pow_eq_bot
end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical
