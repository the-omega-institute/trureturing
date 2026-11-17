/- GID: D5/S3/FiniteGroups/GroupAlgebra/FiniteJetClassification
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/FiniteJetClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite original-jet intertwiners force exactly the inverse weighted coefficient relation. -/
import D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification

set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification
open FiniteJetCoefficients OddPrimeJetDeformation OddPrimeJetPairClassification
open scoped BigOperators
universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Fintype K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "E" => Multiplicative K

/-- The original inverse scalar weights on all n-1 coordinates. -/
def weight (p n : ℕ) (i : Fin (n - 1)) : ℕ := p ^ (i.val + 1) - p + 1

abbrev Q (n : ℕ) (A : Fin (n - 1) → K) : K →ₗ[F] K :=
  (coefficientMap (p := p) n A).val

/-- The actual representation-theoretic condition for a fixed original relabeling. -/
def Intertwines (q r : K →ₗ[F] K) (φ : E ≃* E) : Prop :=
  ∃ P : V ≃ₗ[F] V, ∀ (g : E) (v : V),
    P (originalRepresentation (p := p) q g v) = originalRepresentation r (φ g) (P v)

private theorem derivation_zero (δ : Derivation F K K) : δ = 0 := by
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  ext x
  obtain ⟨y, hy⟩ := (FiniteField.frobeniusAlgEquivOfAlgebraic F K).surjective x
  change y ^ Fintype.card F = x at hy
  rw [ZMod.card] at hy
  rw [← hy, δ.leibniz_pow]
  simp [nsmul_eq_mul, smul_eq_mul]

/-- Reference subtraction is an identity of the actual functions on K. -/
theorem reference_subtraction (n : ℕ) (B : Fin (n - 1) → K) (c x : K) :
    Q (p := p) n B (c*x) - x*Q (p := p) n B c =
      Q (p := p) n (fun i => c ^ (p ^ (i.val + 1)) * B i) x := by
  simp only [Q, coefficientMap_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_pow]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem transformed_coordinates (n : ℕ) (A : Fin (n - 1) → K)
    (c : K) (σ : K ≃ₐ[F] K) (x : K) :
    Q (p := p) n (fun i => c * σ (A i)) (σ x) = c * σ (Q (p := p) n A x) := by
  simp [Q, coefficientMap_apply, map_sum, map_mul, map_sub, map_pow,
    Finset.mul_sum, mul_assoc]

private theorem weight_cancel {n : ℕ} (i : Fin (n - 1)) (c : Kˣ) :
    (c : K) ^ (p ^ (i.val + 1)) * ((c⁻¹ : Kˣ) : K) ^ weight p n i =
      (c : K) ^ (p - 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hle : p ≤ p ^ (i.val + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < p) (by omega : 1 ≤ i.val+1)
  have he : p ^ (i.val + 1) = (p - 1) + weight p n i := by dsimp [weight]; omega
  rw [he, pow_add, mul_assoc, ← mul_pow, ← Units.val_mul]
  simp

theorem scalar_coefficients_iff {n : ℕ} (A B : Fin (n - 1) → K)
    (c : Kˣ) (σ : K ≃ₐ[F] K) :
    (∀ i, (c : K) ^ (p ^ (i.val + 1)) * B i = (c : K) ^ (p - 1) * σ (A i)) ↔
    (∀ i, B i = ((c⁻¹ : Kˣ) : K) ^ weight p n i * σ (A i)) := by
  constructor
  · intro h i
    apply mul_left_cancel₀ (pow_ne_zero (p ^ (i.val + 1)) c.ne_zero)
    rw [h i, ← mul_assoc, weight_cancel]
  · intro h i
    rw [h i, ← mul_assoc, weight_cancel]

/-- Necessity and sufficiency retain the fixed arbitrary original additive
relabeling and allow every invertible merely prime-field-linear intertwiner. -/
theorem fixed_automorphism_coefficients_iff {n : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card K = p ^ n) (A B : Fin (n - 1) → K) (φ : E ≃* E) :
    Intertwines (Q (p := p) n A) (Q (p := p) n B) φ ↔
      ∃ (c : Kˣ) (σ : K ≃ₐ[F] K),
        (∀ a : K, Multiplicative.toAdd (φ (Multiplicative.ofAdd a)) = (c : K)*σ a) ∧
        ∀ i, B i = ((c⁻¹ : Kˣ) : K) ^ weight p n i * σ (A i) := by
  rw [Intertwines, fixed_automorphism_intertwining_iff (Q (p := p) n A) (Q (p := p) n B)
    (coefficientMap (p := p) n A).property (coefficientMap (p := p) n B).property φ]
  constructor
  · rintro ⟨c, σ, δ, hφ, hr⟩
    have hδ := derivation_zero δ
    subst δ
    refine ⟨c, σ, hφ, (scalar_coefficients_iff A B c σ).mp ?_⟩
    have heq : coefficientMap (p := p) n (fun i => (c : K) ^ (p ^ (i.val + 1)) * B i) =
        coefficientMap (p := p) n (fun i => (c : K) ^ (p - 1) * σ (A i)) := by
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      obtain ⟨a, rfl⟩ := σ.surjective x
      change Q (p := p) n _ (σ a) = Q (p := p) n _ (σ a)
      rw [← reference_subtraction, transformed_coordinates]
      have h := hr a
      simp only [Derivation.zero_apply, sub_zero] at h
      linear_combination h
    exact congrFun ((coefficientMap_bijective hn hK).injective heq)
  · rintro ⟨c, σ, hφ, hB⟩
    refine ⟨c, σ, 0, hφ, ?_⟩
    intro a
    have hc := (scalar_coefficients_iff A B c σ).mpr hB
    have he : (fun i => (c : K) ^ (p ^ (i.val + 1)) * B i) =
        (fun i => (c : K) ^ (p - 1) * σ (A i)) := funext hc
    have h := congrArg (fun T => Q (p := p) n T (σ a)) he
    rw [← reference_subtraction, transformed_coordinates] at h
    simp only [Derivation.zero_apply, sub_zero]
    linear_combination h

/-- A scalar-semilinear map constructed as an automorphism of the original group. -/
def parameterAutomorphism (c : Kˣ) (σ : K ≃ₐ[F] K) : E ≃* E :=
  (σ.toLinearEquiv.trans
    ((LinearEquiv.smulOfNeZero K K (c : K) c.ne_zero).restrictScalars F)).toAddEquiv.toMultiplicative

/-- Existential original equivalence is exactly the coefficient relation. -/
theorem original_equivalence_iff {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n)
    (A B : Fin (n - 1) → K) :
    (∃ φ : E ≃* E, Intertwines (Q (p := p) n A) (Q (p := p) n B) φ) ↔
      ∃ (c : Kˣ) (σ : K ≃ₐ[F] K),
        ∀ i, B i = ((c⁻¹ : Kˣ) : K) ^ weight p n i * σ (A i) := by
  constructor
  · rintro ⟨φ, h⟩
    obtain ⟨c, σ, _, hB⟩ := (fixed_automorphism_coefficients_iff hn hK A B φ).mp h
    exact ⟨c, σ, hB⟩
  · rintro ⟨c, σ, hB⟩
    exact ⟨parameterAutomorphism c σ,
      (fixed_automorphism_coefficients_iff hn hK A B _).mpr ⟨c, σ, fun _ => rfl, hB⟩⟩

end D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification
