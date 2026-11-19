/- GID: D5/S3/FiniteGroups/GroupAlgebra/FiniteJetOrbits
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/FiniteJetOrbits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The quotient of actual normalized original jet representations has the full weighted divisor cardinality. -/
import D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification
import D5.S3.FiniteGroups.Semilinear.WeightedOrbits
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.Data.Fintype.Shrink

/-! Actual original representation classes and finite-field orbit transport. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits
open FiniteJetCoefficients FiniteJetClassification OddPrimeJetDeformation
open scoped BigOperators
universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Fintype K] [Algebra (ZMod p) K]
local notation "𝔽" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "E" => Multiplicative K

/-- Actual representations in the normalized original family, with no chosen coefficient data. -/
def OriginalFamily := {ρ : Representation 𝔽 E V //
  ∃ q : Normalized (p := p) (K := K), originalRepresentation q.val = ρ}

/-- Both original relabelings and merely prime-field-linear intertwiners are arbitrary. -/
def originalSetoid : Setoid (OriginalFamily (p := p) (K := K)) where
  r ρ τ := ∃ (φ : E ≃* E) (P : V ≃ₗ[𝔽] V), ∀ (g : E) (v : V),
    P (ρ.val g v) = τ.val (φ g) (P v)
  iseqv := by
    constructor
    · intro ρ
      exact ⟨MulEquiv.refl E, LinearEquiv.refl 𝔽 V, fun _ _ => rfl⟩
    · rintro ρ τ ⟨φ, P, h⟩
      refine ⟨φ.symm, P.symm, ?_⟩
      intro g v
      apply P.injective
      rw [P.apply_symm_apply, h, φ.apply_symm_apply, P.apply_symm_apply]
    · rintro ρ τ υ ⟨φ, P, hP⟩ ⟨ψ, R, hR⟩
      refine ⟨φ.trans ψ, P.trans R, ?_⟩
      intro g v
      change R (P (ρ.val g v)) = υ.val (ψ (φ g)) (R (P v))
      rw [hP, hR]

/-- The quotient of the actual original representations, not a parameter-space surrogate. -/
abbrev OriginalClasses := Quotient (originalSetoid (p := p) (K := K))

private def ofCoefficients (n : ℕ) (A : Fin (n - 1) → K) :
    OriginalFamily (p := p) (K := K) :=
  ⟨originalRepresentation (Q (p := p) n A), coefficientMap (p := p) n A, rfl⟩

private theorem related_coefficients {n : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card K = p ^ n) (A B : Fin (n - 1) → K) :
    originalSetoid (ofCoefficients (p := p) n A) (ofCoefficients (p := p) n B) ↔
      ∃ (c : Kˣ) (σ : K ≃ₐ[𝔽] K),
        ∀ i, B i = ((c⁻¹ : Kˣ) : K) ^ weight p n i * σ (A i) :=
  original_equivalence_iff hn hK A B

section Transport
variable {L : Type} [Field L] [Fintype L] [Algebra (ZMod p) L]

private theorem relation_transport {n : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card K = p ^ n) (e : K ≃ₐ[𝔽] L) (A B : Fin (n - 1) → L) :
    originalSetoid (ofCoefficients (p := p) n (fun i => e.symm (A i)))
      (ofCoefficients (p := p) n (fun i => e.symm (B i))) ↔
      letI := WeightedSemilinear.weightedAction (F := 𝔽) (K := L) (weight p n)
      MulAction.orbitRel (WeightedSemilinear.Group 𝔽 L) (Fin (n - 1) → L) A B := by
  letI := WeightedSemilinear.weightedAction (F := 𝔽) (K := L) (weight p n)
  constructor
  · intro h
    obtain ⟨c, σ, hB⟩ := (related_coefficients hn hK _ _).mp h
    apply (MulAction.orbitRel (WeightedSemilinear.Group 𝔽 L) (Fin (n - 1) → L)).symm
    change ∃ g : WeightedSemilinear.Group 𝔽 L, WeightedSemilinear.act (weight p n) g A = B
    refine ⟨⟨Units.map e.toMonoidHom c, e.symm.trans (σ.trans e)⟩, ?_⟩
    funext i
    have h := congrArg e (hB i)
    simpa [WeightedSemilinear.act, map_mul, map_pow] using h.symm
  · intro h
    apply (originalSetoid (p := p) (K := K)).symm
    apply (related_coefficients hn hK _ _).mpr
    change ∃ g : WeightedSemilinear.Group 𝔽 L, WeightedSemilinear.act (weight p n) g B = A at h
    obtain ⟨g, hg⟩ := h
    refine ⟨Units.map e.symm.toMonoidHom g.left, e.trans (g.right.trans e.symm), ?_⟩
    intro i
    have h := congrArg (fun T => e.symm (T i)) hg
    simpa [WeightedSemilinear.act, map_mul, map_pow] using h.symm

private def orbitToOriginal {n : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card K = p ^ n) (e : K ≃ₐ[𝔽] L) :
    WeightedSemilinear.Orbits (F := 𝔽) (K := L) (weight p n) →
      OriginalClasses (p := p) (K := K) := by
  letI := WeightedSemilinear.weightedAction (F := 𝔽) (K := L) (weight p n)
  exact Quotient.map (fun A => ofCoefficients (p := p) n (fun i => e.symm (A i)))
    (fun A B h => (relation_transport hn hK e A B).mpr h)

/-- Any actual prime-field algebra equivalence transports the full original
representation quotient to the native weighted semilinear orbit quotient. -/
def quotientEquiv {n : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card K = p ^ n) (e : K ≃ₐ[𝔽] L) :
    OriginalClasses (p := p) (K := K) ≃
      WeightedSemilinear.Orbits (F := 𝔽) (K := L) (weight p n) := by
  letI := WeightedSemilinear.weightedAction (F := 𝔽) (K := L) (weight p n)
  apply Equiv.symm
  refine Equiv.ofBijective (orbitToOriginal hn hK e) ⟨?_, ?_⟩
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro A B h
    exact Quotient.sound ((relation_transport hn hK e A B).mp (Quotient.exact h))
  · intro z
    refine Quotient.inductionOn z ?_
    intro ρ
    obtain ⟨q, hq⟩ := ρ.property
    obtain ⟨A, hA⟩ := (coefficientEquiv hn hK).surjective q
    have hA' : coefficientMap (p := p) n A = q := hA
    refine ⟨Quotient.mk _ (fun i => e (A i)), ?_⟩
    change Quotient.mk _ (ofCoefficients (p := p) n (fun i => e.symm (e (A i)))) = Quotient.mk _ ρ
    have he : ofCoefficients (p := p) n (fun i => e.symm (e (A i))) = ρ := by
      apply Subtype.ext
      change originalRepresentation (Q (p := p) n (fun i => e.symm (e (A i)))) = ρ.val
      simp only [AlgEquiv.symm_apply_apply]
      change originalRepresentation (coefficientMap (p := p) n A).val = ρ.val
      rw [hA']
      exact hq
    rw [he]
end Transport

/-- All original field universes are retained through an explicit finite-field
algebra transport to the small field used by the native counting theorem. -/
theorem original_class_cardinality {n : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card K = p ^ n) :
    (Nat.card (OriginalClasses (p := p) (K := K)) : ℚ) =
      (1 / (n : ℚ)) *
        ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) / (p ^ d - 1 : ℕ) *
          ∑ m ∈ (p ^ d - 1).divisors, (Nat.totient m : ℚ) *
            (p : ℚ) ^ (d * (Finset.univ.filter (fun i : Fin (n - 1) => m ∣ weight p n i)).card) := by
  let L := Shrink.{0} K
  let e : K ≃ₐ[𝔽] L := (@Shrink.algEquiv 𝔽 K (inferInstance : Small.{0} K) _ _ _).symm
  have hL : Fintype.card L = p ^ n := by simpa [L] using hK
  rw [Nat.card_congr (quotientEquiv hn hK e)]
  exact WeightedSemilinear.orbit_cardinality p n (weight p n) hL

#print axioms original_class_cardinality
end D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits
