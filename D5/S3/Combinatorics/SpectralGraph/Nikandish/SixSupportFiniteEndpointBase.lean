/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteEndpointBase
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportFiniteEndpointBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite endpoint domains and their actual ideal-graph consumer. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Tactic

/-! This finite endpoint route consumes the full already-proved uniform low-root
supplier. It retains all325 and27562 original triples. It does not claim to
reproduce the manuscript's distinct discriminant/Sylvester/Bareiss certificates. -/

set_option autoImplicit false
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportFiniteEndpointBase

open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra
open D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift (exponents)
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

/-- The source cutoff, with exact natural-number domain. -/
def cutoff (a : ℕ) : ℕ := 4*a*a-2*a

/-- Both possible integer low-root endpoints at an exact original triple. -/
def endpointTest (a b c : ℕ) : Bool :=
  decide (value (a : ℤ) (b : ℤ) (c : ℤ) 1 ≠ 0 ∧ value (a : ℤ) (b : ℤ) (c : ℤ) 2 ≠ 0)

/-- Every b,c in the complete a<b<c<4a²-2a domain. -/
def base (a : ℕ) : Bool :=
  (List.range (cutoff a)).all fun b =>
    if a < b then (List.range (cutoff a)).all fun c =>
      if b < c then endpointTest a b c else true
    else true

/-- Canonical once-per-pair enumeration of precisely the same finite domain. -/
def domain (a : ℕ) : List (ℕ × ℕ) :=
  (List.range (cutoff a)).flatMap fun b =>
    ((List.range (cutoff a)).filter fun c => a < b ∧ b < c).map fun c => (b,c)

/-- Membership is exactly the original inequalities; no source row is omitted. -/
theorem mem_domain (a b c : ℕ) : (b,c) ∈ domain a ↔ a < b ∧ b < c ∧ c < cutoff a := by
  simp only [domain, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨b', hb', c', ⟨hc', hab', hbc'⟩, hb, hc⟩
    subst b'; subst c'
    exact ⟨hab', hbc', hc'⟩
  · rintro ⟨hab, hbc, hc⟩
    exact ⟨b, hbc.trans hc, c, ⟨hc, hab, hbc⟩, rfl, rfl⟩

/-- Complete Boolean checking is consumed as exact integer endpoint inequalities. -/
theorem base_sound (a b c : ℕ) (h : base a = true)
    (hab : a < b) (hbc : b < c) (hc : c < cutoff a) :
    value (a : ℤ) (b : ℤ) (c : ℤ) 1 ≠ 0 ∧ value (a : ℤ) (b : ℤ) (c : ℤ) 2 ≠ 0 := by
  have hb : b ∈ List.range (cutoff a) := List.mem_range.mpr (hbc.trans hc)
  have h1 := List.all_eq_true.mp h b hb
  simp only [hab, ↓reduceIte] at h1
  have h2 := List.all_eq_true.mp h1 c (List.mem_range.mpr hc)
  simp only [hbc, ↓reduceIte] at h2
  exact of_decide_eq_true h2

/-- The complete finite domain has an actual graph consumer. -/
theorem actual_nonintegral (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0 < a)
    (hab : a < b) (hbc : b < c) (hc : c < cutoff a) (h : base a = true) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  intro hint
  have hh := base_sound a b c h hab hbc hc
  rcases endpoint_one_or_two p hp hinj a b c ha hab.le hbc.le hint with h1 | h2
  · apply hh.1
    rw [h_eq_value] at h1
    dsimp [value] at h1 ⊢
    exact_mod_cast h1
  · apply hh.2
    rw [h_eq_value] at h2
    dsimp [value] at h2 ⊢
    exact_mod_cast h2

end D5.S3.Combinatorics.SpectralGraph.SixSupportFiniteEndpointBase
