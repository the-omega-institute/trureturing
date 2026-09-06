/- GID: D5/S0/Certificates/CheckedLinearImage
   generality: G
   mirror-B: D5/B/S0/Certificates/CheckedLinearImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rational primal-dual checks certify full query images over ordered fields. -/

import D5.S0.Certificates.RationalFarkas

/-!
# Checked rational certificates across the scalar boundary

Raw numerical payloads contain no proof fields. Acceptance is checked against
the caller's matrix, right-hand side, and objective. It determines the complete
query image over any linearly ordered field, including real irrational targets.
This supplies the paper's missing rational-certificate to real-range bridge.

Library search: RationalFarkas supplies the rational refutation interface;
Mathlib supplies dot-product monotonicity and matrix associativity, convex
halfspaces, linear images, and order-connectedness. Those facts are reused.
The paper's LinearObjectiveDual module is absent from this pinned worktree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.CheckedLinearImage

open scoped BigOperators Matrix
open D5.S0.Certificates.RationalFarkas

variable {C V : Type*} [Fintype C] [Fintype V]

/-- Untrusted rational endpoints, primal vectors, and dual row multipliers. -/
structure RawSharpPayload (C V : Type*) where
  lower : ℚ
  upper : ℚ
  xLower : V → ℚ
  xUpper : V → ℚ
  yLower : C → ℚ
  yUpper : C → ℚ

/-- Check nonnegative multipliers, the column identity, and the RHS bound. -/
def checkUpper (A : C → V → ℚ) (b : C → ℚ) (c : V → ℚ)
    (upper : ℚ) (y : C → ℚ) : Bool :=
  decide ((∀ i, 0 ≤ y i) ∧
    (∀ j, (∑ i, y i * A i j) = c j) ∧ (∑ i, y i * b i) ≤ upper)

/-- Check both dual bounds and both matching feasible primal endpoints. -/
def checkSharp (A : C → V → ℚ) (b : C → ℚ) (c : V → ℚ)
    (p : RawSharpPayload C V) : Bool :=
  checkUpper A b (fun j => -c j) (-p.lower) p.yLower &&
    checkUpper A b c p.upper p.yUpper &&
    decide ((∀ i, (∑ j, A i j * p.xLower j) ≤ b i) ∧
      (∀ i, (∑ j, A i j * p.xUpper j) ≤ b i) ∧
      (∑ j, c j * p.xLower j) = p.lower ∧
      (∑ j, c j * p.xUpper j) = p.upper)

/-- Check a raw rational Farkas multiplier against the authoritative system. -/
def checkFarkas (A : C → V → ℚ) (b : C → ℚ) (y : C → ℚ) : Bool :=
  decide ((∀ i, 0 ≤ y i) ∧
    (∀ j, (∑ i, y i * A i j) = 0) ∧ (∑ i, y i * b i) < 0)

/-- Successful raw checking constructs the existing rational proof-bearing record. -/
def farkasCertificateOfCheck (A : C → V → ℚ) (b : C → ℚ) (y : C → ℚ)
    (hcheck : checkFarkas A b y = true) : Certificate A b := by
  have h := of_decide_eq_true hcheck
  exact ⟨y, h.1, h.2.1, h.2.2⟩

/-- Farkas replay reuses the repository's rational infeasibility theorem. -/
theorem checked_rational_infeasible (A : C → V → ℚ) (b : C → ℚ) (y : C → ℚ)
    (hcheck : checkFarkas A b y = true) :
    ¬∃ x : V → ℚ, LinearFeasible A b x :=
  infeasible_of_certificate A b (farkasCertificateOfCheck A b y hcheck)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A checked rational upper multiplier bounds every feasible vector over K. -/
theorem checked_upper_bound (A : C → V → ℚ) (b : C → ℚ) (c : V → ℚ)
    (upper : ℚ) (y : C → ℚ) (hcheck : checkUpper A b c upper y = true)
    (x : V → K) (hx : ∀ i, (∑ j, (A i j : K) * x j) ≤ (b i : K)) :
    (∑ j, (c j : K) * x j) ≤ (upper : K) := by
  have h := of_decide_eq_true hcheck
  have hy : (0 : C → K) ≤ fun i => (y i : K) := by
    intro i
    change (0 : K) ≤ (y i : K)
    exact_mod_cast h.1 i
  let AK : Matrix C V K := Matrix.of fun i j => (A i j : K)
  have hc : (fun i => (y i : K)) ᵥ* AK =
      fun j => (c j : K) := by
    funext j
    change (∑ i, (y i : K) * (A i j : K)) = (c j : K)
    exact_mod_cast h.2.1 j
  have hb : (∑ i, (y i : K) * (b i : K)) ≤ (upper : K) := by
    exact_mod_cast h.2.2
  calc
    (∑ j, (c j : K) * x j) =
        (fun i => (y i : K)) ⬝ᵥ (AK *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec, hc]
      rfl
    _ ≤ (fun i => (y i : K)) ⬝ᵥ (fun i => (b i : K)) :=
      dotProduct_le_dotProduct_of_nonneg_left hx hy
    _ ≤ (upper : K) := hb

/-- Accepted rational endpoint data give exactly the whole interval over K.
No convexity, boundedness, nonemptiness, or distinct-endpoint premise is needed. -/
theorem checked_query_image (A : C → V → ℚ) (b : C → ℚ) (c : V → ℚ)
    (p : RawSharpPayload C V) (hcheck : checkSharp A b c p = true) :
    (fun x : V → K => ∑ j, (c j : K) * x j) ''
      {x | ∀ i, (∑ j, (A i j : K) * x j) ≤ (b i : K)} =
        Set.Icc (p.lower : K) (p.upper : K) := by
  simp only [checkSharp, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨hlo, hup⟩, hxl, hxu, hvl, hvu⟩
  have hl : (p.lower : K) ∈
      (fun x : V → K => ∑ j, (c j : K) * x j) ''
        {x | ∀ i, (∑ j, (A i j : K) * x j) ≤ (b i : K)} := by
    refine ⟨fun j => (p.xLower j : K), ?_, ?_⟩
    · intro i
      change (∑ j, (A i j : K) * (p.xLower j : K)) ≤ (b i : K)
      exact_mod_cast hxl i
    · change (∑ j, (c j : K) * (p.xLower j : K)) = (p.lower : K)
      exact_mod_cast hvl
  have hu : (p.upper : K) ∈
      (fun x : V → K => ∑ j, (c j : K) * x j) ''
        {x | ∀ i, (∑ j, (A i j : K) * x j) ≤ (b i : K)} := by
    refine ⟨fun j => (p.xUpper j : K), ?_, ?_⟩
    · intro i
      change (∑ j, (A i j : K) * (p.xUpper j : K)) ≤ (b i : K)
      exact_mod_cast hxu i
    · change (∑ j, (c j : K) * (p.xUpper j : K)) = (p.upper : K)
      exact_mod_cast hvu
  have hconv : Convex K
      {x : V → K | ∀ i, (∑ j, (A i j : K) * x j) ≤ (b i : K)} := by
    simp only [Set.ofPred_forall]
    exact convex_iInter fun i => (convex_Iic (b i : K)).linear_preimage
      (dotProductBilin K K (fun j => (A i j : K)))
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    have h := checked_upper_bound A b (fun j => -c j) (-p.lower) p.yLower hlo x hx
    simp only [Rat.cast_neg, neg_mul, Finset.sum_neg_distrib] at h
    exact ⟨neg_le_neg_iff.mp h, checked_upper_bound A b c p.upper p.yUpper hup x hx⟩
  · exact (hconv.linear_image
      (dotProductBilin K K (fun j => (c j : K)))).ordConnected.out hl hu

/-- The real specialization includes irrational targets and real mass vectors. -/
theorem checked_real_query_image (A : C → V → ℚ) (b : C → ℚ) (c : V → ℚ)
    (p : RawSharpPayload C V) (hcheck : checkSharp A b c p = true) :
    (fun x : V → ℝ => ∑ j, (c j : ℝ) * x j) ''
      {x | ∀ i, (∑ j, (A i j : ℝ) * x j) ≤ (b i : ℝ)} =
        Set.Icc (p.lower : ℝ) (p.upper : ℝ) :=
  checked_query_image A b c p hcheck

/-- Accepted rational Farkas data exclude feasible vectors over every K. -/
theorem checked_infeasible (A : C → V → ℚ) (b : C → ℚ) (y : C → ℚ)
    (hcheck : checkFarkas A b y = true) :
    ¬∃ x : V → K, ∀ i, (∑ j, (A i j : K) * x j) ≤ (b i : K) := by
  have cert := of_decide_eq_true hcheck
  have hu : checkUpper A b (fun _ => 0) (∑ i, y i * b i) y = true := by
    apply decide_eq_true
    exact ⟨cert.1, cert.2.1, le_rfl⟩
  rintro ⟨x, hx⟩
  have h := checked_upper_bound A b (fun _ => 0) (∑ i, y i * b i) y hu x hx
  have hn : ((∑ i, y i * b i : ℚ) : K) < 0 := by
    exact_mod_cast cert.2.2
  simp only [Rat.cast_zero, zero_mul, Finset.sum_const_zero] at h
  exact (not_lt_of_ge h) hn

end D5.S0.Certificates.CheckedLinearImage
