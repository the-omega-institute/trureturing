/- GID: D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported contextual Laurent kernel extraction with every spectator retained. -/

import D5.S3.VertexAlgebra.OrderedCollisionCoordinates

/-! The finite full Hahn antidiagonal controls each convolution fiber.
No cutoff of an expanded intermediate field is assumed.
Hahn series infrastructure: mathlib, Apache 2.0. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction
open SupportedFieldWords.OrderedWords
open OrderedCollisionCoordinates.ContextualLaurentKernel
open CollisionLaurentKernels.LaurentCollision
open scoped BigOperators
variable (K : Type*) [Field K]

private theorem parametric_hahn_convolution {Γ : Type*} [LinearOrder Γ]
    [AddCommGroup Γ] [IsOrderedAddMonoid Γ]
    (U W : HahnSeries Γ K) (p : ℕ → Γ) (injective : Function.Injective p)
    (spans : ∀ a, U.coeff a ≠ 0 → ∃ j, p j = a) (g : Γ) :
    Function.HasFiniteSupport (fun j => U.coeff (p j) * W.coeff (g - p j)) ∧
    (U * W).coeff g = ∑ᶠ j : ℕ, U.coeff (p j) * W.coeff (g - p j) := by
  classical
  let terms (j : ℕ) := U.coeff (p j) * W.coeff (g - p j)
  let pairs := Finset.antidiagonal U.isPWO_support W.isPWO_support g
  have finite : Function.HasFiniteSupport terms := by
    apply (pairs.finite_toSet.preimage
      (show Set.InjOn (fun j => (p j, g - p j)) _ from
        fun j _ k _ h => injective (congrArg Prod.fst h))).subset
    intro j hj
    apply Finset.mem_antidiagonal.mpr
    exact ⟨(mul_ne_zero_iff.mp hj).1, (mul_ne_zero_iff.mp hj).2, by
      rw [add_comm, sub_add_cancel]⟩
  refine ⟨finite, ?_⟩
  rw [HahnSeries.coeff_mul, finsum_eq_sum terms finite]
  symm
  apply Finset.sum_bij_ne_zero (fun j _ _ => (p j, g - p j))
  · intro j hj hn
    apply Finset.mem_antidiagonal.mpr
    exact ⟨(mul_ne_zero_iff.mp hn).1, (mul_ne_zero_iff.mp hn).2, by
      rw [add_comm, sub_add_cancel]⟩
  · intro j hj hn k hk hkn h
    exact injective (congrArg Prod.fst h)
  · intro pair hp hn
    obtain ⟨hu, hw, ht⟩ := Finset.mem_antidiagonal.mp hp
    obtain ⟨j, hj⟩ := spans pair.1 hu
    have second : g - p j = pair.2 := by rw [hj, ← ht]; abel
    refine ⟨j, ?_, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      change terms j ≠ 0
      dsimp only [terms]
      rw [second, hj]
      exact hn
    · dsimp only [terms]
      rw [second, hj]
      exact hn
    · exact Prod.ext hj second
  · intro j hj hn
    rfl

private theorem contextual_kernel_coeff (pre post : ℕ) (r a b : ℤ) :
    (contextPair K pre post (kernelZX K r)).coeff
      (pairIndex pre post (toLex (a, b))) =
      if 0 ≤ a then if b = r - a then
        (-1 : K) ^ a.toNat * ((Ring.choose r a.toNat : ℤ) : K) else 0 else 0 := by
  change (HahnSeries.embDomain (pairEmbedding pre post) (HahnSeries.ofIterate (kernelZX K r))).coeff
    ((pairEmbedding pre post) (toLex (a, b))) = _
  rw [HahnSeries.embDomain_coeff]
  change ((kernelZX K r).coeff a).coeff b = _
  by_cases ha : 0 ≤ a
  · rw [if_pos ha, ← Int.toNat_of_nonneg ha, kernelZX_coeff_nat, HahnSeries.coeff_single]
    simp only [Int.toNat_of_nonneg ha]
  · rw [if_neg ha, kernelZX_coeff_neg K r a (by omega)]
    rfl

/- proof_shape: contextual_kernel_extraction: content
   admission_basis: escape-witness
   escape_witness: the full Hahn antidiagonal bounds each residue fiber, and
   the injective binomial support parametrization reindexes that finite set.
   No field cutoff or positivity of a numerator exponent is assumed. -/
/-- Supported coefficient extraction in an adjacent pair with arbitrary
prefix and suffix. Finiteness follows from the full Hahn support itself. -/
theorem contextual_kernel_extraction (pre post : ℕ) (r : ℤ)
    (W : HahnSeries (Indices ((pre + 2) + post)) K)
    (g : Indices ((pre + 2) + post)) :
    Function.HasFiniteSupport (fun j : ℕ =>
      ((-1 : K) ^ j * ((Ring.choose r j : ℤ) : K)) *
        W.coeff (g - pairIndex pre post (toLex ((j : ℤ), r - j)))) ∧
    (contextPair K pre post (kernelZX K r) * W).coeff g =
      ∑ᶠ j : ℕ, ((-1 : K) ^ j * ((Ring.choose r j : ℤ) : K)) *
        W.coeff (g - pairIndex pre post (toLex ((j : ℤ), r - j))) := by
  let U := contextPair K pre post (kernelZX K r)
  let p (j : ℕ) := pairIndex pre post (toLex ((j : ℤ), r - j))
  have injective : Function.Injective p := by
    intro j k h
    have hpair := (pairEmbedding pre post).injective h
    have hcast := congrArg (fun a : ℤ ×ₗ ℤ => (ofLex a).1) hpair
    exact Int.ofNat_inj.mp hcast
  have spans : ∀ a, U.coeff a ≠ 0 → ∃ j, p j = a := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := HahnSeries.support_embDomain_subset ha
    subst a
    change (contextPair K pre post (kernelZX K r)).coeff
      (pairIndex pre post b) ≠ 0 at ha
    have rep : b = toLex ((ofLex b).1, (ofLex b).2) := rfl
    rw [rep, contextual_kernel_coeff] at ha
    split_ifs at ha with nonnegative diagonal
    · refine ⟨(ofLex b).1.toNat, ?_⟩
      dsimp [p]
      rw [Int.toNat_of_nonneg nonnegative, ← diagonal]
      rfl
    all_goals contradiction
  have coefficient (j : ℕ) :
      U.coeff (p j) = (-1 : K) ^ j * ((Ring.choose r j : ℤ) : K) := by
    dsimp [U, p]
    rw [contextual_kernel_coeff, if_pos (by omega), if_pos rfl, Int.toNat_natCast]
  simpa only [coefficient] using parametric_hahn_convolution K U W p injective spans g

end D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction
