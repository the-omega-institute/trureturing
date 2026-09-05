/- GID: D5/S3/PrimeGaps/ComplementarySupportPatching
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complementary certification regions enlarge a finite nonnegative sieve support and strictly improve its objective when they expose positive new mass. -/

import Mathlib

namespace D5.S3.PrimeGaps.ComplementarySupportPatching

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [Fintype ι]

/-- The support obtained by adjoining every independently certified patch to a base region. -/
def patchedSupport (base : Finset α) (patch : ι → Finset α) : Finset α :=
  base ∪ Finset.univ.biUnion patch

/-- A finite nonnegative objective attached to a support. In sieve applications `weight` is the
local contribution of a coefficient cell or modulus region to the variational functional. -/
def supportMass (weight : α → ℝ) (S : Finset α) : ℝ :=
  ∑ x ∈ S, weight x

/-- Every base point survives complementary patching. -/
theorem base_subset_patchedSupport
    (base : Finset α) (patch : ι → Finset α) :
    base ⊆ patchedSupport base patch := by
  intro x hx
  exact Finset.mem_union_left _ hx

/-- Every point certified by one patch belongs to the patched support, independently of which
other certification mechanisms apply. -/
theorem patch_subset_patchedSupport
    (base : Finset α) (patch : ι → Finset α) (i : ι) :
    patch i ⊆ patchedSupport base patch := by
  intro x hx
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩

/-- Enlarging a support cannot decrease a nonnegative objective. -/
theorem supportMass_mono
    (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    {S T : Finset α} (hST : S ⊆ T) :
    supportMass weight S ≤ supportMass weight T := by
  unfold supportMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => hweight _)

/-- Complementary certification therefore weakly improves every nonnegative finite support
objective. -/
theorem complementary_patching_mass_mono
    (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (base : Finset α) (patch : ι → Finset α) :
    supportMass weight base ≤ supportMass weight (patchedSupport base patch) :=
  supportMass_mono weight hweight (base_subset_patchedSupport base patch)

private theorem supportMass_patched_split
    (weight : α → ℝ) (base : Finset α) (patch : ι → Finset α) :
    supportMass weight (patchedSupport base patch) =
      supportMass weight base +
        supportMass weight ((patchedSupport base patch) \ base) := by
  have hsubset := base_subset_patchedSupport base patch
  have raw := Finset.sum_union
    (f := weight)
    (Finset.disjoint_sdiff : Disjoint base ((patchedSupport base patch) \ base))
  rw [Finset.union_sdiff_of_subset hsubset] at raw
  simpa [supportMass] using raw

/-- Exact escape witness: if one complementary certification region exposes a genuinely new
point carrying positive mass, the patched objective is strictly larger than the base objective.
This is the finite structural reason complementary factorization conditions can improve an
optimized sieve functional when they certify positive-weight cells outside the old support. -/
theorem complementary_patching_mass_strict
    (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (base : Finset α) (patch : ι → Finset α)
    (i : ι) (x : α) (hxpatch : x ∈ patch i) (hxbase : x ∉ base)
    (hxpos : 0 < weight x) :
    supportMass weight base < supportMass weight (patchedSupport base patch) := by
  have hxpatched : x ∈ patchedSupport base patch :=
    patch_subset_patchedSupport base patch i hxpatch
  have hxnew : x ∈ (patchedSupport base patch) \ base :=
    Finset.mem_sdiff.mpr ⟨hxpatched, hxbase⟩
  have hnew_pos : 0 < supportMass weight ((patchedSupport base patch) \ base) := by
    unfold supportMass
    apply Finset.sum_pos'
    · intro y hy
      exact hweight y
    · exact ⟨x, hxnew, hxpos⟩
  rw [supportMass_patched_split]
  linarith

/-- A complementary patch whose newly certified mass exceeds the remaining margin crosses any
prescribed objective threshold. This packages the optimization role separately from the analytic
work needed to certify the patch itself. -/
theorem complementary_patching_crosses_threshold
    (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (base : Finset α) (patch : ι → Finset α) (threshold : ℝ)
    (hgain : threshold - supportMass weight base <
      supportMass weight ((patchedSupport base patch) \ base)) :
    threshold < supportMass weight (patchedSupport base patch) := by
  rw [supportMass_patched_split]
  linarith

#print axioms patchedSupport
#print axioms supportMass
#print axioms base_subset_patchedSupport
#print axioms patch_subset_patchedSupport
#print axioms supportMass_mono
#print axioms complementary_patching_mass_mono
#print axioms complementary_patching_mass_strict
#print axioms complementary_patching_crosses_threshold

end D5.S3.PrimeGaps.ComplementarySupportPatching
