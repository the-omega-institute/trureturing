/- GID: D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationEnumeration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationEnumeration
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: none
   digest: Every infinite set has an omega enumeration increasing in any injective natural rank. -/

import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Function

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationEnumeration

/-- Enumerate an infinite set in increasing order of an injective natural-valued rank. -/
theorem enumerateRank {S : Set ℕ} (hS : S.Infinite) (rank : ℕ → ℕ)
    (hinj : Set.InjOn rank S) :
    ∃ π : ℕ → ℕ, Function.Injective π ∧ Set.range π = S ∧
      ∀ i j : ℕ, i < j → rank (π i) < rank (π j) := by
  classical
  have hImage : (rank '' S).Infinite := hS.image hinj
  let q : ℕ → ℕ := Nat.nth (fun n => n ∈ rank '' S)
  have hqmem : ∀ n : ℕ, q n ∈ rank '' S :=
    Nat.nth_mem_of_infinite hImage
  choose π hπmem hπrank using hqmem
  have hqmono : StrictMono q := Nat.nth_strictMono hImage
  refine ⟨π, ?_, ?_, ?_⟩
  · intro i j hij
    apply hqmono.injective
    rw [← hπrank i, ← hπrank j, hij]
  · apply Set.Subset.antisymm
    · rintro x ⟨n, rfl⟩
      exact hπmem n
    · intro x hx
      have hrange : Set.range q = rank '' S := Nat.range_nth_of_infinite hImage
      have hxrank : rank x ∈ Set.range q := hrange.symm ▸ Set.mem_image_of_mem rank hx
      rcases hxrank with ⟨n, hn⟩
      exact ⟨n, hinj (hπmem n) hx ((hπrank n).trans hn)⟩
  · intro i j hij
    rw [hπrank i, hπrank j]
    exact hqmono hij

end D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationEnumeration
