/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedDefs
   mirror-E: none(waiver:q-metallic-unbounded-hankel-statement-definition)
   anchors: []
   utility: none
   digest: Han and Pedon's conjecture that the Hankel determinants of q-metallic numbers are unbounded from the shift n+3 on. -/

import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedDefs

open MetallicHankelDefs

/-! Fixed public statement: Han and Pedon, *Hankel continued fractions and Hankel determinants for
    q-deformed metallic numbers*, arXiv:2502.05993v2, §1, Conjecture E, part 2, with the varying
    shift `ℓ` in place of the printed superscript `n + 2`: for `ℓ ≥ n + 3` the sequence
    `(Δ_j^{(ℓ)}(Φ_n))_{j ≥ 0}` is unbounded.  The q-metallic number `Φ_n` and the shifted Hankel
    determinants are those of `MetallicHankelDefs`.  The statement below asserts that a solution
    of the defining equation exists for every `n ≥ 1` and that for every solution and every shift
    `ℓ ≥ n + 3`, each bound `M` is exceeded by some `|Δ_j^{(ℓ)}|`. -/

/-- Conjecture E, part 2, for every `n ≥ 1`. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → (∃ Φ : PowerSeries ℤ, IsMetallic n Φ) ∧
    ∀ Φ : PowerSeries ℤ, IsMetallic n Φ → ∀ ℓ : ℕ, n + 3 ≤ ℓ → ∀ M : ℕ,
      ∃ j : ℕ, M < (shiftedHankel Φ ℓ j).natAbs

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedDefs
