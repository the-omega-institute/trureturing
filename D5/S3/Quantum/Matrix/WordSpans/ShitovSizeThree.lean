/- GID: D5/S3/Quantum/Matrix/WordSpans/ShitovSizeThree
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/WordSpans/ShitovSizeThree
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The least positive universal exact word length in the complex three-by-three matrix algebra is seven. -/

import OmegaMath.Matrix.HomogeneousWordPowersSharpThree
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false

open scoped Pointwise
open OmegaMath.HomogeneousWordPowers

namespace D5.S3.Quantum.Matrix.WordSpans.ShitovSizeThree

local notation "Mat3C" => Matrix (Fin 3) (Fin 3) ℂ

/-- The complex span of all ordered products of precisely `k` members of `S`. -/
def exactWordSpan (S : Set Mat3C) (k : ℕ) : Submodule ℂ Mat3C :=
  Submodule.span ℂ (Set.range fun f : Fin k → S =>
    (List.ofFn fun i => (f i : Mat3C)).prod)

/-- In Shitov’s Question 2, the least positive universal exact word length in size three is seven. -/
theorem result :
    IsLeast {k : ℕ | 0 < k ∧ ∀ S : Set Mat3C,
      (∃ m : ℕ, 0 < m ∧ exactWordSpan S m = ⊤) → exactWordSpan S k = ⊤} 7 := by
  have hwords (S : Set Mat3C) (k : ℕ) : exactWordSpan S k = Submodule.span ℂ (S ^ k) := by
    unfold exactWordSpan
    congr 1
    ext X
    exact Set.mem_pow.symm
  letI : Infinite ℂ := Infinite.of_injective _ Complex.ofReal_injective
  simpa only [hwords] using (isLeast_full_word_length_three (K := ℂ))

end D5.S3.Quantum.Matrix.WordSpans.ShitovSizeThree
