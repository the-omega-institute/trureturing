/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelDefs
   mirror-E: none(waiver:q-metallic-shifted-hankel-statement-definition)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Han and Pedon's periodicity and value conjecture for the shift n+2 Hankel determinants of q-metallic numbers. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs

open PowerSeries

/-! Fixed public statement: Han and Pedon, *Hankel continued fractions and Hankel determinants for
    q-deformed metallic numbers*, arXiv:2502.05993v2, equations (1.1), (1.2), (2.5) and §1,
    Conjecture E, part 1.  The q-metallic number `Φ_n(q) = ∑ᵢ fᵢ qⁱ` is the power series with
    constant term `1` satisfying `q Φ² + ((1 + qⁿ)(1 - q) - q [n]_q) Φ = 1`, where
    `[n]_q = 1 + q + ⋯ + q^{n-1}`; its coefficients are integers.  The shifted Hankel determinants
    are `Δ_j^{(ℓ)} = det (f_{ℓ+a+b})_{0 ≤ a,b < j}`, with `Δ_0^{(ℓ)} = 1`.  Conjecture E(1): for
    `n ≥ 2` the sequence `Δ^{(n+2)}` satisfies `Δ_{j+2n(n+1)}^{(n+2)} = (-1)ⁿ Δ_j^{(n+2)}` for every
    `j` and takes only the values `-2, -1, 0, 1, 2`.  The statement below asserts that a solution
    of the equation exists and that every solution has these properties. -/

/-- The linear coefficient `(1 + qⁿ)(1 - q) - q [n]_q` of equation (2.5). -/
noncomputable def linearCoeff (n : ℕ) : PowerSeries ℤ :=
  (1 + X ^ n) * (1 - X) - X * ∑ i ∈ Finset.range n, X ^ i

/-- `Φ` is the q-metallic number `Φ_n`: constant term `1` and equation (2.5). -/
def IsMetallic (n : ℕ) (Φ : PowerSeries ℤ) : Prop :=
  PowerSeries.constantCoeff Φ = 1 ∧ X * Φ ^ 2 + linearCoeff n * Φ = 1

/-- The shifted Hankel determinant `Δ_j^{(ℓ)} = det (f_{ℓ+a+b})_{0 ≤ a,b < j}`. -/
noncomputable def shiftedHankel (Φ : PowerSeries ℤ) (ℓ j : ℕ) : ℤ :=
  (Matrix.of fun a b : Fin j => PowerSeries.coeff (ℓ + a + b) Φ).det

/-- Conjecture E, part 1, for every `n ≥ 2`. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → (∃ Φ : PowerSeries ℤ, IsMetallic n Φ) ∧
    ∀ Φ : PowerSeries ℤ, IsMetallic n Φ → ∀ j : ℕ,
      shiftedHankel Φ (n + 2) (j + 2 * n * (n + 1)) = (-1) ^ n * shiftedHankel Φ (n + 2) j ∧
        shiftedHankel Φ (n + 2) j ∈ ({-2, -1, 0, 1, 2} : Finset ℤ)

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs
