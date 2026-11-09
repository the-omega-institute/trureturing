/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelQuasipolynomialDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelQuasipolynomialDefs
   mirror-E: none(waiver:q-metallic-quasipolynomial-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Eval.Defs]
   utility: none
   digest: Han-Pedon Conjecture C retains all higher shifts, residues, initial sizes and integer inputs. -/

import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Rat.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Trureturing.OpenProblems.HanPedonShiftedQMetallicHankel

open D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs

/-- Conjecture C of Han and Pedon, arXiv:2610.36132v1.
Existence is a conclusion, and every solution of the defining quadratic is covered.
The stated period need not be minimal. Equality starts at m=0 in every residue;
integer-valuedness includes negative integers. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∃ Φ : PowerSeries ℤ, IsMetallic n Φ) ∧
    ∀ Φ : PowerSeries ℤ, IsMetallic n Φ →
      ∀ ℓ : ℕ, n + 3 ≤ ℓ →
        let ρ : ℕ := if n % 2 = 0 then 2 * n * (n + 1) else 4 * n * (n + 1)
        ∃ Q : Fin ρ → Polynomial ℚ,
          (∀ r : Fin ρ, ∀ z : ℤ, ∃ w : ℤ,
            Polynomial.eval (z : ℚ) (Q r) = (w : ℚ)) ∧
          ∀ r : Fin ρ, ∀ m : ℕ,
            (shiftedHankel Φ ℓ (r.val + m * ρ) : ℚ) =
              Polynomial.eval (m : ℚ) (Q r)

end Trureturing.OpenProblems.HanPedonShiftedQMetallicHankel
