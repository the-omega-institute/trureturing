import OmegaBuild.Commands
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Omega original.

Bilateral translation invariance interchanges two mixed readings at the reflected
point. Testing four-point Gram positivity on two differences bounds their contrast
over a linearly ordered commutative ring.
-/

compile_only_with_mathlib

namespace Omega.Geometry.TransportedContrastEndpoints

open scoped Matrix

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

private theorem determinant_nonneg {A C d : R}
    (h : ∀ u v, 0 ≤ A * u ^ 2 + 2 * d * u * v + C * v ^ 2) : d ^ 2 ≤ A * C := by
  have hA : 0 ≤ A := by simpa using h 1 0
  have hC : 0 ≤ C := by simpa using h 0 1
  rcases hA.eq_or_lt with hA0 | hApos
  · rcases hC.eq_or_lt with hC0 | hCpos
    · simpa [← hA0, ← hC0] using
        (show d ^ 2 ≤ 0 by nlinarith only [h d (-1), hA0, hC0])
    · have hp : 0 ≤ C * (A * C - d ^ 2) := by nlinarith only [h C (-d)]
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hp hCpos)
  · have hp : 0 ≤ A * (A * C - d ^ 2) := by nlinarith only [h (-d) A]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hp hApos)

/-- The point obtained by reflecting through the third point interchanges the mixed
readings. The determinant of the Gram form on the two differences is nonnegative. -/
theorem reflected_contrast_sq_le {M : Type*} (k : M → M → R) (tri : M → M → M → M)
    (hdiag : ∀ a, k a a = 1) (hsymm : ∀ a b, k a b = k b a)
    (hcancelLeft : ∀ a b, tri a a b = b) (hcancelRight : ∀ a b, tri a b b = a)
    (hinvLeft : ∀ a b c d, k (tri a b c) (tri a b d) = k c d)
    (hinvRight : ∀ a b c d, k (tri a c d) (tri b c d) = k a b)
    (hgram : ∀ (p : Fin 4 → M) (c : Fin 4 → R),
      0 ≤ ∑ i, ∑ j, c i * c j * k (p i) (p j)) (x y z : M) :
    (k x z - k y z) ^ 2 ≤ (1 - k x y) * (1 - k z (tri x z y)) := by
  let w := tri x z y
  have hxw : k x w = k y z := by
    simpa only [w, hcancelRight, hsymm z y] using hinvLeft x z z y
  have hyw : k y w = k x z := by
    simpa only [w, hcancelLeft, hsymm z x] using hinvRight z x z y
  apply determinant_nonneg
  intro u v
  have ht := hgram ![x, y, z, w] ![u, -u, v, -v]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    hdiag, hsymm y x, hsymm z x, hsymm z y, hsymm w x, hsymm w y, hsymm w z,
    hxw, hyw] at ht
  change 0 ≤ (1 - k x y) * u ^ 2 + 2 * (k x z - k y z) * u * v + (1 - k z w) * v ^ 2
  nlinarith only [ht]

end Omega.Geometry.TransportedContrastEndpoints
