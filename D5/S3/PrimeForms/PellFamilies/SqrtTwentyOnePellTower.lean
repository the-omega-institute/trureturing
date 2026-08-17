/- GID: D5/S3/PrimeForms/PellFamilies/SqrtTwentyOnePellTower
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PellFamilies/SqrtTwentyOnePellTower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The norm-one unit generates a Pell tower of discriminant 21. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.NormNum

namespace D5.S3.PrimeForms.PellFamilies.SqrtTwentyOnePellTower

/-- The rational quadratic algebra with generator squaring to `21`. -/
abbrev SqrtTwentyOneAlgebra := QuadraticAlgebra ℚ 21 0

/-- The norm-four seed `(5, 1)` corresponding to the first tower value `d = 6`. -/
def sqrtTwentyOneSeed : SqrtTwentyOneAlgebra := ⟨5, 1⟩

/-- The norm-one unit `(5 / 2, 1 / 2)` corresponding to `(5 + sqrt 21) / 2`. -/
def sqrtTwentyOneFundamentalUnit : SqrtTwentyOneAlgebra := ⟨5 / 2, 1 / 2⟩

/-- The orbit of the norm-four seed under powers of the fundamental unit. -/
def sqrtTwentyOnePellTower (n : ℕ) : SqrtTwentyOneAlgebra :=
  sqrtTwentyOneSeed * sqrtTwentyOneFundamentalUnit ^ n

/-- Every point in the `sqrt 21` unit orbit remains on the Pell conic
`x^2 - 21y^2 = 4`. -/
theorem sqrt_twenty_one_pell_tower_invariant (n : ℕ) :
    (sqrtTwentyOnePellTower n).re ^ 2 - 21 * (sqrtTwentyOnePellTower n).im ^ 2 = 4 := by
  have hseed : QuadraticAlgebra.norm sqrtTwentyOneSeed = 4 := by
    norm_num [sqrtTwentyOneSeed, QuadraticAlgebra.norm_def]
  have hunit : QuadraticAlgebra.norm sqrtTwentyOneFundamentalUnit = 1 := by
    norm_num [sqrtTwentyOneFundamentalUnit, QuadraticAlgebra.norm_def]
  have hnorm : QuadraticAlgebra.norm (sqrtTwentyOnePellTower n) = 4 := by
    rw [sqrtTwentyOnePellTower, map_mul, map_pow, hseed, hunit]
    simp
  simpa [QuadraticAlgebra.norm_def, pow_two, mul_assoc] using hnorm

end D5.S3.PrimeForms.PellFamilies.SqrtTwentyOnePellTower
