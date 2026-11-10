# Cauchy-Schwarz for positive functionals

## Abstract

Cauchy-Schwarz for positive functionals

For a complex linear functional omega positive on star(a) times a, the squared modulus of omega(star(a) times b) is at most the product of the real values omega(star(a) times a) and omega(star(b) times b). Positivity also gives conjugate symmetry. The quadratic expansion handles the zero diagonal case without division.

**Theorem 1.1 (omega_star_swap_conj).**

$$\forall \{A : Type u_1\} [NonUnitalNonAssocRing.\{u_1\} A] [StarRing.\{u_1\} A] [Module.\{0, u_1\} \mathbb{C} A] [IsScalarTower.\{0, u_1, u_1\} \mathbb{C} A A] [SMulCommClass.\{0, u_1, u_1\} \mathbb{C} A A] [StarModule.\{0, u_1\} \mathbb{C} A] (omega : LinearMap.\{0, 0, u_1, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), (\forall (a : A), LE.le.\{0\} 0 (omega (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} a) a))) \to \forall (a b : A), Eq.\{1\} (omega (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} a) b)) (Star.star.\{0\} (omega (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} b) a)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/CauchySchwarz.omega_star_swap_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity makes every diagonal value real. Expanding the positive values at a+b and at i a+b with omega_expand_add and omega_expand_smul_add gives respectively opposite imaginary parts and equal real parts for the two mixed coefficients. These two identities give complex conjugacy, without continuity or normalization.

**Theorem 1.2 (cauchy_schwarz_inequality).**

$$\forall \{A : Type u_1\} [NonUnitalNonAssocRing.\{u_1\} A] [StarRing.\{u_1\} A] [Module.\{0, u_1\} \mathbb{C} A] [IsScalarTower.\{0, u_1, u_1\} \mathbb{C} A A] [SMulCommClass.\{0, u_1, u_1\} \mathbb{C} A A] [StarModule.\{0, u_1\} \mathbb{C} A] (omega : LinearMap.\{0, 0, u_1, 0\} (RingHom.id.\{0\} \mathbb{C} ) A \mathbb{C} ), (\forall (a : A), LE.le.\{0\} 0 (omega (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} a) a))) \to \forall (a b : A), LE.le.\{0\} (Complex.normSq (omega (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} a) b))) (HMul.hMul.\{0, 0, 0\} (omega (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} a) a)).re (omega (HMul.hMul.\{u_1, u_1, u_1\} (Star.star.\{u_1\} b) b)).re)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/CauchySchwarz.cauchy_schwarz_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use omega_star_swap_conj and omega_expand_smul_add to write positivity at l a+b as a nonnegative Hermitian quadratic in l. If R=Re omega(a* a) is positive, substitute l=-omega(a* b)/R and rearrange. If R=0, a nonzero mixed coefficient would make this quadratic negative for a sufficiently large negative multiple of that coefficient; hence the mixed coefficient vanishes. This includes the degenerate semidefinite case.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/CauchySchwarz.cauchy_schwarz_inequality`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/Physicslib4/GNS/CauchySchwarz.omega_star_swap_conj`
