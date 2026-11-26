# Two-hidden-site scalar Schur response

## Abstract

The four scalar coordinates of a two-hidden-site Schur response have an exact image.

**Theorem 1.1 (Exact image for an allowed set of mixing parameters).**

$$\forall (K: Type) [Field K] (T: Set K) (\beta, \gamma, \varepsilon, \zeta : K), (\forall t \in T, t t \neq 1) \implies ((\exists t \in T, \exists a, b, d, e, f: K, \beta = -b d t \land \gamma = -d (e + t f) \land \varepsilon = -a (e + t f) \land \zeta = -b (t e + f)) \iff ((0 \in T \land \beta = 0) \lor ((\exists t \in T, t \neq 0) \land (\beta \neq 0 \lor \gamma = 0 \lor \zeta = 0) \land (\gamma \neq 0 \lor \beta = 0 \lor \varepsilon = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Schur/TwoHiddenScalarResponse.response_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero t, set h = e + tf and k = te + f. The four outputs are products along the path k, b, d, h, a, with a nonzero factor on the edge between b and d. A zero product between two nonzero products is impossible, because the neighboring products force both of its factors to be nonzero. These are exactly the two displayed disjunctions. Conversely, when β = γ = 0 one may take d = 0 and b = h = 1. When β = 0 and γ is nonzero one takes b = 0 and h = 1. When β is nonzero one takes d = 1, b = −β/t and h = −γ. In each case the remaining weights realize the outer products. The formulas e = (h − tk)/(1 − t²) and f = k − te recover the two amplitudes.

At t = 0 the first coordinate vanishes and the other three are arbitrary. For a fixed t, take the singleton set of mixing parameters. For the real interval (−1, 1), take t = 0 when β = 0 and t = 1/2 when β is nonzero and the second disjunction holds. The exact interval image is γ ≠ 0 or β = 0 or ε = 0.

Use the real basis (1, z) of the complex plane with z nonreal. Let the boundary coupling X have rows (a, bz), (d, 0), (e, f), and let the hidden inverse P have unit diagonal and off-diagonal t. In the reduction D − XPX†, the z coefficient of AB, the real coefficient of BC, and the real and z coefficients of AC are the four displayed outputs when the direct AB bond is real, the direct BC bond is on the z line, and the direct AC bond is zero. Choose the two allowed direct bond coefficients to compensate the remaining induced coefficients. For a reduced target Y, set Dᵢᵢ = Yᵢᵢ + (XPX†)ᵢᵢ to prescribe the real diagonals.

For |t| < 1, P is positive definite. Completing the square in the hidden variables makes the full network positive definite exactly when Y is positive definite. The decomposition is Mathlib's Matrix.schur_complement_eq₂₂, and SchurMinimum.schur_quadratic_is_least gives the attained boundary minimum. Any attainable off-diagonal data admit a positive definite completion by choosing each reduced diagonal greater than the sum of the moduli of the other entries in its row.

For the Chapter 39 wound target with |z| = 1, the off-diagonal entries p conjugate(z), qz², rz have coordinates (β, γ, ε, ζ) = (−p, −q, 0, r). This follows from conjugate(z) = 2 Re(z) − z and z² = 2 Re(z)z − 1. The interval criterion therefore holds for all real p, q, r, including zeros. With a positive definite wound target this gives a positive definite lift in the prescribed local network. The Lean statement classifies the scalar equations. The phase-coordinate and positive definite interpretations use the matrix decomposition above.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/Schur/TwoHiddenScalarResponse.response_iff`
