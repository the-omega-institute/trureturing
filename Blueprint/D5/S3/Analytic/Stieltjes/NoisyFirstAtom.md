# Enclosing the first atom from noisy Stieltjes samples

## Abstract

A finite set of noisy samples of a normalized positive Stieltjes transform bounds its smallest atom.

**Definition 1.1 (Signed forward difference).**

Lean statement: `D5/S3/Analytic/Stieltjes/NoisyFirstAtom.difference`

*Formalization.* `D5/S3/Analytic/Stieltjes/NoisyFirstAtom.difference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At order zero take the initial sample. At each higher order subtract the same difference on the grid shifted by one node.

**Definition 1.2 (Product over positive grid nodes).**

Lean statement: `D5/S3/Analytic/Stieltjes/NoisyFirstAtom.poleProduct`

*Formalization.* `D5/S3/Analytic/Stieltjes/NoisyFirstAtom.poleProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P is the product of x+jh for j from 1 to k. The empty product equals one.

**Theorem 1.3 (Finite-precision enclosure of the first atom).**

$$1 \le SaP(D+e),\ P(D-e) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Stieltjes/NoisyFirstAtom.noisy_first_atom_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be the smallest positive atom of a discrete probability distribution. Its masses p_i are nonnegative, their sum is one, and the mass p_0 at a satisfies S a p_0 ≥ 1 for a known S > 0. The normalized reading at u is the sum of p_i b_i/(b_i+u). On the equally spaced grid starting at zero with step h > 0 the first reading is known exactly as one. Each of the k positive-node readings has absolute error at most ε.

D is the order-k signed difference of the measured grid divided by k! h^k. Its error bound e equals (2^k−1)ε/(k! h^k), and P denotes the positive-node product at a. The difference of each exact single-atom resolvent contributes the inverse product of b_i+jh over j from 1 to k. Absolute summability permits the finite difference to pass through the sum. Each term lies below its mass times the inverse product at a, and retaining the first term gives the other inequality.

For positive k, monotonicity gives a lower endpoint for a from the first inequality. The second gives a finite upper endpoint when D−e is positive and the data are consistent.

## References

- Truth anchor: `D5/S3/Analytic/Stieltjes/NoisyFirstAtom.difference`
- Truth anchor: `D5/S3/Analytic/Stieltjes/NoisyFirstAtom.noisy_first_atom_enclosure`
- Truth anchor: `D5/S3/Analytic/Stieltjes/NoisyFirstAtom.poleProduct`
