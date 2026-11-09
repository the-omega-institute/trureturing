# Prime-power content of cyclic differences

## Abstract

The content of every positive cyclic difference is a prime power.

**Definition 1.1 (Differences of a single occupied block).**

$$\begin{aligned}\forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], \forall j: \operatorname{ZMod}\left(p\right), \operatorname{coeff}\left(p, 0, j\right) = \operatorname{ite}\left(j = 1, 1, 0\right)\\\forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], \forall r: \mathbb{N}, \forall j: \operatorname{ZMod}\left(p\right), \operatorname{coeff}\left(p, r + 1, j\right) = \operatorname{coeff}\left(p, r, j\right) - \operatorname{coeff}\left(p, r, j - 1\right)\end{aligned}$$

*Formalization.* `D5/S3/Arith/Primes/CyclicDifferencePrimeContent.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial coefficient is one at residue one and zero elsewhere. Each next row is the cyclic difference of its predecessor.

**Theorem 1.2 (Annihilating coefficients force prime-power order).**

$$\forall G: Type, [\operatorname{Group}\left(G\right)], \forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], (\operatorname{Nat}.\operatorname{Prime}(p)) \Rightarrow \forall g: G, \forall r: \mathbb{N}, (\forall j: \operatorname{ZMod}\left(p\right), g^{\operatorname{coeff}\left(p, r + 1, j\right)} = 1) \Rightarrow \exists m: \mathbb{N}, \operatorname{orderOf}\left(g\right) = p^{m}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/CyclicDifferencePrimeContent.order_prime_power_of_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. T. Anderson and M. Weippert (2024). *Controlled Gates in the Clifford Hierarchy*. DOI: [10.48550/arXiv.2410.04711](https://doi.org/10.48550/arXiv.2410.04711). URL: <https://arxiv.org/abs/2410.04711v3>.

*Commentary.*

For any group element, annihilation by every coefficient makes its order divide their gcd. A divisor of a power of p is itself a power of p.

## References

- Truth anchor: `D5/S3/Arith/Primes/CyclicDifferencePrimeContent.coeff`
- Truth anchor: `D5/S3/Arith/Primes/CyclicDifferencePrimeContent.order_prime_power_of_coeff`
