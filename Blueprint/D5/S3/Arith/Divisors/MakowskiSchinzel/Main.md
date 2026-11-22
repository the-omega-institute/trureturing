# The sigma-totient inequality for eta at most forty-two

## Abstract

The sigma-totient inequality for eta at most forty-two

**Theorem 1.1 (Lifting from odd squarefree integers).**

$$\forall T \in \mathbb{N},\; \left(\forall m \in \mathbb{N},\; \operatorname{Odd}\left(m\right) \Rightarrow \left(\operatorname{Squarefree}\left(m\right) \Rightarrow \left(\operatorname{eta}\left(m\right) \le T \Rightarrow 1 \le \operatorname{alpha}\left(m\right)\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \operatorname{eta}\left(n\right) \le T \Rightarrow \left(n \le 2 \cdot \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right) \land \left(\operatorname{Odd}\left(n\right) \Rightarrow n \le \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Main.lift_odd_squarefree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Acknowledgement.* Cohen (1997). *Cohen, Colloquium Mathematicum 74, 1–8*. DOI: [10.4064/cm-74-1-1-8](https://doi.org/10.4064/cm-74-1-1-8). URL: <https://doi.org/10.4064/cm-74-1-1-8>.

*Acknowledgement.* Carl Pomerance (2026). *Pomerance, Mąkowski–Schinzel conjecture preprint*. URL: <https://math.dartmouth.edu/~carlp/msconj2.pdf>.

*Commentary.*

A support-bounded inequality for odd squarefree integers implies the factor-two inequality for all natural integers and the stronger inequality for odd ones. Radical reduction removes all multiplicities; adjoining a single factor of 2 halves the ratio. Zero is included because both natural-number inequalities then have zero on both sides.

**Theorem 1.2 (The stronger odd-integer inequality).**

$$\forall n \in \mathbb{N},\; \operatorname{Odd}\left(n\right) \Rightarrow \left(\operatorname{eta}\left(n\right) \le 42 \Rightarrow 1 \le \operatorname{alpha}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Main.odd_alpha_eta_le_42` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Acknowledgement.* Cohen (1997). *Cohen, Colloquium Mathematicum 74, 1–8*. DOI: [10.4064/cm-74-1-1-8](https://doi.org/10.4064/cm-74-1-1-8). URL: <https://doi.org/10.4064/cm-74-1-1-8>.

*Acknowledgement.* Carl Pomerance (2026). *Pomerance, Mąkowski–Schinzel conjecture preprint*. URL: <https://math.dartmouth.edu/~carlp/msconj2.pdf>.

*Commentary.*

Every odd n with at most forty-two distinct non-Fermat odd prime divisors has alpha(n)>=1. The least odd prime divisor of the totient is either excluded by the finite support inequalities or contradicted by the geometric tail bound. A power-of-two totient is handled separately.

**Theorem 1.3 (Both inequalities with unbounded multiplicity).**

$$\forall n \in \mathbb{N},\; \operatorname{eta}\left(n\right) \le 42 \Rightarrow \left(n \le 2 \cdot \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right) \land \left(\operatorname{Odd}\left(n\right) \Rightarrow n \le \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Acknowledgement.* Cohen (1997). *Cohen, Colloquium Mathematicum 74, 1–8*. DOI: [10.4064/cm-74-1-1-8](https://doi.org/10.4064/cm-74-1-1-8). URL: <https://doi.org/10.4064/cm-74-1-1-8>.

*Acknowledgement.* Carl Pomerance (2026). *Pomerance, Mąkowski–Schinzel conjecture preprint*. URL: <https://math.dartmouth.edu/~carlp/msconj2.pdf>.

*Commentary.*

For every natural n with eta(n)<=42, n<=2 sigma(phi(n)); when n is odd, n<=sigma(phi(n)). Prime exponents are unrestricted, as are n and the sizes of its prime factors. The natural-number convention includes zero. Equality prevents universal strictness: n=2 gives equality in the factor-two bound, and n=1 gives equality in the odd bound. This is the support-bounded partial result toward the Mąkowski–Schinzel conjecture, not its unrestricted settlement. The related numerical ranges n<=10^60 and P(n)<10^6 belong to the cited preprint and are separate from eta(n)<=42. They are not additional premises or conclusions.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Main.lift_odd_squarefree`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/Main.odd_alpha_eta_le_42`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/Deletion](Deletion.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/Fermat](Fermat.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion](PrimeDeletion.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction](Reduction.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/TailFactorization](TailFactorization.md)
