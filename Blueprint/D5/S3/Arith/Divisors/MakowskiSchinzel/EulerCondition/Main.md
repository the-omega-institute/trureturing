# An Euler-product condition for the sigma-totient inequalities

## Abstract

An Euler-product condition for the sigma-totient inequalities

**Definition 1.1 (Grouping by the largest predecessor prime).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall q \in \mathbb{N},\; q \in \operatorname{topGroup}\left(n, r\right) \Leftrightarrow \left(q \in \operatorname{primeSources}\left(n, r\right) \land q - 1 \in \operatorname{smoothNumbers}\left(r + 1\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main.topGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The group at r consists of the prime divisors q of n for which r divides q-1 and q-1 is (r+1)-smooth. For an odd prime r this means that r is the largest prime factor of q-1. These groups partition the non-Fermat prime support when r ranges over odd primes.

**Theorem 1.2 (A common divisor bounds the reciprocal mass).**

$$\forall Q \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall r \in \mathbb{N},\; \forall D \in \mathbb{N},\; \left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow \operatorname{dvd}\left(D, q - 1\right)\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow \operatorname{natDiv}\left(q - 1, D\right) \in \operatorname{smoothNumbers}\left(r + 1\right)\right) \Rightarrow \left(\sum_{q \in Q} (\frac{r}{q - 1}) \le \frac{r}{D} \cdot \prod_{p \in \operatorname{primesLE}\left(r\right)} (\frac{p}{p - 1}) \land \left(2 \le r \Rightarrow \left(0 < D \Rightarrow \sum_{q \in Q} (\frac{r}{q - 1}) < \frac{r}{D} \cdot \prod_{p \in \operatorname{primesLE}\left(r\right)} (\frac{p}{p - 1})\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main.mass_le_euler_of_common_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be a finite set of natural numbers. Suppose D divides every predecessor q-1 and each quotient (q-1)/D is nonzero with all prime factors at most r. The mass sum r/(q-1) is bounded by r/D times the Euler product through r. The inequality is strict when r>=2 and D>0. No primality or parity assumption is imposed on q or r.

If D=0 the quotient is zero, so Q must be empty. For positive D, the quotient map is injective on Q. Apply the smooth Euler bound to its finite image and multiply by r/D. For r>=2 choose a power of two above every element of the image. It is smooth and missing from the image. Adding its positive reciprocal before applying the same bound proves strictness.

Quotient smoothness is weaker than predecessor smoothness: Q={11}, r=2, D=5 has smooth quotient 2 but predecessor 10. Without divisibility, Q={3,4}, r=1, D=2 has smooth quotients 1,1 but mass 5/6 above bound 1/2. Without smoothness, Q={2,3,4,5}, r=2, D=1 has mass 25/6 above bound 4. Equality occurs for Q={D+1}, r=1, D>0, and for Q empty, D=0; r=0 also gives equality.

**Theorem 1.3 (Labelled groups and actual odd valuations).**

$$\forall n \in \mathbb{N},\; \forall label \in \mathbb{N} \to \mathbb{N},\; \left(\forall a \in \mathbb{N},\; a \in \operatorname{nonFermatFactors}\left(n\right) \Rightarrow \prod_{q \in \operatorname{filterLabel}\left(\operatorname{nonFermatFactors}\left(n\right), label, \operatorname{label}\left(a\right)\right)} (\frac{q}{q - 1}) \le \operatorname{geom}\left(\operatorname{label}\left(a\right), \operatorname{factorization}\left(\operatorname{oddPredecessorPart}\left(n\right), \operatorname{label}\left(a\right)\right)\right)\right) \Rightarrow 1 \le \operatorname{psi}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main.one_le_psi_of_labelled_groups` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Graeme Cohen (1997). *On a conjecture of Mąkowski and Schinzel*. DOI: [10.4064/cm-74-1-1-8](https://doi.org/10.4064/cm-74-1-1-8). URL: <https://doi.org/10.4064/cm-74-1-1-8>.

*Commentary.*

Let Q be the non-Fermat prime support and U its odd predecessor part. Assign each q an arbitrary natural-number label. If every label fibre has product q/(q-1) at most geom(p,v_p(U)), then psi(n)>=1. Factor the full product into its label fibres, apply the local bounds, and identify the resulting geometric product with the abundancy of the selected full valuation components. Their product divides U. Abundancy monotonicity and cancellation of the Euler factors give the conclusion. In fact the local product condition alone suffices: a nonempty fibre has product strictly above one, so its label has positive valuation in U. It is therefore an odd prime dividing U. Divisibility of each individual predecessor by its assigned label is unnecessary. In the comparison with Cohen's condition below, labels are assumed to divide their assigned predecessors.

This repository-derived criterion generalizes the group condition of Cohen 1997 Theorem 3, described in Library/ArithUnits/cohen1997makowski.md: the latter uses group cardinality instead of the full valuation. Every assigned member contributes to that valuation, and the geometric sum is monotone. The capacity form sum p/(q-1)<=1 implies Cohen's group-product bound by the mass-product inequality necessary_mass, and hence implies this criterion. The global condition psi(n)>=1 can instead be used directly with the quantitative sigma-totient theorem.

**Theorem 1.4 (The common-divisor Euler condition).**

$$\forall n \in \mathbb{N},\; \left(\forall r \in \mathbb{N},\; \operatorname{Prime}\left(r\right) \Rightarrow \left(\operatorname{Odd}\left(r\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{topGroup}\left(n, r\right)\right) \Rightarrow r \cdot \prod_{p \in \operatorname{primesLE}\left(r\right)} (\frac{p}{p - 1}) \le \operatorname{gcdPredecessor}\left(\operatorname{topGroup}\left(n, r\right)\right)\right)\right)\right) \Rightarrow \left(n \le 2 \cdot \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right) \land \left(\left(\operatorname{Odd}\left(n\right) \Rightarrow n \le \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{nonFermatFactors}\left(n\right)\right) \Rightarrow \left(n < 2 \cdot \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right) \land \left(\operatorname{Odd}\left(n\right) \Rightarrow n < \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main.makowski_schinzel_of_euler_condition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Graeme Cohen (1997). *On a conjecture of Mąkowski and Schinzel*. DOI: [10.4064/cm-74-1-1-8](https://doi.org/10.4064/cm-74-1-1-8). URL: <https://doi.org/10.4064/cm-74-1-1-8>.

*Commentary.*

For every nonempty group at an odd prime r, suppose its common predecessor divisor is at least r times the Euler product over primes at most r. The smooth reciprocal estimate then bounds the group capacity, the sum of r/(q-1), by one. The finite geometric product inequality converts this capacity into a lower bound for the odd predecessor abundancy. Each group contributes at most the available r-adic valuation, so the product of the geometric factors is at most the abundancy of the odd predecessor part. Consequently psi(n) is at least one, and the quantitative predecessor criterion gives all four displayed inequalities.

The statement includes zero and arbitrary prime multiplicities. The factor two is attained at n=2, the odd inequality at n=1, and the non-Fermat hypothesis supplies the strict inequalities. The Euler condition is sufficient rather than necessary: at n=7, the group at r=3 has common predecessor divisor 6, below r E(r)=9, while its capacity is only 1/2. The same proof uses only the weaker capacity condition, the consequence associated with Cohen's 1997 result; the displayed theorem retains the explicit Euler and common-divisor condition and applies the labelled-group criterion. Here gcdPredecessor(G) is the gcd of q-1 over q in G, with value zero for the empty group.

The literature comparison covers Cohen (1997), Pomerance (1989), Ford (2001/02), Grytczuk, Luca and Wójtowicz (2000), Luca and Pomerance (2002), Pomerance (2026), Sándor (2005), and Grytczuk (2013); the full text of Grytczuk, Luca and Wójtowicz (2001) is unavailable in this comparison.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main.makowski_schinzel_of_euler_condition`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main.mass_le_euler_of_common_dvd`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main.one_le_psi_of_labelled_groups`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main.topGroup`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/Deletion](../Deletion.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion](Criterion.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion](../PrimeDeletion.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/SmoothedGroups](../SmoothPredecessor/SmoothedGroups.md)
