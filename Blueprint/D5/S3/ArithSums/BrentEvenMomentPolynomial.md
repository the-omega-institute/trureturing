# Integer coefficients of the even double binomial moment

## Abstract

Even double binomial moments admit ordinary integer coefficient polynomials.

Brent, Ohtsuka, Osborn and Prodinger, Some Binomial Sums Involving Absolute Values, Journal of Integer Sequences 19, Article 16.3.7, section 3.3, page 10 immediately after Theorem 9, ask whether the coefficients of 2^(r-4n) W_(2r)(n) are integers. The equivalent cleared identity below takes place in Rat. Both indices range over all natural numbers, including zero, and every zeroth power is one. Polynomial Int is the ordinary polynomial ring with integer monomial coefficients. The polynomial is chosen before n is quantified.

**Definition 1.1 (The binomial convention).**

$$\forall N \in \mathrm{Nat},\; \forall k \in \mathrm{Int},\; \operatorname{binomial}\left(N, k\right) = \operatorname{ite}\left(0 \le k, \operatorname{Nat}.\operatorname{choose}\left(N, \operatorname{Int}.\operatorname{toNat}\left(k\right)\right), 0\right)$$

*Formalization.* `D5/S3/ArithSums/BrentEvenMomentPolynomial.binomial` (`✓ std3`).

*Citation.* Richard P. Brent, Hideyuki Ohtsuka, Judy-anne H. Osborn, Helmut Prodinger (2016). *Some Binomial Sums Involving Absolute Values*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex>.

*Commentary.*

The upper index N is natural and the lower index k is integral. Nat.choose is zero when its lower index exceeds N. The displayed value is cast to Rat.

**Definition 1.2 (The original double sum).**

$$\forall beta \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \operatorname{W}\left(beta, n\right) = \sum_{i \in \operatorname{Icc}\left(-n, n\right)} \sum_{j \in \operatorname{Icc}\left(-n, n\right)} \operatorname{binomial}\left(2 \cdot n, n + i\right) \cdot \operatorname{binomial}\left(2 \cdot n, n + j\right) \cdot \left|i^{2} - j^{2}\right|^{beta}$$

*Formalization.* `D5/S3/ArithSums/BrentEvenMomentPolynomial.W` (`✓ std3`).

*Citation.* Richard P. Brent, Hideyuki Ohtsuka, Judy-anne H. Osborn, Helmut Prodinger (2016). *Some Binomial Sums Involving Absolute Values*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex>.

*Commentary.*

Both integer intervals include their endpoints. The squared indices and the binomial values are interpreted in Rat. In particular the only summand when n=0 uses i=j=0, and its weight is one when beta=0.

**Definition 1.3 (The coefficient assertion).**

$$claim \Leftrightarrow \left(\forall r \in \mathrm{Nat},\; \exists P \in \operatorname{Polynomial}\left(\mathrm{Int}\right),\; \forall n \in \mathrm{Nat},\; 2^{4 \cdot n} \cdot \left(\operatorname{Polynomial}.\operatorname{eval}_{2}\right)\left(\operatorname{Int}.\operatorname{castRingHom}\left(\mathrm{Rat}\right), n, P\right) = 2^{r} \cdot \operatorname{W}\left(2 \cdot r, n\right)\right)$$

*Formalization.* `D5/S3/ArithSums/BrentEvenMomentPolynomial.claim` (`✓ std3`).

*Citation.* Richard P. Brent, Hideyuki Ohtsuka, Judy-anne H. Osborn, Helmut Prodinger (2016). *Some Binomial Sums Involving Absolute Values*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex>.

*Commentary.*

The normalization has been cleared by multiplication by 2^(4*n). Evaluation uses the coefficient homomorphism Int.castRingHom Rat and the rational image of n. This is an assertion about ordinary integer coefficients, not only integral values at natural arguments.

**Theorem 1.4 (The integral polynomial exists).**

$$\forall r \in \mathrm{Nat},\; \exists P \in \operatorname{Polynomial}\left(\mathrm{Int}\right),\; \forall n \in \mathrm{Nat},\; 2^{4 \cdot n} \cdot \left(\operatorname{Polynomial}.\operatorname{eval}_{2}\right)\left(\operatorname{Int}.\operatorname{castRingHom}\left(\mathrm{Rat}\right), n, P\right) = 2^{r} \cdot \operatorname{W}\left(2 \cdot r, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/BrentEvenMomentPolynomial.result` (`✓ std3`). ∎

*Resolves.* `Problems/brent-ohtsuka-osborn-prodinger-even-moment-integrality` (proved) by `D5/S3/ArithSums/BrentEvenMomentPolynomial.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"brent-ohtsuka-osborn-prodinger-even-moment-integrality","declaration_gid":"D5/S3/ArithSums/BrentEvenMomentPolynomial.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Richard P. Brent, Hideyuki Ohtsuka, Judy-anne H. Osborn, Helmut Prodinger (2016). *Some Binomial Sums Involving Absolute Values*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex>.

*Commentary.*

For N=2*n, pair two sign sequences. Their exact binomial multiplicities give the original sum. The coordinates U=(epsilon+eta)/2 and V=(epsilon-eta)/2 take the four values (1,0), (-1,0), (0,1), (0,-1), with equal weight. Their coordinate sums multiply to I^2-J^2. Expand the 2*r factors of each color and group their step labels by the equality partition. A mixed block or an odd block contributes zero. Each nonempty pure even block contributes 1/2. A partition with m blocks has m<=2*r and (2*n).descFactorial(m) injective label assignments. Let K_0=1. In K_(m+1), multiply K_m by X-m/2 when m is even, and by 2*X-m when m is odd; the first quotient m/2 is a natural number. Then 2^ceil(m/2)*K_m(X)=(2*X)_m. The integer polynomial H_(r,m)=2^(r-floor(m/2))*K_m therefore satisfies 2^m*H_(r,m)(n)=2^r*(2*n).descFactorial(m). Sum H_(r,m) over the pure even two-color partitions. All coefficients are integers, and the finite expansion gives the displayed identity for every n. Empty products and empty assignments include r=0 and n=0.

## References

- Truth anchor: `D5/S3/ArithSums/BrentEvenMomentPolynomial.W`
- Truth anchor: `D5/S3/ArithSums/BrentEvenMomentPolynomial.binomial`
- Truth anchor: `D5/S3/ArithSums/BrentEvenMomentPolynomial.claim`
- Truth anchor: `D5/S3/ArithSums/BrentEvenMomentPolynomial.result`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion](../Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.md)
