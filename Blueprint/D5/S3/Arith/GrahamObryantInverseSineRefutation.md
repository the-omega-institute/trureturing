# Graham-O'Bryant Conjecture 5.2: a signed-dyadic counterfamily

## Abstract

Graham and O'Bryant's inverse-sine conditions admit noncanonical positive residue sets.

Fin(n) is the finite index type with natural values 0 through n-1. All n and q are natural numbers; p maps Fin(n) to natural representatives. real denotes the coercion to the real numbers, zmod(q,a) the natural cast to ZMod(q), and val the least nonnegative representative. Inverse and multiplication inside val are operations in ZMod(q), even for composite q. The notation sumFin(i,n,f(i)) sums over every i in Fin(n); imageFin denotes the ordinary finite image in the stated codomain. Fin(n) to N is a function type, and injective(p) asserts pairwise distinct natural representatives.

**Definition 1.1 (The complete inverse-sine row).**

$$\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; \forall k \in \operatorname{Fin}\left(n\right),\; \operatorname{row}\left(q, p, k\right) = \sum_{i \in \operatorname{Fin}\left(n\right)} \frac{1}{\operatorname{abs}\left(\operatorname{sin}\left(\frac{\pi \cdot \operatorname{real}\left(\operatorname{val}\left(\operatorname{zmod}\left(q, p\left(k\right)\right) \cdot \operatorname{inv}\left(\operatorname{zmod}\left(q, p\left(i\right)\right)\right)\right)\right)}{\operatorname{real}\left(q\right)}\right)\right)}$$

*Formalization.* `D5/S3/Arith/GrahamObryantInverseSineRefutation.row` (`✓ std3`).

*Citation.* Ron Graham; Kevin O'Bryant (2005). *A discrete Fourier kernel and Fraenkel's tiling conjecture*. DOI: [10.4064/aa118-3-4](https://doi.org/10.4064/aa118-3-4). URL: <https://mathweb.ucsd.edu/~ronspubs/05_02_fraenkel_tiling.pdf>.

*Commentary.*

The row includes i=k. For q>0 and any integers b(i) satisfying p(i)b(i)=1 modulo q, it also equals the sum of 1/abs(sin(pi*real(p(k))*real(b(i))/real(q))). Integer representatives differ by multiples of q; sine then changes by a sign, which disappears under absolute value. Thus reducing the product before taking sine preserves the author's modular-inverse convention.

**Definition 1.2 (The full source assertion).**

$$claim \Leftrightarrow \left(\forall n \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(n\right) \to \mathbb{N},\; (0 < n) \Rightarrow \left((0 < q) \Rightarrow \left((\forall i \in \operatorname{Fin}\left(n\right),\; 0 < p\left(i\right)) \Rightarrow \left((\operatorname{injective}\left(p\right)) \Rightarrow \left((\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{Coprime}\left(p\left(i\right), q\right)) \Rightarrow \left((\frac{\operatorname{real}\left(7\right)}{\operatorname{real}\left(4\right)}^{n} < \operatorname{real}\left(q\right)) \Rightarrow \left((\sum_{i \in \operatorname{Fin}\left(n\right)} p\left(i\right) \le q) \Rightarrow \left((\forall k \in \operatorname{Fin}\left(n\right),\; \frac{\operatorname{real}\left(2\right)}{\operatorname{sin}\left(\frac{\pi}{\operatorname{real}\left(q\right)}\right)} \le \operatorname{row}\left(q, p, k\right)) \Rightarrow ((q = 2^{n} - 1) \land (\{\operatorname{zmod}\left(q, p\left(i\right)\right) \mid i \in \operatorname{Fin}\left(n\right)\} = \{\operatorname{zmod}\left(q, 2\right)^{\operatorname{val}\left(i\right)} \mid i \in \operatorname{Fin}\left(n\right)\}))\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GrahamObryantInverseSineRefutation.claim` (`✓ std3`).

*Citation.* Ron Graham; Kevin O'Bryant (2005). *A discrete Fourier kernel and Fraenkel's tiling conjecture*. DOI: [10.4064/aa118-3-4](https://doi.org/10.4064/aa118-3-4). URL: <https://mathweb.ucsd.edu/~ronspubs/05_02_fraenkel_tiling.pdf>.

*Commentary.*

Conjecture 5.2, printed page 302, quantifies every positive n and q and every list of n distinct positive representatives coprime to q. It assumes the strict real inequality (7/4)^n<q, the natural sum bound sum p(i)<=q, and the lower row bound for every k. The rational 7/4 is evaluated in R. Both conclusions are required: q=2^n-1 and equality of the ordinary residue set with all n powers 2^0,...,2^(n-1). No prime-modulus, field, omitted diagonal, or independent-sign convention occurs in this assertion.

**Theorem 1.3 (A noncanonical family and the refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GrahamObryantInverseSineRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/graham-obryant-inverse-sine-conjecture52-refutation` (refuted) by `D5/S3/Arith/GrahamObryantInverseSineRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"graham-obryant-inverse-sine-conjecture52-refutation","declaration_gid":"D5/S3/Arith/GrahamObryantInverseSineRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ron Graham; Kevin O'Bryant (2005). *A discrete Fourier kernel and Fraenkel's tiling conjecture*. DOI: [10.4064/aa118-3-4](https://doi.org/10.4064/aa118-3-4). URL: <https://mathweb.ucsd.edu/~ronspubs/05_02_fraenkel_tiling.pdf>.

*Commentary.*

For every natural n>=3, set q=2^n-1 and p(i)=2^i except at i=n-1, where p(i)=2^(n-1)-1. These n entries are positive, strictly below q, distinct and coprime to q. Their finite image has cardinality n and their sum is q-1. Induction from n=3 gives (7/4)^n<q. The last entry is congruent to -2^(n-1); explicit signed powers give all modular inverses without a primality assumption. Absolute sine removes those signs, and i maps to k-i in Fin(n) permutes each complete row, including its diagonal. With x=pi/q, all sin(2^j*x), 0<=j<n, are positive, while sin(2^n*x)=-sin(x). The cotangent identity 1/sin(2t)=cot(t)-cot(2t) telescopes to zero over the shifted dyadic orbit. Removing its final negative term and restoring its first term gives every row exactly 2/sin(x). Every denominator is nonzero. The last positive entry is neither 2^(n-1) nor any smaller power, so the ordinary residue sets differ. This complete universal construction precedes use of the conjecture. Specializing it to n=3 gives q=7 and {1,2,3}, whose residue set differs from {1,2,4}; applying claim would equate those sets. The resulting contradiction is Not claim.

## References

- Truth anchor: `D5/S3/Arith/GrahamObryantInverseSineRefutation.claim`
- Truth anchor: `D5/S3/Arith/GrahamObryantInverseSineRefutation.result`
- Truth anchor: `D5/S3/Arith/GrahamObryantInverseSineRefutation.row`
