# A closed form for the generalized Stirling numbers of boson ordering

## Abstract

The generalized Stirling numbers with parameters (-1, 2; r), which govern boson operator orderings, have the closed form conjectured by Maier for every integer r, once the first binomial coefficient is read as the generalized binomial coefficient.

**Definition 1.1 (The numbers S-hat).**

$$\operatorname{stirlingHat}\left(n, k, r\right) = \sum_{x \in \operatorname{range}\left(k + 1\right)} (-1)^{k - x} \cdot \operatorname{choose}\left(k, x\right) \cdot \operatorname{rising}\left(2 \cdot x + r, n\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.stirlingHat` (`✓ std3`).

*Citation.* Robert S. Maier (2024). *Boson Operator Ordering Identities from Generalized Stirling and Eulerian Numbers*. DOI: [10.48550/arXiv.2308.10332](https://doi.org/10.48550/arXiv.2308.10332). URL: <https://arxiv.org/abs/2308.10332v4>.

*Commentary.*

Theorem 4.1 of the source: for alpha = -1 and beta = 2 the number S-hat(n, k; r) is the k-th forward difference at x = 0 of the rising factorial (2x + r)(2x + r + 1) ... (2x + r + n - 1).

**Definition 1.2 (The conjectured sum).**

$$\operatorname{conjectureSum}\left(n, k, r\right) = \sum_{j \in \operatorname{Icc}\left(\left\lfloor\frac{2 - r}{2}\right\rfloor, \left\lfloor\frac{n + 2 - r}{2}\right\rfloor\right)} \operatorname{Ring.choose}\left(n - j, n - k\right) \cdot \operatorname{factorial}\left(n\right) \cdot \operatorname{choose}\left(n + 1, 2 \cdot j + r - 1\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.conjectureSum` (`✓ std3`).

*Citation.* Robert S. Maier (2024). *Boson Operator Ordering Identities from Generalized Stirling and Eulerian Numbers*. DOI: [10.48550/arXiv.2308.10332](https://doi.org/10.48550/arXiv.2308.10332). URL: <https://arxiv.org/abs/2308.10332v4>.

*Commentary.*

The sum over integers j from floor((2 - r)/2) to floor((n + 2 - r)/2) of the generalized binomial coefficient C(n - j, n - k), times n! and the ordinary binomial coefficient C(n + 1, 2j + r - 1), whose lower index lies between 0 and n + 1 in this range.

**Definition 1.3 (The conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (k \le n) \Rightarrow (\forall r \in \mathbb{Z},\; \operatorname{stirlingHat}\left(n, k, r\right) = \operatorname{conjectureSum}\left(n, k, r\right)))$$

*Formalization.* `D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.claim` (`✓ std3`).

*Citation.* Robert S. Maier (2024). *Boson Operator Ordering Identities from Generalized Stirling and Eulerian Numbers*. DOI: [10.48550/arXiv.2308.10332](https://doi.org/10.48550/arXiv.2308.10332). URL: <https://arxiv.org/abs/2308.10332v4>.

*Commentary.*

Conjecture 5.3 of the source, for all n, all k <= n and all integers r. The source notes that the upper argument n - j may be negative; with the convention that a binomial coefficient with negative upper argument vanishes, the identity fails already at n = 1, k = 1, r = -1.

**Theorem 1.4 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.result` (`✓ std3`). ∎

*Resolves.* `Problems/maier-2024-boson-ordering-stirling-closed-form` (proved) by `D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"maier-2024-boson-ordering-stirling-closed-form","declaration_gid":"D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert S. Maier (2024). *Boson Operator Ordering Identities from Generalized Stirling and Eulerian Numbers*. DOI: [10.48550/arXiv.2308.10332](https://doi.org/10.48550/arXiv.2308.10332). URL: <https://arxiv.org/abs/2308.10332v4>.

*Commentary.*

Extend the sum to all integers j; the terms outside the range vanish. Both sides f(n, k, r) satisfy f(n, k + 1, r) = f(n, k, r + 2) - f(n, k, r) for k < n: on the left because forward differences commute with the shift x -> x + 1, which sends r to r + 2; on the right by shifting j and Pascal's rule for the generalized binomial coefficient. At k = 0 the left side is the rising factorial of r, and both sides satisfy f(n + 1, 0, r) - f(n + 1, 0, r - 1) = (n + 1) f(n, 0, r): on the left because the rising factorials of r and r - 1 share n factors, on the right by Pascal's rule applied twice and a shift of j. Both sides equal (n + 1)! at r = 1, so induction on n and then on the integer r settles k = 0, and induction on k settles every k <= n.

## References

- Truth anchor: `D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.claim`
- Truth anchor: `D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.conjectureSum`
- Truth anchor: `D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.result`
- Truth anchor: `D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.stirlingHat`
