# Gallardo–Rahavandrainy's Binary-Polynomial Collatz Conjecture

## Abstract

The binary-polynomial Collatz length of (M²+M+1)ⁿ equals n+1 for n≥2.

All polynomials have coefficients in ZMod 2. Polynomial.X is the indeterminate, and the natural index k corresponds to the source index 2k+1. The operation divByMonic is polynomial division by a monic polynomial; rootMultiplicity records the multiplicity of a specified root. In characteristic two, X-C(1)=X+1. The least hitting index is taken with sInf on natural numbers; the proof establishes a hit for every polynomial used in the conclusion.

**Definition 1.1 (The first nonconstant odd polynomial).**

$$(M: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)) = (\operatorname{Polynomial}.\operatorname{X})^{2} + \operatorname{Polynomial}.\operatorname{X} + 1$$

*Formalization.* `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.M` (`✓ std3`).

*Citation.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

"The first odd polynomial after 1 is M := x² + x + 1." (p. 2.) The source also says that A is odd if gcd(A, x(x + 1)) = 1. This is Mathlib's IsCoprime A (X*(X+1)).

**Definition 1.2 (Removing the linear factors).**

$$\forall (S: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), \operatorname{oddPart}\left(S\right) = \operatorname{Polynomial}.\operatorname{divByMonic}\left(S, (\operatorname{Polynomial}.\operatorname{X})^{S.\operatorname{rootMultiplicity}\left(0\right)} \cdot (\operatorname{Polynomial}.\operatorname{X} - \operatorname{Polynomial}.\operatorname{C}\left(1\right))^{S.\operatorname{rootMultiplicity}\left(1\right)}\right)$$

*Formalization.* `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.oddPart` (`✓ std3`).

*Citation.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

"S = x^{val_x(S)}(x + 1)^{val_{x+1}(S)} S₁, where S₁ is odd." (p. 2.) The two valuations are rootMultiplicity at 0 and 1. The quotient by their product is S₁ for a nonzero S; the Lean definition is total at S=0 as well.

**Definition 1.3 (The odd Collatz sequence).**

$$\forall (A: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), (\operatorname{oddSeq}\left(A, 0\right) = \operatorname{oddPart}\left(A\right)) \land (\forall (k: \mathbb{N}), \operatorname{oddSeq}\left(A, k + 1\right) = \operatorname{oddPart}\left(1 + M \cdot \operatorname{oddSeq}\left(A, k\right)\right))$$

*Formalization.* `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.oddSeq` (`✓ std3`).

*Citation.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

"A₁ the odd polynomial such that A₀ = x^{a₀}(x + 1)^{b₀}A₁" and "A_{2k} = 1 + MA_{2k−1}", "A_{2k+1} = A_{2k}/(x^{a_{2k}}(x + 1)^{b_{2k}})." (p. 2.) Thus oddSeq A 0 is A₁, and oddSeq A k is A_{2k+1}.

**Definition 1.4 (Counting the odd terms).**

$$\forall (A: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), \operatorname{collatzLength}\left(A\right) = \operatorname{sInf}\left(\{(k: \mathbb{N}) | \operatorname{oddSeq}\left(A, k\right) = 1\}\right) + 1$$

*Formalization.* `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.collatzLength` (`✓ std3`).

*Citation.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

Theorem 1.2 gives "[A₀, …, A_{2m−2}, x² + x] and [A₁, …, A_{2m−1}, 1]" and "where m ∈ ℕ*, ℓ_A = m + 1 ≤ 2^{deg(A)−1}." (p. 3.) The length includes the initial odd term and the terminal 1. For n=9, the source's table has ten odd terms and length 10 (p. 15).

**Definition 1.5 (Conjecture 3.11).**

$$(claim) \iff (\forall (n: \mathbb{N}), (2 \le n) \implies (\operatorname{collatzLength}\left(((M)^{2} + M + 1)^{n}\right) = n + 1))$$

*Formalization.* `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.claim` (`✓ std3`).

*Citation.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

"If A = (M² + M + 1)ⁿ with n ≥ 2, then ℓ_A equals n + 1." (Conjecture 3.11, p. 15.) The exponent n is a natural number and collatzLength is the number of terms just defined.

**Theorem 1.6 (Evaluation one implies nonzero).**

$$\forall (f: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), (\operatorname{Polynomial}.\operatorname{eval}\left(0, f\right) = 1) \implies (f \ne 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.nonzero_of_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

A polynomial whose value at zero is one is nonzero.

**Theorem 1.7 (The unique nonzero binary coefficient).**

$$\forall (c: \operatorname{ZMod}\left(2\right)), (c \ne 0) \implies (c = 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.nonzero_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

Every nonzero element of ZMod 2 equals one.

**Theorem 1.8 (An odd constant polynomial).**

$$\forall (f: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), (\operatorname{Polynomial}.\operatorname{eval}\left(0, f\right) = 1) \implies ((\operatorname{Polynomial}.\operatorname{natDegree}\left(f\right) = 0) \implies (f = 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.eq_one_of_degree_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

A polynomial of natural degree zero whose value at zero is one equals one.

**Theorem 1.9 (Degree of the multiplier).**

$$\operatorname{Polynomial}.\operatorname{natDegree}\left(M\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.degree_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

The multiplier M has natural degree two.

**Theorem 1.10 (The multiplier is nonzero).**

$$M \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.q_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

The multiplier M is nonzero.

**Theorem 1.11 (The odd part of a factored polynomial).**

$$\forall (a: \mathbb{N}), \forall (b: \mathbb{N}), \forall (u: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), (\operatorname{Polynomial}.\operatorname{eval}\left(0, u\right) = 1) \implies ((\operatorname{Polynomial}.\operatorname{eval}\left(1, u\right) = 1) \implies (\operatorname{oddPart}\left((\operatorname{Polynomial}.\operatorname{X})^{a} \cdot (\operatorname{Polynomial}.\operatorname{X} - \operatorname{Polynomial}.\operatorname{C}\left(1\right))^{b} \cdot u\right) = u))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.oddPart_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

If u takes value one at both zero and one, removing powers of X and X-C(1) from their product with u leaves exactly u.

**Theorem 1.12 (Proof of Conjecture 3.11).**

$$\forall (n: \mathbb{N}), (2 \le n) \implies (\operatorname{collatzLength}\left(((M)^{2} + M + 1)^{n}\right) = n + 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.result` (`✓ std3`). ∎

*Resolves.* `Problems/gallardo-rahavandrainy-2023-binary-collatz-3-11` (proved) by `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gallardo-rahavandrainy-2023-binary-collatz-3-11","declaration_gid":"D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Luis H. Gallardo and Olivier Rahavandrainy (2023). *On Collatz Conjecture for binary polynomials*. DOI: [10.48550/arXiv.2308.01181](https://doi.org/10.48550/arXiv.2308.01181). URL: <https://arxiv.org/abs/2308.01181v2>.

*Commentary.*

Substitution of x(x+1) and polynomial reversal identify the odd sequence with the map f ↦ (1+X)f+X^(natDegree f+1). A degree-gap reduction proves termination and relates its first hitting times. For every f with f(0)=1, squaring doubles the hitting time, and multiplying its square by 1+X+X² adds one to twice that time. Strong induction on n, using its even and odd cases, gives hitting time n for (1+X+X²)ⁿ. Transport to the source sequence therefore gives length n+1. The same proof gives this length also for n=0 and n=1. No sharper general upper bound for other initial polynomials is asserted.

## References

- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.M`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.claim`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.collatzLength`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.degree_q`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.eq_one_of_degree_zero`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.nonzero_eq_one`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.nonzero_of_odd`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.oddPart`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.oddPart_factor`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.oddSeq`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.q_ne_zero`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.result`
