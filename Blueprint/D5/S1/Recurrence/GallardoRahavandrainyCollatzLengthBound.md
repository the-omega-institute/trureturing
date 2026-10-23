# A Quadratic Bound for Binary-Polynomial Collatz Length

## Abstract

Every nonzero binary polynomial has Collatz length at most two plus the floor of one quarter of its squared degree.

Polynomials have coefficients in ZMod 2. The operations M, oddPart and oddSeq are those of GallardoRahavandrainyBinaryCollatz: M=X²+X+1, oddPart removes the linear factors, and oddSeq A k is the source term A₂ₖ₊₁. Natural subtraction is truncated at zero, and Nat.div denotes integer floor division. The natural infimum sInf selects the least terminal-pair index; the proof constructs such an index.

**Definition 1.1 (The even-indexed terms).**

$$\forall (A: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), \forall (k: \mathbb{N}), \operatorname{evenTerm}\left(A, k\right) = \operatorname{ite}\left(k = 0, A, 1 + M \cdot \operatorname{oddSeq}\left(A, k - 1\right)\right)$$

*Formalization.* `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.evenTerm` (`✓ std3`).

*Citation.* Luis H. Gallardo and Olivier Rahavandrainy (2025). *A variant of Collatz's Conjecture over Binary Polynomials*. DOI: [10.48550/arXiv.2510.07530](https://doi.org/10.48550/arXiv.2510.07530). URL: <https://arxiv.org/abs/2510.07530v1>.

*Commentary.*

"A₀ = A" and "A₂ₖ = 1 + M₁A₂ₖ₋₁" (§1, p. 4). The natural index k selects A₂ₖ. The displayed ite has value A when k=0 and value 1+M*oddSeq A (k-1) otherwise.

**Definition 1.2 (The source length).**

$$\forall (A: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), \operatorname{rA}\left(A\right) = \operatorname{sInf}\left(\{(m: \mathbb{N}) | (1 \le m) \land (\forall (k: \mathbb{N}), (m \le k) \implies ((\operatorname{evenTerm}\left(A, k\right) = \operatorname{Polynomial}.\operatorname{X} \cdot (\operatorname{Polynomial}.\operatorname{X} + 1)) \land (\operatorname{oddSeq}\left(A, k\right) = 1)))\}\right) + 1$$

*Formalization.* `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.rA` (`✓ std3`).

*Citation.* Luis H. Gallardo and Olivier Rahavandrainy (2025). *A variant of Collatz's Conjecture over Binary Polynomials*. DOI: [10.48550/arXiv.2510.07530](https://doi.org/10.48550/arXiv.2510.07530). URL: <https://arxiv.org/abs/2510.07530v1>.

*Commentary.*

"Let A be a nonzero binary polynomial. Then the sequences of polynomials obtained from Collatz transformations are of finite length r_A." "where m ∈ ℕ* and r_A = m + 1 ≤ 2^{deg(A)−1}." (Theorem 1.2, p. 4.) Here m is the least positive index from which the even and odd terms are respectively X*(X+1) and 1. This counts the terminal pair after the first odd 1.

**Definition 1.3 (The polynomial-bound prediction).**

$$(claim) \iff (\exists (p: \operatorname{Polynomial}\left(\mathbb{N}\right)), \forall (A: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), (A \neq 0) \implies (\operatorname{rA}\left(A\right) \le \operatorname{Polynomial}.\operatorname{eval}\left(\operatorname{Polynomial}.\operatorname{natDegree}\left(A\right), p\right)))$$

*Formalization.* `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.claim` (`✓ std3`).

*Citation.* Luis H. Gallardo and Olivier Rahavandrainy (2025). *A variant of Collatz's Conjecture over Binary Polynomials*. DOI: [10.48550/arXiv.2510.07530](https://doi.org/10.48550/arXiv.2510.07530). URL: <https://arxiv.org/abs/2510.07530v1>.

*Commentary.*

"However, several computations suggest that here also r_A is bounded by a polynomial in deg(A) (see Section 3)." (§1, p. 5.) The polynomial p has natural coefficients, A ranges over all nonzero polynomials over ZMod 2, and natDegree equals the degree on that domain.

**Theorem 1.4 (The explicit quadratic estimate).**

$$\forall (A: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), (A \neq 0) \implies (\operatorname{rA}\left(A\right) \le 2 + \operatorname{Nat}.\operatorname{div}\left((\operatorname{Polynomial}.\operatorname{natDegree}\left(A\right))^{2}, 4\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.rA_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis H. Gallardo and Olivier Rahavandrainy (2025). *A variant of Collatz's Conjecture over Binary Polynomials*. DOI: [10.48550/arXiv.2510.07530](https://doi.org/10.48550/arXiv.2510.07530). URL: <https://arxiv.org/abs/2510.07530v1>.

*Commentary.*

For an odd polynomial F different from 1, set k to the smaller multiplicity of the roots 0 and 1 in F+1. Coprimality of X and X+1 gives k≤natDegree(F)/2. If a Collatz step preserves the degree, both removed multiplicities equal one, and the smaller multiplicity in F+1 decreases by one. Strong induction therefore forces a strict degree decrease within k steps. A second strong induction on degree, using the identity (n+1)/2+n²/4=(n+1)²/4 for natural division, bounds the time to reach 1. The terminal pair starts at the next index. This proves an upper bound on plateau duration; an exact duration and sharpness of the bound are separate questions.

**Theorem 1.5 (Proof of the polynomial-bound prediction).**

$$\exists (p: \operatorname{Polynomial}\left(\mathbb{N}\right)), \forall (A: \operatorname{Polynomial}\left(\operatorname{ZMod}\left(2\right)\right)), (A \neq 0) \implies (\operatorname{rA}\left(A\right) \le \operatorname{Polynomial}.\operatorname{eval}\left(\operatorname{Polynomial}.\operatorname{natDegree}\left(A\right), p\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis H. Gallardo and Olivier Rahavandrainy (2025). *A variant of Collatz's Conjecture over Binary Polynomials*. DOI: [10.48550/arXiv.2510.07530](https://doi.org/10.48550/arXiv.2510.07530). URL: <https://arxiv.org/abs/2510.07530v1>.

*Commentary.*

The quadratic estimate implies the prediction with the natural-coefficient polynomial X²+2, since floor(n²/4)≤n². The stronger explicit floor estimate is the preceding theorem.

## References

- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.claim`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.evenTerm`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.rA`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.rA_quadratic`
- Truth anchor: `D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.result`
- Dependency: [D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz](GallardoRahavandrainyBinaryCollatz.md)
