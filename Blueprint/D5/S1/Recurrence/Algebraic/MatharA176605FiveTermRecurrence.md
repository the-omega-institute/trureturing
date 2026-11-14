# Mathar's A176605 five-term identity

## Abstract

The original A176605 nonlinear convolution satisfies Mathar's five-term identity at every legal backshift index.

**Definition 1.1 (An actual source sequence).**

$$\operatorname{source}\left(0\right) = 1 \land \left(\operatorname{source}\left(1\right) = 1 \land \left(\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \operatorname{source}\left(m + 1\right) = \sum_{p\in\operatorname{range}\left(m + 1\right)}\operatorname{source}\left(p\right) \cdot \operatorname{source}\left(m - p\right) + 1\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence.source` (`✓ std3`).

*Citation.* Richard Choulet; R. J. Mathar; Michael Somos; OEIS Foundation Inc. (2016). *OEIS A176605 — Mathar five-term identity for a nonlinear convolution sequence*. URL: <https://oeis.org/A176605>.

*Commentary.*

The natural-valued sequence is constructed by well-founded recursion: source(0)=source(1)=1, and the displayed convolution defines source(m+1) only for m ≥ 1. Each referenced index is strictly below m+1. The compiled Reg source_conditions proof verifies all these conditions, and changed_law uses this actual sequence to establish full-family variation. Thus the universal implication has an inhabited source domain. No recurrence at m=0 is imposed.

**Definition 1.2 (The full source question).**

$$claim \Leftrightarrow \left(\forall a \in \mathbb{N} \to \mathbb{N},\; \left(\operatorname{a}\left(0\right) = 1 \land \left(\operatorname{a}\left(1\right) = 1 \land \left(\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \operatorname{a}\left(m + 1\right) = \sum_{p\in\operatorname{range}\left(m + 1\right)}\operatorname{a}\left(p\right) \cdot \operatorname{a}\left(m - p\right) + 1\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 4 \le n \Rightarrow ((n:\mathbb{Z}) + 1) \cdot (\operatorname{a}\left(n\right):\mathbb{Z}) + 2 \cdot (-3 \cdot (n:\mathbb{Z}) + 1) \cdot (\operatorname{a}\left(n - 1\right):\mathbb{Z}) + (9 \cdot (n:\mathbb{Z}) - 13) \cdot (\operatorname{a}\left(n - 2\right):\mathbb{Z}) + 8 \cdot (-(n:\mathbb{Z}) + 3) \cdot (\operatorname{a}\left(n - 3\right):\mathbb{Z}) + 4 \cdot ((n:\mathbb{Z}) - 4) \cdot (\operatorname{a}\left(n - 4\right):\mathbb{Z}) = 0\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence.claim` (`✓ std3`).

*Citation.* Richard Choulet; R. J. Mathar; Michael Somos; OEIS Foundation Inc. (2016). *OEIS A176605 — Mathar five-term identity for a nonlinear convolution sequence*. URL: <https://oeis.org/A176605>.

*Commentary.*

OEIS A176605, revision 19, NAME specializes k=0 and l=1 in its nonlinear convolution. FORMULA attributes the five-term conjecture to R. J. Mathar. The source omits the linear onset. Here n ≥ 4 is the disclosed nonnegative-backshift interpretation, independent of OFFSET 0,3. Every lag index is natural; every signed coefficient and sequence value in the identity is evaluated in the integers after casting. All source sequences and all n ≥ 4 are included. The source's generating-function and finite-sum assertions are not hypotheses.

**Theorem 1.3 (The complete five-term identity).**

$$\forall a \in \mathbb{N} \to \mathbb{N},\; \left(\operatorname{a}\left(0\right) = 1 \land \left(\operatorname{a}\left(1\right) = 1 \land \left(\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \operatorname{a}\left(m + 1\right) = \sum_{p\in\operatorname{range}\left(m + 1\right)}\operatorname{a}\left(p\right) \cdot \operatorname{a}\left(m - p\right) + 1\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 4 \le n \Rightarrow ((n:\mathbb{Z}) + 1) \cdot (\operatorname{a}\left(n\right):\mathbb{Z}) + 2 \cdot (-3 \cdot (n:\mathbb{Z}) + 1) \cdot (\operatorname{a}\left(n - 1\right):\mathbb{Z}) + (9 \cdot (n:\mathbb{Z}) - 13) \cdot (\operatorname{a}\left(n - 2\right):\mathbb{Z}) + 8 \cdot (-(n:\mathbb{Z}) + 3) \cdot (\operatorname{a}\left(n - 3\right):\mathbb{Z}) + 4 \cdot ((n:\mathbb{Z}) - 4) \cdot (\operatorname{a}\left(n - 4\right):\mathbb{Z}) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Choulet; R. J. Mathar; Michael Somos; OEIS Foundation Inc. (2016). *OEIS A176605 — Mathar five-term identity for a nonlinear convolution sequence*. URL: <https://oeis.org/A176605>.

*Commentary.*

For A=Σ a(n)X^n in Q[[X]], coefficient extensionality and the original convolution prove F=X(1-X)A²-(1-X)A+1-X+X²=0, with the first two coefficients treated separately. Differentiate F and multiply by X. Polynomial elimination then gives P(XA')+QA=R, where P=1-6X+9X²-8X³+4X⁴, Q=1-4X+5X² and R=1-2X+4X²-2X³. The eliminated factor 2XA-1 has constant coefficient -1 and is nonzero; the formal power-series ring is a domain. The frozen A308815DFiniteRecurrence.euler_coeff and four coefficient shifts give exactly the displayed relation because coeff(n,R)=0 for n ≥ 4. No analytic convergence, assumed generating function or finite-prefix replacement is used. The proof is classified bind-only under the external named-problem resolution basis of issue #30568. No worldwide openness, priority or sibling resolution is asserted.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence.source`
- Dependency: [D5/S1/Recurrence/A308815DFiniteRecurrence](../A308815DFiniteRecurrence.md)
