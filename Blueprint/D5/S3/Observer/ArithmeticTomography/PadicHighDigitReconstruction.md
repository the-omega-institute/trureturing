# Reconstruction from a Timed High Digit

## Abstract

The first high-digit change reconstructs a p-adic residue.

Fix any prime p and natural k, including zero, and put P = p^k. The state space is the full ring of p-adic integers. Write q for PadicInt.toZModPow at depth k+1 and z(x) for its canonical natural representative. All readings come from the single orbit x+n. An index n in Fin(P) ranges from zero through P-1.

**Definition 1.1 (The digit at depth k).**

$$\forall x \in \mathbb{Z}_p, \operatorname{d}\left(x\right) = \left\lfloor\frac{\operatorname{z}\left(x\right)}{P}\right\rfloor.$$

*Formalization.* `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.highDigit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the quotient by P is read; the lower remainder is not observed.

**Definition 1.2 (The fixed consecutive reading protocol).**

$$\forall x \in \mathbb{Z}_p, \forall n \in \operatorname{Fin}\left(P\right), \operatorname{W}\left(x, n\right) = \operatorname{d}\left(x + n\right).$$

*Formalization.* `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word contains exactly P readings and uses P-1 adding-one steps.

For any positive natural P and any word w : Fin(P) to the naturals, let S(w) be the set of natural index values n less than P with w(n) different from w(0). The following two definitions apply to every such finite word, whether or not it is produced by a p-adic orbit.

**Definition 1.3 (First change with a no-change sentinel).**

$$\forall P \in \mathbb{N}, 0 < P \Rightarrow \forall w: \operatorname{Fin}\left(P\right) \to \mathbb{N}, \operatorname{t}\left(w\right) = \operatorname{min}\left(\operatorname{S}\left(w\right) \cup \{P\}\right).$$

*Formalization.* `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.firstChange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite minimum is used when S(w) is nonempty; otherwise the value is P. Adjoining P to S(w) expresses the same convention.

**Definition 1.4 (A decoder using the first digit and the first change).**

$$\forall P \in \mathbb{N}, 0 < P \Rightarrow \forall w: \operatorname{Fin}\left(P\right) \to \mathbb{N}, \operatorname{D}\left(w\right) = \operatorname{w}\left(0\right) \cdot P + (P - \operatorname{t}\left(w\right)).$$

*Formalization.* `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first digit selects the block. Subtracting the change time from P recovers the position inside that block.

In the theorem, P means p^k for the quantified p and k. For each x, write b for z(x) divided by P and r for z(x) modulo P. All quotients inside floors are natural quotients, and mod denotes the nonnegative natural remainder.

**Theorem 1.5 (Exact reconstruction and equality of observation fibers).**

$$\begin{aligned}\forall p,k \in \mathbb{N}, \operatorname{Prime}\left(p\right) \Rightarrow\\(\forall x \in \mathbb{Z}_p, \\b < p \land r < P \land\\\operatorname{z}\left(x\right) = b \cdot P + r \land\\\operatorname{W}\left(x, 0\right) = b \land\\(\forall n \in \operatorname{Fin}\left(P\right), \operatorname{W}\left(x, n\right) = \operatorname{mod}\left(b + \left\lfloor\frac{r + n}{P}\right\rfloor, p\right) \land \left\lfloor\frac{r + n}{P}\right\rfloor \leq 1) \land\\(\forall n \in \operatorname{Fin}\left(P\right), (\operatorname{W}\left(x, n\right) \neq b \iff P - r \leq n \land r \neq 0)) \land\\\operatorname{t}\left(\operatorname{W}\left(x\right)\right) = P - r \land\\(\operatorname{t}\left(\operatorname{W}\left(x\right)\right) = P \iff r = 0) \land\\\operatorname{D}\left(\operatorname{W}\left(x\right)\right) = \operatorname{z}\left(x\right)) \land\\(\forall x,y \in \mathbb{Z}_p, (\operatorname{W}\left(x\right) = \operatorname{W}\left(y\right) \iff \operatorname{q}\left(x\right) = \operatorname{q}\left(y\right))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the window n < P, the lower remainder r+n carries at most once. If r is positive, the first carry occurs at P-r, which lies between 1 and P-1. The digit b differs from (b+1) mod p because p is at least two, including the wrap from p-1 to zero. Thus the change indices have exactly the lower endpoint P-r. A constant word has r equal to zero.

The decoder identity implies that equal words have equal residues. Conversely, the projection is a ring homomorphism, so equal residues give equal digits after each natural translation. At k = 0, P = 1, r = 0, and the single digit already is the representative modulo p.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.decode`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.firstChange`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.highDigit`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.result`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PadicHighDigitReconstruction.word`
