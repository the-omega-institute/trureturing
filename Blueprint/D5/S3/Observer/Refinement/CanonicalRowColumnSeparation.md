# Canonical Row-Column Separation

## Abstract

The canonical row-column behavioral quotient separates both axes.

**Theorem 1.1 (The behavioral double quotient separates rows and columns).**

$$\begin{gathered}\forall X, P, \Lambda: \operatorname{Type},\\{}e: X \to P \to \Lambda,\\{}\operatorname{let} r: X \to P \to \Lambda : = \lambda x p, e(x, p),\\{}c: P \to X \to \Lambda : = \lambda p x, e(x, p),\\{}\overline{X} : = \operatorname{Quotient}(\operatorname{ker}(r)), \overline{P} : = \operatorname{Quotient}(\operatorname{ker}(c)),\\{}\overline{e}: \overline{X} \to \overline{P} \to \Lambda : = \operatorname{QuotientLift2}(e, \operatorname{ker}(r), \operatorname{ker}(c)) \operatorname{in}\\{}(\forall a, b: \overline{X}, (\forall q: \overline{P}, \overline{e}(a, q) = \overline{e}(b, q)) \Rightarrow a = b) \land\\{}(\forall a, b: \overline{P}, (\forall q: \overline{X}, \overline{e}(q, a) = \overline{e}(q, b)) \Rightarrow a = b).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/CanonicalRowColumnSeparation.canonical_row_column_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state row and protocol column are constructed directly from the evaluation channel e. Their equality kernels define the two canonical quotient carriers.

The displayed descended evaluation is the canonical two-variable quotient lift of e. Equality on all quotient protocols forces equal state rows, hence equal state classes; the protocol proof is the symmetric argument.

No representative selector or choice of quotient section is used.

## References

- Truth anchor: `D5/S3/Observer/Refinement/CanonicalRowColumnSeparation.canonical_row_column_separation`
