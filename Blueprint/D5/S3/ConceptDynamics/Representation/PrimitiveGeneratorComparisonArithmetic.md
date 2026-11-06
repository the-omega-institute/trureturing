# Primitive-generator comparison arithmetic

## Abstract

The rational arithmetic core of the primitive-generator versus double-anchor count comparison.

**Theorem 1.1 (The explicit comparison count is strictly reduced).**

$$
\begin{aligned}
&\forall n,m,d\in\mathbb Q,\quad 4\le n\le m\le n+2,\quad
  \frac{n(n+1)}2\le d\\
&\qquad\Longrightarrow
\left(\left(n-2\right)d-\frac{n(n+1)}2\le N_{\rm gen}-N_{\rm pair}\right)
\land\\
\left(\frac{n(n+1)(n-3)}2\le N_{\rm gen}-N_{\rm pair}\right)
\land\left(0<N_{\rm gen}-N_{\rm pair}\right),\\
&\qquad N_{\rm gen}=md-\frac{m(m+1)}2,\quad N_{\rm pair}=2d.
\end{aligned}
$$

*Formalization.* `D5/S3/ConceptDynamics/Representation/PrimitiveGeneratorComparisonArithmetic.explicit_comparison_strict_reduction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proof factors the change in the generator count from the endpoint n as
`(m-n)(d-(m+n+1)/2)`, which is nonnegative under the prefix and dimension bounds. The
second lower bound follows from `d ≥ n(n+1)/2` and `n ≥ 4`. The theorem is a rationalized
arithmetic core: it does not formalize the Euclidean Jordan algebra claim that primitive
generators must span the selected block.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Representation/PrimitiveGeneratorComparisonArithmetic.explicit_comparison_strict_reduction`
