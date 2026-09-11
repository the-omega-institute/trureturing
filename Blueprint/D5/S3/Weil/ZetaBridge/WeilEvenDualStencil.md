# Even Arithmetic Dual Stencil

## Abstract

The actual even zero-trace Fourier stencil has an explicit arithmetic column and a complete inverse-square envelope for certified energy-dual trials.

**Theorem 1.1 (Reflection of the original arithmetic symbol).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.arithmetic_boundary_symbol_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.arithmetic_boundary_symbol_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual arithmeticBoundarySymbol is odd in its integer frequency. The proof unfolds the original finite prime, pole and infinite Gamma expression through a private definitional presentation. No zero data, symmetry premise or replacement public symbol is introduced.

**Theorem 1.2 (Central arithmetic symbol).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.arithmetic_boundary_symbol_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.arithmetic_boundary_symbol_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Oddness implies the existing symbol vanishes at zero. This companion is used when evaluating the central coefficient of the stencil.

**Definition 1.3 (Original column of the specified Fourier stencil).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.zeroTraceColumn`

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.zeroTraceColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the existing couplingColumn with support {n,-n,0}, coefficient -2 at zero and 1 at the two other frequencies. For n positive this represents V_n+V_(-n)-2V_0, with zero endpoint trace. The arithmetic action is specified before evaluating it.

**Theorem 1.4 (Exact arithmetic cancellation on the three-point stencil).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.zero_trace_column_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.zero_trace_column_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive integer n and exterior integer m with |m|>n, the canonical column equals 2n*(m*s_n-n*s_m)/(pi*m*(m^2-n^2)). The proof expands the original finite column, uses proved arithmetic oddness and checks all denominators before cancellation. Both signs of m remain covered.

**Theorem 1.5 (Actual inverse-square exterior estimate).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.zero_trace_column_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.zero_trace_column_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, n>0 and |m|>=2n, use the previously proved prime-pole-Gamma envelope B_c to obtain norm(column)<=4*B_c*n/(pi*|m|^2). The factorization of m^2-n^2 preserves cancellation and improves the generic separate-coefficient estimate. There is no terminal exterior cutoff or assumed moment condition.

**Theorem 1.6 (Finite complex trial with a complete arithmetic tail constant).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.finite_zero_trace_columns_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.finite_zero_trace_columns_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite positive-index set and complex stencil coefficients t_n, bound the actual summed exterior column by 4*B_c/(pi*|m|^2) times sum n*norm(t_n). The concrete consumer reconstructs two exact Gaussian-rational pivots, proves endpoint and candidate-pairing equalities by exact arithmetic, and encloses all retained and exterior residual modes before using the existing energy-dual variational theorem.

The physical Fourier/operator-domain identification, historical full-space coercivity, infinite fourth-power sum, complex-disk extension and interval verifier remain separately stated paper/computer-assisted bridges. No optimal trial or all-scale convergence is assumed. Lean elaboration, Scribe emission and a transitive axiom report have not been run.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.arithmetic_boundary_symbol_neg`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.arithmetic_boundary_symbol_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.finite_zero_trace_columns_bound`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.zeroTraceColumn`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.zero_trace_column_bound`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.zero_trace_column_formula`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet](WeilArithmeticCouplingJet.md)
