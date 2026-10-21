# Actual three-node FiniteAlgebra

## Abstract

Actual three-node FiniteAlgebra

Write g=pi/4, mu=mean(c), a=arithmeticBoundarySymbol(c,n), r=n/N and h=g^2+mu. U,T,C,O are the exact physical finite-form coefficients; this module first states their polynomial identities for arbitrary real g,mu,a,r.

The even block has diagonal U/3,C/6 and off-diagonal T/sqrt(18). Its trace is 6h+4gar+4(a^2-h)r^2/3+2hr^4/5. Its determinant is the displayed exact polynomial of degrees two through six, with no root-distinctness assumption.

At a=0 the determinant is exactly 32h^2 r^4/45 and the trace is 6h-4hr^2/3+2hr^4/5. The different vanishing order is retained in the exceptional spectral branch.

**Definition 1.1 (U).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.U`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def U (g mu a r : ℝ) : ℝ :=   18 * (g ^ 2 + mu) + 12 * g * a * r +     (8 * a ^ 2 / 3 - 4 * (g ^ 2 + mu)) * r ^ 2 -     2 * g * a * r ^ 3 + 2 * (g ^ 2 + mu) * r ^ 4 / 5

**Definition 1.2 (T).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.T`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def T (g mu a r : ℝ) : ℝ :=   6 * g * a * r + (8 * a ^ 2 / 3 + 4 * (g ^ 2 + mu)) * r ^ 2 +     g * a * r ^ 3 - 4 * (g ^ 2 + mu) * r ^ 4 / 5

**Definition 1.3 (C).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.C`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def C (g mu a r : ℝ) : ℝ :=   8 * a ^ 2 * r ^ 2 / 3 + 4 * g * a * r ^ 3 +     8 * (g ^ 2 + mu) * r ^ 4 / 5

**Definition 1.4 (O).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.O`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.O` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def O (g mu a r : ℝ) : ℝ :=   4 * a ^ 2 + 4 * g * a * r + 4 * (g ^ 2 + mu) * r ^ 2 / 3

**Definition 1.5 (evenDet).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.evenDet`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.evenDet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def evenDet (g mu a r : ℝ) : ℝ :=   U g mu a r / 3 * (C g mu a r / 6) -     (T g mu a r / Real.sqrt 18) ^ 2

**Theorem 1.6 (finite trace identity).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.finite_trace_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.finite_trace_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finite_trace_identity (g mu a r : ℝ) :     U g mu a r / 3 + C g mu a r / 6 =       6 * (g ^ 2 + mu) + 4 * g * a * r +         4 / 3 * (a ^ 2 - (g ^ 2 + mu)) * r ^ 2 +         2 * (g ^ 2 + mu) * r ^ 4 / 5

**Theorem 1.7 (finite determinant identity).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.finite_determinant_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.finite_determinant_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finite_determinant_identity (g mu a r : ℝ) :     evenDet g mu a r =       (2 * a ^ 2 * (g ^ 2 + 4 * mu) / 3) * r ^ 2 +       (4 * g * a * (g ^ 2 + mu) / 3) * r ^ 3 +       (2 * a ^ 2 * g ^ 2 - 16 * a ^ 2 * (g ^ 2 + mu) / 9 +         32 * (g ^ 2 + mu) ^ 2 / 45) * r ^ 4 +       (4 * g * a * (g ^ 2 + mu) / 15) * r ^ 5 +       (a ^ 2 * (g ^ 2 + 16 * mu) / 30) * r ^ 6

**Theorem 1.8 (exceptional trace identity).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.exceptional_trace_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.exceptional_trace_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma exceptional_trace_identity (g mu r : ℝ) :     U g mu 0 r / 3 + C g mu 0 r / 6 =       6 * (g ^ 2 + mu) - 4 * (g ^ 2 + mu) * r ^ 2 / 3 +         2 * (g ^ 2 + mu) * r ^ 4 / 5

**Theorem 1.9 (exceptional determinant identity).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.exceptional_determinant_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.exceptional_determinant_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma exceptional_determinant_identity (g mu r : ℝ) :     evenDet g mu 0 r = 32 * (g ^ 2 + mu) ^ 2 * r ^ 4 / 45

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.C`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.O`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.T`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.U`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.evenDet`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.exceptional_determinant_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.exceptional_trace_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.finite_determinant_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.finite_trace_identity`
