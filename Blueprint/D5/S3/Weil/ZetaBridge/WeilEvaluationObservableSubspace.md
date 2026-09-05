# Weil Evaluation Observable Subspace

## Abstract

Scalar even Weil tests do not reach the whole multiplicity-expanded finite zero-coordinate space. Their Fourier–Laplace evaluation repeats one scalar on every analytic-multiplicity copy of a zero and is invariant under functional-equation reflection of the spectral parameter.

This node formalizes both range constraints and gives explicit finite targets proving non-surjectivity when either obstruction is present.

## Definitions

For a finite symmetric spectral window, let

\[
I_T=\{n:n\in Z.\operatorname{symmetricIndices}(T)\}
\]

and let

\[
\widetilde I_T=\sum_{n\in I_T}\operatorname{Fin}(m_n)
\]

be the multiplicity-expanded coordinate type.

The distinct-zero and expanded evaluations are

\[
E_T(g)(n)=\widehat g(\gamma_n),
\qquad
\widetilde E_T(g)(n,k)=\widehat g(\gamma_n).
\]

The node also defines an explicit finite linear combination of bundled `WeilTestFunction` values and proves Fourier–Laplace linearity for that constructor.

## Main results

### Multiplicity-fiber constancy

For every test and every two copies of the same zero,

\[
\widetilde E_T(g)(n,k)=\widetilde E_T(g)(n,l).
\]

Hence no scalar Weil test separates two analytic-multiplicity copies.

### Reflection evenness

Because every bundled Weil test is even and

\[
\gamma_{R(n)}=-\gamma_n,
\]

we have

\[
E_T(g)(R(n))=E_T(g)(n).
\]

### Explicit rank obstructions

If some zero in the window has multiplicity at least two, then

\[
g\longmapsto\widetilde E_T(g)
\]

is not surjective onto the ambient expanded coordinate space.

If the finite window contains a moved functional-equation reflection pair, then

\[
g\longmapsto E_T(g)
\]

is not surjective onto all distinct-zero vectors.

Both proofs construct a concrete target vector violating the corresponding forced equality.

## Mathematical role

The correct comparison object for scalar even Weil tests is a reduced observable space. The full mirror-odd Hilbert sector remains a valid zero-side target geometry, but its multiplicity copies and reflection-antisymmetric directions are not independently reachable by this observer.

## Claim boundary

This node does not compute the exact range dimension for every window and does not introduce derivative jets or vector-valued tests. It proves the range constraints and strict non-surjectivity statements needed to prevent an invalid full-rank assumption.

## Truth anchors

- `finite_weil_evaluation_observable_subspace_spec`
- `finiteWeilCoordinateEvaluation_not_surjective_of_two_copies`
- `finiteWeilIndexEvaluation_not_surjective_of_reflection_pair`
- `fourierLaplace_finiteWeilLinearCombination`
