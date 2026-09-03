# Canonical `ZeroData` Provider

## Abstract

The canonical nontrivial-zeta-zero set is already owned at set level by `Zeta23.zetaZeroConfig`. A duplicate-free exhaustive natural-number enumeration is obtained by classical choice after Riemann--von Mangoldt growth proves that this set is infinite.

The chosen ordering is not intrinsic. Its permitted consumers are intrinsic because the repository has already proved that finite symmetric zero sums, symmetric convergence, and the resulting zero-sum value are invariant under replacement by any other exhaustive duplicate-free `ZeroData` enumeration.

## Source and provider

The analytic source is packaged as

\[
\operatorname{CanonicalZeroDataSource}
=
\bigl\{
\operatorname{RiemannVonMangoldt}(\operatorname{zetaZeroConfig})
\bigr\}.
\]

From it the node defines

\[
\operatorname{canonicalZeroData}(S)
:
\operatorname{ZeroData}
\]

and a provider carrying both the source and the selected value.

## Fidelity guarantees

For every source `S`, the node proves:

1. every enumerated point is a nontrivial zeta zero;
2. every nontrivial zeta zero occurs at exactly one natural-number index;
3. every stored analytic multiplicity is positive;
4. functional-equation reflection preserves the point and multiplicity;
5. complex conjugation preserves the point and multiplicity;
6. every symmetric spectral ball is finite.

## Enumeration-independent consumers

For every alternative `Z : ZeroData`, every Weil test `g`, and every cutoff `T`,

\[
\operatorname{truncatedZeroSum}
  (\operatorname{canonicalZeroData}(S),g,T)
=
\operatorname{truncatedZeroSum}(Z,g,T).
\]

Symmetric convergence is equivalent across the two enumerations, and convergent zero-sum values agree. Thus the word canonical refers to the represented zeta-zero object and all permutation-invariant observables. It does not assert a computable or uniquely ordered list of zeros.
