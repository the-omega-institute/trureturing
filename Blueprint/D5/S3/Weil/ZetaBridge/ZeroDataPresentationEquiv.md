# Canonical equivalence of `ZeroData` presentations

## Scope

Every `ZeroData` value is a duplicate-free exhaustive natural-number presentation of the same set of nontrivial zeta zeros. This node exposes the unique zero-preserving reindexing

\[
e_{Z,Z'}:\mathbb N\simeq\mathbb N
\]

and proves that it transports analytic multiplicity, functional-equation reflection, complex conjugation, and their same-height mirror composite.

## Main result

If `e : ℕ ≃ ℕ` satisfies

\[
Z'.\operatorname{zero}(e(n))=Z.\operatorname{zero}(n)
\quad\text{for every }n,
\]

then

\[
e=e_{Z,Z'}.
\]

The canonical equivalences are identity on one presentation, reverse by taking inverses, and compose functorially.

## Mirror transport

The same-height mirror is

\[
M_Z=C_Z\circ R_Z,
\]

so that

\[
Z.\operatorname{zero}(M_Zn)=1-\overline{Z.\operatorname{zero}(n)}.
\]

It is involutive, preserves multiplicity, and is fixed exactly at the critical line. Presentation transport is equivariant:

\[
e_{Z,Z'}(M_Zn)=M_{Z'}(e_{Z,Z'}n).
\]

## Boundary

The natural-number order remains choice-dependent. Canonicality means uniqueness among zero-preserving reindexings. No height ordering or computable enumeration is asserted.

## Truth anchors

- `zeroDataPresentationEquiv_unique`
- `zeroDataPresentationEquiv_reflection`
- `zeroDataPresentationEquiv_conjugation`
- `zeroDataPresentationEquiv_mirror`
- `zeroDataPresentationEquiv_trans`
