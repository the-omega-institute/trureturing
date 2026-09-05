# Closed Canonical `ZeroData` Nonvacuity Chain

## Abstract

This node assembles the complete logical chain downstream of a canonical Riemann--von Mangoldt source:

\[
\operatorname{RvM}(\mathcal Z_\zeta)
\Longrightarrow
N(T,2T)\to\infty
\Longrightarrow
|\mathcal Z_\zeta|=\infty
\Longrightarrow
\operatorname{Nonempty}(\operatorname{ZeroData})
\Longrightarrow
\text{a faithful exhaustive zero-data certificate}.
\]

## Certificate

`CanonicalZeroDataCertificate` exposes the consumer-facing obligations explicitly:

- an actual `ZeroData` value;
- every entry is a genuine nontrivial zeta zero;
- every nontrivial zeta zero has a unique index;
- analytic multiplicities are positive;
- reflection and conjugation preserve points and multiplicities;
- every symmetric spectral cutoff is finite.

The certificate is built directly from `CanonicalZeroDataProvider.canonicalZeroData` and reuses the existing `ZeroData` fields and `ZeroData.existsUnique_zero` theorem.

## Exact representation theorem

For the certified enumeration `C.data`,

\[
\operatorname{IsNontrivialZero}(\rho)
\iff
\exists!n\in\mathbb N,\;C.data.zero(n)=\rho.
\]

Hence the certificate represents exactly the intended zero set. It neither omits an actual nontrivial zero nor introduces a spurious point.

## Semantic realization theorem

For every predicate `P : ZeroData → Prop`,

\[
\operatorname{RvM}(\mathcal Z_\zeta)
\land
\bigl(\forall Z:\operatorname{ZeroData},\;P(Z)\bigr)
\Longrightarrow
\exists C:\operatorname{CanonicalZeroDataCertificate},\;P(C.data).
\]

The same conclusion carries a concrete represented nontrivial zero. Therefore a universal `ZeroData` theorem can be instantiated on an actual faithful zeta-zero enumeration.

## Boundary

The finite and logical parts of the chain are closed. The present source object still carries `RiemannVonMangoldt zetaZeroConfig` explicitly. Making the final provider hypothesis-free requires the repository's global Riemann--von Mangoldt assembly. No RH premise or RH conclusion appears in this node.
