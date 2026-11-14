---
bibkey: clarissewocjan2005permutationcriteria
authors: Lieven Clarisse; Pawel Wocjan
year: 2006
title: "On independent permutation separability criteria"
doi: null
url: https://arxiv.org/abs/quant-ph/0504160v2
claim: "Definition 1 identifies two permutations when their rearranged operators have equal trace norm on every positive trace-one state. Theorem 3 bounds the number of classes by one quarter of C(2r,r)+2^r+even(r) C(r,r/2). Section V asks for a complete characterization."
strata_touched:
  - D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery
license: citation-only
triage: anchor
---

# Permutation separability criteria

## Source locator

L. Clarisse and P. Wocjan, *On independent permutation separability criteria*,
arXiv:quant-ph/0504160v2, Quantum Information and Computation 6(3), 277–288.
The source locator is https://arxiv.org/abs/quant-ph/0504160v2.
The bibliographic identity and quotations here are supplied by the problem brief;
no independent online literature search is asserted.

## Source statements

Section II uses the interleaved convention

> A general state ρ ∈ H can be expanded as ρ = Σ ρ_{i1 i2, i3 i4, ..., i2r−1 i2r} |i1 i3 ... i2r−1⟩⟨i2 i4 ... i2r|, where all indices run from 1 to d.

and defines the permutation by

> (Λσ(ρ))_{i1 i2, ..., i2r−1 i2r} = ρ_{iσ(1) iσ(2), ..., iσ(2r−1) iσ(2r)}.

The trace norm is denoted by

> ‖A‖ = Tr(AA†)^{1/2}.

Definition 1 states:

> We call the corresponding entanglement criteria σ and µ dependent if and only if ‖Λσ(ρ)‖ = ‖Λµ(ρ)‖, for all quantum states (that is, positive operators with trace 1). Else, the permutation criteria are called independent.

Theorem 3 gives the upper bound

\[
\frac14\left[\binom{2r}{r}+2^r+
\mathbf1_{2\mid r}\binom{r}{r/2}\right].
\]

Section V states:

> to give a complete characterization of the independent criteria is an open problem.

and

> It is unlikely that there are more dependences in the criteria from Theorem 3.

## Mathematical correspondence

The tensor positions in `PermutationCriteria.RowSetRecovery` are numbered from zero.
Position 2k is the ket coordinate and position 2k+1 the bra coordinate of factor k.
The entry permutation uses sigma itself, exactly as in Section II.
The set `rowSet sigma` consists of original positions sent to even output slots.
The matrix index type is the function space from Fin r to Fin d.

The predicate `IsDensity` reuses positivity and trace one on finite complex
matrices. The existing `FiniteTraceDistance.traceNorm` is defined using
the square root of A†A. Equality with the AA† convention follows from
adjoint invariance of that trace norm, since applying its definition to A†
gives the AA† expression.

The four proposed symmetries of an r-element row set are identity,
complementation, simultaneous exchange of each factor's two positions,
and exchange followed by complementation. The proposed separation mechanism
uses one-party mixed states to identify the same-side factors and two-party
Bell states to identify pairwise distances between their two side labels.

## Scope and related count

Norm dependence in Definition 1 is distinct from equality, inclusion, or
incomparability of the sets of entangled states detected by criteria.
The source's term “truly independent” concerns this latter question;
classification of norm dependence alone does not settle it.

The displayed upper-bound sequence is the sequence associated with
OEIS A045723 in the problem brief. Identifying the four-symmetry orbits
with norm-dependence classes would make that upper bound exact. A finite
orbit count and the analytic separation statement are separate obligations.

## Literature boundary

Only the source excerpts and bibliographic data supplied in the brief are
used here. The supplied preregistration is issue 30402. Whether subsequent
literature already resolves the question has not been independently checked
in this offline environment.
