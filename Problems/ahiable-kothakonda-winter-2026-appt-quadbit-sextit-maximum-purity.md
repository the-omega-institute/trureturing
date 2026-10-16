---
slug: ahiable-kothakonda-winter-2026-appt-quadbit-sextit-maximum-purity
bibkey: ahiablekothakondawinter2026geometry
doi: 10.48550/arXiv.2608.03390
url: https://arxiv.org/abs/2608.03390v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.result
---

# Maximum purity in the 4-by-6 absolutely PPT sector

## Problem

Ahiable, Kothakonda and Winter, arXiv:2608.03390v2, Conjecture 6.7,
page 29, asks whether the maximum purity over the absolutely PPT set equals
the inscribed-polytope maximum and occurs at the spectra of Eq. (44).
The exact target is its $m=4,n=6$ sector: every positive semidefinite
complex matrix $\rho$ on $\mathbb C^4\otimes\mathbb C^6$ with trace one and
$(U\rho U^\dagger)^\Gamma\succeq0$ for every global unitary $U$ satisfies
$\operatorname{Re}\operatorname{Tr}(\rho^2)\leq8/169$.
The real purity supremum is $8/169$, attained by the diagonal state with
one entry $3/26$ and twenty-three entries $1/26$. Partial transpose acts
on the second local factor.

## Motivation

Corollary 6.4 and Eq. (44) give $(24+8)/(24+2)^2=8/169$ inside the
inscribed polytope. An attaining state gives only a lower bound. A sharp
upper bound for the full literal APPT set requires an additional inference.
Repeated and zero eigenvalues are included; no simple-spectrum or strict
positivity assumption is added.

## Gap

Research preregistration [#17734](https://github.com/the-omega-institute/trureturing/issues/17734)
fixes this target. It continues the same partial conjecture as
[#17689](https://github.com/the-omega-institute/trureturing/issues/17689),
whose 4-by-4 sector is already delivered. It is not an independent open
problem. The existing qutrit dimension-24 certificate controls all ordered
spectra satisfying two boundary LMIs, but a literal 4-by-6 APPT state needs
a product-corner reduction to those hypotheses. External novelty refresh
is pending; no worldwide-priority conclusion is claimed.

## Route

For all local dimensions $m,n\geq3$, embed $\mathrm{Fin}\,3$ into each
factor and write $c(i,j)=(a(i),b(j))$. The range of $c$ and its finite
complement partition the full product. Cardinality identifies the
complement with $\mathrm{Fin}(mn-9)$, without a dimension-specific list.
The essential identity is

$$ (M^\Gamma)|_c=(M|_c)^\Gamma, $$

since both entries at $(i,j),(k,l)$ are $M(c(i,l),c(k,j))$.
Extending the existing Bell unitary by identity on the complement and
compressing its partial transpose yields the first real boundary LMI;
the existing swapped Bell test gives the second. The global packing used
for sorted spectral diagonalization is a unitary change of eigenbasis,
not an assumed covariance of partial transpose.

The boundary selector takes the largest three and smallest six ordered
eigenvalues and retains every middle value in the full spectrum. Trace
and trace-square therefore remain unchanged. At $mn=24$ the selector is
exactly `QutritSpectralReduction.boundaryValues 5`.
The unchanged `QutritN8PurityBound.certificate_bound` gives the sharp upper
bound, with no copied coefficient arrays or Hildebrand sufficiency premise.

For a computational-basis unit vector $\psi$,
$\rho=(I+2|\psi\rangle\langle\psi|)/26$ has trace one and purity
$(24+8)/26^2$. After every global unitary the unscaled matrix belongs to
the separable cone by the dimension-independent low-rank ray theorem.
Second-factor partial transpose preserves positivity of every separable
product term. Thus this explicit diagonal state is APPT and attains the
upper bound, which also identifies the real supremum.

## Falsifier

A trace-one positive semidefinite 4-by-6 matrix satisfying literal APPT
with real trace-square greater than $8/169$ refutes the target. A failure
of the product compression, complement equivalence or full-spectrum
trace/purity identities would invalidate the proposed reduction.

## Evidence

The canonical Lean targets are `FiniteBellCorner.spectral_reduction` and
`QuadbitSextitMaximumPurity.result` in the owning AbsolutePPT namespace.
The latter states the universal upper bound, real supremum and exact
diagonal attainment together. Local compilation, scoped report, Reg
binding and freeze evidence are reported by their canonical producers;
o whole-repository or official-CI result follows merely from a scoped run.

## Triage

### What the settlement shows

The reusable mechanism transfers necessary Bell-corner constraints across
all finite local dimensions at least three. In total dimension twenty-four,
it allows the existing sharp spectral certificate to settle a second
local tensor-factor sector. The generic reduction is necessary only; it
does not characterize APPT states. The 4-by-5 sector, dimension twenty-five,
all remaining sectors and classification of all maximizers stay outside
this result. The full source conjecture and APPT versus absolute
separability are not settled by this sector.

## ASSUMED-UNVERIFIED

External novelty refresh and official required CI are pending host review.
Same-family Codex CLI independence is disclosed; no Pro review occurred.
Neither a model conclusion nor a source citation substitutes for the
kernel proof or the statement-fidelity review.

The escape registration for the exposed normalization helper
`QuadbitMaximumPurity.norm_of_dot_eq_one` remains unfinished: source
coordinate extraction rejects its implicit `Fintype I` dictionary
(`source.dictionary_or_proof_coordinate`). Its complete original
telescope and compiled Reg proof are retained. The generic
`FiniteBellCorner.spectral_reduction` registration also remains unfinished:
the compiled-source dependency check rejects `Nat.pow`
(`source.unsafe_or_external`). These audit gaps are associated with
[#17689](https://github.com/the-omega-institute/trureturing/issues/17689).
