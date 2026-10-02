---
slug: kumari-adhikari-2022-structured-negativity-coincidence-refutation
bibkey: kumari2022structured
doi: 10.48550/arXiv.2209.03909
url: https://arxiv.org/abs/2209.03909v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.result
---

# Negativity and structured negativity differ for a pure two-qutrit state

## Problem

A. Kumari and S. Adhikari, “Structured negativity: A physically realizable
measure of entanglement based on structural physical approximation”,
arXiv:2209.03909v1 (2022-09-08, quant-ph), state in the abstract:

> For d ⊗ d dimensional state, we conjecture from the result obtained in this work that negativity coincide with the structured negativity when the number of negative eigenvalues of the partially transposed matrix is equal to d(d−1)/2.

The conclusion repeats: “Thus, we conjecture that the negativity and
structured negativity coincides when q=d(d−1)/2.” Issue
[#11475](https://github.com/the-omega-institute/trureturing/issues/11475)
preregisters this quantified reading and the counterexample before any Lean.
The claim ranges over natural dimensions d ≥ 2 and positive semidefinite,
trace-one matrices on ℂ^d ⊗ ℂ^d. The partial transpose on B sends the entry
ρ_(i,j),(k,l) to ρ_(i,l),(k,j); q counts its strictly negative eigenvalues
with multiplicity.

## Motivation

Equation (6) defines negativity as the normalized negative-eigenvalue sum
N(ρ) = (2/(d−1)) Σ_(λ_i<0) |λ_i(ρ^(T_B))|. Equation (7) defines
ρ̃ = (d/(d³+1)) I + (1/(d³+1)) ρ^(T_B). Equation (9) defines
N_S(ρ) = d(d³+1) max{d/(d³+1) − λ_min(ρ̃), 0}.
The conjecture asserts equality when q=d(d−1)/2, rather than only the
inequality derived in the paper.

## Gap

The bounded literature check recorded in #11475 reports that the first
author's thesis, arXiv:2305.16643 (2023), Chapter 6, restates the conjecture
as open. The citing arXiv sources 2504.15203, 2407.04478 and 2301.09884 were
searched for the conjecture; no settlement was found. MathDB and the
formal-conjectures corpus searches recorded there did not identify this
problem's settlement. These readings are not-found-in-searched-scope,
not an exhaustive worldwide literature search or a priority claim.

## Route

Take d=3, ψ=(|00⟩+2|11⟩+2|22⟩)/3 and ρ=|ψ⟩⟨ψ|. The vector has squared
norm (1+4+4)/9=1, so ρ is a positive semidefinite, trace-one matrix. Its
partial-transpose eigenvalue multiset is
{1/9,2/9,2/9,−2/9,4/9,4/9,−2/9,−4/9,4/9}. Hence q=3=3(3−1)/2 and
N=8/9. The contextual source bound q≤(d−1)² also holds: 3≤4.

An explicit rational change of basis uses |ii⟩ and, for i<j,
|ij⟩+|ji⟩ and |ij⟩−|ji⟩. Similarity preserves the characteristic
polynomial; Mathlib identifies its roots with the Hermitian eigenvalue
multiset, retaining algebraic multiplicity. The same basis diagonalizes
ρ̃, with eigenvalues
{7/63,29/252,29/252,25/252,31/252,31/252,25/252,23/252,31/252}.
Thus λ_min(ρ̃)=23/252 and
N_S=84 max{3/28−23/252,0}=4/3, which differs from 8/9.

## Falsifier

The source-literal normalization, negative-eigenvalue multiplicity, and
SPA scale are essential. A different normalization is a different claim.
The proof checks Hermiticity, density, the similarity certificates, both
spectra and their derived quantities with exact rational arithmetic.
The public conclusion is the unconditional negation of the universal
claim, rather than a conditional assertion about an unspecified state.

## Evidence

The canonical source is
`D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.lean`.
Its sole public theorem `result : ¬ claim` refutes the published claim.
Eight parameterized definitions and `claim` supply the source vocabulary;
all matrix certificates are local proofs inside `result`. Its only direct
import is `Mathlib.Analysis.Matrix.PosDef`; the proof uses no new axiom,
`sorry` or `native_decide`. The Scribe mirror attaches resolution `Refuted`
to the frozen result.

Equation (6)'s trace-norm equality is source-attested. The Lean definition
uses its eigenvalue-sum form; no separate trace-norm equivalence is claimed.
The non-Hermitian empty-spectrum extension is unused by the counterexample.

## Triage

Tier 1 external named conjecture, preregistered in #11475; `theorem`,
resolution `Refuted`. The result has `proof_shape: bind-only`: the explicit
rational similarity certificates, pinned spectral theorems and finite
normalization suffice. Admission is `open-problem-resolution`; there is
no escape witness or atom. Utility is `certified-instance`, with typed
`claim` and `result`, basis `refutes`.

逃逸审计未完成：现役 lean-report 输入因
[#11269](https://github.com/the-omega-institute/trureturing/issues/11269)
暂停 Reg，无法产出当前 binding evidence。

### What the settlement shows

- **Proved**, `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.result`:
  density and q=d(d−1)/2 do not suffice for equality, even for a pure state.
- **Computed**, using the exact-matrix command below: the witness has negative
  magnitudes 2/9, 2/9, 4/9. N uses their sum, while N_S is three times the
  largest magnitude; their unequal magnitudes leave a strict gap. Count q=3
  does not control this distinction. Equation (32) specializes to N_S≥N
  and remains true, strictly, for this counterexample; equation (24) also
  holds here, since 8/9≤(4/3)(4/3).
- **Computed**, with the same command: the maximally entangled two-qutrit
  pure state with coefficients (1,1,1)/√3 has q=3 and N=N_S=1. Thus a
  symmetric special case survives; equality is not refuted for every state.
- **Open**: a repaired general statement adding equality of all negative
  partial-transpose eigenvalue magnitudes is a candidate sufficient condition.
  This delivery does not formalize its general affine-spectrum argument or
  settle all dimensions. It is a separate candidate subject to the ordinary
  literature and admission rules, not an extra theorem in this module.
- **Source reading / open boundary**: the paper states inequalities (24),
  (32), its examples and the entanglement-measure properties before the
  concluding conjecture. This refutation removes the asserted universal
  coincidence under the q condition. It does not itself refute those
  independent inequalities, examples, monotonicity arguments or experimental
  claims; their general validity is not certified by this delivery. Any
  downstream use of q alone to replace N_S by N requires a new justification.

Reproducible exact computation (Python 3, SymPy 1.14.0; exit 0):

```sh
python3 - <<'PY'
import sympy as S
for c in [(S.Rational(1,3), S.Rational(2,3), S.Rational(2,3)),
          (1/S.sqrt(3),)*3]:
    rho = S.Matrix(9, 9, lambda a,b:
        c[a//3]*c[b//3] if a//3 == a%3 and b//3 == b%3 else 0)
    pt = S.Matrix(9, 9, lambda a,b: rho[3*(a//3)+b%3, 3*(b//3)+a%3])
    spa = S.Rational(3,28)*S.eye(9) + pt/28
    e = pt.eigenvals()
    q = sum(m for v,m in e.items() if v < 0)
    n = sum(-v*m for v,m in e.items() if v < 0)
    ns = 84*max(S.Rational(3,28)-min(spa.eigenvals()), 0)
    print(e, 'q=', q, 'N=', n, 'N_S=', ns,
          'eq32=', ns >= n, 'eq24=', n <= S.Rational(4,3)*ns)
PY
```

The two output triples are `(3, 8/9, 4/3)` and `(3, 1, 1)`;
both printed inequalities are `True` for each state. These computations
supplement the kernel-checked counterexample; they are not additional frozen
theorems.

## ASSUMED-UNVERIFIED

The non-arXiv 2024 citing record “Entanglement Detection for Multipartite
States Based on Structural Physical Approximation of Partial …” listed in
#11475 was not read. The bounded check does not establish worldwide novelty,
priority or the absence of an independent answer. The Lean kernel verifies
the encoded mathematical statement, not the external source's authorship
or version history. No physical preparation or measurement is certified.
