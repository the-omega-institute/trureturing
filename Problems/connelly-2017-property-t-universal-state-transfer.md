---
slug: connelly-2017-property-t-universal-state-transfer
bibkey: connelly2017universality
doi: 10.1016/j.laa.2017.06.015
url: https://arxiv.org/abs/1701.04145v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.result
---

# A unit-gain circulant on three vertices with universal perfect state transfer

## Problem

E. Connelly, N. Grammel, M. Kraut, L. Serazo and C. Tamon (arXiv:1701.04145,
quant-ph and math.CO; Linear Algebra Appl. 531 (2017) 516–532) study the
continuous-time quantum walk `U(t) = exp(−i t A)` of a graph with Hermitian
adjacency matrix `A`. The walk has universal perfect state transfer if for all
vertices `u, v` some time gives `|U(t)_{v,u}| = 1`. A graph has property `𝕋`
if every nonzero entry of `A` has modulus `1`. The paper states:

> \begin{conjecture} $\Circ(0,-\ii,\ii)$ is the only circulant with property
> $\TT$ which has universal perfect state transfer. \end{conjecture}

and, in its introduction, "The only known examples of complex unit gain graphs
with the universal property are the circulants $K_{2}$ and $\Circ(0,-\ii,\ii)$.
We conjecture that this set is unique."

Issue #11528 fixes the reading. `Circ(a)` has entries `C_{jk} = a_{k−j}`
over `ℤ/nℤ`, "the only" is read up to the paper's switching equivalence
(`MA = BM` with `M` a permutation matrix times an invertible diagonal matrix)
and together with `K₂`, the order is `n ≥ 2`, and the circulant is Hermitian
without loops. The formal `claim` is: every such circulant with property `𝕋`
and universal perfect state transfer is switching equivalent to `K₂` or to
`Circ(0, −i, i)`. The result refutes it.

## Motivation

Universal perfect state transfer is rare: real symmetric matrices on more
than two vertices never have it, and a later paper (arXiv:2301.01473) proved
that among oriented graphs, with weights `±i`, only `K₂` and the oriented
triangle have it. The property-`𝕋` conjecture allows arbitrary unit phases.
The frozen declaration
`D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.result` shows that
it fails already on three vertices.

## Gap

Issue #11528 preregisters the reading, the counterexample and the literature
check. The conjecture is in the latest arXiv version. Semantic Scholar lists 15
citing records. The arXiv sources of the 10 with arXiv identifiers were
searched at every mention of the paper, of universality, of unit gains and of
unimodular weights; none states or refutes the property-`𝕋` conjecture.
arXiv:2002.04666 restates it for unweighted oriented graphs, and
arXiv:2301.01473 proves that oriented version. The witness follows from the
Cameron et al. eigenvalue criterion that the paper quotes, and Zimborás et al.
(arXiv:1208.4049) remark that the chiral triangle reaches perfect transfer for
phases found by phase matching; no publication found states that the
conjecture fails.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Take `A = Circ(0, α, ᾱ)` with `α = (−4√3 + i)/7`. Then `|α| = 1`, so `A` is
   Hermitian, has no loops and has property `𝕋`.
2. The Fourier matrix `V_{km} = ω^{km}`, `ω = e^{2πi/3}`, diagonalizes `A`
   with eigenvalues `(√3/7)(−8, 3, 5)`.
3. At `t₁ = 14√3π/9` the phases `e^{−i t₁ λ_m}` are `ω², 1, ω`, so
   `U(t₁) = ω² P` with `P` the cyclic permutation matrix, and
   `U(2t₁) = U(t₁)²`. With `U(0) = I` this gives universal perfect state
   transfer.
4. `det A = α³ + ᾱ³ = −360√3/343 ≠ 0 = det Circ(0, −i, i)`, and a monomial
   matrix is invertible, so `A` is not switching equivalent to
   `Circ(0, −i, i)`; it is not switching equivalent to `K₂` since `3 ≠ 2`.

## Falsifier

The answer would change if "circulant" were restricted to weights in
`{0, ±i}`: that oriented statement is a theorem of arXiv:2301.01473. It does
not change under rescaling of `A`: for `c ≠ 0`, `det(cA) = c³ det A ≠ 0`
while `det Circ(0, −i, i) = 0`. The literal sentence of the conjecture omits
`K₂`; the reading includes `K₂`, as the paper's introduction does.

## Evidence

Exact SymPy arithmetic (issue #11528) gives the eigenvalues
`[−8√3/7, 3√3/7, 5√3/7]`, `U(14√3π/9) = ω̄ P`, `U(28√3π/9) = ω P²` and
`det A = −360√3/343`. As a positive control, the same code on `Circ(0, −i, i)`
reproduces the paper's known example.

The canonical source is
`D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.lean`. Its public
declarations are `PropertyT`, `UPST`, `SwitchingEquivalent`, `K2`,
`orientedTriangle`, `claim` and `result`. The frozen module state has statement
identity
`sha256:0626c620229dbc592b50fc061705092ee9cf1f27255588fcd0766c2e39a139bc`.
The result declaration has statement identity
`sha256:b351231e29348c584acf93cdc8498913b76e7c7689ef35db3a0ce464419bfda6`.
The Freeze event is
`sha256:2f26f5e60d2e2790d6be55801b59731d2967ebb2b5805966b46a5507ec3f2e7c`.
Its project-level frozen prerequisite is the module providing
`hamiltonianPropagator`. The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2017 quant-ph and math.CO paper, preregistered in
issue #11528 before any Lean. `theorem`; resolution `refuted`. The public
theorem has `proof_shape: bind-only`: the Fourier diagonalization, the three
phases and the matrix exponential lemmas of Mathlib give the closed form of the
walk at `t₁`, and every step is a local `have` of `result`. Its admission basis is
`open-problem-resolution`. Utility `kind=certified-instance; basis=refutes`
with typed `claim` and `result`.

### What the settlement shows

**Refuted:** `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.result`
shows that the property-`𝕋` conjecture fails already for circulants of order 3.
**Inspection of the checked proof, not a separate theorem:** the witness's
eigenvalues are `√3/7` times the integers `−8, 3, 5`, which have distinct
residues mod 3; this is the Cameron et al. criterion quoted by the paper, and it
does not depend on the weights being `±i`.

**Surviving restriction:** for weights `±i` (oriented graphs) the uniqueness
statement is the theorem of arXiv:2301.01473; the witness has unit weights
other than `±i` and does not bear on it.

**Bounded source consequences:** the witness is a Hermitian graph on 3 vertices
with unit weights and universal perfect state transfer that is not switching
equivalent to `Circ(0, −i, i)`, so it also contradicts Fact 5 of
arXiv:1701.04145v2 §8 (l. 1117–1119: "$\Circ(0,-\ii,\ii)$ is the only graph on
$3$ vertices with universal perfect state transfer, up to switching
equivalence") when graphs carry unit gains. The Fact's proof shows that such a
graph is a circulant diagonalized by the Fourier matrix, but it does not fix the
eigenvalues. This consequence follows by inspection of the checked witness and
is not a separate formal theorem.

**Open extent:** the classification, up to switching equivalence, of the
property-`𝕋` circulants of order `n ≥ 3` with universal perfect state
transfer is not settled here.

## ASSUMED-UNVERIFIED

The published Linear Algebra Appl. text was not read, so it is unverified
whether the conjecture was edited there. The bounded literature check does not
establish exhaustive worldwide novelty, priority, or the absence of an
independent answer. The Lean kernel does not authenticate the external source
or its version history.
