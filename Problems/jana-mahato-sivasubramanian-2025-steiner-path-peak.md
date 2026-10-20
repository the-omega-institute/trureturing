---
slug: jana-mahato-sivasubramanian-2025-steiner-path-peak
bibkey: janamahatosivasubramanian2025steinerpeak
doi: 10.1007/s40314-025-03163-5
url: https://arxiv.org/abs/2407.03309v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.result
---

# Conjecture 29 on the path Steiner coefficient peak is false

## Problem

S. Jana, I. Mahato and S. Sivasubramanian, *Unimodality and peak location of the
characteristic polynomials of two distance matrices of trees*, Computational
and Applied Mathematics 44, 223 (2025), arXiv:2407.03309v1, Conjecture 29,
page 18:

> For a path P_n on n > 5 vertices, if CharPoly_{𝔇_{P_n}}(x) = Σ_{i=0}^{2n−3} a_i x^i and |a_ℓ| = max{|a_0|, |a_1|, …, |a_{2n−4}|}, then ℓ = n − 1.

The [Library note](../Library/GraphInvariants/janamahatosivasubramanian2025steinerpeak.md)
quotes the distance, basis and principal-submatrix definitions.
Preregistration: [#19152](https://github.com/the-omega-institute/trureturing/issues/19152).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Minimum edges of a connected subtree containing the four vertices | `steiner n S` | A connected subtree of a path is an interval with $b-a$ edges; the natural infimum ranges over exactly the containing intervals |
| Ordered basis $(e_1,f_1,…,e_{n-2},f_{n-2},e_{n-1})$ | `basis n t` | Even zero-based indices give $e_i=\{i,i+1\}$ and odd indices give $f_j=\{j,j+2\}$ |
| Principal matrix $\mathfrak D_2(P_n)[B,B]$ | `D n` | Each integer entry is the Steiner distance of the union of its row and column pairs |
| Every path with $n>5$ | `claim` quantifies over natural $n$ with $5<n$ | No extra graph or numerical hypothesis |
| Largest magnitude among coefficients $0,…,2n-4$ | The quantified coefficient inequalities in `claim` | The leading coefficient is excluded exactly as in the source |
| Every attaining index equals $n-1$ | The conclusion of `claim` | Quantifying over all attaining indices does not assume uniqueness |
| Refutation | `result : ¬ claim` | The witness has $n=16$ and $\ell=16\ne15$ |

All natural subtractions and finite-index types retain the literal source
conventions. The interval bounds are the definition of a subtree, not an
additional hypothesis on the conjecture. The characteristic polynomial is
$\det(xI-D)$.

## Motivation

The coefficient peak changes location beyond the small sizes displayed in the
source. A finite exact counterexample decides the universal conjecture without
requiring a formula for all path orders.

## Gap

The literature screen recorded in #19152 covers citing works and posted
solutions, MathDB, QIQC, `google-deepmind/formal-conjectures`, repository issues
and the problem register. It found a posted solution of Conjecture 30 and no
settlement of Conjecture 29 in that searched scope. These are
orchestrator-reported source and literature checks. Completeness and comparison
with the journal full text are `ASSUMED-UNVERIFIED`.

## Route

For $n=16$, the principal matrix has order $29$. The private theorem
`steiner_of_bounds` evaluates the interval infimum at its extreme contained
vertices. The private theorem `D_sixteen` identifies the resulting matrix with
its endpoint expression.

The literal integer matrices in the module satisfy $AK=KC$. A left inverse of
$K$ modulo $7$ proves $\det K\ne0$. The proof applies
`Matrix.charpoly_eq_of_mul_eq_mul` to identify the characteristic polynomial
with that of $C$. The existing owner theorem
`D5.S3.Constants.Moments.CoefficientDrivenJacobiCharacteristicPolynomial.multiplication_matrix_charpoly`
identifies the companion polynomial after the injective integer-to-real cast
and finite reindexing in `companion_charpoly`.

The exact coefficient certificate gives
$|a_{15}|=939602445008$ and $|a_{16}|=956326515118$.
The proof of `result` checks that index $16$ dominates all indices $0$ through
$28$, then specializes the universal conjecture to obtain the false equation
$16=15$. Uniqueness is computed below; it is not a separate public Lean theorem.

## Falsifier

A mismatch with the source's ordered principal submatrix, an incorrect
characteristic polynomial, or an index $i\le28$ whose magnitude exceeds that
at $16$ would defeat this witness. The module checks the matrix correspondence,
the integer certificates and the complete nonleading coefficient comparison
in Lean.

## Evidence

The settling module is
`D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.lean`.
Its sole public theorem is `result`; its twelve theorem helpers are private and
consumed. They have `proof_shape: bind-only` and no strict escape witness is
asserted. The module has `admission_basis: open-problem-resolution (#19152; Refuted)`
and certified-instance utility refuting `claim`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The published owner theorem
`D5.S3.Constants.Moments.CoefficientDrivenJacobiCharacteristicPolynomial.multiplication_matrix_charpoly`
has an unfinished escape audit under
[#19385](https://github.com/the-omega-institute/trureturing/issues/19385).
No compiled faithful registration supplies its full polynomial domain,
monicity guard bridge, lawful readout, reconstruction and intervention/sensitivity
proofs. No completed registration is claimed.

### Experiment

[Exact finite checker](https://github.com/the-omega-institute/trureturing-experiments/tree/059752d70d5d4d09830c871edf1dbac708504d2a/docs/reports/jana-mahato-sivasubramanian-2025-steiner-path-peak).
Command: `python3 /Users/auric/trureturing-experiments/docs/reports/jana-mahato-sivasubramanian-2025-steiner-path-peak/check.py`,
using `check.py` verified byte-for-byte against the linked commit; exit $0$,
`RESULT PASS`. Script SHA-256:
`1b4c1ae8bce175d6352cee57496a804b037ca549d83792eb7d846c459063200a`.
The program computes exact integer characteristic polynomials by
Faddeev–LeVerrier for precisely $6\le n\le22$. The unique maximizing index is
$n-1$ for $6\le n\le15$ and $n$ for $16\le n\le22$. At $n=16$ the magnitudes
at indices $15,16,17$ are $939602445008$, $956326515118$ and $802497798666$.
It checks the source peak bound and both coefficient identities throughout
that finite range. The program and data reside in the experiments repository.

## Triage

### What the settlement shows

| Item | Status and evidence | Boundary |
| --- | --- | --- |
| Conjecture 29's exact location $n-1$ | **Kernel-checked:** `result` refutes `claim` using $n=16$, $\ell=16$ and the complete maximum premise | It proves the universal statement false; uniqueness of the maximum is computed |
| The peak changes after the small examples | **Computed:** the experiment finds the unique maximum $n-1$ for $6\le n\le15$ and $n$ for $16\le n\le22$ | No extrapolation beyond $22$ |
| Neighboring source statements remain consistent with the witness | **Computed:** at $n=16$, $16\le\lfloor7n/5\rfloor=22$; for every $6\le n\le22$ the checker verifies $|a_{2n-4}|=3n-5$ and $a_{2n-5}=-(n-1)(n-2)(2n^2+6n-15)/6$ | Neither the uniform upper bound nor Conjecture 30 is negated by this refutation; these identities are not separately formalized here |
| Exact or asymptotic peak for unbounded $n$ | **Open** | The finite computation supplies no uniform formula or asymptotic theorem |
| Affected source conclusions | **Unverified source dependency boundary:** the arXiv excerpt labels the statement Conjecture 29; the complete journal text and every downstream use have not been audited | No completeness claim about affected source conclusions |

The failure mechanism is the larger magnitude at index $16$ than at the proposed
index $15$. The nearest surviving finite observations are the upper bound and
the separate trace and Conjecture-30 identities in the tested range. Whether any
other journal conclusions rely on Conjecture 29 remains unverified.

## ASSUMED-UNVERIFIED

Literature-search completeness, correspondence with the journal full text and
its complete downstream dependency graph are unverified. The experiment is
finite and independent of the kernel proof; its results do not establish a
peak formula for unbounded $n$. The owner theorem's escape audit remains
unfinished under #19385.
