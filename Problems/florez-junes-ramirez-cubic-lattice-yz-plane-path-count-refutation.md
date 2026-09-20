---
slug: florez-junes-ramirez-cubic-lattice-yz-plane-path-count-refutation
bibkey: florez2018cubiclattice
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf
triage: theorem
motivation_gids:
  - D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.result2
---

# Flórez-Junes-Ramírez yz-plane path-count refutation

## Problem

Flórez, Junes, and Ramírez, Journal of Integer Sequences 21 (2018), Article
18.1.2, Section 2 (Background) on printed page 3, define the path family as follows:

> We use C_n^±(k) to mean the set of all paths of length k in the n-dimensional cubic lattice. We divide C_n^±(k) into subfamilies depending on the behavior of the path. We now give definitions and notation for those families. If P = (±e_{j_1})(±e_{j_2}) · · · (±e_{j_k}), then we define V_r := (±e_{j_1}) + (±e_{j_2}) + · · · + (±e_{j_r}), the algebraic combination of the first r components of P for 0 < r ≤ k, i.e., V_r is the sum of the components of any initial subpath of P with r steps. We denote C_n(k) the subset of C_n^±(k) formed by all paths P = (±e_{j_1})(±e_{j_2}) · · · (±e_{j_k}) that satisfy that the nth coordinate of V_k is zero. We use C_n^≥(k) to denote all paths in C_n^±(k) with P = (±e_{j_1})(±e_{j_2}) · · · (±e_{j_k}) and that nth coordinate of V_r is non-negative for all 0 < r ≤ k. We now let C_n^+(k) be C_n^≥(k) ∩ C_n(k). […] For example, Figure 1 depicts the 14 paths in C_2^+(3). Figure 2 depicts the 17 paths in C_3^+(2).

The paper also specifies that paths start at `p_0 = (0, ..., 0)` and each step
is a positive or negative coordinate direction.

Section 6 on printed page 23 states:

> **Conjecture 2:** For k ≥ 1, the number of paths in C_3^+(k) that are completely contained in the yz−plane is Σ_{i=1}^{k+1} \binom{2i}{i}\binom{k}{i−1}/(i+1).

The formal `claim2` retains the
universal quantifier, lower bound, printed path predicate, plane-containment
condition, and binomial sum. The theorem `result2` proves its negation.

## Motivation

The printed definition requires the third coordinate to be nonnegative along
every nonempty prefix and to return to zero after the complete path. Complete
containment in the yz-plane requires the first coordinate of every vertex to
be zero; the initial vertex already is the origin.

Under that printed reading, the yz-plane counts for `k = 1, 2, 3` are
`2, 5, 14`. If the final-zero clause is omitted while prefix nonnegativity is
retained, the corresponding counts are `3, 10, 35`. Both readings disagree
with the printed value `36` at `k = 3`.

Table 4 gives `3, 10, 36, 137, ...`, labels the sequence `A002212(k + 1)`,
and assigns it to the yz-plane count. Direct enumeration from the printed
definitions instead gives the Catalan values `2, 5, 14, 42` for `k <= 4`.
No corrected formula or Catalan identification beyond `k <= 4` is asserted.

## Gap

Issue #9059 records the preregistered statement and literature check. The
published JIS article has no arXiv version. MathDB contains no entry for the
paper. OEIS A002212, the sequence Table 4 names, does not cite the paper and
records no correction of either conjecture.
The repository and open-pull-request searches found no prior settlement in
the searched scope.

These searched surfaces do not establish exhaustive publication absence, and
no publication-priority claim is made.

## Route

Enumerate all `6^3 = 216` signed three-step paths. Filtering by the printed
`C_3^+(3)` and yz-plane predicates gives `yzCount 3 = 14`; evaluating the
printed binomial sum gives `formula 3 = 36`. Instantiating `claim2` at `k = 3`
therefore requires `14 = 36`, a contradiction.

## Falsifier

The refutation would fail if the formal path space omitted a signed coordinate
step, if the prefix, final-zero, or yz-plane condition differed from the
printed definitions, if the filtered count were not 14, or if the printed sum
were not 36 at `k = 3`. The formal definitions, finite controls, and theorem
retain each of these links.

## Evidence

- Lean theorem:
  `D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.result2`.
- Freeze event:
  `sha256:50f66dab38bd4f17913505bd4fe226f9f25e6255162c8affaf2d13c0e81d2f59`.
- Module statement identity:
  `sha256:2f520f596576ed67f83663c5eb685d7a883e917cf9bb5fc38c7f673203e6c86d`.
- Result declaration identity:
  `sha256:aa2421611811c2e9af42158bf1998805b5a3e95eb455afdbab83ebffc5213e93`.
- The Freeze event has no project-level frozen prerequisites; all imports are
  pinned Mathlib modules.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`; first-tier external named conjecture, preregistered in issue #9059.
The public theorem has `proof_shape: bind-only`: it projects the printed
universal clause, instantiates it at `k = 3`, and closes the two finite counts
by kernel evaluation. Its `escape_witness` is `none`, and its
`admission_basis` is `open-problem-resolution`. Its computational use is a
`certified-instance` with a typed `refutes` edge from `result2` to `claim2`.
There is no atom and no digestion coverage edge.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the bounded search cannot
exclude every prior resolution or establish publication priority.
Source-to-Lean fidelity and proof-shape classification remain semantic review
judgments; the Lean kernel checks the formal statement and proof, not their
equivalence to the cited prose.
