---
slug: bce14
bibkey: barrett2022laplacianspread
doi: 10.48550/arXiv.2206.15410
url: https://arxiv.org/abs/2206.15410v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap.result
---

## Problem

Barrett–Cameron–Evans–Hall–Kempton, *On the Laplacian spread of digraphs*, arXiv:2206.15410v1, Conjecture 14, page 15: “There is no balanced digraph that satisfies $0<\operatorname{sp}(\Gamma)<1$.” Section 6 specifies unweighted digraphs. Preregistration: [#21873](https://github.com/the-omega-institute/trureturing/issues/21873).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite simple unweighted digraph | `Digraph (Fin n)`, `FiniteGraphEntropy.adjacency` with its natural entries cast to real numbers | Directed relations permit both opposite arcs; looplessness is explicit. |
| Meaningful constrained extrema | $n\ge2$ | Orders zero and one have no zero-sum unit vector. |
| Balanced at every vertex | Shared `Balanced` | Equality of the explicit outgoing and incoming adjacency sums. |
| $L=D-A$ | Shared `laplacian` | The diagonal holds the outgoing degrees. |
| $\alpha$ and $\beta$ are constrained extrema | Shared `quadraticValues`, `alpha`, `beta` | Real Euclidean unit vectors with zero coordinate sum; infimum and supremum are attained. |
| No strict spread in $(0,1)$ | `claim`, `result` | The full universal assertion; no symmetry assumption or weighted extension. |

`FiniteGraphEntropy.adjacency` supplies the natural adjacency entries. Casting them to real numbers gives exactly the source’s zero/one conditional. The directed degrees, Laplacian and quadratic extrema are owned once by `BarrettLaplacianSpreadSlopeRefutation`; the C14 claim retains the preregistered mathematical convention.

## Motivation

The settling declaration is `D5.S3.Combinatorics.SpectralGraph.BarrettBalancedLaplacianSpreadGap.result`. It proves the complete named gap assertion. The finite checks below support source fidelity and do not replace the universal proof.

## Gap

The published question asks whether a balanced unweighted digraph can have a positive spread below one. The result excludes that interval at every order $n\ge2$. Classification of all spread-one cases and Conjecture 15 remain open here.

## Route

Projected coordinate vectors have Rayleigh values $nd_i/(n-1)$. When the spread is at most one, integral outgoing degrees must coincide. The symmetric adjacency matrix then has entries in $\{0,1,2\}$ and constant even row sum. Pair differences exclude simultaneous off-diagonal zero and two entries under strict width below one. Passing to the complement reduces the remaining case to an even-regular simple graph. The centered Frobenius estimate excludes interior degrees; a matching supplies the endpoint obstruction. Scalar restrictions at the empty and complete endpoints have zero spread.

## Falsifier

A loopless balanced unweighted digraph of order at least two whose literal constrained quadratic extrema give $0<\beta-\alpha<1$ would contradict `result`. Arbitrary positive real weights are outside its hypotheses.

## Evidence

The Lean source and Blueprint are `D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap.lean` and its matching Scribe. The settling theorem has proof shape `bind-only` and admission basis `open-problem-resolution (#21873; Proved)`. Its four-slot escape audit is unfinished under [#22040](https://github.com/the-omega-institute/trureturing/issues/22040); no validated registration is claimed.

The exact experiment is [bcehk-laplspread at commit 2189938c4555f35b12767dce2ac078784f928114](https://github.com/the-omega-institute/trureturing-experiments/tree/2189938c4555f35b12767dce2ac078784f928114/docs/reports/bcehk-laplspread). Command: `python3 /Users/auric/trureturing-experiments/docs/reports/bcehk-laplspread/check.py`; exit 0. Script SHA-256: `c37f6d846b9c1342f26d3284250e053c90313946f9f50d636cb8483fff3d6366`. Python 3 and SymPy 1.14.0 use exact rational arithmetic and polynomial root isolation. All checks pass. Tested scopes and readings appear below.

## Triage

| Item | Status and evidence |
| --- | --- |
| Every loopless balanced unweighted digraph of order $n\ge2$ has no spread strictly between zero and one | Proved in Lean: `BarrettBalancedLaplacianSpreadGap.result`. |
| Spread at most one already forces regular outgoing degrees | Proved in Lean: private `BarrettBalancedLaplacianSpreadGap.regular_of_spread_le_one`, under the same order, looplessness and balance hypotheses. |
| A matching on at least four vertices has zero-sum Rayleigh values $-1$ and $1$, precluding a centered radius below one | Proved in Lean: private `BarrettBalancedLaplacianSpreadGap.matching_bound_impossible` establishes the radius obstruction. Its proof constructs vectors with squared norms $2,4$ and quadratic values $-2,4$, giving those quotients. |
| The literal quadratic-value set is nonempty and compact for $n\ge2$, and both extrema are attained | Proved in Lean: private `quadraticValues_nonempty` and `extrema_attained` in `BarrettBalancedLaplacianSpreadGap`, and public `BarrettLaplacianSpreadSlopeRefutation.quadraticValues_isCompact`. |
| Exact checker, including small balanced orders and directed $C_4$ | Computed by the experiment in Evidence: all labeled balanced digraphs at orders $2,3,4$ have counts $2,10,152$, respectively; zero-spread counts $2,4,2$. Directed cycles at orders $2,3,4,6$ have spreads $0,0,1,3/2$. The variance identity and strict estimate pass at 930 degree/order pairs with $5\le n\le64$. This finite test does not establish an unbounded assertion. |
| Half-weight directed $C_4$ has spread $1/2$; empty and complete bidirected examples have zero spread | Proved in prose by the exact derivation below. The weighted graph is outside the unweighted claim. |
| Complete spread-one classification, a general weighted gap, and Conjecture 15 | Open; none is asserted by this delivery. |

### What the settlement shows

The decisive mechanism is degree integrality followed by the symmetric adjacency entry pattern and a centered Frobenius estimate. The regularity consequence holds already at spread at most one, as the private theorem states. The matching obstruction explains why the endpoint cannot admit a centered radius strictly below one. The strict gap theorem does not classify equality.

For the directed four-cycle, the symmetric part of its Laplacian is $I-(P+P^T)/2$, where $P$ is the cyclic permutation matrix. Its eigenvalues on the zero-sum subspace are $1,1,2$, so its spread is one. Scaling every arc by $1/2$ scales the Laplacian and every quadratic value by $1/2$, giving $1/2,1/2,1$ and spread $1/2$. This is an exact proof in prose of the weighted boundary, not a new Lean claim. On three vertices the empty Laplacian is zero; the complete bidirected Laplacian is $3I-J$, which is $3I$ on the zero-sum subspace. Their spreads are zero. These examples show that the unweighted hypothesis matters and the threshold one is sharp.

The source's Conjecture 15 remains a separate equality-classification question. The proof uses no upper-bound equivalence criticized in the Li–Ji corrigendum. No downstream source theorem is asserted to depend on Conjecture 14, and no source theorem is withdrawn. The companion settlement of Conjecture 20 addresses general digraphs and does not extend the balanced gap to weighted inputs.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The source screen in #21873 found no settlement among the inspected arXiv works and later-author texts. The journal full text, complete citing-work inventory, latest Li–Ji corrigendum, Gregory–Hershkowitz–Kirkland nonprincipal-spectrum implications, and Cameron–Graillat text remain unverified. No exhaustive priority claim is made. Four-slot escape registration remains unfinished under #22040.
