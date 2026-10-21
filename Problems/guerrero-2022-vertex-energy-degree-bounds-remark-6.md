---
slug: guerrero-2022-vertex-energy-degree-bounds-remark-6
bibkey: guerrero2022laplacianenergies
doi: 10.1016/j.laa.2024.11.016
url: https://arxiv.org/abs/2201.01252v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.result
---

# The upper local degree comparison fails on P6

## Problem

J. Guerrero, *Laplacian Energies of Vertices*, arXiv:2201.01252v1,
Remark 6 (Conjecture), page 13, states:

> According to numerical experiments the analog result is true for the energy
> of vertices, that is: $d_{\min}LE_G(v)\le E_G(v)\le d_{\max}LE_G(v)$ for all $v\in V$.

The standing assumptions are that $G$ is simple and connected. The definitions
are $E_G(v)=|A|_{vv}$, $L=I-D^{-1/2}AD^{-1/2}$ and
$LE_G(v)=|L-I|_{vv}$. The [Library note](../Library/GraphInvariants/guerrero2022laplacianenergies.md)
contains the source quotations and locators. The preregistration is
[#19702](https://github.com/the-omega-institute/trureturing/issues/19702).
The v1 conjecture is refuted by the path on six vertices at zero-based index $2$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite simple graph | `V`, `Fintype V`, `SimpleGraph V` in `claim` | Undirected loopless graph; arbitrary finite vertex type |
| Connected | `G.Connected` | Hypothesis on the entire conjunction |
| Every vertex | `∀ v : V` | Universal quantifier |
| $\lvert A\rvert$ and $E_G(v)=\lvert A\rvert_{vv}$ | `matAbs`, `vertexEnergy`, `SimpleGraph.adjMatrix` | Real symmetric spectral absolute value via `cfc` |
| $D^{-1/2}=\operatorname{diag}(1/\sqrt{d_v})$ | `degInvSqrt` | Natural degrees coerced to real numbers |
| $L=I-D^{-1/2}AD^{-1/2}$ | `normLap` | Literal real matrix expression |
| $LE_G(v)=\varphi_v(\lvert L-I\rvert)$ | `normLapVertexEnergy` | $\varphi_v(M)=M_{vv}$ |
| Both degree inequalities | Conjunction in `claim` | `minDegree` and `maxDegree` coerced to real numbers |
| Negative answer | `result : ¬ claim` | One graph and one vertex refute the universal conjunction |
| Implementation instances | `DecidableEq V`, `DecidableRel G.Adj` | Finite graph operations; no additional mathematical restriction |

Real division fixes reciprocal zero to zero. The counterexample has positive
degrees, so this totalization does not affect the refutation.

## Motivation

The source compares the global trace energies by minimum and maximum degree,
then asks for the analogous comparison at each diagonal entry. Summation
forgets how slack is distributed among vertices.

## Gap

The bounded literature screen in #19702 covers arXiv v1, the publisher metadata,
Arizmendi–Guerrero (arXiv:2205.14527), *On Randić energy of a vertex*
(arXiv:2509.22539), *On the vertex Seidel energy of graphs* (arXiv:2602.17741),
MathDB, `google-deepmind/formal-conjectures`, and repository owners.
No settlement of the quoted assertion was located in that scope. The publisher
full text and two citing papers were not read in full. Literature completeness
is `ASSUMED-UNVERIFIED`; the conclusion concerns the quoted v1 statement.

## Route

The Lean module
[`GuerreroVertexEnergyDegreeBounds`](../D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.lean)
uses `SimpleGraph.pathGraph 6`. Its private `exists_b` provides a real root
$b$ of $b^3+b^2-2b-1=0$ with $1<b<4/3$.
Private positive semidefinite square-root certificates identify the two
spectral absolute values, using Mathlib's `CFC.sqrt_unique` in `abs_a` and
`abs_neg_r`. Private `adjacency_energy` and `normalized_energy` give

$$E_{P_6}(2)=\frac{7+4b-2b^2}{7},\qquad LE_{P_6}(2)=\frac{4+\sqrt5}{10}.$$

Private `adjacency_lower` and `normalized_upper` prove

$$2LE_{P_6}(2)<\frac54<E_{P_6}(2).$$

Private `path_max` identifies the maximum degree as two. The public `result`
applies the conjecture to this connected graph and vertex and contradicts
its upper inequality. All proof steps are conservatively classified
`bind-only`; the module's admission basis is
`open-problem-resolution (#19702; Refuted)`.

## Falsifier

The universal upper bound would imply
$E_{P_6}(2)\le 2LE_{P_6}(2)$, contradicting the kernel-checked strict bounds.
A statement restricted to a different graph class is not refuted unless that
class contains this witness. The universal lower bound is a separate question.

## Evidence

The sole public theorem is
`D5.S3.Combinatorics.SpectralGraph.GuerreroVertexEnergyDegreeBounds.result`.
The axiom closure of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The auxiliary numerical experiment is in
[trureturing-experiments at commit `6a1a95527d8ae0d28202baf47e3a99b976a978bc`](https://github.com/the-omega-institute/trureturing-experiments/tree/6a1a95527d8ae0d28202baf47e3a99b976a978bc/docs/reports/guerrero-2022-vertex-energy-degree-bounds-remark-6).
From this worktree, the command
`python3 ../trureturing-experiments/docs/reports/guerrero-2022-vertex-energy-degree-bounds-remark-6/check.py`
exits 0 with `RESULT PASS`; `check.py` has SHA-256
`cc91b24d50779d983ea47cb7b43896bdf86231092e63ae72ffae57013a548328`.
The tested scope is precisely $t=1,2,3,4$, of orders $6,12,18,24$.
For each, the upper violations are exactly the $2t$ central vertices, with
$E=1.268286$ and $d_{\max}LE=1.247214$ at the displayed precision.
For $P_6$, the two closed expressions agree with the numerical diagonals to
$10^{-12}$; the computed comparison is
$1.268286021528>79/63=1.253968253968>5/4>1.247213595500$.
This experiment is corroboration, not the Lean proof or a uniform-family certificate.

## Triage

| Item | Status and evidence |
| --- | --- |
| Upper local degree bound at index $2$ of $P_6$ | **Proved (kernel-checked):** public `result`, using private `adjacency_lower`, `normalized_upper`, and `path_max` |
| Blow-up family $G_t$ for all $t\ge1$ | **Open** in this settlement; no uniform Lean theorem or tensor-identity proof is delivered |
| Symmetric central vertex, zero-based index $3$ | **Computed:** the experiment checks it at $t=1$ and all central copies for $t=2,3,4$; no Lean theorem at index $3$ |
| Universal conjectured lower bound | **Open:** refuting the upper conjunct does not decide the lower inequality |
| Finite blow-up checks | **Computed:** the experiment entry above, exactly $t=1,2,3,4$; no extrapolation to unbounded $t$ |
| Failure mechanism | **Proved in prose:** a global summed inequality alone cannot imply its vertexwise analogue, since `result` refutes that analogue while the source's global comparison is a separate literature result |
| Proof-shape boundary | **Classification:** `result` and its private proof steps are `bind-only`; named external settlement supplies admission, not an escape-witness claim |

### What the settlement shows

**Kernel-checked:** the upper local comparison fails already on a connected
path, without loops, multiple edges or isolated vertices. The exact normalized
energy and the strict separation at $5/4$ identify the failure at a diagonal
entry, rather than a change in the definition of either energy.

**Proved in prose:** for a positive-degree $d$-regular graph,
$D^{-1/2}=d^{-1/2}I$, hence $L-I=-A/d$. Spectral diagonalization gives
$|L-I|=|A|/d$, so $E_G(v)=dLE_G(v)$ at every vertex. Thus the comparison survives
as equality on this class; this argument is not an additional Lean theorem.
The refutation does not assert a general replacement inequality.

**Computed:** the finite blow-up checks show the same obstruction at orders
$6,12,18,24$ with minimum degrees $1,2,3,4$. The infinite-family tensor identities
remain outside this Lean settlement. The symmetric central vertex has the
finite numerical evidence stated above.

**Open:** the universal lower bound and a Lean proof of its survival at every
vertex of $P_6$ are not delivered. Neither is a classification of graphs
satisfying the local comparison.

The source's global trace comparison is not refuted. No conclusion about the validity of the paper's other theorems is asserted. Any use of the conjectured upper local
bound requires a separate hypothesis or replacement; the publisher edition's
use or revision of Remark 6 is unverified.

## ASSUMED-UNVERIFIED

Literature completeness and priority are unverified. The journal edition
may revise or omit Remark 6. Numerical evidence is restricted to the finite
scope stated above. No uniform blow-up result, universal lower-bound verdict,
or general replacement inequality is asserted.
