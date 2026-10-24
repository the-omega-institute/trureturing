---
slug: kirkland-2019-interior-pst-converse-refutation
bibkey: kirkland2019rationalweightspst
doi: 10.1080/03081087.2018.1442810
url: https://arxiv.org/abs/1708.03283v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.result
---

# Interior perfect state transfer without endpoint transfer

## Problem

S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang, *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*, arXiv:1708.03283v2 (Linear and Multilinear Algebra 67, 2019), study perfect state transfer (PST) on weighted paths with real edge weights and real diagonal potentials. Their Proposition `prop:internal` states (source TeX `main.tex`, lines 309–312):

> For a weighted path with or without potentials, PST between vertices $1$ and $n$ implies PST between vertices $j$ and $n+1-j$, for each $j=2, \ldots, n-1$. If for some $j$ with $2 \le j \le n-1$ there is PST between vertices $j$ and $n+1-j$, and if in addition none of the eigenvectors of the Hamiltonian has a zero entry in the $j$--th position, then the converse holds.

The question immediately following it is (source TeX `main.tex`, line 315):

> It is an open question if the converse holds even if there are eigenvectors with zeros in the jth place.

The formal reading settled here uses the repository's vertices $0,\ldots,m$. For every $m : \mathbb N$ with $3 \le m$, every $r : \mathrm{Fin}\,m \to \mathbb R$ with $0 < r(k)$ for every $k$, every $q : \mathrm{Fin}(m+1) \to \mathbb R$, and every $j : \mathrm{Fin}(m+1)$ satisfying
$1 \le j.val$, $j.val \le m-1$, and $j.val \ne m-j.val$, it asserts

$$
\left(\exists t : \mathbb R,\ 0<t \land \operatorname{HasPST}(\operatorname{pathHamiltonian}(r,q),t,j,\operatorname{Fin.rev}(j))\right)
\;\Longrightarrow\;
\left(\exists s : \mathbb R,\ 0<s \land \operatorname{HasPST}(\operatorname{pathHamiltonian}(r,q),s,0,\operatorname{Fin.last}(m))\right).
$$

Here `HasPST H t a b` is exactly the compiled predicate that the squared modulus of the corresponding matrix-exponential entry is one. The theorem `result` settles the negation of this universal proposition.

## Motivation

The source's forward implication explains why endpoint PST produces mirror interior transfer, while the conditional converse would let interior transfer certify endpoint transfer when every eigenvector is nonzero at the chosen interior vertex. Removing that support hypothesis would make interior transfer a much stronger diagnostic for paths with potentials. The settlement tests that proposed extension on the smallest explicit path in the module: $m=4$, hence five vertices, with no potentials.

## Gap

The bounded check recorded in preregistration issue [#21056](https://github.com/the-omega-institute/trureturing/issues/21056) reports:

- the Kirkland et al. v2 TeX and R. Bailey's arXiv:2412.16351v1 retain the question as open;
- the cited-work searches reported in the issue found no settlement, and MathDB and `google-deepmind/formal-conjectures` had no entry;
- web searches reported the two source papers and related PST work, while the source separately notes that the analogous PGST converse fails;
- the repository search reported no earlier issue, module, or `Problems/` record for this converse.

The issue labels this bounded result `not-found-in-searched-scope`.

## Route

Let $H$ be the module's private `pathHamiltonian weights 0`, with
$\mathrm{weights}=(2\sqrt 2,\sqrt 5,\sqrt 5,2\sqrt 2)$, and let
$\tau=2\pi/(2\sqrt 2)$.

1. `weights_pos` proves $\forall k,\ 0<\mathrm{weights}(k)$ by checking all four finite cases. `hamiltonian_entries` identifies $H$ with the displayed five-by-five real symmetric tridiagonal matrix whose outer off-diagonal entries are $2\sqrt2$ and whose inner off-diagonal entries are $\sqrt5$.
2. `spectral_data` proves the conjunction
   $H *ᵥ v_0=0\,\bullet v_0$,
   $H *ᵥ u(1)=(2\sqrt2)\,\bullet u(1)$,
   $H *ᵥ u(-1)=(-2\sqrt2)\,\bullet u(-1)$,
   $H *ᵥ w(1)=(3\sqrt2)\,\bullet w(1)$, and
   $H *ᵥ w(-1)=(-3\sqrt2)\,\bullet w(-1)$, for the exact vectors defined in the module. `eigen_exp` then states, under the explicit hypothesis $H *ᵥ v=E\,\bullet v$, that
   $\exp(((s:\mathbb C)I)\,\bullet H)*ᵥv=\exp((s:\mathbb C)I E)\,\bullet v$.
3. `interior_decomposition` proves the two exact decompositions of the coordinate vectors at vertices $1$ and $3$ into $u(1),u(-1),w(1),w(-1)$. `phases` proves at $\tau$ that the phases for $\pm2\sqrt2$ are $1$ and the phases for $\pm3\sqrt2$ are $-1$. Combining these with `eigen_exp` and the decompositions, `interior_transfer` proves
   $\exists t : \mathbb R,\ 0<t\land\operatorname{HasPST}(H,t,1,3)$.
4. For a hypothetical endpoint transfer, `endpoint_column` assumes exactly $s:\mathbb R$ and `hpst : HasPST H s 0 4` and proves for every $x : \mathrm{Fin}\,5$ that the column indexed by vertex 4 of the propagator is its row-zero entry when $x=0$ and is zero otherwise. Under the same `hpst` premise, `endpoint_eigen_phase` additionally assumes an eigenvector equation $H *ᵥ v=E\,\bullet v$ and proves
   $$exp((s:\mathbb C)I E)\,v(4)=\operatorname{exp}(((s:\mathbb C)I)\,\bullet H)\,0\,4\,v(0).$$
5. `no_endpoint_transfer` proves $\forall s:\mathbb R,\ \neg\operatorname{HasPST}(H,s,0,4)$. Applying `endpoint_eigen_phase` to $v_0$ forces the endpoint phase $\gamma$ to be $1$ because the two endpoint entries of $v_0$ are both $-\sqrt5$ and nonzero. Applying it to $u(1)$ forces $\exp((s:\mathbb C)I(2\sqrt2))=-1$, while applying it to $w(1)$ forces $\exp((s:\mathbb C)I(3\sqrt2))=1$. The proof invokes `exists_int_of_exp_eq_neg_one` for the first equation and `exists_int_of_exp_eq_one` for the second, giving integers $k,l$ with
   $s(2\sqrt2)/\pi=2k+1$ and $s(3\sqrt2)/\pi=2l$; their equality after multiplying by $3$ and $2$ becomes $6k+3=4l$, which `omega` rejects by parity.
6. `result` instantiates `claim` at $m=4$, the positive `weights`, zero potential, and $j=1$. The three vertex inequalities are discharged by `decide`, and the interior premise is `interior_transfer`; the resulting endpoint conclusion contradicts `no_endpoint_transfer`.

## Falsifier

The formal refutation would not address the source question if the formal predicate or indexing changed the statement. The module uses the frozen `pathHamiltonian r q` on vertices $0,\ldots,m$, with $r$ on the $m$ edges and arbitrary real $q$ on the $m+1$ vertices. Its `HasPST` is the squared-modulus condition for the matrix exponential, and the endpoint time $s$ is allowed to differ from the interior time $t$. At $m=4$, `Fin.rev 1` is vertex $3$, `Fin.last 4` is vertex $4$, and the witness has exactly the positive weights above and the zero potential. The module proves interior PST for this witness and proves the stronger statement that endpoint PST is absent at every real time. The zero-eigenvalue vector $v_0=(-\sqrt5,0,2\sqrt2,0,-\sqrt5)$ also verifies that the witness lies in the source's case with an eigenvector zero at the chosen interior vertex.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.lean` (237 lines).
Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.lean.json`, statement `sha256:2fafba2b83bb5e4a641eb88b6815903b93e2b2a9c5c4a7e4a7f4b8fe53892f3e`.
Declaration statements:
- `result`: `sha256:23d1fb572bff02e30e3fc97d9cce517c103d9db78eeee852ba8f79682bd85b52`;
- `claim`: `sha256:cd07c7fe1582c8ce2785f7ed42cffa5b714813555f6322056ba64a46e58afffc`.
- **Proof.** It proves `result : ¬ claim` by applying the quantified `claim` to the explicit five-vertex instance and contradicting `no_endpoint_transfer`.
- **Axioms.** A scratch import followed by `#print axioms D5.S3.Quantum.Dynamics.InteriorPathTransferConverseRefutation.result` reports only `propext`, `Classical.choice`, and `Quot.sound`; `grep -n "sorry\|native_decide\|^axiom" D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.lean` produced no matches, so there is no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1: an explicit open question in the 2019 paper, restated as open in the 2024 paper, preregistered in issue #21056 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none: designated refutation result, exempt from the §3.9 registration | open-problem-resolution |
| `claim`, the witness definitions, and the private spectral and transfer lemmas | bind-only | none: definitions and helpers are consumed by `claim` or the proof of `result` | open-problem-resolution |

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** `result` has type $\neg\,\mathrm{claim}$. Thus the universal implication stated in `claim` is false: it is not the case that every quantified positive-weight path and admissible interior mirror pair with PST must have endpoint PST at some positive time.

**Argued, not formalized.**

- *Failure mechanism.* The vector $v_0$ is a zero-eigenvalue mode with zero entry at the selected interior vertex. Consequently, the interior transfer phase calculation does not impose a condition from that mode. Its nonzero equal endpoint entries instead force the endpoint phase to be $1$. The $\pm2\sqrt2$ modes then require phase $-1$, while the $\pm3\sqrt2$ mode requires phase $1$; the ratio of these energies turns the two exponential conditions into the impossible odd-even equation $6k+3=4l$.
- *Missing structure.* The source's converse includes the hypothesis that no eigenvector vanishes at the selected interior vertex. The witness violates exactly that hypothesis. A converse under another support or spectral hypothesis, or a converse for a restricted family of paths, is not supplied by this settlement and remains open.
- *Nearby statements.* The source's endpoint-to-interior implication and its converse with the nonvanishing-eigenvector hypothesis are not refuted by this example. The source's separate observation about PGST is not a statement proved by this module. The rational-weights results in the same paper concern a different endpoint-PST question and are unaffected.
- *Effect on dependent claims.* Any argument using the unrestricted interior-to-endpoint converse must retain the nonvanishing hypothesis or impose a new restriction; the unrestricted converse is false and cannot be used as a general theorem. No other source statement is thereby characterized by this module.

## ASSUMED-UNVERIFIED

The literature search is bounded by the sources and search routes reported in issue #21056; it does not establish exhaustive worldwide novelty, priority, or the absence of an unpublished counterexample. The Kirkland et al. source TeX was fetched and read here, but Bailey's paper, the cited-work texts, and the search-seat reports were not independently reproduced in this seat. The explanatory mechanism, the consequences for neighboring source statements, and all claims about PGST or possible replacement hypotheses are not separate formalized declarations.
