---
bibkey: designolle2023symmetricbell
authors: Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta
year: 2023
title: "Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms"
doi: 10.1103/PhysRevA.109.022205
url: https://arxiv.org/abs/2310.20677v3
claim: "Section V conjectures that the symmetrised local polytope is affinely equivalent to the cross-polytope in dimension ceil(m/2)."
strata_touched:
  - D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope
  - D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1103/PhysRevA.109.022205

Source: https://arxiv.org/abs/2310.20677v3

Journal: Physical Review A 109, 022205 (2024).

## Source statement

Section V, PDF p. 4, states:

> For all these examples, the number of facets is equal to $2^{\lceil m/2\rceil}$. This seems to indicate that the symmetric polytope is affinely equivalent to the cross-polytope in dimension $\lceil m/2\rceil$. Although we considered the orbits giving rise to the extreme points of this polytope and tried to infer a generalisable pattern, we could not establish this fact. We conjecture, however, that it holds in general, and hope that further research will identify these general extreme points.

The deterministic strategies and their local polytope are defined in
Eqs. (1)–(2):

$$
d^{\vec a^{(1)}\ldots\vec a^{(N)}}_{x_1\ldots x_N}
\coloneqq\prod_{n=1}^N a^{(n)}_{x_n},\qquad
\mathcal L_N^{(m)}\coloneqq\mathrm{conv}\{\mathbf d^{\vec a^{(1)}\ldots\vec a^{(N)}}\}.
$$

Equation (23) gives the four signed permutation generators: swap the first
two parties, cycle the parties, shift their first two input indices in
opposite directions, and reflect every input index. The antiperiodic rule
supplies the signs. Equation (27) defines the Reynolds operator:

$$
\Gamma(\mathbf p)\coloneqq\frac{1}{|G|}\sum_{g\in G}g\cdot\mathbf p.
$$

Equation (28) describes its fixed subspace by the signed residue of the
total input index and reflection about half the number of inputs. Table II
counts distinct projected deterministic tensors; its entries do not count
only extreme points of their convex hull.

## Encoding and result

Inputs are read as $0,\ldots,m-1$, with $e_{x+m}=-e_x$. Integer quotient and
remainder use floor division and nonnegative remainder. The Lean definition
`Gamma` uses orthogonal projection onto the common fixed subspace, the
convention specified in issue #15186. Equality to the finite-group Reynolds
average is not a separately kernel-checked theorem in these modules.

The conjecture is refuted at $N=3$, $m=17$. Nine single-frequency strategies
and their negatives remain uniquely exposed vertices. Writing $q_r = 289\,(\Gamma\,3\,17\,d)_{[r,0,0]}$, a mixed strategy has the displayed
scaled coordinates $(-141,133,-109,69,-13,-43,91,-123,139)$. In these scaled
coordinates it is separated from their convex hull by $(-15,27,-21,8,59,24,-5,-6,10)$: the respective values
are $8421$ and at most $8417$. Consequently there are at least nineteen
extreme points, exceeding the eighteen possible in a nine-dimensional
cross-polytope. The source's other Bell inequalities and computational
results are not consequences of this refutation alone.

## Computed neighbours and open questions

The experiment entry
`docs/reports/designolle-vertesi-pokutta-2023-symmetric-polytope-cross-polytope/check.py`
in `the-omega-institute/trureturing-experiments`, revision
`7ee14723c2f0ce18f299a0f9870eb3d5330ee9e9`, has SHA-256
`9cda6109955a66f89d7510741043b065bc600caf20e96a717b7f0dbd87dab998`.
Its reported command is `python3 check.py`, exit 0, final line `bad= 0`.
These are computations, separate from the Lean theorem: for odd
$m=5,\ldots,13$ at $N=3$ the projected polytope is the indicated
cross-polytope; Table II's $N=3$, $m=3,\ldots,9$ counts are
$10,10,60,100,640,1540,10032$.

The first failing number of inputs at $N=3$ is open here: $m=14,15,16$ have
not been computed. Other numbers of parties and the source's remark that
symmetric facets are full local-polytope facets for odd $N$ and even $m$
remain open here.
