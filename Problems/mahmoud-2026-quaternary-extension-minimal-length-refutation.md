---
slug: mahmoud-2026-quaternary-extension-minimal-length-refutation
bibkey: mahmoud2026macwilliams
doi: 10.48550/arXiv.2607.26214
url: https://arxiv.org/abs/2607.26214v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.result
---

# Five is not the minimal quaternary extension-counterexample length

## Problem

A. A. Mahmoud, *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*, arXiv:2607.26214v1 (2026), §6.2, open problem 2, states:

> \textbf{Minimal length for general $q$.} Determine the minimal counterexample length for general $q$. For $q=2$ it is $3=q+1$ (Theorem~\ref{thm:census}); we expect $q+1$ to be minimal in general, in the light of the threshold results for additive isometries in \cite{Dyshko16,DyshkoGeom}, but we claim it only for $q=2$.

This is a verbatim excerpt of `MzWi_Ext_Th.tex`, line 429, retrieved from the versioned arXiv source; its md5 is `ee3d0a4f9ba273634eb55aad8ed7b850`. The rest of the item asks separately about full-support minimal lengths. The definitions and source locators are also in [the literature note](../Library/Quantum/mahmoud2026macwilliams.md).

The source's Definition 2.3 (TeX lines 237–239) is:

> Fix $q$ and $n$. We say the quantum extension property $\mathrm{QEP}(q,n)$ holds if for every pair $C,D\le\A_q^n$ of trace-symplectically self-orthogonal additive codes and every additive bijection $f\colon C\to D$ with $\wt(f(u))=\wt(u)$ for all $u\in C$, the map $f$ extends to a monomial transformation of $\A_q^n$.

Here $A_q=\mathbb F_q^2$, and additive means $\mathbb F_p$-linear, where $p$ is the characteristic (TeX lines 211–217). Definition 2.1 (lines 221–223) specifies a coordinate permutation followed by maps in $\operatorname{Sp}(2,q)$, and explicitly mentions the larger group of all coordinatewise $\mathbb F_p$-linear automorphisms.

Issue [#20851](https://github.com/the-omega-institute/trureturing/issues/20851) fixes both readings at $q=4$. Write $\mathrm{QEP}(4,n)$ for the specified symplectic coordinate group and $\mathrm{QEP}^{\mathrm{add}}(4,n)$ for the larger additive coordinate group. The formal `claim` is

$\operatorname{IsLeast}\{n\in\mathbb N:1\le n\ \land\ \neg\mathrm{QEP}(4,n)\}\,5\ \lor\ \operatorname{IsLeast}\{n\in\mathbb N:1\le n\ \land\ \neg\mathrm{QEP}^{\mathrm{add}}(4,n)\}\,5.$

`IsLeast` requires both membership in the failure set and being no larger than any member. This disjunction is refuted: neither reading has least positive failure length $5$.

## Motivation

The expected length $q+1$ would make the source's family a minimal obstruction for every prime-power qudit dimension. For non-prime $q$, the codes and isometries are only required to be linear over the prime field, while the specified symplectic coordinate maps are linear over $\mathbb F_q$. Distinguishing these requirements is necessary to identify the actual obstruction and its length.

## Gap

The bounded literature check recorded in #20851 reports:

- the arXiv abstract page lists only v1; the retrieved abstract page and TeX retain the expectation;
- OpenAlex work `W7171833798` has zero citing works (orchestrator reading), and Semantic Scholar has zero citations (search-seat reading);
- arXiv:2610.09900, 2610.04694 and 2610.03429 do not mention the expectation; MathDB and `google-deepmind/formal-conjectures` have no entry (search-seat readings);
- S. Dyshko, *On extendability of additive code isometries* (2016), arXiv:1406.1714v2, Example 3, supplies the length-$|K|+1$ construction for a base field $K$ (orchestrator reading). No located source applies $K=\mathbb F_2$ to settle this quaternary stabilizer expectation;
- issue #11210 addresses the source's Question 5.4, a different question; the preregistration reports no existing repository settlement of open problem 2.

`not-found-in-searched-scope`. The external citation and antecedent readings are attributed reports, with reproduction limits listed below.

## Route

Let $F=\mathbb F_4$ and choose $\omega\in F\setminus\{0,1\}$. The module uses $\operatorname{tr}(x)=x+x^2$ and

$\langle u,v\rangle=\operatorname{tr}\bigl(\sum_i(u_{i,1}v_{i,2}-v_{i,1}u_{i,2})\bigr).$

1. **One coordinate.** For $a,b\in\mathbb F_2$, parameterize $C_1$ by $(a+b\omega,0)$ and $D_1$ by $(a,b)$, and match equal parameters. Both parameterizations are additive and injective. The pairing vanishes on $C_1$; on $D_1$ its argument lies in $\mathbb F_2$, whose trace is zero. Every nonzero word on either side has weight $1$. An extending $F$-linear map would send $(1,0)$ to $(1,0)$ and hence $(\omega,0)$ to $(\omega,0)$, whereas the prescribed image is $(0,1)$. No determinant-one matrix can extend this map.
2. **Three coordinates.** For $a,b\in\mathbb F_2$, put

   $C(a,b)=((a,b\omega),(a,b\omega),(0,0)),\qquad D(a,b)=((a+b,0),(a,0),(b,0)).$

   Match equal parameters. Both parameterizations are additive and injective. The first two pairing contributions for $C$ cancel in characteristic $2$; each pairing contribution for $D$ is zero. Every nonzero word on both sides has weight $2$. The third coordinate of $C$ vanishes identically, while no coordinate of $D$ does. Coordinatewise additive automorphisms fix zero, so a coordinate permutation and such automorphisms cannot map $C$ onto $D$.
3. **Leastness.** The private helpers establish $\neg\mathrm{QEP}(4,1)$ and $\neg\mathrm{QEP}^{\mathrm{add}}(4,3)$. Leastness at $5$ would respectively imply $5\le1$ or $5\le3$. The public `result` negates the disjunction of these leastness assertions.

## Falsifier

The refutation would miss the expectation if its codes, pairing, weight or extension groups differed from the source. The module uses:

- `K 1`, defined as `GaloisField 2 (1 + 1)`, and `HilbertPhase (K 1)`, the product $F\times F$;
- additive subgroups of length-$n$ label vectors, rather than $F$-linear subspaces; in characteristic $2$, these are exactly $\mathbb F_2$-linear subspaces;
- the displayed trace-symplectic pairing and `hammingNorm`, which counts nonzero coordinates. The trace is represented in $F$, with the prime-field values embedded there, so its zero condition is the source's zero condition;
- `QEP`, with a permutation and determinant-one $2\times2$ matrices over $F$, acting on labels at the inverse-permuted coordinates; in dimension two these matrices are $\operatorname{Sp}(2,4)=\operatorname{SL}(2,4)$;
- `QEPAdd`, with arbitrary additive equivalences of the whole label alphabet at each coordinate, and no additional pairing-preservation condition on those equivalences.

The positive-length restriction is explicit. The claim uses `IsLeast`, not an infimum with an unproved existence or boundedness premise. Neither the physical implementation of a coordinate group nor local-unitary equivalence of codespaces is part of `claim`.

## Evidence

The canonical source is `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.lean` (388 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.lean.json`, statement `sha256:faadee2243483161ec80d926392c99becd028ca6e4605e025e795eb4a61c16bc`.

Declaration statements:

- `result`: `sha256:35cd8cad48ddfa184de1f9ba5939c2d345571b6d08d7e86f368777464c7492e7`;
- `claim`: `sha256:5d9939b2756c32d7c8e995ba7339131ff188f9e22a37f7403fa7b6b340ad61c6`.

## Triage

Tier 1 expectation in a 2026 paper, preregistered in issue #20851 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** over the quaternary label alphabet, it is false that either $5$ is the least positive length at which `QEP` fails or $5$ is the least positive length at which `QEPAdd` fails. Equivalently, both leastness assertions are false. This type does not specify an exact minimum for either group.

**Established inside the module** (on the proof path of `result`, not conclusions of it): the binary trace cases $\operatorname{tr}(0)=\operatorname{tr}(1)=0$, the additivity and injectivity of the four code parameterizations, the vanishing of every trace-symplectic pairing, the weights $(0,1,1,1)$ on both length-one codes and $(0,2,2,2)$ on both length-three codes, and the identically zero third coordinate of the first length-three code.

**Hand computation from the definitions, not formalized:** the relation $\omega^2=\omega+1$ gives $\operatorname{tr}(\omega)=\operatorname{tr}(1+\omega)=1$. Also, $|\mathrm{SL}(2,4)|=60$, and none of these matrices extends the length-one map, by the determinant-free argument of the proof (an $\mathbb F_4$-linear map sends $(\omega,0)$ to $\omega$ times the image of $(1,0)$). An additive automorphism of $\mathbb F_4^2\cong\mathbb F_2^4$ extending the same map is determined by the images of a complement basis of the source code, which must be independent modulo the target code: $(16-4)(16-8)=96$ of the $|\mathrm{GL}(4,2)|=20\,160$ automorphisms extend it.

**Argued, not formalized.**

- *The two obstructions are different.* At length one, additivity and weight preservation do not supply $F$-scalar compatibility. Enlarging the coordinate group removes this particular obstruction: any additive isomorphism between subspaces of the four-dimensional $\mathbb F_2$-space $F^2$ extends to an automorphism by completing a basis of each subspace to a basis of the ambient space and matching the added basis vectors. Thus the larger-group extension property at length one follows by this basis argument, independently of self-orthogonality. For the displayed map an explicit extension is $(a+b\omega,c+d\omega)\mapsto(a+c\omega,b+d\omega)$ for binary $a,b,c,d$; this additive map is its own inverse.
- *Minimum for the specified group.* The length-one witness supplies a positive failure, and every positive natural number is at least $1$, so the least positive failure length for that group is $1$. This leastness argument is not a separately stated theorem in the module.
- *Weight loses coordinate information.* At length three, the kernels of the nonzero-coordinate tests change while their total counts agree. On the binary message space the three functionals $a+b,a,b$ have three different one-dimensional kernels, so each nonzero message is zero in exactly one of them. This reproduces weight $2$ without reproducing the identically zero coordinate of $C$. Additive coordinate automorphisms cannot repair that loss: they preserve whether a coordinate is identically zero, and permutations preserve the number of such coordinates.
- *Nearby restrictions.* Requiring the length-one isometry to be $F$-linear excludes that witness; requiring full support on both length-three codes excludes the other witness. These exclusions do not establish a general extension theorem under either restriction. The length-one pair itself has full support, so full support alone does not rescue the specified symplectic-group expectation at $q=4$. The exact larger-group minimum, including the length-two case, is not determined by `result`.
- *Effect on the source.* Theorem 3.3 supplies counterexamples at length $q+1$; its construction and proof (TeX lines 269–310) do not require minimality. Existence at that length is compatible with shorter counterexamples, so this settlement removes the general minimality expectation without contradicting that existence assertion. The source's minimality theorem is explicitly restricted to $q=2$ (Theorem 4.1, lines 338–346), which is not the field treated here. No theorem in the checked source uses the general-$q$ expectation as a hypothesis. The separate questions on full-support lengths and distance restrictions receive no general resolution from this module, and `result` makes no codespace-level local-unitary claim.

## ASSUMED-UNVERIFIED

The bounded literature check in #20851 does not establish exhaustive worldwide novelty or priority. The source TeX, expectation, definitions and versioned abstract page are directly checked. The OpenAlex citation count, the search-seat Semantic Scholar count, the readings of arXiv:2610.09900, 2610.04694 and 2610.03429, the MathDB and formal-conjectures searches, the repository-wide absence search and the orchestrator's reading of Dyshko's Example 3 are not independently reproduced here. The source's qubit census and its supplementary verification programs are not rerun.

The hand computation and the arguments labelled above are not additional Lean declarations. In particular, the larger-group length-one basis-extension argument, an exact larger-group minimum, repaired general extension theorems, other field sizes, distance conditions, and physical local-unitary conclusions are not formalized by `result`.
