---
slug: davies-marigliano-2021-circulant-orbit-eigenvalue-conjecture
bibkey: daviesmarigliano2021symmetries
doi: null
url: https://arxiv.org/abs/2012.01905v5
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.result
---

# A circulant counterexample to Davies–Marigliano Conjecture 4.4

## Problem

Isobel Davies and Orlando Marigliano, *Coloured Graphical Models and their Symmetries*, arXiv:2012.01905v5, Section 4, Conjecture 4.4, PDF page 11:

> If $G$ is an uncoloured circulant graph, then the number of orbits of the action of $\operatorname{Aut}(G)$ on the set $V*V$ of unordered pairs of vertices of $G$ coincides with the number of distinct eigenvalues of its adjacency matrix.

The preceding definition says: “By definition, these are graphs that have a symmetry which is a cyclic permutation of its vertices.” Corollary 3.3, page 7, uses the entrywise action of the full automorphism group; its count $\binom{n+1}{2}$ includes diagonal pairs. The source's adjacency matrix is the real symmetric zero-one matrix of the simple undirected graph. Preregistration: [#21260](https://github.com/the-omega-institute/trureturing/issues/21260).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every uncoloured simple undirected graph of positive order | `claim` quantifies over every natural number and every `SimpleGraph (Fin n)`; positivity is part of `IsCirculant` | No connectivity assumption is added |
| A symmetry which is a cyclic permutation of all vertices | `IsCirculant` uses a graph self-isomorphism whose permutation is `Equiv.Perm.IsCycleOn` on `Set.univ` | The whole vertex set is used |
| Unordered pairs, including repetitions | `pairOrbits` uses `Sym2 (Fin n)` | Diagonal pairs remain |
| Entrywise action of the full automorphism group | Each orbit is the range of `Sym2.map` over every graph self-isomorphism; the outer range collects distinct orbit sets | No subgroup substitution |
| Number of distinct adjacency eigenvalues | `eigenvalueCount` counts `Module.End.Eigenvalues` of the real adjacency endomorphism with `Nat.card` | Scalar values are counted without multiplicity |
| Equality for every circulant | `claim`; `result` proves its negation | No source clause is dropped |

The public definitions retain the literal preregistered expressions. Proofs use Mathlib's common-neighbour and circulant-matrix constructions directly, with the finite adjacency correspondence established in `intMatrix_adj`.

## Motivation

The settling declaration is `D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.result`. The finite graph joins residues modulo $2$, $3$ and $5$ that disagree in exactly one coordinate. It is the thirty-vertex Cartesian product $K_2\square K_3\square K_5$ under the residue-coordinate bijection.

## Gap

A cyclic symmetry does not force full-automorphism pair-orbit counts to equal the number of distinct adjacency eigenvalues. Distinct coordinate disagreement patterns can remain different orbits while different tensor summands share an eigenvalue.

## Route

Translation by one is a cyclic graph symmetry. Edges of the three coordinate types have respectively $0$, $1$ and $3$ common neighbours. These intrinsic counts are invariant under every graph automorphism. Paths using the other two types recover equality of each coordinate, so automorphisms preserve all three coordinate equality relations. Eight representative disagreement patterns therefore lie in distinct unordered-pair orbits.

An exact integer circulant certificate gives the annihilating polynomial

$$p(X)=X(X-7)(X-5)(X-4)(X-2)(X+1)(X+3).$$

Transport to the real adjacency endomorphism and evaluation on an eigenvector put every eigenvalue in $\{-3,-1,0,2,4,5,7\}$. Thus the proof needs only $s\geq8$ and $r\leq7$, which contradict the asserted equality.

## Falsifier

A failure of circulancy, a collapse of the eight representative orbits under a full graph automorphism, or a failure of the exact annihilator identity would invalidate this witness. These obligations are checked on the proof path to `result`. The formal assertion keeps diagonal pairs and the full automorphism group.

## Evidence

The module's single public theorem `result` proves the negation of `claim`. Its private proof path contains `base_circulant`, `mod_map`, `pairTag_map`, `orbit_lower`, `annihilator_int`, `annihilator_zero`, `eigenvalue_mem` and `eigenvalue_upper`. Exact orbit and spectral counts below are experimental claims, distinct from the formal bounds.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact finite experiment

[Experiment directory at immutable revision `bc7eba4d10d7a9ada06fcabe82de3d2bae5ee2f4`](https://github.com/the-omega-institute/trureturing-experiments/tree/bc7eba4d10d7a9ada06fcabe82de3d2bae5ee2f4/docs/reports/davies-marigliano-2021-circulant-orbit-eigenvalue-conjecture).

The script is `docs/reports/davies-marigliano-2021-circulant-orbit-eigenvalue-conjecture/check.py`; SHA-256: `97dbbc1e143d34eab4bd06fb441e38cb19bd71202ccc50c09af55d0ff9b73c2d`. The pinned script is present at this revision and has the SHA-256 above. Execution: `PYTHONPATH=/tmp/op-dm2012/python-libs python3 /Users/auric/.sshx/dde998da336feb3ad2786907/attempt-1/check.py`, exit 0, final assertion `ALL_CHECKS_OK`; NetworkX 3.7 and SymPy 1.14.0. Arithmetic is integral or exact polynomial algebra.

The checker exhaustively enumerates full graph automorphisms only for cycles of orders $3$ through $10$ and the thirty-vertex base. Direct characteristic-polynomial checks also cover the $70$- and $126$-vertex examples. The family and appended-prime outputs are finite subset-sum formula checks, not exhaustive automorphism enumeration outside the base.

## Triage

### What the settlement shows

1. **Computed — surviving cycles.** For every $3\leq n\leq10$, the checker obtains $s(C_n)=r(C_n)=\lfloor n/2\rfloor+1$. At $n=6$ there are four orbits and the spectrum is $2,1,-1,-2$ with multiplicities $1,2,2,1$. Evidence: the pinned experiment entry above.
2. **Proved — universal failure.** `result`, using `base_circulant`, `orbit_lower` and `eigenvalue_upper`, refutes the universal claim at $30$ vertices with diagonal pairs and full graph automorphisms retained. Evidence: kernel-checked declaration `D5.S3.Combinatorics.Hamming.DaviesMariglianoCirculantOrbits.result` and its private dependencies.
3. **Proved — intrinsic separation.** `mod_map` preserves the three residue equality relations under every automorphism; `pairTag_map` preserves the unordered-pair disagreement tag. `orbit_lower` obtains eight distinct representative orbits. Evidence: these kernel-checked private declarations on `result`'s proof path.
4. **Proved — spectral bound.** `annihilator_int` and `annihilator_zero` establish $p(A)=0$ for the integer matrix and real adjacency endomorphism. `eigenvalue_mem` and `eigenvalue_upper` give at most seven distinct real eigenvalues. Evidence: these kernel-checked private declarations on `result`'s proof path.
5. **Computed — exact base counts and resonance.** The base has $1{,}440$ full graph automorphisms and exactly eight unordered-pair orbits of sizes $15,30,30,30,60,60,120,120$. Its characteristic polynomial is $x^4(x-7)(x-5)(x-4)^2(x-2)^6(x+1)^8(x+3)^8$, giving exactly seven distinct eigenvalues. The subset-sum equality $2+3=5$ merges two indexed tensor values. Evidence: the pinned exact experiment; these exact counts are not asserted as separate Lean theorems.
6. **Computed — finite extensions.** Direct graph, cyclic-symmetry and characteristic-polynomial checks cover $b=3,5,7$ in $K_2\square K_b\square K_{b+2}$. All $50$ odd values $3\leq b\leq101$ have seven distinct subset sums. The five checked factor lists are $(2,3,5)$, $(2,3,5,11)$, $(2,3,5,11,23)$, $(2,3,5,11,23,47)$ and $(2,3,5,11,23,47,97)$, with $7,14,28,56,112$ distinct subset sums. The corresponding $8,16,32,64,128$ orbit counts are formula outputs outside the exhaustively enumerated base. Evidence: the pinned experiment and its exact tested scope above.
7. **Open — general families.** The infinite odd-$b$ family, equality if and only if distinct subset sums for general distinct complete factors, and the unbounded-gap extension are not kernel-formalized in this delivery. Finite formula checks do not establish their infinite quantifiers.
8. **Open — other source questions.** This delivery proves no statement about all prime-order circulants or the separate coloured-cycle conjecture. The source's positive families remain separate results; the computed cycle examples survive. Literature completeness is `ASSUMED-UNVERIFIED`.

The failure mechanism is spectral resonance without fusion of intrinsic pair types. **Proved in prose, conditional on the source's dimension formulas:** put $N=\binom{31}{2}$. The full linear relation space has dimension $N-r$ and the symmetry-induced subspace has dimension $N-s$, so their quotient has dimension $(N-r)-(N-s)=s-r=8-7=1$, using the computed counts. This is not a separate kernel theorem here. No binomial form for that relation is asserted. Arguments whose only justification is the conjecture's universal equality lose that justification; the source's independently proved positive families are unaffected.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain `ASSUMED-UNVERIFIED`, as disclosed in #21260. The Beezer originals *A disrespectful polynomial* (1990), *Orbit polynomial graphs of prime order* (1987) and *Trivalent orbit polynomial graphs* (1986) were not obtained in full. Their author abstracts and the inspected secondary literature establish neither absence nor presence of this precise counterexample. The target arXiv v5 source was read in the preregistration; its equivalence to the journal text and the cited journal DOI `10.4418/2021.76.2.13` remains unverified. No global novelty claim is made.
