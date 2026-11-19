---
slug: nguyen-tan-2025-unitary-cayley-prime-zero-eigenvalue
bibkey: nguyentan2025supercharacters
doi: 10.48550/arXiv.2508.10348
url: https://arxiv.org/abs/2508.10348v1
triage: theorem
motivation_gids:
  - D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.result
---

# Nguyen–Tân Question 4.17

## Problem

Nguyen and Tân, *Supercharacters of finite abelian groups and applications to spectra of U-unitary Cayley graphs*, arXiv:2508.10348v1, Section 4.3, Question 4.17, page 19, ask:

> Suppose that Γ(R, U) is both connected and anti-connected. Is it true that Γ(R, U) is prime if and only if 0 is not an eigenvalue?

Here $R$ is a finite commutative Frobenius ring, $U\le R^\times$ contains $-1$, and anti-connected means that the graph complement is connected. A prime graph has no homogeneous set of cardinality between $2$ and $|R|-1$.

### Statement echo

| Source condition | Lean counterpart | Scope |
| --- | --- | --- |
| Finite commutative ring | `R : Type`, `CommRing R`, `Fintype R` in `claim` | The universal source domain. |
| Frobenius functional | `IsFrobenius R` | An additive functional into `ZMod n`, annihilation by $n$, and no nonzero ideal in its kernel. Additivity supplies the required $\mathbb Z/n$-linearity. |
| Unit subgroup containing minus one | `U : Subgroup Rˣ`, `-1 ∈ U` | The source hypothesis is retained. |
| Cayley adjacency | `unitaryCayley R U` | The literal preregistered `SimpleGraph.fromRel` expression; the private `unitary_cayley_as_add_cayley` bridge uses `SimpleGraph.addCayley`. Loops are removed, including degenerate zero-ring cases. |
| Connected and anti-connected | The graph's `Connected` predicate and its complement's `Connected` predicate | Both source hypotheses occur. |
| Prime | `IsPrimeGraph` and `IsHomogeneousSet` | The literal homogeneous-set condition. Finsets exhaust subsets of a finite vertex type. |
| Zero adjacency eigenvalue | `HasZeroEigenvalue` | A nonzero complex vector in the adjacency kernel; the private `zeroEigenvalue_iff` gives the spectral interface. |
| Affirmative equivalence | `claim` | The closed universal proposition. |
| Negative answer | `result : ¬ claim` | Refuted; no source hypothesis is discarded. |

## Motivation

The frozen settling declaration is `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.result`. Preregistration: [#20113](https://github.com/the-omega-institute/trureturing/issues/20113). The module has generality `I`, utility `none`, and admission basis `open-problem-resolution (#20113; Refuted)`.

## Gap

Primeness constrains homogeneous sets; it does not exclude cancellation of adjacency characters. The counterexamples separate these two properties. The bounded literature screen recorded in #20113 found no settlement; completeness remains `ASSUMED-UNVERIFIED`.

## Route

For a finite commutative group $G$ with even cardinality at least three, use $R=\mathbb F_2[G]$ and the subgroup of basis units. The coefficient of the identity is a Frobenius functional: if a nonzero element has a nonzero coefficient at $g$, multiplication by the basis element $g^{-1}$ detects it. Coefficient vectors identify the Cayley graph with the binary Hamming graph on $G$ coordinates.

Coordinate changes connect the graph. Two complement edges realize a single coordinate change using two other coordinates. In a connected triangle-free graph, a proper homogeneous set is independent; two of its members therefore have equal neighbourhoods. Three coordinates exclude such twins in the cube. For every subset $S$ of coordinates, the product character has adjacency eigenvalue $|G|-2|S|$. Choosing half the coordinates supplies a nonzero zero eigenvector.

The cyclic specialization uses $G=\operatorname{Multiplicative}(\mathbb Z/d\mathbb Z)$ for every even $d\ge4$. The final contradiction uses $d=4$. The Lean construction is a group algebra; an isomorphism to $\mathbb F_2[z]/(z^d-1)$ is not formalized.

## Falsifier

The affirmative claim would make a prime connected and anti-connected member of this family have no zero adjacency eigenvalue. The constructed nonzero kernel vector contradicts that consequence. The proof uses symbolic graph and group-algebra arguments rather than a finite adjacency certificate.

## Evidence

The settling module is `D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum.lean`; its Scribe displays the complete negated claim and carries one `OpenProblemResolutionClaim(Refuted)`.

### Experiment

[Experiment at immutable revision f7b6aa25309df5b390bb7bc5e9508beca82b63e8](https://github.com/the-omega-institute/trureturing-experiments/tree/f7b6aa25309df5b390bb7bc5e9508beca82b63e8/docs/reports/nguyen-tan-2025-unitary-cayley-prime-zero-eigenvalue), script `check.py`, SHA-256 `b999f68f21251f9c72f08a43ba1f5d04ea36da575a4d727cb4c6ddc69e4c10e2`. The pinned script is checked with `git cat-file -e` and extracted unchanged for execution with `python3 /tmp/op-nt2508/stageb/check.py`. Exit code 0. For $d=3,4,5,6,8$, the zero multiplicities are respectively $0,6,0,20,70$; all five graphs are regular of degree $d$, connected, anti-connected and prime under the experiment's homogeneous-set closure check. The script also reproduces the stated primeness/nonsingularity agreement for the connected and anti-connected unitary graphs over $\mathbb Z/n\mathbb Z$ with $2\le n\le30$. These are finite numerical readings, distinct from the symbolic Lean proof.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Prime does not imply nonsingular for connected and anti-connected U-unitary Cayley graphs | Kernel-checked: `result` refutes `claim`; the private `even_cyclic_family` supplies every even $d\ge4$. |
| Every finite commutative group of even cardinality at least three supplies a counterexample | Kernel-checked: private `group_algebra_counterexample`, consumed by `even_cyclic_family` and `result`. |
| Product characters have eigenvalue $|G|-2|S|$, and a half-sized subset gives zero | Kernel-checked: private `character_mulVec` and `cube_zero_eigenvalue`. No complete eigenbasis is claimed. |
| Nonsingular implies prime | Source boundary: Proposition 4.16 with the source structure results supplies the surviving direction. This module does not reprove it, and the counterexamples do not contradict it. |
| Zero multiplicities at $d=4,6,8$ are $6,20,70$ | Computed: the pinned experiment, with the command, exit and SHA-256 in Evidence. Full character-basis completeness and the general multiplicity formula are open in this formalization. |
| Full odd-$d$ nonsingularity and a sharp characterization beyond this family | Open in this formalization. The character eigenvalue calculation alone does not prove completeness of the eigenbasis. |
| Cyclic basis size $d$ and the characteristic-two boundary in Proposition 4.20 | Source comparison and prose argument: distinct group basis vectors are distinct units, so their subgroup has size $d$; for even $d$, $2\mid d$. This agrees with the source's $p\nmid|U|$ restriction. That subgroup-cardinality identification is not separately formalized. |

For the cyclic basis-cardinality comparison, the group homomorphism into units sends $g$ to its basis vector. If two such vectors agreed with $g\ne h$, evaluation of the coefficient at $g$ would give $1=0$ in $\mathbb F_2$. Thus this homomorphism is injective, its image subgroup is in bijection with $G$, and the cyclic case has $|U|=d$. This is a prose derivation, not a separately stated Lean theorem.

The failure mechanism is the coexistence of triangle-free twin-free primeness with cancellation of balanced character sums. Requiring the source's $p\nmid|U|$ condition excludes this family; no sharp replacement characterization is asserted. Source results proved independently of the questioned converse retain their stated scope. No additional result depending on that converse is certified by this module.

### Escape audit

The designated `result` has utility `none` and has no utility-refutation exemption. Its four-slot registration is unfinished under [#20113](https://github.com/the-omega-institute/trureturing/issues/20113). The same delivery publishes `D5.S3.Combinatorics.Hamming.InducedSubcubes.invariant_of_toggles` and the definition `D5.S3.Combinatorics.Hamming.InducedSubcubes.toggle`; both are listed under #20113. The definition has no theorem-domain DTR verdict. The existing owner issue is [#15283](https://github.com/the-omega-institute/trureturing/issues/15283). No Reg mirror or `declared_validated` status is claimed. Missing evidence consists of faithful dependent source reconstruction and equivalence bridges, whole-family variation, sensitivity, actual observational dependence, and matching source selection.

## ASSUMED-UNVERIFIED

Literature-search completeness is `ASSUMED-UNVERIFIED`. The recorded screen includes the repeated question in arXiv:2603.21239v1 and arXiv:2607.00404v1 and arXiv:2609.30407v1. It establishes no exhaustive priority claim. The polynomial-quotient isomorphism, full character eigenbasis, general zero multiplicity, odd-dimensional nonsingularity theorem and sharp characterization beyond the family are not formalized here. Escape registration is unfinished as stated in Triage.
