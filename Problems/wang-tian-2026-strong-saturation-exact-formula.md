---
slug: wang-tian-2026-strong-saturation-exact-formula
bibkey: wangtian2026strongsaturation
doi: 10.48550/arXiv.2605.01269
url: https://arxiv.org/abs/2605.01269v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.result
---

# The unrestricted exact Wang–Tian saturation formula is false

## Problem

Qinglin Wang and Yingzhi Tian, *Extremal Problems for the Family of k-Strongly
Connected Digraphs*, arXiv:2605.01269v1, Section 4, Conjecture 1, printed PDF
page 13, state: “For sufficiently large $n$,
$\operatorname{ex}(n,\mathcal D_k)=\frac32(k-\frac43)(n-k+1)+\binom n2$.”
The source is [Conjecture 1](https://arxiv.org/html/2605.01269v1#Thmconj1).

### Statement echo

The closed proposition `claim` quantifies every $k\in\mathbb N$ with
$1\le k$, then a threshold $N\in\mathbb N$ depending on $k$, then every
$n\in\mathbb N$ with $N\le n$. Its equality is

$$
(\operatorname{ex}(n,\mathcal D_k):\mathbb Q)
=\frac32\left((k:\mathbb Q)-\frac43\right)
\left((n:\mathbb Q)-(k:\mathbb Q)+1\right)
+(\operatorname{Nat.choose}(n,2):\mathbb Q).
$$

Every division and subtraction is rational. There is no rounding, parity,
divisibility restriction or error term. The local Section 4 reading $k\ge2$
is also contradicted by $k=3$.

Strict digraphs have ordered distinct-endpoint arcs, permit reciprocal arcs,
and have no parallel arcs. A subdigraph chooses arbitrary vertex and arc
subsets, retaining isolated vertices. Dipaths are vertex-simple directed
paths. A separator leaves a nonstrong or singleton remainder. For nonempty
records the connectivity is the attained minimum separator size. Positive
strong connectivity excludes empty records; the source leaves null
connectivity unspecified. This explicit totalization retains the source's
Lemma 2.2 consequence that a $k$-strong graph has at least $k+1$ vertices.
Saturation means forbidden-free and that every missing ordered arc creates
a $k$-strong arbitrary subdigraph. The extremum is the actual attained
maximum arc count over a proved nonempty finite family of saturated hosts.
The Blueprint explains the invertible relabelling to `Fin n`; it does not
claim a separate compiled transport theorem.

## Motivation

An exact extremal count must be integral. An obstruction at arbitrarily large
orders defeats the eventual quantifier without computing any extremizer.
The target is the full printed equality, not an arithmetic surrogate or a
claim restricted to one graph order.

## Gap

The bounded source and literature qualification is recorded in
[preregistration #23010](https://github.com/the-omega-institute/trureturing/issues/23010)
and [the source note](../Library/GraphInvariants/wangtian2026strongsaturation.md).
No prior exact correction or refutation was found in the inspected sources.
Unavailable citation and discovery routes supply no negative evidence.
The original 1979 Mader chapter remains unread and unused. The related
Bernshteyn–Kostochka work concerns an undirected upper bound. No exhaustive
literature or global priority assertion is made.

## Route

Assume the entire claim and instantiate $k=3$. For its proposed threshold
$N$, choose $n=2N+5\ge N$. The equality becomes
$\operatorname{ex}(n,\mathcal D_3)=\binom n2+\frac52(n-2)$.
Clearing the denominator gives

$$
2\operatorname{ex}(2N+5,\mathcal D_3)
=2\binom{2N+5}{2}+5(2N+3)
=2\left(\binom{2N+5}{2}+5N+7\right)+1.
$$

The natural-to-rational cast is injective. The left side is even and the
right side odd, a contradiction for every threshold. The saturated family
and its maximum exist independently of the conjectured equality: maximize
cardinality in the finite nonempty family of free arc sets, then maximize
in the finite nonempty saturated family. Attainment and domination remain
part of the minimum and maximum definitions' dependent certificates.

## Falsifier

The source-level interpretation would fail if Conjecture 1 excluded the
unbounded odd orders at $k=3$, included rounding, or used another quantity
instead of an integer arc cardinality. The printed statement contains none
of those restrictions. The formal model must retain arbitrary subdigraphs,
positive connectivity's empty-domain exclusion and actual attained extrema.

## Evidence

The canonical module is
[D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.lean](../D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.lean).
Its closed `claim : Prop` is the whole statement above; `result : Not claim`
is its kernel-checked negation. The source model, finite-family nonemptiness
and attained certificates are implemented in the same module. The
[Blueprint](../Blueprint/D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.md)
displays every public definition and the full negated formula.

The proof shape is bind-only and the admission basis is
`open-problem-resolution` (#23010; Refuted). The utility is a certified
instance under `refutes`; no escape witness or new axiom is claimed.
The public result is the designated refutation result (`basis=refutes`) and
is exempt from four-slot escape registration (CLAUDE.md §3.9).
The endpoint proof-field projection is structure-generated, not an authored
companion theorem. The axiom closure of every public declaration is contained
in {propext, Classical.choice, Quot.sound}.

## Triage

### What the settlement shows

- **Proved, kernel-checked:** the full unrestricted eventual equality is false;
  the declaration is `D5.S3.Combinatorics.Graph.Saturation.WangTianStrongSaturationRefutation.result`.
- **Proved in prose:** parity and integrality defeat every threshold at
  $k=3$, $n=2N+5$ by the displayed even/odd derivation. This describes the
  proof of `result`; no additional Lean family theorem is asserted.
- **Open:** the actual extremal number at these orders is not computed by
  this argument. The formal maximum has an attainment certificate, which
  supplies existence rather than an evaluated value.
- **Open:** a corrected rounded exact formula; the half-integrality
  obstruction alone does not decide it.
- **Open:** an exact formula on divisible orders; the odd-order witnesses
  do not settle the excluded orders.
- **Open:** corrected inequality or asymptotic versions; negating an exact
  equality supplies neither their proof nor their refutation.
- **Source argument retained, literature reading:** Theorem 4.2's
  construction and its divisibility-sensitive equality condition are
  distinct from Conjecture 1's unrestricted equality. No refutation of the
  source's proved construction or bounds follows from `result`.
- **Open:** source consequences requiring a corrected conjecture or further
  graph estimates remain unsettled. No unresolved source consequence is
  claimed settled by this dossier.

No computation or experiment is used as evidence for an extremal value.
The parity derivation is symbolic and unbounded in $N$.

## ASSUMED-UNVERIFIED

Author intent about a corrected conjecture and worldwide priority are
unverified. Null-graph connectivity in the source's cited textbook is
unverified and is not asserted. The formalization uses the explicit
empty-domain convention above. Definition-level relabelling exposition is
not a separate Lean transport result. Required CI and the final independent
review triplet own publication admission; this dossier asserts no merge or
solution credit.
