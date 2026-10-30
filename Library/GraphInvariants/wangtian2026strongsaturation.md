---
bibkey: wangtian2026strongsaturation
authors: Qinglin Wang; Yingzhi Tian
year: 2026
title: Extremal Problems for the Family of k-Strongly Connected Digraphs
doi: 10.48550/arXiv.2605.01269
url: https://arxiv.org/abs/2605.01269v1
claim: "Section 4, Conjecture 1 states the unrestricted exact eventual extremal arc formula for the family of k-strongly connected strict digraphs."
strata_touched:
  - D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation
license: citation-only
triage: anchor
---

# Exact strong-digraph saturation formula

The source is arXiv:2605.01269v1. Section 1 defines finite strict directed
graphs, directed dipaths, strong connectivity, separators and vertex-strong
connectivity. Reciprocal arcs are permitted. A separator leaves a graph that is
not strongly connected or is trivial. The finite model uses singleton for
trivial and excludes the empty graph from positive strong connectivity; the
source does not separately specify null connectivity. This convention preserves
the consequence that a k-strong graph has at least k+1 vertices used in the
proof of Lemma 2.2. The cited textbook's null-graph convention is not asserted.

Saturation excludes every k-strong subdigraph and requires that adding any
missing ordered arc creates one. Subdigraphs permit arbitrary vertex and arc
subsets, with isolated vertices retained. The extremal number is the maximum
arc cardinality among saturated n-vertex hosts, rather than among induced
subgraphs or only spanning forbidden copies.

Section 4, Conjecture 1 (printed PDF p. 13) states:

> For sufficiently large n,

$$
\mathrm{ex}(n,\mathcal D_k)
=\frac32\left(k-\frac43\right)(n-k+1)+\binom n2.
$$

The displayed formula has no rounding, divisibility condition or error term.
The full formal claim quantifies every positive k, a threshold depending on k,
and every n beyond that threshold. The local Section 4 context uses k at least
two; the k=3 obstruction applies to that reading as well. Theorem 4.2's
construction has a divisibility-sensitive equality condition, which is not
present in the conjecture.

The repository's argument uses k=3 and n=2N+5 for every proposed threshold N.
Twice the putative extremal value would be
2(choose(2N+5,2)+5N+7)+1, contradicting its evenness. The formal extremum is an
actual finite maximum with a proved nonempty saturated family, an attaining
host and domination over every saturated host. The proof is a repository
derivation from integrality; the paper is the source of the target, not an
attribution of this refutation to Wang and Tian. The labelled Fin n
presentation and its definition-level bijective transport are explained in
the corresponding Blueprint.

This argument only addresses the literal unrestricted exact equality. It does
not settle corrected rounded, divisible-order, upper-bound or asymptotic
variants. The related Bernshteyn–Kostochka work, arXiv:1504.03758v2, concerns an
undirected upper-bound problem and supplies no graph theorem used here. The
original Mader chapter is not invoked as proof. The bounded qualification of
this target found no previous exact correction or refutation in the inspected
sources; unavailable citation-graph routes give no negative evidence. No
exhaustive literature search or global novelty assertion is made.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2605.01269
- URL: https://arxiv.org/abs/2605.01269v1
- HTML: https://arxiv.org/html/2605.01269v1#Thmconj1
- PDF: https://arxiv.org/pdf/2605.01269v1
- Section 1 definitions, Lemma 2.2, Section 4 Theorem 4.2 and Conjecture 1;
  conjecture on printed PDF page 13.
