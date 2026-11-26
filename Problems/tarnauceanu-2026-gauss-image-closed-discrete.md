---
slug: tarnauceanu-2026-gauss-image-closed-discrete
bibkey: tarnauceanu2026gauss
doi: 10.48550/arXiv.2611.34371
url: https://arxiv.org/pdf/2611.34371v1#page=10
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/Gauss/TarnauceanuImage.gauss_family
  - D5/S3/FiniteGroups/Gauss/TarnauceanuImage.image_not_closed_and_discrete
---

# Tărnăuceanu’s Gauss image in the relative real topology

## Problem

Marius Tărnăuceanu, *On some problems regarding a group-theoretical
generalization of the Gauss formula*, arXiv:2611.34371v1, Remark 3.4, p. 10.

> It remains an open problem to determine the accumulation points of Im(f) (or to decide whether Im(f) is closed and discrete in [1, ∞)).

The registered target is the parenthetical alternative. For each finite group
`G`, write `f(G)` for the sum of the full automorphism-group orders of its
actual subgroups divided by the group order. Let `I` be the image over all
finite groups. Decide whether `I` is both closed and discrete in the real
subspace `[1,∞)`. The registered answer is the negative conjunction.

| Source object | Lean binding |
| --- | --- |
| All actual subgroups and their full automorphism groups | `H : Subgroup G` and `Nat.card (MulAut H)` in `gauss` |
| All finite groups | `gaussImage` is a range over bundled finite groups. Every finite group in any carrier universe has an isomorphic representative in that range. |
| Real subspace `[1,∞)` | `Set.Ici (1 : ℝ)` with its inherited topology |
| Closed and discrete | `IsClosed gaussImage ∧ DiscreteTopology gaussImage` |
| Decision and exact witness family | `image_not_closed_and_discrete` and `gauss_family` for every natural `n ≥ 1` |

[Published locator](https://arxiv.org/pdf/2611.34371v1#page=10) · [Preregistration](https://github.com/the-omega-institute/trureturing/issues/34522)

## Motivation

The paper proves a gap between 2 and 5/2 and discusses further gaps near
the bottom of the image. A geometric limit tests the topological question
above those gaps. [Theorem 3.3 and Remark 3.4](https://arxiv.org/pdf/2611.34371v1#page=10)

## Gap

Table 1 gives the first two cyclic-product values. The cited 2023 paper
counts the cyclic contribution and gives a general abelian automorphism
formula. The exact subgroup distribution for all exponents and its use in
the relative-topology argument require a uniform proof.
[Table 1](https://arxiv.org/pdf/2611.34371v1#page=11) · [Earlier source](https://arxiv.org/abs/2212.09055v1)

## Route

Each element belongs to the generator fiber of one cyclic subgroup. The
cyclic terms therefore sum to the group order. In the projection onto
`C_(2^n)`, a subgroup meeting the order-two kernel trivially injects into
the first factor. Every noncyclic subgroup contains the kernel and is the
full inverse image of a nontrivial subgroup of the first factor. This
gives one actual subgroup of type `C_(2^k) × C₂` for each `1 ≤ k ≤ n`.

Ordered generator images give six automorphisms at `k=1` and
`2^(k+1)` for `k≥2`. The noncyclic sum is `4·2^n−2` and the denominator is
`2·2^n`. Thus `f(C_(2^n) × C₂)=3−2^(−n)`. The positive-exponent sequence
converges to 3 in the ambient subtype and each term differs from 3.
Closedness would put 3 in the image. Discreteness would then make its
singleton a neighborhood in the image, contradicting convergence there.

## Falsifier

An actual subgroup absent from the proposed classification, an incorrect
full automorphism count, or a failure of the limit in the relative topology
would invalidate the respective part of the route.

## Evidence

- [Preregistered statement and literature screen](https://github.com/the-omega-institute/trureturing/issues/34522)
- [Exact finite probe at exponents 1–4](https://github.com/the-omega-institute/trureturing/issues/34522#issuecomment-7195973821)
- [Public report of the independently replayed Lean proof](https://github.com/the-omega-institute/trureturing/issues/34522#issuecomment-7196556792)
- [Primary bibliography note](../Library/FiniteGroups/tarnauceanu2026gauss.md)
- [Earlier bibliography note](../Library/FiniteGroups/fasolatarnauceanu2023gauss.md)

## Triage

**Proved.** The entire family formula holds, and
`image_not_closed_and_discrete` proves the registered alternative. The
limit 3 is an accumulation point in `[1,∞)`. The obstruction is the
convergence of image points other than 3. The gaps proved earlier in
the paper are compatible with this behavior.

**Independently Lean-checked evidence.** The separate order-ten dihedral
proof counts 20 full automorphisms and gives value 3. This places the
accumulation point in the image and implies failure of discreteness.
Fasolă–Tărnăuceanu give the value in their general odd-dihedral formula,
and the 2026 proof of Theorem 3.3 gives the same value by specialization.
This fixed-instance evidence is outside the settling module and its
typed resolution. [Earlier formula](https://arxiv.org/pdf/2212.09055v1) · [Public replay report](https://github.com/the-omega-institute/trureturing/issues/34522#issuecomment-7196556792)

**Open in this dossier.** The complete set of accumulation points and
closedness alone remain undetermined by the supplied arguments.

## ASSUMED-UNVERIFIED

The literature screen covers the pinned preprint, the cited predecessor,
and the bounded searches recorded in the preregistration. Full
citation-index coverage and priority remain unverified.
[Preregistered literature screen](https://github.com/the-omega-institute/trureturing/issues/34522)
