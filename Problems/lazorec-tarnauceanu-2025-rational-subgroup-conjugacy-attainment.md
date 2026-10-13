---
slug: lazorec-tarnauceanu-2025-rational-subgroup-conjugacy-attainment
bibkey: lazorec2025subgroupconjugacy
doi: 10.48550/arXiv.2508.14267
url: https://arxiv.org/html/2508.14267v2
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/CycleNineThreeObstruction
---

# Exact rational attainment of finite-group subgroup conjugacy ratios

## Problem

Mihai-Silviu Lazorec and Marius Tărnăuceanu, *On the number of conjugacy
classes of subgroups of a finite group*, arXiv:2508.14267v2, Section 4,
Problem 4.1:

> Let a,b be integers such that $1\leq a<b$. In Section 2 we proved that
> any ratio of the form $\frac{a}{a+1}$ can be achieved by computing $d'$
> for specific non-nilpotent supersolvable groups having one conjugacy
> class of non-normal subgroups. We also showed that each ratio of the
> form $\frac{a}{b}$ can be achieved as the limit of $(d'(G_n))_{n\geq1}$
> where $(G_n)_{n\geq1}$ is a sequence of nilpotent groups formed as
> direct products of some modular p-groups. Hence, we pose the following
> question: Is it true that there is a group G such that
> $d'(G)=\frac{a}{b}$?

Section 1 specifies that all groups are finite, defines $L(G)$ as the
subgroup lattice and $k'(G)$ as the number of conjugacy classes of
subgroups, and sets $d'(G)=k'(G)/|L(G)|$. Bottom and top belong to $L(G)$.
Conjugacy means inner conjugation by elements of $G$.

The exact settling statement is

```lean
∀ a b : ℤ, 1 ≤ a → a < b → ∃ W : FiniteGroup,
  b * (classCount W.Carrier : ℤ) = a * (latticeCount W.Carrier : ℤ)
```

The source clauses correspond as follows.

| Source clause | Formal meaning |
| --- | --- |
| Integers $a,b$ | Universal `a b : ℤ`, with no coprimality or reduced-fraction condition |
| $1\leq a<b$ | Exactly `1 ≤ a` and `a < b` |
| A finite group $G$ | `FiniteGroup` contains a carrier, its `Group` dictionary and its `Finite` proof; groups are nonempty |
| The whole lattice $L(G)$ | `Subgroup W.Carrier`, including bottom and top, counted by `Nat.card` |
| $k'(G)$ | `Nat.card` of the orbit quotient of that lattice for `ConjAct W.Carrier`; the action is actual inner conjugation |
| $d'(G)=a/b$ | Exact integer equation `b * classCount = a * latticeCount`; the finite lattice and its quotient are both nonempty and have positive counts |
| Every allowed pair | No bounded range, structural restriction, supplied count formula or family-selection hypothesis in the final theorem |

## Motivation

Exact attainment distinguishes a single finite realization from a limit
of realizations. Theorem A in the source establishes density for
nilpotent groups, and Corollary 2.4 establishes the consecutive ratios.
Neither assertion alone supplies compatible factors for an arbitrary
$a/b$. The paper itself proposes the telescoping product; its missing
ingredient is a simultaneous choice of the required ratios with
coprime group orders.

The existing `CycleNineThreeObstruction` develops finite-group order,
Sylow and cyclic-action reasoning. It motivates using actual groups
with controlled orders here, rather than numerical proxy counts. It is
not an imported prerequisite or an attainment theorem.

## Gap

The source's proposed route needs $b-a$ groups of pairwise coprime orders
and ratios $(a+i-1)/(a+i)$. The examples in Corollary 2.4 establish each
ratio separately; they do not by themselves establish the required
joint coprimality. Arbitrary products cannot use coprime multiplicativity
without that compatibility.

The kernel construction fills this gap by choosing each new factor
above the order of the entire accumulated product. Its action,
whole-lattice enumeration, orbit enumeration and count multiplicativity
are proved for the actual groups. The primary v2 still presents
Problem 4.1 as a question; the bounded literature search and its limits
are given in the source note and below.

## Route

Write $C_m=\operatorname{Multiplicative}(\operatorname{ZMod}(m))$.
For primes $p,q$ with $q\mid p-1$ and $s>0$, the automorphism group of
$C_p$ has order $p-1$. Cauchy's theorem supplies an automorphism of
exact order $q$. Since $q\mid q^s$, the cyclic-generator extension
constructs an actual action $A:C_{q^s}\to\operatorname{Aut}(C_p)$.
Take the genuine semidirect product $V=C_p\rtimes_A C_{q^s}$.

Every subgroup $H$ is classified by its intersection with $C_p$ and
its projection to $C_{q^s}$. An intersection equal to $C_p$ makes $H$
the inverse image of a subgroup of $C_{q^s}$. Trivial intersection
makes projection injective. A proper projected subgroup acts trivially;
coprime element orders force the left coordinate of $H$ to be trivial.
If projection is full, solving the fixed-point-free commutator equation
conjugates $H$ to the full complement.

Thus the lattice has three disjoint families: $s+1$ inverse-image
subgroups, $s$ proper embedded subgroups, and $p$ conjugate full
complements. The first two families are respectively normal and central,
so each contributes singleton conjugacy classes. The last family
contributes one class. The complete bijections give

$$|L(V)|=2s+p+1,\qquad k'(V)=2s+2.$$

These formulas are already stated in the proof of Proposition 2.2(ii)
of the source, with $n=s+1$. The Lean theorem supplies full formal
evidence, including $s=1$; the formulas are not new mathematical claims.

For finite groups $W,V$ of coprime orders, every subgroup of $W\times V$
is the product of its projected subgroups. Powers isolate each
component because its element order is coprime to the other group order.
Conjugation acts componentwise, so two product subgroups are conjugate
exactly when their respective factors are conjugate. Whole-lattice and
orbit-quotient bijections prove both count identities, and hence
$d'(W\times V)=d'(W)d'(V)$. The ratio identity is already source-attested
in Section 1; it is not assumed by the Lean proof.

Given a positive natural $t$ and any accumulated actual finite group
$W$, choose primes

$$\max(4,|W|)<q<p,\qquad q\mid p-1.$$

The infinitude of primes supplies $q$; the pinned theorem
`Nat.exists_prime_gt_modEq_one` supplies $p\equiv1\pmod q$ with $p>q$.
Set $n=t(p-1)/2$ and $s=n-1$. Since $p$ is odd and $p>4$, these are
integers with $n\geq2$ and $s>0$. For the action constructed above,

$$d'(V)=\frac{2n}{2n+p-1}=\frac{t}{t+1},\qquad |V|=pq^s.$$

Both primes exceed the positive integer $|W|$, so neither divides it.
Consequently $|V|$ is coprime to $|W|$. This establishes compatible
consecutive-ratio factors without assuming a previously chosen prime family.

For every positive natural $a$, induction on $m$ produces a finite group
with ratio $a/(a+m)$. The base $m=0$ is the trivial group, with both
counts equal to one. At the step, put $t=a+m$ and multiply the accumulated
group by the fresh factor just constructed. Coprime multiplicativity gives

$$\frac{a}{t}\frac{t}{t+1}=\frac{a}{t+1}.$$

For the original integers, use their nonnegative natural representatives
and $m=b-a$. Exact rational cross-multiplication and integer casting
give the universal settling equation. No finitary scan is used.

## Falsifier

A counterexample to the target would be an integer pair $1\leq a<b$
for which no actual finite group has the stated ratio. A witness with
only proxy counts, a restricted lattice, or subgroup-isomorphism classes
would not meet the target. For this route, a missing subgroup in the
classification, an incorrect orbit identification, failure of the prime
supplier for any accumulated order, or failure of coprime product
multiplicativity would break the universal construction. Each is an
obligation in the existing kernel proof, rather than an additional
hypothesis of the conclusion.

## Evidence

The sole settling declaration is
`D5/S3/FiniteGroups/RationalSubgroupConjugacyAttainment.rational_attainment`.
Its full type is the statement in `Problem`. The proof uses
`CyclicPrimePowerAction.actionData`, `subgroup_classification`,
`subgroupEnumeration`, `classesEnumeration`, `split_counts`, and
`SubgroupConjugacyRatio.coprime_product_counts`, together with the
fresh-prime and consecutive-factor constructions and unbounded induction.
The theorem's allowed axiom closure is `Classical.choice`, `Quot.sound`
and `propext`; no new axiom or sorry is part of these sources.

[Preregistration #15875](https://github.com/the-omega-institute/trureturing/issues/15875)
specifies the full universal target, tier 1, proof settlement, the
fresh-prime compatibility route and bounded literature qualification.
Tier 1 identifies a recent explicit exploratory question, rather than
an already established result or a finite partial computation.

`Reg/D5/S3/FiniteGroups/RationalSubgroupConjugacyAttainment.lean` retains
the exact source realization and count observations, positivity,
whole-family intervention sensitivity and actual observational dependence.
The helper escape registrations remain unfinished under
[issue #15888](https://github.com/the-omega-institute/trureturing/issues/15888);
that exception is not a helper validation claim. This dossier does not
assert freezing, completion of publication checks, or a merged delivery.

## Triage

`theorem`: the full formal proof answers the universal Problem 4.1
affirmatively. The result concerns every allowed integer pair and an
actual finite group, without weakening the original claim.

### What the settlement shows

- **Proved — universal attainment.**
  `RationalSubgroupConjugacyAttainment.rational_attainment` gives every
  rational strictly between zero and one as an exact value of $d'$ on
  finite groups. Coprime fresh factors are the decisive mechanism:
  consecutive ratios can be assembled in one common realization.
  Unreduced fractions and arbitrarily large parameters are included.
- **Source-attested — known ingredients.** Proposition 2.2(ii) gives the
  split-family counts, Corollary 2.4 gives consecutive-ratio attainment,
  and Section 1 gives coprime multiplicativity. Problem 4.1 proposes the
  telescoping product. The formal construction supplies its missing
  compatible-order choice; it does not claim invention of those ingredients.
- **Proved construction — avoiding existing primes.** The
  `consecutive_factor` proof chooses the new order coprime to any supplied
  finite group. Thus each step avoids every prime divisor of the
  accumulated order. This explains why the route extends from separate
  consecutive ratios to the entire unbounded rational target. It supplies
  no order-minimality or computational complexity bound.
- **Source-attested boundary — nilpotent density.** Theorem A's density
  result remains a statement specifically about nilpotent groups.
  Exact attainment here uses nontrivial split extensions. The final
  theorem gives no nilpotence or supersolvability certificate. Exact
  attainment within nilpotent groups is not established by this result;
  density alone would not establish it either.
- **Source question answered — the route in Problem 4.1.** The
  proposed sufficient construction can now be made with jointly
  compatible orders for all $1\leq a<b$. No theorem elsewhere in the
  paper is invalidated. Its limit construction remains valid with its
  nilpotent restriction; unrestricted exact realization is additional.
- **Open in the cited source, outside this settlement — Problems 4.2
  and 4.3.** Problem 4.2 asks about the structure of a Sylow 2-subgroup
  when $d^*>2/3$. Problem 4.3 asks for extremal $d'$ and $d^*$ values on
  groups of prescribed prime-power order. Neither follows from a
  construction allowing freely chosen primes and orders. The present
  theorem concerns $d'$, and supplies no conclusion about $d^*$.
- **Boundary — endpoints and classification.** The target is the open
  interval $(0,1)$. The proof uses the trivial group's value one as its
  induction base, but asserts no attainment of zero and no classification
  of all groups realizing a specified rational. It resolves one named
  problem, not the whole paper or the world's priority question.

## ASSUMED-UNVERIFIED

The source identity, finite-group convention, definitions, split-family
scope, explicit counts and Problem 4.1 were checked against the primary
arXiv v2 HTML and abstract page. The version history lists v1 on
19 August 2025 and v2 on 9 August 2026. The source is CC BY 4.0.

The literature qualification is bounded: #15875 reports the primary
version history, three related arXiv texts, author-result windows, title
and subgroup-conjugacy searches, and repository/issue duplicate checks;
no resolution was located in that reported scope. The full windows and
unavailable citation services are specified in
[the source note](../Library/FiniteGroups/lazorec2025subgroupconjugacy.md).
Those attributed search results are not an exhaustive worldwide survey.
A later or unindexed independent settlement cannot be excluded, and no
mathematical priority claim is made. The remaining source questions are
identified as open in that version, without a claim that their current
worldwide status has been independently settled.
