---
bibkey: meddaugh2025neighborhoodshadowing
authors: Jonathan Meddaugh and Elyssa Stephens
year: 2025
title: Shadowing with small diameter sets of bounded cardinality
doi: null
url: https://arxiv.org/abs/2509.04312v1
claim: Question 5.3 asks whether a subshift can have neighborhood 2-shadowing without being of quasi-finite type in the exact-length sense of Definition 3.5.
strata_touched:
  - D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances
license: citation-only
triage: anchor
---

# Neighborhood two-shadowing beyond quasi-finite type

Jonathan Meddaugh and Elyssa Stephens, *Shadowing with small diameter sets
of bounded cardinality*, arXiv:2509.04312v1, Question 5.3:

> Are there subshifts with neighborhood 2-shadowing which are not a subshift of quasi-finite type?

Definition 2.1 requires that for every $\varepsilon>0$ there is
$\delta>0$ such that every natural-time $\delta$-pseudo-orbit $(x_i)$
has a fixed nonempty finite tracing set $A$, with $|A|\leq2$,
$\operatorname{diam}(A)<\varepsilon$, and
$\operatorname{dist}(x_i,\sigma^i(A))<\varepsilon$ at every $i\geq0$.
The choice of a member of $A$ may vary with time; the set $A$ does not.

Definition 3.5 requires a threshold $M$ such that whenever $n\geq M$,
$u,v$ are language words and some language word $w$ of length $n$ has
$uw,wv$ in the language, there is a language word $z$ of length **exactly**
$n$ with $uzv$ in the language. Ordinary $N$-shadowing without the initial
diameter condition, density shadowing and entropy-based uses of
“quasi-finite type” do not supply this statement.

The return-distance example is the binary two-sided subshift with
consecutive-one distances $D=\{2^j:j\geq0\}$. Its zero-run lengths are
$2^j-1$, and distance one is allowed. Finite supports and the configuration
with no ones remain in the space. The declaration
`D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.powers_two_return_distance_example`
establishes nonemptiness, compactness, continuity of the shift,
neighborhood two-shadowing and failure of the exact-length condition.
Its consumer exposition is in the corresponding Blueprint document;
the original question is also retained in
[the problem entry](../../Problems/meddaugh-stephens-2025-neighborhood-two-shadowing.md).

The formal metric is Mathlib's genuine compatible countable-product
metric. It is not literally the source's printed infimum over disagreeing
windows: for distinct configurations, that printed expression has
infimum zero. The finite-window arguments use the actual product
uniformity, and the QFT obstruction uses nonempty words with
$n=\max(M,1)$.

## Literature boundary

The inspected primary version lists Question 5.3 as a question. A bounded
independent search found no exact prior answer within its searched scope;
this does not certify exhaustive priority or novelty. Carrasco-Olivera,
Lee, Morales and Villavicencio, *Finite-expansivity and N-shadowing*
(2022), DOI 10.1007/s00574-021-00253-w, has a
[17-page author manuscript](https://drive.google.com/uc?export=download&id=1iH0yrc9TX8SG11O3yKeyDHMhT9GikHrq)
linked from [Villavicencio's research page](https://sites.google.com/imca.edu.pe/hvillavicencio/research).
The inspected passages are Definition 1.5 and Theorem 3 (pp. 3–4) and
Lemma 16 (pp. 11–12). Definition 1.5 uses a fixed nonempty tracing set of
at most $N$ points and two-sided pseudo-orbit time, without a separate
initial diameter bound. The set-distance definition on p. 3 is printed
as a supremum; its literal definition is not identified with Definition
2.1 here. Theorem 3 states an $N$-shadowing hierarchy with interval and
genus-two surface examples. Lemma 16 transfers finite-cardinality
shadowing through the whole inverse image of a tracing set, without a
separate initial diameter bound. These inspected statements do not give
a direct answer to Question 5.3. This bounded comparison is not an
exhaustive full-text exclusion or validation of the journal version,
which remains unread. Dastjerdi and Hosseini, *Sub-shadowings* (2010),
DOI 10.1016/j.na.2010.01.014, remains unread after full-text access
failures (HTTP 403/401); no full-text exclusion is claimed for it.
Dastjerdi and Jangjoo, arXiv:1108.3242, is withdrawn because of a flaw in
Theorem 3.2 and is not used as proof.

## Verified locator

Versioned primary: https://arxiv.org/abs/2509.04312v1.
Full-text primary: https://arxiv.org/html/2509.04312v1.
The relevant locators are Definition 2.1, Definition 3.5 and Question 5.3.
