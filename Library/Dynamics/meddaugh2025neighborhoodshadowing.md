---
bibkey: meddaugh2025neighborhoodshadowing
authors: Jonathan Meddaugh and Elyssa Stephens
year: 2025
title: Shadowing with small diameter sets of bounded cardinality
doi: null
url: https://arxiv.org/abs/2509.04312v1
claim: Questions 5.1 and 5.2 ask for strict finite neighborhood-shadowing levels. Question 5.3 asks for neighborhood two-shadowing without exact-length quasi-finite type. Question 5.4 asks for a shadowing characterization of quasi-finite type. Question 5.5 asks for a language characterization of neighborhood two-shadowing. Question 5.6 asks for weak mixing and neighborhood N-shadowing without dense small periodic sets.
strata_touched:
  - D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances
  - D5/S1/Dynamics/Shadowing/ProgressionExample
  - D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy
  - D5/S1/Dynamics/Shadowing/LanguageCharacterization
  - D5/S1/Dynamics/Shadowing/QuasiFiniteType
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

## Weak mixing without nonempty small periodic sets

Question 5.6 in the same primary version asks:

> Is there a weakly mixing system which has the neighborhood N-shadowing property (N>1) that does not have dense small periodic sets?

The source's compact metric system uses a continuous map; it does not
require invertibility. Its small-periodic-set definition omits explicit
nonemptiness. The intended nonempty reading is necessary, since the empty
set is compact, contained in every open set and periodic for every map.

`D5/S1/Dynamics/Shadowing/ProgressionExample.quadratic_progression_example`
uses the one-sided binary carrier with a zero in every progression
{s+jp : 0<=j<=p^2+2}, for every s>=0 and p>=1. It has the genuine
first-disagreement metric, a continuous onto mixing shift, and original
neighborhood two-shadowing. The nonempty clopen cylinder [1] contains no
nonempty forward power-invariant subset, hence no nonempty compact periodic
set. The exact construction and proof are exposed in its Blueprint source
and [problem entry](../../Problems/meddaugh-stephens-2025-mixing-small-periodic-sets.md).

The arithmetic-progression construction, two rotation masks and constants
are attributed to the supplied completed Pro proposal. Native implementation
and its verification are separate from its isolated ordinary mathematical
review. The current arXiv metadata lookup returns v1; no exhaustive
literature novelty or priority exclusion is claimed.

## Every positive finite neighborhood level

Questions 5.1 and 5.2 ask which N admit neighborhood (N+1)-shadowing
without neighborhood N-shadowing, for systems and for subshifts. The
primary text explicitly says its authors had not found three-but-not-two.

`LacunaryShadowingHierarchy.lacunary_shadowing_hierarchy` gives every
positive finite level. For m=N+2, its binary two-sided subshift X_m
requires at most two ones in each m-term progression of step (m+1)^k.
It is compact, nonempty and invariant under the continuous invertible
shift. The upper bound uses m-1 explicit periodic masks with a common
initial window and a complete future-window cover; all long progression
phases reduce to one regular m-gon. The lower bound forces all tracers
to retain the initial one and each to cover at most one later target.
The exact original fixed-set, initial-diameter and natural-time contract
is retained, using the existing compatible product metric.

The construction is attributed to the supplied Pro proposal, with native
Lean implementation by Codex. The complete endpoint has passed a scoped
Lean build. Its [problem entry](../../Problems/meddaugh-stephens-2025-neighborhood-shadowing-hierarchy.md)
retains the source questions, construction and limits.

An independent bounded followup read Baylor's November 6, 2026
[dissertation-defense announcement](https://math.artsandsciences.baylor.edu/news/story/2026/two-mathematics-phd-students-successfully-defend-dissertations)
for Ellie Stephens, *Local Variations of Shadowing*, advised by Jonathan
Meddaugh. The announcement discusses neighborhood shadowing but states no
hierarchy theorem, and the full dissertation was inaccessible. Priority
relative to that dissertation remains unverified.

## Shadowing both tails of a single jump

Question 5.4 asks for a shadowing characterization of exact-length
quasi-finite type. For any compatible metric on a two-sided finite-alphabet
subshift, quasi-finite type is equivalent to the following property.
For every accuracy there are a tolerance and an integer cutoff.
Take two points closer than that tolerance and form a pseudo-orbit
from the entire past of the first and the entire future of the second.
One true orbit traces both tails at the original times outside the
interval set by the cutoff. The cutoff is uniform over both inputs.

The forward argument uses Definition 3.5 on increasingly long exterior
contexts of the common central block. Compactness gives a point realizing
both infinite tails. Conversely, take accuracy small enough to detect
coordinate zero, align occurrences with a long common bridge, and use the
tracing point to retain the two exterior contexts. Its central coordinates
supply the replacement of exactly the original bridge length.

The single-jump pseudo-orbit also occurs in simple two-sided limit
shadowing. That property describes eventual tracing for all pairs with
pair-dependent onset. Two-sided limit shadowing with a phase gap allows
shifting the positive-time comparison. The criterion for quasi-finite
type applies to nearby inputs with a uniform interval and the original phase.
[Primary comparison](https://arxiv.org/html/1402.0674v1)

## Finite-language characterization

Question 5.5 asks whether neighborhood two-shadowing in subshifts can be
characterized by the language. For any positive integer $N$ on a two-sided
finite-alphabet subshift, the criterion uses finite words and colorings.
For each tracing window radius $k$, one local radius $m\geq k$ must work
for every $n$ and every word on $[-m,n+m]$ whose radius-$m$ blocks at
times $0,\ldots,n$ occur in the language. The times $1,\ldots,n$ must
admit an $N$-coloring. Each color class must have an extension in the
language that simultaneously matches the initial radius-$k$ block and
the radius-$k$ block at each time of that color.

The theorem `LanguageCharacterization.neighborhoodFiniteShadowing_iff_languageColoring`
proves the equivalence for every compatible metric on the subshift.
Finite requirements yield one fixed tracing tuple by compactness. The
initial block is included in every color class's extension requirement
because the initial tracer diameter is small and the set traces time zero.

The comparison included the mixing-sofic and quasi-finite-type sufficient
conditions in the primary version and the usual $N=1$ equivalence with
finite type. The authors' later [arXiv:2608.28845v2](https://arxiv.org/abs/2608.28845v2)
addresses ordinary shadowing and inverse shadowing. The search found
no prior equivalent for $N=2$ among the inspected sources. The full text
of Stephens's dissertation remains unavailable for comparison.

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
The relevant locators are Definition 2.1, Definition 3.5, Question 5.3,
the small-periodic-set definition immediately before Proposition 4.3,
and Question 5.6.
