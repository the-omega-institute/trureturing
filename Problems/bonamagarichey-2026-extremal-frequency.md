---
slug: bonamagarichey-2026-extremal-frequency
bibkey: bonamagarichey2026letter
doi: null
url: https://arxiv.org/abs/2606.06655v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.claim
  - D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.result
---

# Bóna–Maga–Richey: the unrestricted extremal avoidance frequency

## Problem

Miklós Bóna, Balázs Maga and Jacob Richey, *Letter frequency in shifts of finite type with one forbidden word*, arXiv:2606.06655v2, Section 5.3, printed p. 19:

> Among all words of a fixed length k, forbidding the word 10^{k−1} or its reversal should maximize the frequency ρ, although we do not have a proof of this.

The global domain in Section 2 is binary words of integer length $k\ge1$. For every nonempty binary word $w$ and every positive integer $n$, let $\Omega_n^w$ be all length-$n$ binary words avoiding $w$ as a contiguous factor, and put

$$
\rho_n^w=\frac{\sum_{v\in\Omega_n^w}|v|_1}{n|\Omega_n^w|}.
$$

For every integer $k\ge1$, put $u_k=10^{k-1}$. The complete assertion requires limits $L_w=\lim_{n\to\infty}\rho_n^w\in\mathbb R$ for every $w\in\{0,1\}^k$, and, for every such $w$, both $L_w\le L_{u_k}$ and $L_w\le L_{\operatorname{reverse}(u_k)}$. There is no nonconstancy, fixed-composition, irreducibility or larger-length restriction. The source's subsequent fixed-composition question is separate. The stopped first-hit statistic $q$ is also separate.

The claim truth anchor is `D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.claim`. Its `MaximizesFrequency k u` includes length equality, existence of an actual native limit for $u$, and existence of an actual native limit for every same-length competitor, with the required inequality. The claim conjoins this property for both proposed words at every $k\ge1$. Uniqueness of real limits identifies the limits appearing in its two conjuncts.

## Motivation

The proposed extremizers concern the source's actual avoidance average, rather than an assigned frequency or a finite-length surrogate. Testing the complete positive-length domain distinguishes the published universal assertion from possible restricted replacements. The half-frequency characterization in Conjecture 6.1 is a different problem.

## Gap

The original body of [preregistration #30346](https://github.com/the-omega-institute/trureturing/issues/30346) records Tier 1, the full source sentence and domain, and the bounded pre-probe literature and duplicate screens. GitHub reports `createdAt: 2026-11-14T09:08:21Z` and `lastEditedAt: null`. Its recorded author-page/notes, arXiv metadata/history, OpenAlex citing-work, Crossref and formal-conjectures checks found no explicit resolution of this Section 5.3 sentence. MathDB returned 403; Semantic Scholar and the exact-ID Scholar search returned 429. Those inaccessible routes were not read. This is bounded eligibility evidence, not a worldwide absence or priority claim, and no new pre-probe search is claimed here.

The preserved [research-prereg-v1 comment](https://github.com/the-omega-institute/trureturing/issues/30346#issuecomment-6875035771) has identical creation and update timestamps, `2026-11-14T09:13:01Z`. It preserves the full event, both forecasts and the cutoff `2026-11-14T11:08:21Z`; the Tier and literature evidence are in the original issue body. Both public timestamps precede the supplied probe start `2026-11-14T09:14:40Z`.

The original bounded all-state repository screen identified [#14224](https://github.com/the-omega-institute/trureturing/issues/14224) and [#14385](https://github.com/the-omega-institute/trureturing/pull/14385) as the Conjecture 6.1 half-frequency work, and [#24397](https://github.com/the-omega-institute/trureturing/pull/24397) as different $q$-clause exposition. No owner of the Section 5.3 sentence was found in that recorded scope. The related `FORBIDDEN_WORD_STOPPING_FREQUENCY.md` concerns a different result; it supplies no corresponding extremal atom. These statements report the original eligibility record, not a new search or a complete census.

## Route

Reuse `ForbiddenWordCounting.omega` and `ForbiddenWordCounting.rho` without changing their native definitions. At $k=1$ both proposed words are `[true]`; the competitor `[false]` has the same length. The existing owner theorem `D5/S1/Words/Forbidden/BalancedBordersHalfFrequency.rho_singleton` gives $\rho_n^{[true]}=0$ and $\rho_n^{[false]}=1$ for every $n>0$. The candidate's private `singleton_tendsto` transfers these eventually constant native sequences to their real limits. If the claim held, its first maximizer conjunct would give limits $r,s$ with $s\le r$; uniqueness forces $r=0$ and $s=1$, contradicting $0<1$.

## Falsifier

The correspondence would fail if the source excluded length one or constant competitors, if $\rho$ meant the stopped statistic $q$, or if only a finite-$n$ inequality were established. The exact source domain includes these words, and the formal claim uses native `rho` and actual `Tendsto` limits. Both proposed maximizer clauses remain in the claim, even though contradicting the first at one allowed length suffices to refute their universal conjunction.

## Evidence

`D5/S1/Words/Forbidden/BonaMagaRicheyExtremalFrequency.result` has the literal type `Not claim`, with no extra mathematical hypotheses. The matching Scribe attaches exactly one typed `OpenProblemResolutionClaim` with this dossier's slug and `ResolutionKind.Refuted` to that result. The claim and all four public declaration truth anchors remain in its Blueprint.

The admission basis is `open-problem-resolution (#30346; Refuted)`. The result and its consumed private limit helper have `proof_shape: bind-only`; the helper's consumer is `result`. No escape witness or new general frequency theorem is claimed. The designated refutation result is exempt from four-slot escape registration. This dossier is a pre-freeze authoring surface: it asserts no first freeze, new frozen identity, successful admission or publication. The owner exposure remains private-only in origin and its existing frozen pin requires later canonical maintenance.

## Triage

Tier 1: a recent externally authored assertion explicitly lacking a proof in the source; settlement kind small-case refutation of its complete universal statement. No separate problem is counted for each length or proposed optimizer. The corresponding endpoint uses the later uncovered route, since the existing related theory has no corresponding extremal statement.

### What the settlement shows

- **Proved by `BonaMagaRicheyExtremalFrequency.result`:** the unrestricted $k\ge1$ assertion is false. At length one, forbidding either proposed word excludes every one; forbidding the competitor excludes every zero. `BalancedBordersHalfFrequency.rho_singleton` and the consumed private `singleton_tendsto` supply the exact positive-length values and native limits. The failure mechanism is the inclusion of this endpoint in a universal maximizer claim.
- **Open:** the proposed-maximizer assertions restricted to $k\ge2$, restricted to $k\ge3$, or restricted to nonconstant words. None is proved or refuted by this endpoint. A fixed-composition replacement and a classification of all optimizers also remain unresolved here; merely excluding this counterexample proves none of them.
- **Open as consequences of this settlement:** further claims using this universal extremal assertion need a separately established replacement. No other theorem of the source is refuted here. Conjecture 6.1's existing half-frequency settlement and the distinct $q$ questions do not follow from, and are not settled by, this refutation.

## ASSUMED-UNVERIFIED

Literature priority and absence of resolutions outside the original bounded accessible searches are unverified. The probe-start time is supplied by the assignment; GitHub independently supplies only the issue and comment timestamps above. The inaccessible search routes remain unverified. No all-length optimizer classification, corrected-domain extremal theorem or settlement of a $q$ or fixed-composition variant is claimed.
