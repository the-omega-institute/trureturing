---
bibkey: yoshida2010fiskbranden
authors: Rintaro Yoshida
year: 2010
title: "On some questions of Fisk and Brändén"
doi: 10.48550/arXiv.1005.4218
url: https://arxiv.org/abs/1005.4218v1
claim: "Open Problem 5 asks whether the coefficient transform a_k^2-a_{k-r}a_{k+r} preserves positive rapidly decreasing sequences."
strata_touched:
  - D5/S0/Certificates/YoshidaRapidDecreaseRefutation
license: citation-only
triage: anchor
---

# Yoshida, On some questions of Fisk and Brändén

## Verified locator

DOI: 10.48550/arXiv.1005.4218

Source: https://arxiv.org/abs/1005.4218v1

The quotations are from the numbered pages of the v1 PDF,
https://arxiv.org/pdf/1005.4218v1. The journal version has DOI
10.1080/17476933.2011.603418; its full text is not the source of these quotations.

## Source statements

Definition 8, page 3: “and $a_j=0$ if $j\notin\{0,1,\ldots, n\}$.”
For an infinite coefficient sequence, negative indices are zero-extended.

Definition 29, page 10: “A sequence of positive real numbers
$\{s_k\}_{k=0}^\infty$ is called rapidly decreasing, if the sequence satisfies the
following condition
$s_k^2\ge\alpha^2s_{k-1}s_{k+1}, \text{ for } \alpha\ge\max \{2, \frac{\sqrt{2}}{2}\left(1+\sqrt{1+s_1}\right)\}.$”

Open Problem 5, page 11: “Let $f(x)=\sum_{k=0}^\infty a_k x^k$ where
$\{a_k\}_{k=0}^\infty$ is a rapidly decreasing sequence. If
$S_r[f(x)]=\sum_{k=0}^\infty (a_k^2-a_{k-r}a_{k+r}) x^k:=\sum_{k=0}^\infty b_k x^k$,
is it true that $\{b_k\}_{k=0}^\infty$ is a rapidly decreasing sequence?”

## Coefficient interpretation

The coefficient sequence is a function from the natural numbers to the reals.
Rapid decrease requires positivity at every index and a single real parameter
above the displayed threshold satisfying all adjacent inequalities at positive
indices. The transform uses integer shifted indices and zero at negative indices.
The question quantifies over all positive natural r. The explicit existence
conjunct records the source's implicitly specified input sequence.

The concrete sequence $a_k=48^k/32^{\binom{k}{2}}$ and r=1 refute this coefficient
closure assertion. Entire-series convergence, the full parameter family, and
Laguerre-Pólya preservation are outside the formalized conclusion.

## Literature boundary

The literature screen recorded in issue #23414 is partial. The journal full text,
Yoshida's dissertation, and the identified Karp and Zhu citing papers remain
unread. Exhaustiveness and absence of an earlier settlement are
ASSUMED-UNVERIFIED; no originality claim follows from that screen.
