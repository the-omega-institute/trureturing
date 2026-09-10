---
bibkey: sloane2003nonsquashing
authors: N. J. A. Sloane; James A. Sellers
year: 2003
title: On Non-Squashing Partitions
doi: 10.48550/arXiv.math/0312418
claim: Theorem 2 gives the distinct non-squashing partition recurrence; Corollary 4 gives parity rules, with equation (21) restricted to odd n at least 3.
strata_touched: []
license: citation-only
triage: anchor
---

# Distinct non-squashing partition counts

## Verified locator

doi: 10.48550/arXiv.math/0312418

url: https://arxiv.org/abs/math/0312418

The arXiv abstract page was retrieved on 2026-09-10 and supplies the title, both
authors, the submission date 2003-12-22, and the DOI above. The v1 PDF was opened
in attempt 1; its extracted pages 6–8 were read again in attempt 2. Theorem 2,
equations (11) and (14), is on pages 6–7. Corollary 4, equations (20)–(24) and its
proof, is on page 8. Other pages and external linked publications were not opened
in attempt 2 (ASSUMED-UNVERIFIED).

## Domain correction and kernel witness

Write B(n) for the number of distinct positive-part partitions of n such that,
in decreasing order, every part is at least the sum of its suffix. Equality is
allowed. The empty partition gives B(0)=1; the singleton gives B(1)=1.

The printed equation (21) states, without an exception, that for odd n,
B(n) is congruent to B(n−1)+1 modulo 2. At n=1 this would assert 1≡0.
The correct usable domain is odd n≥3, exactly matching the condition m≥1
in Theorem 2's formula B(2m+1)=B(2m)+1. This correction does not refute
the A110037 difference conjecture, whose domain starts at n=2.

The private Lean theorem `printed_odd_rule_false` in
`docs/reports/a110037-0910/BoundaryProbe.lean` gives the kernel witness by
specializing the printed assertion to n=1 and evaluating the direct finite
partition sets. The witness is retained in the attempt 2 proof record. It is
not used to justify freezing an unrelated result.

The m>0 condition printed before (24) is retained. Any use of its two
arithmetic progressions at m=0 must be justified separately, either from
Theorem 2 or from Corollary 4's final binary-digit characterization for m>0.
Corollary 3(i)'s phrase “adding 1” conflicts with (14)'s subtraction and
is not used.

## Formalization boundary

This note cites an established paper proof. It is not a Lean axiom or theorem,
and citing it does not by itself give a kernel proof of the corresponding
statement about the concrete finite partition sets. The attempt 2 report
records the search for an existing Lean declaration and the remaining input.
