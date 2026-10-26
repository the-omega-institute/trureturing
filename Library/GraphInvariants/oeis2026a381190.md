---
bibkey: oeis2026a381190
authors: Eric W. Weisstein; Joerg Arndt; Peter Luschny; Emily Egolf; Veronika Furst
year: 2026
title: "OEIS A381190, connected minimal dominating sets in the n-trapezohedral graph"
doi: null
url: https://oeis.org/A381190
claim: "Conjectured g.f.: -2*x^3*(4*x^5 + 8*x^4 + 4*x^3 - 9*x^2 - 8*x - 3)/(x^3 + x^2 - 1)^2."
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries
license: citation-only
triage: anchor
---

# OEIS A381190 and the trapezohedral graph

The entry is named “Number of connected minimal dominating sets in the n-trapezohedral graph.” Its sequence author is Eric W. Weisstein. The formula line reads:

> Conjectured g.f.: -2 * x^3 * (4*x^5 + 8*x^4 + 4*x^3 - 9*x^2 - 8*x - 3) / (x^3 + x^2 - 1)^2.

The formula is attributed to Joerg Arndt. Revision 15 records Arndt's review, while revision 16 records approval by Peter Luschny. Arndt is the conjecture/formula author in this record; Luschny is the approver of revision 16.

The primary graph definition is Egolf and Furst, *On the minimum number of distinct eigenvalues of triangle-free strongly regular graphs*, arXiv:2502.05031v1, Definition 3.6:

> An n-trapezohedral graph T_n is a graph on 2n+2 vertices in which 2n vertices comprise an outer cycle C_{2n} = (a_0, b_0, a_1, b_1, ..., a_{n-1}, b_{n-1}, a_0) and the two remaining vertices α, β satisfy N(α) = {a_0, ..., a_{n-1}} and N(β) = {b_0, ..., b_{n-1}}.

The formalization uses the actual labelled subsets, closed domination, inclusion minimality over every proper subset independently of connectivity, and induced connectedness. It counts each labelled subset once and uses the ordinary formal series with the source offset beginning at n=3.

## Verified locator

- URL: https://oeis.org/A381190
- Primary graph source: https://arxiv.org/abs/2502.05031v1, Definition 3.6
- Source authors: Emily Egolf; Veronika Furst
- Formula author: Joerg Arndt
- Revision-16 approver: Peter Luschny
