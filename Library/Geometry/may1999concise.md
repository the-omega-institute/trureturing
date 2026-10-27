---
bibkey: may1999concise
authors: J. P. May
year: 1999
title: A Concise Course in Algebraic Topology
doi: null
url: https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf
claim: "A homotopy equivalence under A between cofibrations A→X and A→Y is a cofiber homotopy equivalence, with both inverse homotopies relative to A."
strata_touched:
  - D5/S3/Geometry/SingletonRetractionBasedInverse
license: citation-only
triage: anchor
---

# Cofiber homotopy equivalence and prescribed traces

## Locator

Source: https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf

Chapter 6, section 5, printed pp. 46–48 (physical PDF pages 54–56),
contains two unnumbered propositions. The first, on p. 46, assumes
cofibrations i:A→X and j:A→Y, a map f:X→Y satisfying f∘i=j, and that
f is an underlying homotopy equivalence. It concludes that f is a cofiber
homotopy equivalence: there is g:Y→X with g∘j=i and homotopies
g∘f≃id and f∘g≃id relative to A. Its proof on pp. 46–47 adjusts an
ordinary inverse by homotopy extension and corrects a homotopy between
homotopies. The second proposition, stated on p. 47 and proved on p. 48,
treats a commuting pair of homotopy equivalences of pairs; its proof
includes a three-stage correction of the right inverse homotopy.

For A a point, the first proposition supplies the classical based inverse
theorem for an already based homotopy equivalence. The repository module
uses actual singleton-cylinder retractions and constructs the relative
square retraction explicitly. Its full `based_inverse` theorem starts
with an unbased f, an ordinary homotopy inverse with both homotopies, and
a prescribed path gamma from f(x) to y. It constructs a based equivalence
E and a homotopy A from f to E.forward with A(t,x)=gamma(t) for every t.
This exact prescribed-trace statement is a repository construction
refinement, not a verbatim statement of either proposition. The
repository-derived definitions and full refinement acknowledge the
classical source; this attribution makes no novelty claim.
