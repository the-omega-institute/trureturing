---
bibkey: "daskalakis2018testing"
authors: "Constantinos Daskalakis; Nishanth Dikkala; Nick Gravin"
year: 2018
title: "Testing Symmetric Markov Chains From a Single Trajectory"
doi: null
url: "https://proceedings.mlr.press/v75/daskalakis18a.html"
claim: "The Bhattacharyya affinity between two Markov path laws is the initial affinity vector multiplied by a power of the entrywise geometric-mean transition matrix and the all-one vector."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Testing Symmetric Markov Chains From a Single Trajectory

Proceedings of Machine Learning Research 75, 385–409 (COLT 2018).
Lemma 5, equation (5), on PDF page 8 states the path-affinity recursion;
Appendix B proves it. That lemma permits general Markov chains and initial
laws. The symmetry assumptions of the paper's testing algorithms are not
assumptions of the recursion.

The authors attribute the recursion to Dimitri Kazakos, *The Bhattacharyya
distance and detection between Markov chains*, IEEE Transactions on Information
Theory 24(6), 747–754 (1978), DOI `10.1109/TIT.1978.1055967`.
The inspected primary statement is Lemma 5 of the 2018 paper.

The matrix recursion is `literature-attested`. The parity kernel's rank-four
factorization, two-statistic quartic, and single-spike cubic are `repo-derived`
specializations. Exact Bayes error exponents additionally require a matching
lower bound; affinity alone supplies only bounds on the error.
