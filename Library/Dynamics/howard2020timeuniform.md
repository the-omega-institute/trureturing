---
bibkey: "howard2020timeuniform"
authors: "Steven R. Howard; Aaditya Ramdas; Jon McAuliffe; Jasjeet Sekhon"
year: 2020
title: "Time-uniform Chernoff bounds via nonnegative supermartingales"
doi: "10.1214/18-PS321"
url: "https://arxiv.org/abs/1808.03204v8"
claim: "Ville's inequality bounds the probability that a nonnegative supermartingale ever crosses a positive fixed level by its initial expectation divided by that level."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Time-uniform Chernoff bounds via nonnegative supermartingales

Probability Surveys 17 (2020). Lemma 1, equation (2.11), of the inspected
arXiv:1808.03204v8 states Ville's inequality; section 6.1 supplies its proof.
For a nonnegative supermartingale with initial expectation at most one,
the probability of crossing `1/eta` at any time is at most `eta`.
The authors explicitly attribute this maximal inequality to Ville (1939).

The maximal inequality and its use with mixture martingales are
`literature-attested`. In the parity-kernel result, the additional
`repo-derived` structure is that a reverse likelihood defined relative to
uniform reference observations is a martingale under every forward kernel
in the entire zero-parity-mean family, by the identity `P_c P_b = Pi`.
The resulting direction test assumes a fixed unknown positive spike in a
known parity block with known amplitude. Its guarantee concerns error
probability and almost-sure stopping, not an optimal expected stopping time.
