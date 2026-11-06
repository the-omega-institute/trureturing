---
bibkey: zhanghaobo2026pgmrefutation
authors: "Wenlin Zhang and Haobo / trureturing"
year: 2026
title: "An equiprobable mixed-state counterexample to the active-set PGM comparison"
doi: null
url: null
claim: "The existing three-state rational actual-density/POVM/CFC refutation, reused without a second proof."
strata_touched: []
license: citation-only
triage: anchor
---

# An equiprobable mixed-state counterexample to the active-set PGM comparison

The supplied two-page note is dated 9 October 2026 and has the literal byline
“Wenlin Zhang and Haobo / trureturing”. Its PDF has SHA256
`8955c3bcd1bbc9c595445d98a468968da89d7befbcf5234c06a07f5235fe2e44`.
No DOI, public URL, or license grant was supplied. The later new note's CC BY
4.0 grant does not apply here.

The actual canonical implementation is
`D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.lean`, particularly
`result : ¬ claim`. It retains the rational states, universal POVM dual bound,
every-optimum active-pair argument, and exact original-prior CFC scores. Its
reference to Cha and Lee's comparison is documented separately in
`cha2026structural.md`. The later implementation reuses this source and does not
claim the old refutation as a new outcome.
