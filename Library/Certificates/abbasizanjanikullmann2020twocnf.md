---
bibkey: abbasizanjanikullmann2020twocnf
authors: "Hoda Abbasizanjani and Oliver Kullmann"
year: 2020
title: "Classification of minimally unsatisfiable 2-CNFs"
doi: 10.48550/arXiv.2003.03639
url: https://arxiv.org/abs/2003.03639v1
claim: "Section 4 identifies the minimally unsatisfiable family U^0_{n,i}; its n=5, i=3 member is the Boolean obstruction forced by the six semiprime packets."
strata_touched:
  - D5/S3/Arith/Covering/SemiprimeDivisorRepairRefutation
license: citation-only
triage: anchor
---

# A six-clause Boolean obstruction

The inspected primary source is arXiv:2003.03639v1, Section 4, printed
pages 5--6. It defines

\[
M=\{\{-1,2\},\ldots,\{-(n-1),n\}\},\qquad
U^0_{n,i}=M\cup\{\{1,i\},\{-n,-i\}\}
\]

for \(n\ge3\) and \(2\le i\le(n+1)/2\), as a family of minimally
unsatisfiable 2-CNFs of deficiency one. Signed integers denote literals.
For \(n=5,i=3\), put \((1,2,3,4,5)=(y,z,x,u,v)\). The six clauses are

\[
(x\lor y),\quad(\neg y\lor z),\quad(\neg z\lor x),\quad
(\neg x\lor u),\quad(\neg u\lor v),\quad(\neg v\lor\neg x).
\]

In the semiprime repair model, the five Boolean variables assert that the
respective prime phases modulo \(5,7,11,13,17\) equal one. A phase equal
to zero implies the corresponding Boolean negation. Other residues remain
allowed, so the arithmetic endpoint constraints imply these Boolean clauses;
they are not claimed equivalent to them for arbitrary phase assignments.

The source attributes this family to Chvatal and Reed, *Mick gets some
(the odds are on his side)*, FOCS 1992, DOI
`10.1109/SFCS.1992.267789`. This historical attribution is taken from the
inspected paper, not from an independently inspected copy of that article.

The Boolean obstruction is established literature. Its minimality is
clause-set minimality, not minimality of the arithmetic packet union or
donor bank. The relative-density reduction from arbitrary output residues
to whole-child divisor service is a separate arithmetic argument. No source
text or third-party Lean code is vendored, and no priority claim is made
for the arithmetic realization.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2003.03639
- Inspected version: https://arxiv.org/abs/2003.03639v1
- Primary text: https://arxiv.org/pdf/2003.03639v1
