---
bibkey: hanna2013derivativesubstitutioncongruences
authors: Paul D. Hanna
year: 2013
title: Derivative-substitution exponential generating functions A232694, A232695, A232696 and A232686
doi: null
url: https://oeis.org/A232694
claim: The nominated COMMENTS conjectures concern congruences of the factorial-normalized coefficients of four derivative-substitution exponential generating functions.
strata_touched:
  - D5/S1/Recurrence/Residue/HannaEGFMachinery
  - D5/S1/Recurrence/Residue/HannaA232694Congruences
  - D5/S1/Recurrence/Residue/HannaA232695Congruences
  - D5/S1/Recurrence/Residue/HannaA232696Congruences
  - D5/S1/Recurrence/Residue/HannaA232686Congruences
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A232694

Related source records: https://oeis.org/A232695, https://oeis.org/A232696,
https://oeis.org/A232686. OEIS records have no page numbering and no DOI or arXiv identifier.

## Source statements

### A232694

```text
%I A232694 #7 Dec 03 2013 20:49:42
%N A232694 E.g.f. A(x) satisfies: A'(x) = A(x*A'(x)^4) with A(0)=1.
%C A232694  CONJECTURES.
%C A232694 a(n) == 0 (mod 3) for n>=3.
%C A232694 a(n) == 1 (mod 8) for n>=0.
%e A232694 E.g.f.: A(x) = 1 + x + x^2/2! + 9*x^3/3! + 177*x^4/4! + 5601*x^5/5! +...
%O A232694 0,4
%A A232694 _Paul D. Hanna_, Nov 27 2013
```

### A232695

```text
%I A232695 #22 Dec 03 2013 20:44:17
%N A232695 E.g.f. A(x) satisfies: A'(x) = A(x*A'(x)^5) with A(0)=1.
%C A232695  CONJECTURES.
%C A232695 a(n) == 1 (mod 5) for n>=0.
%C A232695 a(n) == 0 (mod 2) for n>=4.
%C A232695 a(n) == 0 (mod 2^2) for n>=10.
%C A232695 a(n) == 0 (mod 2^3) for n>=18.
%C A232695 a(n) == 0 (mod 2^k) for n>=(8*k-6) for k>1.
%e A232695 E.g.f.: A(x) = 1 + x + x^2/2! + 11*x^3/3! + 266*x^4/4! + 10326*x^5/5! +...
%O A232695 0,4
%A A232695 _Paul D. Hanna_, Nov 27 2013
```

### A232696

```text
%I A232696 #11 Dec 03 2013 20:51:28
%N A232696 E.g.f. A(x) satisfies: A'(x) = A(x/A'(x)) with A(0)=1.
%C A232696  CONJECTURES.
%C A232696 a(n) == 0 (mod 2) for n>=4.
%C A232696 a(n) == 0 (mod 2^2) for n>=10.
%C A232696 a(n) == 0 (mod 2^3) for n>=18.
%C A232696 a(n) == 0 (mod 2^k) for n>=(8*n-6) for k>1.
%e A232696 E.g.f.: A(x) = 1 + x + x^2/2! - x^3/3! + 2*x^4/4! + 6*x^5/5! - 264*x^6/6! + 5370*x^7/7! +...
%O A232696 0,5
%A A232696 _Paul D. Hanna_, Nov 28 2013
```

### A232686

```text
%I A232686 #16 Dec 07 2013 12:29:18
%N A232686 E.g.f. A(x) satisfies: A'(x) = A(x*A'(x))^2.
%C A232686 CONJECTURES.
%C A232686 a(n) == 0 (mod 2) for n>=2.
%C A232686 a(n) == 0 (mod 2^2) for n>=4.
%C A232686 a(n) == 0 (mod 2^3) for n>=5.
%C A232686 a(n) == 0 (mod 2^k) for n>=(2*k-1), k>=3.
%C A232686 a(2*n) == 2^n (mod 2^(n+1)) for n>=0.
%e A232686 E.g.f.: A(x) = 1 + x + 2*x^2/2! + 14*x^3/3! + 196*x^4/4! + 4352*x^5/5! +...
%O A232686 0,3
%A A232686 _Paul D. Hanna_, Dec 03 2013
```

## Interpretation and scope

The coefficient a(n) is n! times the ordinary rational coefficient of x^n.
The initial coefficient is one in every displayed exponential series. The selected pairs
are modulo 3 and 8 for A232694, modulo 5 and 2 for A232695, modulo 2 and 4
for A232696, and modulo 2 and 4 for A232686. The other quoted conjectures
are outside these four propositions. The reciprocal equation is interpreted by formal
unit inversion, with derivative constant coefficient one.

## Evidence and literature boundary

The exact-coefficient experiment is in the private repository
the-omega-institute/trureturing-experiments, commit
e2566e824df32e3f308cd1b801ef82dd17fa64cf,
docs/reports/hanna-efg-congruences/check.py, SHA-256
14fa66db49524fd5b8ccbf45b2245d0a4813980bff076b1b0a855d869393f259.
The recorded command is `python3 check.py > output.txt`, exit 0. It checks
indices 0 through 300 and compares independent rational-series iteration through degree 12.
These finite calculations support the coefficient interpretation; they do not prove an unbounded congruence.
The all-index conclusions are repository derivations from integral recurrences and exact residuals.
Literature-screen completeness is ASSUMED-UNVERIFIED; no prior settlement was located
in the sources inspected for issues #21485, #21486, #21487 and #21488.
