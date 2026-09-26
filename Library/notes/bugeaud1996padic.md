---
bibkey: bugeaud1996padic
authors: Yann Bugeaud; Michel Laurent
year: 1996
title: "Minoration effective de la distance p-adique entre puissances de nombres algebriques"
doi: 10.1006/jnth.1996.0152
url: https://doi.org/10.1006/jnth.1996.0152
claim: Explicit two-term p-adic logarithm estimate, used to give an absolute exponent cutoff for the entire Erdos699 3-p column family.
strata_touched: []
license: citation-only
triage: anchor
---

# Exact external input for the uniform 3-p continuation

Research issue #9670, continuing PR #9769.
Complete application and executable finite certificate:
`tools/scripts/agent/openproblem/erdos699-uniform-three-prime-check.py`.
The previous normalized-cubic and single-row deductions remain separate dependencies.
No Lean truth declaration or complete Erdos699 resolution is registered here.

## Source actually read

Original: Y. Bugeaud and M. Laurent, Journal of Number Theory61(2),311-342
(1996), Corollary1, DOI above. Its full original proof was not retrieved.
The explicit formulation actually inspected is Lemma2.6 of:
Herbert Batte, Mahadi Ddamulira, Juma Kasozi and Florian Luca,
*On a problem of Pillai involving S-units and Lucas numbers*,
Periodica Mathematica Hungarica91 (2025),53-87.
https://doi.org/10.1007/s10998-025-00649-x
https://link.springer.com/article/10.1007/s10998-025-00649-x
The published HTML and parsed PDF printed page58 were read. PDF screenshot
requests for both the journal version and arXiv:2401.06555 returned cache
errors. No successful visual page verification is claimed. The arXiv
version labels the corresponding estimate Lemma2.2; numbering differs.

## Rational-number specialization, with every parameter retained

Let gamma1,gamma2 be multiplicatively independent rational p-units, and
B1,B2 positive integers. Take H_i>=max(h(gamma_i),log p), where the height
of a reduced rational a/b is log(max(abs(a),abs(b))). Let g be the common
positive residue period, and put

    Eprime=B1/H2+B2/H1,
    E=max(log(Eprime)+log(log(p))+0.4,10,10*log(p)).

The stated bound, specialized to number-field degree1, is

    vp(gamma1^B1*gamma2^B2-1)
    <=24*p*g/((p-1)*log(p)^4)*E^2*H1*H2.

Only rational numbers are used in this application, so algebraic local
valuation and field-degree conventions do not enter. A different
specialized theorem requiring p not to divide B1 is NOT being applied.
Here B2=1, while B1 is divisible by3.

## Actual application and novelty boundary

Put A=D-x, gamma1=4, gamma2=(A/x)^2, p=3, g=1,
B1=N-1, B2=1, H1=log4, H2=2logD. Both bases are1 mod3 and their
3-adic valuations are zero. The complete multiplicative-dependence case
is separately excluded by elementary lifting and an exponential inequality.
For the independent case, the original integer ratio supplies

    alpha+s+1 <= v3(gamma1^(N-1)*gamma2-1).

For N>=10^6, the explicit theorem then gives s<70*(logN+1)^3.
A separately proved integer cofactor bound gives
2^N<32*D^5*3^(2s)+1, with D<=3*(N-1)/2. Together they force N<10^6.
The entire resulting finite necessary-square domain is exhausted by the
committed checker. The external theorem itself is not reproved by that
program or claimed as an original project result.

This establishes a written closure of every j=2^b*3^s*p^t column for i=3,
conditional only on the explicitly inherited mathematical lemmas and this
classical input in the ordinary theorem-dependency sense. Independent
review and complete Lean formalization remain outstanding. General
multi-prime columns and original indices4..324 are not closed by this file.
