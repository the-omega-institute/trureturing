# The real Kilbas-Saigo function

## Abstract

Kilbas-Saigo series and hyperbolic bounds on the negative real axis.

**Definition 1.1 (Gamma product coefficients).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Defs.ksCoeff`

*Formalization.* `D5/S3/Analytic/KilbasSaigo/Defs.ksCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of order n is the product, for k from zero to n minus one, of Gamma(1+alpha(k m+l)) divided by Gamma(1+alpha(k m+l+1)). The empty product is one.

**Definition 1.2 (The defining real series).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Defs.kilbasSaigo`

*Formalization.* `D5/S3/Analytic/KilbasSaigo/Defs.kilbasSaigo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real parameters alpha, m, l and real argument z, the function is the sum over natural n of the coefficient of order n times z to the power n.

**Definition 1.3 (Two hyperbolic bounds).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Defs.claim`

*Formalization.* `D5/S3/Analytic/KilbasSaigo/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For 0<alpha<=1, m>0, l>m-1/alpha and x>=0, the value at -x lies between 1/(1+Gamma(1+alpha(l-m))/Gamma(1+alpha(l-m+1)) times x) and 1/(1+Gamma(1+alpha l)/Gamma(1+alpha(1+l)) times x).

## References

- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Defs.claim`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Defs.kilbasSaigo`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Defs.ksCoeff`
