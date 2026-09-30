# Erdős 699 shared exponent cap

This note isolates the exact arithmetic certificate used by the 11-23
endpoint configuration in the continuation of Draft PR #9769. It records a
finite modular calculation, not the full Erdős 699 statement.

The base-two residues are

\[
  2^8\equiv3\pmod {11},\qquad 2^8\equiv3\pmod {23},\qquad
  2^{10}\equiv 1+5\cdot11\pmod {121},
\]

and the exact returns are

\[
  2^{110}\equiv1\pmod {121},\qquad
  2^{10}\equiv1\pmod {11},\qquad
  2^{11}\equiv1\pmod {23}.
\]

No positive multiple of 10 smaller than 110 is a return modulo 121. The
four second-lift rows in the written 11-23 argument require, for one common
exponent `N`, respectively

\[
 (N\bmod110,N\bmod11)\in
 \{(0,1),(22,4),(1,0),(23,3)\}.
\]

Each pair is impossible because reduction modulo 110 fixes the reduction
modulo 11. The Lean theorem records this exact finite obstruction. It does
not assert that the inherited normal-form or mixed-support hypotheses hold,
and it does not close the unrestricted Erdős 699 problem.
