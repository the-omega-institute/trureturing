---
bibkey: mathlib2026shearpowers
authors: The mathlib community
year: 2026
title: Integer powers of the modular translation matrix
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean
claim: Powers of the upper unit shear have upper-right entry equal to the exponent; transposition gives the lower unit shear formula.
strata_touched:
  - D5/S3/Observer/TraceFibers/FixedFiberPairModulus
license: Apache-2.0
triage: anchor
---

# Unit shear powers

## Verified locator

https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean

`ModularGroup.coe_T_zpow` states that the integer power of the modular
translation matrix has rows `(1,n)` and `(0,1)` for every integer exponent `n`.
Natural exponents and the integer-to-real matrix homomorphism give the real
upper shear formula. `Matrix.transpose_pow` gives the corresponding lower
shear formula with rows `(1,0)` and `(n,1)`.

Keith Conrad, *SL2(Z)*, Section 1, page 1, also states the displayed formula
for powers of the matrix `T`:
https://kconrad.math.uconn.edu/blurbs/grouptheory/SL(2,Z).pdf

The Fibonacci action matrices satisfy `JM=T` and `MJ=T.transpose`.
These identities specialize the standard shear formulas; they do not supply
the fixed-fiber scalar and matrix supremum estimates.
