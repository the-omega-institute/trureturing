# Shifted Euler interpolation and exact gain readout

## Abstract

Shifted Euler interpolation and exact gain readout

For a real shift s, euler(s) sends a polynomial p to X p derivative+s p. jet(s,j,p,x) evaluates its jth iterate at x. The shifts s=0 and s=1 represent D and D+1. They specify fixed linear readout coefficients; no acquisition clock is changed.

JetIndex(d) has a first Fin(d+1) block, a second Fin(d+1) block, and one final coordinate. jetMatrix(d,n,s,a,b,c) has entries (i+s)^j a^i in the first block, (i+s)^j b^i in the second, and c^i in the final row. jetMap is its linear action on n ordinary polynomial coefficients.

**Theorem 1.1 (Exact monomial jet identity).**

Lean statement: `D5/S3/Observer/Linear/GainRayJets.jet_ofFn`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayJets.jet_ofFn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real s,x, natural j,n and c:Fin n to the reals, jet(s,j,ofFn(n,c),x) is the sum over i:Fin n of c(i)(i+s)^j x^i. Initial index zero is included, with the ordinary convention 0^0=1.

**Theorem 1.2 (Triangular vanishing equivalence).**

Lean statement: `D5/S3/Observer/Linear/GainRayJets.jets_vanish_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayJets.jets_vanish_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real s,x with x nonzero, natural d and polynomial p, all shifted Euler jets of orders 0 through d vanish at x if and only if all ordinary iterated derivatives of orders 0 through d vanish there. No degree or nonzero polynomial hypothesis is needed.

**Theorem 1.3 (Exact leading derivative factor).**

Lean statement: `D5/S3/Observer/Linear/GainRayJets.jet_leading`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayJets.jet_leading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real s,x, natural n and polynomial p whose ordinary derivative jets of every order j<n vanish at x, jet(s,n,p,x)=x^n times the nth ordinary derivative evaluated at x. This statement also permits x=0.

**Theorem 1.4 (Whole multiple-root divisibility).**

Lean statement: `D5/S3/Observer/Linear/GainRayJets.jets_root_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayJets.jets_root_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real s,x with x nonzero, natural d and polynomial p, vanishing shifted Euler jets of every order 0 through d imply (X-C(x))^(d+1) divides p. The zero polynomial and lower actual degrees are included.

**Theorem 1.5 (Attainment and uniqueness of all square jet data).**

Lean statement: `D5/S3/Observer/Linear/GainRayJets.jetMap_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayJets.jetMap_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d and real s,a,b,c, assume a and b are nonzero and the three nodes are pairwise distinct. Then jetMap(d,2(d+1)+1,s,a,b,c) is bijective. Both sets of d+1 shifted Euler jets and the separate value can be prescribed arbitrarily. The proof combines the three coprime root factors in the homogeneous kernel, compares their degree with the coefficient bound, and uses equal finite dimensions for surjectivity.

exactBetaReadout(d) is a real (d+1) by (2(d+1)+1) matrix on the History of the literal word replicate (2(d+1)) false. Its kth coefficient polynomial has value zero at 1 and shifted Euler jets at shift zero equal to the kth Kronecker coordinate at both golden nodes. The square interpolation system supplies every row. Matrix entries depend on d and the fixed atoms only.

Multiplying these rows by the original readings gives alpha(P) beta_k+eta(P) beta_k. Trace-one normalization makes this beta_k. The drift cancels because each row sums to zero. No division by the gain, a sample, a source weight or an observed quantity occurs.

**Theorem 1.6 (Exact whole coefficient vector).**

Lean statement: `D5/S3/Observer/Linear/GainRayJets.pureM_exact_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayJets.pureM_exact_beta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d and every original W:World d, exactBetaReadout(d) multiplied by readings W (replicate (2(d+1)) false) equals W.coeff exactly. There are exactly 2(d+1) separate M actions and 2(d+1)+1 initial-inclusive reads. Arbitrary drift, all coefficient signs, sampled roots, lower actual degree, eta=0 and negative eta remain in scope. Since World carries W.coeff nonzero, the successful gain-ray scalar is 1. The singleton containing this fixed matrix is countable and independent of history.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayJets.jetMap_bijective`
- Truth anchor: `D5/S3/Observer/Linear/GainRayJets.jet_leading`
- Truth anchor: `D5/S3/Observer/Linear/GainRayJets.jet_ofFn`
- Truth anchor: `D5/S3/Observer/Linear/GainRayJets.jets_root_dvd`
- Truth anchor: `D5/S3/Observer/Linear/GainRayJets.jets_vanish_iff`
- Truth anchor: `D5/S3/Observer/Linear/GainRayJets.pureM_exact_beta`
- Dependency: [D5/S3/Observer/Linear/GainRayEvaluation](GainRayEvaluation.md)
- Dependency: [D5/S3/Observer/Linear/GainRaySpectral](GainRaySpectral.md)
