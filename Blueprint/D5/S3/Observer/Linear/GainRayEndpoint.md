# The whole pure-M endpoint obstruction

## Abstract

The whole pure-M endpoint obstruction

EndpointRow(d,k,u,v,p) requires p.natDegree<=2d+1, p(1)=0, and for each j<=d the shift-zero Euler jets at phi and psi equal u and v respectively when j=k, and zero otherwise. The value at 1 is the separate drift-annihilation condition.

The first row has derivative proportional to (X-phi)^d(X-psi)^d. Reflection about 1/2 makes its endpoint sum twice its midpoint value. Strict monotonicity between the golden nodes and the zero at 1 force u(u+v)<0 unless both weights vanish. The last row factors as (X-phi)^d(X-psi)^d a(X-1); its exact top jets force u(u+v)>=0 for d>=1, including equality at d=1.

**Theorem 1.1 (Incompatible first and last row signs).**

Lean statement: `D5/S3/Observer/Linear/GainRayEndpoint.endpoint_jet_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayEndpoint.endpoint_jet_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d>=1, all real u,v and real polynomials f,g, EndpointRow(d,0,u,v,f) and EndpointRow(d,d,u,v,g) imply u=0 and v=0. No row polynomial or spectral output is assumed nonzero.

**Theorem 1.2 (No nonzero original pure-M universal identity through 2m reads).**

Lean statement: `D5/S3/Observer/Linear/GainRayEndpoint.pureM_universal_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayEndpoint.pureM_universal_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=1 and natural n with n+1<=2(d+1), let C be any Readout d (replicate n false) and ell any real linear functional on Mat. Suppose C times the all-ones history is zero, and for every auxiliary real matrix S and every beta:Coeff d, C applied to the vector with entries gain(d,beta)(i) trace(acquisition((replicate n false).take i) S) equals ell(S) beta. Then ell is the zero functional. The finite indices are the literal initial-inclusive history, so n=0 and every shorter pure-M endpoint are included. The auxiliary identity is the conclusion needed from universal collinearity; a separate countable covering argument must connect this obstruction to unrestricted adaptive palettes.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayEndpoint.endpoint_jet_obstruction`
- Truth anchor: `D5/S3/Observer/Linear/GainRayEndpoint.pureM_universal_obstruction`
- Dependency: [D5/S3/Observer/Linear/GainRayJets](GainRayJets.md)
