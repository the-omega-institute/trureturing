# A support-state prerequisite for original affine identification

## Abstract

Finite original-table support obstruction on an arbitrary real normed carrier.

E is any real normed vector space, including incomplete spaces. S is a symmetric real bilinear map E x E -> E, u is its unit, and norm(S(x,x)) = norm(x)^2 for every original x. D is the same total function E x E -> E throughout. P is a set of real linear readings separating original elements. P2(S,D,P) means that every reading in P makes the actual directed two-table positive semidefinite: its diagonal is alpha(S(a,a)), alpha(S(b,b)), and its off-diagonal entries are alpha(S(a,b))-i alpha(D(a,b)) and alpha(S(b,a))-i alpha(D(b,a)). Readings are not normalized in P2; zero, unequal and subnormalized masses remain permitted.

PB(S,D) is the complete original element equality for every a,b,c in E. With nu = D(a,b)-S(a,c) and omega = S(a,b)+D(a,c), it states D(b+nu,c+omega)-D(b-nu,c-omega) = -2 S(b,nu)-2 S(c,omega). No input sum or scalar is expanded through D. OriginalSupportStage(E,S,D,P,u) in the displayed formula means exactly P2, PB, symmetry and bilinearity of S, S(u,x)=x, the square norm identity, and the stated separation by P.

**Theorem 1.1 (Support readings annihilate the second original label).**

$$\forall E \in \mathit{RealNormedSpaces},\; \forall S \in \operatorname{RealBilinearMaps}\left(E\right),\; \forall D \in \operatorname{TotalBinaryMaps}\left(E\right),\; \forall P \in \operatorname{ReadingFamilies}\left(E\right),\; \forall u \in E,\; \operatorname{OriginalSupportStage}\left(E, S, D, P, u\right) \Rightarrow \left(\forall mu \in R,\; \forall b \in E,\; \forall alpha \in P,\; \operatorname{NormalizedContractive}\left(\mathit{alpha}, u\right) \Rightarrow \left(\forall Z \in R,\; \left(Z \ne 0 \land \left(\operatorname{alpha}\left(\operatorname{D}\left(\mathit{mu} \cdot u, b\right)\right) = Z \land \operatorname{abs}\left(Z\right) = \operatorname{norm}\left(\operatorname{D}\left(\mathit{mu} \cdot u, b\right)\right)\right)\right) \Rightarrow \left(\operatorname{alpha}\left(\operatorname{S}\left(b, \operatorname{D}\left(\mathit{mu} \cdot u, b\right)\right)\right) = 0 \land \operatorname{alpha}\left(b\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalUnitSupport.support_unit_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real mu and original b, write h = D(mu u,b). Choose alpha in P with alpha(u)=1 and abs(alpha(x)) <= norm(x) for every original x. NormalizedContractive(alpha,u) denotes precisely these two requirements. For every nonzero real Z with alpha(h)=Z and abs(Z)=norm(h), both alpha(S(b,h)) and alpha(b) vanish. No state attaining a norm is constructed or assumed to be an actual physical preparation. The theorem quantifies over each supplied mathematical support reading.

Positivity of the actual two-table gives the determinant bound with its real Jordan term retained. Separation then makes all scalar-unit input pairs have zero D. Let B(x,y)=alpha(S(x,y)) and w=h-Zu. Contractivity and the square norm identity give B(w,w)=0. Nonnegativity of B(x+t w,x+t w), through the real quadratic discriminant, gives B(w,x)=0 for every x; this is a statement about the known Jordan form and does not descend D to a quotient.

Set k=mu Z/(1+mu^2), nu=h-mu k u and omega=mu b. The actual PB labels a=mu u, b=b, c=ku have inner values h and zero. Their outer pairs are rplus=b+nu, splus=ku+omega and rminus=b-nu, sminus=ku-omega. Exactly splus=mu rplus-mu w and sminus=-mu rminus-mu w. Since w is null for B, both actual outer Gram determinants are zero, so P2 reads both unknown outer D values as zero. PB then gives alpha(S(b,h))=0. The support identity makes this Z alpha(b), and Z nonzero gives alpha(b)=0. All labels are finite original linear combinations; no regularity or output closure of D enters.

This is the support-zero-face inference of small-window Unit Bridge 99.2, an upstream component of the general unit-row route used by central 16.2 and 36.1. Its interpretation on a JB original candidate still requires the recovered same S and norm, the exact cone extension of P2 to mathematical readings, and a norm-support state with the listed properties. It does not establish those recovery and state-existence bridges.

The full central target remains: for every original x,y in the actual U=span(h,k,j), j=D(h,k), and all real T,s,t, D(x,Tu+y)=x cross y and D(su+x,tu+y)=x cross y. Pure response identification and the generated frame of central 63.1, transverse unit transport of 36.1, and general original SO(2) invariance must be proved on this same E before that target can use them. This theorem supplies none of them as a premise or conclusion. E is not replaced by a four-dimensional carrier; its own JB completion need not fill the ambient selfadjoint part. All zero and dependent target branches and the full original quantum-source and consumer conditions remain part of that larger obligation. Mathematical readings do not supply actual preparations, instruments, joint systems, legal histories, physical clocks, energy or action constants.

## References

- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalUnitSupport.support_unit_obstruction`
