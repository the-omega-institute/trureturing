# A support-state prerequisite for original affine identification

## Abstract

Finite original-table support obstruction on an arbitrary real normed carrier.

E is any real normed vector space, including incomplete spaces. S is a symmetric real bilinear map E x E -> E, u is its unit, and norm(S(x,x)) = norm(x)^2 for every original x. D is the same total function E x E -> E throughout. P is a set of real linear readings separating original elements. P2(S,D,P) means that every reading in P makes the actual directed two-table positive semidefinite: each entry at labels v,w is alpha(S(v,w))-i alpha(D(v,w)), including both unknown diagonal responses. Hermitian positivity itself annihilates the diagonal D readings. Readings are not normalized in P2; zero, unequal and subnormalized masses remain permitted.

PB(S,D,P) is the complete original balance for every reading alpha in P and every a,b,c in E. With nu = D(a,b)-S(a,c), omega = S(a,b)+D(a,c), and Qalpha(v,w)=alpha(S(v,v))+alpha(S(w,w))+2 alpha(D(v,w)), it states Qalpha(b+nu,c+omega)=Qalpha(b-nu,c-omega). Expanding only the known S and using separation derives the element equality D(b+nu,c+omega)-D(b-nu,c-omega) = -2 S(b,nu)-2 S(c,omega). No input sum or scalar is expanded through D. OriginalSupportStage(E,S,D,P,u) in the displayed formula means exactly P2, PB, symmetry and bilinearity of S, S(u,x)=x, the square norm identity, and the stated separation by P.

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

**Theorem 1.2 (Nonzero unit support excludes the closed semidefinite boundary).**

$$\forall E \in \mathit{RealNormedSpaces},\; \forall S \in \operatorname{RealBilinearMaps}\left(E\right),\; \forall D \in \operatorname{TotalBinaryMaps}\left(E\right),\; \forall P \in \operatorname{ReadingFamilies}\left(E\right),\; \forall u \in E,\; \forall C \in \operatorname{Subsets}\left(E\right),\; \left(\operatorname{OriginalSupportStage}\left(E, S, D, P, u\right) \land \operatorname{ConeExact}\left(C, P\right)\right) \Rightarrow \left(\forall mu \in R,\; \forall b \in E,\; \forall beta \in \operatorname{RealLinearReadings}\left(E\right),\; \forall Z \in R,\; \operatorname{PositiveNormalizedContractiveNonzeroSupport}\left(\mathit{beta}, C, u, \operatorname{D}\left(\mathit{mu} \cdot u, b\right), Z\right) \Rightarrow \left(\mathit{mu} \ne 0 \land \left(\forall t \in R,\; \operatorname{abs}\left(t\right) < \operatorname{norm}\left(b - t \cdot u\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalUnitSupport.positive_support_unit_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the entire original support stage, and let C be any set accurately determined by P: x belongs to C if and only if alpha(x) is nonnegative for every alpha in P. The supplied beta is any real linear mathematical reading nonnegative on C, with beta(u)=1 and abs(beta(x))<=norm(x). It need not belong to P. For h=D(mu u,b), retain every nonzero support requirement beta(h)=Z, abs(Z)=norm(h), Z nonzero. The conclusion is mu nonzero and abs(t)<norm(b-tu) for every real t. In particular no such nonzero support realization exists when mu=0, b=0, or norm(b-tu)<=abs(t) for even one real t; equality is included in the excluded boundary.

For each complex two-column z, form the original element Wz from the squared moduli of its coefficients multiplying S(a,a), S(b,b), twice their real overlap multiplying S(a,b), and twice their imaginary overlap multiplying D(a,b). Original Hermitian P2 and separation give the same D's skew symmetry. Every original reading of Wz is its nonnegative actual table quadratic value, so exactness puts Wz in C. Positivity of beta then proves the full directed P2 table for beta, including arbitrary original labels and unknown diagonal responses. The original finite-difference equality also gives PB for every real linear reading. These statements neither descend D nor require any output subspace closure.

Apply the existing support obstruction to the whole positive dual of C; original P is a subset, so separation is retained. This gives beta(b)=0. If norm(b-tu)<=abs(t), contractivity and the square norm identity bound beta((b-tu)^2) by t^2. Expanding the known Jordan product and using beta(b)=0 gives beta(b^2)<=0. P2 for the original pair (mu u,b) then gives Z^2<=mu^2 beta(b^2)<=0, contradicting Z nonzero. This is a test of the nonzero support telescope, not a zero-output witness substituted into it.

The later unit_row_semidefinite theorem proves the positive/negative-to-ball implication and constructs its support reading from the original order-unit data. Recovery of that same Jordan/order-norm stage from the full original A1-A3 remains a separate unpaid original-source bridge. The general nonzero support telescope outside these balls remains unresolved here: no complete nonzero model and no general impossibility proof is supplied. This proves a necessary obstruction and the exact-cone reading bridge, not all unit rows or the transverse row of central 36.1. The complete original central 76.2 and 77.1 remain open with the same E, cone, D, generated U, all zero and dependent branches, and all source and quantum-consumer conditions. The unfinished four-slot audit is tracked in issue 28178.

**Theorem 1.3 (Original unit rows vanish on the closed semidefinite norm balls).**

$$\forall E \in \mathit{RealNormedSpaces},\; \forall S \in \operatorname{RealBilinearMaps}\left(E\right),\; \forall D \in \operatorname{TotalBinaryMaps}\left(E\right),\; \forall P \in \operatorname{ReadingFamilies}\left(E\right),\; \forall A \in \operatorname{ConeUnitData}\left(E\right),\; \left(\operatorname{OriginalSupportStage}\left(E, S, D, P, \operatorname{unit}\left(A\right)\right) \land \left(\operatorname{ConeExact}\left(\operatorname{cone}\left(A\right), P\right) \land \operatorname{OriginalOrderNorm}\left(A\right)\right)\right) \Rightarrow \left(\forall mu \in R,\; \forall b \in E,\; \forall t \in R,\; \operatorname{norm}\left(b - \operatorname{smul}\left(t, \operatorname{unit}\left(A\right)\right)\right) \le \operatorname{abs}\left(t\right) \Rightarrow \operatorname{D}\left(\operatorname{smul}\left(\mathit{mu}, \operatorname{unit}\left(A\right)\right), b\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalUnitSupport.unit_row_closed_ball` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here A is the original closed salient convex cone with its interior unit on the same real normed E; its constructed order norm equals the given norm at every x. Original P accurately determines this cone and separates E. S is the same symmetric unital bilinear product with the square norm identity, and the same total D satisfies the whole original P2 and PB. For every real mu,t and every original b satisfying norm(b-tu)<=abs(t), the conclusion is D(mu u,b)=0. OriginalOrderNorm in the displayed formula means precisely these cone data and equality of the constructed order norm with the original norm. No support state is assumed in this theorem.

If that actual output were nonzero, OrderUnitNorm.Data.positive_norm_support constructs a positive normalized norm-support reading on all original E. The exact-cone bridge makes its P2/PB legitimate. positive_support_unit_boundary then contradicts the given closed-ball inequality. This includes t=0, b=0, mu=0, and equality at either semidefinite boundary. The original E remains arbitrary and possibly incomplete; there is no replacement by a four-dimensional carrier or extension of D.

This is a proved norm-ball form of the semidefinite unit-row step preceding triangle 183.3. The semidefinite theorem below proves the needed positive/negative-to-ball direction. The full original A1-A3 to recovered Jordan/order-norm stage and the general unit row remain unpaid. It therefore supplies no transverse 36.1, pure generated frame 63.1 or original 76.2/77.1 conclusion. Those full targets, all degenerate branches and original quantum-source conditions remain unchanged. Its faithful source audit remains unfinished under issue 28178.

**Theorem 1.4 (All semidefinite original second labels have zero unit rows).**

$$\forall E \in \mathit{RealNormedSpaces},\; \forall S \in \operatorname{RealBilinearMaps}\left(E\right),\; \forall D \in \operatorname{TotalBinaryMaps}\left(E\right),\; \forall P \in \operatorname{ReadingFamilies}\left(E\right),\; \forall A \in \operatorname{ConeUnitData}\left(E\right),\; \left(\operatorname{OriginalSupportStage}\left(E, S, D, P, \operatorname{unit}\left(A\right)\right) \land \left(\operatorname{ConeExact}\left(\operatorname{cone}\left(A\right), P\right) \land \operatorname{OriginalOrderNorm}\left(A\right)\right)\right) \Rightarrow \left(\forall mu \in R,\; \forall b \in E,\; \left(\operatorname{mem}\left(b, \operatorname{cone}\left(A\right)\right) \lor \operatorname{mem}\left(\operatorname{neg}\left(b\right), \operatorname{cone}\left(A\right)\right)\right) \Rightarrow \operatorname{D}\left(\operatorname{smul}\left(\mathit{mu}, \operatorname{unit}\left(A\right)\right), b\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalUnitSupport.unit_row_semidefinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep exactly the full cone, norm, S, D and P telescope of unit_row_closed_ball. For every real mu and original b in C or with -b in C, the conclusion is D(mu u,b)=0. OriginalOrderNorm has exactly the cone and norm meaning specified in the preceding declaration. There is no separate assumed norm-ball property, support-state existence, input regularity or D output closure.

For c in C, construct a positive normalized support reading for w=c-(norm(c)/2)u when w is nonzero. Its original positivity and norm bound put beta(c) between zero and norm(c), so abs(beta(w))<=norm(c)/2. Its norm-support equality proves norm(w)<=norm(c)/2. If w=0 the bound is immediate. Apply the proved closed-ball unit row. For -b in C apply the same construction to -b and use the negative ball center; this does not assume oddness of D. This proves the complete semidefinite second-input step of triangle 183.3 on the recovered original order-norm stage.

The next missing general-unit inference is the original semidefinite approximation of the fixed support correction in triangle 183.5-183.8, followed by the actual fixed-table residual elimination. Neither those approximating original labels nor the full transverse/generated-frame bridge are assumed or proved here. General nonzero support inhabitation or impossibility outside the semidefinite region remains unresolved. The full original 76.2 and 77.1 and their source conditions remain open. The faithful four-slot audit remains unfinished under issue 28178.

## References

- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalUnitSupport.positive_support_unit_boundary`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalUnitSupport.support_unit_obstruction`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalUnitSupport.unit_row_closed_ball`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalUnitSupport.unit_row_semidefinite`
- Dependency: [D5/S3/Topology/OrderNormSupport](../../Topology/OrderNormSupport.md)
