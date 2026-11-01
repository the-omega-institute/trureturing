# Weighted Legal-Path Temperley-Lieb Relations

## Abstract

Finite symmetric weighted legal paths carry the exact local Temperley-Lieb projections.

**Theorem 1.1 (Weighted path projections satisfy all four local relations).**

$$\begin{gathered}\forall L: \operatorname{Finite}, R: L \to L \to \operatorname{Prop},\ \operatorname{Symmetric}(R), d: L \to \mathbb{R}, 0<\Delta, \forall a\in L, 0<d_{a} \land \sum_{b: \operatorname{R}(a, b)} d_{b}=\Delta d_{a},\ \forall n\in\mathbb{N}, s, t\in L,\\\operatorname{let} \operatorname{LegalPath}(R, n, s, t): Type = \{x: \operatorname{Fin}(n+1) \to L | x\left(0\right) = s \land \left(x\left(n\right) = t \land \left(\forall k \in \operatorname{Fin}(n),\; R\left(x\left(k\right), x\left(k+1\right)\right)\right)\right)\}; \\\operatorname{let} P_{i}: \operatorname{Matrix}(\operatorname{LegalPath}(R, n, s, t), \operatorname{LegalPath}(R, n, s, t), \mathbb{C}), i\in \mathbb{N}, 1\le i<n, \forall x \in \operatorname{LegalPath}(R, n, s, t), y \in \operatorname{LegalPath}(R, n, s, t),\; P_{i}\left(x, y\right) = (\begin{cases}\operatorname{Complex.ofReal}(\frac{\sqrt{d\left(x\left(i\right)\right) \cdot d\left(y\left(i\right)\right)}}{\Delta \cdot d\left(x\left(i-1\right)\right)}) & \text{if} (\left(\forall k \in \operatorname{Fin}(n+1),\; k \ne i \Rightarrow x\left(k\right) = y\left(k\right)\right) \land x\left(i-1\right) = x\left(i+1\right))\\0 & \text{otherwise}\end{cases}); \\(\forall i, 1\le i<n \Rightarrow \operatorname{conjTranspose}(P_{i})=P_{i} \land P_{i}P_{i}=P_{i}) \land\\(\forall i, 1\le i, i+1<n \Rightarrow P_{i}P_{i+1}P_{i}=\Delta^{-2}P_{i}) \land\\(\forall i, j, 1\le i<n, 1\le j<n, i+2\le j \lor j+2\le i \Rightarrow P_{i}P_{j}=P_{j}P_{i}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb.weighted_legal_path_temperley_lieb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be any finite label type and R a symmetric Boolean adjacency relation, including possible self-loops. Every label has a strictly positive real weight d, delta is strictly positive, and the sum of d(b) over R(a,b) equals delta times d(a) for every a. Fix any path length n and endpoints s,t. The path basis contains precisely the legal length-n paths from s to t and may be empty.

For every interior i, P_i(x,y) is zero unless x and y agree outside i and x at i-1 equals x at i+1. In the remaining case its literal FT.12 coefficient is the complex cast of sqrt(d(x_i) * d(y_i)) / (delta * d(x_(i-1))). This is the source's square root of the product, with no rescaling or normalization of P_i.

The theorem establishes self-adjointness and idempotence at every interior index, the forward adjacent triple product whenever i+1 is interior, and commutation for both ordered cases of distance at least two. Its local replacement equivalence identifies a legal fiber with the neighbors of its common flank; the proof also establishes the adjacent unique survivor and the distant locality argument. No nonempty path-space premise is used.

## Application: Fibonacci three-setting tomography

Use labels 0=vacuum and 1=tau, adjacency R(c,d) iff c=1 or d=1, weights d(0)=1 and d(1)=phi, and delta=phi, where phi is the golden ratio. The fixed-endpoint carrier LegalPath R 3 0 1 has precisely the two ordered paths (0,1,0,1) and (0,1,1,1). Reindexing the coordinate orthonormal basis by these paths identifies the source H_3^tau with C^2. The literal pathProjection entries at positions 1 and 2 are P=diag(1,0) and Q=[[r^2,b],[b,r]], with r=1/phi>0, s=sqrt(r)>0, and b=r*s>0. The Perron equation is phi=phi*1 at label 0 and 1+phi=phi^2 at label 1; the weighted-path theorem therefore supplies the actual projection laws. In the fixed gauge F=[[r,s],[s,-r]], Q=F*P*F-adjoint. The permitted active pulse V=I+(i-1)P=diag(i,1) is unitary.

For every real p,x,y with 0<=p<=1 and x^2+y^2<=p(1-p), keep the entire mixed-state matrix rho=[[p,x+i*y],[x-i*y,1-p]]. All three readouts use this same rho: m0=Tr(P*rho), m1=Tr(Q*rho), and m2=Tr(Q*V*rho*V-adjoint). Writing h=r^2-r=1-2*r<0, they equal p, r+h*p+2*b*x, and r+h*p-2*b*y. Thus p=m0, x=(m1-r-h*m0)/(2*b), and y=(r+h*m0-m2)/(2*b), exactly FT.25. The sign in the scalarB correspondence is essential: rho=FourQubitParentConstruction.scalarB(1/2,(x,-y,p-1/2)). Its public scalarB_posSemidef_iff identifies precisely the full closed radius-1/2 ball, including all boundary states.

For every epsilon>=0 and all three errors |eta_j|<=epsilon, invert the noisy readouts m+eta without imposing positivity on the reconstructed matrix. The coordinate errors are delta_p=eta0, delta_x=(eta1-h*eta0)/(2*b), and delta_y=(h*eta0-eta2)/(2*b). Since (1-h)/(2*b)=sqrt(phi), their absolute values are at most epsilon, sqrt(phi)*epsilon, and sqrt(phi)*epsilon. Applying TraceNorm.transitionMass_sq and traceNorm_nonneg to this same trace-zero matrix difference gives half its trace norm equal to sqrt(delta_p^2+delta_x^2+delta_y^2). Consequently it is at most kappa*epsilon, where kappa=sqrt(1+2*phi), as in FT.26. These are applications and coefficient normalizations of existing matrix and norm results; no new mathematical declaration is required.

For eta0=eta1=eta2=epsilon, the three coordinate errors are simultaneously epsilon, sqrt(phi)*epsilon, and -sqrt(phi)*epsilon, and half the trace norm is exactly kappa*epsilon. At the true state rho=I/2 all three exact readouts are 1/2. For every 0<=epsilon<=1/(4*kappa), the noisy readouts are in [0,1], the reconstructed Bloch radius is at most 1/4, and the reconstructed trace-one matrix is positive semidefinite. Its actual P,Q,V readouts equal those same noisy values. This is a positive physical neighborhood, so any constant smaller than kappa fails even there; sharpness concerns one simultaneously realizable state and error triple.

For arbitrary raw reconstruction project u=(p_hat-1/2,x_hat,y_hat) onto the actual Euclidean closed ball of radius 1/2. Mathlib's exists_norm_eq_iInf_of_complete_convex supplies a nearest point v. Its norm_eq_iInf_iff_real_inner_le_zero characterization gives inner(u-v,w-v)<=0 for every true ball point w. Expanding the squared distance yields norm(v-w)<=norm(u-w). The signed coordinate permutation (u0,u1,u2) maps to (u1,-u2,u0), preserving this distance and the ball. Return v to the same matrix family as rho(v0+1/2,v1,v2). It is positive semidefinite with trace one, and its half trace-norm error to every true state cannot exceed the raw error. Hence FT.26 survives this closed-ball projection. The readouts throughout are expectations from independent preparations; finite-sample statistics require a separate error budget.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb.weighted_legal_path_temperley_lieb`
