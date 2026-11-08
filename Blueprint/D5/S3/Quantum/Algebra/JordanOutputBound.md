# Actual-output estimates on an incomplete original carrier

## Abstract

Actual rows of a recovered Jordan relation satisfy the square-root-three estimate, and normalized original polynomials have single actual-output remainders.

Let E be any real normed vector space, including the zero space, with no completeness or dimension assumption. Let S:E x E -> E be real bilinear. RecoveryStage(S,D) below means exactly the following conditions, on all original vectors: S is symmetric; S(S(x,y),S(x,x))=S(x,S(y,S(x,x))); norm(S(x,y))<=norm(x)norm(y); norm(S(x,x))=norm(x)^2; D(a,b)=-D(b,a); and D(D(a,b),c)=S(b,S(a,c))-S(a,S(b,c)). It also includes the original associator equation S(S(a,b),c)-S(a,S(b,c))=D(D(a,b),c)-D(a,D(b,c)). The first four are intermediate conclusions about the same S, rather than newly asserted consequences of raw small-window data in this module.

The actual output set A(D) is precisely {D(r,s):r,s in E}. No span, closure, output coverage, norming family, new completion, or enlarged output set is used. Norms are those of E. Applying this supplier to Unit Theorem 15.2 still requires the faithful original order-norm/JB bridge and the finite actual-output algebraic recovery from the common original certificate. Those bridges and the full bound 2 sqrt(3), Abel remainder elimination and unique extension remain open here.

**Theorem 1.1 (Only an actual output row needs Leibniz).**

$$\forall E \in \mathit{RealNormedSpaces},\; \forall S \in \operatorname{RealBilinearMaps}\left(E\right),\; \forall D \in \operatorname{TotalBinaryMaps}\left(E\right),\; \operatorname{RecoveryStage}\left(S, D\right) \Rightarrow \left(\forall q \in \operatorname{ActualOutputs}\left(D\right),\; \forall b \in E,\; \operatorname{norm}\left(\operatorname{D}\left(q, b\right)\right) \le \operatorname{sqrt}\left(3\right) \cdot \operatorname{norm}\left(q\right) \cdot \operatorname{norm}\left(b\right) \land \operatorname{norm}\left(\operatorname{D}\left(b, q\right)\right) \le \operatorname{sqrt}\left(3\right) \cdot \operatorname{norm}\left(q\right) \cdot \operatorname{norm}\left(b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/JordanOutputBound.actual_output_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In this theorem D is only a total function E x E -> E: it is not assumed linear, continuous, bounded or Leibniz. For q=D(r,s), the actual row is exactly the linear commutator S(s,S(r,-))-S(r,S(s,-)). Mathlib's linearized Jordan identity, applied twice on the same carrier, proves its Leibniz rule. No special associative representation is introduced.

Skewness gives D(a,a)=0. The actual row equation at (a,a,b) gives D(0,b)=0. The original associator at (a,a,b) then gives D(a,D(a,b))=S(a,S(a,b))-S(S(a,a),b), with exactly this sign and order. Thus the square of the actual row delta_q is H_q. Applying its proved Leibniz rule twice to S(b,b) yields H_q(S(b,b))=S(H_q(b),b)+S(b,H_q(b))+2 S(delta_q(b),delta_q(b)). Product norm domination and the square norm identity give 2 norm(delta_q(b))^2<=6 norm(q)^2 norm(b)^2. Taking the nonnegative square root gives the displayed constant; skewness gives the other slot. General rows are not declared derivations.

**Theorem 1.2 (The removed part is one original nested output).**

$$\forall E \in \mathit{RealNormedSpaces},\; \forall S \in \operatorname{RealBilinearMaps}\left(E\right),\; \forall D \in \operatorname{RealBilinearMaps}\left(E\right),\; \operatorname{RecoveryStage}\left(S, D\right) \Rightarrow \left(\forall a \in E,\; \forall b \in E,\; \forall q \in \mathit{RealPolynomials},\; \operatorname{coeff}\left(q, 0\right) = 1 \Rightarrow \left(\exists r \in \mathit{RealPolynomials},\; 1 - q = X \cdot r \land \left(b - \operatorname{Q}\left(b\right) = \operatorname{D}\left(a, \operatorname{D}\left(a, \operatorname{rH}\left(b\right)\right)\right) \land \left(\operatorname{D}\left(a, \operatorname{Q}\left(b\right)\right) = \operatorname{Q}\left(\operatorname{D}\left(a, b\right)\right) \land \left(\operatorname{mem}\left(b - \operatorname{Q}\left(b\right), \operatorname{ActualOutputs}\left(D\right)\right) \land \operatorname{norm}\left(\operatorname{D}\left(a, b\right) - \operatorname{Q}\left(\operatorname{D}\left(a, b\right)\right)\right) \le \operatorname{sqrt}\left(3\right) \cdot \operatorname{norm}\left(a\right) \cdot \operatorname{norm}\left(b - \operatorname{Q}\left(b\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/JordanOutputBound.polynomial_actual_output_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This second supplier additionally takes D real bilinear as an explicit recovery-stage input. It does not derive that input from the original common finite certificates, and it does not assume continuity or a bound for D. Define H on original E by H(x)=S(a,S(a,x))-S(S(a,a),x). For every real polynomial q with coefficient q(0)=1, put Q=q(H), evaluated in the associative algebra of algebraic linear endomorphisms of E. Associativity of this operator algebra imposes no associativity on S.

Polynomial.X_dvd_iff supplies r with 1-q=Xr. The original associator identity identifies H with D(a,-) squared, so that D(a,-) commutes with H and with q(H) by the pinned adjoin/centralizer supplier. Consequently b-Qb=D(a,D(a,r(H)b)) is one actual original output and D(a,Qb)=Q(D(a,b)). Apply the previous actual-output estimate to b-Qb in the second slot. All polynomial values remain in E; no completed-domain D(a,R_lambda b) is formed.

There is no polynomial approximation, semigroup construction, inverse-root calculus, Abel integral, limit interchange, weak-star argument or finite-certificate estimate in these statements. They supply the original finite-polynomial step needed before those limits. Zero vectors, zero actual outputs and the zero-space case are included through the exact range membership and the universal normed-space scope. These are source-derived prerequisites of Unit 15.2 equations (15.3), (15.4), (15.7) and (15.8), not a proof of full Theorem 15.2 or of its later physical or algebraic consequences.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/JordanOutputBound.actual_output_bound`
- Truth anchor: `D5/S3/Quantum/Algebra/JordanOutputBound.polynomial_actual_output_control`
