# Normalized transport and its Robin application

## Abstract

Explicit logarithmic transport for weighted tails

Use the existing tail(k,x) and weightedTail(k,x) from Weil.Mertens.WeightedTailTransport. Their logarithmic weight is r(t)=(1+log(t))/log(t)^2 and density(t)=-r'(t) on t>1. Write D(x)=sqrt(x)*log(x).

**Theorem 1.1 (Explicit logarithmic transport error).**

$$\forall k \in \mathbb{R} \to \mathbb{R},\; \forall x \in \mathbb{R},\; \forall C \in \mathbb{R},\; 2 \le x \Rightarrow \left(\operatorname{IntegrableOn}\left(k, \operatorname{Ioi}\left(x\right)\right) \Rightarrow \left(\left(\forall t \in \mathbb{R},\; x \le t \Rightarrow \left|\operatorname{tail}\left(k, t\right)\right| \le \frac{C}{\operatorname{sqrt}\left(t\right)}\right) \Rightarrow \left|\operatorname{D}\left(x\right) \cdot \operatorname{weightedTail}\left(k, x\right) - \operatorname{sqrt}\left(x\right) \cdot \operatorname{tail}\left(k, x\right)\right| \le \frac{3 \cdot C}{\operatorname{log}\left(x\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/WeightedTail/SharpTailTransport.normalized_tail_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute Fubini in WeightedTailTransport.transport gives tail(k,x)*r(x)-weightedTail(k,x) as the integral of density(t)*tail(k,t). After scaling and subtracting sqrt(x)*tail(k,x), the boundary term is sqrt(x)*tail(k,x)/log(x), of magnitude at most C/log(x). For t>=x>=2, density(t)/sqrt(t) is bounded by the derivative of -2/(sqrt(t)*log(t)^2). This derivative is nonnegative and its half-line integral is 2/(sqrt(x)*log(x)^2), by the improper fundamental theorem and the primitive's zero limit. The integrated error after scaling is therefore at most 2*C/log(x). The closed-tail hypothesis includes the boundary t=x. This estimate follows from the existing Fubini identity and the derivative comparison.

## Consequences at the Robin lower endpoint

Write L=firstLiMass, J(x)=weightedTail(psiErrorKernel,x), and G(v)=exp(-v/2)*U(exp(v)). The earlier RHSharpArithmeticEnvelope proves sqrt(x)*Q(x)=-G(log(x)) for x>=2 (sqrt_Q), identifies J with Jpsi via weighted_eq, and gives the signed limit D(x)*J(x)+G(log(x))->0 under RH (Jpsi_signed_limit). The new estimate also gives this limit: RHSharpActualEnvelope.actual_G_control and firstLiMass_lt_third supply the eventual closed-tail bound with C=1/3. For each epsilon>0, eventually |D(x)*J(x)|<L+epsilon by the triangle inequality. The recurrence G(m)->L along arbitrarily late natural m, together with the signed limit at x=exp(m), gives |D(exp(m))*J(exp(m))+L|<epsilon arbitrarily far out.

For y=log(n), put F(n)=D(y)*robinLogMargin(n), A(n)=D(y)*(robinLogMargin(n)-J(y)), S(n)=G(log(y)), and B=2*sqrt(2)-2. For each eta>0, SharpReserveLower.sharp_lower_reserve_all_integers gives A(n)>B-eta eventually since D(y)>0 on y>=16. Under RH, RHSharpActualEnvelope.actual_G_control gives S(n)<L+eta and the signed limit gives |E(y)|<eta, where E(y)=D(y)*J(y)+G(log(y)). Use the maximum of these three thresholds. For any real delta with F(n)<=B-L+delta, the identity F=A-S+E implies B-eta<=A(n)<=B+delta+2*eta and L-delta-2*eta<=S(n)<=L+eta. Thus both components approach their respective endpoints along every sequence tending to infinity with F(n)->B-L. The earlier RHSharpAllIntegerMargin.all_integer_sharp_margin supplies the all-integer lower envelope and sharp attainment at strict original records under RH.

## References

- Truth anchor: `D5/S3/Arith/Robin/WeightedTail/SharpTailTransport.normalized_tail_transport`
- Dependency: [D5/S3/Weil/Mertens/WeightedTailTransport](../../../Weil/Mertens/WeightedTailTransport.md)
