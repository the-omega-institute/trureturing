# Original Repeated Prefix

## Abstract

Literal repeated original heights and their native exponential survival.

**Theorem 1.1 (Every positive cycle count with the fixed early clock).**

$$\begin{gathered}\forall B:Band,n:\mathbb{N},chi:\mathbb{R},1\leq n\Rightarrow \\{}0< \operatorname{q}(B)\land \operatorname{q}(B)< 1\land \\{}\operatorname{OC}(B,2,\operatorname{E}(B,n),chi)\land \operatorname{OC}(B,2,\operatorname{L}(B,n),chi)\land \\{}\operatorname{AC}(\operatorname{E}(B,n),0,2)\land \operatorname{AC}(\operatorname{L}(B,n),0,2)\land \\{}(\forall t:\mathbb{R},t\in \operatorname{Icc}(0,1)\Rightarrow \operatorname{E}(B,n)(t)=\operatorname{P}(B,n)(t)\land \operatorname{L}(B,n)(t)=\operatorname{P}(B,n)(t))\land \\{}\operatorname{E}(B,n)(2)=\operatorname{a}(B)\land \operatorname{L}(B,n)(2)=\operatorname{a}(B)\land \\{}\operatorname{S}(\operatorname{c}(B),\operatorname{E}(B,n),2)=\operatorname{q}(B)^{n+1}\land \operatorname{S}(\operatorname{c}(B),\operatorname{L}(B,n),2)=\operatorname{q}(B)^{n+1}\land \\{}\operatorname{E}(B,n)(\frac{5}{4})=\operatorname{b}(B)\land \operatorname{L}(B,n)(\frac{5}{4})=\operatorname{a}(B)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalRepeatedPrefix.early_late_native_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Band B consists of real numbers a,b,c with 0<a<b<c<1/2. Its q is (a/b)*((c-b)/(c-a)). For d>0, up(B,d) and down(B,d) are the original affine Leg objects a to b and b to a, both of duration d. Their loop is the actual concatenate of those height functions at time d. No law or survival certificate is stored in the construction.

The prefix P(B,d,0) is the constant height a. Recursively P(B,d,j+1)=concatenate(P(B,d,j),loop(B,d),2*j*d). The prefix P(B,d,j) has duration 2*j*d. For n>=1 set d=1/(2*n), so P(B,d,n) has duration one and consists of n literal a-b-a cycles.

The early suffix concatenates the duration-1/2 loop with d=1/4 and the constant height a for duration 1/2. The late suffix concatenates that wait with the same loop. E(B,n) and L(B,n) concatenate P(B,d,n) with the respective suffix at time one. Thus their actual affine suffix joins are at 1,5/4,3/2,7/4,2. The real phase chi is constant in every original control.

OC(B,T,k,chi) denotes OriginalControl((c,c,1-2*c),T,k,const(chi)); AC(k,0,T) denotes absolute continuity on that interval. S(c,k,t) is the exponential of minus the interval integral of the native derivative hazard max(k prime,0)/k+max(-k prime,0)/(c-k). In the formula a=a(B), b=b(B), c=c(B), q=q(B), E=E(B,n), L=L(B,n), and P=P(B,1/(2*n),n).

The original affine survival formula gives a/b on each rising leg and (c-b)/(c-a) on each falling leg. At every recursive join, concatenate_original supplies the original-control certificate and native_concatenation splits the actual exponential hazard integral. Induction therefore gives S(c,P,1)=q^n. Each actual suffix contributes one more q, giving the two terminal equalities. The same recursive heights return to a. At time 5/4 they are b and a, so their height separation there is b-a independently of n.

The theorem proves absolute continuity and the original-control alternative. A separate finite-piecewise-C1 certificate for the full repeated heights, exact support-band bounds and a supremum height-distance equality require further conclusions. It does not yet prove normalization or an event identity for the full marked laws, their total variation, inverse nonuniformity or exact resource totals. Arbitrary-reference quantum outputs, operational suprema and absorbing extensions are outside its statement.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalRepeatedPrefix.early_late_native_survival`
- Dependency: [D5/S3/Quantum/Fibers/OriginalMarkedConcatenation](OriginalMarkedConcatenation.md)
