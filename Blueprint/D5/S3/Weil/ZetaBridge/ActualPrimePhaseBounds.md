# Actual Prime Phase Bounds

## Abstract

Explicit bounds for the amplitude and the first and centered second moments of the finite prime-power symbol.

Let c>=3 be natural, L=log(c)>0, w(q)=vonMangoldt(q)/sqrt(q), and z(q)=exp(2*pi*I*log(q)/L). Every q in Ico(2,c) is retained, including all prime powers. A(c) is the sum of these nonnegative weights. The moments use the existing actual phases and the factor two per ordered pair.

**Theorem 1.1 (A finite amplitude bound with every prime power).**

$$\operatorname{AtLeastThree}(c)\Rightarrow\operatorname{A}(c)\leq2 \operatorname{sqrt}(c) L$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualPrimePhaseBounds.amplitude_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c>=3, sum_{q in Ico(2,c)} primeWeight(q) is at most 2*sqrt(c)*log(c). The von Mangoldt bound gives w(q)<=L/sqrt(q). For q>=2, 1/sqrt(q) is at most 2*(sqrt(q)-sqrt(q-1)); summing telescopes to 2*(sqrt(c-1)-1)<=2*sqrt(c). The sum does not discard prime powers.

The phase estimates bound the actual chord denominators. For 0<=t<=L and e<=min(t,L-t), the chord abs(1-exp(2*pi*I*t/L))=2*abs(sin(pi*t/L)) is at least 4*e/L. The two halves of the period use sin(x)>=2*x/pi on [0,pi/2]. The logarithmic inequality (y-x)/y<=log(y)-log(x), for positive x,y, pays the integer gaps and the gaps at both ends of the period.

**Theorem 1.2 (The actual first moment).**

$$\operatorname{AtLeastThree}(c)\Rightarrow\operatorname{primeFirstMoment}(c)\leq c \operatorname{sqrt}(c) L^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualPrimePhaseBounds.firstMoment_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c>=3, primeFirstMoment(c)<=c*sqrt(c)*L^2. For every label 2<=q<c, both log(q) and L-log(q) are at least 1/c. Thus norm(1-z(q))>=4/(c*L). Each exact first-moment term 2*abs(w(q))/norm(1-z(q)) is at most (c*L/2)*w(q). Summation and the amplitude bound yield the result.

**Theorem 1.3 (The centered second-moment offset with ordered resonances).**

$$\operatorname{AtLeastThree}(c)\Rightarrow\operatorname{offset}(c)\leq c {2 c+1} L^{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualPrimePhaseBounds.offset_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c>=3, offset(c)<=c*(2*c+1)*L^3. Distinct-label differences have chord at least 4/(c*L), in either orientation, including wraparound. Hence primeCross is at most (c*L/2)*A(c)^2. For p*q!=c, the sum chord is at least 4/((c+1)*L), and sumCross is at most ((c+1)*L/2)*A(c)^2.

For t=log(p)+log(q), the distances to 0, L and 2*L are all paid. Below resonance p*q<=c-1 gives L-t>=1/c. Above resonance p*q>=c+1 gives t-L>=log(c+1)-log(c)>=1/(c+1). The endpoint gaps follow from the first-phase gaps. All ordered p*q=c pairs, including p=q, remain in resonantMass and in the unchanged mean. Only the corresponding sumCross terms vanish. The identity offset=(primeCross+sumCross)/2 and A(c)^2<=4*c*L^2 give the bound. These inequalities supply arithmetic estimates; they do not identify a physical operator or prove RH.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPrimePhaseBounds.amplitude_le`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPrimePhaseBounds.firstMoment_le`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPrimePhaseBounds.offset_le`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualFullSymbolTail](ActualFullSymbolTail.md)
