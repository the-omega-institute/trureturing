# Logarithmic spectral phase stiffness

## Abstract

Logarithmic spectral phase stiffness.

**Theorem 1.1 (Logarithmic spectral phase stiffness).**

Lean statement: `D5/S3/Analytic/Asymptotics/LogarithmicPhaseStiffness.logarithmic_phase_stiffness`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/LogarithmicPhaseStiffness.logarithmic_phase_stiffness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be any index type, gamma and m real-valued functions on I, and L,c,C real constants. Assume L>1, gamma(i)>=L, m(i)>=0, c>=0, and finiteness of every strict cutoff gamma(i)<Y. Its finite weighted count Nless(Y) satisfies abs(Nless(u)-c*u*log(u))<=C*u for every u>=L.

Put a(i)=m(i)/(gamma(i)*(1/4+gamma(i)^2)), M(Y)=sum over gamma(i)<Y of a(i)*gamma(i)^2, delta(t)=sum over I of 2*a(i)*(1-cos(gamma(i)*t)), and v(t)=sum over I of 2*a(i)*gamma(i)*sin(gamma(i)*t). Both a and a*gamma are summable. The derivative of delta at every real t, including zero, is v(t), and v is continuous.

For 0<abs(t) and L*abs(t)<=1, put Y=1/abs(t). The absolute differences delta(t)-t^2*M(Y) and v(t)-2*t*M(Y) are bounded by t^2*(9*c*log(Y)+8*c+9*C) and abs(t)*(5*c*log(Y)+4*c+5*C), respectively.

Let A be the sum of a and R(L,Y)=c*log(Y)+C+(c/2)*log(L)^2+C*(log(Y)-log(L))+A/4. The absolute differences delta(t)-(c/2)*t^2*log(Y)^2 and v(t)-c*t*log(Y)^2 are bounded by t^2*(9*c*log(Y)+8*c+9*C+R(L,Y)) and abs(t)*(5*c*log(Y)+4*c+5*C+2*R(L,Y)), respectively.

The strict low cutoff and inclusive high cutoff partition the spectrum exactly. Layer integrals bound arbitrary finite high sets before infinite summability is deduced. A summable first derivative majorant gives global C1 regularity; no second derivative interchange is asserted.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/LogarithmicPhaseStiffness.logarithmic_phase_stiffness`
