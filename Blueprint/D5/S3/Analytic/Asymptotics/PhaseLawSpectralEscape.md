# Phase inversion and spectral escape

## Abstract

Phase inversion and spectral escape.

**Theorem 1.1 (Phase inversion and spectral escape).**

Lean statement: `D5/S3/Analytic/Asymptotics/PhaseLawSpectralEscape.phase_law_spectral_escape`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/PhaseLawSpectralEscape.phase_law_spectral_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be any index type, with nonnegative summable real weights a(i) and positive real frequencies gamma(i). Put A=sum a(i) and delta(t)=sum 2*a(i)*(1-cos(gamma(i)*t)). Assume alpha>0, B>=0 and 0<T0<=exp(-1). For every 0<t<=T0 assume abs(delta(t)-alpha*t^2*log(1/t)^2)<=B*t^2*(log(1/t)+1).

Fix Kinv=2*alpha+3*B, Y0=16/T0, CM=B+136*Kinv, C2=max(CM,Y0^2*A+alpha*log(Y0)^2), C4=max(64*Kinv,Y0^2*A), CT=max(32*Kinv,Y0^2*A), Cnum=C2+C4/8, Lstar=max(1,log(Y0),4*B/alpha), tstar=exp(-Lstar), and Qcdf=4*(Cnum+B)/alpha. These constants precede every cutoff, time, and quantile parameter; the total mass A remains in them.

For each Y>=1 and either strict or closed low cutoff, abs(M2(Y)-alpha*log(Y)^2)<=C2*(log(Y)+1) and M4(Y)<=C4*Y^2*(log(Y)+1). Both strict and closed high tails have mass at most CT*Y^(-2)*(log(Y)+1). The moments and tails are consequences of the phase hypothesis, not assumptions.

For every signed time 0<abs(t)<=tstar, let L=log(1/abs(t)). Then delta(t)>=alpha*t^2*L^2/2>0. Simultaneously for every s in [0,1], including both endpoints and moving choices, the phase mass below exp(s*L), with either cutoff convention, divided by delta(t) differs from s^2 by at most Qcdf/L.

The original-index masses p(i)=2*a(i)*(1-cos(gamma(i)*t))/delta(t) form a PMF on I. Map this PMF to real positions log(gamma(i))/L before taking its Borel probability measure. Equal positions add their masses, and I needs no measurable structure. Along the punctured real neighborhood of zero, these native probability measures converge weakly to Beta(2,1), whose density is 2*s on [0,1]. Every fixed bounded continuous real test function has the corresponding integral limit.

In the native complex Hilbert space lp(I,C,2), the coordinates sqrt(a(i))*(exp(I*gamma(i)*t)-1)/sqrt(delta(t)) give a unit vector throughout the same neighborhood. These vectors converge to zero in WeakSpace(C,lp(I,C,2)); every fixed continuous complex-linear functional tends to zero. Outside the neighborhood the probability family may equal Beta(2,1) and the vector family may equal zero.

The dyadic defect 4*delta(u/2)-delta(u) is a nonnegative sum of 4*a(i)*(1-cos(gamma(i)*u/2))^2. Low-frequency coercivity yields the fourth moment, while ordinary integration of finite high-frequency subsums yields the tail bound. The cosine remainder 5/96 gives the safe doubled remainder 1/8. No infinite integral interchange, local-finiteness, distinctness, RH, simplicity, or finite full second moment is required; all zero-weight and early modes remain admitted. Complex weak convergence uses linear dual evaluation and Riesz representation, not a complex-bilinear Hermitian pairing.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/PhaseLawSpectralEscape.phase_law_spectral_escape`
- Dependency: [D5/S3/Analytic/Asymptotics/LogarithmicPhaseStiffness](LogarithmicPhaseStiffness.md)
- Dependency: [D5/S3/Analytic/Asymptotics/PhaseLawDyadicCoercivity](PhaseLawDyadicCoercivity.md)
