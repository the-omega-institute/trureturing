# Smooth tests on the circle of circumference two pi

## Abstract

Weighted two-sided Fourier summability derived from genuine smooth periodic tests.

Test consists of a function lift:R->C that is globally ContDiff of every finite order and periodic with period 2*pi. jet(s) is its s-th iterated derivative, jetCompact(s) is its restriction to the compact interval [0,2*pi], and jetNorm(s) is the supremum norm of that continuous restriction. No rapid-decay assumption or finite Fourier support is part of Test.

coefficient(m) is fourierCoeffOn at derivative order zero, with the normalized integral convention f(theta)*exp(-i*m*theta)/(2*pi). It agrees exactly with Mathlib's fourierCoeff of the periodic lift on AddCircle. Uniqueness of derivatives proves periodicity of every jet from the original global periodicity. Mathlib's fourierCoeffOn_of_hasDerivAt then cancels the endpoint term at each integration-by-parts step. For every nonzero integer m, iteration gives coefficient(m)=((i*m)^(-1))^s*coeffJet(s,m), and hence its norm is at most jetNorm(s)/abs(m)^s.

For every natural r, weight(r,m)=norm(coefficient(m))*(1+abs(m))^r and W(r) is its sum over all integers. The zero mode is bounded separately by jetNorm(0). For nonzero m, the derivative of order r+2 gives the majorant 2^r*jetNorm(r+2)/m^2. Mathlib's two-sided integer inverse-square summability proves weighted_summable and W(r)<=jetNorm(0)+2^r*jetNorm(r+2)*sum_m(1/m^2). The finite bound does not require evaluation of the Basel sum.

conjugate is the pointwise complex conjugate of the actual smooth test and again satisfies Test. Its coefficient at m is conjugate(coefficient(-m)). OriginalInfiniteSmearing consumes weighted_summable and W_le to construct absolutely convergent operator sums; OriginalSmoothDomain consumes coefficient_conjugate for the opposite-charge pairing. These private estimates and definitions are support for the endpoint, without separate named theorem Describes or novelty claims. Fourier integration, calculus and summability retain Mathlib's Apache 2.0 attribution.
