# Complete Robin Coefficient Laplace Representation

SOURCE ONLY / UNCOMPILED. Every declaration in the accompanying D5 and Reg
modules is uncompiled in this delivery. This document records the intended
mathematics and the written proof route, not kernel verification or acceptance.
The canonical narrative source is CompleteCoefficientLaplace.scribe.cs; this
source-only Markdown companion was written without running an emitter.

For every real A>1, put L=log A>0. For every complex s with 0<Re(s)<1, the
literal physical coefficient is

\[
F_A(s)=s^{-1}\int_A^\infty
 (u:\mathbb C)^{s-2}\frac{1+\log u}{(\log u)^2}\,du.
\]

The positive real base makes the complex power exp((s-2)log u).
`coefficient` is defined by this physical integral. It is not defined by the
resolvent. With g(x)=1/x+1/x², the intended complete theorem establishes
physical integrability, the exact logarithmic substitution

\[
F_A(s)=s^{-1}\int_L^\infty e^{(s-1)x}g(x)\,dx,
\]

integrability of the actual complex kernel
K(x,t)=(1+t)exp(-((1-s)+t)x) under the product of the restricted Lebesgue
measures on x>L and t>0, integrability of the resolvent, and

\[
F_A(s)=\frac{A^{s-1}}s\int_0^\infty
 \frac{(1+t)e^{-Lt}}{1-s+t}\,dt,
\qquad
\|F_A(s)\|\le
 \frac{A^{\operatorname{Re}s-1}(1/L+1/L^2)}{\|s\|\|1-s\|}.
\]

The target declaration is
`D5.S3.Arith.Robin.CompleteCoefficientLaplace.complete_coefficient_laplace`.
The open endpoints are Lebesgue conventions at regular finite endpoints;
no subdomain of A>1 or of the open strip is substituted.

The written proof reuses n=0 and n=1 of
`D5.S3.Analytic.LiCausalTrichotomy.integrableOn_complex_laplace_moment` and
`integral_complex_laplace_moment`. These give the exact numerator mass
integral (1+t)exp(-Lt)=g(L), without a new generic moment proof.
The logarithmic integrand is dominated by g(L)exp((Re(s)-1)x).
`integrableOn_comp_exp_Ioi` transports this integrability back to the physical
integral; `integral_comp_exp_Ioi` supplies the integral equality with the
actual exponential Jacobian and the positive-base complex-power identity.

For x>L and t>0 the actual kernel norm satisfies

\[
\|K(x,t)\|=(1+t)e^{-((1-\operatorname{Re}s)+t)x}
 \le e^{(\operatorname{Re}s-1)x}(1+t)e^{-Lt}.
\]

The right side is an integrable product by `Integrable.mul_prod`, the project
moments and `integrableOn_exp_mul_Ioi`. `Integrable.mono'` proves integrability
of K itself. Only then does `integral_integral_swap` exchange the integrals.
Integrating t first uses the two project moments; integrating x first uses
`integral_exp_mul_complex_Ioi`. The exponential factor is exactly A^(s-1).
Finally, the norm-square difference
||1-s+t||²-||1-s||²=2t(1-Re(s))+t² is nonnegative. The integrable positive
numerator therefore dominates the resolvent norm, and
`norm_integral_le_integral_norm` gives the factor-one estimate.

The source APIs were inspected at Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d (Lean v4.33.0), not at master.
The existing MellinWeightedVariation module concerns a real clipped
variation kernel; it supplies neither this physical coefficient nor the
complex resolvent, and its unrelated theorems are not imported as decoration.
The helpers in the new module are consumed by the complete proof route.

The original source is M1 in Library/ArithSums/nicolas2025comparison.md at
7f52221f2e23da81475058d5b5b6620e68709401. The literal signed explicit formula
is attributed there to Broadbent–Fiori–Kadiri–Ng–Wilk, Bounds for Mertens sums,
Proposition 13(i), equation (55), proof (82)–(83). The ordinary proof plan is
full-proof.md in the caller's robin5040-complete-coefficient-laplace-audit
directory, SHA256 785458a254b194c78d0850a6e140eb10dfb16e623c615586176cc9a6258e2b1e.
This is a composition of classical integration results applied to the
existing complete coefficient, with no literature priority claim.

The identity keeps the entire H1 remainder within the complete integral.
Finite-endpoint U2 retains its separate factor-two statement and is not
replaced here. A positive numerator is not a positive real coefficient or
a sign theorem for the actual-zero response. The Gamma response, both
ordinate signs, multiplicities, actual beta values, infinite tail,
elementary terms, directed comparisons, and arithmetic reserve/defect all
require their own verified consumers. No RH or Robin acceptance follows.

The matching Reg source attempts the existing DependentFamily template on
the full theorem telescope, with the real physical-input axis, a nonintegrable
constant intervention, role sensitivity and actual observational dependence.
It is unvalidated: all proof terms await compilation, and compiler-derived
sourceSelection and current binding evidence are absent. No concrete template
defect or applicability of issue #5214 was established. No new judge, ledger,
dataset, or recursive D5 audit template was introduced.

There are no intentionally omitted mathematical proof blocks or added
conclusion hypotheses in the written D5 route. Whether the tactic terms
elaborate against the pinned APIs, whether the exact statement and axiom
closure pass, and whether the Reg source binds lawfully remain unresolved.
No builds, probes, reporters or official acceptance checks were run.
