# Native Marked Concatenation

## Abstract

The native double-wall hazard and original Kraus outputs compose chronologically.

**Theorem 1.1 (Hazard, survival and the unchanged input).**

$$\begin{gathered}\forall c,T,s,a,chi:\mathbb{R}, k,K:\mathbb{R}\to \mathbb{R},\\{}c< \frac{1}{2}\land 0\leq T\land 0\leq s\land k(T)=K(0)\land a\in \operatorname{Ioo}(0,c)\land k(T)\in \operatorname{Ioo}(0,c)\land K(s)\in \operatorname{Ioo}(0,c)\land \operatorname{OC}(c,T,k,chi)\land \operatorname{OC}(c,s,K,chi)\Rightarrow \\{}(\forall^{\operatorname{ae}(\operatorname{Lebesgue}())} u:\mathbb{R},\operatorname{lambda}(c,\operatorname{J}(k,K,T),u)=\operatorname{If}(u\leq T,\operatorname{lambda}(c,k,u),\operatorname{lambda}(c,K,u-T)))\land \\{}\operatorname{S}(c,\operatorname{J}(k,K,T),T+s)=\operatorname{S}(c,k,T)\cdot \operatorname{S}(c,K,s)\land \\{}(\forall psi:\operatorname{Fin}(5)\to \mathbb{C},\operatorname{Act}(\operatorname{P}(c,k(T),K(s),\operatorname{S}(c,K,s)),\operatorname{Act}(\operatorname{P}(c,a,k(T),\operatorname{S}(c,k,T)),psi))=\operatorname{Act}(\operatorname{P}(c,a,K(s),\operatorname{S}(c,\operatorname{J}(k,K,T),T+s)),psi))\land \\{}(\forall g:\operatorname{Fin}(5)\to \mathbb{R},i:\operatorname{Fin}(5),psi:\operatorname{Fin}(5)\to \mathbb{C},\operatorname{Act}(\operatorname{A}(c,k(T),K(s),\operatorname{S}(c,K,s),g,i),\operatorname{Act}(\operatorname{P}(c,a,k(T),\operatorname{S}(c,k,T)),psi))=\operatorname{Act}(\operatorname{A}(c,a,K(s),\operatorname{S}(c,\operatorname{J}(k,K,T),T+s),g,i),psi))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalMarkedConcatenation.native_concatenation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native hazard_integrable assertion holds on [0,T] for every OriginalControl((c,c,1-2*c),T,k,const(chi)). For arbitrary nonnegative T,s and a matching join k(T)=K(0), hazard_integral splits the integral on [0,T+s] into the two local integrals whenever those local hazards are interval integrable. For any 0<=t<=T, survival_before identifies the native survival with the first height survival. For t<T, rate_before identifies the full five-mode logarithmic jump-rate vector; for T<t, rate_after identifies it with the second vector at t-T when the heights join. For every affine Leg L, leg_rate identifies the native logarithmic rate function jumpRate(L.c,L.height) with the affine Leg.jumpRate function on the full real clock. markedLaw_apply evaluates every measurable record event as its native successful source mass plus the sum of its native time-and-mode failure integrals.

The superscript ae(Lebesgue) on the first quantifier means Lebesgue almost everywhere. The local hazard and survival names are consumed aliases of OriginalControlSurvivalInstability.hazard and OriginalControlSurvivalInstability.survival, so that module supplies their single scalar implementation. For a real height k, lambda(c,k,t) is max(k prime(t),0)/k(t)+max(-k prime(t),0)/(c-k(t)). Here k prime is the derivative of the actual function, including for the concatenated height. S(c,k,t) is exp of minus the interval integral from zero to t of lambda(c,k,u). The join J(k,K,T) equals k(t) for t<=T and k(T)+K(t-T)-K(0) otherwise. The height match k(T)=K(0) makes the latter expression exactly K(t-T).

OC(c,T,k,chi) abbreviates OriginalControl((c,c,1-2*c),T,k,const(chi)). It includes both original regularity alternatives, continuity, strict support and finite phase variation. A finite piecewise C1 original coordinate is absolutely continuous. Its derivative is integrable, and its reciprocal and opposite-wall reciprocal are continuous on the compact interval. Multiplying these reciprocals by the positive and negative derivative parts proves integrability of the native hazard. No separate integrability certificate is assumed.

Write P(c,a,k,S)=successfulKraus(c,a,k,S) and A(c,a,k,S,g,i)=jumpKraus(c,a,k,S,g,i). These are exactly the original diagonal successful matrix and absorbing row followed by that matrix. Act denotes ordinary matrix-vector multiplication.

At every time other than the join, a neighborhood identifies the actual concatenated height with the first height or the translated second height. Equality of derivatives follows on those neighborhoods. The exceptional singleton has zero Lebesgue measure. Splitting the actual hazard integral and translating its second interval proves the exponential product formula. In the successful matrices, the intermediate positive probabilities cancel under their square roots. This is an equality of matrices before choosing an input. The absorbing row then preserves that equality.

The vector psi is arbitrary and need not be normalized. In particular it may be the original preparation source(c,a,beta,m,theta) with any beta, integer m and initial phase vector. The second action takes the first successful output as its input, preserving that vector and its unnormalized weight.

**Theorem 1.2 (All measurable events of two actual affine pieces).**

$$\begin{gathered}\forall L,R:Leg,chi,beta:\mathbb{R},m:\mathbb{Z},theta:\operatorname{Fin}(5)\to \mathbb{R},\\{}\operatorname{c}(R)=\operatorname{c}(L)\Rightarrow \operatorname{y}(L)=\operatorname{x}(R)\Rightarrow \\{}\operatorname{OC}(\operatorname{c}(L),\operatorname{duration}(L)+\operatorname{duration}(R),\operatorname{J}(\operatorname{height}(L),\operatorname{height}(R),\operatorname{duration}(L)),chi)\land \\{}(\forall E:\operatorname{Set}(Record),\operatorname{MeasurableSet}(E)\Rightarrow \\{}\operatorname{mu}(L,R,beta,m,theta)(E)=\operatorname{If}(\operatorname{success}()\in E,\operatorname{ofReal}(\operatorname{survival}(L,\operatorname{duration}(L))\cdot \operatorname{survival}(R,\operatorname{duration}(R))),0)+\sum_{i: \operatorname{Fin}(5)} \operatorname{F}(L,E,i)+\operatorname{ofReal}(\operatorname{survival}(L,\operatorname{duration}(L)))\cdot \sum_{i: \operatorname{Fin}(5)} \operatorname{G}(L,R,E,i))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalMarkedConcatenation.native_marked_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

L and R are actual positive-duration affine Leg objects from OriginalControlMarkedJump. Their heights join and their double-wall parameter c agrees. Let T=duration(L), U=duration(R), J=J(height(L),height(R),T), SL=survival(L,T), and SR=survival(R,U). The phase chi is constant on the full concatenation. The source is exactly source(c(L),x(L),beta,m,theta); beta is any real number, m any signed integer, and theta any real phase vector on the five original modes.

The measure mu(L,R,beta,m,theta) is markedLaw(c(L),x(L),beta,T+U,m,theta,J). Its success atom has weight equal to the sum of the squared successful Kraus amplitudes on that source. Its mode i failure measure is Lebesgue measure on (0,T+U], weighted by the squared absorbing Kraus amplitude of the same source, using the native hazard, exponential survival and logarithmic jump rates of J. The record space is Unit plus Fin5 times the real line, with success() denoting Sum.inl(()). No law or probability adapter is supplied as a premise.

Write B(E,i)={t: Sum.inr(i,t) is in E}. F(L,E,i) is the nonnegative integral on (0,T] intersect B(E,i) of ofReal(density(L,t,i)). G(L,R,E,i) is the nonnegative integral on (T,T+U] intersect B(E,i) of ofReal(density(R,t-T,i)). The latter integrand and interval retain the exact shifted second clock. All integrals use Lebesgue measure. ofReal denotes ENNReal.ofReal. The formula quantifies over every measurable set of records.

On the first open piece, the native rates and survival agree with those of L. On the second piece they agree with the shifted rates of R, and native survival equals SL times the shifted survival of R. Acting on the original source gives the second failure density SL*density(R,t-T,i). This uses the known source diagonal and the actual successful and absorbing matrices; it does not replace the first successful vector by a normalized preparation. For arbitrary real functions f and g, deriv_before identifies deriv(J(f,g,T),t) with deriv(f,t) whenever t<T; deriv_after identifies it with deriv(g,t-T) whenever T<t. These are local identities and require no derivative at the join. The singleton at the join contributes zero. Splitting each mode integral and summing gives the displayed event identity.

These two-piece statements supply chronological composition. They do not assert properties of a complete repeated early/late family. The full-family finite-piecewise-C1 certificate, exact resource totals, event-supremum total variation formula and inverse obstruction require further results. Arbitrary-reference quantum distance, operational suprema and the six-dimensional absorbing extension are also outside the statement.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalMarkedConcatenation.native_concatenation`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalMarkedConcatenation.native_marked_join`
- Dependency: [D5/S3/Quantum/Fibers/OriginalControlMarkedJump](OriginalControlMarkedJump.md)
- Dependency: [D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability](OriginalControlSurvivalInstability.md)
