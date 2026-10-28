# Repeated Native Marked Laws

## Abstract

The original marked measures retain the common prefix and the exact failure clock.

**Theorem 1.1 (Native failure composition on Borel events).**

$$\forall c,a,b,beta,T,U,chi:\mathbb{R},m:\mathbb{Z},theta:\operatorname{Fin}(5)\to \mathbb{R},k,K:\mathbb{R}\to \mathbb{R},A:\operatorname{Set}(Record),c< \frac{1}{2}\land a\in \operatorname{Ioo}(0,c)\land b\in \operatorname{Ioo}(0,c)\land 0\leq T\land 0\leq U\land \operatorname{eval}(k,T)=\operatorname{eval}(K,0)\land \operatorname{OC}(c,T,k,chi)\land \operatorname{OC}(c,U,K,chi)\land \operatorname{MeasurableSet}(A)\Rightarrow \operatorname{F}(c,a,beta,T+U,m,theta,\operatorname{J}(k,K,T),A)=\operatorname{F}(c,a,beta,T,m,theta,k,A)+\operatorname{ofReal}(\operatorname{S}(c,k,T))\cdot \operatorname{F}(c,b,beta,U,m,theta,K,\operatorname{shift}(T,A))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.failure_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Record is Unit plus Fin5 times the real clock. Success is inl(()); failures are inr(i,t). OC(c,T,k,chi) is OriginalControl((c,c,1-2*c),T,k,const(chi)). S(c,k,t) is the exponential of minus the interval integral of the derivative hazard max(k prime,0)/k+max(-k prime,0)/(c-k). The join J(k,K,T) equals k before the join and k(T)+K(t-T)-K(0) after it.

F(c,a,beta,T,m,theta,k,A) is the sum over the five modes of the nonnegative integrals on (0,T] intersect {t:inr(i,t) in A} of the squared absorbing amplitude. That amplitude is jumpKraus(c,a,k(t),S(c,k,t),jumpRate(c,k,t),i) applied to the original source(c,a,beta,m,theta), where jumpRate is the derivative hazard minus the derivative of log p_i(k). The shift(T,A) is the pullback of A by the clock map sending inr(i,s) to inr(i,s+T), preserving success. All measures and integrals use the original Lebesgue clock.

The parameter b may be any interior preparation height for the second integral. The original source diagonal cancels its positive reference probabilities in the absorbing squared norm. Thus the weighted density identity follows directly from the native matrices; it introduces no normalization or independent reset. The actual first successful output remains unnormalized in chronological Kraus composition. At the join the derivative may change, but its singleton has zero Lebesgue measure. Splitting the integrals and translating the second interval proves the event identity for every measurable A.

**Theorem 1.2 (All repeated native measures are probabilities).**

$$\forall B:Band,n:\mathbb{N},beta:\mathbb{R},m:\mathbb{Z},theta:\operatorname{Fin}(5)\to \mathbb{R},e:Bool,1\leq n\Rightarrow \operatorname{IsProbabilityMeasure}(\operatorname{mu}(B,n,beta,m,theta,e))\land (\forall A:\operatorname{Set}(Record),\operatorname{MeasurableSet}(A)\Rightarrow \operatorname{eval}(\operatorname{mu}(B,n,beta,m,theta,e),A)=\operatorname{If}(\operatorname{success}()\in A,\operatorname{ofReal}(\operatorname{q}(B)^{n+1}),0)+\operatorname{F}(\operatorname{c}(B),\operatorname{a}(B),beta,1,m,theta,\operatorname{P}(B,n),A)+\operatorname{ofReal}(\operatorname{q}(B)^{n})\cdot \operatorname{F}(\operatorname{c}(B),\operatorname{a}(B),beta,1,m,theta,\operatorname{H}(B,e),\operatorname{shift}(1,A)))\land \operatorname{Chrono}(B,n,e)\land \operatorname{TerminalKraus}(B,n,e)\land \operatorname{FailureNoAtoms}(B,n,beta,m,theta,e)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.early_late_marked_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

B is an arbitrary Band with 0<a<b<c<1/2, and q=(a/b)*((c-b)/(c-a)). For every n>=1, P(B,n) is the existing repeated height with n complete affine up-and-down loops on [0,1]. E(B,n) and L(B,n) are the existing early and late heights on [0,2], and HE(B), HL(B) are their actual suffix heights on their local clock [0,1]. The Boolean e chooses E,HE when true and L,HL when false. The measure mu(B,n,beta,m,theta,e) is exactly OriginalMarkedConcatenation.markedLaw(c,a,beta,2,m,theta,k), with that chosen existing height k.

Each affine leg has native loss equal to the decrease of its surviving probability. For a concatenation, terminal survival multiplies, and the preceding failure-composition identity adds first losses to survival-weighted second losses. Induction over the actual repeated prefix therefore preserves total mass one. The same argument applies to the two suffixes and their join to the prefix. The success weight is q^(n+1), the identical prefix failure term is F(P,1,A), and the remaining term is q^n F(H,1,shift(1,A)). The arbitrary real beta, signed integer m and five initial phases are the same in all terms. Chrono(B,n,e) asserts that for every actual time 1<t<=2 and every vector psi on the five live modes, the successful action at t equals the suffix successful action at t-1 after successfulKraus(c,a,a,q^n) on psi. For every mode i the same equality holds for the absorbing action, with the actual suffix jumpRate at t-1 and the full actual jumpRate at t. TerminalKraus(B,n,e) records the additional endpoint clause: for every live vector, the early and late successful Kraus actions at time 2 agree, and both equal successfulKraus(c,a,a,q^(n+1)) applied to that vector. The vector is arbitrary and may be unnormalized. FailureNoAtoms(B,n,beta,m,theta,e) states that each native failureMeasure(c,a,beta,2,m,theta,k,i) assigns zero to every real singleton, for every i. Thus no failure atom is placed at either suffix endpoint or at any join.

**Theorem 1.3 (An attained supremum over all measurable events).**

$$\forall B:Band,n:\mathbb{N},beta:\mathbb{R},m:\mathbb{Z},theta:\operatorname{Fin}(5)\to \mathbb{R},1\leq n\Rightarrow (\forall A:\operatorname{Set}(Record),\operatorname{MeasurableSet}(A)\Rightarrow \lvert \operatorname{toReal}(\operatorname{eval}(\operatorname{mu}(B,n,beta,m,theta,\operatorname{true}()),A))-\operatorname{toReal}(\operatorname{eval}(\operatorname{mu}(B,n,beta,m,theta,\operatorname{false}()),A))\rvert\leq \operatorname{q}(B)^{n}\cdot (1-\operatorname{q}(B)))\land \operatorname{MeasurableSet}(\operatorname{AE}())\land \lvert \operatorname{toReal}(\operatorname{eval}(\operatorname{mu}(B,n,beta,m,theta,\operatorname{true}()),\operatorname{AE}()))-\operatorname{toReal}(\operatorname{eval}(\operatorname{mu}(B,n,beta,m,theta,\operatorname{false}()),\operatorname{AE}()))\rvert=\operatorname{q}(B)^{n}\cdot (1-\operatorname{q}(B))\land \operatorname{TV}(\operatorname{mu}(B,n,beta,m,theta,\operatorname{true}()),\operatorname{mu}(B,n,beta,m,theta,\operatorname{false}()))=\operatorname{q}(B)^{n}\cdot (1-\operatorname{q}(B))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.native_marked_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

TV(mu,nu) means the real supremum of |mu(A).toReal-nu(A).toReal| over every measurable record event A. It is the probability convention, without replacing the distance by a prescribed expression. AE is the actual early failure event inr '' (Fin5 times (1,3/2]). It includes all original modes and excludes terminal success.

The common prefix and terminal success cancel on every event. Each suffix failure integral is nonnegative and at most its total mass 1-q, so their difference has absolute value at most 1-q. The native prefix survival supplies the factor q^n. The early suffix is a loop followed by a constant wait, and the late suffix is that wait followed by the loop. A wait has zero native jump density. Translation of AE therefore captures the full early suffix failure mass and none of the late suffix failure mass. Endpoints carry no failure atoms because the mode measures have densities with respect to Lebesgue measure. This proves both the all-event bound and attainment, hence the supremum equality. An L1 representation of the same probability distance would include the factor one half.

**Theorem 1.4 (The actual marked laws defeat every modulus at zero).**

$$\forall B:Band,beta:\mathbb{R},m:\mathbb{Z},theta:\operatorname{Fin}(5)\to \mathbb{R},omega:\mathbb{R}\to \mathbb{R},\operatorname{Tendsto}(omega,\operatorname{nhdsWithin}(0,\operatorname{Ioi}(0)),\operatorname{nhds}(0))\Rightarrow (\forall n:\mathbb{N},1\leq n\Rightarrow \forall t:\mathbb{R},t\in \operatorname{Icc}(0,2)\Rightarrow \operatorname{eval}(\operatorname{E}(B,n),t)\in \operatorname{Icc}(\operatorname{a}(B),\operatorname{b}(B))\land \operatorname{eval}(\operatorname{L}(B,n),t)\in \operatorname{Icc}(\operatorname{a}(B),\operatorname{b}(B)))\land (\forall n:\mathbb{N},1\leq n\Rightarrow \operatorname{heightDistance}(\operatorname{E}(B,n),\operatorname{L}(B,n),2)=\operatorname{b}(B)-\operatorname{a}(B))\land \neg (\forall n:\mathbb{N},1\leq n\Rightarrow \operatorname{heightDistance}(\operatorname{E}(B,n),\operatorname{L}(B,n),2)\leq \operatorname{eval}(omega,\operatorname{TV}(\operatorname{mu}(B,n,beta,m,theta,\operatorname{true}()),\operatorname{mu}(B,n,beta,m,theta,\operatorname{false}()))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.marked_inverse_nonuniformity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

omega is any real function tending to zero from the positive side at zero. The statement gives the exact common height band [a,b], the full supremum height distance b-a on [0,2] for every n>=1, and the failure of every displayed uniform inverse estimate for these actual pairs. heightDistance(k,K,T) is the supremum of |k(t)-K(t)| for t in [0,T]. The lemma actual_range quantifies over every Band, n>=1, branch and time in [0,2], and proves that its actual height lies in [a,b]. Recursive concatenation preserves [a,b]. The actual values at 5/4 are b and a, so this point attains the full supremum. Their positive native marked distances q^n*(1-q) tend to zero, which contradicts b-a>0 if the displayed estimates all held.

These statements concern the original source-family marked probability laws. They do not establish arbitrary-reference quantum distance, an operational supremum, or the six-dimensional absorbing extension. Exact resource totals and full repeated finite-piecewise-C1 certificates are further assertions. In particular no common speed or variation cap is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.early_late_marked_probability`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.failure_join`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.marked_inverse_nonuniformity`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.native_marked_tv`
- Dependency: [D5/S3/Quantum/Fibers/OriginalRepeatedPrefix](OriginalRepeatedPrefix.md)
