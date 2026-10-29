# Mixing from an Expanding Minimal Real Flow

## Abstract

Expanding covariance of a compact minimal real flow forces topological mixing of the expanding map.

**Theorem 1.1 (Every sufficiently large iterate meets each pair of nonempty open sets).**

$$\forall X \in Type,\; \forall alpha \in \operatorname{RealAction}\left(X\right),\; \forall a \in R,\; \forall f \in \operatorname{SelfMap}\left(X\right),\; \left(\operatorname{CompactHausdorff}\left(X\right) \land \left(\operatorname{JointlyContinuous}\left(alpha\right) \land \left(\operatorname{Minimal}\left(alpha\right) \land \left(1 < a \land \left(\operatorname{Continuous}\left(f\right) \land \left(\forall t \in R,\; \forall x \in X,\; \operatorname{f}\left(\operatorname{alpha}\left(t, x\right)\right) = \operatorname{alpha}\left(a \cdot t, \operatorname{f}\left(x\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall U \in \operatorname{Set}\left(X\right),\; \forall V \in \operatorname{Set}\left(X\right),\; \left(\operatorname{IsOpen}\left(U\right) \land \left(\operatorname{Nonempty}\left(U\right) \land \left(\operatorname{IsOpen}\left(V\right) \land \operatorname{Nonempty}\left(V\right)\right)\right)\right) \Rightarrow \left(\exists N \in Nat,\; \forall n \in Nat,\; N \le n \Rightarrow \left(\exists x \in X,\; x \in U \land \operatorname{iterate}\left(f, n, x\right) \in V\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/MinimalFlowDilationMixing.minimal_real_flow_dilation_mixing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a compact Hausdorff topological space with an additive action alpha of the real numbers. The action is jointly continuous and minimal: the orbit of every point is dense in X. Let a be a real number greater than one and f a continuous map from X to itself satisfying f(alpha(t,x)) = alpha(a*t,f(x)) for all real t and all x in X. For every pair U,V of nonempty open subsets of X there is a natural N such that, for every natural n at least N, some x in U has f iterated n times at x in V. The witness x may depend on n. No global nonemptiness of X is assumed; the open-set assertion is vacuous on the empty space.

Choose u in U. Continuity of the orbit map at time zero gives a positive epsilon such that alpha(s,u) belongs to U whenever the absolute value of s is less than epsilon. Minimality makes translates of V cover X. Compactness and Mathlib's IsCompact.exists_finite_cover_vadd give a finite set I of translating times. If z = alpha(s,v) for s in I and v in V, then alpha(-s,z) = v. Thus the sum M of the absolute values of times in I bounds a hitting time for every z in X. The minus sign converts a covering translate into a hitting time.

Induction gives f^n(alpha(s,u)) = alpha(a^n*s,f^n(u)). Since a is greater than one, Mathlib's tendsto_pow_atTop_atTop_of_one_lt makes M/a^n less than epsilon for every sufficiently large n. For each such n choose a bounded hitting time t for f^n(u). The point alpha(t/a^n,u) lies in U and its nth iterate is alpha(t,f^n(u)), which lies in V. The uniform bound over all z is what gives every sufficiently large n.

For the actual dyadic inverse limit DyadicSolenoid of DyadicTimeSeparation, take alpha(t,x) = realFlow(t) + x, a = 2 and f(x) = 2 times x in the additive group. The public dyadic_time_separation theorem supplies compactness and the continuous dense-range realFlow, whose nth circle coordinate is t/2^n modulo one. The inherited product topology is Hausdorff. Translation by x is a homeomorphism, so composing it with the dense-range realFlow makes every orbit dense. The homomorphism law makes alpha an additive real action; its continuity is joint. Doubling is continuous and realFlow(2*t) = 2 times realFlow(t), giving the exact expanding covariance. Consequently doubling on this dyadic solenoid is topologically mixing in the displayed all-sufficiently-large-n sense. This exact application is checked with a local action instance, without changing the solenoid's public action instances or retaining a named specialization.

The conclusion concerns topological mixing of the discrete map f. It assumes no group structure on X, freeness of the real action, surjectivity or invertibility of f. It makes no entropy, periodic-point or chaos assertion and does not assert that the real flow is mixing. The compact Hausdorff and continuity-of-f hypotheses are retained in the declared theorem; the argument uses compactness, minimality, action continuity and expanding covariance. The searched pinned Dynamics minimality and transitivity APIs do not supply this all-large-iterate implication. This is a repository proof of the displayed inference, with no claim of novelty in the literature.

## References

- Truth anchor: `D5/S1/Dynamics/MinimalFlowDilationMixing.minimal_real_flow_dilation_mixing`
