# Rational Interval Orbit Retraction

## Abstract

An explicit finite weighted orbit retraction is continuous on the entire closed interval pseudo-orbit domain, including both empty caps.

Let I=[0,1], f(u)=2u/(1+u), delta=1/256, and P=P_delta. For any real gamma, P_gamma consists of all x:Z->I with |f(x(k))-x(k+1)|<=gamma at every integer k, with the product subtype topology. These are the closed bi-infinite domains of Artigue, Shadowing maps, Section 2.1. This rational construction is separate from the cited paper. Write shift(l,x)(k)=x(l+k) and O(p)(k)=f^k(p).

The actual weight is w(u)=max(0,(u-1/3)(2/3-u)), and g(u)=w(u)u/max(1/3,1-u). The continuous extension g is zero off the open middle band and equals w(u)u/(1-u) on it. Let B(x)={k:1/3<x(k)<2/3}. The marker classification gives a finite consecutive set of at most three indices. Define W(x) as the sum of w(x(k)) and A(x) as the sum of 2^(-k)g(x(k)) over all integers; their supports are finite. W(x)>0 exactly when B(x) is nonempty. For Q(s)=s/(1+s), set R(x)=Q(A(x)/W(x)) in that case. If B(x) is empty, the entire sequence lies strictly in one cap; R(x) is zero on the lower cap and one on the upper cap.

**Theorem 1.1 (Lower cap cylinder estimate).**

$$\begin{aligned}\forall x\in P, \forall j\in \mathbb{Z}, x(j)<\frac{1}{2}\Rightarrow R(x)\le 8\cdot 2^{-j}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_lower_cylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

For a nonempty marker block [a,b], the quotient lies between 2^(-b)/2 and 2*2^(-a). The coordinate condition forces b>=j and hence a>=j-2. Thus Q(A/W)<=A/W<=8*2^(-j). Empty-marker sequences in this cylinder are in the lower cap.

**Theorem 1.2 (Upper cap cylinder estimate).**

$$\begin{aligned}\forall x\in P, \forall j\in \mathbb{Z}, \frac{1}{2}<x(j)\Rightarrow 1-R(x)\le 8\cdot 2^{j}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_upper_cylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The coordinate condition forces a<=j and b<=j+2, so A/W>=2^(-j-2)/2. Then 1-Q(A/W)=1/(1+A/W)<=8*2^j. Empty-marker sequences in this cylinder are in the upper cap.

**Theorem 1.3 (Continuity on the entire closed domain).**

$$\begin{aligned}\operatorname{Continuous}(R:P\to I)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.continuous_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

At a point with marker j, keeping its weight positive confines every neighboring marker to [j-2,j+2]. The numerator and denominator are then fixed finite coordinate sums and the denominator is positive. At every empty lower-cap sequence, a cylinder at a sufficiently large positive j makes the lower estimate arbitrarily small. At every empty upper-cap sequence, use a sufficiently negative j and the upper estimate. This covers nonconstant empty-cap sequences and the appearance or disappearance of boundary markers. No global continuity of W or uniform positive lower bound on W is asserted.

**Theorem 1.4 (Integer reindexing of the weight sum).**

$$\begin{aligned}\forall x\in P, \forall l\in \mathbb{Z}, W(shift(l,x))=W(x)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.W_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Translation is a bijection of the integer index set, so it preserves the finite weight sum.

**Theorem 1.5 (Integer reindexing of the phase numerator).**

$$\begin{aligned}\forall x\in P, \forall l\in \mathbb{Z}, A(shift(l,x))=2^{l}A(x)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.A_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The exact identity 2^(-k)=2^l*2^(-(l+k)) supplies the phase factor under the same reindexing.

**Theorem 1.6 (Exact equivariance at every integer time).**

$$\begin{aligned}\forall x\in P, \forall l\in \mathbb{Z}, R(shift(l,x))=f^{l}(R(x))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

For nonempty marker sets the quotient scales by 2^l, and Q(2^l s)=H(2^l)(Q(s)). Empty marker sets retain their cap under translation, and both endpoints are fixed. The proof establishes one-step equivariance directly and uses the existing homeomorphism-group integer equivariance theorem for every positive and negative l.

**Theorem 1.7 (Fixing all genuine orbits).**

$$\begin{aligned}\forall p\in I, R(O(p))=p\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_trueOrbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Both endpoint orbits have empty markers and are fixed by their cap value. For an interior p, the negative orbit limit is zero and the positive orbit limit is one, so the orbit cannot lie wholly in either cap and must have a marker. At every marker k, 2^(-k) times the odds of f^k(p) equals p/(1-p). The finite weighted sum therefore gives A/W=p/(1-p), and Q(A/W)=p.

For the following statement define e(x,k)=dist(x(k+1),f(x(k))) and E(x,k)=dist(f^k(R(x)),x(k)). Inclusion from P_gamma into P is literal sequence inclusion. For x in P_gamma the expression R(x) in E means evaluation after that inclusion. Limits as |k| tends to infinity are the cofinite filter on Z.

**Theorem 1.8 (One explicit map at all accuracies and both infinite tails).**

$$\begin{aligned}(\forall \varepsilon>0, \exists \gamma>0, \gamma\le \frac{1}{256}\land \forall x\in P_{\gamma}, \forall k\in \mathbb{Z}, E(x,k)<\varepsilon)\land\\(\forall x\in P, \lim_{|k|\to \infty}e(x,k)=0\Rightarrow\\(\forall \varepsilon>0, \exists N\in \mathbb{N}, \forall k\in \mathbb{Z}, N\le |k|\Rightarrow E(x,k)<\varepsilon)\land\\\lim_{|k|\to \infty}E(x,k)=0)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_global_and_limit_shadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Apply CompactSelector.global_and_limit_shadowing to this fixed R, its continuity, true-orbit identity and exact one-step equivariance. The first conclusion is uniform over all integer centers after shrinking the closed error scale. The second holds on the full fixed P and imposes no finite-support or eventual-exactness condition on the link errors. The natural tail bound and the cofinite limit are both included. This establishes the selector and its global and two-sided limit shadowing. The phase-memory map T and its every-rho failure of self-tuning are separate further conclusions.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.A_shift`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_global_and_limit_shadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_lower_cylinder`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_shift`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_trueOrbit`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.R_upper_cylinder`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.W_shift`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalRetraction.continuous_R`
- Dependency: [D5/S1/Dynamics/Shadowing/RationalIntervalAction](RationalIntervalAction.md)
