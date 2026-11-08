# Rational Interval Phase Memory

## Abstract

The one fixed phase-memory perturbation of the explicit interval orbit retraction satisfies the original shadowing and L-shadowing definitions.

Let I=[0,1], f(u)=2u/(1+u), delta=1/256, and P=P_delta, where P_gamma is the entire closed domain of sequences x:Z->I with d(x(k+1),f(x(k)))<=gamma at every integer k. Use the product subtype topology and the completed finite-marker orbit retraction R. Set e(x)=d(x(0),f(x(-1))) and T(x)=action(1+e(x),R(x)), with action(c,u)=cu/(1-u+cu). This is one fixed map on P; neither its formula nor its memory coordinate depends on an accuracy, time or restriction radius. For x in a smaller P_gamma, T and R mean evaluation after literal inclusion into P. Write shift(k,x)(j)=x(k+j), O(p)(j)=f^j(p), and d for the inherited interval distance. Artigue supplies the definitions; the rational phase-memory construction is separate from the cited paper.

**Theorem 1.1 (Commutation at all integer times).**

$$\begin{aligned}\forall c\in \mathbb{R}, \forall k\in \mathbb{Z}, \forall u\in I, 0<c\Rightarrow f^{k}(action(c,u))=action(c,f^{k}(u))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.action_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The existing action multiplication law and f^k=H(2^k) give commutation, for negative times as well as positive times.

**Theorem 1.2 (Exact phase displacement).**

$$\begin{aligned}\forall e\in \mathbb{R}, \forall u\in I, 0\le e\Rightarrow action(1+e,u)-u=\frac{eu(1-u)}{1+eu}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.action_displacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Clear the positive denominator 1+eu. The displacement is nonnegative on the full closed interval.

**Theorem 1.3 (Quarter-error bound).**

$$\begin{aligned}\forall e\in \mathbb{R}, \forall u\in I, 0\le e\Rightarrow d(action(1+e,u),u)\le \frac{e}{4}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.action_displacement_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The exact displacement, u(1-u)<=1/4 and 1+eu>=1 give a bound including u=0 and u=1.

**Theorem 1.4 (Continuity on the unchanged full domain).**

$$\begin{aligned}\operatorname{Continuous}(T:P\to I)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.continuous_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The actual link error at minus one is continuous. Combine it with continuity of R and the existing joint continuity of the positive rational action.

**Theorem 1.5 (All genuine orbits are fixed).**

$$\begin{aligned}\forall p\in I, T(O(p))=p\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_trueOrbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The origin memory of every true orbit is zero, so action(1,R(O(p)))=p. This includes both endpoint orbits.

**Theorem 1.6 (The original memory parameter persists under iteration).**

$$\begin{aligned}\forall x\in P, \forall k\in \mathbb{Z}, f^{k}(T(x))=action(1+e(x),f^{k}(R(x)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Commutation keeps e(x) fixed while f^k acts on R(x). It does not replace that parameter with the shifted memory.

**Theorem 1.7 (Actual uniform phase defect).**

$$\begin{aligned}\forall gamma\in \mathbb{R}, gamma\le \frac{1}{256}\Rightarrow \forall x\in P_{gamma}, \forall k\in \mathbb{Z}, d(f^{k}(T(x)),T(shift(k,x)))\le \frac{gamma}{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_shadowing_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Exact equivariance gives R(shift(k,x))=f^k(R(x)). Apply the quarter-error estimate to e(x) and e(shift(k,x)), each bounded by gamma, and use the triangle inequality.

**Theorem 1.8 (Literal shadowing-map condition).**

$$\begin{aligned}Continuous(T)\land (\forall p\in I, T(O(p))=p)\land \\\forall \varepsilon>0, \exists \gamma>0, \gamma\le \frac{1}{256}\land \forall x\in P_{\gamma}, \forall k\in \mathbb{Z}, d(f^{k}(T(x)),T(shift(k,x)))\le \varepsilon\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_shadowing_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Choose gamma=min(delta,2 epsilon). This is exactly Definition 3.1 for the prescribed single T, at every integer time.

**Theorem 1.9 (Uniform global tracing).**

$$\begin{aligned}\forall \varepsilon>0, \exists \gamma>0, \gamma\le \frac{1}{256}\land \forall x\in P_{\gamma}, \forall k\in \mathbb{Z}, d(f^{k}(T(x)),x(k))<\varepsilon\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_global_shadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

Take R's global tracing scale for epsilon/2 and shrink it to at most 2 epsilon. The additional displacement is at most gamma/4. No support condition on errors is imposed.

**Theorem 1.10 (Both tails of every fixed phase perturbation).**

$$\begin{aligned}\forall c\in \mathbb{R}, \forall p\in I, 0<c\Rightarrow \lim_{|k|\to \infty}d(action(c,f^{k}(p)),f^{k}(p))=0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.action_orbit_displacement_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

An interior orbit tends to zero at its negative tail and one at its positive tail. Continuity of action(c,.) and its two fixed endpoints make the displacement tend to zero at both tails. Endpoint base points are handled identically zero. The two natural-number limits are joined into the cofinite limit on Z. No uniform rate over p or c is claimed.

**Theorem 1.11 (Full-domain two-sided limit tracing).**

$$\begin{aligned}\forall x\in P, \lim_{|k|\to \infty}linkError(x,k)=0\Rightarrow \lim_{|k|\to \infty}d(f^{k}(T(x)),x(k))=0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_limit_shadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

For the fixed x use p=R(x), c=1+e(x) in the phase limit. Commutation and the triangle inequality combine that limit with the completed full-domain limit theorem for R. The domain contains arbitrary infinitely supported error sequences tending to zero in both directions.

**Theorem 1.12 (Literal L-shadowing-map condition).**

$$\begin{aligned}Continuous(T)\land (\forall p\in I, T(O(p))=p)\land \\\forall \varepsilon>0, \exists \gamma>0, \gamma\le \frac{1}{256}\land \forall x\in P_{\gamma}, \lim_{|k|\to \infty}linkError(x,k)=0\Rightarrow\\(\forall k\in \mathbb{Z}, d(f^{k}(T(x)),x(k))<\varepsilon)\land \lim_{|k|\to \infty}d(f^{k}(T(x)),x(k))=0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_L_shadowing_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The global tracing scale works simultaneously for the uniform all-time bound and the cofinite limit, with the same output T(x). This is Definition 4.5, including all admitted two-sided limit pseudo-orbits. The literal weighted-sum self-tuning antecedent and the every-positive-radius counterwitnesses are further obligations, not conclusions of this module.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_L_shadowing_map`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_global_shadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_iterate`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_limit_shadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_shadowing_defect`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_shadowing_map`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.T_trueOrbit`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.action_commutes`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.action_displacement`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.action_displacement_le`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.action_orbit_displacement_tendsto`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory.continuous_T`
- Dependency: [D5/S1/Dynamics/Shadowing/RationalIntervalRetraction](RationalIntervalRetraction.md)
