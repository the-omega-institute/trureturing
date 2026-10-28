# Original Control Survival Instability

## Abstract

Uniform height convergence with common scalar resource bounds need not preserve original hazard survival.

For every real c define doubleWall(c)=B(c)=(c,c,1-2c). This is the original five-mode base, with modes ordered 0,1,2,3,13 and probability vector (k,c-k,1-2c,c-k,k). The theorems use I=[0,1], duration one, 0<c<1/2, any positive natural n, and the constant real phase q(t)=phi with arbitrary real phi.

For natural n,j and real t define tent(n,j,t)=max(0,min(t-j/n,(j+1)/n-t)). For real c,t and natural n define triangle(c,n,t)=C(c,n,t)=(c/2) times the sum of tent(n,j,t) over j in the finite natural range 0<=j<n, and height(c,n,t)=c/2-C(c,n,t)/(2-t). These are total real functions with Lean's total real division; the theorems use n>=1 and t in I, where both denominators are nonzero. A finite sum retains every corner as a control value. On each closed rising half-cycle C=(c/2)(t-j/n); on each closed falling half-cycle C=(c/2)((j+1)/n-t). The predicate Legs(c,n) below denotes exactly these two universally quantified closed-leg equations for every natural j<n.

**Definition 1.1 (Survival from the original derivative hazard).**

$$\forall c: \mathbb{R}, \forall k: \mathbb{R}\to \mathbb{R}, \forall t: \mathbb{R}, \operatorname{survival}(c,k,t)=\exp (-\int_{0}^{t}(\frac{\operatorname{max}(\operatorname{deriv}(k)(u),0)}{k(u)}+\frac{\operatorname{max}(-\operatorname{deriv}(k)(u),0)}{c-k(u)}) du)$$

*Formalization.* `D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability.survival` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real c, real height function k and real t, hazard(c,k,u) is max(k prime(u),0)/k(u)+max(-k prime(u),0)/(c-k(u)). The displayed integral is the real interval integral with Lebesgue measure. The definition does not assert its integrability; the construction theorem proves actual interval integrability at every endpoint t in I. Derivatives at corners are used only through almost-everywhere integral identities.

**Theorem 1.2 (The finite triangular family and its actual survival).**

$$\forall c: \mathbb{R}, \forall phi: \mathbb{R}, \forall n: \mathbb{N}, 0<c<\frac{1}{2}\land 1\leq n\Rightarrow (\operatorname{ValidBase}(\operatorname{doubleWall}(c)))\land (\operatorname{OC}(\operatorname{doubleWall}(c),1,\operatorname{height}(c,n),\operatorname{constant}(phi)))\land (\operatorname{FC}(\operatorname{height}(c,n),\operatorname{constant}(phi)))\land ((\operatorname{AC}(\operatorname{height}(c,n)))\land (\operatorname{AC}(\operatorname{constant}(phi))))\land ((\operatorname{height}(c,n)(0)=\frac{c}{2})\land (\operatorname{height}(c,n)(1)=\frac{c}{2}))\land (\operatorname{Legs}(c,n))\land (\forall t\in [0,1], (\frac{c}{4}\leq \operatorname{height}(c,n)(t))\land (\operatorname{height}(c,n)(t)\leq \frac{c}{2})\land (|\operatorname{height}(c,n)(t)-\frac{c}{2}|\leq \frac{c}{4n}))\land ((0<\operatorname{min}(\frac{c}{4},1-2c))\land (\forall t\in [0,1], \forall i: \operatorname{Fin}(5), \operatorname{min}(\frac{c}{4},1-2c)\leq \operatorname{probability}(\operatorname{doubleWall}(c),\operatorname{height}(c,n)(t))(i)))\land (\operatorname{Lip}(\operatorname{height}(c,n),[0,1],\frac{3c}{4}))\land (\operatorname{TV}(\operatorname{constant}(phi))=0)\land (\operatorname{TV}(\operatorname{height}(c,n))\leq \frac{3c}{4})\land (\forall t: \mathbb{R}, \operatorname{deriv}(\operatorname{constant}(phi))(t)=0)\land ((\operatorname{IL}(\operatorname{height}(c,n),\operatorname{constant}(phi)))\land (\operatorname{IQ}(\operatorname{height}(c,n),\operatorname{constant}(phi)))\land (\operatorname{Length}(\operatorname{height}(c,n),\operatorname{constant}(phi))\leq \frac{3c}{4})\land (\operatorname{Cost}(\operatorname{height}(c,n),\operatorname{constant}(phi))\leq \frac{9c^{2}}{16}))\land (\operatorname{AE}(t\in [0,1],(\operatorname{hazard}(c,\operatorname{height}(c,n))(t)=\frac{1}{2-t})\land (|\operatorname{deriv}(\operatorname{height}(c,n))(t)|\leq \frac{3c}{4})))\land (\forall t\in [0,1], (\operatorname{II}(\operatorname{hazard}(c,\operatorname{height}(c,n)),0,t))\land (\operatorname{survival}(c,\operatorname{height}(c,n),t)=1-\frac{t}{2}))\land (\operatorname{OC}(\operatorname{doubleWall}(c),1,\operatorname{constant}(\frac{c}{2}),\operatorname{constant}(phi)))\land (\forall t: \mathbb{R}, (\operatorname{hazard}(c,\operatorname{constant}(\frac{c}{2}),t)=0)\land (\operatorname{survival}(c,\operatorname{constant}(\frac{c}{2}),t)=1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability.oscillatory_original_controls` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula, k=height(c,n), q=constant(phi), a=c/2, m=min(c/4,1-2c), and B=B(c). OC is OriginalControl on this same base and duration one. FC is FiniteC1Control with continuous derivative rates on the closed partition pieces, and AC means AbsolutelyContinuousOnInterval on [0,1]. TV is eVariationOn on I, with real upper bounds embedded by ENNReal.ofReal. Lip(k,I,L) is LipschitzOnWith(Real.toNNReal(L),k,I). These abbreviations retain the original carrier and both regularity alternatives.

For arbitrary real functions k,q, coordinateLength(k,q)=Length(k,q) is the real interval integral from zero to one of sqrt(k prime squared plus q prime squared), and quadraticCost(k,q)=Cost(k,q) is the same interval integral of k prime squared plus q prime squared. Both use Lebesgue measure. IL and IQ assert interval integrability of those actual integrands. II(h,0,t) asserts IntervalIntegrable(h,volume,0,t). AE(t in I,P) means that for Lebesgue-almost every real t, membership in I implies P. All remaining time quantifiers include both endpoints. The margin inequality holds for every one of the five actual probabilities.

The partition times are j/(2n), with 2n legs. The triangle is continuous, and 2-t is at least one on I. On an open leg, differentiating the height gives -C prime/(2-t)-C/(2-t)^2. The triangle derivative is c/2 on rising legs and -c/2 on falling legs. Consequently the height derivative is -(c-k)/(2-t) on rising legs and k/(2-t) on falling legs. These rates extend continuously to each closed leg. The original finite-C1-to-AC theorem supplies absolute continuity of both coordinates.

The bounds 0<=C<=c/(4n) and 2-t>=1 give the legal height band and uniform error bound. The signed derivative identities and that band give the speed bound 3c/4 almost everywhere. Absolute continuity and the fundamental theorem on every subinterval give the same Lipschitz bound. Its variation estimate gives TV(k)<=3c/4. Integrating the actual speed and its square gives Length<=3c/4 and Cost<=9c^2/16; measurability and domination also prove integrability of the squared derivative. The constant real phase has derivative and total variation zero.

Substituting the signed derivatives into the original positive/negative hazard gives exactly 1/(2-t) outside the finite mesh corners. This function is continuous on I. Its primitive -log(1-t/2) gives the integral from zero to every t in I, so the integral-defined survival equals 1-t/2 at every such t. Waiting uses the same hazard definition; its derivative is zero, hence its hazard is zero and its survival is one. No prescribed survival function is an assumption of the theorem.

These are scalar control and survival statements. They do not identify C with the instrument's actual signed-loss output, establish its variation, prove an exact identity between height total variation and length, or establish marked, quantum, operator or arbitrary-reference distance equalities. Those conclusions require their additional output and variation arguments.

**Theorem 1.3 (Uniform convergence with a fixed terminal discrepancy).**

$$\forall c: \mathbb{R}, \forall phi: \mathbb{R}, 0<c<\frac{1}{2}\Rightarrow (\forall e: \mathbb{R}, 0<e\Rightarrow \exists N: \mathbb{N}, 1\leq N\land \forall n: \mathbb{N}, N\leq n\Rightarrow (\operatorname{OC}(\operatorname{doubleWall}(c),1,\operatorname{height}(c,n),\operatorname{constant}(phi)))\land (\forall t\in [0,1], |\operatorname{height}(c,n)(t)-\frac{c}{2}|<e))\land (\forall n: \mathbb{N}, 1\leq n\Rightarrow |\operatorname{survival}(c,\operatorname{height}(c,n),1)-\operatorname{survival}(c,\operatorname{constant}(\frac{c}{2}),1)|=\frac{1}{2})\land (\neg \operatorname{Tendsto}(n\mapsto \operatorname{survival}(c,\operatorname{height}(c,n+1),1),\operatorname{atTop}(),\operatorname{nhds}(\operatorname{survival}(c,\operatorname{constant}(\frac{c}{2}),1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability.uniform_height_survival_discontinuity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same explicit family is used here. For every positive error tolerance there is a positive natural threshold N such that every n>=N is an original control with height error strictly below that tolerance at every point of I. Each member has the common scalar bounds proved above. Nevertheless the actual terminal survival difference from waiting is exactly one half for every n>=1, and the sequence indexed by n+1 does not converge to the waiting terminal survival.

Choose N larger than c/(4e). The uniform estimate c/(4n) then gives convergence. The construction theorem gives survival(c,height(c,n),1)=1/2 and survival(c,constant(c/2),1)=1. Uniqueness of real limits excludes convergence of the constant terminal-survival sequence to one. Thus uniform height approximation together with these common upper resource bounds does not control scalar survival.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability.oscillatory_original_controls`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability.survival`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalControlSurvivalInstability.uniform_height_survival_discontinuity`
- Dependency: [D5/S3/Quantum/Fibers/OriginalControlComposition](OriginalControlComposition.md)
