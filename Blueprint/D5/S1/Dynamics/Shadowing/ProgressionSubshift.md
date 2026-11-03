# Progression-Avoidance Subshifts

## Abstract

Compact hereditary one-sided progression subshifts, zero-gap mixing and a nonempty periodic-set obstruction.

The alphabet is the existing binary ReturnBit={0,1}. A configuration x is ProgressionLegal(ell,x) when, for every natural start s and every positive natural difference p, some j<ell(p) has x(s+jp)=0. Mathlib PiNat.metricSpaceOfDiscreteUniformity supplies exactly the first-disagreement metric d(x,y)=2^(-firstDiff(x,y)), with zero distance on equal points, and the actual product topology and uniformity. The arithmetic-progression construction and its use for Meddaugh--Stephens Question 5.6 are attributed to Pro.

**Theorem 1.1 (Closedness of all progression constraints).**

$$\begin{aligned}\forall ell: \mathbb{N} \to \mathbb{N}, \operatorname{IsClosed}(\{x: \mathbb{N} \to ReturnBit \mid \operatorname{ProgressionLegal}(ell, x)\})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProgressionSubshift.progression_legal_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed progression condition is a finite union of closed coordinate cylinders. Intersect over all starts and positive differences. The finite-alphabet product is compact, hence its closed carrier subtype is compact.

All natural shifts preserve the constraints. Prepending a zero yields a legal preimage whenever ell(p)>0 for every positive p, so the continuous left shift is onto. Deleting ones preserves every already satisfied constraint. The all-zero point is legal under the same positive-length assumption; the configuration 10-infinity is legal when all lengths are at least two.

**Theorem 1.2 (Zero-gap joining without new forbidden progressions).**

$$\begin{aligned}\forall ell: \mathbb{N} \to \mathbb{N},\\(\forall p \in \mathbb{N}, 0<p \Rightarrow 3\le\operatorname{ell}(p)) \Rightarrow\\\forall x,y: \mathbb{N} \to ReturnBit, \operatorname{ProgressionLegal}(ell, x) \Rightarrow \operatorname{ProgressionLegal}(ell, y) \Rightarrow\\\forall a,b,n \in \mathbb{N}, a+\operatorname{max}(a, b)\le n \Rightarrow \operatorname{ProgressionLegal}(ell, \operatorname{progressionJoin}(x, y, a, b, n))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProgressionSubshift.progression_join_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume ell(p)>=3 for all positive p. Keep x on [0,a), y shifted to [n,n+b), and put zeros elsewhere. A progression with p<=max(a,b) starting in the first word cannot cross the gap, by induction on its index. At p>max(a,b), at most one progression term lies in each word; its first three terms cannot all be supported. A progression starting in the second word contradicts legality of y. Thus every sufficiently large n connects any two prescribed prefix cylinders. Metric neighborhoods contain such cylinders, proving open-set mixing in progression_shift_mixing.

**Theorem 1.3 (No nonempty forward invariant subset in the one cylinder).**

$$\begin{aligned}\forall ell: \mathbb{N} \to \mathbb{N}, \forall p \in \mathbb{N}, 0<p \Rightarrow\\\forall B: \operatorname{Set}(\operatorname{ProgressionPoint}(ell)), B \subseteq \operatorname{progressionOneCylinder}(ell) \Rightarrow\\\operatorname{MapsTo}((\operatorname{progressionShift}(ell))^{p}, B, B) \Rightarrow \neg \operatorname{Nonempty}(B)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProgressionSubshift.progression_no_invariant_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Set(T) denotes subsets of T, f^p denotes p-fold iteration, and MapsTo(f,B,B) means that f maps B into B. Choose x in B. Forward invariance gives (progressionShift(ell))^(jp)(x) in B for every natural j, so x(jp)=1 at every such coordinate, contradicting its p-progression condition. The cylinder [1] is clopen, and nonempty when ell(p)>=2. Compactness and image equality are unnecessary for this obstruction.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/ProgressionSubshift.progression_join_legal`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ProgressionSubshift.progression_legal_closed`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ProgressionSubshift.progression_no_invariant_subset`
- Dependency: [D5/S1/Dynamics/Shadowing/ReturnDistanceShadowing](ReturnDistanceShadowing.md)
