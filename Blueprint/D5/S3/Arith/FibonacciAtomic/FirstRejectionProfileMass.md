# Two-State Profile Mass for Every Window Cut

## Abstract

Every actual uniform window-cut profile mass equals its chronological two-state matrix value, is positive, and the profile masses sum to one.

Fix k≥0 and n=k+1. Positions are indexed by Fin(n), starting at zero. A is any finite set of positions and B is its complement. The alphabet Window consists of the five complete windows 000,100,010,101,001, written from low to high. Owned(k,A) is the subtype of Fin(n) consisting of positions in A, and Side(k,A) is the function type Owned(k,A) to Window. The law profileLaw(k,A) has type FiniteResponseLaw(Side(k,A)): its rational mass is nonnegative and its total is one. It is the independent product of the actual five-window laws with mass 1/5, so each assignment has mass 5 to the power minus card(A). There is no legality restriction on the raw assignments.

Profile(k,A) consists of an allowed cutoff and its active crossing bits. profileMass(P) is the pushforward mass of code(A) at encode(P), namely the sum of profileLaw(k,A).mass(a) over that actual fiber. Equivalently it is the uniform finite mean of the fiber indicator. The code and encode maps identify that fiber. The cutoff records the earliest bad A-internal seam, the terminal zero window when the terminal position belongs to A, or top when neither occurs. A seam j has left position j and right position j+1. A retained crossing has j strictly before the cutoff. Its owned high or low bit is required to equal the encoded bit. When the cutoff is terminal, only the crossing into the terminal position has its low bit forced to false by encode; earlier independent crossing ports retain their own bits.

filterWindow(P,i,x) checks all retained crossing ports owned by i. At the terminal position it additionally requires x=000 for the terminal cutoff, x≠000 for top, and nothing for an earlier internal cutoff. internalFactor(P,j,r,u) is one minus the product of the two Bool bits when j is A-internal and before the cutoff, their product when j equals the cutoff, and one otherwise. seamFactor uses this factor at the seam immediately before the current position, and is one at position zero. Thus the rejecting seam keeps both its endpoints constrained, while every later raw window is free.

The public matrix D at an A position has entry (r,v) equal to one fifth of the sum over all five actual windows x of the indicator high(x)=v, the window filter, and seamFactor(P,i,r,low(x)). This average preserves the difference between 000 and 010. At a B position its entry is the indicator v=false, for both input states, with weight one. Matrices are multiplied in chronological position order. Each matrix is rational and indexed by Bool in both directions. matrixProduct(P) denotes this ordered product; summing its false initial row over both final Bool states gives the scalar profileOperatorMass(P).

For every prefix length m≤n, restrict a uniform raw m-window tuple to the coordinates owned by A. This restriction has exactly their actual product law. Complementary coordinates integrate to one. The accepted-prefix mass with saved state v equals the false,v entry of the first m matrix factors. The saved state is the immediately preceding window's high bit after A and false after B. Final-coordinate integration gives the five-window A average and the weight-one B reset. At m=n, acceptance of all filters is equivalent to code(A,a)=encode(P). Every profile has a representative of positive weight, and the profile fibers partition Side(k,A). In particular the empty cut has one assignment and scalar mass one.

**Theorem 1.1 (Actual profile fibers and exact two-state probabilities).**

$$\left(\forall \left(k: \operatorname{Nat}\left(\right)\right), \left(\forall \left(A: \operatorname{Finset}\left(\operatorname{Fin}\left(k+1\right)\right)\right), \left(\left(\forall \left(a: \operatorname{Side}\left(k, A\right)\right), \operatorname{mass}\left(\operatorname{profileLaw}\left(k, A\right), a\right) = \frac{1}{5^{\operatorname{card}\left(A\right)}}\right) \land \left(\left(\forall \left(P: \operatorname{Profile}\left(k, A\right)\right), \left(\forall \left(a: \operatorname{Side}\left(k, A\right)\right), \left(\operatorname{code}\left(A, a\right) = \operatorname{encode}\left(P\right) \iff \left(\left(\forall \left(i: \operatorname{Owned}\left(k, A\right)\right), \operatorname{filterWindow}\left(P, \operatorname{index}\left(i\right), \operatorname{apply}\left(a, i\right)\right) = true\right) \land \left(\forall \left(j: \operatorname{Fin}\left(k\right)\right), \operatorname{internalFactor}\left(P, j, \operatorname{last}\left(\operatorname{apply}\left(\operatorname{extend}\left(A, a\right), \operatorname{left}\left(j\right)\right)\right), \operatorname{first}\left(\operatorname{apply}\left(\operatorname{extend}\left(A, a\right), \operatorname{right}\left(j\right)\right)\right)\right) = 1\right)\right)\right)\right)\right) \land \left(\left(\forall \left(P: \operatorname{Profile}\left(k, A\right)\right), \left(\operatorname{profileMass}\left(P\right) = \sum_{v \in \operatorname{Bool}\left(\right)} \operatorname{entry}\left(\operatorname{matrixProduct}\left(P\right), false, v\right) \land 0 < \operatorname{profileMass}\left(P\right)\right)\right) \land \sum_{P \in \operatorname{Profile}\left(k, A\right)} \operatorname{profileMass}\left(P\right) = 1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FirstRejectionProfileMass.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All statements hold for every natural k, arbitrary A, reachable profile P, and actual A assignment a. In the formula, index(i) is the underlying position of the owned-coordinate subtype. extend(A,a) fills B with the middle window, whose two endpoint bits are false. The first clause gives the exact atom mass. The second identifies the whole fiber with its window and internal-seam filters. The third gives the chronological matrix value and its strict positivity. The last sums the actual profile probabilities to one.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FirstRejectionProfileMass.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity](FirstRejectionCutCapacity.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping](../../ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.md)
