# Band Switching and Expectation Symmetry

## Abstract

The actual switch of two band pairs exchanges good and regular and yields equal expectations under an invariant finite law.

Let X be a finite flag carrier. The permutations s and t are involutions without fixed points, representing corner and band matchings. For four distinct points a,b,t(a),t(b), let u swap t(a) and t(b), and let t'=u*t*u. This replaces a--t(a), b--t(b) by a--t(b), b--t(a) and leaves all other pairs unchanged. Good(s,t,a,b) means that a and b are in the same integer-power orbit of s*t. Bad(s,t,a,b) means that s(a) and b are in the same such orbit. Regular(s,t,a,b) means that neither orbit relation holds. The two-matching connectivity theorem identifies Regular with distinct combinatorial boundary components.

**Theorem 1.1 (Actual Band Surgery Exchanges the Categories).**

$$\forall X \in FiniteType,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \forall a \in X,\; \forall b \in X,\; \left(\left(\left(\operatorname{Involutive}\left(s\right) \land \operatorname{FixedPointFree}\left(s\right)\right) \land \left(\operatorname{Involutive}\left(t\right) \land \operatorname{FixedPointFree}\left(t\right)\right)\right) \land \operatorname{FourDistinct}\left(a, b, \operatorname{apply}\left(t, a\right), \operatorname{apply}\left(t, b\right)\right)\right) \Rightarrow \left(\left(\operatorname{Good}\left(s, \operatorname{switch}\left(t, a, b\right), a, b\right) \Leftrightarrow \operatorname{Regular}\left(s, t, a, b\right)\right) \land \left(\left(\operatorname{Bad}\left(s, \operatorname{switch}\left(t, a, b\right), a, b\right) \Leftrightarrow \operatorname{Bad}\left(s, t, a, b\right)\right) \land \left(\operatorname{Regular}\left(s, \operatorname{switch}\left(t, a, b\right), a, b\right) \Leftrightarrow \operatorname{Good}\left(s, t, a, b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch.band_switch` (`✓ std3`). ∎

*Citation.* Babak Ghanbari, Robert Šámal (2026). *Facial diagrams and cycle double cover*. DOI: [10.48550/arXiv.2605.01410](https://doi.org/10.48550/arXiv.2605.01410). URL: <https://arxiv.org/abs/2605.01410v1>.

*Commentary.*

Delete the two selected band pairs by fixing their four endpoints. First-return paths in the remaining finite matching system construct a fixed-point-free endpoint pairing. Its value at one endpoint and involutivity force one of the three pairings of four points. The proved reattachment orbit formula then gives good-to-regular, regular-to-good, and bad-to-bad. The cut and both reattachments are explicitly identified with t and u*t*u; their orbit effect is not a premise.

For the expectation statement, Omega is a nonempty finite set of equally weighted states. The corner matching s is fixed and t(omega) is a fixed-point-free involutive band matching for every state. The four marked points are distinct in every state. A state bijection tau satisfies t(tau(omega)) = switch(t(omega),a,b) for each omega, where switch is the actual matching operation above. MeanGood and MeanPhysicalRegular are the rational sums of the corresponding zero-one indicators divided by card(Omega). PhysicalRegular is the negation of corner/band connectivity.

**Theorem 1.2 (Equal Good and Regular Expectations Under the Stated Law).**

$$\forall X \in FiniteType,\; \forall Omega \in NonemptyFiniteType,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Function}\left(Omega, \operatorname{Perm}\left(X\right)\right),\; \forall tau \in \operatorname{Equiv}\left(Omega, Omega\right),\; \forall a \in X,\; \forall b \in X,\; \operatorname{ActualTwistFamily}\left(s, t, tau, a, b\right) \Rightarrow \operatorname{MeanGood}\left(s, t, a, b\right) = \operatorname{MeanPhysicalRegular}\left(s, t, a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch.twist_invariant_uniform_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Babak Ghanbari, Robert Šámal (2026). *Facial diagrams and cycle double cover*. DOI: [10.48550/arXiv.2605.01410](https://doi.org/10.48550/arXiv.2605.01410). URL: <https://arxiv.org/abs/2605.01410v1>.

*Commentary.*

Band surgery proves that a state's regular indicator equals the good indicator of its image under tau. Reindexing the finite sum gives equality of the two means. The statement makes the state-space and actual matching-transport assumptions explicit. It does not identify an unspecified distribution on unlabelled embeddings, prove surface realization, or imply exact thirds for any category.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch.band_switch`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch.twist_invariant_uniform_expectation`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing](FiniteEndpointPairing.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit](InvolutionOrbitSplit.md)
