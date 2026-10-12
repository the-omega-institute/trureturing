# A Projective Cover Obstruction

## Abstract

An infinite disjoint open forward tube in an extremally disconnected source rules out finite-cover shadowing.

**Theorem 1.1 (Disjoint open forward tubes exclude shadowing).**

$$\begin{aligned}\forall Y: Type, [\operatorname{TopologicalSpace}(Y)] [\operatorname{ExtremallyDisconnected}(Y)],\\\forall g: Y \Rightarrow Y, U: \mathbb{N} \Rightarrow \operatorname{Set}(Y),\\\operatorname{Continuous}(g) \Rightarrow (\forall n: \mathbb{N}, \operatorname{IsOpen}(U(n))) \Rightarrow\\(\forall i, j: \mathbb{N}, i \neq j \Rightarrow \operatorname{Disjoint}(U(i), U(j))) \Rightarrow\\\operatorname{Nonempty}(U(0)) \Rightarrow (\forall n: \mathbb{N}, \operatorname{MapsTo}(g, U(n), U(n+1))) \Rightarrow \neg \operatorname{HasShadowing}(g).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/StoneanForwardTubeObstruction.not_has_shadowing_of_disjoint_open_forward_tubes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrew M. Gleason (1958). *Projective topological spaces*. DOI: [10.1215/ijm/1255454110](https://doi.org/10.1215/ijm/1255454110). URL: <https://projecteuclid.org/euclid.ijm/1255454110>.

*Commentary.*

Let Y be any extremally disconnected topological space, g a continuous self-map, and U(n) open sets indexed by all natural numbers. Assume distinct U(n) are disjoint, U(0) is nonempty, and g maps U(n) into U(n+1). Then g does not have finite-open-cover shadowing. Compactness, Hausdorff separation, metrizability, countable weight, onto dynamics and density of the tube union are not hypotheses.

The closure W of the union of U(2^k) is clopen. Its continuous binary indicator on U(n) is true exactly at powers of two. Every finite itinerary starting with true has a nonempty open cylinder meeting W, hence the closure of the whole tube union. It therefore occurs on some tube. Consecutive true observations are separated by a power-of-two distance, and all these distances occur.

The existing finite_observation_isSofic theorem would give one finite graph for the entire observed language. With N vertices, an actual tube orbit gives distance D=2^(N+2) between consecutive true labels. Vertices at times 1 through N+1 repeat at times i<j. Erasing that zero cycle preserves the complete infinite suffix and creates distance D-(j-i), strictly between 2^(N+1) and 2^(N+2). This contradicts the tube-cylinder restriction. Finite-cylinder soundness follows from openness and density in the closure of the tube union.

For Peng Question 5.1, take the compact convergent sequence N with its point at infinity and successor fixing infinity. Initial-singleton and tail partitions prove shadowing; the source is already zero-dimensional and its identity cover works. Fibers over the isolated natural points of any onto equivariant extremally disconnected cover are precisely such open forward tubes. Thus every such cover, and by Gleason every projective compact Hausdorff cover, fails shadowing for every continuous lift. This application is explained in the problem dossier; it is not a negative answer to Question 5.1 or a worldwide originality claim.

The finite-observation theorem supplies an exact complete graph language. Clopen Boolean indicators, finite pigeonhole and powers supply the other ingredients. The obstruction couples arbitrary clopen coloring of open tubes to an exact finite-cylinder restriction and a whole-path cycle erasure. The still missing all-face construction must control its clopen observations without demanding projectivity, and must prove every live finite word source-feasible with coherent whole deletion lifts or Mittag-Leffler images.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/StoneanForwardTubeObstruction.not_has_shadowing_of_disjoint_open_forward_tubes`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteObservationSofic](FiniteObservationSofic.md)
