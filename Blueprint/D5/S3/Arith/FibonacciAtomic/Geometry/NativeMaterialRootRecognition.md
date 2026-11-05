# Original Material Root Recognition

## Abstract

Original material roots and syntax are rigid under complete linear terminal order; finite labelled presentations admit an effective inverse.

**Theorem 1.1 (Universal Original Root and Coordinate Rigidity).**

$$\forall t: Source, (\forall s: Source, ((\operatorname{D}\left(t\right)) \implies ((\operatorname{D}\left(s\right)) \implies ((\operatorname{atLeastThreeLeaves}\left(t\right)) \implies ((\operatorname{atLeastThreeLeaves}\left(s\right)) \implies (\forall e: \operatorname{OrderedIso}\left(t, s\right), ((\operatorname{forward}\left(e, \operatorname{nil}\left(\right)\right) = \operatorname{nil}\left(\right)) \land ((\forall p: Address, ((\operatorname{member}\left(p, \operatorname{material}\left(t\right)\right)) \implies (\operatorname{forward}\left(e, p\right) = p))) \land (t = s)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.original_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source is the existing FreeMagma Bool, with true denoting alpha and false beta. D(t) says that readout(pL,t) is never alpha, for every logical address p. Both sources range over this original domain and have at least three logical leaves. No global substitution image, positivity restriction, or alternate birth condition is used.

C(alpha) is one terminal vertex. C(beta) has its logical root and a distinct left terminal marker. C(pair(l,r)) has its root and both ordered child material trees. The material list retains every vertex, including each beta marker; addresses use the existing Boolean lists and readout. The full terminal list recursively concatenates left then right rosters and replaces a beta logical leaf by its marker. Neighbors comprise outward children and the actual parent, with no supplied orientation in the isomorphism: neighborhood images are permutations, while the entire terminal list image is an equality at every position.

A nonroot vertex of material degree two is a beta root with an adjacent degree-one marker. A branch root with no terminal neighbor is consequently the unique degree-two vertex without one. If the root has a terminal neighbor, original birth typing rules out a left alpha; that neighbor is the last terminal in the complete linear order. In the latter case both compared roots adjoin that same last terminal, whose unique neighbor forces root preservation. This excludes root ambiguity before any ordered navigation is assumed.

Root preservation gives depth preservation in both directions, so children map outward. Each child has a terminal descendant. The complete linear terminal order rules out reversing two children, and a beta has its sole left marker child. Induction identifies every material coordinate. Support equality then gives literal readout equality; the existing source_foundation leaf-equality theorem identifies the original ordered source and all its logical constructors.

**Theorem 1.2 (Uniform Finite Recognition without Concealed Advice).**

$$(\forall I: FiniteInput, (\forall R: Recovery, ((\operatorname{recover}\left(I\right) = \operatorname{some}\left(R\right)) \implies ((\operatorname{Fits}\left(I, R\right)) \land (\operatorname{completeDegreeOneRoster}\left(I\right)))))) \land ((\forall I: FiniteInput, (\forall R: Recovery, ((\operatorname{Fits}\left(I, R\right)) \implies ((\operatorname{recover}\left(I\right) = \operatorname{some}\left(R\right)) \land (\forall S: Recovery, ((\operatorname{Fits}\left(I, S\right)) \implies (S = R))))))) \land ((\operatorname{recover}\left(sixVertex\right) = \operatorname{some}\left(sixRecovery\right)) \land (\forall S: Recovery, ((\operatorname{Fits}\left(sixVertex, S\right)) \implies (S = sixRecovery)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.effective_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FiniteInput supplies only its own vertex enumeration Fin(n), an arbitrary neighbor list for each vertex, and the complete linear terminal list. Recovery contains an original source and one material address for every input vertex. Fits checks coordinate length, permutation of the entire material support, every neighborhood permutation, the complete terminal list equality, the executable original birth check, and at least three logical leaves. It contains no assumed uniqueness or termination field.

recover enumerates sources of exact material size n and all permutations of their material coordinates, then returns the first candidate satisfying Fits. The finite syntax catalog uses n as its recursion fuel and splits each pair size into its two positive child sizes. Its bounds come entirely from the supplied input. There is no runtime root, original term, Tag, old word, external size bound, or image witness.

Every actual relabelling is a Fits witness only in the correctness proof. Catalog completeness supplies a candidate. Two successes induce a full unrooted terminal-order-preserving material isomorphism; universal rigidity identifies their sources and every vertex coordinate. Thus recovery returns the unique original parse. The input vertex whose recovered coordinate is empty is its original root. The complete degree-one roster is derived from the material representation and neighbor equations.

The same correctness path checks the existing six-vertex LAB14.2 input for pair(pair(beta,alpha),alpha). Vertex indices are r=0,h=1,b=2,c=3,d=4,e=5; edges are r-h,r-e,h-b,h-d,b-c and the ordered terminals are c,d,e. Its candidate certificate is checked and passed to the uniform inverse theorem. The rival rooting at b lies outside D and is not a counterexample to this result.

This is effectiveness by finite exhaustive search, with no polynomial runtime claim. Wave acquisition, first arrivals and subdivision reconstruction; weighted field laws, paid trials and the last-trial cut; persistent fields, guards, framing and adaptive growth; source binding, authority, calibration and backing; zero-field four-view common-image recovery; old serialization; and LAB7/15 numerical resource claims are separate obligations. No physical installation or full callable service is constructed here.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.effective_inverse`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.original_rigidity`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](../ActualLeafHistoryRigidity.md)
