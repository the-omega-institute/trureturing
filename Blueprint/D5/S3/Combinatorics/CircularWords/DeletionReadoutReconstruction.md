# Reconstruction from Labeled Circular Deletions

## Abstract

Labeled one-label deletions recover the orientation of a circle on at least four distinct labels.

A circular word is a Mathlib Cycle: lists are identified under rotation and retain their orientation. Fix a finite support A. SupportedCircle(A) consists of actual circles C with C.Nodup and C.toFinset = A. The xth observation is CircularDeletionTransport.delete(x,C), the oriented residual obtained by filtering out x. The deleted label remains the index of the observation. There is no assumed injectivity, no quotient by reversal, and no unlabeled multiset of observations.

**Theorem 1.1 (Four or More Labels Determine the Circle).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall C \in \mathrm{Cycle}\left(T\right),\; \forall D \in \mathrm{Cycle}\left(T\right),\; ((4 \le \mathrm{card}\left(A\right)) \land ((\mathrm{Nodup}\left(C\right)) \land ((\mathrm{Nodup}\left(D\right)) \land (((\mathrm{support}\left(C\right) = A) \land (\mathrm{support}\left(D\right) = A)) \land (\forall x \in T,\; (x \in A) \Rightarrow (\mathrm{delete}\left(x, C\right) = \mathrm{delete}\left(x, D\right))))))) \Rightarrow (C = D)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction.reconstruct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a label r in A and rotate both circles to begin with r. Write their representatives as r,a,L and r,b,K. They have at least four distinct labels, so there exists x in A distinct from r,a,b. Deleting x leaves representatives beginning with r,a and r,b. The existing CyclicInsertionGap.anchored_coe_injective theorem turns equality of their circular classes into equality of these lists, hence a = b. Now delete a itself. Since a occurs once, the residual representatives are r,L and r,K. Apply anchored uniqueness again to obtain L = K. This constructs reconstruction from the deletion equalities rather than assuming it.

**Theorem 1.2 (The Exact Faithfulness Threshold).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; (3 \le \mathrm{card}\left(A\right)) \Rightarrow ((\mathrm{jointKernel}\left(\mathrm{deletionReadout}\left(A\right)\right) = \mathrm{diagonal}\left(\mathrm{SupportedCircle}\left(A\right)\right)) \Leftrightarrow (4 \le \mathrm{card}\left(A\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction.deletion_joint_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set X = SupportedCircle(A), take index type A, output type Cycle(Ambient), and define q(x,C) = delete(x,C). The reconstruction theorem proves that equal outputs for every index force equality in X. Applying JointFaithfulnessLeibnizCriterion.joint_faithfulness_tfae identifies the intersection of these observation kernels with the equality diagonal. For supports of at least three labels, this equality holds if and only if there are at least four labels: the opposite three-label orientations supply the failure direction. Thus the existing abstract concept-family criterion has a concrete circular-word application: joint readout loses no circular state, although each individual deletion forgets its insertion gap. The kernel statement concerns deterministic observations and does not assert a probability model, noisy-channel recovery, or a computational reconstruction bound.

For three distinct labels a,b,c, the circles [a,b,c] and [a,c,b] differ by orientation. Anchored uniqueness proves they are distinct. Deleting any of a,b,c leaves the same two-label circle, because its two possible list orders differ by rotation. This is the obstruction used in the forward direction of the exact kernel threshold theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction.deletion_joint_kernel_iff`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction.reconstruct`
- Dependency: [D5/S3/Combinatorics/CircularWords/CyclicInsertionGap](CyclicInsertionGap.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
