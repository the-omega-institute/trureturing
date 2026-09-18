# Uniform Height Bound for Residue Identification

## Abstract

Every complete prime-power residue node admits an identifying passive protocol with at most (e-d)(p-1) queries on every target.

Let p be prime and let e and d be natural numbers with d at most e. For a label b in ZMod(p^d), B is the node of residues in X=ZMod(p^e) whose depth-d projection is b. Its remaining height is e-d. Tree means PassiveProtocol X with natural-number answers. The sensor q(c,a)=residueReadout(p,e,c,a) returns the greatest congruence depth of its center and target, including zero and e. R(T,a) means runPassiveProtocol q T a; it records both centers and their actual answers.

**Theorem 1.1 (An identifying tree with a uniform bound on realized traces).**

$$\forall p \in \mathbb{N}, \forall e \in \mathbb{N}, \operatorname{Prime}\left(p\right) \Rightarrow \forall d \in \mathbb{N}, \left(d \leq e\right) \Rightarrow \forall b \in \operatorname{ZMod}\left(p^{d}\right), \exists T \in Tree, \operatorname{Ident}\left(\operatorname{node}\left(p, e, d, b\right), T\right) \land \forall a \in \operatorname{node}\left(p, e, d, b\right), \operatorname{len}\left(\operatorname{R}\left(T, a\right)\right) \leq \left(e-d\right)\left(p-1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ResidueHeightUpperBound.residue_height_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tree exists for every label and every allowed depth. Ident(B,T) means that equal complete traces of targets in B imply equal targets. The length bound holds separately for every target in B, without an averaging measure or an assumed family of bounded child trees. Centers remain actual residues in X.

Induct on the remaining height. At height zero the node has one element, and the stop tree suffices. At height one its p leaves have an arbitrary enumeration. The leaf protocol realizes the capped position lengths, at most p-1; its existence follows by assigning constant positive mass to all leaves.

At greater heights the induction hypothesis constructs an identifying bounded tree for each of the p complete children. Extracting the chronological prefix for a singleton child gives a tree headed inside that child. Removing this constant prefix cannot increase any realized length. The child is nonleaf, so the extracted tree has the required head. Splicing these actual trees in any child order yields an identifying parent tree. For a target in position i, numbered from zero, the trace has exactly i failed sibling entries followed by its child trace. Since i is at most p-1, its length is at most (p-1)+(e-d-1)(p-1). The final child needs no additional entry query.

For any strictly positive normalized rational prior, transport this tree to its full-history selector. The transport preserves each complete terminal trace and its length. Hence at every integer horizon t at least (e-d)(p-1), this eventually zero-error terminating selector succeeds on all of B. Every selector's successful mass is bounded above by the total mass of B, so the maximum over all original selectors equals that total mass. No cutoff truncation or deletion of delays in arbitrary selectors is needed. In particular the statement includes p=2, e=0 and d=e. It asserts no evaluator or runtime bound.

## References

- Truth anchor: `D5/S3/Observer/Budget/ResidueHeightUpperBound.residue_height_upper_bound`
- Dependency: [D5/S3/Observer/Budget/ResidueChildPrefixStructure](ResidueChildPrefixStructure.md)
- Dependency: [D5/S3/Observer/Budget/ResidueFirstStepOptimality](ResidueFirstStepOptimality.md)
- Dependency: [D5/S3/Observer/Budget/ResidueLeafOptimality](ResidueLeafOptimality.md)
- Dependency: [D5/S3/Observer/Budget/ResiduePosteriorClosure](ResiduePosteriorClosure.md)
