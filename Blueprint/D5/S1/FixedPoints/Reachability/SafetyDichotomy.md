# Reachability Safety Dichotomy

## Abstract

A relation-generated least fixed point either certifies all finite paths as safe or supplies a finite path to a bad state.

**Theorem 1.1 (Safety and finite counterexample paths form a dichotomy).**

$$\forall X: Type,\\{}R: \operatorname{Set}\left(X \times X\right), I_{0}, S: \operatorname{Set}\left(X\right),\\{}(\operatorname{lfp}\left(\operatorname{reachStep}\left(R, I_{0}\right)\right) \subseteq S \Rightarrow \forall x_{0} \in I_{0}, x: X, \operatorname{ReflTransGen}\left(R, x_{0}, x\right) \Rightarrow x \in S) \land \\{}(\operatorname{Nonempty}\left(\operatorname{inter}\left(\operatorname{lfp}\left(\operatorname{reachStep}\left(R, I_{0}\right)\right), X \setminus S\right)\right) \Rightarrow \exists x_{0} \in I_{0}, x \in X \setminus S, \operatorname{ReflTransGen}\left(R, x_{0}, x\right)).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/Reachability/SafetyDichotomy.reachability_safety_and_bad_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A transition relation R and initial set I0 construct the reachability operator by adjoining I0 to the direct R-image of the current approximation. Reach is the least fixed point of this operator.

If Reach is contained in the safe set S, every finite reflexive-transitive R-path beginning in I0 ends in S. This is the path-level safety clause of the source theorem.

If Reach meets the complement of S, finite-stage expansion locates the bad state at a finite iterate. Induction over that iterate constructs an initial state and a finite R-path ending outside S.

The proof imports the canonical relation-generated reachability operator and its finite-stage expansion rather than redeclaring either source object. The pinned relation closure constructors supply the exact finite path.

## References

- Truth anchor: `D5/S1/FixedPoints/Reachability/SafetyDichotomy.reachability_safety_and_bad_path`
- Dependency: [D5/S1/FixedPoints/RelationalReachExpansion](../RelationalReachExpansion.md)
