# Common Four-Sector Decomposition

## Abstract

Commuting orthogonal projections admit the common four-sector decompositions.

**Theorem 1.1 (Commuting projections have four equivalent decompositions).**

$$\begin{gathered}\forall k, H: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{NormedAddCommGroup}(H)],\ [\operatorname{InnerProductSpace}(k, H)],\ [\operatorname{CompleteSpace}(H)],\\\forall P, Q: \operatorname{ContinuousLinearEnd}(k, H),\ \operatorname{Projection}(P) \land \operatorname{Projection}(Q),\\S_{11}=PQ,\quad S_{10}=P(I-Q),\quad S_{01}=(I-P)Q,\quad S_{00}=(I-P)(I-Q),\\\left[PQ=QP\right] \Leftrightarrow \left[\forall a, b\in \{0,1\},\ \operatorname{Projection}(S_{ab})\right] \Leftrightarrow\\\left[\operatorname{OrthogonalFamily}(\operatorname{Ran}(S_{ab})) \land \operatorname{InternalDirectSum}(\operatorname{Ran}(S_{ab}))\right] \Leftrightarrow\\\left[\exists R,\ (\forall a, b\in \{0,1\},\ \operatorname{Projection}(R_{ab})) \land\\(\forall a, b, c, d\in \{0,1\},\ ((a,b)\neq(c,d)\Rightarrow R_{ab}R_{cd}=0)) \land\\\sum_{a,b\in\{0,1\}}R_{ab}=I \land\\P=R_{10}+R_{11} \land Q=R_{01}+R_{11}\right].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommutingProjectionFourSector.commuting_projection_four_sector_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P and Q be orthogonal projections on an arbitrary complete real or complex inner-product space. Define the four sector operators by S11 = PQ, S10 = P(I-Q), S01 = (I-P)Q, and S00 = (I-P)(I-Q).

The theorem retains all four conditions of the named source statement. They are: commutation of P and Q; projection of every sector operator; orthogonality and internal direct-sum completeness of the four ranges; and existence of four pairwise orthogonal projection outcomes whose sum is the identity and whose two marginals are P and Q.

The reverse direct-sum implication uses uniqueness of sector components to make distinct sector products vanish, which recovers PQ = QP without a finite-dimensional or closed-range assumption.

Loogle returned IsStarProjection.mul as an exact result for products of commuting projections, and the proof applies it. Pinned Mathlib also supplied the orthogonal-family, star-projection range, and internal direct-sum declarations used in the proof. Repository and LeanSearch queries found no theorem packaging the complete four-condition criterion.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CommutingProjectionFourSector.commuting_projection_four_sector_criterion`
