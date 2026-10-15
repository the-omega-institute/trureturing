# Compact Observation Factorization

## Abstract

Compact observation fibers determine every continuous finite readout and every finite action window.

**Theorem 1.1 (Finite readouts and bounded action windows).**

$$\begin{gathered}\forall f \in \operatorname{C}(X, Y), \exists N, \exists! g: Q_{N}\to Y, \forall x, g(q_{N}(x))=f(x),\\\forall H, \exists N, \forall x,y, q_{N}(x)=q_{N}(y) \Rightarrow \forall w, \operatorname{length}(w)\leq H \Rightarrow o(F_{w}(x))=o(F_{w}(y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.compact_observation_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a nonempty compact topological space. For each natural number n, let Q_n be a finite discrete space and q_n : X → Q_n a continuous surjection. Let p_n : Q_(n+1) → Q_n satisfy q_n(x) = p_n(q_(n+1)(x)) for every x. Assume that all actual singleton fibers of all q_n form a topological basis for X. Let Y be any finite discrete space. C(X,Y) denotes all continuous maps X → Y.

The second conclusion holds for every finite action type Σ, every family of continuous total maps F_a : X → X, every continuous observation o : X → Y, and every natural horizon H. Words are all lists over Σ of length at most H. The existing runWord executes the head action first and then the tail, so F_(uv) = F_v ∘ F_u. Empty words, H = 0, empty action types, repeated actions, and noninvertible actions remain included.

Adjacent compatibility propagates equality from level N to every level n ≤ N. For each x, continuity makes the inverse image of the singleton {f(x)} open. The basis supplies a singleton observation fiber containing x inside that inverse image. IsTopologicalBasis.exists_subset_of_mem_open supplies this neighborhood directly.

IsCompact.elim_finite_subcover selects finitely many of those open fibers covering X. Take the finite supremum of their levels. Two points with equal observations at that level agree at the level of any selected fiber containing the first point; consequently both lie in that fiber and have equal f-values. This uniform fiber constancy is the compactness step.

Apply split_surjection_factorization to q_N and f, using Function.surjInv and Function.rightInverse_surjInv for the section of the actual surjection. This gives existence and uniqueness of g on the entire Q_N. The level N need not be unique. No independent inhabitant of Y is required by this construction; whenever f is given, a point of the nonempty X also supplies an element of Y.

For the window conclusion, List.finite_length_le proves that the subtype W_H of all bounded words is finite. The response map x ↦ (w ↦ o(runWord F w x)) takes values in the finite discrete product W_H → Y. Word induction and continuous_pi prove its continuity. Applying the finite-readout factorization to this response map supplies one level for the entire window. Every bounded list enters the product as its own subtype element.

Only compactness and the actual fiber basis are used on X. The statement assumes neither a separation axiom nor a metric nor finiteness of X, and it assumes no inverse-limit representation. The conclusions are existence statements and provide no effective finite-subcover procedure or computable bound on N. OrdinaryReadout in FiniteStageReadout is a colimit of stage maps; its representative theorem alone does not establish the factorization of an arbitrary continuous map considered here.

## References

- Truth anchor: `D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization.compact_observation_factorization`
- Dependency: [D5/S0/Rewriting/Quotients/SplitSurjectionFactorization](../../../S0/Rewriting/Quotients/SplitSurjectionFactorization.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../Prediction/ControlledBehaviorUniversality.md)
