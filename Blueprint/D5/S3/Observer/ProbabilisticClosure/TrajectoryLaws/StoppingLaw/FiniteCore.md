# A full finite stopping law determines constructors and geometry

## Abstract

A full finite stopping law determines constructors and geometry

Observation retains the hidden endpoint value, optional output, return indicator and exact paid count. fullMass averages the two phase sections using a fair independent phase and the iid biased spins. lawWindow(T) contains the actual spin support of the tree and the target vertices. HasStoppingLaw equates every observation mass to stoppingMass, including the tuples of mass zero.

The input tree permits none leaves, repeated reads, separator reads, arbitrary binary branching and wrong output labels. A height cap and the full law first reconstruct its unpadded stopping comb. The recovered zero-prefix masses then determine its integer edge geometry.

**Theorem 1.1 (Finite inverse stopping-law theorem).**

$$\forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{T} : \operatorname{ReadTree}), (((1 \le \operatorname{k}) \land (\operatorname{height} (\operatorname{T}) \le \operatorname{k}) \land (\operatorname{HasStoppingLaw} (\operatorname{beta}, \operatorname{lawWindow} (\operatorname{T}), \operatorname{j}, \operatorname{k}, \operatorname{T}))) \to (\exists (\operatorname{es} : \operatorname{List} (\operatorname{Int})), ((\operatorname{length} (\operatorname{es}) = \operatorname{k}) \land (\operatorname{Nodup} (\operatorname{es})) \land (\exists (\operatorname{L} : \operatorname{Int}), ((\operatorname{T} = \operatorname{stopComb} (\operatorname{mapAddresses} (\operatorname{es}, \operatorname{not} (\operatorname{j})))) \land (\operatorname{toFinset} (\operatorname{es}) = \operatorname{pathEdges} (\operatorname{L}, \operatorname{k})) \land (\operatorname{notMem} (\operatorname{toInt} (\operatorname{j}), \operatorname{pathVertices} (\operatorname{L}, \operatorname{k})))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore.finite_full_law_forces_stopping_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

mapAddresses(es,phi) maps each edge e to the original integer address 2e+toInt(phi). Constructor reconstruction forces exactly k read nodes: a zero reply continues and a one reply returns a1, with final zero return a0. The edge list is duplicate-free, its set is a consecutive interval, and the target spin vertex lies outside that interval. Each prefix may extend either endpoint.

**Theorem 1.2 (Infinite iid source agrees with the finite window).**

$$\forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{T} : \operatorname{ReadTree}), (\forall (\operatorname{z} : \operatorname{Observation}), (\operatorname{real} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{observationEvent} (\operatorname{j}, \operatorname{T}, \operatorname{z})) = \operatorname{fullMass} (\operatorname{beta}, \operatorname{lawWindow} (\operatorname{T}), \operatorname{j}, \operatorname{T}, \operatorname{z})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore.sourceLaw_observation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

observationEvent(j,T,z) is the source event observation(j,phase,T,spins)=z. The source law is fairPhase.prod spinLaw. Finite coordinate projection identifies its probability with the finite-window fullMass, while the visible and hidden formulas keep the original endpoint.

**Theorem 1.3 (A first remote read has the required prefix mass).**

$$\forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{T} : \operatorname{ReadTree}), (((1 \le \operatorname{k}) \land (\operatorname{height} (\operatorname{T}) \le \operatorname{k}) \land (\operatorname{HasStoppingLaw} (\operatorname{beta}, \operatorname{lawWindow} (\operatorname{T}), \operatorname{j}, \operatorname{k}, \operatorname{T}))) \to (\exists (\operatorname{m} : \operatorname{Nat}), ((1 \le \operatorname{m}) \land (\operatorname{m} \le \operatorname{k}) \land (\operatorname{remoteMass} (\operatorname{beta}, \operatorname{lawWindow} (\operatorname{T}), \operatorname{j}, ((2 * \operatorname{k}) + 1), \operatorname{T}) = \frac{(1 + \operatorname{T} (\operatorname{beta}, \operatorname{m}))}{2}) \land (\frac{(1 + \operatorname{T} (\operatorname{beta}, \operatorname{k}))}{2} \le \operatorname{remoteMass} (\operatorname{beta}, \operatorname{lawWindow} (\operatorname{T}), \operatorname{j}, ((2 * \operatorname{k}) + 1), \operatorname{T}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore.finite_remote_read_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every permitted bias beta, endpoint j, k at least one and tree T of height at most k satisfying HasStoppingLaw in lawWindow(T), the remote-read source event has probability at least (1+T(k))/2. Remote means distance at least 2k+1 from j, and the proof concerns an actual executed read. The first remote node at position m is reached after m-1 zero replies; its phase-averaged mass is (1+T(m))/2, and antitonicity gives the stated lower bound.

Actual source events are measurable cylinder events supported on the finite tree window. Their finite and infinite product masses agree exactly.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore.finite_full_law_forces_stopping_path`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore.finite_remote_read_section`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore.sourceLaw_observation`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity](PathRigidity.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization](SemanticNormalization.md)
