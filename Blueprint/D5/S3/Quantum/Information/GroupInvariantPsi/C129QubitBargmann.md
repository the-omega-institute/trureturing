# C129 qubit three-label orientation

## Abstract

The ordered qubit Bargmann trace is the Bloch scalar-plus-oriented-volume formula.

**Definition 1.1 (Pauli combination).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.pauliCombination`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.pauliCombination` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit two by two complex matrix with the three real coordinates in the Pauli X, Y and Z slots.

**Definition 1.2 (Bloch projector expression).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.qubitProjector`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.qubitProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affine half-sum of the identity matrix and the Pauli combination. Unit Bloch vectors give the pure-qubit projector case.

**Definition 1.3 (Ordered triple trace).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.tripleBargmann`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.tripleBargmann` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace of the ordered product of the three Bloch projector expressions.

**Definition 1.4 (Rank-one state projector).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateProjector`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rank-one density matrix built from a two-component complex amplitude vector.

**Definition 1.5 (Computational basis state).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vZero`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude vector for the state |0⟩.

**Definition 1.6 (Real equatorial state).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vPlus`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude vector (|0⟩+|1⟩)/√2.

**Definition 1.7 (Positive Y state).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYPlus`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude vector (|0⟩+i|1⟩)/√2.

**Definition 1.8 (Negative Y state).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYMinus`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYMinus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude vector (|0⟩−i|1⟩)/√2.

**Definition 1.9 (State triple trace).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateTripleBargmann`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateTripleBargmann` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace of the ordered product of three rank-one state projectors.

**Theorem 1.10 (Bloch formula for the ordered qubit trace).**

$$\forall r \in (\operatorname{Fin}\left(3\right)) \to (\mathbb{R}),\; \forall s \in (\operatorname{Fin}\left(3\right)) \to (\mathbb{R}),\; \forall t \in (\operatorname{Fin}\left(3\right)) \to (\mathbb{R}),\; \operatorname{tripleBargmann}\left(r, s, t\right) = \frac{\operatorname{Complex.ofReal}\left((1: \mathbb{R}) + \operatorname{dotProduct}\left(r, s\right) + \operatorname{dotProduct}\left(s, t\right) + \operatorname{dotProduct}\left(t, r\right)\right)}{4} + \frac{\operatorname{Complex.ofReal}\left(\operatorname{dotProduct}\left(r, \operatorname{crossProduct}\left(s, t\right)\right)\right) \cdot \mathrm{i}}{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.triple_bargmann_bloch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity is proved by expanding the three explicit two by two matrices. It is stated for arbitrary real three-coordinate vectors; unit-norm vectors give the pure-qubit interpretation from the source atom. The scalar terms are the three pairwise dot products and the imaginary term is the oriented scalar triple product.

**Theorem 1.11 (Opposite Bloch orientations).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_qubit_orientation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_qubit_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered coordinate triples (0,0,1), (1,0,0), and (0,±1,0) give the two values (1+i)/4 and (1-i)/4. The pairwise dot products vanish while the oriented triple product changes sign.

**Theorem 1.12 (Explicit pure-state witnesses).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_state_orientation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_state_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For v₁=|0⟩, v₂=(|0⟩+|1⟩)/√2, and v₃±=(|0⟩±i|1⟩)/√2, the rank-one density matrices have ordered traces (1±i)/4. This records the concrete two-sign witness; the remaining geometric interpretation of zero added orthogonal remainder stays in the source prose.

## Application: an unordered pair comparison loses a cyclic direction

Use precisely the normalized vectors v₁=vZero, v₂=vPlus, v₃⁺=vYPlus and v₃⁻=vYMinus above, with the label order (1,2,3) fixed. Write Pⱼ=|vⱼ⟩⟨vⱼ| and Tᵢⱼ=Tr(PᵢPⱼ)=|⟨vᵢ|vⱼ⟩|². For either sign the full table has diagonal 1 and every off-diagonal entry 1/2: T=[[1,1/2,1/2],[1/2,1,1/2],[1/2,1/2,1]]. Each triple consists of three distinct rays, and the two choices of the third ray are distinct. Thus every pair is comparable, with Tᵢⱼ=Tⱼᵢ; reversing the arguments of this comparison changes no result.

The existing explicit_state_orientation theorem gives B⁺=Tr(P₁P₂P₃⁺)=(1+i)/4 and B⁻=(1−i)/4. If a function of T alone recovered the ordered B on both triples, the identical argument T would have two different outputs, a contradiction. This excludes recovery by any postprocessing of that table, including a random procedure whose output law depends only on T. It does not say that arbitrary quantum protocols on the actual input states have identical statistics. The observation has discarded information; further arithmetic on it cannot restore that information.

## Conditional cycle readout and its supplied resources

Assume three separately prepared, stored qubits with the joint product promise R=P₁⊗P₂⊗P₃; for pure inputs put V=v₁⊗v₂⊗v₃. Also supply a control qubit initially |0⟩, coherent controlled permutation access, a calibrated phase between its two branches, and the usual quantum state, unitary-operation and Born measurement rules. Define C|a,b,c⟩=|b,c,a⟩, so (CV)(a,b,c)=V(c,a,b). This direction gives ⟨V|C|V⟩=B, not its conjugate. The three input vectors need no common global-phase locking: their independent scalar phases multiply V by one overall phase and cancel from every density matrix and B.

Let q have modulus one. Apply a Hadamard to the control, then the controlled C with relative branch factor q, then a second Hadamard, and measure the control in the computational basis. The middle operation is diag(I,qC); its phase is relative to the unchanged control-0 branch. The output is |0⟩⊗K₀V+|1⟩⊗K₁V, where K₀=(I+qC)/2 and K₁=(I−qC)/2. These are actual data-system Kraus operators, not a definition of a scalar called probability. Since C†C=I and q̄q=1, K₀†K₀+K₁†K₁=I. Consequently R↦KₐRKₐ† is a normalized two-outcome finite instrument, with one Kraus operator per outcome.

The parameter correspondence to finite_kraus_instrument_born_marginal is: n=Fin 2×(Fin 2×Fin 2), Setting=Unit, Outcome=Fin 2, Kraus=Unit, instrumentKraus((),a,())=Kₐ, and rho=R as a DensityState. PureStateHandshake.rankOneDensity supplies R=|V⟩⟨V|, with V normalized; positivity and trace one put it in the existing DensityState carrier. The theorem identifies the branch trace with FiniteDimensional.bornProbability(R,Eₐ), where Eₐ=Kₐ†Kₐ. Thus the operation uses the repository's existing Born/instrument semantics. It does not introduce a new measurement postulate or a new Lean declaration.

For either of these product inputs, expanding E₀ gives [2I+qC+q̄C†]/4, with E₁=I−E₀. Taking its Born trace against R, using Tr(R)=1 and Tr(RC)=B, gives p₀=(1+Re(qB))/2 and p₁=(1−Re(qB))/2. In particular q=1 reads Re B. With the declared left-cycle direction, q=−i reads Im B: the branch phase gate is diag(1,−i). Reversing C conjugates B and reverses this imaginary-part sign; q=+i with the present C instead gives p₀=(1−Im B)/2. A permutation symbol alone, without its action on tensor factors and its phase convention, is insufficient to fix that sign.

For the two explicit inputs, q=1 gives (p₀,p₁)=(5/8,3/8) for both. With the same calibrated q=−i device, the plus triple gives (5/8,3/8) and the minus triple gives (3/8,5/8). These are different Bernoulli laws despite the identical pair table. They allow statistical discrimination through repeated independent preparations and readouts. Both outcomes have positive probability under either input, so a decision based on this one binary result cannot identify the sign perfectly. The phase-sensitive apparatus accesses a joint cyclic relation that is absent from T. Preparing a product, preserving the registers, and coherently interfering the branches are additional resources, not consequences of knowing T.

## Geometry, reference transformations and limits

The Bloch vectors are r₁=(0,0,1), r₂=(1,0,0), r₃±=(0,±1,0). Their pair dot products vanish, while r₁·(r₂×r₃±)=±1. The existing Bloch formula therefore makes Im B one quarter of this oriented volume. Here B is nonzero, so its argument is defined. Relating that phase to an oriented spherical geodesic triangle requires a declared path and geometric-phase sign convention; it does not identify Bloch orientation with spatial chirality. In particular the source volume uses −arg B for its specified geometric-phase convention.

Independent rephasing of the input vectors leaves B invariant, and a common unitary change of basis preserves its trace-product value. Common complex conjugation sends B to its conjugate. Conjugating the inputs alone while keeping the calibrated q=−i apparatus fixed exchanges the two displayed output laws. Conjugating the entire experiment, including the phase reference q, instead conjugates qB and preserves its real part and all these probabilities. A nonreal B rules out making this entire tuple simultaneously real while preserving that invariant. It does not rule out every real simulation with enlarged state space or extra encoding.

The application is the known three-state Bargmann cycle test specialized to this owner's qubit witnesses, not a literature novelty. Oszmaniec, Brod and Galvão, Measuring relational information between quantum states, and applications, arXiv:2109.10006v1, equation (1), Figure 1 and the qubit example on PDF pages 1–3 provide the primary reference; Library/HilbertOperators/oszmaniec2021relational.md records the version and convention boundaries. The many-body exchange character readout and the renewal-instrument posterior cycle are different inputs and protocols. No claim here reconstructs arbitrary complex Gram data from pair intensities, resolves every zero-edge overlap network with triangles, derives Born or Lüders rules, selects a complex field from raw kernel positivity, or completes quantum origins.

In plain terms, every pair in either triple can be compared, and reversing the two endpoints leaves its strength unchanged; the two comparison tables are identical. Yet following the three states around a cycle in a chosen direction can retain an oriented phase absent from the table. If we are additionally supplied with three independently prepared quantum states whose joint state is promised to be a product, storage, a control qubit, a coherent controlled cyclic permutation, a fixed calibrated relative phase reference between the control branches, and Born readout rules, this direction can produce different measurement frequencies. With the declared left cycle and q=−i, the same apparatus gives outcome zero with probability 5/8 for the plus triple and 3/8 for the minus triple. Repeated independent preparations and readouts can distinguish their statistics, but a single readout does not identify the triple perfectly. The pair strengths omit this three-state relation, and the readout needs the stated resources. Pairwise comparability alone derives neither these operations nor the whole quantum theory.

## References

- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_qubit_orientation`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.explicit_state_orientation`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.pauliCombination`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.qubitProjector`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateProjector`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.stateTripleBargmann`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.tripleBargmann`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.triple_bargmann_bloch`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vPlus`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYMinus`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vYPlus`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.vZero`
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../PureState/PureStateHandshake.md)
