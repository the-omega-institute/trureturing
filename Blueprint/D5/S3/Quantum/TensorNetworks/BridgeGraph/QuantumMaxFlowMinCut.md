# QuantumMaxFlowMinCut

## Abstract

QuantumMaxFlowMinCut supplies the width-three bridge max-flow proof.

Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.

**Definition 1.1 (claim).**

$$\operatorname{QuantumMaxFlowMinCut.claim} \iff (\forall (a b c d : \mathbb{N}) , 0 < a \to a \leq b \to 0 < c \to c \leq d \to a \cdot a + b \cdot b \leq 3 \cdot a \cdot b \to c \cdot c + d \cdot d \leq 3 \cdot c \cdot d \to \operatorname{QuantumMaxFlowBound.QMaxFlow} a b c d = \operatorname{QuantumMaxFlowBound.QMinCut} a b c d \land \operatorname{QuantumMaxFlowBound.QMinCut} a b c d = min (a \cdot d) (b \cdot c))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut.claim` (`✓ std3`).

*Citation.* Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan (2025). *Quantum max-flow in the bridge graph*. DOI: [10.1007/s00031-024-09863-2](https://doi.org/10.1007/s00031-024-09863-2). URL: <https://arxiv.org/abs/2212.09794v2>.

*Commentary.*

Conjecture 1.4, page 6: “Let (a, b), (a′, b′) ∈ U_w ∪ V_w ∪ W_w. Then” followed by “QMaxFlow = QMinCut = min{a·b′, a′·b}” with the bridge-diagram arguments. Conjecture 3.14 repeats this on page 19. Conjecture 3.15, page 19: “Let (a, b), (a′, b′) ∈ U_3 ∪ V_3 ∪ W_3. Then” followed by “QMinCut = QMaxFlow = min{a′b, ab′}” at width three. The parameters are positive natural dimensions, and (a,b,c,d)=(a,b,a′,b′). The source region is exactly a ≤ b and a*a+b*b ≤ 3*a*b: its larger ratio endpoint is (3+√5)/2, as derived in the cited note. Both equalities are retained.

**Theorem 1.2 (result).**

$$\operatorname{QuantumMaxFlowMinCut.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan (2025). *Quantum max-flow in the bridge graph*. DOI: [10.1007/s00031-024-09863-2](https://doi.org/10.1007/s00031-024-09863-2). URL: <https://arxiv.org/abs/2212.09794v2>.

*Commentary.*

The unconditional width-three settlement combines a rational cyclic shift construction, short and long reservoir Schur complements, scalar extension to complex matrices, and castling deficit preservation followed by strong induction on b+d. Proposition 3.18 of the source derives Conjecture 1.4 at every w≥3 from this case; that general-width implication is a literature reading, not a theorem formalized here.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut.claim`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut.result`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/CastlingDeficit](CastlingDeficit.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/LongReservoir](LongReservoir.md)
