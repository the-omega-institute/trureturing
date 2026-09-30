# The six-cycle graph state is not strongly 2-resistant

## Abstract

The six-cycle graph state is not strongly 2-resistant: tracing out qubits 0 and 2 leaves a convex combination of products across the cut {1} | {3,4,5}. The C5 clause of the question is not answered here.

**Definition 1.1 (Full separability).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall rho \in \operatorname{Matrix}\left((V)\to Bool, (V)\to Bool, \mathbb{C}\right),\; \operatorname{IsFullySeparable}\left(rho\right) \Leftrightarrow (\exists k \in \mathbb{N},\; \exists p \in (\operatorname{Fin}\left(k\right))\to \mathbb{R},\; \exists sigma \in (\operatorname{Fin}\left(k\right))\to (V)\to \operatorname{DensityState}\left(Bool\right),\; (\forall j \in \operatorname{Fin}\left(k\right),\; 0 \le p\left(j\right)) \land ((\sum_{j:\operatorname{Fin}\left(k\right)} (p\left(j\right)) = 1) \land (\forall x \in (V)\to Bool,\; \forall y \in (V)\to Bool,\; rho\left(x, y\right) = \sum_{j:\operatorname{Fin}\left(k\right)} (\operatorname{ofReal}\left(p\left(j\right)\right) \cdot \prod_{v:V} (\operatorname{val}\left(sigma\left(j, v\right)\right)\left(x\left(v\right), y\left(v\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsFullySeparable` (`✓ std3`).

*Citation.* Zicheng Han; Wanchen Zhang; Xiande Zhang (2026). *A five-qubit 1-resistant graph state and stabilizer marginal certificates*. URL: <https://arxiv.org/abs/2606.08561v1>.

*Commentary.*

Zhang et al., arXiv:2505.06567v1, page 2, equation (1): "A state is fully separable if it can be written as a convex combination of product states,". Han, Zhang and Zhang, arXiv:2606.08561v1, page 2, Section II.A: "A mixed state ρ on H₁ ⊗ · · · ⊗ H_N is called fully separable if it can be written as" the displayed convex sum, "where p_α ≥ 0, ∑_α p_α = 1, and each ρ_i^(α) is a one-particle density operator". V labels the qubits, configurations are functions V -> Bool, and DensityState is the positive semidefinite trace-one complex matrix carrier. The map val forgets the density-state proof. Real weights are embedded into C in the entrywise equality.

**Definition 1.2 (Biseparability with explicit qubit reindexing).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall rho \in \operatorname{Matrix}\left((V)\to Bool, (V)\to Bool, \mathbb{C}\right),\; \operatorname{IsBiseparable}\left(rho\right) \Leftrightarrow (\exists k \in \mathbb{N},\; \exists p \in (\operatorname{Fin}\left(k\right))\to \mathbb{R},\; \exists A \in (\operatorname{Fin}\left(k\right))\to \operatorname{Finset}\left(V\right),\; \exists sigma \in (j:\operatorname{Fin}\left(k\right))\to \operatorname{DensityState}\left((A\left(j\right))\to Bool\right),\; \exists tau \in (j:\operatorname{Fin}\left(k\right))\to \operatorname{DensityState}\left((A\left(j\right)^{c})\to Bool\right),\; (\forall j \in \operatorname{Fin}\left(k\right),\; 0 \le p\left(j\right)) \land ((\sum_{j:\operatorname{Fin}\left(k\right)} (p\left(j\right)) = 1) \land ((\forall j \in \operatorname{Fin}\left(k\right),\; (\operatorname{Nonempty}\left(A\left(j\right)\right)) \land (\operatorname{Nonempty}\left(A\left(j\right)^{c}\right))) \land (\forall x \in (V)\to Bool,\; \forall y \in (V)\to Bool,\; rho\left(x, y\right) = \sum_{j:\operatorname{Fin}\left(k\right)} (\operatorname{ofReal}\left(p\left(j\right)\right) \cdot \operatorname{val}\left(sigma\left(j\right)\right)\left((\lambda (v:A\left(j\right)), x\left(\operatorname{val}\left(v\right)\right)), (\lambda (v:A\left(j\right)), y\left(\operatorname{val}\left(v\right)\right))\right) \cdot \operatorname{val}\left(tau\left(j\right)\right)\left((\lambda (v:A\left(j\right)^{c}), x\left(\operatorname{val}\left(v\right)\right)), (\lambda (v:A\left(j\right)^{c}), y\left(\operatorname{val}\left(v\right)\right))\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsBiseparable` (`✓ std3`).

*Citation.* Wanchen Zhang; Zicheng Han; Fei Shi; Xiande Zhang (2025). *New constructions of multipartite entanglement resistant to particle loss*. URL: <https://arxiv.org/abs/2505.06567v1>.

*Commentary.*

Zhang et al., arXiv:2505.06567v1, page 2, following equation (3): "where the first sum goes over all bipartitions of [N]. If a state does admit such a decomposition, it is called biseparable". A_j and its complement are nonempty subsets of V. In a carrier position a finite set denotes its subtype, and (j : Fin k) -> T(j) denotes a dependent function type. Restricting x and y to these complementary subsets explicitly pulls back sigma_j tensor tau_j to the original configuration basis. The finite mixture permits different cuts in different terms; flattening the two finite convex sums in equation (3) gives this single sum.

**Definition 1.3 (Genuine multipartite entanglement).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall rho \in \operatorname{Matrix}\left((V)\to Bool, (V)\to Bool, \mathbb{C}\right),\; \operatorname{IsGME}\left(rho\right) \Leftrightarrow (\neg \operatorname{IsBiseparable}\left(rho\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsGME` (`✓ std3`).

*Citation.* Wanchen Zhang; Zicheng Han; Fei Shi; Xiande Zhang (2025). *New constructions of multipartite entanglement resistant to particle loss*. URL: <https://arxiv.org/abs/2505.06567v1>.

*Commentary.*

Zhang et al., arXiv:2505.06567v1, page 2: "An N-particle state ρ on Hilbert space H₁ ⊗ · · · ⊗ H_N is genuinely entangled if it cannot be decomposed into as" equation (3), the convex mixture across bipartitions. Thus GME is the negation of biseparability. These predicates are applied to normalized density matrices in the state question.

**Definition 1.4 (Joining lost and retained configurations).**

$$\forall V \in Type,\; [\operatorname{DecidableEq}\left(V\right)], \forall J \in \operatorname{Finset}\left(V\right),\; \forall z \in (J)\to Bool,\; \forall x \in (\{w:V\mid\neg w \in J\})\to Bool,\; \forall v \in V,\; \operatorname{joinBits}\left(J, z, x, v\right) = \operatorname{dite}\left(v \in J, (\lambda h, z\left(\langle v,h\rangle\right)), (\lambda h, x\left(\langle v,h\rangle\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.joinBits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In a carrier position J denotes the subtype {w : V | w is in J}, and {w : V | w is not in J} denotes the complementary subtype. The dependent conditional dite joins z and x by the membership test. Its first h binder carries a membership proof and its second h binder carries a nonmembership proof; the angle brackets are the actual subtype constructors. Proof irrelevance makes the branch values independent of the proof terms. The function restrictions and this join are inverse coordinate maps between V -> Bool and (J -> Bool) times ({w : V | w is not in J} -> Bool).

**Definition 1.5 (Finite partial trace over a loss set).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall rho \in \operatorname{Matrix}\left((V)\to Bool, (V)\to Bool, \mathbb{C}\right),\; \forall J \in \operatorname{Finset}\left(V\right),\; \forall x \in (\{w:V\mid\neg w \in J\})\to Bool,\; \forall y \in (\{w:V\mid\neg w \in J\})\to Bool,\; \operatorname{partialTrace}\left(rho, J\right)\left(x, y\right) = \sum_{z:(J)\to Bool} (rho\left(\operatorname{joinBits}\left(J, z, x\right), \operatorname{joinBits}\left(J, z, y\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.partialTrace` (`✓ std3`).

*Citation.* Wanchen Zhang; Zicheng Han; Fei Shi; Xiande Zhang (2025). *New constructions of multipartite entanglement resistant to particle loss*. URL: <https://arxiv.org/abs/2505.06567v1>.

*Commentary.*

Zhang et al., arXiv:2505.06567v1, page 2: "Take the partial trace over all particles in J ⊂ [N], and denote the reduced state" ρ_J̄(ψ) ≜ Tr_J(|ψ⟩⟨ψ|), equation (2). Here the finite sum is the existing bipartite partialTraceFirst after reindexing with joinBits: the same traced configuration z appears in the row and column. This definition also applies to a general input matrix rho.

**Definition 1.6 (Cycle graph-state amplitudes).**

$$\forall n \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)], \forall x \in (\operatorname{Fin}\left(n\right))\to Bool,\; \operatorname{cycleGraphState}\left(n, x\right) = \frac{(-1)^{\sum_{i:\operatorname{Fin}\left(n\right)} (\operatorname{toNat}\left(x\left(i\right)\right) \cdot \operatorname{toNat}\left(x\left(\langle\operatorname{NatMod}\left(\operatorname{val}\left(i\right) + 1, n\right)\rangle\right)\right))}}{\operatorname{ofReal}\left(\sqrt{2^{n}}\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.cycleGraphState` (`✓ std3`).

*Citation.* Zicheng Han; Wanchen Zhang; Xiande Zhang (2026). *A five-qubit 1-resistant graph state and stabilizer marginal certificates*. URL: <https://arxiv.org/abs/2606.08561v1>.

*Commentary.*

Han, Zhang and Zhang, arXiv:2606.08561v1, page 2, Section II.B: "The graph state |G⟩ is obtained by preparing each qubit in" |+⟩ = (|0⟩ + |1⟩)/√2 "and applying a controlled-Z gate along each edge:" |G⟩ = (∏_{{u,v} ∈ E} CZ_uv)|+⟩^⊗N. Qubits are numbered 0,...,n-1, Bool.toNat sends false to 0 and true to 1. NatMod(a,n) denotes Nat.mod a n, the natural-number remainder. The angle brackets denote the Fin n element whose value is the displayed remainder; the successor index uses val(i)+1 modulo n. For n >= 3 the edge sum counts each edge of C_n once, so this controlled-Z definition gives the displayed amplitudes. The square root and division are in R and C respectively; the formula also defines a vector for other positive n.

**Definition 1.7 (Strong resistance to particle loss).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall psi \in ((\operatorname{Fin}\left(n\right))\to Bool)\to \mathbb{C},\; \operatorname{IsStrongResistant}\left(m, psi\right) \Leftrightarrow ((\operatorname{IsGME}\left(\operatorname{vecMulVec}\left(psi, \operatorname{star}\left(psi\right)\right)\right)) \land ((\forall J \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{card}\left(J\right) = m) \Rightarrow (\operatorname{IsGME}\left(\operatorname{partialTrace}\left(\operatorname{vecMulVec}\left(psi, \operatorname{star}\left(psi\right)\right), J\right)\right))) \land (\forall J \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{card}\left(J\right) = m + 1) \Rightarrow (\operatorname{IsFullySeparable}\left(\operatorname{partialTrace}\left(\operatorname{vecMulVec}\left(psi, \operatorname{star}\left(psi\right)\right), J\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsStrongResistant` (`✓ std3`).

*Citation.* Wanchen Zhang; Zicheng Han; Fei Shi; Xiande Zhang (2025). *New constructions of multipartite entanglement resistant to particle loss*. URL: <https://arxiv.org/abs/2505.06567v1>.

*Commentary.*

Zhang et al., arXiv:2505.06567v1, page 3, Definition 2: "A genuinely entangled state |ϕ⟩ is called strong m-resistant if it satisfies the following properties: 1) ρ_J̄(ϕ) is genuinely entangled for any J ⊂ [N] with |J| = m. 2) ρ_J̄(ϕ) is fully separable for any J ⊂ [N] with |J| = m + 1." The initial genuinely entangled state supplies the first conjunct. Fin n replaces [N] by zero-based labels, losses are finite subsets, and psi is the amplitude vector; vecMulVec(psi,star(psi)) is |psi><psi|. The two universal quantifiers retain both loss conditions verbatim.

**Definition 1.8 (The C6 clause of the published question).**

$$claim \Leftrightarrow (\operatorname{IsStrongResistant}\left(2, \operatorname{cycleGraphState}\left(6\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.claim` (`✓ std3`).

*Citation.* Zicheng Han; Wanchen Zhang; Xiande Zhang (2026). *A five-qubit 1-resistant graph state and stabilizer marginal certificates*. URL: <https://arxiv.org/abs/2606.08561v1>.

*Commentary.*

Han, Zhang and Zhang, arXiv:2606.08561v1, page 8, Discussion: "Several open problems remain. First, do C₅ and C₆ give strongly m-resistant graph states for m = 1 and m = 2, respectively? Here, “strong” means genuine multipartite entanglement rather than mere entanglement.". This claim encodes only the C6, m = 2 clause, on labels 0,...,5 with amplitudes (-1) raised to the cyclic edge phase, divided by 8. The C5, m = 1 clause remains open here.

**Theorem 1.9 (A two-qubit loss destroys genuine multipartite entanglement).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zicheng Han; Wanchen Zhang; Xiande Zhang (2026). *A five-qubit 1-resistant graph state and stabilizer marginal certificates*. URL: <https://arxiv.org/abs/2606.08561v1>.

*Commentary.*

For J = {0,2}, write the traced bits as t,u and the retained bits as r,x,y,z on qubits 1,3,4,5. The six-cycle phase splits as (t+u)r + xy + yz + ux + tz. Set a_tu(r) = (-1)^((t+u)r) and b_tu(x,y,z) = (-1)^(xy+yz+ux+tz). The marginal is (1/4) times the sum over the four t,u of (a_tu a_tu* / 2) tensor (b_tu b_tu* / 8). Each factor is positive semidefinite with trace one, and the four nonnegative weights sum to one. This is a product mixture across the nontrivial cut {1} | {3,4,5}; it is biseparable and violates the requirement that every two-qubit-loss marginal be GME.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsBiseparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsFullySeparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsGME`
- Truth anchor: `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsStrongResistant`
- Truth anchor: `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.cycleGraphState`
- Truth anchor: `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.joinBits`
- Truth anchor: `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.partialTrace`
- Truth anchor: `D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence](LocalObservationPartialTraceEquivalence.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
