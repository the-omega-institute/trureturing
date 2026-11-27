# C5 common-bias variational bound

## Abstract

The sharp normalized rank-one common-bias gain for signed five-cycle matrices.

**Theorem 1.1 (Independent-pair weight).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5CommonGain.pairWeight_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuC5CommonGain.pairWeight_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative weights on C5, the sum of the five step-two pair products is at most one quarter of the squared total weight. Applying PosteriorMomentDistance.edge_bound to i ↦ w(2i) modulo five sends each cycle edge to a step-two pair and permutes the five weights.

**Theorem 1.2 (Centered common field).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5CommonGain.commonField_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuC5CommonGain.commonField_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every SignedCycle representation, Hermitian base and occupation matrices, real controls tᵢ, and a nonnegative common occupation weight a, the centered Hamiltonian is bounded above by (3a + 2√(a² + sumᵢtᵢ²/2))I. With S = sumᵢ tᵢ² and D = sumᵢ tᵢ²tᵢ₊₂², the pair-weight bound makes S² − 4D nonnegative. The two nonnegative roots of y² − Sy + D supply the quadratic factors for the matrix reflection bound.

**Theorem 1.3 (Complex control upper bound).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5CommonGain.ladderField_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuC5CommonGain.ladderField_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex lowering controls cᵢ, local phase removal converts each control to a nonnegative magnitude without changing the signed relations. The common-field Loewner bound therefore holds with sumᵢ‖cᵢ‖².

**Theorem 1.4 (Normalized rank-one gain).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5CommonGain.gain_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuC5CommonGain.gain_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any finite signed ladder representation of C5, for a unit vector v and bias x ≥ 0, the sum of squared complex lowering expectations minus x times the actual hole probabilities is at most (1 − x)²/2. The proof chooses phases from the individual expectations and applies realGain_le to the resulting phaseCycle, using commonField_le and the original hole projections.

**Theorem 1.5 (Explicit attainment in the ordered spin model).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5CommonGain.spin_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuC5CommonGain.spin_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0 ≤ x ≤ 1, the ordered five-mode spin representation has a unit vector whose gain is exactly (1 − x)²/2. The witness uses p = √((1+x)/2) and q = √((1−x)/2) on the two independent superposed sites, with the other three occupation bits filled.

**Definition 1.6 (Ordered five-mode spin ladders).**

Lean statement: `D5/S3/Quantum/Fermionic/WuC5CommonGain.spinLadders`

*Formalization.* `D5/S3/Quantum/Fermionic/WuC5CommonGain.spinLadders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The five-mode lowering matrices act on 32 occupation words through bit flips with signs from earlier neighbors. They satisfy the signed ladder relations.

## Source comparison with Wu

The comparison with Wu v1, Eqs. (2.1), (2.4), (3.20)–(3.26), and (3.54)–(3.55), is an ordinary calculation outside Lean. Fix the C5 signs, all five μᵢ⁴ = exp(β), finite β ≥ 0, and 1 < s < ∞. In the convention of Eq. (3.22), Jᵢ is the adjoint of the normalized γᵢ and uses earlier neighbors, as in spinLadders. Put Qᵢ = JᵢJᵢ* for the hole projection, Pᵢ = I − Qᵢ, Zᵢ = Pᵢ − Qᵢ, a = 1/(1+exp(β)), and b = 1 − a. The thermal density ρ is the product of the commuting factors aQᵢ + bPᵢ. Wu's conjectural inequality (3.54) concerns positive invertible inputs, arbitrary finite signed-spin systems and sign patterns, and 1 ≤ μᵢ⁴ ≤ exp(β). The following calculation concerns the rank-one boundary of the fixed C5 system.

The Wick-degree generator uses the jumps Kᵢ = (∏ⱼ∼ᵢ Zⱼ)Jᵢ. Each neighboring Zⱼ cancels the sign of Jᵢ against both ladder letters at site j, and nonneighbors already commute. The occupation projections at all other sites commute as well. The i-th summand is Lᵢ(X) = {bQᵢ + aPᵢ, X} − 2b Kᵢ X Kᵢ* − 2a Kᵢ* X Kᵢ, where {A, X} = AX + XA. Using KᵢKᵢ* = Qᵢ and Kᵢ*Kᵢ = Pᵢ gives Lᵢ(I) = 0, Lᵢ(Jᵢ) = Jᵢ, Lᵢ(Jᵢ*) = Jᵢ*, and Lᵢ(Qᵢ) = 2bQᵢ − 2aPᵢ = 2(Qᵢ − aI). Thus the local Wick degrees are 0, 1, 1, 2. Commutation with the other-site letters carries this action to their ordered Wick products, so the sum of the Lᵢ multiplies each Wick word by its degree.

On an occupation word η, the diagonal unitary U has entry (−1)^(∑_{edges {k,l}} ηₖηₗ). Flipping bit i changes its sign by (−1)^(∑ⱼ∼ᵢ ηⱼ), which equals ∏ⱼ∼ᵢ (2ηⱼ − 1) because each C5 site has two neighbors. Thus Kᵢ = UJᵢU is the later-neighbor jump string, and U commutes with ρ and Qᵢ. For a unit vector v, put rᵢ = ⟨v,Qᵢv⟩ and zᵢ = ⟨v,Kᵢv⟩. These are the hole probability and the lowering expectation in spinLadders on Uv.

Take the symmetric embedding M = ρ^(1/(2s)) X ρ^(1/(2s)) = m vv* with m > 0. Conjugating Kᵢ by ρ^(1/(2s)) on the left and its inverse on the right gives exp(−β/(2s))Kᵢ, and the adjoint jump has the reciprocal multiplier. Hence the embedded jumps have weights b exp(−β/s) and a exp(β/s), with the factor −2 from Lᵢ. After division by Tr(M^s), each jump trace with its weight factored out is |zᵢ|². The normalized anticommutator trace is 2[a + (b − a)rᵢ]. The rank-one spectral entropy cancels its trace-normalization term, leaving −⟨v,(log ρ)v⟩, or −log b + βrᵢ per site.

Write K = s²/(2(s−1)) and α = αₛ*(β) as in Eq. (3.55). Put c = a exp(β/s) + b exp(−β/s), d = b − a − αβ/K, and F = K a + α log b. Multiplying the traces by the Dirichlet prefactor K/2 in Eq. (2.4) and subtracting α times entropy gives the normalized deficit ∑ᵢ [F + Kd rᵢ − Kc |zᵢ|²] = 5F − Kc gain(spinLadders, Uv, d/c). For β > 0, let τ = tanh(β/2). Then c = cosh((1/2−1/s)β)/cosh(β/2) and αβ/K = (1−c)/τ. The inequality c ≥ sech²(β/2) gives d = (c+τ²−1)/τ ≥ 0. The bound c ≤ 1 gives c−d = (1−τ)(1+τ−c)/τ > 0. At β = 0, c = 1 and d = 0. Thus 0 ≤ d/c < 1. Since U is unitary, the gain bound and its attaining vector give the exact minimum normalized deficit 5F − K(c−d)²/(2c), or 5F − 2Kg with g = (c−d)²/(4c).

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5CommonGain.commonField_le`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5CommonGain.gain_le`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5CommonGain.ladderField_le`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5CommonGain.pairWeight_le`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5CommonGain.spinLadders`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuC5CommonGain.spin_attains`
- Dependency: [D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance](../../ConceptDynamics/ObservationOrder/PosteriorMomentDistance.md)
- Dependency: [D5/S3/Quantum/Fermionic/WuC5TransferReflection](WuC5TransferReflection.md)
