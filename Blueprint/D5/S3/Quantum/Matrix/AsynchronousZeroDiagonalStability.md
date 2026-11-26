# A sharp boundary for real asynchronous histories

## Abstract

The signed three-block family has a sharp boundary between convergence for every bounded constant delay and explicit nondecaying real histories.

All coordinates and initial histories are real. History slot zero is the newest slot. For the three singleton blocks, write B(c,d,δ,K)=asyncMatrix (family c d) δ K, using the constant-delay history matrix. Its newest row is (By)₀,ᵢ=Σⱼ Mᵢⱼ yδⱼᵢ,ⱼ, with source-to-destination delay δⱼᵢ; its other rows satisfy (By)ₛ,ᵢ=yₛ₋₁,ᵢ. Thus Bᵗy is the actual history after t updates, not a free trajectory. In the formulas e₀=(0,⟨0,0⟩) is the newest coordinate in block zero, ev(v,e₀)=v(e₀), and mulVec(B,y) is Matrix.mulVec B y.

**Definition 1.1 (Three singleton block coordinates).**

Lean statement: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.Coord`

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.Coord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coord is Vtx (fun i : Fin 3 => 1): each coordinate is a block i in Fin 3 together with its unique internal coordinate in Fin 1.

**Definition 1.2 (Every retained history slot).**

Lean statement: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.History`

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.History` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural K, History K is Fin (K+1) × Coord. An arbitrary function y : History K → R prescribes every real slot from time −K through time zero.

**Definition 1.3 (The signed zero-diagonal family).**

Lean statement: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.family`

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary real c,d, family c d is the matrix on Coord with rows (0,1,1), (c,0,0), and (−d,0,0), read by block coordinate. All three diagonal entries vanish.

**Definition 1.4 (A fixed positive remote-delay array).**

Lean statement: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.fixedDelay`

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.fixedDelay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixedDelay array, written fixedDelay in the formula and δ* in the explanation, has rows (0,1,2), (1,0,1), and (2,1,0). It has zero local delays, positive remote delays and maximum delay two.

**Definition 1.5 (Nonnegative arrays bounded by K).**

Lean statement: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.bounded`

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.bounded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For K in N and δ : Fin 3 → Fin 3 → N, bounded K δ means δᵢᵢ=0 for every i and δᵢⱼ≤K for every i,j. Remote entries may be zero.

**Definition 1.6 (Positive remote entries).**

Lean statement: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.remotePositive`

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.remotePositive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

remotePositive K δ means bounded K δ together with 0<δᵢⱼ whenever i≠j. Entries on zero matrix coefficients still satisfy this requirement.

**Definition 1.7 (Convergence for every real initial history).**

Lean statement: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.stable`

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.stable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

stable c d K δ means that, for every y : History K → R, the newest-slot vector i ↦ (B(c,d,δ,K)ᵗ y)(0,i) tends to the zero vector as the natural time t tends to infinity. No bound, sign condition or compatibility condition is imposed on y.

**Theorem 1.8 (All bounded delays and explicit boundary histories).**

$$\forall (\lambda: \mathbb{R}), (\forall (c: \mathbb{R}), ((\lambda^{2} \le c) \Rightarrow (((2 \cdot c - \lambda^{2} < 1) \Leftrightarrow (\forall (K: \mathbb{N}), (\forall (\delta: \operatorname{Fin}\left(3\right) \to \left(\operatorname{Fin}\left(3\right) \to \mathbb{N}\right)), ((\operatorname{bounded}\left(K, \delta\right)) \Rightarrow (\operatorname{stable}\left(c, c - \lambda^{2}, K, \delta\right)))))) \land (((2 \cdot c - \lambda^{2} < 1) \Leftrightarrow (\operatorname{stable}\left(c, c - \lambda^{2}, 2, fixedDelay\right))) \land ((\forall (K: \mathbb{N}), ((2 \le K) \Rightarrow (((2 \cdot c - \lambda^{2} < 1) \Leftrightarrow (\forall (\delta: \operatorname{Fin}\left(3\right) \to \left(\operatorname{Fin}\left(3\right) \to \mathbb{N}\right)), ((\operatorname{bounded}\left(K, \delta\right)) \Rightarrow (\operatorname{stable}\left(c, c - \lambda^{2}, K, \delta\right))))) \land ((2 \cdot c - \lambda^{2} < 1) \Leftrightarrow (\forall (\delta: \operatorname{Fin}\left(3\right) \to \left(\operatorname{Fin}\left(3\right) \to \mathbb{N}\right)), ((\operatorname{remotePositive}\left(K, \delta\right)) \Rightarrow (\operatorname{stable}\left(c, c - \lambda^{2}, K, \delta\right)))))))) \land (((2 \cdot c - \lambda^{2} = 1) \Rightarrow (\forall (K: \mathbb{N}), ((2 \le K) \Rightarrow (\exists (y: \operatorname{History}\left(K\right) \to \mathbb{R}), ((\forall (t: \mathbb{N}), (\operatorname{mulVec}\left(\operatorname{B}\left(c, c - \lambda^{2}, fixedDelay, K\right)^{t + 4}, y\right) = \operatorname{mulVec}\left(\operatorname{B}\left(c, c - \lambda^{2}, fixedDelay, K\right)^{t}, y\right))) \land (\forall (m: \mathbb{N}), (\operatorname{ev}\left(\operatorname{mulVec}\left(\operatorname{B}\left(c, c - \lambda^{2}, fixedDelay, K\right)^{4 \cdot m}, y\right), e_{0}\right) = 1))))))) \land ((1 < 2 \cdot c - \lambda^{2}) \Rightarrow (\forall (K: \mathbb{N}), ((2 \le K) \Rightarrow (\exists (r: \mathbb{R}), ((1 < r) \land (\exists (y: \operatorname{History}\left(K\right) \to \mathbb{R}), (\forall (m: \mathbb{N}), (\operatorname{ev}\left(\operatorname{mulVec}\left(\operatorname{B}\left(c, c - \lambda^{2}, fixedDelay, K\right)^{4 \cdot m}, y\right), e_{0}\right) = r^{4 \cdot m}))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.whole_theorem_three_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put d=c−λ² and S=2c−λ². The formal theorem allows arbitrary real λ,c with λ²≤c, so c≥0 and d≥0, including zero endpoints. The source theorem under 0<λ<1 is a direct instance of this stronger statement. When S<1, positive coordinate weights make the absolute update rows strictly contractive. Weights on the older history slots then give a geometric bound for every coordinate of every matrix power applied to an arbitrary real history. The bound tends to zero and therefore also gives convergence of the newest-slot vector. Its rate may depend on K; no single rate independent of K is asserted. When S≥1, one can choose a positive r≥1 with r⁶=cr²+d, taking r=1 at S=1 and r>1 at S>1. For z=ir, the real parts of zᵗ, czᵗ⁻² and −dzᵗ⁻³ satisfy the three delayed update equations for every integer t. Their values at times −K through zero form a real history for δ*, and its matrix-power orbit is exactly this solution. At time 4m the newest first coordinate equals r⁴ᵐ. For r=1 the entire history orbit is four-periodic and cannot tend to zero; for r>1 this subsequence grows exponentially. The same fixed array is available in both bounded classes whenever K≥2. No fixed-bound necessity is asserted for K=0 or K=1.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.Coord`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.History`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.bounded`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.family`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.fixedDelay`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.remotePositive`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.stable`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability.whole_theorem_three_one`
- Dependency: [D5/S3/Quantum/Matrix/AsynchronousTwoBlockSpectrum](AsynchronousTwoBlockSpectrum.md)
