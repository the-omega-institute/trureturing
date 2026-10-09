# Spectral contraction of the Token-1 transfer map

## Abstract

Token-1 damping strictly contracts the spectrum and every centered trajectory.

**Definition 1.1 (The stacked next-coordinate matrix).**

$$\forall m \in \mathbb{N},\; \forall v \in \operatorname{Fin}\left(m + 1\right) \to \mathbb{R},\; \forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{A}\left(m, v, i, j\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) \bmod 2 = 0, \operatorname{ite}\left(i = j, 1, 0\right), \operatorname{ite}\left(i = j, v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right) + v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right), \operatorname{ite}\left(\operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right), -\left(2 \cdot v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)\right), \operatorname{ite}\left(\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right), -\left(2 \cdot v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)\right), 0\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.A` (`✓ std3`).

*Citation.* T. Wallner, D. Krupke, A. Schmidt, and S. P. Fekete (2026). *Pass the Bucket: Efficient, Robust, Local Load Balancing for Teams of Heterogeneous Robots*. DOI: [10.48550/arXiv.2608.27085](https://doi.org/10.48550/arXiv.2608.27085). URL: <https://arxiv.org/abs/2608.27085v1>.

*Commentary.*

Stacking these m relations yields a three-banded system A x′ = B x + c ⇔ x′ = A⁻¹ B x + A⁻¹ c, where A and B reflect the coefficients of x′ and x in the odd/even relations, and c collects the constants. (Section IV, page 3.) The source has m = n − 1 adjacent pairs. Pair i here has source index i + 1; an odd source row therefore has i.val mod 2 = 0. The velocities of its two robots are v(Fin.castSucc i) and v(Fin.succ i). The centered endpoint coordinates are zero.

**Definition 1.2 (The stacked original-coordinate matrix).**

$$\forall m \in \mathbb{N},\; \forall v \in \operatorname{Fin}\left(m + 1\right) \to \mathbb{R},\; \forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{B}\left(m, v, i, j\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) \bmod 2 = 0, \operatorname{ite}\left(i = j, -1, \operatorname{ite}\left(\operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right), \frac{2 \cdot v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)}{v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right) + v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)}, \operatorname{ite}\left(\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right), \frac{2 \cdot v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)}{v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right) + v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)}, 0\right)\right)\right), \operatorname{ite}\left(i = j, -\left(v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right) + v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)\right), 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.B` (`✓ std3`).

*Citation.* T. Wallner, D. Krupke, A. Schmidt, and S. P. Fekete (2026). *Pass the Bucket: Efficient, Robust, Local Load Balancing for Teams of Heterogeneous Robots*. DOI: [10.48550/arXiv.2608.27085](https://doi.org/10.48550/arXiv.2608.27085). URL: <https://arxiv.org/abs/2608.27085v1>.

*Commentary.*

Stacking these m relations yields a three-banded system A x′ = B x + c ⇔ x′ = A⁻¹ B x + A⁻¹ c, where A and B reflect the coefficients of x′ and x in the odd/even relations, and c collects the constants. (Section IV, page 3.) These are exactly the coefficients of the original coordinates in the source odd/even relations; missing neighbors contribute zero.

**Definition 1.3 (The Token-1 right-coordinate matrix).**

$$\forall m \in \mathbb{N},\; \forall v \in \operatorname{Fin}\left(m + 1\right) \to \mathbb{R},\; \forall a \in \mathbb{R},\; \forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; \left(B_{\alpha}\right)\left(m, v, a, i, j\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) = 0, \operatorname{ite}\left(i = j, \frac{v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right) \cdot \left(1 - 2 \cdot a\right) - a \cdot v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)}{v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right) + a \cdot v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)}, \operatorname{ite}\left(\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right), \frac{2 \cdot a \cdot v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)}{v\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right) + a \cdot v\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)}, 0\right)\right), \operatorname{B}\left(m, v, i, j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.Balpha` (`✓ std3`).

*Citation.* T. Wallner, D. Krupke, A. Schmidt, and S. P. Fekete (2026). *Pass the Bucket: Efficient, Robust, Local Load Balancing for Teams of Heterogeneous Robots*. DOI: [10.48550/arXiv.2608.27085](https://doi.org/10.48550/arXiv.2608.27085). URL: <https://arxiv.org/abs/2608.27085v1>.

*Commentary.*

This changes only the first pair’s relation: 2x₁/v₁ + (x′₁ − x₁)/(αv₁) = (x₂ − x₁)/v₂ + (x₂ − x′₁)/v₂, all other equations remain unchanged. In matrix form, with the same A, replace B by Bα and obtain u′ = Mαu, with Mα := A⁻¹Bα. (Section IV.B.1, page 4.) The displayed real parameter a denotes the source α. Solving the first travel-time equation for x′₁ gives the displayed first row. Every remaining row equals B. B_α displays the Lean definition Balpha.

**Definition 1.4 (The literal damped transfer map).**

$$\forall m \in \mathbb{N},\; \forall v \in \operatorname{Fin}\left(m + 1\right) \to \mathbb{R},\; \forall a \in \mathbb{R},\; \left(M_{\alpha}\right)\left(m, v, a\right) = \operatorname{A}\left(m, v\right)^{-1} \cdot \left(B_{\alpha}\right)\left(m, v, a\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.Malpha` (`✓ std3`).

*Citation.* T. Wallner, D. Krupke, A. Schmidt, and S. P. Fekete (2026). *Pass the Bucket: Efficient, Robust, Local Load Balancing for Teams of Heterogeneous Robots*. DOI: [10.48550/arXiv.2608.27085](https://doi.org/10.48550/arXiv.2608.27085). URL: <https://arxiv.org/abs/2608.27085v1>.

*Commentary.*

This changes only the first pair’s relation: 2x₁/v₁ + (x′₁ − x₁)/(αv₁) = (x₂ − x₁)/v₂ + (x₂ − x′₁)/v₂, all other equations remain unchanged. In matrix form, with the same A, replace B by Bα and obtain u′ = Mαu, with Mα := A⁻¹Bα. (Section IV.B.1, page 4.) The displayed a denotes α. Matrix inverse is Mathlib's inverse; positive velocities make A invertible. M_α displays the Lean definition Malpha.

**Definition 1.5 (Conjecture 1 in all finite dimensions).**

$$\operatorname{claim}\left(\right) = (\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left(\forall v \in \operatorname{Fin}\left(m + 1\right) \to \mathbb{R},\; \left(\forall j \in \operatorname{Fin}\left(m + 1\right),\; 0 < v\left(j\right)\right) \Rightarrow \left(\forall a \in \mathbb{R},\; 0 < a \Rightarrow \left(a < 1 \Rightarrow \left(\left(\forall c \in \mathbb{C},\; c \in \operatorname{spectrum}\left(\mathbb{C}, \operatorname{Matrix}.\operatorname{map}\left(\left(M_{\alpha}\right)\left(m, v, a\right), \operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right)\right) \Rightarrow \left\lVert c \right\rVert < 1\right) \land \left(\forall u \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \operatorname{Filter}.\operatorname{Tendsto}\left((\lambda k:\mathbb{N},\operatorname{Matrix}.\operatorname{mulVec}\left(\left(M_{\alpha}\right)\left(m, v, a\right)^{k}, u\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(0\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.claim` (`✓ std3`).

*Citation.* T. Wallner, D. Krupke, A. Schmidt, and S. P. Fekete (2026). *Pass the Bucket: Efficient, Robust, Local Load Balancing for Teams of Heterogeneous Robots*. DOI: [10.48550/arXiv.2608.27085](https://doi.org/10.48550/arXiv.2608.27085). URL: <https://arxiv.org/abs/2608.27085v1>.

*Commentary.*

Conjecture 1 (Spectral contraction): The damped transfer map Mα is repeatedly applied and its spectral radius satisfies ρ(Mα) < 1, such that u → 0 for 0 < α < 1. (Section IV.B.1, page 4.) The encoding ranges over every m ≥ 1, every positive vector v : Fin(m + 1) → ℝ and every real a with 0 < a < 1. The first conjunct bounds every complex spectral value of the complexification of Mα. In finite dimension this is strict spectral-radius contraction. The second conjunct states Filter.Tendsto to the zero real vector for every initial u. The same damped map is used at every power.

**Theorem 1.6 (Strict spectrum bound and convergence).**

$$\operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.result` (`✓ std3`). ∎

*Resolves.* `Problems/wallner-krupke-schmidt-fekete-2026-token-spectral-contraction` (proved) by `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wallner-krupke-schmidt-fekete-2026-token-spectral-contraction","declaration_gid":"D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* T. Wallner, D. Krupke, A. Schmidt, and S. P. Fekete (2026). *Pass the Bucket: Efficient, Robust, Local Load Balancing for Teams of Heterogeneous Robots*. DOI: [10.48550/arXiv.2608.27085](https://doi.org/10.48550/arXiv.2608.27085). URL: <https://arxiv.org/abs/2608.27085v1>.

*Commentary.*

The weighted Dirichlet form Q(z) is the sum of |zⱼ − zⱼ₋₁|²/vⱼ with both endpoint values zero. Every local reflection preserves Q. The damped event is (1 − θ)I + θE₁, where θ = a(v₁ + v₂)/(v₂ + av₁) lies strictly between zero and one. Its Q-loss vanishes exactly when E₁ fixes the vector. A hypothetical unit-modulus eigenvector is then an undamped eigenvector fixed by E₁. For eigenvalue one, weighted Dirichlet rigidity forces zero; for every other unit-modulus eigenvalue, its first coordinate vanishes and the row recurrence propagates zero through the chain. Thus every spectral modulus is strictly below one. The finite-dimensional power-decay theorem gives convergence of every real centered trajectory.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.A`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.B`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.Balpha`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.Malpha`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.result`
- Dependency: [D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance](../../../ConceptDynamics/Coding/FixedPositivePartitionSseDistance.md)
- Dependency: [D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics](FinitePathDynamics.md)
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordPathRealizations](../../Measurements/CliffordJointMeasurability/CliffordPathRealizations.md)
