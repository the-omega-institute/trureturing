# The Gaussian limit for localized quantum Bernoulli noise walks

## Abstract

Every unit localized quantum Bernoulli noise state has the standard Gaussian scaling limit.

The Hilbert space is ObserverHilbertSpace (Finset ℕ), the complex space ℓ² over finite subsets of ℕ. Its coordinate unit vectors correspond to the source's orthonormal basis Zσ of the space h of square-integrable Bernoulli functionals (Section 2, equation (7)). This identification transports the source's operators and localized initial states to their coefficient sequences.

**Definition 1.1 (Annihilation at a coordinate).**

$$\forall \left(k: \mathbb{N}\right), \left(\forall \left(\varphi: \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right), \left(\forall \left(\sigma: \operatorname{Finset}\left(\mathbb{N}\right)\right), \left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.annihilation}\left(k, \varphi, \sigma\right) = \operatorname{ite}\left(\neg \left(k \in \sigma\right), \varphi\left(\operatorname{symmDiff}\left(\sigma, \left\{k\right\}\right)\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.annihilation` (`✓ std3`).

*Citation.* Caishi Wang; Ce Wang; Yuling Tang; Suling Ren (2018). *Quantum Walk in Terms of Quantum Bernoulli Noise and Quantum Central Limit Theorem for Quantum Bernoulli Noise*. DOI: [10.1155/2018/2507265](https://doi.org/10.1155/2018/2507265). URL: <https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265>.

*Commentary.*

The annihilation operator removes k from a basis index that contains it and sends every other basis vector to zero (Lemma 1, equation (8)). In coefficient form, the output at σ reads the input at σ symmetric-difference {k} when k is absent from σ. The displayed coordinate identity specifies the continuous complex-linear operator uniquely.

**Definition 1.2 (Creation at a coordinate).**

$$\forall \left(k: \mathbb{N}\right), \left(\forall \left(\varphi: \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right), \left(\forall \left(\sigma: \operatorname{Finset}\left(\mathbb{N}\right)\right), \left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.creation}\left(k, \varphi, \sigma\right) = \operatorname{ite}\left(k \in \sigma, \varphi\left(\operatorname{symmDiff}\left(\sigma, \left\{k\right\}\right)\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.creation` (`✓ std3`).

*Citation.* Caishi Wang; Ce Wang; Yuling Tang; Suling Ren (2018). *Quantum Walk in Terms of Quantum Bernoulli Noise and Quantum Central Limit Theorem for Quantum Bernoulli Noise*. DOI: [10.1155/2018/2507265](https://doi.org/10.1155/2018/2507265). URL: <https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265>.

*Commentary.*

The creation operator adds k to a basis index that does not contain it and sends every other basis vector to zero (Lemma 2, equation (9)). In coefficient form, the output at σ reads the input at σ symmetric-difference {k} when k belongs to σ. It is the adjoint of annihilation on this Hilbert space.

**Definition 1.3 (The right operator).**

$$\forall \left(k: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.R}\left(k\right): \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right) \to_{L[\mathbb{C}]} \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right) = \left(\left(\frac{1}{2}: \mathbb{C}\right)\right) \cdot \left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.creation}\left(k\right) + \operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.annihilation}\left(k\right) + \operatorname{ContinuousLinearMap.id}\left(\mathbb{C}, \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.R` (`✓ std3`).

*Citation.* Caishi Wang; Ce Wang; Yuling Tang; Suling Ren (2018). *Quantum Walk in Terms of Quantum Bernoulli Noise and Quantum Central Limit Theorem for Quantum Bernoulli Noise*. DOI: [10.1155/2018/2507265](https://doi.org/10.1155/2018/2507265). URL: <https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265>.

*Commentary.*

The right operator is half the sum of creation, annihilation and the identity, as in Lemma 5. It is the orthogonal projection onto the positive eigenspace of the coordinate flip.

**Definition 1.4 (The left operator).**

$$\forall \left(k: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.L}\left(k\right): \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right) \to_{L[\mathbb{C}]} \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right) = \left(\left(\frac{1}{2}: \mathbb{C}\right)\right) \cdot \left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.creation}\left(k\right) + \operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.annihilation}\left(k\right) - \operatorname{ContinuousLinearMap.id}\left(\mathbb{C}, \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.L` (`✓ std3`).

*Citation.* Caishi Wang; Ce Wang; Yuling Tang; Suling Ren (2018). *Quantum Walk in Terms of Quantum Bernoulli Noise and Quantum Central Limit Theorem for Quantum Bernoulli Noise*. DOI: [10.1155/2018/2507265](https://doi.org/10.1155/2018/2507265). URL: <https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265>.

*Commentary.*

The left operator is half the sum of creation and annihilation minus the identity, as in Lemma 5. Its negative is the orthogonal projection onto the negative eigenspace of the coordinate flip; this sign is retained in the walk recursion.

**Definition 1.5 (The walk with a localized initial vector).**

$$\forall \left(\varphi: \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.walk}\left(\varphi\right): \left(\mathbb{N}\right) \to \left(\left(\mathbb{Z}\right) \to \left(\operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right)\right)\right) = \operatorname{Nat.rec}\left(\lambda \left(x: \mathbb{Z}\right) \mapsto \left(\operatorname{ite}\left(x = \left(0: \mathbb{Z}\right), \varphi, \left(0: \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right)\right)\right), \lambda \left(n: \mathbb{N}\right) \mapsto \left(\lambda \left(\psi: \left(\mathbb{Z}\right) \to \left(\operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right)\right) \mapsto \left(\lambda \left(x: \mathbb{Z}\right) \mapsto \left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.R}\left(n, \psi\left(x - \left(1: \mathbb{Z}\right)\right)\right) + \operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.L}\left(n, \psi\left(x + \left(1: \mathbb{Z}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.walk` (`✓ std3`).

*Citation.* Caishi Wang; Ce Wang; Yuling Tang; Suling Ren (2018). *Quantum Walk in Terms of Quantum Bernoulli Noise and Quantum Central Limit Theorem for Quantum Bernoulli Noise*. DOI: [10.1155/2018/2507265](https://doi.org/10.1155/2018/2507265). URL: <https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265>.

*Commentary.*

At time zero the state equals φ at the integer position zero and vanishes at all other positions (equation (53)). The successor step is equation (16): the right operator acts on the state at x minus one, and the left operator acts on the state at x plus one. The definition allows every vector φ; normalization is imposed in the limit theorem.

**Definition 1.6 (The scaled position measure).**

$$\forall \left(\varphi: \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right), \left(\forall \left(n: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.walkLaw}\left(\varphi, n\right): \operatorname{Measure}\left(\mathbb{R}\right)\right) = \sum_{x \in \operatorname{Finset.Icc}\left(-\left(\operatorname{Nat.cast}\left(n\right): \mathbb{Z}\right), \left(\operatorname{Nat.cast}\left(n\right): \mathbb{Z}\right)\right)} \left(\left(\operatorname{ENNReal.ofReal}\left(\left\lVert \operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.walk}\left(\varphi, n, x\right) \right\rVert^{2}\right)\right) \cdot \left(\operatorname{Measure.dirac}\left(\frac{\left(\operatorname{Int.cast}\left(x\right): \mathbb{R}\right)}{\operatorname{Real.sqrt}\left(\left(\operatorname{Nat.cast}\left(n\right): \mathbb{R}\right)\right)}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.walkLaw` (`✓ std3`).

*Citation.* Caishi Wang; Ce Wang; Yuling Tang; Suling Ren (2018). *Quantum Walk in Terms of Quantum Bernoulli Noise and Quantum Central Limit Theorem for Quantum Bernoulli Noise*. DOI: [10.1155/2018/2507265](https://doi.org/10.1155/2018/2507265). URL: <https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265>.

*Commentary.*

The mass at the scaled position x divided by the square root of n is the squared norm of the walk amplitude at x (Section 3; the proof of Theorem 20, equations (64) and (67)). Only the integer interval from minus n to n can carry mass. The total mass is the squared norm of φ, so a unit vector gives a probability measure. At n equal to zero, real division by zero places the initial mass at zero as well.

**Theorem 1.7 (Weak convergence to the standard Gaussian).**

$$\forall \left(\varphi: \operatorname{ObserverHilbertSpace}\left(\operatorname{Finset}\left(\mathbb{N}\right)\right)\right), \left(\left(\left\lVert \varphi \right\rVert = \left(1: \mathbb{R}\right)\right) \Rightarrow \left(\forall \left(f: \operatorname{BoundedContinuousFunction}\left(\mathbb{R}, \mathbb{R}\right)\right), \left(\operatorname{Filter.Tendsto}\left(\lambda \left(n: \mathbb{N}\right) \mapsto \left(\int \left(y: \mathbb{R}\right), f\left(y\right) \operatorname{d}\left(\operatorname{D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.walkLaw}\left(\varphi, n\right)\right)\right), \operatorname{Filter.atTop}, \operatorname{nhds}\left(\int \left(y: \mathbb{R}\right), f\left(y\right) \operatorname{d}\left(\operatorname{ProbabilityTheory.gaussianReal}\left(\left(0: \mathbb{R}\right), \left(1: \operatorname{NNReal}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/wang-wang-tang-ren-2018-bernoulli-noise-walk-gaussian-limit` (proved) by `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wang-wang-tang-ren-2018-bernoulli-noise-walk-gaussian-limit","declaration_gid":"D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Caishi Wang; Ce Wang; Yuling Tang; Suling Ren (2018). *Quantum Walk in Terms of Quantum Bernoulli Noise and Quantum Central Limit Theorem for Quantum Bernoulli Noise*. DOI: [10.1155/2018/2507265](https://doi.org/10.1155/2018/2507265). URL: <https://onlinelibrary.wiley.com/doi/10.1155/2018/2507265>.

*Commentary.*

For each unit vector φ, the scaled position measures converge against every bounded continuous real function to the standard Gaussian. The initial vector is arbitrary in the whole Hilbert space. The convergence is asserted for each fixed φ and test function f; it does not assert uniformity over initial vectors.

Let Tₖ be the coordinate flip, sending the coefficient at σ to the coefficient at σ symmetric-difference {k}. Each flip is a self-adjoint isometric involution, and the flips commute. Creation plus annihilation equals Tₖ, so Rₖ = (I + Tₖ)/2 and −Lₖ = (I − Tₖ)/2 are complementary orthogonal projections. The recursion first shows that the amplitude vanishes outside the integer interval from minus n to n.

For σ contained in {0,…,n−1}, let Bₙ,σ be the ordered product, starting with the identity, of −Lₖ when k belongs to σ and Rₖ otherwise, for k less than n. The vector Bₙ,σφ is a simultaneous flip eigenvector, with eigenvalue minus one at the coordinates in σ and plus one at the other coordinates below n. Distinct subsets therefore give orthogonal vectors. Summing Bₙ,σφ over all such subsets gives φ.

The displacement associated to σ is n − 2|σ|, an integer between minus n and n. Induction in the walk recursion expresses its amplitude at x as the sum of (−1)^|σ| Bₙ,σφ over subsets with that displacement. Orthogonality removes the cross terms: the squared amplitude at x is the sum of the squared norms of Bₙ,σφ over the same subsets. The orthogonal resolution of φ makes the sum of these squared norms equal to the squared norm of φ. This proves that every scaled measure associated to a unit vector is a probability measure.

For real u define U₀(u) = I and Uₙ₊₁(u) = (cos(u) I + i sin(u) Tₙ)Uₙ(u). The one-step factor equals exp(iu)Rₙ − exp(−iu)Lₙ. Expanding the product gives Uₙ(u)φ as the sum of exp(iu(n − 2|σ|))Bₙ,σφ. The orthogonal resolution also gives ⟨φ,Bₙ,σφ⟩ = ‖Bₙ,σφ‖². Integration of the atomic position measure and regrouping by displacement now identify its characteristic function at t with ⟨φ,Uₙ(t/√n)φ⟩. Expanding the inner product of a one-step factor shows that the mixed terms cancel by self-adjointness of Tₖ, while cos²(u) + sin²(u) = 1. Thus every Uₙ(u) preserves norms.

Suppose η has nonzero coefficients only at subsets of {0,…,m−1}. The first m flip factors preserve this support. At every later step the flipped contribution has zero inner product with η. Consequently, for n at least m, ⟨η,Uₙ(u)η⟩ = cos(u)^(n−m)⟨η,Uₘ(u)η⟩. For the symmetric probability measure giving mass one half to each of 1 and −1, the mean is zero, the second moment is one, and the characteristic function is cos(u). Its central limit theorem gives cos(t/√n)^n → exp(−t²/2). The parameter t/√n tends to zero. Continuity of the finite product Uₘ at zero, where Uₘ(0) = I, and division by cos(t/√n)^m give ⟨η,Uₙ(t/√n)η⟩ → ‖η‖² exp(−t²/2).

Finite sums of coordinate unit vectors are dense in ℓ². For any finite set of coefficient indices, choose m greater than every natural number in their union; the corresponding finite vector has the required support. Norm preservation and the inner-product inequality give |⟨φ,Uₙ(u)φ⟩ − ⟨η,Uₙ(u)η⟩| ≤ (‖φ‖ + ‖η‖)‖φ − η‖, uniformly in n and u. Given ε positive, take ‖φ − η‖ < δ with δ = min(1,ε/12). Since ‖φ‖ = 1, one has ‖η‖ ≤ 2 and |‖η‖² − 1| ≤ 3‖φ − η‖. The Gaussian factor has norm at most one. The two approximation errors are therefore bounded by 3‖φ − η‖ each, and the finite-vector limit eventually bounds the middle error by ε/3. Their sum is less than ε, proving the Gaussian characteristic-function limit for every unit vector φ.

Regard the scaled measures and the standard Gaussian as probability measures. The characteristic-function criterion for weak convergence applies at every real frequency, using the standard Gaussian characteristic function exp(−t²/2). The characterization of weak convergence by integrals of bounded continuous real functions then gives exactly the displayed conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.L`
- Truth anchor: `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.R`
- Truth anchor: `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.annihilation`
- Truth anchor: `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.creation`
- Truth anchor: `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.walk`
- Truth anchor: `D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit.walkLaw`
- Dependency: [D5/S3/Analytic/Probability/UniformCDFConvergence](../../Analytic/Probability/UniformCDFConvergence.md)
- Dependency: [D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization](../../Observer/Approximation/ReadoutUpdateCommutatorFactorization.md)
