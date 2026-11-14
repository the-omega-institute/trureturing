# C1 local fibers and dimension obstruction

## Abstract

Actual local fibers of finite-dimensional real C1 maps

**Theorem 1.1 (The vertical rank criterion).**

$$\forall (kappa: Type*), ([\operatorname{DivisionRing}\left(kappa\right)] \forall (R: Type*), ([\operatorname{AddCommGroup}\left(R\right)] [\operatorname{Module}\left(kappa, R\right)] [\operatorname{FiniteDimensional}\left(kappa, R\right)] \forall (K: Type*), ([\operatorname{AddCommGroup}\left(K\right)] [\operatorname{Module}\left(kappa, K\right)] [\operatorname{FiniteDimensional}\left(kappa, K\right)] \forall (G: Type*), ([\operatorname{AddCommGroup}\left(G\right)] [\operatorname{Module}\left(kappa, G\right)] [\operatorname{FiniteDimensional}\left(kappa, G\right)] \forall (T: \operatorname{LinearMap}\left(kappa, (R) \times (K), G\right)), (\forall (p: \operatorname{LinearMap}\left(kappa, G, R\right)), ((\operatorname{comp}\left(p, T\right) = \operatorname{fst}\left(kappa, R, K\right)) \to ((\operatorname{finrank}\left(kappa, \operatorname{range}\left(T\right)\right) \le \operatorname{finrank}\left(kappa, R\right)) \to (\forall (z: K), (\operatorname{T}\left((0, z)\right) = 0)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/C1LocalFiber.linear_vertical_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a linear map T from R times K to G over a division ring, suppose an observed linear projection p satisfies p composed with T equals the first coordinate. If the range dimension of T is at most the dimension of R, every vector (0,z) is killed by T. Restrict p to the actual range of T: it is surjective, the dimension bound makes it injective, and its kernel therefore vanishes. The argument adapts BochaoKong's Apache-2.0 LeanPool complex constant-rank linear algebra, commit 2b1ec889365345f19a45fa94b6457a4d92c96295. It is consumed by the real fiber construction and by finite matrix completion.

**Theorem 1.2 (An actual C1 ball in a level set).**

$$\forall (E: Type*), ([\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] \forall (F: Type*), ([\operatorname{NormedAddCommGroup}\left(F\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, F\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, F\right)] \forall (U: \operatorname{Set}\left(E\right)), (\forall (f: E \to F), ((\operatorname{IsOpen}\left(U\right)) \to ((\operatorname{ContDiffOn}\left(\mathbb{R}, 1, f, U\right)) \to (\forall (a: E), ((a \in U) \to ((\forall (x: E), ((x \in U) \to (\operatorname{finrank}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{fderiv}\left(\mathbb{R}, f, x\right)\right)\right) \le \operatorname{finrank}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{fderiv}\left(\mathbb{R}, f, a\right)\right)\right)))) \to (\exists (K: \operatorname{Submodule}\left(\mathbb{R}, E\right)), (\exists (q: \operatorname{ContinuousLinearMap}\left(\mathbb{R}, E, K\right)), (\exists (k: K \to E), (\exists (epsilon: \mathbb{R}), (((((0 < epsilon) \land (\operatorname{finrank}\left(\mathbb{R}, K\right) + \operatorname{finrank}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{fderiv}\left(\mathbb{R}, f, a\right)\right)\right) = \operatorname{finrank}\left(\mathbb{R}, E\right))) \land (\operatorname{k}\left(0\right) = a)) \land (\operatorname{ContDiffOn}\left(\mathbb{R}, 1, k, \operatorname{ball}\left(0, epsilon\right)\right))) \land (\forall (z: K), ((z \in \operatorname{ball}\left(0, epsilon\right)) \to (((\operatorname{k}\left(z\right) \in U) \land (\operatorname{f}\left(\operatorname{k}\left(z\right)\right) = \operatorname{f}\left(a\right))) \land (\operatorname{q}\left(\operatorname{k}\left(z\right) - a\right) = z)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/C1LocalFiber.exists_local_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be real C1 on an open set U and a belong to U. Assume the derivative rank at a bounds the derivative rank at every point of U. The theorem constructs a subspace K, a continuous linear map q, a map k and a positive radius. The dimension of K plus the derivative rank at a equals the source dimension. On the K-ball, k is C1, k(0)=a, k(z) belongs to U, f(k(z))=f(a), and q(k(z)-a)=z. Thus distinct ball parameters give distinct actual source points, including when the maximal rank is zero. Complementary range and kernel projections make the derivative of the centered coordinate map invertible. A local inverse supplies the coordinates. The rank criterion kills all vertical derivatives; the convex-ball zero-derivative theorem supplies equality of values. Neither a derivative kernel alone nor a formal tangent direction is presented as a fiber.

**Theorem 1.3 (Collision in every nonempty open domain).**

$$\forall (E: Type*), ([\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] \forall (F: Type*), ([\operatorname{NormedAddCommGroup}\left(F\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, F\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, F\right)] \forall (U: \operatorname{Set}\left(E\right)), (\forall (f: E \to F), ((\operatorname{IsOpen}\left(U\right)) \to ((\operatorname{ContDiffOn}\left(\mathbb{R}, 1, f, U\right)) \to ((\operatorname{Nonempty}\left(U\right)) \to ((\operatorname{finrank}\left(\mathbb{R}, F\right) < \operatorname{finrank}\left(\mathbb{R}, E\right)) \to (\exists (x: E), ((x \in U) \land (\exists (y: E), (((y \in U) \land (\neg x = y)) \land (\operatorname{f}\left(x\right) = \operatorname{f}\left(y\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/C1LocalFiber.exists_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real C1 map from a finite-dimensional normed space to a strictly smaller one has two distinct source points in any specified nonempty open domain with identical output. The bounded integer-valued derivative rank attains a maximum on that domain. The constructed local fiber then has positive dimension, and a nonzero vector in its ball produces the collision. No compactness of the domain and no density of the global maximum-rank set are assumed.

**Theorem 1.4 (Open-domain noninjectivity).**

$$\forall (E: Type*), ([\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] \forall (F: Type*), ([\operatorname{NormedAddCommGroup}\left(F\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, F\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, F\right)] \forall (U: \operatorname{Set}\left(E\right)), (\forall (f: E \to F), ((\operatorname{IsOpen}\left(U\right)) \to ((\operatorname{ContDiffOn}\left(\mathbb{R}, 1, f, U\right)) \to ((\operatorname{Nonempty}\left(U\right)) \to ((\operatorname{finrank}\left(\mathbb{R}, F\right) < \operatorname{finrank}\left(\mathbb{R}, E\right)) \to (\neg \operatorname{InjOn}\left(f, U\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/C1LocalFiber.not_injOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual collision immediately excludes injectivity on the nonempty open domain. This is an analysis supplier for the twelve-real-coordinate MPS record. By itself it neither proves two-site density minimality nor supplies a nonempty phase-identifiable MPS chart.

## References

- Truth anchor: `D5/S3/Geometry/C1LocalFiber.exists_collision`
- Truth anchor: `D5/S3/Geometry/C1LocalFiber.exists_local_fiber`
- Truth anchor: `D5/S3/Geometry/C1LocalFiber.linear_vertical_eq_zero`
- Truth anchor: `D5/S3/Geometry/C1LocalFiber.not_injOn`
