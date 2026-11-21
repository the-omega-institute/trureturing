# Displacements of uniform couplings on group fibers

## Abstract

Every law on a group homomorphism fiber arises as the displacement of a uniform coupling.

**Theorem 1.1 (Exact displacement laws for a uniform fiber coupling).**

$$\begin{aligned}\forall G, H: \operatorname{Group}, \forall \phi: \operatorname{Hom}\left(G, H\right), \forall t \in H, \\|K| < \infty \implies \forall \rho: T \to \mathbb{R},\\(\forall d \in T, 0 \leq \rho\left(d\right)) \land \sum_{d \in T} \rho\left(d\right) = 1\\\iff \exists w: K \times T \to \mathbb{R}, (\forall x \in K, \forall y \in T, 0 \leq w\left(x, y\right))\\\land (\forall x \in K, \sum_{y \in T} w\left(x, y\right) = \frac{1}{|K|})\\\land (\forall y \in T, \sum_{x \in K} w\left(x, y\right) = \frac{1}{|T|})\\\land (\forall d \in T, \sum_{x \in K, y \in T, x^{-1}y = d} w\left(x, y\right) = \rho\left(d\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformFiberCoupling.displacement_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G and H be groups, and take a homomorphism from G to H and an element t of H. Assume its kernel K is finite. Write T for the fiber over t. If T is empty, neither assertion can hold. There is no probability law on T, and the row at the identity cannot have its prescribed positive mass.

To construct the coupling, give a pair the weight of its displacement divided by the size of K. With the first entry fixed, left translation permutes T. With the second entry fixed, varying the first entry gives a bijection from K to T. These two bijections give the marginals. The first bijection also gives one occurrence of each prescribed displacement in every row. In reverse, the displacement weights are sums of nonnegative entries. Their sum gives the total mass of the coupling.

## References

- Truth anchor: `D5/S3/Analytic/Probability/UniformFiberCoupling.displacement_iff`
