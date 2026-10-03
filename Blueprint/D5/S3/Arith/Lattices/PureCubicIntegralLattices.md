# Integral Lattices in a Pure Cubic Field

## Abstract

Two integral rational bases in a pure cubic field have explicit lattice discriminants.

**Theorem 1.1 (Two integral rational bases and their trace discriminants).**

$$\begin{aligned}\operatorname{Field}\left(K\right) \land \operatorname{Algebra}\left(\mathbb{Q}, K\right) \land m,n,c,a,k,v \in \mathbb{Z} \land \operatorname{PowerBasis}\left(\mathbb{Q}, K, 1, \alpha, \alpha^{2}\right) \land\\\operatorname{dim}\left(\mathbb{Q}, K\right) = 3 \land m \neq 0 \land n \neq 0 \land v^{2} = 1 \land\\\alpha^{3} = m \cdot n^{2} \land c^{3} \cdot m \cdot n^{2} = 1+9a \land c^{2} \cdot n = v+3k \Rightarrow\\\beta = \frac{\alpha^{2}}{n}, \gamma = \frac{1+c \cdot \alpha+v \cdot \beta}{3},\\\operatorname{IsIntegral}\left(\mathbb{Z}, \alpha\right) \land \operatorname{IsIntegral}\left(\mathbb{Z}, \beta\right) \land \operatorname{IsIntegral}\left(\mathbb{Z}, \gamma\right),\\\operatorname{Basis}\left(\mathbb{Q}, 1, \alpha, \beta\right) \land \operatorname{Basis}\left(\mathbb{Q}, 1, \alpha, \gamma\right),\\\operatorname{discr}\left(\mathbb{Q}, 1, \alpha, \beta\right) = -27{m \cdot n}^{2},\\\operatorname{discr}\left(\mathbb{Q}, 1, \alpha, \gamma\right) = -3{m \cdot n}^{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/PureCubicIntegralLattices.integral_cubic_lattices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a characteristic-zero field with a rational power basis (1, alpha, alpha squared) of dimension three. Assume alpha cubed equals m times n squared, where m and n are nonzero integers. Let c, a, k, and v be integers with v equal to one or minus one, c cubed times m times n squared equal to one plus nine a, and c squared times n equal to v plus three k. Define beta and gamma as displayed.

The cubic equations for alpha and beta make them integral. For t=c alpha, the element (1+t+t squared)/3 satisfies the monic polynomial T cubed minus T squared minus 3aT minus 3a squared. It is integral, and gamma differs from it by the integral multiple k beta.

The rational power basis has discriminant minus 27 times (m n squared) squared. The two displayed changes of basis have determinants 1/n and v/(3n). Their nonzero discriminants also establish that both triples are rational bases. These are discriminants of the specified integral lattices. The rational power basis is assumed here; the theorem does not construct it from irreducibility, identify the field discriminant, or prove maximality.

## References

- Truth anchor: `D5/S3/Arith/Lattices/PureCubicIntegralLattices.integral_cubic_lattices`
