# Forced Fixed-Price Inventory

## Abstract

The LCM with the strict inventory is the least fixed-price optimizer among positive base multiples.

**Theorem 1.1 (A least optimizer that retains the forced floor).**

Lean statement: `D5/S3/Arith/GoldenResource/ForcedInventoryLeastMaximum.forced_inventory_least_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ForcedInventoryLeastMaximum.forced_inventory_least_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let lambda be any positive real price and let m and C be positive natural integers. Suppose C.factorization(q) equals optimalLayerCount(lambda,q) for every natural q. Then lcm(m,C) maximizes goldenResourceObjective(lambda,n) among all positive multiples n of m, and divides every maximizer in that same domain. Its positivity makes divisibility imply integer leastness. The price is fixed and is not assumed to be a clock derived from n.

Existing arbitrary-base attainment supplies a maximum. Choose the least maximizing integer T. Inserting one prime is always legal in the full multiples domain, so all strictly active layers occur in every maximum. If T has an exponent above the forced m floor, deleting its top layer gives a smaller legal integer. An equal objective value would make that integer another maximum, contradicting leastness. The public single-layer identity and active-count interval therefore identify T's exponent as the maximum of the forced exponent and the strict active count. Factorization of the LCM identifies the actual integer T.

Forced inactive or equal-price layers remain present. Removable equal-price layers are absent only from the least optimizer; other optimizers may contain ties. The theorem assumes no activity of the forced bottom layers and no upper divisor bound. At m=5040*P it protects the complete forced factor, but does not supply nonlinear leastness, complete near-price mass, backward curvature, a signed prime estimate, Robin's inequality or RH.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ForcedInventoryLeastMaximum.forced_inventory_least_maximum`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison](GoldenResource5040EndpointComparison.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount](GoldenResourceOptimalLayerCount.md)
