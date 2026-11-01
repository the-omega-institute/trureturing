# Complete well-covered-power classification of cubic circulants

## Abstract

All admissible parameters, all positive faithful powers, five native graph types and exact component multipliers.

Throughout, n is even and at least four, and 1 at most a is less than n/2. Let G=cubic(n,a), h=gcd(n,a), ell=n/h and g=gcd(a,n/2). The allowed set is exactly {3,4,5,6,8}. AllPowers(G) means that every faithful finite-distance power with positive exponent is well-covered. The component size function s(ell,d) has first values: ell=4 gives 1; ell=6 or 8 gives 3,1; ell=3 gives 2,1; ell=5 gives 4,2,1. Every later value is one. The five named types are K4=C4(1,2), K3,3=C6(1,3), P3=C6(2,3), M8=C8(1,4), and P5=C10(2,5). Their diameters are 1,2,2,2,3. The first-power classification is attributed to Brown and Hoshino, Well-covered circulant graphs, DOI 10.1016/j.disc.2010.11.007; the component decomposition is further attributed to Davis, Domke and Garner. Fresh verification recovered Brown-Hoshino metadata but not the full primary mathematical text, so the precise historical theorem-text attribution remains ASSUMED-UNVERIFIED. No novelty claim is made for that classification.

**Theorem 1.1 (Every positive power exactly when the first is well-covered).**

$$\left(\operatorname{AllPowers}\left(G\right) \Leftrightarrow \operatorname{WellCovered}\left(G\right)\right) \land \left(\operatorname{WellCovered}\left(G\right) \Leftrightarrow \operatorname{mem}\left(ell, \mathrm{fiveOrders}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.all_powers_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native first-power spectra classify all Mobius and prism components. Their exact attained values show that only ell in the stated set can be well-covered. Conversely, all their powers have singleton spectra: diameter bounds make later powers complete, and the pentagonal square is handled by its actual complement ten-cycle. The faithful component transport proves the equivalence for the entire disconnected graph.

**Theorem 1.2 (Exact uniform sizes and attainability in every component multiplicity).**

$$\operatorname{mem}\left(ell, \mathrm{fiveOrders}\right) \Rightarrow \left(\forall d \in \mathrm{Nat},\; 1 \le d \Rightarrow \operatorname{spectrum}\left(\operatorname{graphPower}\left(G, d\right)\right) = \operatorname{singleton}\left(\operatorname{mul}\left(g, \operatorname{componentPowerSize}\left(ell, d\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.cubic_power_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual component has the singleton spectrum s(ell,d). The full componentwise Minkowski formula gives exactly g times that value, including an actual maximal independent Finset attaining the sum. This is a consequence of native component isomorphisms and finite-path powers, rather than a scalar decomposition assumption.

**Theorem 1.3 (The native five-type table).**

$$\forall t \in \mathrm{ConnectedType},\; \operatorname{GraphIso}\left(\operatorname{cubic}\left(\operatorname{typeOrder}\left(t\right), \operatorname{typeStep}\left(t\right)\right), \operatorname{typeGraph}\left(t\right)\right) \land \left(\operatorname{Connected}\left(\operatorname{cubic}\left(\operatorname{typeOrder}\left(t\right), \operatorname{typeStep}\left(t\right)\right)\right) \land \left(\operatorname{diam}\left(\operatorname{cubic}\left(\operatorname{typeOrder}\left(t\right), \operatorname{typeStep}\left(t\right)\right)\right) = \operatorname{typeDiameter}\left(t\right) \land \left(\forall d \in \mathrm{Nat},\; 1 \le d \Rightarrow \operatorname{spectrum}\left(\operatorname{graphPower}\left(\operatorname{cubic}\left(\operatorname{typeOrder}\left(t\right), \operatorname{typeStep}\left(t\right)\right), d\right)\right) = \operatorname{singleton}\left(\operatorname{typePowerSize}\left(t, d\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.native_type_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index t ranges over exactly the five types listed above. The graph side of the correspondence is literal: the complete graph, complete bipartite graph, two Cartesian prisms and the native eight-vertex Mobius graph. Parity coordinates identify the six-vertex Mobius graph with K3,3. The odd-order component construction identifies each listed prism circulant. All exponent statements quantify over every positive natural number.

**Theorem 1.4 (Every actual component belongs to the native table).**

$$\operatorname{mem}\left(ell, \mathrm{fiveOrders}\right) \Rightarrow \left(\forall C \in \operatorname{Components}\left(G\right),\; \exists t \in \mathrm{ConnectedType},\; ell = \operatorname{NatDiv}\left(\operatorname{typeOrder}\left(t\right), \operatorname{gcd}\left(\operatorname{typeOrder}\left(t\right), \operatorname{typeStep}\left(t\right)\right)\right) \land \operatorname{GraphIso}\left(\operatorname{componentGraph}\left(C\right), \operatorname{typeGraph}\left(t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.classified_component_type` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-parameter component decomposition selects the even Mobius or odd prism case. The attained first-power spectrum restricts it to the appropriate entry of the five-type table. The theorem supplies a graph isomorphism on each actual component support and also identifies its normalized cycle order.

**Theorem 1.5 (Exactly one selected vertex per original component).**

$$\operatorname{mem}\left(ell, \mathrm{fiveOrders}\right) \Rightarrow \left(\forall d \in \mathrm{Nat},\; 3 \le d \Rightarrow \operatorname{spectrum}\left(\operatorname{graphPower}\left(G, d\right)\right) = \operatorname{singleton}\left(g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.eventual_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

By exponent three all five connected models are complete. Each maximal independent set therefore has exactly one vertex from each original component. Positive faithful powers preserve those components, so the exact eventual cardinality is g, with attainment.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.all_powers_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.classified_component_type`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.cubic_power_spectrum`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.eventual_spectrum`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification.native_type_table`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CubicCirculant](CubicCirculant.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MobiusMetric](MobiusMetric.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PentagonalPrismSquare](PentagonalPrismSquare.md)
