# Noninjectivity on complete finite boards

## Abstract

A collision in the deterministic RiskCA at the highest active threshold.

Use the complete simple graph on V. The carrier S(V,P,M) is the full product over V of P available owner labels and the unit counts 1 through M. Equality is pointwise. The map Φ(π,b,ρ,X) applies the deterministic local step of §3.2 and Appendix B Algorithm 1 to X with priority permutation π, fortification flag b, battle ratio ρ, growth zero and threshold M − 1.

**Theorem 1.1 (Two configurations map to the same fixed image).**

$$\begin{aligned}\forall V: Type, [\operatorname{Fintype}\left(V\right)], \forall P,M: \mathbb{N}, \forall \pi: \operatorname{Perm}\left(V\right), \forall b: Bool, \forall \rho: \mathbb{R}, \\(2 \leq \operatorname{card}\left(V\right) \land 2 \leq P \land 3 \leq M \land 1 \leq\rho) \longrightarrow\\\exists X,Y: S\left(V, P, M\right), X \neq Y \land \phi\left(\pi, b, \rho, X\right)=Y \land \phi\left(\pi, b, \rho, Y\right)=Y\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.paper_collision_fixed_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* María Teresa Arias Noguerales (2026). *Territorial Conflict as a Cellular Automaton: Frozen Domains and Active Fronts in a Risk-Derived Local Rule*. DOI: [10.48550/arXiv.2611.34784](https://doi.org/10.48550/arXiv.2611.34784). URL: <https://arxiv.org/abs/2611.34784v1>.

*Commentary.*

Choose distinct vertices u and v. Put M units at u and one unit everywhere else. Assign one owner to v and a different owner everywhere else. The unique request is from u to v. Its committed force is M − 1 and the defending cell has one unit. For ρ ≥ 1 the attack wins and the ceiling of 1/ρ is one, leaving M − 2 units at v.

The output Y has one owner and one unit everywhere except at v. Its threats vanish and the zero-growth step fixes it. At u the two inputs have M units and one unit, respectively.

**Theorem 1.2 (Noninjectivity in the paper's ratio band).**

$$\begin{aligned}\forall V: Type, [\operatorname{Fintype}\left(V\right)], \forall P,M: \mathbb{N}, \forall \pi: \operatorname{Perm}\left(V\right), \forall b: Bool, \forall \rho: \mathbb{R}, \\(2 \leq \operatorname{card}\left(V\right) \land 2 \leq P \land 3 \leq M \land 1<\rho<2) \longrightarrow\\\exists X,Y: S\left(V, P, M\right), X \neq Y \land \phi\left(\pi, b, \rho, X\right)=\phi\left(\pi, b, \rho, Y\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.paper_noninjective` (`✓ std3`). ∎

*Resolves.* `Problems/arias-noguerales-2026-riskca-complete-board-endpoint` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.paper_noninjective`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"arias-noguerales-2026-riskca-complete-board-endpoint","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.paper_noninjective","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* María Teresa Arias Noguerales (2026). *Territorial Conflict as a Cellular Automaton: Frozen Domains and Active Fronts in a Risk-Derived Local Rule*. DOI: [10.48550/arXiv.2611.34784](https://doi.org/10.48550/arXiv.2611.34784). URL: <https://arxiv.org/abs/2611.34784v1>.

*Commentary.*

For 1 < ρ < 2 the fixed-image collision gives two distinct configurations with equal images. This settles the complete-board branch registered for Proposition 2. The branch for connected incomplete boards with fortification disabled remains open in this formalization.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.paper_collision_fixed_image`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.paper_noninjective`
