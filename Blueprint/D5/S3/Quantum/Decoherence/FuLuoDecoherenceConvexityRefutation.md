# Fu-Luo decoherence convexity is refuted

## Abstract

An explicit four-dimensional system with four qubit sub-environments violates the conjectured convexity of the Fu-Luo decoherence quantifier.

S. Fu and S. Luo, Quantifying Decoherence via Increases in Classicality, Entropy 23(12) (2021), 1594, Section 3. The source states verbatim: "We conjecture that D(ρ_S|Π, U) is convex in ρ. It seems that a proof may require some deep mathematics." Equation (17) states "J(ρ,Π) = 1 + tr(√ρ Π†(√ρ)) = 1 + Σ_i 〈i|√ρ|i〉²." Equations (21)–(22) state "ρ′_S = tr_E ρ′_SE = Σ_{i,j=1}^d tr(U_{Ei} ρ_E U_{Ej}†) · Π_i ρ_S Π_j", with "ρ_S ∘ Ω", and Equation (27) states "D(ρ_S|Π, U) = J(ρ′_S, Π) − J(ρ_S, Π)".

**Definition 1.1 (The classicality functional J).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{J}\left(rho\right) = 1 + \sum_{i: \operatorname{Fin}\left(d\right)} \operatorname{Complex}.\operatorname{re}\left((\operatorname{CFC}.\operatorname{sqrt}\left(rho\right)\left(i, i\right))^{2}\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.J` (`✓ std3`).

*Citation.* S. Fu and S. Luo (2021). *Quantifying Decoherence via Increases in Classicality*. DOI: [10.3390/e23121594](https://doi.org/10.3390/e23121594). URL: <https://www.mdpi.com/1099-4300/23/12/1594>.

*Commentary.*

Equation (17) states verbatim: "J(ρ,Π) = 1 + tr(√ρ Π†(√ρ)) = 1 + Σ_i 〈i|√ρ|i〉²." The encoding uses the standard basis of Fin d and takes the real part of each diagonal square.

**Definition 1.2 (Environment basis labels).**

$$\forall d \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \operatorname{EnvIdx}\left(k\right) = ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{Fin}\left(k\left(l\right)\right))$$

*Formalization.* `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.EnvIdx` (`✓ std3`).

*Citation.* S. Fu and S. Luo (2021). *Quantifying Decoherence via Increases in Classicality*. DOI: [10.3390/e23121594](https://doi.org/10.3390/e23121594). URL: <https://www.mdpi.com/1099-4300/23/12/1594>.

*Commentary.*

An environment basis label assigns to each part l a basis element of Fin (k l).

**Definition 1.3 (A local environment operator).**

$$\forall d \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall i \in \operatorname{Fin}\left(d\right),\; \forall Ui \in \operatorname{Matrix}\left(\operatorname{Fin}\left(k\left(i\right)\right), \operatorname{Fin}\left(k\left(i\right)\right), \mathbb{C}\right),\; \operatorname{liftE}\left(i, Ui\right) = \lambda x: \operatorname{EnvIdx}\left(k\right), \lambda y: \operatorname{EnvIdx}\left(k\right), \operatorname{ite}\left((\forall l \in \operatorname{Fin}\left(d\right),\; (l \ne i) \Rightarrow (x\left(l\right) = y\left(l\right))), Ui\left(x\left(i\right)\right)\left(y\left(i\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.liftE` (`✓ std3`).

*Citation.* S. Fu and S. Luo (2021). *Quantifying Decoherence via Increases in Classicality*. DOI: [10.3390/e23121594](https://doi.org/10.3390/e23121594). URL: <https://www.mdpi.com/1099-4300/23/12/1594>.

*Commentary.*

The source describes U_{Ei} acting only on H_{Ei}. The encoding applies Ui at coordinate i and enforces equality at every other environment coordinate.

**Definition 1.4 (The product environment state).**

$$\forall d \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall tau \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{DensityState}\left(\operatorname{Fin}\left(k\left(l\right)\right)\right)),\; \operatorname{rhoE}\left(tau\right) = \lambda x: \operatorname{EnvIdx}\left(k\right), \lambda y: \operatorname{EnvIdx}\left(k\right), \prod_{l: \operatorname{Fin}\left(d\right)} \operatorname{Subtype}.\operatorname{val}\left(tau\left(l\right)\right)\left(x\left(l\right)\right)\left(y\left(l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.rhoE` (`✓ std3`).

*Citation.* S. Fu and S. Luo (2021). *Quantifying Decoherence via Increases in Classicality*. DOI: [10.3390/e23121594](https://doi.org/10.3390/e23121594). URL: <https://www.mdpi.com/1099-4300/23/12/1594>.

*Commentary.*

The source describes the initial state as ρ_SE = ρ_S ⊗ ρ_E with ρ_E = ρ_{E1} ⊗ ρ_{E2} ⊗ ⋯ ⊗ ρ_{Ed}. The encoding multiplies the corresponding entries of the component density states.

**Definition 1.5 (The environment overlap matrix).**

$$\forall d \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall tau \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{DensityState}\left(\operatorname{Fin}\left(k\left(l\right)\right)\right)),\; \forall U \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(k\left(l\right)\right), \mathbb{C}\right)),\; \forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; \operatorname{omega}\left(tau, U, i, j\right) = \operatorname{Matrix}.\operatorname{trace}\left(((\operatorname{liftE}\left(i, \operatorname{val}\left(U\left(i\right)\right)\right)) \cdot (\operatorname{rhoE}\left(tau\right))) \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{liftE}\left(j, \operatorname{val}\left(U\left(j\right)\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.omega` (`✓ std3`).

*Citation.* S. Fu and S. Luo (2021). *Quantifying Decoherence via Increases in Classicality*. DOI: [10.3390/e23121594](https://doi.org/10.3390/e23121594). URL: <https://www.mdpi.com/1099-4300/23/12/1594>.

*Commentary.*

Equation (21) states verbatim: "ρ′_S = tr_E ρ′_SE = Σ_{i,j=1}^d tr(U_{Ei} ρ_E U_{Ej}†) · Π_i ρ_S Π_j". The overlap is the displayed trace factor.

**Definition 1.6 (The final system state).**

$$\forall d \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall tau \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{DensityState}\left(\operatorname{Fin}\left(k\left(l\right)\right)\right)),\; \forall U \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(k\left(l\right)\right), \mathbb{C}\right)),\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{finalState}\left(tau, U, rho\right) = \lambda a: \operatorname{Fin}\left(d\right), \lambda b: \operatorname{Fin}\left(d\right), (rho\left(a, b\right)) \cdot (\operatorname{omega}\left(tau, U, a, b\right))$$

*Formalization.* `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.finalState` (`✓ std3`).

*Citation.* S. Fu and S. Luo (2021). *Quantifying Decoherence via Increases in Classicality*. DOI: [10.3390/e23121594](https://doi.org/10.3390/e23121594). URL: <https://www.mdpi.com/1099-4300/23/12/1594>.

*Commentary.*

Equation (22) states verbatim that the reduced state is "ρ_S ∘ Ω", where ∘ is the Hadamard product and Ω = (ω_ij). The encoding multiplies each entry by omega.

**Definition 1.7 (The decoherence quantifier D).**

$$\forall d \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall tau \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{DensityState}\left(\operatorname{Fin}\left(k\left(l\right)\right)\right)),\; \forall U \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(k\left(l\right)\right), \mathbb{C}\right)),\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{D}\left(tau, U, rho\right) = \operatorname{J}\left(\operatorname{finalState}\left(tau, U, rho\right)\right) - \operatorname{J}\left(rho\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.D` (`✓ std3`).

*Citation.* S. Fu and S. Luo (2021). *Quantifying Decoherence via Increases in Classicality*. DOI: [10.3390/e23121594](https://doi.org/10.3390/e23121594). URL: <https://www.mdpi.com/1099-4300/23/12/1594>.

*Commentary.*

Equation (27) states verbatim: "D(ρ_S|Π, U) = J(ρ′_S, Π) − J(ρ_S, Π)". The encoding subtracts the initial classicality from the final classicality.

**Definition 1.8 (The conjectured convexity statement).**

$$(\operatorname{claim}) \Leftrightarrow (\forall d \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall tau \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{DensityState}\left(\operatorname{Fin}\left(k\left(l\right)\right)\right)),\; \forall U \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(k\left(l\right)\right), \mathbb{C}\right)),\; \forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \forall sigma \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \forall t \in \mathbb{R},\; (0 \le t) \Rightarrow ((t \le 1) \Rightarrow (\operatorname{D}\left(tau, U, \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left((t) \cdot (\operatorname{Subtype}.\operatorname{val}\left(rho\right)) + (1 - t) \cdot (\operatorname{Subtype}.\operatorname{val}\left(sigma\right))\right)\right) \le (t) \cdot (\operatorname{D}\left(tau, U, \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(rho\right)\right)\right)) + (1 - t) \cdot (\operatorname{D}\left(tau, U, \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(sigma\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.claim` (`✓ std3`).

*Citation.* S. Fu and S. Luo (2021). *Quantifying Decoherence via Increases in Classicality*. DOI: [10.3390/e23121594](https://doi.org/10.3390/e23121594). URL: <https://www.mdpi.com/1099-4300/23/12/1594>.

*Commentary.*

The source states verbatim after Proposition 3: "We conjecture that D(rho_S|Pi, U) is convex in rho. It seems that a proof may require some deep mathematics." The formal statement expands convexity as the Jensen inequality for every dimension, product environment, family of local unitaries, pair of density states, and t in [0,1].

**Theorem 1.9 (An explicit violation in dimension four).**

$$\neg (\forall d \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(d\right) \to \mathbb{N},\; \forall tau \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{DensityState}\left(\operatorname{Fin}\left(k\left(l\right)\right)\right)),\; \forall U \in ((l: \operatorname{Fin}\left(d\right)) \to \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(k\left(l\right)\right), \mathbb{C}\right)),\; \forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \forall sigma \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \forall t \in \mathbb{R},\; (0 \le t) \Rightarrow ((t \le 1) \Rightarrow (\operatorname{D}\left(tau, U, \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left((t) \cdot (\operatorname{Subtype}.\operatorname{val}\left(rho\right)) + (1 - t) \cdot (\operatorname{Subtype}.\operatorname{val}\left(sigma\right))\right)\right) \le (t) \cdot (\operatorname{D}\left(tau, U, \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(rho\right)\right)\right)) + (1 - t) \cdot (\operatorname{D}\left(tau, U, \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\operatorname{Subtype}.\operatorname{val}\left(sigma\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Fu and S. Luo (2021). *Quantifying Decoherence via Increases in Classicality*. DOI: [10.3390/e23121594](https://doi.org/10.3390/e23121594). URL: <https://www.mdpi.com/1099-4300/23/12/1594>.

*Commentary.*

For four system coordinates, four qubit environments in the state |0><0|, and detector unitaries (X, X, Z, Z), the two explicit density states have D equal to 5/16 while their midpoint has D equal to 3/8. Thus the Jensen inequality in the expanded claim is false.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.D`
- Truth anchor: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.EnvIdx`
- Truth anchor: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.J`
- Truth anchor: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.finalState`
- Truth anchor: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.liftE`
- Truth anchor: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.omega`
- Truth anchor: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.rhoE`
- Dependency: [D5/S3/Quantum/Reduction/ProbeComponentRigidity](../Reduction/ProbeComponentRigidity.md)
