# The proposed noncommuting Tsallis bound order fails

## Abstract

A noncommuting positive definite qubit pair reverses the proposed Tsallis bound order.

**Definition 1.1 (The deformed logarithm).**

$$\forall (r: \mathbb{R}), \forall (x: \mathbb{R}), \operatorname{lnr}\left(r, x\right) = (\frac{(x^{r}) - (1)}{r})$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.lnr` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Definition 1, printed p. 2: “The r-logarithm is denoted by ln_r(x) and it is defined by ln_r(x) = (x^r − 1)/r, for r ≠ 0 and x ≥ 0.” The real power is Real.rpow.

**Definition 1.2 (The deformed Rényi relative entropy).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (alpha: \mathbb{R}), \forall (r: \mathbb{R}), \forall (z: \mathbb{R}), \operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right) = ((\frac{1}{(alpha) - (1)}) \cdot (\operatorname{lnr}\left(r, (\operatorname{Matrix}.\operatorname{trace} (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{z}), ((\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{\frac{(1) - (alpha)}{(2) \cdot (z)}}), sigma\right)) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{\frac{alpha}{z}}), rho\right))) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{\frac{(1) - (alpha)}{(2) \cdot (z)}}), sigma\right))\right))).\operatorname{re}\right)))$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.renyiRZ` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Definition 2, printed p. 2: “The r-deformed α-z-Rényi relative entropy for any two positive semi-definite operators ρ and σ with Supp(ρ) ⊆ Supp(σ) is defined by D^{(r)}_{α,z}(ρ||σ) = (1/(α−1)) ln_r Tr[(σ^{(1−α)/(2z)} ρ^{α/z} σ^{(1−α)/(2z)})^z] … where α, r ∈ R and z ∈ R+.” The source calls this quantity B₁. Here n is the dimension, rho and sigma are complex matrices, alpha denotes α, cfc evaluates each real function of a Hermitian matrix, and re takes the real part of its trace.

**Definition 1.3 (The Tsallis relative entropy).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (alpha: \mathbb{R}), \operatorname{tsallis}\left(alpha, rho, sigma\right) = (\frac{(\operatorname{Matrix}.\operatorname{trace} ((rho) - ((\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{alpha}), rho\right)) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{(1) - (alpha)}), sigma\right))))).\operatorname{re}}{(1) - (alpha)})$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.tsallis` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Equation (6), printed p. 2, gives D_α(ρ||σ) = Tr[ρ − ρ^α σ^{1−α}]/(1 − α). The displayed expression uses cfc for the two matrix powers and the real part of the trace.

**Definition 1.4 (The second upper bound).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (alpha: \mathbb{R}), \forall (q: \mathbb{R}), \operatorname{B2}\left(alpha, q, rho, sigma\right) = (- ((\operatorname{Matrix}.\operatorname{trace} ((rho) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto \operatorname{lnr}\left((1) - (alpha), x\right)), \operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{\frac{1}{q}}), ((\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{- (\frac{q}{2})}), rho\right)) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{q}), sigma\right))) \cdot (\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x^{- (\frac{q}{2})}), rho\right))\right)\right)))).\operatorname{re}))$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B2` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Equations (8) and (47), printed pp. 2 and 11, give B₂(ρ||σ) = −Tr[ρ ln_{1−α}((ρ^{−q/2} σ^q ρ^{−q/2})^{1/q})]. Each real matrix function is evaluated by cfc, with the negative sign outside the real trace.

**Definition 1.5 (The source's proposed ordering).**

$$claim \Leftrightarrow (\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((rho).\operatorname{PosDef}) \Rightarrow (((rho).\operatorname{trace} = (1)) \Rightarrow (((sigma).\operatorname{PosDef}) \Rightarrow (((sigma).\operatorname{trace} = (1)) \Rightarrow (((rho) \cdot (sigma) \ne (sigma) \cdot (rho)) \Rightarrow (\forall (alpha: \mathbb{R}), \forall (r: \mathbb{R}), \forall (z: \mathbb{R}), \forall (q: \mathbb{R}), (0 \le alpha) \Rightarrow ((alpha < 1) \Rightarrow ((r \ne 0) \Rightarrow ((0 < z) \Rightarrow (((1) - (alpha) < q) \Rightarrow ((\operatorname{tsallis}\left(alpha, rho, sigma\right) \le \operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right)) \land (\operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right) \le \operatorname{B2}\left(alpha, q, rho, sigma\right)))))))))))))$$

*Formalization.* `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.claim` (`✓ std3`).

*Citation.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Equations (8)–(9), printed p. 2: “For 0 ≤ α < 1 and q > (1 − α), we compare two upper bounds B₁(ρ||σ) = D^{(r)}_{α,z}(ρ||σ) and B₂(ρ||σ) = −Tr[ρ ln_{1−α}((ρ^{−q/2} σ^q ρ^{−q/2})^{1/q})] of the Tsallis relative entropy, numerically. We observe that for non-commutative density operators ρ and σ, D_α(ρ||σ) ≤ B₁(ρ||σ) ≤ B₂(ρ||σ).” Section 4, Case 5, printed p. 12: “Let Tr(ρ) = 1 and Tr(σ) = 1, that is both ρ and σ are density operators. Here, we numerically observe that for any two operators ρ and σ, B₁(ρ||σ) is a tighter bound of Tsallis relative entropy than B₂(ρ||σ).” The formula ranges over every finite dimension. Positive definite matrices with unit trace satisfy the support condition and admit negative powers. The parameters r≠0 and z>0 come from Definitions 1–2. The function renyiRZ is precisely the source's B₁.

**Theorem 1.6 (A noncommuting qubit counterexample).**

$$\neg (\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((rho).\operatorname{PosDef}) \Rightarrow (((rho).\operatorname{trace} = (1)) \Rightarrow (((sigma).\operatorname{PosDef}) \Rightarrow (((sigma).\operatorname{trace} = (1)) \Rightarrow (((rho) \cdot (sigma) \ne (sigma) \cdot (rho)) \Rightarrow (\forall (alpha: \mathbb{R}), \forall (r: \mathbb{R}), \forall (z: \mathbb{R}), \forall (q: \mathbb{R}), (0 \le alpha) \Rightarrow ((alpha < 1) \Rightarrow ((r \ne 0) \Rightarrow ((0 < z) \Rightarrow (((1) - (alpha) < q) \Rightarrow ((\operatorname{tsallis}\left(alpha, rho, sigma\right) \le \operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right)) \land (\operatorname{renyiRZ}\left(alpha, r, z, rho, sigma\right) \le \operatorname{B2}\left(alpha, q, rho, sigma\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta (2026). *r-deformed α-z-Rényi relative entropy*. URL: <https://arxiv.org/abs/2607.01805v1>.

*Commentary.*

Take rho = diag(4/5,1/5) and sigma = (1/125)[[28,6√6],[6√6,97]]. Both matrices are positive definite with unit trace, and they do not commute. At alpha = r = 1/2, z = 2 and q = 1, the proof gives 2/5 < renyiRZ(alpha,r,z,rho,sigma) and B2(alpha,q,rho,sigma) < 2/5. For the first value the trace inside the deformed logarithm is (2117+288√2)/3125, so B₁ = 4(1−√((2117+288√2)/3125)). For the second, put A = (1/25)[[7,3√6],[3√6,97]]. Its positive square root is (5/√154)(A+1), giving B₂ = 2−20/√154. These inequalities contradict the second conjunct of the proposed order. The inequality tsallis≤renyiRZ is not refuted here.

## References

- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.B2`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.claim`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.lnr`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.renyiRZ`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.result`
- Truth anchor: `D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.tsallis`
- Dependency: [D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus](../Quantum/Matrix/TwoPointFunctionalCalculus.md)
