# A negative damped spin distribution satisfying the Husimi coefficient bound

## Abstract

The damped spin kernel criterion fails for spin three-halves.

**Definition 1.1 (Doubled spin selection rules).**

$$\forall j \in \mathbb{Z},\; \forall m \in \mathbb{Z},\; \operatorname{SpinValid}\left(j, m\right) \Leftrightarrow ((0 \le j) \land ((0 - j \le m) \land ((m \le j) \land (\operatorname{mod}\left(j - m, 2\right) = 0))))$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.SpinValid` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

The integers j and m are twice the spin and magnetic quantum numbers. The parity condition uses Euclidean integer remainder.

**Definition 1.2 (Clebsch–Gordan selection rules).**

$$\forall jone \in \mathbb{Z},\; \forall mone \in \mathbb{Z},\; \forall jtwo \in \mathbb{Z},\; \forall mtwo \in \mathbb{Z},\; \forall J \in \mathbb{Z},\; \forall M \in \mathbb{Z},\; \operatorname{CGValid}\left(jone, mone, jtwo, mtwo, J, M\right) \Leftrightarrow ((\operatorname{SpinValid}\left(jone, mone\right)) \land ((\operatorname{SpinValid}\left(jtwo, mtwo\right)) \land ((\operatorname{SpinValid}\left(J, M\right)) \land ((M = mone + mtwo) \land ((J \le jone + jtwo) \land ((jone - jtwo \le J) \land ((jtwo - jone \le J) \land (\operatorname{mod}\left(jone + jtwo + J, 2\right) = 0))))))))$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.CGValid` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

All three magnetic rules, magnetic conservation, the triangle inequalities and total-spin parity are imposed. Variables jone, mone, jtwo and mtwo denote j₁, m₁, j₂ and m₂.

**Definition 1.3 (The Condon–Shortley Clebsch–Gordan coefficient).**

$$\forall jone \in \mathbb{Z},\; \forall mone \in \mathbb{Z},\; \forall jtwo \in \mathbb{Z},\; \forall mtwo \in \mathbb{Z},\; \forall J \in \mathbb{Z},\; \forall M \in \mathbb{Z},\; \operatorname{CG}\left(jone, mone, jtwo, mtwo, J, M\right) = \operatorname{if} (\operatorname{CGValid}\left(jone, mone, jtwo, mtwo, J, M\right)) \operatorname{then} (\operatorname{let} A = \operatorname{ediv}\left(jone + jtwo - J, 2\right); B = \operatorname{ediv}\left(jone - mone, 2\right); C = \operatorname{ediv}\left(jtwo + mtwo, 2\right); D = \operatorname{ediv}\left(J - jtwo + mone, 2\right); E = \operatorname{ediv}\left(J - jone - mtwo, 2\right); fac = \operatorname{fun} (u:\mathbb{Z}) \mapsto \operatorname{castReal}\left(\operatorname{factorial}\left(\operatorname{toNat}\left(u\right)\right)\right) \operatorname{in} \operatorname{sqrt}\left(\frac{\operatorname{castReal}\left(J + 1\right) \cdot \operatorname{fac}\left(\operatorname{ediv}\left(J + jone - jtwo, 2\right)\right) \cdot \operatorname{fac}\left(\operatorname{ediv}\left(J - jone + jtwo, 2\right)\right) \cdot \operatorname{fac}\left(A\right)}{\operatorname{fac}\left(\operatorname{ediv}\left(jone + jtwo + J, 2\right) + 1\right)} \cdot \operatorname{fac}\left(\operatorname{ediv}\left(J + M, 2\right)\right) \cdot \operatorname{fac}\left(\operatorname{ediv}\left(J - M, 2\right)\right) \cdot \operatorname{fac}\left(\operatorname{ediv}\left(jone + mone, 2\right)\right) \cdot \operatorname{fac}\left(B\right) \cdot \operatorname{fac}\left(C\right) \cdot \operatorname{fac}\left(\operatorname{ediv}\left(jtwo - mtwo, 2\right)\right)\right) \cdot \sum_{z \in \operatorname{range}\left(\operatorname{toNat}\left(A\right) + 1\right)} (\operatorname{if} ((\operatorname{castInt}\left(z\right) \le A) \land ((\operatorname{castInt}\left(z\right) \le B) \land ((\operatorname{castInt}\left(z\right) \le C) \land ((0 \le D + \operatorname{castInt}\left(z\right)) \land (0 \le E + \operatorname{castInt}\left(z\right)))))) \operatorname{then} (\frac{(0 - 1)^{z}}{\operatorname{fac}\left(\operatorname{castInt}\left(z\right)\right) \cdot \operatorname{fac}\left(A - \operatorname{castInt}\left(z\right)\right) \cdot \operatorname{fac}\left(B - \operatorname{castInt}\left(z\right)\right) \cdot \operatorname{fac}\left(C - \operatorname{castInt}\left(z\right)\right) \cdot \operatorname{fac}\left(D + \operatorname{castInt}\left(z\right)\right) \cdot \operatorname{fac}\left(E + \operatorname{castInt}\left(z\right)\right)}) \operatorname{else} (0))) \operatorname{else} (0)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.CG` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

Racah's factorial formula on doubled integer arguments is zero outside the selection rules. The local fac function is the real cast of the factorial of the nonnegative part of its integer argument. Each live summand has nonnegative factorial arguments. ediv is Lean's Euclidean integer division; mod is its remainder. The alternating sign is the Condon–Shortley phase.

**Definition 1.4 (The ordered spin basis).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{mag}\left(n, i\right) = \operatorname{castInt}\left(n\right) - 2 \cdot \operatorname{castInt}\left(\operatorname{val}\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.mag` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

The index i in Fin(n+1) labels the basis J, J−1, …, −J, with J=n/2. val is the natural value of a Fin index; castInt is the integer cast.

**Definition 1.5 (Irreducible tensors).**

$$\forall n \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall k \in \mathbb{Z},\; \forall i \in \operatorname{Fin}\left(n + 1\right),\; \forall j \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{T}\left(n, L, k\right)\left(i, j\right) = \operatorname{ofReal}\left(\operatorname{sqrt}\left(\frac{2 \cdot \operatorname{castReal}\left(L\right) + 1}{\operatorname{castReal}\left(n\right) + 1}\right) \cdot \operatorname{CG}\left(\operatorname{castInt}\left(n\right), \operatorname{mag}\left(n, j\right), 2 \cdot \operatorname{castInt}\left(L\right), 2 \cdot k, \operatorname{castInt}\left(n\right), \operatorname{mag}\left(n, i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.T` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

Equation (12), page 2: "the matrix elements of the irreducible tensors in the standard Ĵz-bases are given by ⟨J, m′|T̂^J_{L,k}|J, m⟩ = √((2L + 1)/(2J + 1)) C^{Jm′}_{Jm Lk}, where the C^{JM}_{j1 m1 j2 m2} denote the Clebsch-Gordan coefficients." Row i is m′ and column j is m. castReal, castInt and ofReal make the scalar embeddings explicit.

**Definition 1.6 (Density-matrix multipoles).**

$$\forall n \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right),\; \forall L \in \mathbb{N},\; \forall k \in \mathbb{Z},\; \operatorname{rhoCoeff}\left(rho, L, k\right) = \operatorname{trace}\left(\operatorname{conjTranspose}\left(\operatorname{T}\left(n, L, k\right)\right) \cdot rho\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.rhoCoeff` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

Equation (13), page 2: "ρ̂ = Σ_{L=0}^{2J} Σ_{k=−L}^{L} ρ_{Lk} T̂^J_{L,k}, ρ_{L,k} = tr((T̂^J_{L,k})† ρ̂)." The adjoint precedes the density matrix in the product.

**Definition 1.7 (Legendre polynomials).**

$$\forall L \in \mathbb{N},\; \operatorname{legendre}\left(L\right) = \operatorname{comp}\left(\operatorname{map}\left(\operatorname{shiftedLegendre}\left(L\right), \operatorname{castRingHom}\left(\mathbb{R}\right)\right), \operatorname{C}\left(\frac{1}{2}\right) \cdot (1 - X)\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.legendre` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

Polynomial.shiftedLegendre L is the integer polynomial P_L(1−2x). Mapping to real coefficients and composing with (1−X)/2 gives the ordinary Legendre polynomial for every natural degree.

**Definition 1.8 (Associated Legendre functions).**

$$\forall L \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall x \in \mathbb{R},\; \operatorname{assocLegendre}\left(L, m, x\right) = (0 - 1)^{m} \cdot (\operatorname{sqrt}\left(1 - (x)^{2}\right))^{m} \cdot \operatorname{eval}\left(\operatorname{iterate}\left(\operatorname{derivative}, m, \operatorname{legendre}\left(L\right)\right), x\right)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.assocLegendre` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

The Condon–Shortley factor is (−1)^m. iterate(derivative,m,p) means m applications of Polynomial.derivative to p; eval evaluates the resulting polynomial at x. The square root is the nonnegative real square root.

**Definition 1.9 (Scaled harmonics of nonnegative order).**

$$\forall L \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall theta \in \mathbb{R},\; \forall phi \in \mathbb{R},\; \operatorname{Ypos}\left(L, m, theta, phi\right) = \operatorname{if} (m \le L) \operatorname{then} (\operatorname{ofReal}\left(\operatorname{sqrt}\left(\frac{\left(2 \cdot \operatorname{castReal}\left(L\right) + 1\right) \cdot \operatorname{castReal}\left(\operatorname{factorial}\left(\operatorname{natSub}\left(L, m\right)\right)\right)}{\operatorname{castReal}\left(\operatorname{factorial}\left(L + m\right)\right)}\right) \cdot \operatorname{assocLegendre}\left(L, m, \operatorname{cos}\left(theta\right)\right)\right) \cdot \operatorname{complexExp}\left(I \cdot \operatorname{castComplex}\left(m\right) \cdot \operatorname{ofReal}\left(phi\right)\right)) \operatorname{else} (0)$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.Ypos` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

Footnote 1, page 3: "We use the convention Y^0_0 = 1, so that the spherical harmonics are orthonormal with respect to the uniform probability measure dµ^0_{θ,ϕ} = (4π)^{−1} sin θ dθ dϕ. This differs from the Condon–Shortley convention by a factor of √4π: Y_{Lm} = √4π Y_{Lm,CS}". The usual 1/√4π factor is therefore absent. The imaginary unit is I. Natural subtraction in L−m is expressed by natSub, and factorials have natural arguments.

**Definition 1.10 (Scaled harmonics of all integer orders).**

$$\forall L \in \mathbb{N},\; \forall k \in \mathbb{Z},\; \forall theta \in \mathbb{R},\; \forall phi \in \mathbb{R},\; \operatorname{Y}\left(L, k, theta, phi\right) = \operatorname{if} (0 \le k) \operatorname{then} (\operatorname{Ypos}\left(L, \operatorname{toNat}\left(k\right), theta, phi\right)) \operatorname{else} ((\operatorname{ofReal}\left(0 - 1\right))^{\operatorname{natAbs}\left(k\right)} \cdot \operatorname{star}\left(\operatorname{Ypos}\left(L, \operatorname{natAbs}\left(k\right), theta, phi\right)\right))$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.Y` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

Nonnegative k uses toNat(k). Negative k uses the Condon–Shortley conjugation identity with natAbs(k). Harmonics vanish outside |k|≤L.

**Definition 1.11 (The binomial ratio).**

$$\forall n \in \mathbb{N},\; \forall L \in \mathbb{N},\; \operatorname{r}\left(n, L\right) = \frac{\operatorname{castReal}\left(\operatorname{choose}\left(n, L\right)\right)}{\operatorname{castReal}\left(\operatorname{choose}\left(n + L + 1, L\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.r` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

The binomial ratio in equations (44) and (53) is a quotient of real casts of natural binomial coefficients.

**Definition 1.12 (The damped quasidistribution).**

$$\forall n \in \mathbb{N},\; \forall sigma \in \mathbb{R},\; \forall gamma \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right),\; \forall theta \in \mathbb{R},\; \forall phi \in \mathbb{R},\; \operatorname{F}\left(n, sigma, gamma, t, rho, theta, phi\right) = \operatorname{ofReal}\left((\operatorname{castReal}\left(n\right) + 1)^{\frac{0 - 1}{2}}\right) \cdot \sum_{L \in \operatorname{range}\left(n + 1\right)} (\sum_{k \in \operatorname{Icc}\left(0 - \operatorname{castInt}\left(L\right), \operatorname{castInt}\left(L\right)\right)} (\operatorname{ofReal}\left(\operatorname{exp}\left(\frac{\left(0 - gamma\right) \cdot \operatorname{castReal}\left(L\right) \cdot \left(\operatorname{castReal}\left(L\right) + 1\right) \cdot t}{2}\right) \cdot (\operatorname{r}\left(n, L\right))^{\frac{0 - sigma}{2}}\right) \cdot \operatorname{rhoCoeff}\left(rho, L, k\right) \cdot \operatorname{star}\left(\operatorname{Y}\left(L, k, theta, phi\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.F` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

Equation (44), page 5: "F^σ(θ, ϕ, t) = a_J Σ_{L,k} e^{−γ L(L+1) t/2} ( C(2J, L) / C(2J+L+1, L) )^{−σ/2} ρ_{Lk}(0) overline(Y_{Lk}(θ, ϕ))." Equations (35)–(36) give a_J=(2J+1)^{−1/2}. The outer sum is over range(n+1) and the inner sum over the integer interval Icc(−castInt(L),castInt(L)). rpow denotes the real power, ofReal the complex embedding. sigma, gamma, theta and phi stand for σ, γ, θ and ϕ.

**Definition 1.13 (The positivity conjecture).**

$$\operatorname{claim} \Leftrightarrow (\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\forall sigma \in \mathbb{R},\; (sigma \in \operatorname{Icc}\left(0 - 1, 1\right)) \Rightarrow (\forall gamma \in \mathbb{R},\; (0 < gamma) \Rightarrow (\forall t \in \mathbb{R},\; (0 \le t) \Rightarrow ((\forall L \in \mathbb{N},\; (L \le n) \Rightarrow (\operatorname{exp}\left(\frac{\left(0 - gamma\right) \cdot \operatorname{castReal}\left(L\right) \cdot \left(\operatorname{castReal}\left(L\right) + 1\right) \cdot t}{2}\right) \cdot (\operatorname{r}\left(n, L\right))^{\frac{0 - sigma}{2}} \le (\operatorname{r}\left(n, L\right))^{\frac{1}{2}})) \Rightarrow (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \mathbb{C}\right),\; (\operatorname{IsDensity}\left(rho\right)) \Rightarrow (\forall theta \in \mathbb{R},\; \forall phi \in \mathbb{R},\; 0 \le \operatorname{re}\left(\operatorname{F}\left(n, sigma, gamma, t, rho, theta, phi\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.claim` (`✓ std3`).

*Citation.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

Section VI, page 8: "For J > 1/2 we do not have an exact result, but it seems reasonable to conjecture that positivity is ensured provided that the damped σ kernel in (44), due to decoherence, becomes no sharper than the Husimi (σ = −1) kernel. That is, if e^{−½γL(L+1)} ( C(2J,L)/C(2J+L+1,L) )^{−σ/2} ≤ ( C(2J,L)/C(2J+L+1,L) )^{1/2} (53) for all L, then we restore positivity." Equation (12), page 2: "the matrix elements of the irreducible tensors in the standard Ĵz-bases are given by ⟨J, m′|T̂^J_{L,k}|J, m⟩ = √((2L + 1)/(2J + 1)) C^{Jm′}_{Jm Lk}, where the C^{JM}_{j1 m1 j2 m2} denote the Clebsch-Gordan coefficients." Equation (13), page 2: "ρ̂ = Σ_{L=0}^{2J} Σ_{k=−L}^{L} ρ_{Lk} T̂^J_{L,k}, ρ_{L,k} = tr((T̂^J_{L,k})† ρ̂)." Equation (44), page 5: "F^σ(θ, ϕ, t) = a_J Σ_{L,k} e^{−γ L(L+1) t/2} ( C(2J, L) / C(2J+L+1, L) )^{−σ/2} ρ_{Lk}(0) overline(Y_{Lk}(θ, ϕ))." Footnote 1, page 3: "We use the convention Y^0_0 = 1, so that the spherical harmonics are orthonormal with respect to the uniform probability measure dµ^0_{θ,ϕ} = (4π)^{−1} sin θ dθ dϕ. This differs from the Condon–Shortley convention by a factor of √4π: Y_{Lm} = √4π Y_{Lm,CS}". The encoding uses n=2J≥2, sigma∈[−1,1], gamma>0, t≥0, every L≤n, every positive semidefinite unit-trace matrix rho on Fin(n+1), and all real angles theta and phi. IsDensity is the existing positive-semidefinite unit-trace predicate. Equation (53) is printed without t; the time-dependent premise follows (44), and the counterexample has t=1 so both readings coincide. Real-part nonnegativity is a necessary condition for positivity. The symbols X and I in the definitions denote Polynomial.X and Complex.I, respectively.

**Theorem 1.14 (Refutation at spin three-halves).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/brody-graefe-melanathuru-2026-damped-kernel-positivity` (refuted) by `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"brody-graefe-melanathuru-2026-damped-kernel-positivity","declaration_gid":"D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru (2026). *Phase-space measurements and decoherence for angular momentum systems*. DOI: [10.48550/arXiv.2605.02696](https://doi.org/10.48550/arXiv.2605.02696). URL: <https://arxiv.org/abs/2605.02696v1>.

*Commentary.*

Set n=3, sigma=1, gamma=log(20/11), t=1, rho=Matrix.single(3,3,1) on Fin 4, and theta=phi=0. The four binomial ratios are 1, 3/5, 1/5 and 1/35, and q=exp(−gamma)=11/20 satisfies q^(L(L+1)/2)≤r(3,L) for every L≤3. At the north pole only k=0 contributes. The lowest-weight state's multipole signs alternate, giving F=(1−3q+5q³−7q⁶)/4=−760927/256000000<0. The density predicate is reused directly from D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity: positive semidefinite and trace one. The counterexample has t=1, so equation (53)'s printed omission of t does not affect the refutation.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.CG`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.CGValid`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.F`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.SpinValid`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.T`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.Y`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.Ypos`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.assocLegendre`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.legendre`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.mag`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.r`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation.rhoCoeff`
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
