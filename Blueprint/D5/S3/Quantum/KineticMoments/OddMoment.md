# Kinetic odd frequency moments

## Abstract

The kinetic contribution obeys the all-order odd-moment formula for every isotropic momentum distribution with finite required moments.

**Definition 1.1 (Single-particle momentum shift).**

$$\forall N: \mathbb{N}, \forall j: \operatorname{Fin}\left(N\right), \forall v: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{shift}\left(j, v\right) = \operatorname{LinearMap}.\operatorname{funLeft}\left(\mathbb{C}, \mathbb{C}, (P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mapsto \operatorname{Function}.\operatorname{update}\left(P, j, P\left(j\right) + v\right))\right)$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.shift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

The momentum-space construction acts on every complex-valued configuration function. It replaces only particle j by p_j + v. The linear map is Mathlib LinearMap.funLeft; no regularity or operator-domain restriction is imposed.

**Definition 1.2 (Density operator).**

$$\forall N: \mathbb{N}, \forall hbar: \mathbb{R}, \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{rho}\left(N, hbar, q\right) = \sum_{j:\operatorname{Fin}\left(N\right)} (\operatorname{shift}\left(j, \operatorname{smul}\left(hbar, q\right)\right))$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.rho` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

Sec. 2.4, p. 5, gives the microscopic density operator and its Hermitian conjugate as sums of opposite position exponentials. In the momentum convention these are sums of pullbacks by +hbar q and -hbar q respectively. Multiplication of a real scalar and a vector here denotes real scalar multiplication.

**Definition 1.3 (Conjugate density operator).**

$$\forall N: \mathbb{N}, \forall hbar: \mathbb{R}, \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{rhoDag}\left(N, hbar, q\right) = \sum_{j:\operatorname{Fin}\left(N\right)} (\operatorname{shift}\left(j, -\operatorname{smul}\left(hbar, q\right)\right))$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.rhoDag` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

Sec. 2.4, p. 5, gives the microscopic density operator and its Hermitian conjugate as sums of opposite position exponentials. In the momentum convention these are sums of pullbacks by +hbar q and -hbar q respectively. Multiplication of a real scalar and a vector here denotes real scalar multiplication.

**Definition 1.4 (Kinetic energy multiplier).**

$$\forall N: \mathbb{N}, \forall m: \mathbb{R}, \forall P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{energy}\left(m, P\right) = \sum_{j:\operatorname{Fin}\left(N\right)} (\frac{\Vert P\left(j\right)\Vert ^{2}}{2 \cdot m})$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.energy` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

The source substitutes the kinetic energy operator K = sum_i p_i^2/(2m) (Sec. 2.4, p. 5). The squared momentum is the Euclidean norm squared, and each term is divided by twice the common mass.

**Definition 1.5 (Kinetic operator).**

$$\forall N: \mathbb{N}, \forall m: \mathbb{R}, \operatorname{kinetic}\left(N, m\right) = \operatorname{LinearMap}.\operatorname{mulLeft}\left(\mathbb{C}, (P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mapsto (\operatorname{val}\left(\operatorname{energy}\left(m, P\right)\right): \mathbb{C}))\right)$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.kinetic` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

The kinetic Hamiltonian acts by multiplication by the real energy, embedded in the complex numbers. This uses the existing LinearMap.mulLeft construction.

**Definition 1.6 (One kinetic commutator nest).**

$$\forall N: \mathbb{N}, \forall m: \mathbb{R}, \forall X: \operatorname{Module}.\operatorname{End}\left(\mathbb{C}, (((\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)) \to \mathbb{C})\right), \operatorname{delta}\left(m, X\right) = X \cdot \operatorname{kinetic}\left(N, m\right) - \operatorname{kinetic}\left(N, m\right) \cdot X$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.delta` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

Sec. 2.2, p. 3: "The pure kinetic contribution to the odd dynamic structure factor frequency moments of arbitrary order is obtained from Eq.(4) by considering only the kinetic part of the Hamiltonian, i.e. setting Ĥ ≡ K̂." Thus the first H nest and all later K nests coincide. delta(X) is [X,K], with this order.

**Definition 1.7 (The split nested commutator).**

$$\forall N: \mathbb{N}, \forall hbar: \mathbb{R}, \forall m: \mathbb{R}, \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \forall k: \mathbb{N}, \forall ell: \mathbb{N}, \operatorname{C}\left(N, hbar, m, q, k, ell\right) = \operatorname{Bracket}.\operatorname{bracket}\left(\operatorname{Function}.\operatorname{iterate}\left(\operatorname{delta}\left(m\right), \operatorname{Nat}.\operatorname{sub}\left(2 \cdot k + 1, ell\right)\right)\left(\operatorname{rho}\left(N, hbar, q\right)\right), \operatorname{Function}.\operatorname{iterate}\left(\operatorname{delta}\left(m\right), ell\right)\left(\operatorname{rhoDag}\left(N, hbar, q\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.C` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

Equation (9), p. 3, assigns 2k+1-ell nests to rho and ell nests to rhoDag. iterate denotes Function.iterate; the sub in its natural-number exponent is Nat.sub (truncated subtraction). The later hypothesis ell ≤ 2k+1 ensures the two counts sum to 2k+1. Bracket.bracket is the ring commutator XY-YX.

**Definition 1.8 (Recoil energy).**

$$\forall hbar: \mathbb{R}, \forall m: \mathbb{R}, \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{a}\left(hbar, m, q\right) = \frac{hbar^{2} \cdot \Vert q\Vert ^{2}}{2 \cdot m}$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

This recoil energy is the momentum-independent part of the energy difference under the shift hbar q.

**Definition 1.9 (Directional energy increment).**

$$\forall N: \mathbb{N}, \forall hbar: \mathbb{R}, \forall m: \mathbb{R}, \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \forall j: \operatorname{Fin}\left(N\right), \forall P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{b}\left(hbar, m, q, j, P\right) = \frac{hbar}{m} \cdot \langle q,P\left(j\right)\rangle $$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

The linear increment depends on the same particle and momentum configuration as the kinetic energy. It is (hbar/m) times the real inner product q·p_j.

**Definition 1.10 (The real commutator multiplier).**

$$\forall N: \mathbb{N}, \forall hbar: \mathbb{R}, \forall m: \mathbb{R}, \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \forall k: \mathbb{N}, \forall ell: \mathbb{N}, \forall P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{F}\left(hbar, m, q, k, ell, P\right) = \left(-1\right)^{ell} \cdot \sum_{j:\operatorname{Fin}\left(N\right)} (\left(\operatorname{b}\left(hbar, m, q, j, P\right) + \operatorname{a}\left(hbar, m, q\right)\right)^{2 \cdot k + 1} - \left(\operatorname{b}\left(hbar, m, q, j, P\right) - \operatorname{a}\left(hbar, m, q\right)\right)^{2 \cdot k + 1})$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

This multiplier records the two surviving same-particle shift products. All products with different particle labels cancel. It is defined independently of the nested operator expression.

**Definition 1.11 (Finite highest required moment).**

$$\forall N: \mathbb{N}, \forall nu: \operatorname{Measure}\left(((\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right))\right), \forall k: \mathbb{N}, \operatorname{FiniteTopMoment}\left(nu, k\right) \Leftrightarrow (\forall j: \operatorname{Fin}\left(N\right), \operatorname{Integrable}\left((P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mapsto \Vert P\left(j\right)\Vert ^{2 \cdot k}), nu\right))$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.FiniteTopMoment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

The finite 2k-th moment is assumed for each particle. Under a probability measure all lower even moments follow by domination with 1+|p_j|^(2k).

**Definition 1.12 (Per-particle radial average).**

$$\forall N: \mathbb{N}, \forall nu: \operatorname{Measure}\left(((\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right))\right), \forall i: \mathbb{N}, \operatorname{momentumMoment}\left(nu, i\right) = (\operatorname{val}\left(N\right): \mathbb{R})^{-1} \cdot \sum_{j:\operatorname{Fin}\left(N\right)} (\int_{P:(\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)} \Vert P\left(j\right)\Vert ^{2 \cdot i} \mathrm{d} nu)$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.momentumMoment` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

The source averages even powers of momentum over the exact distribution (Sec. 2.3, p. 5). The per-particle convention is N^-1 times the sum of the individual radial integrals, rather than a moment of the total many-particle kinetic energy.

**Definition 1.13 (The complex sum-rule prefactor).**

$$\forall N: \mathbb{N}, \forall k: \mathbb{N}, \forall ell: \mathbb{N}, \forall hbar: \mathbb{R}, \operatorname{prefactor}\left(N, k, ell, hbar\right) = (-1:\mathbb{C})^{k + ell + 1} \cdot \frac{(\operatorname{val}\left(hbar\right): \mathbb{C})}{2 \cdot (\operatorname{val}\left(N\right): \mathbb{C})} \cdot (\frac{\operatorname{Complex}.\operatorname{I}}{(\operatorname{val}\left(hbar\right): \mathbb{C})})^{2 \cdot k + 2}$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.prefactor` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

Equation (9), p. 3, gives (-1)^(k+ell+1) hbar/(2N) (imath/hbar)^(2k+2). Its arithmetic is complex, and N and hbar are embedded in the complex numbers before division.

**Definition 1.14 (The conjectured odd moment).**

$$\forall N: \mathbb{N}, \forall hbar: \mathbb{R}, \forall m: \mathbb{R}, \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \forall nu: \operatorname{Measure}\left(((\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right))\right), \forall k: \mathbb{N}, \operatorname{target}\left(hbar, m, q, nu, k\right) = \frac{(\frac{hbar \cdot \Vert q\Vert ^{2}}{2 \cdot m})^{2 \cdot k + 1}}{2 \cdot (\operatorname{val}\left(k\right): \mathbb{R}) + 2} \cdot \sum_{i \in \operatorname{Finset}.\operatorname{range}\left(k + 1\right)} ((\operatorname{val}\left(\operatorname{Nat}.\operatorname{choose}\left(2 \cdot k + 2, 2 \cdot i + 1\right)\right): \mathbb{R}) \cdot (\frac{2}{hbar \cdot \Vert q\Vert })^{2 \cdot i} \cdot \operatorname{momentumMoment}\left(nu, i\right))$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.target` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

Equation (16), Sec. 2.3, p. 5, is encoded literally, with q the norm of the real wave vector, all divisions real and the finite sum indexed by Finset.range(k+1), hence 0 ≤ i ≤ k. choose is Nat.choose. The natural sum indices are embedded in the reals before the denominators are formed.

**Definition 1.15 (The Tolias-Dornheim-Vorberger conjecture).**

$$claim \Leftrightarrow (\forall N: \mathbb{N}, (1 \le N) \Rightarrow \forall hbar: \mathbb{R}, \forall m: \mathbb{R}, (0 < hbar) \Rightarrow \left((0 < m) \Rightarrow \forall q: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), (q \ne 0) \Rightarrow \forall k: \mathbb{N}, \forall ell: \mathbb{N}, (ell \le 2 \cdot k + 1) \Rightarrow \left((\operatorname{C}\left(N, hbar, m, q, k, ell\right) = \operatorname{LinearMap}.\operatorname{mulLeft}\left(\mathbb{C}, (P: (\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right) \mapsto (\operatorname{val}\left(\operatorname{F}\left(hbar, m, q, k, ell, P\right)\right): \mathbb{C}))\right)) \land (\forall nu: \operatorname{Measure}\left(((\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right))\right), (\operatorname{IsProbabilityMeasure}\left(nu\right)) \Rightarrow \left((\operatorname{IsIsotropic}\left(nu\right)) \Rightarrow \left((\operatorname{FiniteTopMoment}\left(nu, k\right)) \Rightarrow \operatorname{prefactor}\left(N, k, ell, hbar\right) \cdot (\operatorname{val}\left(\int_{P:(\operatorname{Fin}\left(N\right)) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)} \operatorname{F}\left(hbar, m, q, k, ell, P\right) \mathrm{d} nu\right): \mathbb{C}) = (\operatorname{val}\left(\operatorname{target}\left(hbar, m, q, nu, k\right)\right): \mathbb{C})\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Quantum/KineticMoments/OddMoment.claim` (`✓ std3`).

*Citation.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

Sec. 2.3, p. 5: "Therefore, our conjecture states that the following result holds for the interacting uniform electron gas" (Eq. (16)), followed by "where k is an arbitrary non-negative integer." Encoding: N ≥ 1; hbar>0; m>0; q ≠ 0; every k and every ell ≤ 2k+1; the exact operator multiplier identity; every simultaneous-SO(3)-invariant probability measure with finite highest required per-particle moment. The average of the multiplication operator is the integral of its multiplier. The kinetic prescription H ≡ K is the source sentence in Sec. 2.2, p. 3. The statement constructs no thermodynamic-limit state, assumes moment finiteness and makes no assertion about the full non-kinetic moment.

**Theorem 1.16 (All odd kinetic moments satisfy the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/KineticMoments/OddMoment.result` (`✓ std3`). ∎

*Resolves.* `Problems/tolias-dornheim-vorberger-2025-kinetic-odd-moments` (proved) by `D5/S3/Quantum/KineticMoments/OddMoment.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tolias-dornheim-vorberger-2025-kinetic-odd-moments","declaration_gid":"D5/S3/Quantum/KineticMoments/OddMoment.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Tolias; T. Dornheim; J. Vorberger (2025). *Kinetic contribution to the arbitrary order odd frequency moments of the dynamic structure factor*. DOI: [10.1002/ctpp.70090](https://doi.org/10.1002/ctpp.70090). URL: <https://arxiv.org/abs/2508.17810v1>.

*Commentary.*

The operator identity reduces the kinetic average to an odd binomial difference. Isotropic averaging produces 1/(2i+1); Nat.add_one_mul_choose_eq transfers this factor to the denominator 2k+2. Kinematic powers and the complex sum-rule prefactor then give Eq. (16) for every split. The proof imposes no particle-statistics condition: it applies whenever the stated momentum measure exists and is isotropic with finite moments.

## References

- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.C`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.F`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.FiniteTopMoment`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.a`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.b`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.claim`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.delta`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.energy`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.kinetic`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.momentumMoment`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.prefactor`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.result`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.rho`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.rhoDag`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.shift`
- Truth anchor: `D5/S3/Quantum/KineticMoments/OddMoment.target`
- Dependency: [D5/S3/Quantum/KineticMoments/IsotropicAverage](IsotropicAverage.md)
- Dependency: [D5/S3/Quantum/ObserverCommutator](../ObserverCommutator.md)
