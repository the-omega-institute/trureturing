# Collision paths for the long-range swap matrices

## Abstract

The literal local matrices and adjacent-slot operators have uniformly bounded positive-weight collision exit paths.

**Definition 1.1 (The local matrix B).**

$$\forall N \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall pi \in \operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right),\; \forall nu \in \operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right),\; \operatorname{B}\left(N, mu, pi, nu\right) = \operatorname{ite}\left(pi = nu \land (\operatorname{Prod}.\operatorname{fst}\left(nu\right) = \operatorname{Prod}.\operatorname{snd}\left(nu\right)), mu\left(\operatorname{Prod}.\operatorname{fst}\left(nu\right)\right), \operatorname{ite}\left(\operatorname{Prod}.\operatorname{fst}\left(pi\right) = \operatorname{Prod}.\operatorname{snd}\left(nu\right) \land (\operatorname{Prod}.\operatorname{snd}\left(pi\right) = \operatorname{Prod}.\operatorname{fst}\left(nu\right) \land (\operatorname{Prod}.\operatorname{fst}\left(nu\right) < \operatorname{Prod}.\operatorname{snd}\left(nu\right))), 1, 0\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.B` (`✓ std3`).

*Citation.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Equation (7), source label 138am42, assigns the diagonal same-species weight mu and the unit weight to a swapped increasing input pair. Species are Fin N, with their natural order.

**Definition 1.2 (The local matrix B prime).**

$$\forall N \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall pi \in \operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right),\; \forall nu \in \operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right),\; \operatorname{Bprime}\left(N, mu, pi, nu\right) = \operatorname{ite}\left(pi = nu \land (\operatorname{Prod}.\operatorname{fst}\left(nu\right) = \operatorname{Prod}.\operatorname{snd}\left(nu\right)), 1 - mu\left(\operatorname{Prod}.\operatorname{fst}\left(nu\right)\right), \operatorname{ite}\left(\operatorname{Prod}.\operatorname{fst}\left(pi\right) = \operatorname{Prod}.\operatorname{snd}\left(nu\right) \land (\operatorname{Prod}.\operatorname{snd}\left(pi\right) = \operatorname{Prod}.\operatorname{fst}\left(nu\right) \land (\operatorname{Prod}.\operatorname{snd}\left(nu\right) < \operatorname{Prod}.\operatorname{fst}\left(nu\right))), 1, 0\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.Bprime` (`✓ std3`).

*Citation.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

The second matrix in equation (7) assigns 1 - mu to an equal pair and the unit weight to a swapped decreasing input pair.

**Definition 1.3 (An adjacent-slot operator).**

$$\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right), \mathbb{R}\right),\; \forall s \in \mathbb{N},\; \forall pi \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(N\right),\; \forall nu \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(N\right),\; \operatorname{adjacent}\left(N, n, M, s, pi, nu\right) = \operatorname{ite}\left(s + 1 < n, M\left((pi\left(\operatorname{Fin}.\operatorname{mk}\left(s\right)\right),pi\left(\operatorname{Fin}.\operatorname{mk}\left(s + 1\right)\right)), (nu\left(\operatorname{Fin}.\operatorname{mk}\left(s\right)\right),nu\left(\operatorname{Fin}.\operatorname{mk}\left(s + 1\right)\right))\right) \cdot \prod_{r:\operatorname{Fin}\left(n\right)} (\operatorname{ite}\left(\operatorname{val}\left(r\right) = s \lor (\operatorname{val}\left(r\right) = s + 1), 1, \operatorname{ite}\left(pi\left(r\right) = nu\left(r\right), 1, 0\right)\right)), 0\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.adjacent` (`✓ std3`).

*Citation.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

The two slots are zero-based s and s + 1. The product imposes the identity on every other slot. The value is zero when s + 1 is outside Fin n. Fin.mk displays only the value component; its bound proof is suppressed. All implicit size parameters are displayed explicitly.

**Definition 1.4 (The block coefficient).**

$$\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall j \in \mathbb{N},\; \forall i \in \mathbb{N},\; \operatorname{calB}\left(N, n, mu, j, i\right) = \operatorname{adjacent}\left(N, n, \operatorname{B}\left(N, mu\right), j + i - 2\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.calB` (`✓ std3`).

*Citation.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

The source tensor product I to the power j + i - 2, then B, then I to the power n - j - i acts on the one-indexed slots j + i - 1 and j + i. Natural subtraction in the slot argument is truncated subtraction.

**Definition 1.5 (The second block coefficient).**

$$\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall j \in \mathbb{N},\; \forall i \in \mathbb{N},\; \operatorname{calBprime}\left(N, n, mu, j, i\right) = \operatorname{adjacent}\left(N, n, \operatorname{Bprime}\left(N, mu\right), j + i - 2\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.calBprime` (`✓ std3`).

*Citation.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

The same adjacent-slot construction uses B prime in place of B.

**Definition 1.6 (Exchange the adjacent word slots).**

$$\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall h \in s + 1 < n,\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(N\right),\; \forall r \in \operatorname{Fin}\left(n\right),\; \operatorname{swapWord}\left(N, n, s, h, w\right)\left(r\right) = w\left(\operatorname{Equiv}.\operatorname{swap}\left(\operatorname{Fin}.\operatorname{mk}\left(s\right), \operatorname{Fin}.\operatorname{mk}\left(s + 1\right), r\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.swapWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Precomposition with Equiv.swap exchanges the two valid adjacent coordinates. The proof h guarantees both Fin constructors are valid.

**Theorem 1.7 (The row action of the block coefficient).**

$$\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall j \in \mathbb{N},\; \forall i \in \mathbb{N},\; \forall h \in j + i - 2 + 1 < n,\; \forall f \in \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(N\right)\right) \to \mathbb{R},\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(N\right),\; \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{calB}\left(N, n, mu, j, i\right), f\right)\left(w\right) = \operatorname{B}\left(N, mu, (w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2\right)\right),w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2 + 1\right)\right)), (\operatorname{Prod}.\operatorname{snd}\left((w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2\right)\right),w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2 + 1\right)\right))\right),\operatorname{Prod}.\operatorname{fst}\left((w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2\right)\right),w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2 + 1\right)\right))\right))\right) \cdot f\left(\operatorname{swapWord}\left(N, n, j + i - 2, h, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.calB_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Every row has one possible successor word. Its coefficient is the corresponding swapped entry of B.

**Theorem 1.8 (The second row action).**

$$\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall j \in \mathbb{N},\; \forall i \in \mathbb{N},\; \forall h \in j + i - 2 + 1 < n,\; \forall f \in \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(N\right)\right) \to \mathbb{R},\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(N\right),\; \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{calBprime}\left(N, n, mu, j, i\right), f\right)\left(w\right) = \operatorname{Bprime}\left(N, mu, (w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2\right)\right),w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2 + 1\right)\right)), (\operatorname{Prod}.\operatorname{snd}\left((w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2\right)\right),w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2 + 1\right)\right))\right),\operatorname{Prod}.\operatorname{fst}\left((w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2\right)\right),w\left(\operatorname{Fin}.\operatorname{mk}\left(j + i - 2 + 1\right)\right))\right))\right) \cdot f\left(\operatorname{swapWord}\left(N, n, j + i - 2, h, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.calBprime_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

The same row rule holds for B prime.

**Theorem 1.9 (The two outgoing masses).**

$$\forall N \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (\forall a \in \operatorname{Fin}\left(N\right),\; 0 \le mu\left(a\right) \land (mu\left(a\right) \le 1)) \Rightarrow (\forall pi \in \operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right),\; 0 \le \operatorname{B}\left(N, mu, pi, (\operatorname{Prod}.\operatorname{snd}\left(pi\right),\operatorname{Prod}.\operatorname{fst}\left(pi\right))\right) \land (0 \le \operatorname{Bprime}\left(N, mu, pi, (\operatorname{Prod}.\operatorname{snd}\left(pi\right),\operatorname{Prod}.\operatorname{fst}\left(pi\right))\right) \land (\operatorname{B}\left(N, mu, pi, (\operatorname{Prod}.\operatorname{snd}\left(pi\right),\operatorname{Prod}.\operatorname{fst}\left(pi\right))\right) + \operatorname{Bprime}\left(N, mu, pi, (\operatorname{Prod}.\operatorname{snd}\left(pi\right),\operatorname{Prod}.\operatorname{fst}\left(pi\right))\right) = 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.weights_nonneg_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

For each pair and each parameter in the closed unit interval, the two swapped entries are nonnegative and sum to one. This includes both endpoint parameters.

**Definition 1.10 (Exchange an integer-indexed pair).**

$$\forall N \in \mathbb{N},\; \forall w \in \mathbb{Z} \to \operatorname{Fin}\left(N\right),\; \forall i \in \mathbb{Z},\; \forall x \in \mathbb{Z},\; \operatorname{Path}.\operatorname{swap}\left(N, w, i\right)\left(x\right) = w\left(\operatorname{Equiv}.\operatorname{swap}\left(i, i + 1, x\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.swap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Integer-indexed words use the existing coordinate transposition Equiv.swap.

**Definition 1.11 (Choose a collision direction).**

$$\forall N \in \mathbb{N},\; \forall pref \in \operatorname{Fin}\left(N\right) \to \operatorname{Bool},\; \forall s \in \mathbb{Z} \times (\mathbb{Z} \to \operatorname{Fin}\left(N\right)),\; \operatorname{Path}.\operatorname{left}\left(N, pref, s\right) = \operatorname{ite}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right) + 1\right) < \operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right)\right), \operatorname{true}, \operatorname{ite}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right)\right) < \operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right) + 1\right), \operatorname{false}, pref\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.left` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Move toward the smaller label. At an equal pair use its preferred direction.

**Definition 1.12 (A collision transition).**

$$\forall N \in \mathbb{N},\; \forall pref \in \operatorname{Fin}\left(N\right) \to \operatorname{Bool},\; \forall s \in \mathbb{Z} \times (\mathbb{Z} \to \operatorname{Fin}\left(N\right)),\; \operatorname{Path}.\operatorname{next}\left(N, pref, s\right) = (\operatorname{ite}\left(\operatorname{Path}.\operatorname{left}\left(N, pref, s\right), \operatorname{Prod}.\operatorname{fst}\left(s\right) - 1, \operatorname{Prod}.\operatorname{fst}\left(s\right) + 1\right),\operatorname{Path}.\operatorname{swap}\left(N, \operatorname{Prod}.\operatorname{snd}\left(s\right), \operatorname{Prod}.\operatorname{fst}\left(s\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.next` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Swap the collision pair and move its position one step in the selected direction.

**Definition 1.13 (The interior collision positions).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall s \in \mathbb{Z} \times (\mathbb{Z} \to \operatorname{Fin}\left(N\right)),\; \operatorname{Path}.\operatorname{interior}\left(N, m, s\right) = \left(0 \le \operatorname{Prod}.\operatorname{fst}\left(s\right) \land (\operatorname{Prod}.\operatorname{fst}\left(s\right) < (m:\mathbb{Z}))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.interior` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Interior positions are the integers from zero through m - 1; all other positions are boundary states.

**Definition 1.14 (Select a positive equal-pair weight).**

$$\forall N \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall a \in \operatorname{Fin}\left(N\right),\; \operatorname{Path}.\operatorname{preferred}\left(N, mu, a\right) = \operatorname{decide}\left(\frac{1}{2} \le mu\left(a\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.preferred` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

Choose left at a same-species pair when mu is at least one half; otherwise choose right. The displayed fraction is real division.

**Definition 1.15 (The left successor).**

$$\forall N \in \mathbb{N},\; \forall s \in \mathbb{Z} \times (\mathbb{Z} \to \operatorname{Fin}\left(N\right)),\; \operatorname{Path}.\operatorname{leftState}\left(N, s\right) = (\operatorname{Prod}.\operatorname{fst}\left(s\right) - 1,\operatorname{Path}.\operatorname{swap}\left(N, \operatorname{Prod}.\operatorname{snd}\left(s\right), \operatorname{Prod}.\operatorname{fst}\left(s\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.leftState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

The left successor swaps the pair and decrements its position.

**Definition 1.16 (The right successor).**

$$\forall N \in \mathbb{N},\; \forall s \in \mathbb{Z} \times (\mathbb{Z} \to \operatorname{Fin}\left(N\right)),\; \operatorname{Path}.\operatorname{rightState}\left(N, s\right) = (\operatorname{Prod}.\operatorname{fst}\left(s\right) + 1,\operatorname{Path}.\operatorname{swap}\left(N, \operatorname{Prod}.\operatorname{snd}\left(s\right), \operatorname{Prod}.\operatorname{fst}\left(s\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.rightState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

The right successor swaps the pair and increments its position.

**Definition 1.17 (The selected transition weight).**

$$\forall N \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall s \in \mathbb{Z} \times (\mathbb{Z} \to \operatorname{Fin}\left(N\right)),\; \operatorname{Path}.\operatorname{chosenWeight}\left(N, mu, s\right) = \operatorname{ite}\left(\operatorname{Path}.\operatorname{left}\left(N, \operatorname{Path}.\operatorname{preferred}\left(N, mu\right), s\right), \operatorname{B}\left(N, mu, (\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right)\right),\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right) + 1\right)), (\operatorname{Prod}.\operatorname{snd}\left((\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right)\right),\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right) + 1\right))\right),\operatorname{Prod}.\operatorname{fst}\left((\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right)\right),\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right) + 1\right))\right))\right), \operatorname{Bprime}\left(N, mu, (\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right)\right),\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right) + 1\right)), (\operatorname{Prod}.\operatorname{snd}\left((\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right)\right),\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right) + 1\right))\right),\operatorname{Prod}.\operatorname{fst}\left((\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right)\right),\operatorname{Prod}.\operatorname{snd}\left(s\right)\left(\operatorname{Prod}.\operatorname{fst}\left(s\right) + 1\right))\right))\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.chosenWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

The selected mass is the actual B or B prime matrix entry. No assumption on mu is needed for this selected mass to be positive.

**Theorem 1.18 (A bounded positive-weight exit path).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall mu \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall s \in \mathbb{Z} \times (\mathbb{Z} \to \operatorname{Fin}\left(N\right)),\; \exists l \in \mathbb{N},\; l \le 2 \cdot N \cdot m \land (\left(\neg (\operatorname{Path}.\operatorname{interior}\left(N, m, \operatorname{Function}.\operatorname{iterate}\left(\operatorname{Path}.\operatorname{next}\left(N, \operatorname{Path}.\operatorname{preferred}\left(N, mu\right)\right), l, s\right)\right))\right) \land (0 < \prod_{r:\operatorname{Fin}\left(l\right)} \operatorname{Path}.\operatorname{chosenWeight}\left(N, mu, \operatorname{Function}.\operatorname{iterate}\left(\operatorname{Path}.\operatorname{next}\left(N, \operatorname{Path}.\operatorname{preferred}\left(N, mu\right)\right), \operatorname{val}\left(r\right), s\right)\right) \land (\left(\forall r \in \mathbb{N},\; (r < l) \Rightarrow (\operatorname{Path}.\operatorname{interior}\left(N, m, \operatorname{Function}.\operatorname{iterate}\left(\operatorname{Path}.\operatorname{next}\left(N, \operatorname{Path}.\operatorname{preferred}\left(N, mu\right)\right), r, s\right)\right))\right) \land (\operatorname{Relation}.\operatorname{ReflTransGen}\left(\lambda a:\mathbb{Z} \times (\mathbb{Z} \to \operatorname{Fin}\left(N\right)) \mapsto \lambda b:\mathbb{Z} \times (\mathbb{Z} \to \operatorname{Fin}\left(N\right)) \mapsto \operatorname{Path}.\operatorname{interior}\left(N, m, a\right) \land (\left(0 < \operatorname{B}\left(N, mu, (\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right)\right),\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right) + 1\right)), (\operatorname{Prod}.\operatorname{snd}\left((\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right)\right),\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right) + 1\right))\right),\operatorname{Prod}.\operatorname{fst}\left((\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right)\right),\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right) + 1\right))\right))\right) \land (\operatorname{Path}.\operatorname{leftState}\left(N, a\right) = b)\right) \lor (0 < \operatorname{Bprime}\left(N, mu, (\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right)\right),\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right) + 1\right)), (\operatorname{Prod}.\operatorname{snd}\left((\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right)\right),\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right) + 1\right))\right),\operatorname{Prod}.\operatorname{fst}\left((\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right)\right),\operatorname{Prod}.\operatorname{snd}\left(a\right)\left(\operatorname{Prod}.\operatorname{fst}\left(a\right) + 1\right))\right))\right) \land (\operatorname{Path}.\operatorname{rightState}\left(N, a\right) = b))), s, \operatorname{Function}.\operatorname{iterate}\left(\operatorname{Path}.\operatorname{next}\left(N, \operatorname{Path}.\operatorname{preferred}\left(N, mu\right)\right), l, s\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.exits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eunghyun Lee (2026). *Integrability of multispecies long-range swap models with species-dependent interpolation*. DOI: [10.1088/1742-5468/ae80b5](https://doi.org/10.1088/1742-5468/ae80b5). URL: <https://arxiv.org/abs/2604.12136v1>.

*Commentary.*

The minimum collision label never increases. While the minimum stays fixed, a direction change can only turn toward the preferred direction of that label, so there is at most one reversal. A decreasing integer rank combines the label, this reversal budget, and the remaining distance. Its bound is 2 N m. Following the selected transitions gives an exit of at most that length, positive product weight, interior states before the endpoint, and a path in the positive-weight transition relation. The conclusion applies to every real parameter vector; nonnegativity of both outgoing masses is a separate interval condition.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.B`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.Bprime`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.adjacent`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.calB`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.calB_mulVec`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.calBprime`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.calBprime_mulVec`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.chosenWeight`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.exits`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.interior`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.left`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.leftState`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.next`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.preferred`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.rightState`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.swap`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.swapWord`
- Truth anchor: `D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.weights_nonneg_sum`
