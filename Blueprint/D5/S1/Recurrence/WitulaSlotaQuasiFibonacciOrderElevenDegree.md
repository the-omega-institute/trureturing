# Degrees of the Order-Eleven Quasi-Fibonacci Polynomials

## Abstract

Every order-eleven quasi-Fibonacci polynomial in the five families has full degree from index five onward.

The coefficient ring is Z and X represents the paper's variable delta. The five-fold product is right-associated. Thus fst selects its first component and snd moves to the remaining product. Polynomial degree takes values in the naturals with a bottom element; the zero polynomial has degree bottom. A natural number on the right of a degree equality is embedded in that ordered type.

**Definition 1.1 (The order-eleven recurrence system).**

$$\begin{aligned}quasi : \mathbb{N} \to \mathbb{Z}[X] \times (\mathbb{Z}[X] \times (\mathbb{Z}[X] \times (\mathbb{Z}[X] \times \mathbb{Z}[X])))\\\operatorname{quasi}\left(0\right) = (1, 0, 0, 0, 0)\\\forall n \in \mathbb{N},\; \operatorname{A}\left(n + 1\right) = \operatorname{A}\left(n\right) + 2 \cdot X \cdot \operatorname{B}\left(n\right) - X \cdot \operatorname{E}\left(n\right)\\\forall n \in \mathbb{N},\; \operatorname{B}\left(n + 1\right) = X \cdot \operatorname{A}\left(n\right) + \operatorname{B}\left(n\right) + X \cdot \operatorname{C}\left(n\right) - X \cdot \operatorname{E}\left(n\right)\\\forall n \in \mathbb{N},\; \operatorname{C}\left(n + 1\right) = X \cdot \operatorname{B}\left(n\right) + \operatorname{C}\left(n\right) + X \cdot \operatorname{D}\left(n\right) - X \cdot \operatorname{E}\left(n\right)\\\forall n \in \mathbb{N},\; \operatorname{D}\left(n + 1\right) = X \cdot \operatorname{C}\left(n\right) + \operatorname{D}\left(n\right)\\\forall n \in \mathbb{N},\; \operatorname{E}\left(n + 1\right) = X \cdot \operatorname{D}\left(n\right) + (1 - X) \cdot \operatorname{E}\left(n\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.quasi` (`✓ std3`).

*Citation.* Roman Wituła; Damian Słota (2007). *Quasi-Fibonacci Numbers of Order 11*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf>.

*Commentary.*

System (3.12) on printed page 5 gives these five recurrence lines and the initial values A(0)=1 and B(0)=C(0)=D(0)=E(0)=0. The tuple quasi(n) contains the five polynomials in that order.

**Definition 1.2 (The polynomial A(n)).**

$$\forall n \in \mathbb{N},\; \operatorname{A}\left(n\right) = \operatorname{fst}\left(\operatorname{quasi}\left(n\right)\right)$$

*Formalization.* `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.A` (`✓ std3`).

*Citation.* Roman Wituła; Damian Słota (2007). *Quasi-Fibonacci Numbers of Order 11*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf>.

*Commentary.*

A(n) is the first component of quasi(n).

**Definition 1.3 (The polynomial B(n)).**

$$\forall n \in \mathbb{N},\; \operatorname{B}\left(n\right) = \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{quasi}\left(n\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.B` (`✓ std3`).

*Citation.* Roman Wituła; Damian Słota (2007). *Quasi-Fibonacci Numbers of Order 11*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf>.

*Commentary.*

B(n) is the first component after one move into the remaining product.

**Definition 1.4 (The polynomial C(n)).**

$$\forall n \in \mathbb{N},\; \operatorname{C}\left(n\right) = \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{snd}\left(\operatorname{quasi}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.C` (`✓ std3`).

*Citation.* Roman Wituła; Damian Słota (2007). *Quasi-Fibonacci Numbers of Order 11*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf>.

*Commentary.*

C(n) is the first component after two moves into the remaining product.

**Definition 1.5 (The polynomial D(n)).**

$$\forall n \in \mathbb{N},\; \operatorname{D}\left(n\right) = \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{snd}\left(\operatorname{snd}\left(\operatorname{quasi}\left(n\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.D` (`✓ std3`).

*Citation.* Roman Wituła; Damian Słota (2007). *Quasi-Fibonacci Numbers of Order 11*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf>.

*Commentary.*

D(n) is the first component after three moves into the remaining product.

**Definition 1.6 (The polynomial E(n)).**

$$\forall n \in \mathbb{N},\; \operatorname{E}\left(n\right) = \operatorname{snd}\left(\operatorname{snd}\left(\operatorname{snd}\left(\operatorname{snd}\left(\operatorname{quasi}\left(n\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.E` (`✓ std3`).

*Citation.* Roman Wituła; Damian Słota (2007). *Quasi-Fibonacci Numbers of Order 11*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf>.

*Commentary.*

E(n) is the final component of the right-associated product.

**Definition 1.7 (The page-19 degree problem).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (5 \le n) \Rightarrow ((\operatorname{deg}\left(\operatorname{A}\left(n\right)\right) = n) \land ((\operatorname{deg}\left(\operatorname{B}\left(n\right)\right) = n) \land ((\operatorname{deg}\left(\operatorname{C}\left(n\right)\right) = n) \land ((\operatorname{deg}\left(\operatorname{D}\left(n\right)\right) = n) \land (\operatorname{deg}\left(\operatorname{E}\left(n\right)\right) = n))))))$$

*Formalization.* `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.claim` (`✓ std3`).

*Citation.* Roman Wituła; Damian Słota (2007). *Quasi-Fibonacci Numbers of Order 11*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf>.

*Commentary.*

The Problem on printed page 19 asks verbatim: "Problem. Is it true that deg A_n(Δ) = deg B_n(Δ) = deg C_n(Δ) = deg D_n(Δ) = deg E_n(Δ) = n for every n = 5, 6, . . .?" Here deg is Polynomial.degree, so each equality also asserts that the corresponding polynomial is nonzero.

**Theorem 1.8 (All five degrees are full).**

$$\forall n \in \mathbb{N},\; (5 \le n) \Rightarrow ((\operatorname{deg}\left(\operatorname{A}\left(n\right)\right) = n) \land ((\operatorname{deg}\left(\operatorname{B}\left(n\right)\right) = n) \land ((\operatorname{deg}\left(\operatorname{C}\left(n\right)\right) = n) \land ((\operatorname{deg}\left(\operatorname{D}\left(n\right)\right) = n) \land (\operatorname{deg}\left(\operatorname{E}\left(n\right)\right) = n)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.result` (`✓ std3`). ∎

*Resolves.* `Problems/witula-slota-2007-quasi-fibonacci-order-eleven-degree` (proved) by `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"witula-slota-2007-quasi-fibonacci-order-eleven-degree","declaration_gid":"D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Roman Wituła; Damian Słota (2007). *Quasi-Fibonacci Numbers of Order 11*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf>.

*Commentary.*

The answer is affirmative. Each recurrence step raises degree by at most one. For the coefficient of X^n, apply alternating signs to the five coordinates. At n=5 the resulting vector is (1,9,1,4,1). Its coordinates remain positive and its last coordinate remains smaller than the sum of the first and third: the next vector is (2b+e,a+c-e,b+d+e,c,d+e), and the new difference between that sum and the last coordinate is 3b+e. Consequently every degree-n coefficient is nonzero for n at least five, and the upper degree bounds are equalities.

## References

- Truth anchor: `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.A`
- Truth anchor: `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.B`
- Truth anchor: `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.C`
- Truth anchor: `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.D`
- Truth anchor: `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.E`
- Truth anchor: `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.claim`
- Truth anchor: `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.quasi`
- Truth anchor: `D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.result`
