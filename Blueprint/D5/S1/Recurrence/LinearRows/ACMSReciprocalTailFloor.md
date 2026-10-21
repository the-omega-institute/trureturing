# Reciprocal Tails of Generalized Fibonacci Numbers

## Abstract

Generalized Fibonacci reciprocal tails have the conjectured integer floor.

Amdeberhan, Chen, Moll and Sagan's Conjecture 4.6 has two clauses. The theorem here proves its first clause, including convergence of the tail. The clause concerning squared reciprocals is not asserted here.

**Definition 1.1 (The generalized Fibonacci sequence).**

$$\forall s: \mathbb{Z}, \forall t: \mathbb{Z}, (\operatorname{U}\left(s, t, 0\right) = 0) \land ((\operatorname{U}\left(s, t, 1\right) = 1) \land (\forall n: \mathbb{N}, \operatorname{U}\left(s, t, n + 2\right) = s \cdot \operatorname{U}\left(s, t, n + 1\right) + t \cdot \operatorname{U}\left(s, t, n\right)))$$

*Formalization.* `D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.U` (`✓ std3`).

*Citation.* Tewodros Amdeberhan, Xi Chen, Victor H. Moll, Bruce E. Sagan (2014). *Generalized Fibonacci polynomials and Fibonomial coefficients*. DOI: [10.1007/s00026-014-0242-9](https://doi.org/10.1007/s00026-014-0242-9). URL: <https://arxiv.org/abs/1306.6511v2>.

*Commentary.*

Section 1, p. 2: "Throughout this work, P will stand for the positive integers." "{0}_{s,t} = 0, {1}_{s,t} = 1 and, for n ≥ 2, {n}_{s,t} = s{n − 1}_{s,t} + t{n − 2}_{s,t}." U uses integer coefficients s and t and natural indices. The three equations display all cases of its recursive definition.

**Definition 1.2 (Conjecture 4.6, first clause).**

$$claim \iff (\forall s: \mathbb{Z}, \forall t: \mathbb{Z}, (1 \le t) \implies ((t < s) \implies (((s, -t) \ne (2, -1)) \implies (\forall n: \mathbb{N}, \forall r: \mathbb{N}, (1 \le n) \implies ((1 \le r) \implies ((\operatorname{Summable}\left((k: \mathbb{N} \mapsto \frac{(1: \mathbb{R})}{(\operatorname{U}\left(s, -t, r \cdot (n + k)\right): \mathbb{R})})\right)) \land (\left\lfloor(\sum'_{k: \mathbb{N}} \frac{(1: \mathbb{R})}{(\operatorname{U}\left(s, -t, r \cdot (n + k)\right): \mathbb{R})})^{-1}\right\rfloor = \operatorname{U}\left(s, -t, r \cdot n\right) - \operatorname{U}\left(s, -t, r \cdot (\operatorname{Nat}.\operatorname{sub}\left(n, 1\right))\right) - 1)))))))$$

*Formalization.* `D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.claim` (`✓ std3`).

*Citation.* Tewodros Amdeberhan, Xi Chen, Victor H. Moll, Bruce E. Sagan (2014). *Generalized Fibonacci polynomials and Fibonomial coefficients*. DOI: [10.1007/s00026-014-0242-9](https://doi.org/10.1007/s00026-014-0242-9). URL: <https://arxiv.org/abs/1306.6511v2>.

*Commentary.*

Conjecture 4.6, p. 13: "If s > t ≥ 1 with (s, −t) ≠ (2, −1) and n, r ∈ P then ⌊(∑_{k=n}^∞ 1/{rk}_{s,−t})^{−1}⌋ = {rn}_{s,−t} − {r(n − 1)}_{s,−t} − 1." The index k in the displayed infinite sum starts at zero, so the source index is n+k. Summable records convergence explicitly. Each denominator is cast from the integer U value to the reals; the floor and right side are integers. Nat.sub is subtraction in the natural indices.

**Theorem 1.3 (The reciprocal-tail floor identity).**

$$\forall s: \mathbb{Z}, \forall t: \mathbb{Z}, (1 \le t) \implies ((t < s) \implies (((s, -t) \ne (2, -1)) \implies (\forall n: \mathbb{N}, \forall r: \mathbb{N}, (1 \le n) \implies ((1 \le r) \implies ((\operatorname{Summable}\left((k: \mathbb{N} \mapsto \frac{(1: \mathbb{R})}{(\operatorname{U}\left(s, -t, r \cdot (n + k)\right): \mathbb{R})})\right)) \land (\left\lfloor(\sum'_{k: \mathbb{N}} \frac{(1: \mathbb{R})}{(\operatorname{U}\left(s, -t, r \cdot (n + k)\right): \mathbb{R})})^{-1}\right\rfloor = \operatorname{U}\left(s, -t, r \cdot n\right) - \operatorname{U}\left(s, -t, r \cdot (\operatorname{Nat}.\operatorname{sub}\left(n, 1\right))\right) - 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tewodros Amdeberhan, Xi Chen, Victor H. Moll, Bruce E. Sagan (2014). *Generalized Fibonacci polynomials and Fibonomial coefficients*. DOI: [10.1007/s00026-014-0242-9](https://doi.org/10.1007/s00026-014-0242-9). URL: <https://arxiv.org/abs/1306.6511v2>.

*Commentary.*

The companion matrix of U at stride r yields a real recurrence a(k+2)=P a(k+1)−Q a(k), with Q=t^r and a(1)=c=U(s,−t,r). Its parameters satisfy Q≥1, P≥Q+1, P≥3 and P≥c+1. Induction bounds the successive difference fwdDiff(1,a,k) below by c(k+1). Cassini's identity gives a(k+1)^2−a(k)a(k+2)=c^2 Q^k, and a second induction bounds this defect plus one by a(k+2)−a(k). Dividing by positive denominators places each reciprocal between two telescoping differences. Their sums put the reciprocal tail in the interval whose integer floor is the stated difference minus one. The endpoint with difference one uses positivity and the strict lower tail estimate.

## References

- Truth anchor: `D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.U`
- Truth anchor: `D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.claim`
- Truth anchor: `D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.result`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
