# Solovay–Kitaev error and level estimates

## Abstract

The scalar three-halves error recurrence and fivefold length growth yield the exact logarithmic exponent log(5)/log(3/2).

These scalar and logarithmic proofs are Apache-2.0 reuse from Zayn Blore's CSD SolovayKitaevStep and SolovayKitaevCount at commit 9b2d2c17e926ae13795119c5f2f62e85ea240c2d. Their exact original file and declaration references appear in the Lean source. The full license is docs/reports/qmutualinfo/csd-lean4-LICENSE.txt. The scalar sequence is skErr(e,0)=e and skErr(e,n+1)=33*skErr(e,n)^(3/2). They bound scalar sequences and level counts; the ordinary-word theorem separately supplies one actual list satisfying error and length together.

**Theorem 1.1 (Closed scalar error bound).**

$$\forall C \in \operatorname{Real}\left(\right),\; \forall e \in \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right),\; \left(0 < C \land \left(\left(\forall j \in \operatorname{Nat}\left(\right),\; 0 \le e\left(j\right)\right) \land \left(\forall j \in \operatorname{Nat}\left(\right),\; e\left(j + 1\right) \le C \cdot e\left(j\right)^{\frac{3}{2}}\right)\right)\right) \Rightarrow \left(\forall n \in \operatorname{Nat}\left(\right),\; C^{2} \cdot e\left(n\right) \le \left(C^{2} \cdot e\left(0\right)\right)^{\frac{3}{2}^{n}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/SolovayKitaevRate.skError_le_rpow` (`✓ std3`). ∎

*Citation.* Christopher M. Dawson; Michael A. Nielsen (2006). *The Solovay-Kitaev algorithm*. URL: <https://arxiv.org/abs/quant-ph/0505030>.

*Commentary.*

For a nonnegative error sequence with e(n+1)<=C*e(n)^(3/2), induction gives double exponential decay after multiplication by C^2. C is any positive real constant.

**Theorem 1.2 (The sufficient three-halves step).**

$$\forall epsilon \in \operatorname{Real}\left(\right),\; \left(0 \le epsilon \land \operatorname{sqrt}\left(epsilon\right) \le \frac{1}{2}\right) \Rightarrow 4 \cdot \left(\operatorname{sqrt}\left(2\right) \cdot \operatorname{sqrt}\left(epsilon\right) + epsilon\right) \cdot epsilon \cdot \left(1 + \operatorname{sqrt}\left(2\right) \cdot \operatorname{sqrt}\left(epsilon\right) + epsilon\right) \le 33 \cdot epsilon^{\frac{3}{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/SolovayKitaevRate.step_bound` (`✓ std3`). ∎

*Citation.* Christopher M. Dawson; Michael A. Nielsen (2006). *The Solovay-Kitaev algorithm*. URL: <https://arxiv.org/abs/quant-ph/0505030>.

*Commentary.*

At a=sqrt(2)*sqrt(epsilon)+epsilon and delta=epsilon, the commutator stability expression is at most 33*epsilon^(3/2) whenever sqrt(epsilon)<=1/2.

**Theorem 1.3 (The chosen level reaches the error).**

$$\forall b \in \operatorname{Real}\left(\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; \left(0 < b \land \left(b < 1 \land \left(0 < epsilon \land epsilon \le b\right)\right)\right) \Rightarrow b^{\frac{3}{2}^{\operatorname{skLevel}\left(b, epsilon\right)}} \le epsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/SolovayKitaevRate.skLevel_rpow_le` (`✓ std3`). ∎

*Citation.* Christopher M. Dawson; Michael A. Nielsen (2006). *The Solovay-Kitaev algorithm*. URL: <https://arxiv.org/abs/quant-ph/0505030>.

*Commentary.*

For 0<epsilon<=b<1, skLevel(b,epsilon)=ceil(log(log(epsilon)/log(b))/log(3/2)). At this level the closed error is at most epsilon.

**Theorem 1.4 (Fivefold growth is polylogarithmic).**

$$\forall b \in \operatorname{Real}\left(\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; \left(0 < b \land \left(b < 1 \land \left(0 < epsilon \land epsilon \le b\right)\right)\right) \Rightarrow 5^{\operatorname{skLevel}\left(b, epsilon\right)} \le 5 \cdot \frac{\operatorname{log}\left(epsilon\right)}{\operatorname{log}\left(b\right)}^{\frac{\operatorname{log}\left(5\right)}{\operatorname{log}\left(\frac{3}{2}\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/SolovayKitaevRate.five_pow_skLevel_le` (`✓ std3`). ∎

*Citation.* Christopher M. Dawson; Michael A. Nielsen (2006). *The Solovay-Kitaev algorithm*. URL: <https://arxiv.org/abs/quant-ph/0505030>.

*Commentary.*

Rounding the level upward costs a factor of at most five. The exponent is exactly log(5)/log(3/2); this scalar estimate asserts no word-length bound without a paired word construction.

## References

- Truth anchor: `D5/S3/Quantum/Approximate/SolovayKitaevRate.five_pow_skLevel_le`
- Truth anchor: `D5/S3/Quantum/Approximate/SolovayKitaevRate.skError_le_rpow`
- Truth anchor: `D5/S3/Quantum/Approximate/SolovayKitaevRate.skLevel_rpow_le`
- Truth anchor: `D5/S3/Quantum/Approximate/SolovayKitaevRate.step_bound`
