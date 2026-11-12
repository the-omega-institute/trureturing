# Pointwise integrality of the first dual Somos recurrence

## Abstract

The first dual Somos-4 orbit has integer shadows exactly at p=1, for each integer initial tuple.

DualNumber K is the square-zero algebra K + K epsilon, with epsilon squared zero. The first and second projections are the real and shadow coefficients. All sequence indices are natural and the four initial slots are indexed from zero. The source's product of two p-th powers equals the p-th power of their product in this commutative algebra. No positivity or nonvanishing assumption is added to the source exchange predicate.

**Definition 1.1 (The rational-dual exchange predicate).**

$$\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(4\right) \to \mathbb{Z},\; \forall A \in \mathbb{N} \to \operatorname{DualNumber}\left(\mathbb{Q}\right),\; \operatorname{IsOrbit}\left(p, q, c, A\right) \Leftrightarrow \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; A\left(i\right) = 1 + (c\left(i\right): \mathbb{Q}) \cdot epsilon\right) \land \left(\forall n \in \mathbb{N},\; A\left(n + 4\right) \cdot A\left(n\right) = \left(A\left(n + 1\right) \cdot A\left(n + 3\right)\right)^{p} + \left(1 + epsilon\right) \cdot A\left(n + 2\right)^{q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.IsOrbit` (`✓ std3`).

*Citation.* Valentin Ovsienko; Serge Tabachnikov (2017). *Dual numbers, weighted quivers, and extended Somos and Gale-Robinson sequences*. DOI: [10.1007/s10468-018-9779-3](https://doi.org/10.1007/s10468-018-9779-3). URL: <https://arxiv.org/abs/1705.01623v1>.

*Commentary.*

The first non-homogeneous recurrence in the source conjecture, with each arbitrary integer tuple retained separately. The source's initial-shadow indices b1 through b4 are normalized to the section's leading slots 0 through 3.

**Definition 1.2 (Coefficientwise inclusion into real duals).**

$$\forall x \in \operatorname{DualNumber}\left(\mathbb{Q}\right),\; \operatorname{fst}\left(\operatorname{realCast}\left(x\right)\right) = (\operatorname{fst}\left(x\right): \mathbb{R}) \land \operatorname{snd}\left(\operatorname{realCast}\left(x\right)\right) = (\operatorname{snd}\left(x\right): \mathbb{R})$$

*Formalization.* `D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.realCast` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Valentin Ovsienko; Serge Tabachnikov (2017). *Dual numbers, weighted quivers, and extended Somos and Gale-Robinson sequences*. DOI: [10.1007/s10468-018-9779-3](https://doi.org/10.1007/s10468-018-9779-3). URL: <https://arxiv.org/abs/1705.01623v1>.

*Commentary.*

This is a ring homomorphism. The result proves it is injective and that it preserves and reflects the existence of an integer shadow coefficient.

**Definition 1.3 (The real-dual source exchange predicate).**

$$\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(4\right) \to \mathbb{Z},\; \forall A \in \mathbb{N} \to \operatorname{DualNumber}\left(\mathbb{R}\right),\; \operatorname{IsRealOrbit}\left(p, q, c, A\right) \Leftrightarrow \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; A\left(i\right) = 1 + (c\left(i\right): \mathbb{R}) \cdot epsilon\right) \land \left(\forall n \in \mathbb{N},\; A\left(n + 4\right) \cdot A\left(n\right) = \left(A\left(n + 1\right) \cdot A\left(n + 3\right)\right)^{p} + \left(1 + epsilon\right) \cdot A\left(n + 2\right)^{q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.IsRealOrbit` (`✓ std3`).

*Citation.* Valentin Ovsienko; Serge Tabachnikov (2017). *Dual numbers, weighted quivers, and extended Somos and Gale-Robinson sequences*. DOI: [10.1007/s10468-018-9779-3](https://doi.org/10.1007/s10468-018-9779-3). URL: <https://arxiv.org/abs/1705.01623v1>.

*Commentary.*

The same recurrence over real dual numbers, as in the paper. The final theorem identifies every such orbit with the embedded rational orbit.

**Theorem 1.4 (The full integrality equivalence and faithful source realization).**

$$\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(4\right) \to \mathbb{Z},\; \left(0 < p \land 0 < q\right) \Rightarrow \left(\exists A \in \mathbb{N} \to \operatorname{DualNumber}\left(\mathbb{Q}\right),\; \operatorname{IsOrbit}\left(p, q, c, A\right) \land \left(\left(\forall X \in \mathbb{N} \to \operatorname{DualNumber}\left(\mathbb{Q}\right),\; \operatorname{IsOrbit}\left(p, q, c, X\right) \Rightarrow X = A\right) \land \left(\left(\forall n \in \mathbb{N},\; 0 < \operatorname{fst}\left(A\left(n\right)\right)\right) \land \left(\left(\left(\forall n \in \mathbb{N},\; \exists b \in \mathbb{Z},\; (b: \mathbb{Q}) = \operatorname{snd}\left(A\left(n\right)\right)\right) \Leftrightarrow p = 1\right) \land \left(\left(\forall B \in \mathbb{N} \to \operatorname{DualNumber}\left(\mathbb{R}\right),\; \operatorname{IsRealOrbit}\left(p, q, c, B\right) \Leftrightarrow B = (n: \mathbb{N} \mapsto \operatorname{realCast}\left(A\left(n\right)\right))\right) \land \left(\left(\left(\forall n \in \mathbb{N},\; \exists b \in \mathbb{Z},\; (b: \mathbb{R}) = \operatorname{snd}\left(\operatorname{realCast}\left(A\left(n\right)\right)\right)\right) \Leftrightarrow p = 1\right) \land \left(\forall x \in \operatorname{DualNumber}\left(\mathbb{Q}\right),\; \forall y \in \operatorname{DualNumber}\left(\mathbb{Q}\right),\; \operatorname{realCast}\left(x\right) = \operatorname{realCast}\left(y\right) \Rightarrow x = y\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Valentin Ovsienko; Serge Tabachnikov (2017). *Dual numbers, weighted quivers, and extended Somos and Gale-Robinson sequences*. DOI: [10.1007/s10468-018-9779-3](https://doi.org/10.1007/s10468-018-9779-3). URL: <https://arxiv.org/abs/1705.01623v1>.

*Commentary.*

For every positive p and q and each integer tuple c there exists a unique rational-dual orbit with the prescribed initial data; its real coefficients are positive. All of its shadow coefficients are integers if and only if p=1. The displayed conjunction also gives the unique real-dual realization, the same shadow equivalence there, and injectivity of the coefficientwise embedding. The p=1 sufficient direction is published prior work. The formal proof uses the following elementary divisibility route.

For eight consecutive integer duals A,B,C,D,E,F,G,H, reduce modulo E. Coprimality of the real parts of B,C,D with that of E makes B,C,D units by a lifted Bezout identity. The four exchange equations make F,G,H units as well. Writing t=1+v epsilon and N=(FH)^p+tG^q, lawful unit calculations give t^(2p)N=(HF)^p(t^(2p)-t^2). The difference is (2p-2)v epsilon. Both prefactors are units, so E divides N exactly when the real part of E divides (2p-2)v. Coefficient comparison proves this last equivalence without cancelling epsilon. Only natural powers occur, so q=1 is included.

With zero obstruction, strong induction constructs the next integer dual before propagating pairwise coprimality of each four-term real window. Its v=0 instance proves real-part integrality for arbitrary exponents; its p=1 instance proves the required shadows. Conversely, an entirely integer v=1 orbit would force 2^p+1 to divide 2p-2 at the window with divisor A5. For p at least two the latter is positive and strictly smaller. This contradiction is independent of all four initial shadows. Neither the second deformation nor a separate growth assertion is part of this theorem. No global novelty or priority is asserted.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.IsOrbit`
- Truth anchor: `D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.IsRealOrbit`
- Truth anchor: `D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.realCast`
- Truth anchor: `D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.result`
