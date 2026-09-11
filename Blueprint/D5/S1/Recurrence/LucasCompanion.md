# Lucas Companion Traces and Dyadic Zeros

## Abstract

Companion traces, equality of periods when two is a unit, and the dyadic positive-zero criterion; Questions 5.3 and 5.4 remain outside this module's scope.

The companion sequence V is realized as trace(M^n), where M is the invertible companion matrix underlying U. Integer indices come from zpow. This module proves that the least period of V equals the matrix order when 2 is invertible and V has a zero. For even integer p and odd integer q it also proves the exact valuations v₂(V(2j)) = 1 and v₂(V(2j+1)) = v₂(p), and, for v ≥ 2, the existence of a positive zero modulo 2^v exactly when 2^v divides p, with index 1 as witness. These arithmetic assertions concern natural indices and include p = 0, with mathlib's v₂(0) = 0 convention.

This does not settle Questions 5.3 or 5.4 of Fiebig, Mbirika and Spilker. They ask whether the periods of U and V agree when p and the modulus are both even. The module supplies the base layer and one of the two ingredients; multiplicativity of the period over a coprime factorization and the assembly are not here. The paper's exceptional case is q = 1, modulus 4, and 4 dividing p. The zero criterion explains where that condition comes from, but the exception itself is a statement about periods and is out of scope for this module.

Every theorem below is proved in the repository. The paper supplies the vocabulary of the companion recurrence and entry point: the entry point is the least positive zero index, if one exists. The two recurrence nodes cite that vocabulary and those initial values and recurrence equations. Their extensions to the full displayed parameter domains are proved here. The trace definitions, period constructions, and remaining results are repository work; literature attribution does not pass along their dependencies.

In the displays U(p,q,n) is LucasEvenDescent.lucasU, V(p,q,n) is lucasV, and W(p,q,n) is lucasVInt. M(p,q) is LucasEvenDescent.companion, while A(p,q,n) abbreviates val(M(p,q)^n), the private powerMatrix definition unfolded. Mat2(R) means Matrix (Fin 2) (Fin 2) R, with labels 0 and 1; Units(R) means Rˣ and val is its coercion. Cast denotes the canonical cast. piM and piV denote matrixPeriod and companionPeriod. Per(p,q,k) means that V(p,q,n+k) = V(p,q,n) for every integer n. S_R is the shift on functions from the integers to R, defined by S_R(f)(n) = f(n+1). Its minimalPeriod at a function is zero if there is no positive return time; orderOf uses the analogous zero convention for infinite order. v₂(x) abbreviates padicValInt 2 x. Type* allows any universe, and bracketed binders retain the Lean typeclass hypotheses.

**Definition 1.1 (The bilateral companion trace).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\forall n: \mathbb{Z},\\\operatorname{V}\left(p, q, n\right) = \operatorname{trace}\left(\operatorname{val}\left(\operatorname{M}\left(p, q\right)^{n}\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/LucasCompanion.lucasV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Taking the trace of a power of the companion unit defines the sequence at every integer index over any commutative ring.

**Theorem 1.2 (The shape of every integer companion power).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\forall n: \mathbb{Z},\\\operatorname{A}\left(p, q, n\right) = \begin{bmatrix}\operatorname{U}\left(p, q, n + 1\right)&-\operatorname{val}\left(q\right) \cdot \operatorname{U}\left(p, q, n\right)\\\operatorname{U}\left(p, q, n\right)&\operatorname{U}\left(p, q, n + 1\right) - p \cdot \operatorname{U}\left(p, q, n\right)\end{bmatrix}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.companion_power_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Commutation with M determines the off-diagonal and lower-right entries. Multiplication by M identifies the upper-left entry with U(n+1). The displayed A is the unfolded private definition.

**Theorem 1.3 (The determinant at integer powers).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\forall n: \mathbb{Z},\\\operatorname{det}\left(\operatorname{A}\left(p, q, n\right)\right) = \operatorname{val}\left(q^{n}\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.companion_power_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant homomorphism sends M to q and respects integer powers of units, including negative powers.

**Theorem 1.4 (The trace expressed through U).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\forall n: \mathbb{Z},\\\operatorname{V}\left(p, q, n\right) = 2 \cdot \operatorname{U}\left(p, q, n + 1\right) - p \cdot \operatorname{U}\left(p, q, n\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasV_eq_lucasU` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Add the diagonal entries in the power-shape identity. This is the bridge used to transfer the frozen recurrence to the trace.

**Theorem 1.5 (The companion initial values and bilateral recurrence).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\operatorname{V}\left(p, q, 0\right) = 2 \land \operatorname{V}\left(p, q, 1\right) = p \land\\\forall n: \mathbb{Z}, \operatorname{V}\left(p, q, n + 2\right) = p \cdot \operatorname{V}\left(p, q, n + 1\right) - \operatorname{val}\left(q\right) \cdot \operatorname{V}\left(p, q, n\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasV_recurrence` (`✓ std3`). ∎

*Citation.* Morgan Fiebig, aBa Mbirika, Jürgen Spilker (2025). *Period patterns, entry points, and orders in the Lucas sequences: theory and applications*. URL: <https://arxiv.org/abs/2408.14632v2>.

*Commentary.*

The cited paper defines the companion sequence by V(0)=2, V(1)=p and this recurrence. Here its trace realization is proved to satisfy those equations over every commutative ring with unit q, at all integer indices. That general algebraic extension is established here, without the paper's standing parameter restrictions. The paper's entry point, when it exists, is its least positive zero index.

**Theorem 1.6 (The companion quadratic determinant identity).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\forall n: \mathbb{Z},\\\operatorname{V}\left(p, q, n + 1\right)^{2} - p \cdot \operatorname{V}\left(p, q, n\right) \cdot \operatorname{V}\left(p, q, n + 1\right) + \operatorname{val}\left(q\right) \cdot \operatorname{V}\left(p, q, n\right)^{2} = -\operatorname{val}\left(q^{n}\right) \cdot (p^{2} - 4 \cdot \operatorname{val}\left(q\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasV_determinant_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitute the bridge to U into the companion-power determinant identity and use the recurrence. The right side retains the unit power q^n and the discriminant p^2-4q.

**Theorem 1.7 (A zero trace gives a scalar double power).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\forall r: \mathbb{Z},\\\operatorname{V}\left(p, q, r\right) = 0 \Rightarrow \operatorname{A}\left(p, q, 2 \cdot r\right) = \operatorname{smul}\left(-\operatorname{val}\left(q^{r}\right), 1: \operatorname{Mat2}\left(R\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.companion_double_of_lucasV_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the two-by-two Cayley--Hamilton identity to A(r). The zero trace removes its linear term, leaving the negative determinant times the identity matrix. smul denotes scalar multiplication.

**Definition 1.8 (The order of the companion unit).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\operatorname{piM}\left(p, q\right) = \operatorname{orderOf}\left(\operatorname{M}\left(p, q\right)\right) \in \mathbb{N}\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/LucasCompanion.matrixPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This noncomputable repository definition is the order of M in the matrix unit group. It may be zero without finiteness.

**Theorem 1.9 (Identity powers are period multiples).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\forall k: \mathbb{Z},\\\operatorname{M}\left(p, q\right)^{k} = 1 \iff \operatorname{Cast}\left(\operatorname{piM}\left(p, q\right), \mathbb{Z}\right) \mid k\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.companion_zpow_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer-power order theorem characterizes every identity power, with no finite-ring assumption.

**Theorem 1.10 (Positive matrix period over a finite ring).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\{}[\operatorname{Finite}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\0 < \operatorname{piM}\left(p, q\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.matrixPeriod_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finiteness makes the companion unit have positive order.

**Theorem 1.11 (Positive matrix period modulo a positive modulus).**

$$\begin{aligned}\forall m: \mathbb{N},\\0 < m \Rightarrow\\\forall p: \operatorname{ZMod}\left(m\right), \forall q: \operatorname{Units}\left(\operatorname{ZMod}\left(m\right)\right),\\0 < \operatorname{piM}\left(p, q\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.matrixPeriod_zmod_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive-modulus hypothesis supplies NeZero m and hence the finite-ring instance for ZMod m.

**Theorem 1.12 (Matrix periodicity passes to the trace).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\operatorname{Per}\left(p, q, \operatorname{Cast}\left(\operatorname{piM}\left(p, q\right), \mathbb{Z}\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasV_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The companion power at its order is the identity, so translating any integer index by that order leaves the trace unchanged.

**Definition 1.13 (The minimal return time under the shift).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\operatorname{piV}\left(p, q\right) = \operatorname{minimalPeriod}\left(S_{R}, \operatorname{V}(p,q,\cdot)\right) \in \mathbb{N}\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/LucasCompanion.companionPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply Function.minimalPeriod to the shift on the entire bilateral sequence. This is a repository construction; a zero value is allowed when the sequence has no positive period.

**Theorem 1.14 (Natural periods are minimal-period multiples).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\forall k: \mathbb{N}, \operatorname{piV}\left(p, q\right) \mid k \iff \operatorname{Per}\left(p, q, \operatorname{Cast}\left(k, \mathbb{Z}\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.companionPeriod_dvd_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterating the shift k times translates by k. The minimal-period divisibility theorem therefore applies to all natural translation periods, including zero.

**Theorem 1.15 (The companion period divides the matrix period).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\operatorname{piV}\left(p, q\right) \mid \operatorname{piM}\left(p, q\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.companionPeriod_dvd_matrixPeriod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combine trace periodicity with the divisibility characterization.

**Theorem 1.16 (The least positive companion period over a finite ring).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\{}[\operatorname{Finite}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\0 < \operatorname{piV}\left(p, q\right) \land \operatorname{Per}\left(p, q, \operatorname{Cast}\left(\operatorname{piV}\left(p, q\right), \mathbb{Z}\right)\right) \land (\forall k: \mathbb{N}, 0 < k \Rightarrow \operatorname{Per}\left(p, q, \operatorname{Cast}\left(k, \mathbb{Z}\right)\right) \Rightarrow \operatorname{piV}\left(p, q\right) \leq k)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.companionPeriod_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A divisor of the positive matrix period is positive. The same characterization proves periodicity at piV and its minimality among positive natural periods; all three conclusions are retained.

**Theorem 1.17 (Equality of periods from a zero and invertible two).**

$$\begin{aligned}\forall R: Type*, [\operatorname{CommRing}\left(R\right)],\\\forall p: R, \forall q: \operatorname{Units}\left(R\right),\\\operatorname{IsUnit}\left(2: R\right) \Rightarrow (\exists r: \mathbb{Z}, \operatorname{V}\left(p, q, r\right) = 0) \Rightarrow \operatorname{piV}\left(p, q\right) = \operatorname{piM}\left(p, q\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.companionPeriod_eq_matrixPeriod_of_lucasV_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This repository result strengthens the published Corollary 3.13, which assumes p odd, or p even with the modulus odd. Here the only additional hypotheses are that 2 is a unit and V has an integer zero: there is no parity hypothesis, no restriction on q beyond its unit type, and no finiteness assumption. Commutation and translation at the zero give a two-by-two linear system; its determinant is the unit -q^r. Cancellation forces the companion power at piV to be the identity. This direct proof removes both external dependencies of the published argument: Ballot's theorem and McDaniel's 1991 gcd theorem.

**Definition 1.18 (Natural traces for arbitrary integer parameters).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \mathbb{Z},\\\forall n: \mathbb{N},\\\operatorname{W}\left(p, q, n\right) = \operatorname{trace}\left((\begin{bmatrix}p&-q\\1&0\end{bmatrix}: \operatorname{Mat2}\left(\mathbb{Z}\right))^{n}\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/LucasCompanion.lucasVInt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Natural matrix powers require no inverse. W therefore allows every integer q, including nonunits, while retaining integral values.

**Theorem 1.19 (Agreement at natural indices for unit q).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \operatorname{Units}\left(\mathbb{Z}\right),\\\forall n: \mathbb{N},\\\operatorname{W}\left(p, \operatorname{val}\left(q\right), n\right) = \operatorname{V}\left(p, q, \operatorname{Cast}\left(n, \mathbb{Z}\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasVInt_eq_lucasV` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unit's natural power agrees with its integer power at the cast index. Unfold both traces and the companion definition.

**Theorem 1.20 (The integral companion recurrence without a unit restriction).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \mathbb{Z},\\{}\\\operatorname{W}\left(p, q, 0\right) = 2 \land \operatorname{W}\left(p, q, 1\right) = p \land\\\forall n: \mathbb{N}, \operatorname{W}\left(p, q, n + 2\right) = p \cdot \operatorname{W}\left(p, q, n + 1\right) - q \cdot \operatorname{W}\left(p, q, n\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasVInt_recurrence` (`✓ std3`). ∎

*Citation.* Morgan Fiebig, aBa Mbirika, Jürgen Spilker (2025). *Period patterns, entry points, and orders in the Lucas sequences: theory and applications*. URL: <https://arxiv.org/abs/2408.14632v2>.

*Commentary.*

The paper's companion sequence has these initial values and recurrence. The repository proves them for every integer p and q by multiplying the matrix identity M^2=pM-qI by M^n and taking traces. The unrestricted parameter extension and its proof are repository work.

**Theorem 1.21 (Simultaneous dyadic congruences for W).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \mathbb{Z},\\\operatorname{Even}\left(p\right) \Rightarrow\\\forall j: \mathbb{N},\\\operatorname{let} t = \operatorname{padicValInt}\left(2, p\right) \operatorname{in}\\\operatorname{W}\left(p, q, 2 \cdot j\right) \equiv 2 \cdot (-q)^{j} (\operatorname{mod} (2: \mathbb{Z})^{t + 1}) \land\\\operatorname{W}\left(p, q, 2 \cdot j + 1\right) \equiv (2 \cdot \operatorname{Cast}\left(j, \mathbb{Z}\right) + 1) \cdot p \cdot (-q)^{j} (\operatorname{mod} (2: \mathbb{Z})^{t + 1})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasVInt_two_adic_congruences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A paired recurrence induction works whenever the modulus divides p^2. Evenness of p supplies that divisibility for 2^(v₂(p)+1). No oddness or unit assumption on q is required for these congruences.

**Theorem 1.22 (Even terms of W have valuation one).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \mathbb{Z},\\\operatorname{Even}\left(p\right) \Rightarrow \operatorname{Odd}\left(q\right) \Rightarrow\\\forall j: \mathbb{N},\\\operatorname{padicValInt}\left(2, \operatorname{W}\left(p, q, 2 \cdot j\right)\right) = 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasVInt_even_two_adic_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For even p and odd q the paired factorization writes W(2j) as 2 times an odd integer. Its valuation is exactly one, including at j=0 and p=0.

**Theorem 1.23 (Odd terms of W have the valuation of p).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \mathbb{Z},\\\operatorname{Even}\left(p\right) \Rightarrow \operatorname{Odd}\left(q\right) \Rightarrow\\\forall j: \mathbb{N},\\\operatorname{padicValInt}\left(2, \operatorname{W}\left(p, q, 2 \cdot j + 1\right)\right) = \operatorname{padicValInt}\left(2, p\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasVInt_odd_two_adic_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The paired factorization writes W(2j+1) as p times an odd integer. The proof handles p=0 separately, retaining mathlib's zero convention for padicValInt.

**Theorem 1.24 (The exact dyadic positive-zero criterion).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \mathbb{Z},\\\operatorname{Even}\left(p\right) \Rightarrow \operatorname{Odd}\left(q\right) \Rightarrow\\\forall v: \mathbb{N}, 2 \leq v \Rightarrow\\(\exists r: \mathbb{N}, 0 < r \land (2: \mathbb{Z})^{v} \mid \operatorname{W}\left(p, q, r\right)) \iff (2: \mathbb{Z})^{v} \mid p\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasVInt_exists_positive_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This repository result is sharper than the paper's remark that the exceptional case needs 4 dividing p. For every v at least 2, even-index terms cannot vanish modulo 2^v because their valuation is one; an odd-index zero forces 2^v to divide p, including the separate p=0 case. Conversely W(1)=p is a positive-index witness. This characterizes zeros, not the period exception or the unresolved period assembly.

**Theorem 1.25 (Index one witnesses every positive zero for W).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \mathbb{Z},\\\operatorname{Even}\left(p\right) \Rightarrow \operatorname{Odd}\left(q\right) \Rightarrow\\\forall v: \mathbb{N}, 2 \leq v \Rightarrow\\(\exists r: \mathbb{N}, 0 < r \land (2: \mathbb{Z})^{v} \mid \operatorname{W}\left(p, q, r\right)) \iff (2: \mathbb{Z})^{v} \mid \operatorname{W}\left(p, q, 1\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasVInt_positive_zero_iff_index_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewrite the divisibility criterion using W(1)=p. The result retains even p, odd q, and v at least 2.

**Theorem 1.26 (Dyadic congruences for the bilateral sequence at natural indices).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \operatorname{Units}\left(\mathbb{Z}\right),\\\operatorname{Even}\left(p\right) \Rightarrow\\\forall j: \mathbb{N},\\\operatorname{let} t = \operatorname{padicValInt}\left(2, p\right) \operatorname{in}\\\operatorname{V}\left(p, q, \operatorname{Cast}\left(2 \cdot j, \mathbb{Z}\right)\right) \equiv 2 \cdot (-\operatorname{val}\left(q\right))^{j} (\operatorname{mod} (2: \mathbb{Z})^{t + 1}) \land\\\operatorname{V}\left(p, q, \operatorname{Cast}\left(2 \cdot j + 1, \mathbb{Z}\right)\right) \equiv (2 \cdot \operatorname{Cast}\left(j, \mathbb{Z}\right) + 1) \cdot p \cdot (-\operatorname{val}\left(q\right))^{j} (\operatorname{mod} (2: \mathbb{Z})^{t + 1})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasV_two_adic_congruences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the integral congruences through the trace bridge. Here q is an integer unit and j is natural; the displayed casts distinguish the bilateral indices from natural exponents.

**Theorem 1.27 (Even natural indices of V have valuation one).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \operatorname{Units}\left(\mathbb{Z}\right),\\\operatorname{Even}\left(p\right) \Rightarrow\\\forall j: \mathbb{N},\\\operatorname{padicValInt}\left(2, \operatorname{V}\left(p, q, \operatorname{Cast}\left(2 \cdot j, \mathbb{Z}\right)\right)\right) = 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasV_even_two_adic_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer unit is odd. Apply the result for W and the agreement of the two traces at natural indices.

**Theorem 1.28 (Odd natural indices of V have the valuation of p).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \operatorname{Units}\left(\mathbb{Z}\right),\\\operatorname{Even}\left(p\right) \Rightarrow\\\forall j: \mathbb{N},\\\operatorname{padicValInt}\left(2, \operatorname{V}\left(p, q, \operatorname{Cast}\left(2 \cdot j + 1, \mathbb{Z}\right)\right)\right) = \operatorname{padicValInt}\left(2, p\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasV_odd_two_adic_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd-index integral valuation transfers to V for integer unit q, still allowing p=0 with v₂(0)=0.

**Theorem 1.29 (The dyadic positive-zero criterion for V).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \operatorname{Units}\left(\mathbb{Z}\right),\\\operatorname{Even}\left(p\right) \Rightarrow\\\forall v: \mathbb{N}, 2 \leq v \Rightarrow\\(\exists r: \mathbb{N}, 0 < r \land (2: \mathbb{Z})^{v} \mid \operatorname{V}\left(p, q, \operatorname{Cast}\left(r, \mathbb{Z}\right)\right)) \iff (2: \mathbb{Z})^{v} \mid p\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasV_exists_positive_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specialize the integral criterion to unit q and cast each natural zero index into the bilateral index type.

**Theorem 1.30 (Index one witnesses every positive zero for V).**

$$\begin{aligned}\forall p: \mathbb{Z}, \forall q: \operatorname{Units}\left(\mathbb{Z}\right),\\\operatorname{Even}\left(p\right) \Rightarrow\\\forall v: \mathbb{N}, 2 \leq v \Rightarrow\\(\exists r: \mathbb{N}, 0 < r \land (2: \mathbb{Z})^{v} \mid \operatorname{V}\left(p, q, \operatorname{Cast}\left(r, \mathbb{Z}\right)\right)) \iff (2: \mathbb{Z})^{v} \mid \operatorname{V}\left(p, q, \operatorname{Cast}\left(1, \mathbb{Z}\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasCompanion.lucasV_positive_zero_iff_index_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The criterion and V(1)=p identify existence of a positive natural zero with vanishing at index one, for v at least 2.

## References

- Truth anchor: `D5/S1/Recurrence/LucasCompanion.companionPeriod`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.companionPeriod_dvd_iff`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.companionPeriod_dvd_matrixPeriod`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.companionPeriod_eq_matrixPeriod_of_lucasV_zero`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.companionPeriod_spec`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.companion_double_of_lucasV_zero`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.companion_power_det`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.companion_power_shape`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.companion_zpow_eq_one_iff`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasVInt`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasVInt_eq_lucasV`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasVInt_even_two_adic_valuation`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasVInt_exists_positive_zero_iff`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasVInt_odd_two_adic_valuation`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasVInt_positive_zero_iff_index_one`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasVInt_recurrence`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasVInt_two_adic_congruences`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV_determinant_identity`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV_eq_lucasU`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV_even_two_adic_valuation`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV_exists_positive_zero_iff`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV_odd_two_adic_valuation`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV_periodic`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV_positive_zero_iff_index_one`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV_recurrence`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.lucasV_two_adic_congruences`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.matrixPeriod`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.matrixPeriod_pos`
- Truth anchor: `D5/S1/Recurrence/LucasCompanion.matrixPeriod_zmod_pos`
- Dependency: [D5/S1/Recurrence/LucasEvenDescent](LucasEvenDescent.md)
