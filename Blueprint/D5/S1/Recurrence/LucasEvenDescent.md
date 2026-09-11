# Lucas Descent for Even Moduli

## Abstract

A machine-checked proof of Conjecture 5.2 on Lucas descent at all integer indices.

Fiebig, Mbirika and Spilker state Conjecture 5.2 as open in Section 5 of their paper and attribute it there to Diego Garcia-Fernandezsesma, Oliver Lippard and aBa Mbirika. For even p and even positive m with gcd(q,m) = 1, the congruences U(2n) = 0 and U(2n+1) = q^n modulo m force exactly one of two alternatives: U(n) = 0, or U(n) = m/2 with n an odd integer multiple of half the entry point. This module proves the stronger implication at all integer indices: besides the two doubling hypotheses, it needs only a positive even modulus and a unit q. It needs none of the paper's standing restrictions on the parameters: nonzero parameters, coprimality of p and q, nondegeneracy, or parity of p.

The sequence, the entry-point notion and the conjecture come from the literature. The repository realizes the recurrence by powers of an invertible companion matrix and defines the entry point from the subgroup of integer zero indices. The general ring identities and the subgroup formulation below are repository formulations; the two final statements carry the paper's attribution.

In the displays, U(p,q,n) denotes lucasU p q n and e(p,q) denotes entryPoint p q. Mat2(R) means Matrix (Fin 2) (Fin 2) R, with row and column labels 0 and 1. Units(R) is the group Rˣ; val denotes its coercion to R (or to the matrix ring). Powers of units use integer exponents. Type* permits any universe, and bracketed binders retain the indicated Lean typeclass hypotheses. Cast(x,T) denotes the canonical cast to T. Div(x,2) denotes Lean's integer or natural division, as determined by the type of x; the evenness hypotheses make the halves in the conclusion exact.

**Definition 1.1 (The invertible companion matrix).**

$$\begin{aligned}\forall R: Type* [\operatorname{CommRing}\left(R\right)],\\\forall p: R, q: \operatorname{Units}\left(R\right),\\\operatorname{companion}\left(p, q\right): \operatorname{Units}\left(\operatorname{Mat2}\left(R\right)\right),\\\operatorname{val}\left(\operatorname{companion}\left(p, q\right)\right) = \begin{bmatrix}p&-\operatorname{val}\left(q\right)\\1&0\end{bmatrix}\\\operatorname{val}\left(\operatorname{companion}\left(p, q\right)^{-1}\right) = \begin{bmatrix}0&1\\-\operatorname{val}\left(q^{-1}\right)&\operatorname{val}\left(q^{-1}\right) \cdot p\end{bmatrix}\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/LucasEvenDescent.companion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix has determinant q. Its displayed inverse uses the inverse of the unit q, so the construction needs only a commutative ring and supports negative powers as well as nonnegative powers.

**Definition 1.2 (The Lucas sequence from integer matrix powers).**

$$\begin{aligned}\forall R: Type* [\operatorname{CommRing}\left(R\right)],\\\forall p: R, q: \operatorname{Units}\left(R\right),\\\forall n: \mathbb{Z},\\\operatorname{U}\left(p, q, n\right) = (\operatorname{val}\left(\operatorname{companion}\left(p, q\right)^{n}\right))_{1,0}\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/LucasEvenDescent.lucasU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the entry in row 1, column 0 of the n-th power of the companion unit. This is a repository realization of the paper's recurrence. Invertibility makes it meaningful for every integer n.

**Theorem 1.3 (Initial values and recurrence at every integer index).**

$$\begin{aligned}\forall R: Type* [\operatorname{CommRing}\left(R\right)],\\\forall p: R, q: \operatorname{Units}\left(R\right),\\\operatorname{U}\left(p, q, 0\right) = 0 \land \operatorname{U}\left(p, q, 1\right) = 1 \land\\\forall n: \mathbb{Z}, \operatorname{U}\left(p, q, n + 2\right) = p \cdot \operatorname{U}\left(p, q, n + 1\right) - \operatorname{val}\left(q\right) \cdot \operatorname{U}\left(p, q, n\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasEvenDescent.lucas_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Commuting a matrix power with the companion matrix determines all four entries in terms of U(n) and U(n+1). Multiplication by one more companion matrix gives the recurrence; the zeroth and first powers give U(0)=0 and U(1)=1. No sign restriction on n is used.

**Theorem 1.4 (The doubling hypotheses force two-torsion).**

$$\begin{aligned}\forall R: Type* [\operatorname{CommRing}\left(R\right)],\\\forall p: R, q: \operatorname{Units}\left(R\right),\\\forall n: \mathbb{Z},\\\operatorname{U}\left(p, q, 2 \cdot n\right) = 0 \Rightarrow \operatorname{U}\left(p, q, 2 \cdot n + 1\right) = \operatorname{val}\left(q^{n}\right) \Rightarrow\\2 \cdot \operatorname{U}\left(p, q, n\right) = 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasEvenDescent.two_mul_lucas_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary p, matrix multiplication gives both doubling identities, and the determinant gives the quadratic identity with right side q^n. Combining them under both displayed hypotheses yields (2U(n))q^n=0. Cancel the unit q^n. This step holds over any commutative ring, without a finiteness or modulus hypothesis.

**Definition 1.5 (The nonnegative generator of the zero indices).**

$$\begin{aligned}\forall R: Type* [\operatorname{CommRing}\left(R\right)],\\\forall p: R, q: \operatorname{Units}\left(R\right),\\g: \mathbb{Z}, g\mathbb{Z} = \{ n: \mathbb{Z} \mid \operatorname{U}\left(p, q, n\right) = 0 \},\\\operatorname{e}\left(p, q\right) = \operatorname{natAbs}\left(g\right) \in \mathbb{N}\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/LucasEvenDescent.entryPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The addition identity closes the zero indices under addition. At a zero index, the determinant identity makes the next value a unit; the addition identity then closes the zero indices under negation. Every additive subgroup of the integers is cyclic. Lean chooses a generator g using Classical.choose and takes its natural absolute value. In the display gZ denotes its subgroup of integer multiples. This construction is noncomputable and may give zero over an infinite ring; positivity is proved separately under the finite-ring hypothesis.

**Theorem 1.6 (Zero indices are exactly entry-point multiples).**

$$\begin{aligned}\forall R: Type* [\operatorname{CommRing}\left(R\right)],\\\forall p: R, q: \operatorname{Units}\left(R\right),\\\forall n: \mathbb{Z},\\\operatorname{U}\left(p, q, n\right) = 0 \iff \operatorname{Cast}\left(\operatorname{e}\left(p, q\right), \mathbb{Z}\right) \mid n\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasEvenDescent.lucas_eq_zero_iff_entry_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in the cyclic subgroup is integer divisibility by its generator. Replacing that generator by its natural absolute value does not change divisibility. The equivalence includes negative indices and does not require a finite ring.

**Theorem 1.7 (The least positive zero index over a finite ring).**

$$\begin{aligned}\forall R: Type* [\operatorname{CommRing}\left(R\right)],\\{}[\operatorname{Finite}\left(R\right)],\\\forall p: R, q: \operatorname{Units}\left(R\right),\\0 < \operatorname{e}\left(p, q\right) \land \operatorname{U}\left(p, q, \operatorname{Cast}\left(\operatorname{e}\left(p, q\right), \mathbb{Z}\right)\right) = 0 \land\\\forall r: \mathbb{N}, 0 < r \Rightarrow \operatorname{U}\left(p, q, \operatorname{Cast}\left(r, \mathbb{Z}\right)\right) = 0 \Rightarrow \operatorname{e}\left(p, q\right) \leq r\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasEvenDescent.entry_point_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The companion unit has positive finite order, and its power at that order is the identity. Thus there is a positive zero index. The divisibility characterization makes e positive, makes e itself a zero index, and bounds it by every positive natural zero index. This identifies the subgroup construction with the usual entry point of the sequence at nonnegative indices.

**Theorem 1.8 (Exactly one descent alternative in ZMod m).**

$$\begin{aligned}\forall m: \mathbb{N}, 0 < m \Rightarrow \operatorname{Even}\left(m\right) \Rightarrow\\\forall p: \operatorname{ZMod}\left(m\right),\\\forall q: \operatorname{Units}\left(\operatorname{ZMod}\left(m\right)\right), \forall n: \mathbb{Z},\\\operatorname{U}\left(p, q, 2 \cdot n\right) = 0 \Rightarrow \operatorname{U}\left(p, q, 2 \cdot n + 1\right) = \operatorname{val}\left(q^{n}\right) \Rightarrow\\\operatorname{Xor}\left(\operatorname{U}\left(p, q, n\right) = 0, \operatorname{U}\left(p, q, n\right) = \operatorname{Cast}\left(\operatorname{Div}\left(m, 2\right), \operatorname{ZMod}\left(m\right)\right) \land \operatorname{Even}\left(\operatorname{e}\left(p, q\right)\right) \land \exists c: \mathbb{Z}, \operatorname{Odd}\left(c\right) \land n = c \cdot \operatorname{Div}\left(\operatorname{Cast}\left(\operatorname{e}\left(p, q\right), \mathbb{Z}\right), 2\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasEvenDescent.lucas_even_descent` (`✓ std3`). ∎

*Citation.* Morgan Fiebig, aBa Mbirika, Jürgen Spilker (2025). *Period patterns, entry points, and orders in the Lucas sequences: theory and applications*. URL: <https://arxiv.org/abs/2408.14632v2>.

*Commentary.*

The ring theorem gives 2U(n)=0 for arbitrary p. In ZMod m, the self-negative residues are zero and the half-modulus residue. In the nonzero case, e divides 2n but does not divide n. Writing 2n=e c forces c odd and e even, hence n=c(e/2). The conclusion records both the evenness of e and the odd integer multiplier, including when n is negative.

Here Xor(A,B) means (A and not B) or (B and not A), matching Lean's exclusive disjunction. The alternatives are mutually exclusive because an even positive m is at least 2 and 0 < m/2 < m. Consequently the half-modulus residue is not zero. Both alternatives actually occur: for p=2, q=1 and m=4 the recurrence gives U(n)=n modulo 4 and e=4. The index n=4 gives the zero alternative, while n=2 gives the half-modulus alternative with odd multiplier c=1; both indices satisfy the two doubling hypotheses.

**Theorem 1.9 (Conjecture 5.2 with integer parameters).**

$$\begin{aligned}\forall p: \mathbb{Z}, q: \mathbb{Z}, m: \mathbb{N},\\0 < m \Rightarrow \operatorname{Even}\left(p\right) \Rightarrow \operatorname{Even}\left(m\right) \Rightarrow \operatorname{gcd}\left(q, \operatorname{Cast}\left(m, \mathbb{Z}\right)\right) = 1 \Rightarrow\\\forall n: \mathbb{Z},\\\operatorname{let} Q: \operatorname{Units}\left(\operatorname{ZMod}\left(m\right)\right) = \operatorname{unit}\left(q, m\right) \operatorname{in}\\\operatorname{U}\left(\operatorname{Cast}\left(p, \operatorname{ZMod}\left(m\right)\right), Q, 2 \cdot n\right) = 0 \Rightarrow \operatorname{U}\left(\operatorname{Cast}\left(p, \operatorname{ZMod}\left(m\right)\right), Q, 2 \cdot n + 1\right) = \operatorname{val}\left(Q^{n}\right) \Rightarrow\\\operatorname{Xor}\left(\operatorname{U}\left(\operatorname{Cast}\left(p, \operatorname{ZMod}\left(m\right)\right), Q, n\right) = 0, \operatorname{U}\left(\operatorname{Cast}\left(p, \operatorname{ZMod}\left(m\right)\right), Q, n\right) = \operatorname{Cast}\left(\operatorname{Div}\left(m, 2\right), \operatorname{ZMod}\left(m\right)\right) \land \operatorname{Even}\left(\operatorname{e}\left(\operatorname{Cast}\left(p, \operatorname{ZMod}\left(m\right)\right), Q\right)\right) \land \exists c: \mathbb{Z}, \operatorname{Odd}\left(c\right) \land n = c \cdot \operatorname{Div}\left(\operatorname{Cast}\left(\operatorname{e}\left(\operatorname{Cast}\left(p, \operatorname{ZMod}\left(m\right)\right), Q\right), \mathbb{Z}\right), 2\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LucasEvenDescent.conjecture_five_two` (`✓ std3`). ∎

*Citation.* Morgan Fiebig, aBa Mbirika, Jürgen Spilker (2025). *Period patterns, entry points, and orders in the Lucas sequences: theory and applications*. URL: <https://arxiv.org/abs/2408.14632v2>.

*Commentary.*

For integers p and q, the hypothesis gcd(q,m)=1 supplies the canonical unit Q in ZMod m. In the display unit(q,m) abbreviates ZMod.unitOfIsCoprime q (Int.isCoprime_iff_gcd_eq_one.mpr hqm), where hqm is the displayed gcd hypothesis; its value is q modulo m. Thus Q^n specifies the modular meaning of q^n even at negative indices, without integer division. Applying lucas_even_descent proves the paper's conjecture under precisely the hypotheses displayed here. The parity hypothesis on p is retained for fidelity to the cited statement and is not used by the proof.

## References

- Truth anchor: `D5/S1/Recurrence/LucasEvenDescent.companion`
- Truth anchor: `D5/S1/Recurrence/LucasEvenDescent.conjecture_five_two`
- Truth anchor: `D5/S1/Recurrence/LucasEvenDescent.entryPoint`
- Truth anchor: `D5/S1/Recurrence/LucasEvenDescent.entry_point_spec`
- Truth anchor: `D5/S1/Recurrence/LucasEvenDescent.lucasU`
- Truth anchor: `D5/S1/Recurrence/LucasEvenDescent.lucas_eq_zero_iff_entry_dvd`
- Truth anchor: `D5/S1/Recurrence/LucasEvenDescent.lucas_even_descent`
- Truth anchor: `D5/S1/Recurrence/LucasEvenDescent.lucas_recurrence`
- Truth anchor: `D5/S1/Recurrence/LucasEvenDescent.two_mul_lucas_eq_zero`
