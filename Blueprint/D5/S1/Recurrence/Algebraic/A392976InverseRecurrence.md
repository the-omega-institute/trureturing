# A392976: The Formal Inverse Quintic Recurrence

## Abstract

The inverse quintic satisfies the full A392976 recurrence and is D-finite.

OEIS A392976, https://oeis.org/A392976, defines the sequence by reversion of f(X)=X((1-X^2)^2-X). All series here are formal power series over Q, with ordinary degree beginning at zero. Rational coefficients provide the characteristic-zero carrier of the published integer sequence. The inverse has constant coefficient zero; both formal compositions are X. No analytic branch is selected. The offset is zero. The secondary offset three does not set the recurrence threshold. Every recurrence index is a natural number at least five, representing every integer in that range, and subtraction in a sequence argument is natural subtraction. The function castQ embeds a natural number into Q. Substitution uses the polynomial f as its formal power series.

**Definition 1.1 (The quintic polynomial).**

$$f = X \cdot ((1 - X^{2})^{2} - X)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial lies in Q[X], has constant coefficient zero and linear coefficient one.

**Definition 1.2 (The zero-constant inverse).**

$$U = \operatorname{substInvOfIsUnit}\left(f\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formal inverse construction applies because the linear coefficient of f is a unit. Its defining uniqueness and both inverse compositions appear in the complete assertion below.

**Definition 1.3 (The quotient series).**

$$A = \operatorname{mk}\left((n:\mathbb{N} \mapsto \operatorname{coeff}\left(n + 1, U\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The n-th coefficient is the coefficient of degree n+1 in U, so X A=U.

**Definition 1.4 (The offset-zero sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n + 1, U\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Thus A is the ordinary generating series of a(n), beginning at n=0.

**Definition 1.5 (Homogeneous D-finiteness).**

$$\forall B \in \mathbb{Q}[[X]],\; \operatorname{DFinite}\left(B\right) \Leftrightarrow \left(\exists d \in \mathbb{N},\; \exists p \in \operatorname{Fin}\left(d + 1\right) \to \mathbb{Q}[X],\; \left(\exists j \in \operatorname{Fin}\left(d + 1\right),\; \operatorname{p}\left(j\right) \ne 0\right) \land \sum_{j:\operatorname{Fin}\left(d + 1\right)} \operatorname{p}\left(j\right) \cdot \operatorname{iterateDerivative}\left(j, B\right) = 0\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.DFinite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The derivative is formal. A polynomial family indexed by Fin(d+1) gives the coefficients of derivative orders zero through d. At least one polynomial is nonzero; the differential equation is homogeneous.

**Definition 1.6 (The complete inverse and recurrence assertion).**

$$claim \Leftrightarrow \left(\operatorname{coeff}\left(0, U\right) = 0 \land \left(\operatorname{subst}\left(f, U\right) = X \land \left(\operatorname{subst}\left(U, f\right) = X \land \left(\left(\forall V \in \mathbb{Q}[[X]],\; \operatorname{coeff}\left(0, V\right) = 0 \Rightarrow \left(\operatorname{subst}\left(f, V\right) = X \Rightarrow V = U\right)\right) \land \left(X \cdot A = U \land \left(\operatorname{DFinite}\left(A\right) \land \left(\forall n \in \mathbb{N},\; 5 \le n \Rightarrow 283 \cdot \operatorname{castQ}\left(n\right) \cdot (\operatorname{castQ}\left(n\right) - 1) \cdot (\operatorname{castQ}\left(n\right) - 2) \cdot (83022305213 \cdot \operatorname{castQ}\left(n\right) - 178385058984) \cdot (\operatorname{castQ}\left(n\right) + 1) \cdot \operatorname{a}\left(n\right) - 6 \cdot \operatorname{castQ}\left(n\right) \cdot (\operatorname{castQ}\left(n\right) - 1) \cdot (\operatorname{castQ}\left(n\right) - 2) \cdot (12196786904129 \cdot \operatorname{castQ}\left(n\right)^{2} - 45110300936020 \cdot \operatorname{castQ}\left(n\right) + 52641391340361) \cdot \operatorname{a}\left(n - 1\right) - 6 \cdot (\operatorname{castQ}\left(n\right) - 1) \cdot (\operatorname{castQ}\left(n\right) - 2) \cdot (67790996421377 \cdot \operatorname{castQ}\left(n\right)^{3} - 248299346995054 \cdot \operatorname{castQ}\left(n\right)^{2} + 202497447227007 \cdot \operatorname{castQ}\left(n\right) + 3061418504418) \cdot \operatorname{a}\left(n - 2\right) - 2 \cdot (\operatorname{castQ}\left(n\right) - 2) \cdot (192167357944360 \cdot \operatorname{castQ}\left(n\right)^{4} - 559010679688491 \cdot \operatorname{castQ}\left(n\right)^{3} - 2120668219560541 \cdot \operatorname{castQ}\left(n\right)^{2} + 9123363136130610 \cdot \operatorname{castQ}\left(n\right) - 8342981628089220) \cdot \operatorname{a}\left(n - 3\right) + 5 \cdot (15640122296875 \cdot \operatorname{castQ}\left(n\right)^{5} - 565964885220500 \cdot \operatorname{castQ}\left(n\right)^{4} + 4989857715427325 \cdot \operatorname{castQ}\left(n\right)^{3} - 18667678380008380 \cdot \operatorname{castQ}\left(n\right)^{2} + 32085126156301848 \cdot \operatorname{castQ}\left(n\right) - 20925325629575136) \cdot \operatorname{a}\left(n - 4\right) + 10 \cdot (5 \cdot \operatorname{castQ}\left(n\right) - 17) \cdot (5 \cdot \operatorname{castQ}\left(n\right) - 18) \cdot (5 \cdot \operatorname{castQ}\left(n\right) - 21) \cdot (5 \cdot \operatorname{castQ}\left(n\right) - 19) \cdot (22509687685 \cdot \operatorname{castQ}\left(n\right) - 60308240636) \cdot \operatorname{a}\left(n - 5\right) = 0\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assertion includes both inverse compositions, uniqueness among all zero-constant formal right inverses, X A=U, homogeneous D-finiteness, and all six signed terms of the stated recurrence at every n at least five. No exceptional index is removed.

**Theorem 1.7 (The full A392976 identity and D-finiteness).**

$$\operatorname{coeff}\left(0, U\right) = 0 \land \left(\operatorname{subst}\left(f, U\right) = X \land \left(\operatorname{subst}\left(U, f\right) = X \land \left(\left(\forall V \in \mathbb{Q}[[X]],\; \operatorname{coeff}\left(0, V\right) = 0 \Rightarrow \left(\operatorname{subst}\left(f, V\right) = X \Rightarrow V = U\right)\right) \land \left(X \cdot A = U \land \left(\operatorname{DFinite}\left(A\right) \land \left(\forall n \in \mathbb{N},\; 5 \le n \Rightarrow 283 \cdot \operatorname{castQ}\left(n\right) \cdot (\operatorname{castQ}\left(n\right) - 1) \cdot (\operatorname{castQ}\left(n\right) - 2) \cdot (83022305213 \cdot \operatorname{castQ}\left(n\right) - 178385058984) \cdot (\operatorname{castQ}\left(n\right) + 1) \cdot \operatorname{a}\left(n\right) - 6 \cdot \operatorname{castQ}\left(n\right) \cdot (\operatorname{castQ}\left(n\right) - 1) \cdot (\operatorname{castQ}\left(n\right) - 2) \cdot (12196786904129 \cdot \operatorname{castQ}\left(n\right)^{2} - 45110300936020 \cdot \operatorname{castQ}\left(n\right) + 52641391340361) \cdot \operatorname{a}\left(n - 1\right) - 6 \cdot (\operatorname{castQ}\left(n\right) - 1) \cdot (\operatorname{castQ}\left(n\right) - 2) \cdot (67790996421377 \cdot \operatorname{castQ}\left(n\right)^{3} - 248299346995054 \cdot \operatorname{castQ}\left(n\right)^{2} + 202497447227007 \cdot \operatorname{castQ}\left(n\right) + 3061418504418) \cdot \operatorname{a}\left(n - 2\right) - 2 \cdot (\operatorname{castQ}\left(n\right) - 2) \cdot (192167357944360 \cdot \operatorname{castQ}\left(n\right)^{4} - 559010679688491 \cdot \operatorname{castQ}\left(n\right)^{3} - 2120668219560541 \cdot \operatorname{castQ}\left(n\right)^{2} + 9123363136130610 \cdot \operatorname{castQ}\left(n\right) - 8342981628089220) \cdot \operatorname{a}\left(n - 3\right) + 5 \cdot (15640122296875 \cdot \operatorname{castQ}\left(n\right)^{5} - 565964885220500 \cdot \operatorname{castQ}\left(n\right)^{4} + 4989857715427325 \cdot \operatorname{castQ}\left(n\right)^{3} - 18667678380008380 \cdot \operatorname{castQ}\left(n\right)^{2} + 32085126156301848 \cdot \operatorname{castQ}\left(n\right) - 20925325629575136) \cdot \operatorname{a}\left(n - 4\right) + 10 \cdot (5 \cdot \operatorname{castQ}\left(n\right) - 17) \cdot (5 \cdot \operatorname{castQ}\left(n\right) - 18) \cdot (5 \cdot \operatorname{castQ}\left(n\right) - 21) \cdot (5 \cdot \operatorname{castQ}\left(n\right) - 19) \cdot (22509687685 \cdot \operatorname{castQ}\left(n\right) - 60308240636) \cdot \operatorname{a}\left(n - 5\right) = 0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write theta=X d/dX and let c(k,n) be the six signed polynomial coefficients displayed above. The operator sum over k=0,...,5 of X^k c(k,theta+k) annihilates A. Multiplication by X transforms it into the corresponding operator on U with theta+k-1. After composition with f, the chain rule clears denominators using H=f', whose constant coefficient is one. The resulting polynomial identity is zero. Coefficient extraction gives exactly the displayed identity at every n at least five. Expanding theta powers into ordinary derivatives gives a homogeneous operator of order five; its fifth-derivative polynomial has coefficient 23495312375279 at degree five, so the operator is nonzero. No minimal-order assertion is made.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.DFinite`
- Truth anchor: `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.U`
- Truth anchor: `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.a`
- Truth anchor: `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.f`
- Truth anchor: `D5/S1/Recurrence/Algebraic/A392976InverseRecurrence.result`
- Dependency: [D5/S1/Recurrence/A308815DFiniteRecurrence](../A308815DFiniteRecurrence.md)
