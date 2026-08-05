# Finite-Window Escape and Hidden Fibers

## Abstract

Finite prime windows escape; finite readings retain a nonzero kernel difference.

**Theorem 1.1 (Finite prime windows escape and finite readings retain hidden differences).**

$$\forall S\subset_{\mathrm{fin}}\mathbb{N},\ \left(\forall p\in S,\ \operatorname{Prime}(p)\right) \Rightarrow P_{S}=\prod_{r\in S}r,\ E_{S}=P_{S}+1,\ \left(\left(\forall p\in S,\ E_{S}\equiv1[\operatorname{mod}p]\right) \land \neg(E_{S}\in S) \land \left(\exists q\in\mathbb{N},\ \operatorname{Prime}(q) \land q\mid E_{S} \land \neg(q\in S)\right) \land \left(\forall q\in\mathbb{N},\ \operatorname{Prime}(q) \land q\mid E_{S} \Rightarrow \neg(q\in S)\right) \land \forall G\text{ infinite additive group},\ \forall A\text{ finite additive group},\ \forall R:G\to A\text{ additive},\ \exists x,y\in G,\ x\neq y \land R(x)=R(y) \land x-y\neq0 \land R(x-y)=0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FiniteWindowEscape.finite_window_escape_and_hidden_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite set S of natural primes, write P_S for its product, and set E_S = P_S + 1. The declaration proves that E_S is congruent to one modulo every member of S, that E_S itself is outside S, that E_S has a prime divisor outside S, and that every prime divisor of E_S is outside S. Thus every finite prime window leaves an external prime direction: the prime-axis tail persists and the window is not closed under the product-plus-one escape construction.

For the finite-reading clause, G is any infinite additive group, A is any finite additive group, and R is any additive homomorphism from G to A. The witnesses x and y are distinct but have equal readings; their difference is explicitly nonzero and R maps it to zero. The formal statement therefore realizes the kernel branch of the hidden-difference alternative directly. It introduces no narrative ledger object and makes no claim about ledger custody.

The proof combines the classical product-plus-one argument with the finite pigeonhole principle. Divisibility of P_S by every window prime gives the modular escape and excludes every prime divisor of E_S from S; existence of a prime divisor supplies the persistent tail. Finiteness of A and infinitude of G force a repeated reading, while additivity places the resulting nonzero difference in the kernel. The exact conjunction and its packaging as one declaration are repository-derived, and the result has no numerical certificate.
