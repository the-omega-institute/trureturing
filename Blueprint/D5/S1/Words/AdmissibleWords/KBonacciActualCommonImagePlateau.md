# Two-step growth of actual common polynomial images

## Abstract

Every two-step plateau of the exact-length legal common image is already the full polynomial image. Its first saturation length is at most twice the common-image cardinality minus three, including composite coefficient moduli.

Fix k and d at least two and a nonempty finite injective family of probe orders a_i at least two. The coefficient ring is ZMod d. Each Phi_b is X^b minus the sum of X^j for zero at most j below b. The map q sends one polynomial to its classes in all the AdjoinRoot quotients, and H is q.range with its induced ring structure. The map O returns the monic remainder representatives in all coordinates. Thus range O is a carrier equivalent to H, and M is Nat.card H.

A word w has type Fin n to Bool, with position zero at the constant term. The function bit sends false to zero and true to one in ZMod d. Pw(n,w) is its polynomial. I_n is the raw tuple image of accepted words of exact length n, using the original DBonacciAdmissible k scanner. One word and one polynomial supply every probe. Every zero occupies a position, and n ranges over all natural numbers, including zero. IsLeast(S,N) means N belongs to S and is at most every member of S.

**Theorem 1.1 (No proper two-step plateau and the first exact full-image length).**

$$\forall k: \mathbb{N}, \forall d: \mathbb{N}, \forall r: \mathbb{N}, \forall a: \operatorname{Fin}(r) \to \mathbb{N}, (2\leq k \land 2\leq d \land 1\leq r \land \operatorname{Injective}(a) \land (\forall i: \operatorname{Fin}(r), 2\leq a(i))) \implies \operatorname{let} R= \operatorname{ZMod}(d), \operatorname{let} Phi= (b: \mathbb{N} \mapsto X^{b}-\sum_{j\in \operatorname{range}(b)}X^{j}), \operatorname{let} Q= \prod_{i: \operatorname{Fin}(r)}\operatorname{AdjoinRoot}(Phi(a(i))), \operatorname{let} q= (P: R[X] \mapsto (mk_{Phi(a(i))}(P))_{i: \operatorname{Fin}(r)}): \operatorname{RingHom}(R[X], Q), \operatorname{let} H= \operatorname{range}(q), \operatorname{let} O= (P: R[X] \mapsto (P \operatorname{modByMonic} Phi(a(i)))_{i: \operatorname{Fin}(r)}), \operatorname{let} Pw= (n: \mathbb{N} \mapsto (w: \operatorname{Fin}(n) \to \operatorname{Bool} \mapsto \sum_{i: \operatorname{Fin}(n)}\operatorname{bit}(w(i))X^{\operatorname{val}(i)})), \operatorname{let} I= (n: \mathbb{N} \mapsto \{y: \operatorname{Fin}(r) \to R[X] \mid \exists w: \operatorname{Fin}(n) \to \operatorname{Bool}, \operatorname{DBonacciAdmissible}(k, n, w) \land O(\operatorname{Pw}(n, w))= y\}), \operatorname{let} M= \operatorname{card}(H), (\forall n: \mathbb{N}, (I_{n}= I_{n+2} \implies I_{n}= \operatorname{range}(O))) \land (\exists N\in \mathbb{N}, \operatorname{IsLeast}(\{n\in \mathbb{N} \mid I_{n}= \operatorname{range}(O)\}, N) \land N\leq 2M-3 \land (\forall n: \mathbb{N}, (I_{n}= \operatorname{range}(O) \Leftrightarrow N\leq n)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciActualCommonImagePlateau.kbonacci_actual_common_image_plateau_and_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite polynomial quotient by the product of all Phi_(a_i) maps onto H. Its root is a unit, so multiplication by x, the image of X, is injective on finite H. Projection onto any probe gives M at least d^(a_i), hence M at least four. Monic remainder representatives inject into raw polynomial tuples; their multiplication is quotient multiplication followed by remainder.

Appending a high-side false bit preserves value and acceptance. Prepending a low-side false bit multiplies the value by x. Appending the literal high-side suffix false,true adds x^(n+1), and its delimiter preserves acceptance even at k=2 and n=0. These operations give the required inclusions into length n+1 or n+2 without changing k.

At a two-step plateau S, the finite injective images xS and S+x^(n+1) equal S. Iteration makes each multiplication by x^j surjective on S. Pulling back the translation by x^(n+1) and cancelling this unit gives closure under addition of one. Pulling back by x^j then gives closure under addition of x^j. Repeating this addition by a coefficient's natural representative and summing monomials gives every polynomial translation. The all-false word supplies zero, so S is all H. All these pullbacks act on algebraic images.

Every proper image therefore gains at least one element in two positions. The length-one image is exactly the distinct pair zero,one. Induction gives card I_(2j+1) at least min(M,j+2). Taking j=M-2 gives full image at the single common exact length 2M-3. The least full-image length N exists and is at most that bound. Counted high-side zero padding preserves saturation at every later length; minimality gives the converse.

The conclusion concerns the accepted remainder image and bit length. It asserts no sharp threshold, terminal-tail or phase constraint, runtime bound, reconstruction of an unknown word, or replacement of the scanner's rejection output.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciActualCommonImagePlateau.kbonacci_actual_common_image_plateau_and_budget`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciActualTailImages](KBonacciActualTailImages.md)
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciJointLegalRealization](KBonacciJointLegalRealization.md)
