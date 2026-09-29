# Global affine behavior and joint local realization

## Abstract

Actual local quotient codes classify all legal finite words and have a common positive source.

**Theorem 1.1 (Exact behavior of the original positive operation library).**

$$\forall H \in \mathbb{N}, \forall A \in \operatorname{List}(\mathbb{N}_{>0}), (2 \le H) \Rightarrow ((\forall x \in \mathbb{N}_{>0}, \forall y \in \mathbb{N}_{>0}, (\operatorname{globalEncoding}(H, A, x) = \operatorname{globalEncoding}(H, A, y)) \Leftrightarrow (\forall w \in \operatorname{List}(\operatorname{Operation}(A)), \operatorname{gcd}(\operatorname{runWord}(A, w, x), H) = \operatorname{gcd}(\operatorname{runWord}(A, w, y), H))) \land (\forall x \in \mathbb{N}_{>0}, \forall y \in \mathbb{N}_{>0}, (\operatorname{globalEncoding}(H, A, x) = \operatorname{globalEncoding}(H, A, y)) \Leftrightarrow (\forall w \in \operatorname{List}(\operatorname{Operation}(A)), \operatorname{div}(H, \operatorname{gcd}(\operatorname{runWord}(A, w, x), H)) = \operatorname{div}(H, \operatorname{gcd}(\operatorname{runWord}(A, w, y), H)))) \land (\forall x \in \mathbb{N}_{>0}, \forall y \in \mathbb{N}_{>0}, (\operatorname{globalEncoding}(H, A, x) \neq \operatorname{globalEncoding}(H, A, y)) \Rightarrow \exists p \in \operatorname{primeFactors}(H), \exists a \in \mathbb{N}_{>0}, \exists ws \in \operatorname{List}(\operatorname{Fin}(\operatorname{length}(A))), \operatorname{factorization}(\operatorname{gcd}(\operatorname{runWord}(A, \operatorname{multiplyThenAdd}(a, ws), x), H), p) \neq \operatorname{factorization}(\operatorname{gcd}(\operatorname{runWord}(A, \operatorname{multiplyThenAdd}(a, ws), y), H), p)) \land (\forall c \in \operatorname{GlobalCode}(H, A), \exists x \in \mathbb{N}_{>0}, \operatorname{globalEncoding}(H, A, x) = c))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/GlobalAffineGcdBehavior.global_encoding_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix H at least two and a finite list A of positive integer addends. Put d = libraryGcd(H,A), with d = H when A is empty. Each prime p dividing H has h = H.factorization(p) and e = d.factorization(p). The function globalEncoding(H,A,x) is the dependent tuple of the actual localEncoding(p,h,e,x modulo p^h) on these prime axes. Its codomain GlobalCode(H,A) is the product of the typed LocalCode(p,h,e) spaces.

Two positive sources have equal global codes exactly when every same legal finite word produces equal gcds with H, and exactly when every same word produces equal quotients H/gcd. Legal words contain positive multiplications and indexed additions from A, include the empty word, and have no fixed length bound. A multiplier congruent to zero is permitted: the positive multiplier H represents that residue.

If two codes differ, one prime axis and one positive multiplier followed by a finite list of original additions give different gcd exponents on that axis for the same two sources. Writing d = p^e t, the cofactor t is coprime to p and is a unit modulo p^(h-e). A local signed translation p^e delta is therefore represented by one nonnegative global coefficient b in d b. When e = h, that translation vanishes on the axis and b = 0 suffices. The original-library affine realization supplies the finite list of additions. Other prime axes may change; a different exponent on the chosen axis already distinguishes the gcds.

Conversely, a mixed word has a positive affine slope and a translation divisible by d. Equal local codes preserve every such depth. The depth on each prime axis is exactly its exponent in the output gcd, so the global gcds agree. Since both gcds divide the same positive H, their quotients agree exactly when the gcds agree.

Every tuple of typed local labels is attained by one positive source. First choose the integer representative of each label supplied by the local completeness theorem. The Chinese remainder equivalence for the actual prime-power factors of H gives one residue z modulo H. The positive integer z.val + H represents it simultaneously on every axis, including when the residue is zero.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/GlobalAffineGcdBehavior.global_encoding_complete`
- Dependency: [D5/S3/Factorization/PrimePowers/AffineGcdBehavior](AffineGcdBehavior.md)
