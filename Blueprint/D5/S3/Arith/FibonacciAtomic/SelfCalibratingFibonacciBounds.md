# Sharp Fibonacci Bounds for Literal Matrix Words

## Abstract

Every literal Fibonacci and swap word obeys five Fibonacci bounds with explicit sharpness words.

Let M have rows (0,1),(1,1), and let J have rows (0,1),(1,0). A finite Boolean list w is read chronologically, with false denoting M and true denoting J. Its matrix E(w) satisfies E(empty)=I and E(p followed by q)=E(q)E(p). Write E(w) with rows (a,b),(c,d), set delta=d-a, and let n be the literal list length.

The Fibonacci sequence has F(0)=0, F(1)=1 and F(n+2)=F(n)+F(n+1). Set K(n)=F(n-2), where subtraction of natural numbers is truncated at zero. Thus K(n)=0 for n=0,1,2. All matrix entries and comparisons are integers.

For each natural n define the lists m(n)=replicate(n,false) and q(n)=[true] followed by replicate(n-2,false) followed by [true]. The functions b(v), c(v), and delta(v) read the corresponding entries and diagonal difference of E(v). In the first conjunct n=length(w).

**Theorem 1.1 (Five universal inequalities and two exact word families).**

$$(\forall w, b \leq \operatorname{F}\left(n\right) \land c \leq \operatorname{F}\left(n\right) \land \Vert delta\Vert \leq \operatorname{F}\left(n\right) \land -delta \leq \operatorname{K}\left(n\right) \land delta-2b \leq \operatorname{K}\left(n\right)) \land (\forall n \geq 1, \operatorname{length}\left(\operatorname{m}\left(n\right)\right)=n \land \operatorname{b}\left(\operatorname{m}\left(n\right)\right)=\operatorname{F}\left(n\right) \land \operatorname{c}\left(\operatorname{m}\left(n\right)\right)=\operatorname{F}\left(n\right) \land \Vert\operatorname{delta}\left(\operatorname{m}\left(n\right)\right)\Vert=\operatorname{F}\left(n\right)) \land (\forall n \geq 3, \operatorname{length}\left(\operatorname{q}\left(n\right)\right)=n \land -\operatorname{delta}\left(\operatorname{q}\left(n\right)\right)=\operatorname{K}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SelfCalibratingFibonacciBounds.raw_word_fibonacci_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every raw list is included: the empty list, lengths 1,2,3,4, and lists with arbitrary adjacent JJ pairs. The bound uses the length before any pair is removed.

For every n>=1 the single list v=replicate(n,false) has length n and simultaneously satisfies b(v)=F(n), c(v)=F(n), and abs(delta(v))=F(n). Its matrix is M to the power n, with rows (F(n-1),F(n)),(F(n),F(n-1)+F(n)).

For every n>=3 the literal list v=[true] followed by replicate(n-2,false) followed by [true] has length n and satisfies -delta(v)=F(n-2)=K(n). Its matrix is J M to the power n-2 J. No equality for delta-2b at every length is asserted.

A joint strong induction treats the two offdiagonal entries and four linear signed inequalities. A JJ pair leaves the matrix unchanged and reduces the length by two; monotonicity of F and K then gives the bounds at the original length. An MM pair uses M squared=M+I, so its matrix is the sum of word matrices of lengths n-1 and n-2. The linear inequalities add, F(n-1)+F(n-2)=F(n), and K(n-1)+K(n-2)<=K(n), including n=2,3,4.

Without an equal adjacent pair the word alternates. At even length 2j the matrices have rows (1,j),(0,1) or (1,0),(j,1). At odd length 2j+1 they have rows (0,1),(1,j+1) or (j,1),(1,0). The estimates j<=F(2j-1) and j+1<=F(2j+1) give all remaining bounds, including j=0. The two bounds on delta give the absolute value bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SelfCalibratingFibonacciBounds.raw_word_fibonacci_bounds`
- Dependency: [D5/S3/Arith/FibonacciAtomic/SelfCalibratingRawWords](SelfCalibratingRawWords.md)
