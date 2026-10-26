# Cyclic carries and zero relations of the physical circle source

## Abstract

Cyclic natural carrying gives a unique physical binary endpoint and sharp unit-source relation length; binary masks also bound exact zero subsets and independent zero blocks.

**Theorem 1.1 (Natural cyclic carries and the sharp unit relation length).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall n \in \operatorname{Fin}\left(k\right) \to \mathrm{Nat},\; \left(0 < k \land \operatorname{ne}\left(n, 0\right)\right) \Rightarrow \left(\exists A \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right),\; \exists m \in \operatorname{Fin}\left(k\right) \to \mathrm{Nat},\; \left(\operatorname{Nonempty}\left(A\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{int}\left(\operatorname{apply}\left(n, i\right)\right) = \operatorname{indicator}\left(A, i\right) + 2 \cdot \operatorname{int}\left(\operatorname{apply}\left(m, i\right)\right) - \operatorname{int}\left(\operatorname{apply}\left(m, \operatorname{pred}\left(k, i\right)\right)\right)\right) \land \left(\operatorname{L}\left(n\right) = \operatorname{card}\left(A\right) + \operatorname{L}\left(m\right) \land \left(\operatorname{E}\left(n\right) = \operatorname{M}\left(A\right) + \left(2^{k} - 1\right) \cdot \operatorname{apply}\left(m, k - 1\right) \land \left(\operatorname{T}\left(k, t, n\right) = \operatorname{sourceSum}\left(k, t, A\right) + \left(2^{k} - 1\right) \cdot \operatorname{J}\left(k, t, m\right) \land \left(\left(\operatorname{T}\left(k, t, n\right) = 0 \Rightarrow \operatorname{dvd}\left(\operatorname{div}\left(2^{k} - 1, \operatorname{gcd}\left(t, 2^{k} - 1\right)\right), \operatorname{M}\left(A\right)\right)\right) \land \left(\operatorname{Coprime}\left(t, 2^{k} - 1\right) \Rightarrow \left(\operatorname{T}\left(k, t, n\right) = 0 \Rightarrow \left(A = \operatorname{univ}\left(\operatorname{Fin}\left(k\right)\right) \land \left(\operatorname{J}\left(k, t, m\right) = 0 \land \left(\operatorname{L}\left(n\right) = k + \operatorname{L}\left(m\right) \land \left(k \le \operatorname{L}\left(n\right) \land \left(\operatorname{L}\left(n\right) = k \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{apply}\left(n, i\right) = 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\forall B \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right),\; \forall v \in \operatorname{Fin}\left(k\right) \to \mathrm{Nat},\; \left(\operatorname{Nonempty}\left(B\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{int}\left(\operatorname{apply}\left(n, i\right)\right) = \operatorname{indicator}\left(B, i\right) + 2 \cdot \operatorname{int}\left(\operatorname{apply}\left(v, i\right)\right) - \operatorname{int}\left(\operatorname{apply}\left(v, \operatorname{pred}\left(k, i\right)\right)\right)\right) \land \left(\operatorname{L}\left(n\right) = \operatorname{card}\left(B\right) + \operatorname{L}\left(v\right) \land \left(\operatorname{E}\left(n\right) = \operatorname{M}\left(B\right) + \left(2^{k} - 1\right) \cdot \operatorname{apply}\left(v, k - 1\right) \land \left(\operatorname{T}\left(k, t, n\right) = \operatorname{sourceSum}\left(k, t, B\right) + \left(2^{k} - 1\right) \cdot \operatorname{J}\left(k, t, v\right) \land \left(\left(\operatorname{T}\left(k, t, n\right) = 0 \Rightarrow \operatorname{dvd}\left(\operatorname{div}\left(2^{k} - 1, \operatorname{gcd}\left(t, 2^{k} - 1\right)\right), \operatorname{M}\left(B\right)\right)\right) \land \left(\operatorname{Coprime}\left(t, 2^{k} - 1\right) \Rightarrow \left(\operatorname{T}\left(k, t, n\right) = 0 \Rightarrow \left(B = \operatorname{univ}\left(\operatorname{Fin}\left(k\right)\right) \land \left(\operatorname{J}\left(k, t, v\right) = 0 \land \left(\operatorname{L}\left(n\right) = k + \operatorname{L}\left(v\right) \land \left(k \le \operatorname{L}\left(n\right) \land \left(\operatorname{L}\left(n\right) = k \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{apply}\left(n, i\right) = 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(B = A \land v = m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ZeroSumSubsets.cyclic_binary_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k>0 and t be arbitrary natural numbers, N=2^k-1, and s(i)=actualSource(k,t,i) on the physical labels Fin(k). For any nonzero natural coefficient function n, there is exactly one pair consisting of a nonempty physical subset A and natural carries m. Write pred for the inverse of finRotate(k), L(x)=sum_i x(i), E(x)=sum_i x(i)2^i, and M(A)=sum_{i in A}2^i. In the coordinate equation the indicator is integer valued, every coefficient is cast to the integers before subtraction, and the last index k-1 denotes its physical Fin(k) label.

The pair satisfies n(i)=indicator_A(i)+2m(i)-m(pred(i)), L(n)=card(A)+L(m), and E(n)=M(A)+N m(k-1). The endpoint mask lies in [1,N]; the full mask N represents residue zero. To construct it, fire any coordinate containing at least two units, subtracting two there and adding one at its successor. The natural total decreases by exactly one and the vector remains nonzero. At k=1 these changes occur at the same coordinate and subtract one. Strong induction ends at a nonempty binary vector. Summing the coordinate identity gives the length formula; weighting by powers of two cancels every interior contribution and leaves only the last carry.

Two possible endpoints have congruent masks in [1,N], so their masks agree and binary-mask injectivity gives the same physical subset. For two carry vectors their integer difference d satisfies 2d(i)=d(pred(i)). Reindexing the sum of absolute values gives twice that sum equal to itself, hence d=0. This proves uniqueness of the counts, without asserting uniqueness of a firing order.

For the exact source put eps(i)=1 when N<4s(i), eps(i)=-1 when 4s(i)<-N, and eps(i)=0 otherwise. Define T(x)=sum_i x(i)s(i) and J(m)=sum_i m(i)eps(i), in the integers; their displayed arguments also show the fixed parameters k,t. The displayed sourceSum(k,t,A) means sum_{i in A}s(i). Centered doubling gives 2s(i)-s(next(i))=N eps(i). The unsigned potential u(i)=s(i)+(N if s(i)<0 else 0) satisfies u(next(i))-u(i)=s(i). Reindexing its cyclic sum gives sum_i s(i)=0, including k=1, zero sources, repeated values and short periods. Pairing the same coordinate equation with s proves T(n)=sum_{i in A}s(i)+N J(m). In particular carrying preserves modular charge but can change exact integer charge; the negative wrap has sign minus one.

If T(n)=0, then N divides t E(n). The weighted identity and gcd cancellation imply that N/gcd(t,N) divides M(A), for the very same pair. For a unit t modulo N, positivity and the upper bound M(A)<=N force M(A)=N and A=univ. The source total and the charge identity then give J(m)=0. Consequently L(n)=k+L(m), so L(n)>=k, and L(n)=k if and only if every physical n(i) equals one. No coordinatewise positivity was assumed. At k=1, N=1 and the result reads n(0)=1+m(0); at k=2 the unit source values are opposite.

For a nonunit source the divisibility condition and card(A)<=L(n) are necessary restrictions only. They do not make the endpoint integer-zero, assert a minimum-weight mask is attained by a relation, or realize any ordering in an interval. A closed-walk count vector may use the unit length bound only after an independent telescoping proof of its exact source charge zero. These arithmetic restrictions do not construct a capacity-(N-1)/2 permutation. Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671, remains open in its full all-source scope. No literature novelty claim is made.

**Theorem 1.2 (The source gcd bounds the entire zero fibre).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; 3 \le k \Rightarrow \operatorname{card}\left(\operatorname{Z}\left(k, t\right)\right) \le \operatorname{gcd}\left(t, 2^{k} - 1\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ZeroSumSubsets.zero_subsets_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be any natural number at least three, t any natural number, and N=2^k-1. The source is exactly SourceWidth.actualSource: at the physical label p in Fin(k), take the integer centered representative of t times 2^p modulo N. The centered interval is [-floor(N/2),floor(N/2)]. Cyclic doubling supplies these arithmetic residues; the count concerns their exact integer sums. Equal numerical values at different positions remain different labels.

Write Z for all finsets A of Fin(k) whose source values sum to the integer zero. Thus Z ranges over every physical-label finset satisfying that equality. Then card(Z) is at most gcd(t,N)+1. There is no unit, distinct-value or full-period assumption.

Encode A by the natural binary mask M(A)=sum over p in A of 2^p. Colexicographic binary-sum injectivity makes M injective on physical subsets. Every mask lies in [0,N], including the empty mask zero and the full mask N. Each centered value is congruent to t times 2^p modulo N. Summing these congruences shows that integer zero forces N to divide t M(A).

Put g=gcd(t,N) and Q=N/g. Since N is positive, g and Q are positive. Cancel g, then use coprimality of t/g and N/g: Q divides every zero-subset mask. The quotient M(A)/Q is therefore an integer in [0,g]. It still determines A, because multiplication by Q recovers M(A). This injection into g+1 integers proves the bound. The same cancellation includes t=0: g=N and Q=1, so all binary masks remain allowed.

Mask divisibility is used only as a necessary condition. A mask with Q dividing M(A) need not have exact integer source sum zero: congruence modulo N cannot detect a nonzero multiple of N. The argument counts a superset of the integer-zero fibre and does not replace that fibre by a congruence class.

**Theorem 1.3 (Independent zero blocks consume exponentially many masks).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall blocks \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)\right),\; 3 \le k \Rightarrow \left(\left(\left(\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{mem}\left(A, blocks\right) \Rightarrow \operatorname{Nonempty}\left(A\right)\right) \land \left(\operatorname{PairwiseDisjoint}\left(blocks\right) \land \left(\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{mem}\left(A, blocks\right) \Rightarrow \operatorname{sum}\left(A, \operatorname{actualSource}\left(k, t\right)\right) = 0\right)\right)\right) \Rightarrow 2^{\operatorname{card}\left(blocks\right)} \le \operatorname{gcd}\left(t, 2^{k} - 1\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ZeroSumSubsets.disjoint_zero_blocks_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite family blocks of nonempty, pairwise disjoint physical-label finsets, assume each block has exact integer source sum zero. Then 2 raised to card(blocks) is at most gcd(t,N)+1. The family need not cover all labels; a partition of the entire source is a special case. The empty family is also allowed.

Every subfamily has a union with exact sum zero, by disjoint-union sum additivity. Distinct subfamilies have distinct unions: choose a label in a block belonging to one subfamily, and disjointness forces any block covering that label in the other subfamily to be the same block. Thus the 2^b subfamilies inject into Z. Combining this injection with the source count gives the restriction.

For a unit source g=1, this permits at most one nonempty zero block. More generally, any proposed splitting into b independent zero pieces must satisfy the exponential bound, even when source values repeat or have a short period. A construction based on freely choosing arbitrarily many independent integer-zero pieces therefore has an arithmetic obstruction. Existence of such a decomposition is not an assumption about the source in the count theorem.

The source motivation is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. These are necessary restrictions on exact zero subsets and decompositions. They do not construct a permutation with every prefix in [0,(N-1)/2]. The full all-source capacity-C conclusion remains open; collective splitting and interleaving with nonzero block charges is not controlled by this count. No claim of literature novelty is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ZeroSumSubsets.cyclic_binary_normal_form`
- Truth anchor: `D5/S3/Combinatorics/Circle/ZeroSumSubsets.disjoint_zero_blocks_bound`
- Truth anchor: `D5/S3/Combinatorics/Circle/ZeroSumSubsets.zero_subsets_card_le`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
