# Joint legal realization over a finite coefficient ring

## Abstract

A single actual Boolean word realizes every compatible polynomial observation over ZMod d, with its entire length, zero tail and quotient phase accounted for.

Fix natural numbers k and d at least two, a positive natural number r, and an injective family a from Fin r to the natural numbers with every a_i at least two. Put R = ZMod d, Phi_b = X^b minus the sum of X^j for 0 <= j < b, F = the product of Phi_(a_i), and D = the sum of a_i. Let A = AdjoinRoot F, let x be the class of X in A, and let L be orderOf x. For an actual word w from Fin n to Bool, P_w is the sum of the monomials w(i)X^i, where false means zero and true means one. The length n counts all leading, internal and trailing zero bits.

For one common polynomial P over R, write O(P)_i for its monic remainder modulo Phi_(a_i). Write Legal_k(n,w) for DBonacciAdmissible k n w, the original scanner predicate forbidding k consecutive true bits. Write Tail_k(n,w) for the assertion that w(i) is false at every position i in Fin n with n-k <= i. In the displayed existence clause, n is a natural number and w is a function from Fin n to Bool. The same n and w satisfy all five realization clauses together. The set W_k consists of all such finite scanner-legal words; the final image equality is an additional assertion about that set.

**Theorem 1.1 (One shared word, a counted budget, a zero tail and trivial phase).**

$$\begin{aligned}\operatorname{card}(A) = d^{D} \land \operatorname{IsUnit}(x) \land 1\leq L\leq d^{D},\\\exists T\in\mathbb{N}: L\mid T \land D+k\leq T,\\\forall T\in\mathbb{N}, (L\mid T \land D+k\leq T) \Rightarrow \forall P\in R[X], \exists n,w:(\\\operatorname{Legal}_{k}(n,w) \land O(P_{w})=O(P) \land k\leq n\leq T(D(d-1)+1) \land\\\operatorname{Tail}_{k}(n,w) \land x^{n}=1),\\O(R[X])=\{O(P_{w}) \mid w\in W_{k}\}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciJointLegalRealization.kbonacci_joint_legal_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each Phi_(a_i) is monic of degree a_i and constant coefficient -1. Thus F is monic of degree D with constant coefficient (-1)^r. Its monic power basis identifies A with D coefficient slots, giving cardinality d^D. The identity X divX(F) + F(0) = F shows that x times an element of A is the unit -F(0), so x is a unit even when d is composite. Its positive finite order is bounded by the cardinality of A. The multiple L(D+k) provides a suitable T.

For any suitable T and any P, reduce P by monic division modulo F. Let c_j in {0,...,d-1} be the natural representative of the jth coefficient, for j < D, and put N = sum_j c_j. Enumerate the disjoint coefficient-copy slots (j,u) with u < c_j as s = 0,...,N-1. Let j_s be the first coordinate. Define n = T(N+1) and set exactly the positions (s+1)T+j_s to true.

These positions are distinct and ordered positions differ by more than k. Consequently no two true positions are adjacent and the word avoids every block of k true bits. Each position plus k lies below n, so all final k bits are false. Since x^T = 1, the contribution of a placed bit is x^(j_s). Reindexing the distinct support counts every coefficient copy exactly once, hence the actual word polynomial equals P in A. Every Phi_(a_i) divides F, so all coordinate remainders agree for this same word.

The coefficient bound gives N <= D(d-1), hence the stated length budget. The length n is a multiple of T and has phase x^n = 1. When N is zero, the construction is the all-false word of length T. Applying the construction with a suitable T gives the forward image inclusion; the reverse inclusion uses the word polynomial itself as a common polynomial. No coprimality of the probe polynomials is required. The image equality is over unrestricted finite lengths, concerns compatible arrays, and makes no assertion of recovery or of a shortest budget.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciJointLegalRealization.kbonacci_joint_legal_realization`
- Dependency: [D5/S1/Words/ClosedRunStarts](../ClosedRunStarts.md)
