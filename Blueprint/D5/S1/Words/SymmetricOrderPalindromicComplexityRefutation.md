# Transient Letters and Palindromic Complexity

## Abstract

A four-letter path language has symmetric orders and no connection, but only three palindromes of length three.

Words are finite lists over Fin k. A permutation sigma gives the departure order by sigma a < sigma b and the arrival order by sigma b < sigma a. Thus the two orders are strict, total and symmetric. Section 2, page 5: "A pair of orders (<D, <A) is symmetric if <A is the reverse of <D, i.e. a <A b if and only if b <D a for all distinct letters a, b ∈ A."

**Definition 1.1 (Factors remain in the language).**

$$\forall k \in Nat,\; \forall K \in Set\left(List\left(Fin\left(k\right)\right)\right),\; IsFactorial\left(K\right) \Leftrightarrow \left(\forall w \in List\left(Fin\left(k\right)\right),\; w\in K \Rightarrow \left(\forall u \in List\left(Fin\left(k\right)\right),\; \operatorname{List}.IsInfix\left(u, w\right) \Rightarrow u\in K\right)\right)$$

*Formalization.* `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.IsFactorial` (`✓ std3`).

*Citation.* Sébastien Ferenczi, Luca Q. Zamboni (2025). *Clustering, order conditions, and languages of interval exchanges*. URL: <https://arxiv.org/abs/2507.17370v2>.

*Commentary.*

Section 1, page 4: "By a language L over A we mean a factorial language: a collection of sets (Ln)n≥0 where the only element of L0 is the empty word ε, and where each Ln for n ≥ 1 consists of words of length n, such that each v ∈ Ln+1 can be written in the form v = au = u′b with a, b ∈ A and u, u′ ∈ Ln." IsFactorial encodes closure under every contiguous factor using List.IsInfix. The counterexample contains the empty word; UsesAllLetters fixes its alphabet.

**Definition 1.2 (Two-sided extendability).**

$$\forall k \in Nat,\; \forall K \in Set\left(List\left(Fin\left(k\right)\right)\right),\; IsExtendable\left(K\right) \Leftrightarrow \left(\forall w \in List\left(Fin\left(k\right)\right),\; w\in K \Rightarrow \left(\left(\exists a \in Fin\left(k\right),\; \operatorname{List}.cons\left(a, w\right)\in K\right) \land \left(\exists b \in Fin\left(k\right),\; (w++[b])\in K\right)\right)\right)$$

*Formalization.* `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.IsExtendable` (`✓ std3`).

*Citation.* Sébastien Ferenczi, Luca Q. Zamboni (2025). *Clustering, order conditions, and languages of interval exchanges*. URL: <https://arxiv.org/abs/2507.17370v2>.

*Commentary.*

Section 1, page 4: "Except when otherwise mentioned, all our languages are tacitly assumed to be extendable: for each v ∈ Ln there exists a,b ∈ A with av,vb ∈ Ln+1." Left extension is List.cons; right extension appends a singleton.

**Definition 1.3 (The alphabet has k letters).**

$$\forall k \in Nat,\; \forall K \in Set\left(List\left(Fin\left(k\right)\right)\right),\; UsesAllLetters\left(K\right) \Leftrightarrow \left(\forall a \in Fin\left(k\right),\; [a]\in K\right)$$

*Formalization.* `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.UsesAllLetters` (`✓ std3`).

*Citation.* Sébastien Ferenczi, Luca Q. Zamboni (2025). *Clustering, order conditions, and languages of interval exchanges*. URL: <https://arxiv.org/abs/2507.17370v2>.

*Commentary.*

Conjecture 1, page 14: "A language on k letters satisfying a symmetric order condition and with no connection has palindromic complexity 1 for n even, k for n odd." Every element of Fin k occurs as a singleton. Consequently the alphabet has exactly k letters, rather than merely being contained in Fin k.

**Definition 1.4 (The symmetric order condition).**

$$\forall k \in Nat,\; \forall K \in Set\left(List\left(Fin\left(k\right)\right)\right),\; \forall sigma \in \operatorname{Equiv}.Perm\left(Fin\left(k\right)\right),\; SymOrderCondition\left(K, sigma\right) \Leftrightarrow \left(\forall a \in Fin\left(k\right),\; \forall b \in Fin\left(k\right),\; \forall c \in Fin\left(k\right),\; \forall d \in Fin\left(k\right),\; \forall x \in List\left(Fin\left(k\right)\right),\; \operatorname{List}.cons\left(a, (x++[b])\right)\in K \Rightarrow \left(\operatorname{List}.cons\left(c, (x++[d])\right)\in K \Rightarrow \left(a \ne c \Rightarrow \left(b \ne d \Rightarrow \left(sigma\left(c\right) < sigma\left(a\right) \Leftrightarrow sigma\left(b\right) < sigma\left(d\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.SymOrderCondition` (`✓ std3`).

*Citation.* Sébastien Ferenczi, Luca Q. Zamboni (2025). *Clustering, order conditions, and languages of interval exchanges*. URL: <https://arxiv.org/abs/2507.17370v2>.

*Commentary.*

Definition 6, page 6: "A language L (extendable or not) satisfies the order condition for the pair of orders (<D,<A) if whenever axb, cxd ∈ L with a, b,c,d ∈ A, x ∈ A* (possibly empty), a ≠ c and b ≠ d, then a <A c if and only if b <D d. The order condition is called the symmetric order condition if the pair of orders (<D,<A) is symmetric." The middle word x may be empty. The reversed arrival order explains the comparison sigma c < sigma a.

**Definition 1.5 (Bispecial words).**

$$\forall k \in Nat,\; \forall K \in Set\left(List\left(Fin\left(k\right)\right)\right),\; \forall w \in List\left(Fin\left(k\right)\right),\; IsBispecial\left(K, w\right) \Leftrightarrow \left(\left(\exists a1 \in Fin\left(k\right),\; \exists a2 \in Fin\left(k\right),\; a1 \ne a2 \land \left(\operatorname{List}.cons\left(a1, w\right)\in K \land \operatorname{List}.cons\left(a2, w\right)\in K\right)\right) \land \left(\exists b1 \in Fin\left(k\right),\; \exists b2 \in Fin\left(k\right),\; b1 \ne b2 \land \left((w++[b1])\in K \land (w++[b2])\in K\right)\right)\right)$$

*Formalization.* `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.IsBispecial` (`✓ std3`).

*Citation.* Sébastien Ferenczi, Luca Q. Zamboni (2025). *Clustering, order conditions, and languages of interval exchanges*. URL: <https://arxiv.org/abs/2507.17370v2>.

*Commentary.*

Section 1, page 4: "A word w in L is right special (resp. left special) if it has more than one right extension wx (resp. left extension xw) in L, with x in A. If w is both right special and left special, then w is bispecial." The two existential pairs state that the one-letter extensions are distinct. For a factorial language these extensions also imply w ∈ L.

**Definition 1.6 (No connection).**

$$\forall k \in Nat,\; \forall K \in Set\left(List\left(Fin\left(k\right)\right)\right),\; \forall sigma \in \operatorname{Equiv}.Perm\left(Fin\left(k\right)\right),\; NoConnection\left(K, sigma\right) \Leftrightarrow \left(\forall w \in List\left(Fin\left(k\right)\right),\; IsBispecial\left(K, w\right) \Rightarrow \left(\forall a \in Fin\left(k\right),\; \forall ap \in Fin\left(k\right),\; \forall b \in Fin\left(k\right),\; \forall bp \in Fin\left(k\right),\; \left(sigma\left(ap\right) < sigma\left(a\right) \land \left(\forall z \in Fin\left(k\right),\; \neg (sigma\left(ap\right) < sigma\left(z\right) \land sigma\left(z\right) < sigma\left(a\right))\right)\right) \Rightarrow \left(\left(sigma\left(b\right) < sigma\left(bp\right) \land \left(\forall z \in Fin\left(k\right),\; \neg (sigma\left(b\right) < sigma\left(z\right) \land sigma\left(z\right) < sigma\left(bp\right))\right)\right) \Rightarrow \left(\operatorname{List}.cons\left(a, (w++[b])\right)\in K \Rightarrow \left(\operatorname{List}.cons\left(ap, (w++[bp])\right)\in K \Rightarrow \left(\neg (\operatorname{List}.cons\left(a, (w++[bp])\right)\in K) \Rightarrow \left(\neg (\operatorname{List}.cons\left(ap, (w++[b])\right)\in K) \Rightarrow False\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.NoConnection` (`✓ std3`).

*Citation.* Sébastien Ferenczi, Luca Q. Zamboni (2025). *Clustering, order conditions, and languages of interval exchanges*. URL: <https://arxiv.org/abs/2507.17370v2>.

*Commentary.*

Definition 7, page 6: "If a language L on an alphabet A satisfies the order condition for (<D,<A), a bispecial word w has a connection if there are letters a <A a′, consecutive in the order <A, letters b <D b′, consecutive in the order <D, such that awb and a′wb′ are in L, and neither awb′ nor a′wb is in L." The letters ap and bp encode a′ and b′. Consecutiveness means strict comparison with no intervening letter. Arrival consecutiveness is reversed, so sigma ap < sigma a; departure consecutiveness is sigma b < sigma bp.

**Definition 1.7 (Palindromic complexity).**

$$\forall k \in Nat,\; \forall K \in Set\left(List\left(Fin\left(k\right)\right)\right),\; \forall n \in Nat,\; palComplexity\left(K, n\right) = \operatorname{Set}.ncard\left(\{w: List\left(Fin\left(k\right)\right) \mid w\in K \land \left(\operatorname{List}.length\left(w\right) = n \land \operatorname{List}.reverse\left(w\right) = w\right)\}\right)$$

*Formalization.* `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.palComplexity` (`✓ std3`).

*Citation.* Sébastien Ferenczi, Luca Q. Zamboni (2025). *Clustering, order conditions, and languages of interval exchanges*. URL: <https://arxiv.org/abs/2507.17370v2>.

*Commentary.*

Introduction, page 3: "We give also some estimates on the palindromic complexity of L, i.e., the number of palindromes in L of each given length n." A palindrome satisfies List.reverse w = w. Set.ncard counts the set of such words of length n; this set is finite because Fin k is finite. The empty word contributes one at length zero whenever it belongs to the language.

**Definition 1.8 (Conjecture 1).**

$$claim \Leftrightarrow \left(\forall k \in Nat,\; \forall K \in Set\left(List\left(Fin\left(k\right)\right)\right),\; \forall sigma \in \operatorname{Equiv}.Perm\left(Fin\left(k\right)\right),\; IsFactorial\left(K\right) \Rightarrow \left(IsExtendable\left(K\right) \Rightarrow \left(UsesAllLetters\left(K\right) \Rightarrow \left(SymOrderCondition\left(K, sigma\right) \Rightarrow \left(NoConnection\left(K, sigma\right) \Rightarrow \left(\forall n \in Nat,\; palComplexity\left(K, n\right) = if Even\left(n\right) then 1 else k\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.claim` (`✓ std3`).

*Citation.* Sébastien Ferenczi, Luca Q. Zamboni (2025). *Clustering, order conditions, and languages of interval exchanges*. URL: <https://arxiv.org/abs/2507.17370v2>.

*Commentary.*

Section 4, Conjecture 1, page 14: "A language on k letters satisfying a symmetric order condition and with no connection has palindromic complexity 1 for n even, k for n odd." The encoding quantifies over every natural k, every K : Set (List (Fin k)), every sigma : Equiv.Perm (Fin k), and every natural n, including zero. The hypotheses state factoriality, two-sided extendability, use of all letters, the symmetric order condition, and absence of connections. No recurrence or closure under reversal is assumed.

**Theorem 1.9 (A four-letter counterexample).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ferenczi-zamboni-2025-palindromic-complexity-no-connection` (refuted) by `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ferenczi-zamboni-2025-palindromic-complexity-no-connection","declaration_gid":"D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sébastien Ferenczi, Luca Q. Zamboni (2025). *Clustering, order conditions, and languages of interval exchanges*. URL: <https://arxiv.org/abs/2507.17370v2>.

*Commentary.*

Use the graph on Fin 4 with edges 0 → 3, 1 → 3, 2 → j for every j, and 3 → 0. Its finite paths form a factorial language containing the empty word. Vertex 2 precedes every vertex, and every vertex has a successor, so the language extends on both sides and uses all four letters. Distinct incoming edges force their common target into {0,3}; subsequent vertices stay in the deterministic two-cycle. Hence no nonempty word is bispecial. The empty word satisfies the symmetric order condition and has no connection, as verified from the edge rows. The palindromes of length three are exactly [2,2,2], [0,3,0] and [3,0,3]. Thus palComplexity at three is three, while the conjecture requires four. The source vertices 1,2,3,4 correspond to 0,1,2,3.

## References

- Truth anchor: `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.IsBispecial`
- Truth anchor: `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.IsExtendable`
- Truth anchor: `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.IsFactorial`
- Truth anchor: `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.NoConnection`
- Truth anchor: `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.SymOrderCondition`
- Truth anchor: `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.UsesAllLetters`
- Truth anchor: `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.claim`
- Truth anchor: `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.palComplexity`
- Truth anchor: `D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.result`
