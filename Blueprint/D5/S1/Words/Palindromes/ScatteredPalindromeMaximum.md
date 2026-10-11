# Maximum Number of Scattered Palindromes

## Abstract

The sharp maximum of distinct scattered palindromes and its alphabet sizes.

Words are List A, and List.Sublist is scattered containment. Finite sets remove duplicate embeddings. The empty subword is excluded. Nat.div is integer division, so Nat.div (n+1) 2 represents ⌈n/2⌉. Every subtraction is truncated natural subtraction.

**Definition 1.1 (Distinct nonempty palindromic subsequences).**

$$\forall A \in Type,\; [\operatorname{DecidableEq}\left(A\right)], \forall w \in \operatorname{List}\left(A\right),\; \operatorname{spal}\left(w\right) = \operatorname{Finset}.filter\left(fun (u: \operatorname{List}\left(A\right)) \mapsto u \ne [] \land \operatorname{List}.reverse\left(u\right) = u, \operatorname{List}.toFinset\left(\operatorname{List}.sublists\left(w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.spal` (`✓ std3`).

*Citation.* K. Mahalingam, P. Pandoh (2021). *Counting scattered palindromes in a finite word*. URL: <https://arxiv.org/abs/2108.02729v1>.

*Commentary.*

Section 2, page 2: "We denote by PAL(w) and SPAL(w), the set of all non-empty palindromic factors, and scattered palindromic subwords of w, respectively." List.sublists enumerates scattered subwords; List.toFinset counts each word once. A palindrome satisfies List.reverse u = u.

**Definition 1.2 (Number of scattered palindromes).**

$$\forall A \in Type,\; [\operatorname{DecidableEq}\left(A\right)], \forall w \in \operatorname{List}\left(A\right),\; \operatorname{sp}\left(w\right) = \operatorname{Finset}.card\left(\operatorname{spal}\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.sp` (`✓ std3`).

*Citation.* K. Mahalingam, P. Pandoh (2021). *Counting scattered palindromes in a finite word*. URL: <https://arxiv.org/abs/2108.02729v1>.

*Commentary.*

Section 2, page 2: "Also, P(w)=|PAL(w)| and SP(w)=|SPAL(w)|." Page 3: "Throughout the paper, by the number of palindromic factors (resp. scattered palindromic subwords), we mean the number of non-empty distinct palindromic factors (resp. scattered palindromic subwords) in a word."

**Definition 1.3 (Number of distinct letters).**

$$\forall A \in Type,\; [\operatorname{DecidableEq}\left(A\right)], \forall w \in \operatorname{List}\left(A\right),\; \operatorname{alphabetSize}\left(w\right) = \operatorname{Finset}.card\left(\operatorname{List}.toFinset\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.alphabetSize` (`✓ std3`).

*Citation.* K. Mahalingam, P. Pandoh (2021). *Counting scattered palindromes in a finite word*. URL: <https://arxiv.org/abs/2108.02729v1>.

*Commentary.*

Section 2, page 2: "Alph(w) denotes the set of all the subwords of w of length 1." List.toFinset contains exactly the letters that occur in w, so its cardinality is the source's q.

**Definition 1.4 (The proposed sharp maximum).**

$$\forall n \in Nat,\; \operatorname{maxSP}\left(n\right) = if \operatorname{Nat}.mod\left(n, 2\right) = 1 then 3 \cdot 2^{\operatorname{Nat}.div\left(n + 1, 2\right) - 1} - 2 else (2^{\operatorname{Nat}.div\left(n, 2\right) + 1} - 2)$$

*Formalization.* `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.maxSP` (`✓ std3`).

*Citation.* K. Mahalingam, P. Pandoh (2021). *Counting scattered palindromes in a finite word*. URL: <https://arxiv.org/abs/2108.02729v1>.

*Commentary.*

Conjecture 5.6, page 18:

“The maximum number of scattered palindromic subwords in a word of length n is

3(2^{⌈n/2⌉−1})−2, if n is odd,

2^{n/2+1}−2, if n is even.

and this bound is achieved only when

q =

⌈n/2⌉, if n is odd

n/2 and n/2+1, if n is even.”

The two printed cases are encoded literally with natural integer division.

**Definition 1.5 (The extremal alphabet sizes).**

$$\forall n \in Nat,\; \forall q \in Nat,\; \operatorname{permittedQ}\left(n, q\right) \Leftrightarrow if \operatorname{Nat}.mod\left(n, 2\right) = 1 then q = \operatorname{Nat}.div\left(n + 1, 2\right) else (q = \operatorname{Nat}.div\left(n, 2\right) \lor q = \operatorname{Nat}.div\left(n, 2\right) + 1)$$

*Formalization.* `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.permittedQ` (`✓ std3`).

*Citation.* K. Mahalingam, P. Pandoh (2021). *Counting scattered palindromes in a finite word*. URL: <https://arxiv.org/abs/2108.02729v1>.

*Commentary.*

Conjecture 5.6, page 18:

“The maximum number of scattered palindromic subwords in a word of length n is

3(2^{⌈n/2⌉−1})−2, if n is odd,

2^{n/2+1}−2, if n is even.

and this bound is achieved only when

q =

⌈n/2⌉, if n is odd

n/2 and n/2+1, if n is even.”

The even case is a disjunction between two alphabet sizes.

**Definition 1.6 (Conjecture 5.6).**

$$\operatorname{claim}\left(\right) \Leftrightarrow \left(\left(\forall A \in Type,\; [\operatorname{DecidableEq}\left(A\right)], \forall w \in \operatorname{List}\left(A\right),\; \operatorname{sp}\left(w\right) \le \operatorname{maxSP}\left(\operatorname{List}.length\left(w\right)\right)\right) \land \left(\left(\forall n \in Nat,\; \forall q \in Nat,\; 1 \le n \Rightarrow \left(\operatorname{permittedQ}\left(n, q\right) \Rightarrow \left(\exists w \in \operatorname{List}\left(Nat\right),\; \operatorname{List}.length\left(w\right) = n \land \left(\operatorname{alphabetSize}\left(w\right) = q \land \operatorname{sp}\left(w\right) = \operatorname{maxSP}\left(n\right)\right)\right)\right)\right) \land \left(\forall A \in Type,\; [\operatorname{DecidableEq}\left(A\right)], \forall w \in \operatorname{List}\left(A\right),\; 1 \le \operatorname{List}.length\left(w\right) \Rightarrow \left(\operatorname{sp}\left(w\right) = \operatorname{maxSP}\left(\operatorname{List}.length\left(w\right)\right) \Rightarrow \operatorname{permittedQ}\left(\operatorname{List}.length\left(w\right), \operatorname{alphabetSize}\left(w\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.claim` (`✓ std3`).

*Citation.* K. Mahalingam, P. Pandoh (2021). *Counting scattered palindromes in a finite word*. URL: <https://arxiv.org/abs/2108.02729v1>.

*Commentary.*

Conjecture 5.6, page 18:

“The maximum number of scattered palindromic subwords in a word of length n is

3(2^{⌈n/2⌉−1})−2, if n is odd,

2^{n/2+1}−2, if n is even.

and this bound is achieved only when

q =

⌈n/2⌉, if n is odd

n/2 and n/2+1, if n is even.”

The encoding states a universal upper bound, attainment for every positive length and every permitted alphabet size, and necessity for every extremal nonempty word. Natural-number letters suffice for attainment; the bound and necessity quantify over every decidable alphabet.

**Theorem 1.7 (The conjecture holds).**

$$\operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.result` (`✓ std3`). ∎

*Resolves.* `Problems/mahalingam-pandoh-2021-scattered-palindrome-maximum` (proved) by `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mahalingam-pandoh-2021-scattered-palindrome-maximum","declaration_gid":"D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Mahalingam, P. Pandoh (2021). *Counting scattered palindromes in a finite word*. URL: <https://arxiv.org/abs/2108.02729v1>.

*Commentary.*

Partition by the outer letter. A letter occurring once contributes one palindrome; a repeated letter contributes two plus the number of palindromes between its first and last occurrences. The convex endpoint matching estimate and the recurrence maxSP(n+2)=2 maxSP(n)+2 yield a residue bound by strong induction. Equality forces the residual length k to satisfy maxSP(k)=k and hence k≤2, and forces all repeated letters to occur exactly twice. For each permitted q, start with k distinct letters, where k is zero, one or two, and add r fresh matching outer pairs. The resulting word has length 2r+k, alphabet size r+k and count maxSP(2r+k). This constructs extremizers and restricts their alphabet sizes; it does not classify all extremal words or determine the maximum at every fixed alphabet size below half the length.

## References

- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.alphabetSize`
- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.claim`
- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.maxSP`
- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.permittedQ`
- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.result`
- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.sp`
- Truth anchor: `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.spal`
- Dependency: [D5/S1/Words/Palindromes/ScatteredPalindromeMatching](ScatteredPalindromeMatching.md)
