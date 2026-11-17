# Ianakiev's shortest palindromes of factorial run lengths

## Abstract

The literal factorial run lengths have exactly the shortest-palindrome first occurrences specified by Ianakiev.

All indices and lengths are natural numbers. F has offset zero and is the least positive factorial index. The constant runs include its initial singleton. B and the source's third sequence P use positive indices. The first value P(1)=1 is stipulated; the minimum over palindrome lengths at least two applies only at indices at least two. A has offset zero. Every palindrome is a contiguous block.

**Definition 1.1 (Least positive factorial indices).**

$$\forall m \in \mathrm{Nat},\; (1 \le F\left(m\right)) \land ((2^{m} \mid F\left(m\right)!) \land (\forall h \in \mathrm{Nat},\; ((1 \le h) \land (2^{m} \mid h!)) \Rightarrow (F\left(m\right) \le h)))$$

*Formalization.* `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.F` (`✓ std3`).

*Citation.* Ivan N. Ianakiev; The OEIS Foundation Inc. (2019). *OEIS A094373: Ianakiev's shortest-palindrome and first-occurrence conjecture*. URL: <https://oeis.org/A094373>.

*Commentary.*

For every exponent m, F(m) is the least positive h with 2^m dividing h!. Such an h exists because 2^m divides its own factorial. In particular F(0)=1.

**Definition 1.2 (Successive maximal constant runs).**

$$(S\left(0\right) = 0) \land (\forall r \in \mathrm{Nat},\; ((S\left(r\right) < S\left(r + 1\right)) \land (F\left(S\left(r + 1\right)\right) \ne F\left(S\left(r\right)\right))) \land (\forall m \in \mathrm{Nat},\; ((S\left(r\right) < m) \land (F\left(m\right) \ne F\left(S\left(r\right)\right))) \Rightarrow (S\left(r + 1\right) \le m)))$$

*Formalization.* `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.S` (`✓ std3`).

*Citation.* Ivan N. Ianakiev; The OEIS Foundation Inc. (2019). *OEIS A094373: Ianakiev's shortest-palindrome and first-occurrence conjecture*. URL: <https://oeis.org/A094373>.

*Commentary.*

S(0)=0. Each following boundary is the least strictly later exponent where F changes. Minimality makes F constant throughout the intervening run, and membership makes the next run start with a different value. Every such boundary exists.

**Definition 1.3 (Lengths of the actual runs).**

$$\forall i \in \mathrm{Nat},\; B\left(i\right) = S\left(i\right) - S\left(i - 1\right)$$

*Formalization.* `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.B` (`✓ std3`).

*Citation.* Oliver Kullmann; Xishun Zhao (2015). *Parameters for minimal unsatisfiability: Smarandache primitive numbers and full clauses*. URL: <https://arxiv.org/abs/1505.02318v2>.

*Commentary.*

At positive i, B(i)=S(i)-S(i-1). The initial value is B(1)=1. For r positive, B(r+1)=1+v2(r). This follows from the actual factorial minima and boundaries: S(r+1)=v2((2r)!)+1 and F(S(r+1))=2(r+1). The positive plateau identification is classical; the initial singleton retains the least-positive convention.

**Definition 1.4 (Contiguous reflection).**

$$\forall i \in \mathrm{Nat},\; \forall L \in \mathrm{Nat},\; (Pal\left(i, L\right)) \Leftrightarrow (\forall t \in \mathrm{Nat},\; (t < L) \Rightarrow (B\left(i + t\right) = B\left(i + L - 1 - t\right)))$$

*Formalization.* `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.Pal` (`✓ std3`).

*Citation.* Ivan N. Ianakiev; The OEIS Foundation Inc. (2019). *OEIS A094373: Ianakiev's shortest-palindrome and first-occurrence conjecture*. URL: <https://oeis.org/A094373>.

*Commentary.*

The indices paired by reflection are i+t and i+L-1-t for every t<L. Length at least two is a separate admissibility condition.

**Definition 1.5 (The shortest admissible length).**

$$(P\left(1\right) = 1) \land (\forall i \in \mathrm{Nat},\; (2 \le i) \Rightarrow (((2 \le P\left(i\right)) \land (Pal\left(i, P\left(i\right)\right))) \land (\forall L \in \mathrm{Nat},\; ((2 \le L) \land (Pal\left(i, L\right))) \Rightarrow (P\left(i\right) \le L))))$$

*Formalization.* `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.P` (`✓ std3`).

*Citation.* Ivan N. Ianakiev; The OEIS Foundation Inc. (2019). *OEIS A094373: Ianakiev's shortest-palindrome and first-occurrence conjecture*. URL: <https://oeis.org/A094373>.

*Commentary.*

The admissible-length set is nonempty at every i at least two. P(i) is its least member, rather than a definition by a proposed closed formula. Index zero is outside the source's third sequence.

**Definition 1.6 (The present OEIS sequence).**

$$(A\left(0\right) = 1) \land (\forall e \in \mathrm{Nat},\; A\left(e + 1\right) = 2^{e} + 1)$$

*Formalization.* `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.A` (`✓ std3`).

*Citation.* Ivan N. Ianakiev; The OEIS Foundation Inc. (2019). *OEIS A094373: Ianakiev's shortest-palindrome and first-occurrence conjecture*. URL: <https://oeis.org/A094373>.

*Commentary.*

The formula preceding Ianakiev's comment gives A(0)=1 and A(e+1)=2^e+1. The sequence A is strictly increasing.

**Definition 1.7 (First appearances).**

$$\forall i \in \mathrm{Nat},\; (First\left(i\right)) \Leftrightarrow (\forall j \in \mathrm{Nat},\; ((1 \le j) \land (j < i)) \Rightarrow (P\left(j\right) \ne P\left(i\right)))$$

*Formalization.* `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.First` (`✓ std3`).

*Citation.* Ivan N. Ianakiev; The OEIS Foundation Inc. (2019). *OEIS A094373: Ianakiev's shortest-palindrome and first-occurrence conjecture*. URL: <https://oeis.org/A094373>.

*Commentary.*

A value first appears at i precisely when every earlier positive position has a different value.

**Definition 1.8 (The complete two-clause assertion).**

$$(claim) \Leftrightarrow ((\forall m \in \mathrm{Nat},\; (1 \le F\left(m\right)) \land ((2^{m} \mid F\left(m\right)!) \land (\forall h \in \mathrm{Nat},\; ((1 \le h) \land (2^{m} \mid h!)) \Rightarrow (F\left(m\right) \le h)))) \land (((S\left(0\right) = 0) \land (\forall r \in \mathrm{Nat},\; ((S\left(r\right) < S\left(r + 1\right)) \land (F\left(S\left(r + 1\right)\right) \ne F\left(S\left(r\right)\right))) \land (\forall m \in \mathrm{Nat},\; ((S\left(r\right) < m) \land (F\left(m\right) \ne F\left(S\left(r\right)\right))) \Rightarrow (S\left(r + 1\right) \le m)))) \land ((P\left(1\right) = 1) \land ((\forall i \in \mathrm{Nat},\; (2 \le i) \Rightarrow (((2 \le P\left(i\right)) \land (Pal\left(i, P\left(i\right)\right))) \land (\forall L \in \mathrm{Nat},\; ((2 \le L) \land (Pal\left(i, L\right))) \Rightarrow (P\left(i\right) \le L)))) \land ((StrictMono\left(A\right)) \land ((\forall i \in \mathrm{Nat},\; (1 \le i) \Rightarrow ((First\left(i\right)) \Leftrightarrow (\exists m \in \mathrm{Nat},\; i = A\left(m\right)))) \land (\forall m \in \mathrm{Nat},\; (2 \le m) \Rightarrow (P\left(A\left(m - 1\right)\right) = A\left(m\right)))))))))$$

*Formalization.* `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.claim` (`✓ std3`).

*Citation.* Ivan N. Ianakiev; The OEIS Foundation Inc. (2019). *OEIS A094373: Ianakiev's shortest-palindrome and first-occurrence conjecture*. URL: <https://oeis.org/A094373>.

*Commentary.*

The assertion includes existence and minimality of every factorial index, every successive boundary, and every admissible palindrome minimum. Its two conclusions give the entire increasing first-occurrence list and the value at every specified A-position. Neither conclusion is restricted to a finite prefix.

**Theorem 1.9 (All minima and both conclusions).**

$$(\forall m \in \mathrm{Nat},\; (1 \le F\left(m\right)) \land ((2^{m} \mid F\left(m\right)!) \land (\forall h \in \mathrm{Nat},\; ((1 \le h) \land (2^{m} \mid h!)) \Rightarrow (F\left(m\right) \le h)))) \land (((S\left(0\right) = 0) \land (\forall r \in \mathrm{Nat},\; ((S\left(r\right) < S\left(r + 1\right)) \land (F\left(S\left(r + 1\right)\right) \ne F\left(S\left(r\right)\right))) \land (\forall m \in \mathrm{Nat},\; ((S\left(r\right) < m) \land (F\left(m\right) \ne F\left(S\left(r\right)\right))) \Rightarrow (S\left(r + 1\right) \le m)))) \land ((P\left(1\right) = 1) \land ((\forall i \in \mathrm{Nat},\; (2 \le i) \Rightarrow (((2 \le P\left(i\right)) \land (Pal\left(i, P\left(i\right)\right))) \land (\forall L \in \mathrm{Nat},\; ((2 \le L) \land (Pal\left(i, L\right))) \Rightarrow (P\left(i\right) \le L)))) \land ((StrictMono\left(A\right)) \land ((\forall i \in \mathrm{Nat},\; (1 \le i) \Rightarrow ((First\left(i\right)) \Leftrightarrow (\exists m \in \mathrm{Nat},\; i = A\left(m\right)))) \land (\forall m \in \mathrm{Nat},\; (2 \le m) \Rightarrow (P\left(A\left(m - 1\right)\right) = A\left(m\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a094373-ianakiev-shortest-ruler-palindrome` (proved) by `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a094373-ianakiev-shortest-ruler-palindrome","declaration_gid":"D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan N. Ianakiev; The OEIS Foundation Inc. (2019). *OEIS A094373: Ianakiev's shortest-palindrome and first-occurrence conjecture*. URL: <https://oeis.org/A094373>.

*Acknowledgement.* Oliver Kullmann; Xishun Zhao (2015). *Parameters for minimal unsatisfiability: Smarandache primitive numbers and full clauses*. URL: <https://arxiv.org/abs/1505.02318v2>.

*Commentary.*

Write j=i-1, k=v2(j), and q=2^k for i at least two. Equal endpoint values in a palindrome force its endpoint indices to have equal valuations. Their odd quotients differ by at least two, so every admissible length is at least 2q+1. The center c=j+q is divisible by 2^(k+1). For each positive s at most q, v2(s) is at most k, and the unequal-valuation addition law gives v2(c-s)=v2(c+s). This supplies the full palindrome of length 2q+1, proving P(i)=2^(v2(i-1)+1)+1. The least positive integer of valuation k is 2^k. Thus each later value first occurs at 2^k+1, while P(1)=1 is the initial first occurrence. At m at least two, substituting i=A(m-1) gives P(i)=A(m). The argument is specific to the binary factorial runs; no arbitrary-prime analogue is asserted.

## References

- Truth anchor: `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.A`
- Truth anchor: `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.B`
- Truth anchor: `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.F`
- Truth anchor: `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.First`
- Truth anchor: `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.P`
- Truth anchor: `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.Pal`
- Truth anchor: `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.S`
- Truth anchor: `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.claim`
- Truth anchor: `D5/S1/Words/Palindromes/IanakievShortestRulerPalindrome.result`
