# Murthy's A077739 Classification

## Abstract

The complete decimal prefix, suffix, divisibility and digit-sum classification in OEIS A077739.

OEIS A077739 defines a(n) as the smallest positive multiple of n beginning and ending with the usual decimal expansion of n and having digit sum n, or zero if no such number exists. The source conjecture says that the zero indices are exactly 11, 17 and 19. The statement below concerns every natural n at least one; there is no bound on the value or decimal length of the multiple. Decimal expansions have no leading zeros, may have interior zeros, and their prescribed ends may overlap.

Generality I records the concrete decimal certificate rows consumed below 1000. The symbolic tail and final assertion remain unbounded in n and witness length; no classification for arbitrary numeral bases is asserted.

Write s(x) for the sum of Nat.digits 10 x and w(x) for that list's length. A positive N begins in n exactly when N=n times 10^k+r for some k,r with 0<=r<10^k. It ends in n exactly when N modulo 10^w(n) equals n. These conditions allow k=0 and do not require the two ends to be disjoint. The predicate Witness conjoins positivity, n dividing N, s(N)=n, and these two positional conditions. Admissible(n) means that some N satisfies Witness(n,N).

**Definition 1.1 (Decimal digit sum).**

$$\forall n \in Nat,\; digitSum\left(n\right) = sumDigits10\left(n\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/MurthyA077739Classification.digitSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Amarnath Murthy (2002). *OEIS A077739, Smallest multiple of n beginning and ending in n and having a digit sum of n, or 0 if no such number exists*. URL: <https://oeis.org/A077739>.

*Commentary.*

Nat.digits lists digits from least to most significant; their sum is independent of that order.

**Definition 1.2 (The source's least-or-zero sequence).**

$$\forall n \in Nat,\; a\left(n\right) = sInf\left(positiveWitnessSet\left(n\right)\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/MurthyA077739Classification.a` (`✓ std3`).

*Citation.* Amarnath Murthy (2002). *OEIS A077739, Smallest multiple of n beginning and ending in n and having a digit sum of n, or 0 if no such number exists*. URL: <https://oeis.org/A077739>.

*Commentary.*

The natural infimum of the witness set is its least member when nonempty, and zero when empty. Every member is positive. Nat.sInf_mem and Nat.sInf_eq_zero therefore prove a(n)=0 exactly when Admissible(n) is false; this is the well-ordering bridge from the existence construction to the actual source sequence.

**Theorem 1.3 (The complete least-or-zero classification).**

$$\forall n \in Nat,\; 1 \le n \Rightarrow \left(a\left(n\right) = 0 \Leftrightarrow \left(n = 11 \lor \left(n = 17 \lor n = 19\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/MurthyA077739Classification.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a077739-murthy-zero-indices` (proved) by `D5/S1/Digit/Admissibility/MurthyA077739Classification.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a077739-murthy-zero-indices","declaration_gid":"D5/S1/Digit/Admissibility/MurthyA077739Classification.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Amarnath Murthy (2002). *OEIS A077739, Smallest multiple of n beginning and ending in n and having a digit sum of n, or 0 if no such number exists*. URL: <https://oeis.org/A077739>.

*Commentary.*

Concatenating multiples of n preserves divisibility and adds digit sums. Start and end with a literal n block. For L with n<=10^L, the multiple B_L=n(10^L-1) has digit sum 9L: write it as (n-1)10^L+(10^L-n), with the lower block padded to L digits. Its complement identity follows by decimal recursion. For n>=1000, put d=w(n)>=4. Induction gives 9d^2+81d<=10^(d-1)<=n, and s(n)<=9d. Congruence modulo nine gives the integer q=(n-10s(n))/9>=d(d-1). Set b=q mod d and a=floor(q/d)-b; then q=ad+b(d+1). The blocks n, eight additional copies of n, a copies of B_d, b copies of B_(d+1), and a final n give a positive witness with digit sum 10s(n)+9ad+9b(d+1)=n. This is an unbounded symbolic construction. For 10<=n<1000 outside the three exceptions, the retained certificate records multiplicities of blocks jn. Kernel reduction checks that their digit sums total n-2s(n), and the general block construction supplies the witness. The certificate arrays MurthyA077739CertificateLow.entries and MurthyA077739CertificateHigh.entries retain indices 0..499 and 500..999; certificateData appends them in that order. The certificate uses j<=195 and 1643 multiplier-count pairs; n=18 uses an empty middle. For 1<=n<=9, take N=n. No certificate failure proves nonexistence. For 11, the suffix forces N=11+100q, s(q)=9, and 11 dividing q. Evaluating q's digits at -1 yields a multiple of 11 between -9 and 9 which is odd, a contradiction. For 17 and 19, a zero-length appended block gives digit sum 8 or 10; a one-digit overlap is impossible. With disjoint ends, write N=n10^(k+2)+100M+n. For 19 the ends already contribute 20. For 17 the middle has sum one, so M=10^j; divisibility would make 17 divide a power of ten, contradicting primality. These arguments cover all lengths and all overlaps. Combining existence, the three exclusions, and the infimum bridge proves the whole source claim. No minimal witness values beyond existence are asserted. The public OEIS source still presents this as a conjecture in the supplied revision. The bounded repository, pinned Mathlib and public-source search located no full classification in its examined scope; third-party coverage is incomplete and this document makes no priority or exhaustive novelty claim. The general certificate soundness theorem consumes the finite data, and the terminal classification consumes both that bounded branch and the symbolic tail; the table alone is not the result. The source-equivalence Reg registration retains exact source reconstruction, lawful template enrollment, whole-family variation and sensitivity, and actual observational dependence. Its continuation is unknown, which does not assert undecidability. The result does not compute least positive witnesses, classify other bases, or settle new external questions. A qualified successor remains pending literature screening.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/MurthyA077739Classification.a`
- Truth anchor: `D5/S1/Digit/Admissibility/MurthyA077739Classification.digitSum`
- Truth anchor: `D5/S1/Digit/Admissibility/MurthyA077739Classification.result`
- Dependency: [D5/S1/Digit/Admissibility/MurthyA077739CertificateHigh](MurthyA077739CertificateHigh.md)
- Dependency: [D5/S1/Digit/Admissibility/MurthyA077739CertificateLow](MurthyA077739CertificateLow.md)
