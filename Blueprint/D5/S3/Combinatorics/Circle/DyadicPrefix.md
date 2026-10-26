# Binary quotient separation and labelled two-run prefixes

## Abstract

Dyadic quotient separation constructs a compatible actual occurrence prefix at a two-run boundary.

Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, C3.1, DOI 10.5070/C6.68671, supplies the source problem. The arithmetic and local prefix argument here is repository-derived support, with no claim of literature novelty or resolution of C3.1. All powers, quotients, remainders and scalar masses are natural-number operations; signed prefix sums are integers.

**Definition 1.1 (Actual binary occurrence positions).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicPrefix.bitSubset`

*Formalization.* `D5/S3/Combinatorics/Circle/DyadicPrefix.bitSubset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural u,x with x<2^u, bitSubset(u,x) is a Finset of Fin u positions, constructed by filtering the actual Nat.bitIndices of x and embedding their distinct natural indices in Fin u. A position i is selected exactly when x.testBit(i.val) is true. Its powers of two sum to x, so its weights a*2^i.val sum to a*x. When 2^(u-1)<=x and u>0, the top position u-1 is selected. These consumed binary helpers reuse the pinned Mathlib bitIndices membership, sum and power-bound theorems.

**Definition 1.2 (Physical labels and signed weights).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicPrefix.occurrenceWeight`

*Formalization.* `D5/S3/Combinatorics/Circle/DyadicPrefix.occurrenceWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An occurrence label is in Fin u + Fin v: inl(i) denotes positive position i with integer weight a*2^i.val; inr(j) denotes negative position j with integer weight -(q*2^j.val). The sign and position together identify the physical occurrence, including when different occurrences have equal numerical magnitudes.

**Definition 1.3 (The actual appended negative occurrence).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicPrefix.packetLabels`

*Formalization.* `D5/S3/Combinatorics/Circle/DyadicPrefix.packetLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For v>0 and a list order of positive Fin u positions, packetLabels is order.map(inl) followed by the single actual top negative label inr(v-1). The append preserves the position labels rather than inserting a freely chosen scalar debit.

**Definition 1.4 (Exact subset and every-prefix certificate).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicPrefix.PrefixSelection`

*Formalization.* `D5/S3/Combinatorics/Circle/DyadicPrefix.PrefixSelection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive u,v, put P=(2^u-1)*a, L=2^(u-1)*a and M=2^(v-1)*q. PrefixSelection(u,v,a,q,C,U,S,order) requires max(L,M)<=U<=min(P,C), membership of the actual top position u-1 in S, sum over i in S of a*2^i.val=U, order.Nodup and order.toFinset=S. Every natural positive prefix mass is at most U. The constructed signed prefix is Nodup and every one of its integer prefix sums, for all natural prefix lengths including lengths beyond the end, lies in [0,C]. Its endpoint is U-M, and U is exactly min(P,a*(C/a)). No occurrence is duplicated or split.

**Theorem 1.5 (The dyadic rounding loss is controlled).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicPrefix.quotient_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/DyadicPrefix.quotient_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all positive natural u,v,a and odd natural q, assume Q=(2^v-1)*q<=P=(2^u-1)*a. With C=2^(u-1)*a+(q-1)/2 and M=2^(v-1)*q, the conclusion is M<=a*(C/a)<=C. This is a separation bound on the largest multiple of a below C, not a hypothesis that a suitable subset exists. Write x=2^(u-1), y=2^(v-1), d=2^v-1. For v>1 the actual Euclidean remainder beta of x by d is 2^((u-1)%v), using Mathlib's pow_sub_one_mod_pow_sub_one; hence 1<=beta<=y. For v=1 take beta=1 and h=x-1. In both cases x=h*d+beta and d+1=2*y. Oddness writes q=2*a*n+2*t+1 with t<a, where n=((q-1)/2)/a. The run-mass inequality first forces n<=h. The case n<h is a strict quotient gap. If n=h, cancellation gives d*(2*t+1)+a<=2*a*beta; beta<=y then implies 2*t+1<=a, and consequently (d+1)*(2*t+1)<=2*a*beta. This yields y*q<=a*(x+n). Finally C/a=x+n. The v=1, u=1, n=0 and equality boundaries remain in the quantified statement.

**Theorem 1.6 (Realizing the separated mass by actual binary positions).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicPrefix.occurrence_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/DyadicPrefix.occurrence_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the quotient theorem's u,v,a,q hypotheses, the conclusion is the existence of U,S,order satisfying PrefixSelection with C=L+(q-1)/2. Set x=min(2^u-1,C/a) and U=a*x=min(P,a*(C/a)). The quotient separation gives M<=a*(C/a), while Q<=P and M<=Q give M<=P. Also L<=P and L<=a*(C/a). Thus max(L,M)<=U<=min(P,C). The actual bitSubset(u,x) realizes U and includes the top position, since 2^(u-1)<=x<2^u. Its Finset.toList supplies a distinct occurrence order. Each positive prefix is a natural submass of U. Appending the actual -M ends at U-M in [0,C], which proves every prefix of the signed labelled prefix is safe. Remaining original occurrences are not scheduled by this theorem.

**Theorem 1.7 (Deriving the construction from the original two-run equations).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicPrefix.two_run_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/DyadicPrefix.two_run_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quantify over natural u,v,a,q,b,N,C with u,v,a,q,b positive and a<=b. The only run equations assumed are N=2*C+1, N=2^u*a+q and N=2^v*q+b. The theorem concludes Odd(q), the integer identity P-Q=b-a, Q<=P, C=L+(q-1)/2, L<=C, M<=C, and an actual PrefixSelection at that same C. It assumes no quotient inequality, chosen mass, subset, parity of b, or safe order. Since u>0, the first run term is even and the odd N forces q odd. The run equations give P+a=Q+b, so a<=b yields Q<=P. Their first equation also gives C=L+(q-1)/2. The arithmetic theorem and the actual occurrence construction then apply. In the full source problem the global minimum supplies a<=b; extraction of cyclic runs and a compatible global root order are outside this support theorem.

Arbitrary legal-start insertion cannot replace the missing global ordering argument. The actual source at k=7,t=19,N=127,C=63 is (19,38,-51,25,50,-27,-54). The local packet obstruction uses the legal height H=26 with packet (19,38,-51). At H, only +19 is legal, reaching 45; +38 then exceeds C, while -51 goes below zero. Therefore this packet has no capacity-preserving insertion from that legal start. The prefix construction above starts from zero with a jointly selected positive subset. It proves neither arbitrary-start packet insertion, arbitrary source-order preservation, a compatible global root order, nor full C3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicPrefix.PrefixSelection`
- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicPrefix.bitSubset`
- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicPrefix.occurrenceWeight`
- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicPrefix.occurrence_prefix`
- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicPrefix.packetLabels`
- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicPrefix.quotient_separation`
- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicPrefix.two_run_prefix`
