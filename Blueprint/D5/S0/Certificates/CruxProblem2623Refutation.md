# Crux Problem 2623: cyclic ratio-sum monotonicity

## Abstract

The cyclic ratio-sum monotonicity assertion in Crux Problem 2623 is false.

**Definition 1.1 (The cyclic ratio sum).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{NeZero}\left(n\right)) \Rightarrow (\forall x \in (\operatorname{ZMod}\left(n\right) \to \mathrm{Real}),\; \forall k \in \mathrm{Nat},\; \operatorname{S}\left(x, k\right) = \sum_{j \in \operatorname{ZMod}\left(n\right)} \frac{\sum_{i \in Finset.range\left(k + 1\right)} \operatorname{x}\left(j + (i : \operatorname{ZMod}\left(n\right))\right)}{\sum_{i \in Finset.range\left(k + 1\right)} \operatorname{x}\left(j + ((i + 1 : \mathrm{Nat}) : \operatorname{ZMod}\left(n\right))\right)})$$

*Formalization.* `D5/S0/Certificates/CruxProblem2623Refutation.S` (`✓ std3`).

*Citation.* Faruk Zejnulahi; Sefket Arslanagic (2001). *Problem 2623*. URL: <https://cms.math.ca/wp-content/uploads/crux-pdfs/CRUXv27n2.pdf>.

*Commentary.*

For n with a nonzero residue ring, S(x,k) sums over every j in ZMod n. Finset.range(k+1) contains exactly 0 through k. The numerator uses x(j+i), while the denominator uses x(j+(i+1)); both natural indices are cast to ZMod n before addition, so residue addition supplies the cyclic wraparound.

**Definition 1.2 (The proposed monotonicity assertion).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow (\forall x \in (\operatorname{ZMod}\left(n\right) \to \mathrm{Real}),\; (\forall j \in \operatorname{ZMod}\left(n\right),\; 0 < \operatorname{x}\left(j\right)) \Rightarrow (\forall k \in \mathrm{Nat},\; (k + 2 \le n) \Rightarrow (\operatorname{S}\left(x, k + 1\right) \le \operatorname{S}\left(x, k\right)))))$$

*Formalization.* `D5/S0/Certificates/CruxProblem2623Refutation.claim` (`✓ std3`).

*Citation.* Faruk Zejnulahi; Sefket Arslanagic (2001). *Problem 2623*. URL: <https://cms.math.ca/wp-content/uploads/crux-pdfs/CRUXv27n2.pdf>.

*Commentary.*

For every n at least two and every positive real-valued function on ZMod n, the assertion requires S(x,k+1) <= S(x,k) whenever k+2 <= n. The bound on n supplies the nonzero instance used by ZMod n. Lean index j=0 corresponds to printed index j=1.

**Theorem 1.3 (The monotonicity assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CruxProblem2623Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/crux-problem-2623-refutation` (refuted) by `D5/S0/Certificates/CruxProblem2623Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"crux-problem-2623-refutation","declaration_gid":"D5/S0/Certificates/CruxProblem2623Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Faruk Zejnulahi; Sefket Arslanagic (2001). *Problem 2623*. URL: <https://cms.math.ca/wp-content/uploads/crux-pdfs/CRUXv27n2.pdf>.

*Commentary.*

Take n=4, k=1, and the cyclic tuple (1,2,1,2). Its four terms give S(x,1)=1+1+1+1=4, while S(x,2)=4/5+5/4+4/5+5/4=41/10. Thus S(x,2) is strictly greater than S(x,1), at an interior index rather than an endpoint.

## References

- Truth anchor: `D5/S0/Certificates/CruxProblem2623Refutation.S`
- Truth anchor: `D5/S0/Certificates/CruxProblem2623Refutation.claim`
- Truth anchor: `D5/S0/Certificates/CruxProblem2623Refutation.result`
