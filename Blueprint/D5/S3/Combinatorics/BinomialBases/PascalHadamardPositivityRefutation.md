# A negative minor of a fractional Hadamard power of the Pascal matrix

## Abstract

A strictly separated Pascal minor has negative determinant at real exponent one tenth, refuting the original MO515594 positivity assertion.

**Definition 1.1 (The full original strict-positivity assertion).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall alpha \in \operatorname{Fin}\left(k\right) \to \mathrm{Nat},\; \forall beta \in \operatorname{Fin}\left(k\right) \to \mathrm{Nat},\; \forall r \in \mathrm{Real},\; (0 < r) \Rightarrow ((\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; (i < j) \Rightarrow (alpha\left(i\right) < alpha\left(j\right))) \Rightarrow ((\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; (i < j) \Rightarrow (beta\left(i\right) < beta\left(j\right))) \Rightarrow ((\forall i \in \operatorname{Fin}\left(k\right),\; alpha\left(i\right) \le n) \Rightarrow ((\forall i \in \operatorname{Fin}\left(k\right),\; beta\left(i\right) \le n) \Rightarrow ((\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; beta\left(j\right) < alpha\left(i\right)) \Rightarrow (0 < \operatorname{Matrix}.\operatorname{det}\left(\operatorname{Matrix}.\operatorname{of}\left(\lambda (i: \operatorname{Fin}\left(k\right)) \mapsto (\lambda (j: \operatorname{Fin}\left(k\right)) \mapsto (((\operatorname{Nat}.\operatorname{choose}\left(alpha\left(i\right), beta\left(j\right)\right): \mathrm{Nat}): \mathrm{Real})^{r}))\right)\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.claim` (`✓ std3`).

*Citation.* VSP (2026). *Total positivity of Hadamard powers of Binomial matrix*. URL: <https://mathoverflow.net/questions/515594>.

*Commentary.*

VSP's original question, MathOverflow 515594, revision 1, GUID 24043C19-8B17-4527-819F-D0DAEA1E8F86. Both n and k range over all natural numbers. The functions alpha and beta list row and column indices in their original increasing order, with every index at most n. The condition beta(j)<alpha(i) for every pair imposes strict separation of the complete column list from the complete row list.

Nat.choose gives the actual entries of the finite Pascal matrix indexed by 0,...,n. Casting these natural entries to the reals and using real rpow gives its Hadamard power; Matrix.of on the two Fin(k) indices is exactly the selected square submatrix, and Matrix.det is its ordinary determinant. For k>0, the displayed pairwise conditions are equivalent to beta(0)<...<beta(k-1)<alpha(0)<...<alpha(k-1). For k=0, all index conditions are vacuous and the empty determinant is one, so including the empty minor adds a true case.

The source question is attributed to VSP at https://mathoverflow.net/questions/515594 under https://creativecommons.org/licenses/by-sa/4.0/. This adaptation replaces the source's one-based lists by Fin(k) functions and makes every natural-index bound explicit. The separately appended nonvanishing question for r>1 is not part of this assertion.

**Theorem 1.2 (The original assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mo515594-original-pascal-hadamard-positivity` (refuted) by `D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mo515594-original-pascal-hadamard-positivity","declaration_gid":"D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* VSP (2026). *Total positivity of Hadamard powers of Binomial matrix*. URL: <https://mathoverflow.net/questions/515594>.

*Commentary.*

Take n=5, k=3, alpha=(3,4,5), beta=(0,1,2) and r=1/10. The strict ordering is 0<1<2<3<4<5. The selected unpowered matrix has rows (1,3,3), (1,4,6), (1,5,10). Matrix.det_fin_three and Real.mul_rpow identify the powered determinant D with 40^(1/10)+18^(1/10)+15^(1/10)-2*30^(1/10)-12^(1/10). All roots here are real rpow on positive bases.

Put q=1000000. Exact integer inequalities give 40*q^10<1446126^10, 18*q^10<1335142^10, 15*q^10<1311020^10, 1405115^10<30*q^10 and 1282088^10<12*q^10. Nonnegativity, the identity (a^(1/10))^10=a and strict monotonicity of tenth powers give upper bounds for the three positive terms and lower bounds for the two negative terms. Thus D<(1446126+1335142+1311020-2*1405115-1282088)/q=-30/1000000<0. The proof uses exact rational arithmetic and the standard real-power identities, with no floating-point premise.

This one admissible negative minor disproves the full original universal assertion; no restriction on its other indices or exponents is needed. General failures of fractional Hadamard powers are known, and the bounded inspected sources did not identify a prior complete answer for this fixed Pascal-family question. Worldwide priority remains unknown. This argument gives no conclusion about the later all-size nonvanishing question for r>1.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.result`
