# Exact exceptional19 physical zero-subset count

## Abstract

For every natural r, the full exceptional19 family of physical integer-zero subsets has cardinality Z with 76Z=941*2^(18r+12)+536.

**Theorem 1.1 (All exponents and every original physical subset).**

Lean statement: `D5/S3/Combinatorics/Circle/MersenneExceptional19ZeroCount.actual_zero_subsets_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/MersenneExceptional19ZeroCount.actual_zero_subsets_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d=18r+12, B=2^d, N=B^3-1, t=(B-1)(2B-3), C=B^2+B+1, Q=C/19 and K=19(B-1). The theorem quantifies all natural r, including zero. Z counts all Finset(Fin(3d)) whose literal integer sum of SourceWidth.actualSource(3d,t) is zero. Equal source values at different labels remain different choices. Empty and full subsets are included. The conclusion is the exact equation 76Z=941B+536; there is no finite exponent bound, generic floor-zero premise, rank condition, transport assumption or replacement by modular zero.

The proof first establishes B modulo 19 equals 11 and 8 divides B, hence B=152M-8 with M=(B+8)/152 at least 27. The sealed phase_scaled_gcd theorem gives gcd(t,N)=19(B-1), so N/gcd(t,N)=Q. ZeroSumSubsets supplies the physical binary-mask injection, bounds and surjectivity. Literal integer zero implies Q divides the mask. Choosing the unique physical subset with mask kQ yields an exact bijection between the physical zero subsets and those 0<=k<=K whose actual integer sum is zero. Divisibility is only a sieve: its inverse condition still checks the literal integer sum.

The freshly compiled MersenneExceptional19Stabilizer.actual_sum_blocks is reused for arbitrary physical subsets. It expresses their actual sum in the three literal label slices L,Mb,U as (B-1) times ((2B-3)L-(5B+2)Mb+(3B+5)U+C*(-floor(2L/B)+floor(8Mb/B)-floor(4Mb/B)-floor(4U/B))). The existing mask_slices identity and strict digit bounds give mask/B=Mb+B*U and mask/B^2=U. Because 8 divides B, exact Euclidean division moves the factors 4 and 8 across the block boundary without a spurious remainder. This derives S(mask)=t*mask-N*(floor(2mask/B)-floor(8mask/B^2)+floor(4mask/B^2)-floor(mask/B^2)+floor(4mask/B^3)). No six-carry or bit-transport premise is assumed.

For mask=kQ the preceding identity becomes S(kQ)=N*f(k), where f(k)=((2B-3)/19)*k-floor(2kQ/B)+floor(8kQ/B^2)-floor(4kQ/B^2)+floor(kQ/B^2)-floor(4kQ/B^3). For k=19u+v the integer terms cancel exactly. The resulting five floors have numerators 38u+(5B+2)v, 152(B+1)u+8vC, 76(B+1)u+4vC, 19(B+1)u+vC and 76Cu+4vC, with positive denominators 19B, 19B^2, 19B^2, 19B^2 and 19B^3 respectively and signs -,+,-,+,-. The proof also identifies this normalized integer expression with the rational rowValue using x=(19u+v)/(19B), z=v/19+x*(1+1/B) and H(z)=floor(8z)-floor(4z)+floor(z). The exact B^-2 contribution remains present.

All 19 rows are proved for every M>=27 by writing M=n+27 with arbitrary natural n. The supplied ordinary symbolic certificate lists 260 consecutive half-open cells. On each cell, every one of the five affine numerators is monotone in u. Lean checks the lower floor bound at the first integer and the strict upper bound at the last integer. After expansion in n, the corresponding polynomial has nonnegative coefficients, and each required strict inequality has a positive constant. The generic floor_on_cell lemma therefore proves the exact row value at every integer in the cell. These are universal polynomial proofs, not finite-M sampling or native evaluation.

For each row, extensional equality identifies the filtered range with the union of exactly its zero-valued integer intervals. Pairwise disjointness and actual Ico cardinalities then prove the row count. In residue order 0 through 18, the counts are 76M-5, 84M-3, 89M-5, 90M-5, 90M-4, 106M-5, 98M-5, 130M-7, 124M-6, 92M-4, 92M-4, 124M-6, 130M-7, 98M-5, 106M-5, 90M-4, 90M-5, 89M-5 and 84M-3. Rows 9 and 11 retain their distinct correct counts. Their sum is 1882M-93. Signed interval-length arithmetic alone is not used as a substitute for the classification or finite cardinalities.

The exact bijection k -> (k/19,k modulo 19) partitions k<K into 0<=u<B-1 and 0<=v<19. The nonzero integer N allows the equivalence S(kQ)=0 iff f(k)=0. The remaining endpoint k=K has mask N and is the full physical subset; its actual sum is zero by the sealed source_cycle theorem, so it contributes one more subset. Thus Z=1882M-92. Substituting B=152M-8 gives the stated equation. Every helper lies on this connected proof path; the final statement adds no assumption.

The ordinary all-M proof and exact certificate supplied in this task informed this implementation. Only the actual Lean kernel build and its accepted axiom closure establish the formal result. This work claims no mathematical novelty, model diversity, independent review or official acceptance. The faithful full-telescope Reg source compiles with the same standard axiom closure. The coherent 62-module scoped report confirms the exact theorem, but its native count binding remains declared_unresolved: IE-C050 ClosedTruthReadout, reason unclassified_form, rule source.missing_let. There is no native binding certificate for this attempt. No issue specifically covering this missing-let case is linked in the supplied evidence; the related two-readout reconstruction issue https://github.com/the-omega-institute/trureturing/issues/18956 concerns a different theorem. No issue or judge mutation is made. Both faithful rotation Reg repairs compile, while their native bindings retain the separate source.statement_reconstruction diagnostic. The three protected RadixFourDigitBalance bindings remain declared_validated and byte-for-byte unchanged in this report.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/MersenneExceptional19ZeroCount.actual_zero_subsets_card`
- Dependency: [D5/S3/Combinatorics/Circle/MersenneExceptional19Stabilizer](MersenneExceptional19Stabilizer.md)
- Dependency: [D5/S3/Combinatorics/Circle/MersenneExceptional19ZeroCountRows](MersenneExceptional19ZeroCountRows.md)
- Dependency: [D5/S3/Combinatorics/Circle/MersennePhaseNoncyclicFamily](MersennePhaseNoncyclicFamily.md)
- Dependency: [D5/S3/Combinatorics/Circle/ZeroSumSubsets](ZeroSumSubsets.md)
