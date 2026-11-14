# Sorting Positive Real-Rooted Product Coefficients

## Abstract

Strict log concavity restricts every coefficient-sorting permutation.

**Theorem 1.1 (Strict increase before a selected maximum).**

Lean statement: `D5/S3/Combinatorics/RealRootedPermutations/LogConcave.increasing_before_max`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RealRootedPermutations/LogConcave.increasing_before_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be a real sequence positive at every natural index through N. Suppose f(i)f(i+2) is strictly less than f(i+1) squared whenever i+2 is at most N. If m is at most N and f(i) is at most f(m) throughout that interval, then f(a) is strictly less than f(a+1) for every natural a with a+1 less than m. The step immediately into m follows weakly from maximality.

**Theorem 1.2 (Strict decrease after a selected maximum).**

Lean statement: `D5/S3/Combinatorics/RealRootedPermutations/LogConcave.decreasing_after_max`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RealRootedPermutations/LogConcave.decreasing_after_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same explicit positivity, strict log-concavity and maximality assumptions on a real sequence, f(a+1) is strictly less than f(a) whenever m is less than a and a+1 is at most N. The step immediately out of m follows weakly from maximality; two adjacent maximal values are allowed.

**Theorem 1.3 (Every weak coefficient sorting is unimodal).**

Lean statement: `D5/S3/Combinatorics/RealRootedPermutations/LogConcave.unimodal_of_arises`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/RealRootedPermutations/LogConcave.unimodal_of_arises` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural n, let r range over n+1 strictly positive real numbers and form the product of 1+r(i)x. If a permutation of the nonconstant coefficient indices lists their coefficients in weakly increasing order, then the inverse positions increase up to the value listed last and decrease thereafter. Coefficient indices and permutation values differ by one; the constant coefficient is omitted.

Induction on a finite set of factors proves positivity through the degree, vanishing above the degree, and strict log concavity at every interior index. Multiplication by 1+sx sends c(k+1) to c(k+1)+s c(k). Expansion of the resulting log-concavity difference gives two adjacent differences and a nonnegative middle term. The lowest interior index is handled separately, using the positive constant coefficient.

For a positive strictly log-concave sequence, a weak decrease forces the next decrease to be strict, and this propagates to the end of the sequence. Consequently the indices strictly below a selected maximum form a strictly increasing sequence, and those strictly above it form a strictly decreasing sequence. The final position of a weak sorting is a maximum. Comparisons away from that position are therefore strict; comparisons involving it follow from the final-position property. This includes a possible tie between two adjacent maximal coefficients.

## References

- Truth anchor: `D5/S3/Combinatorics/RealRootedPermutations/LogConcave.decreasing_after_max`
- Truth anchor: `D5/S3/Combinatorics/RealRootedPermutations/LogConcave.increasing_before_max`
- Truth anchor: `D5/S3/Combinatorics/RealRootedPermutations/LogConcave.unimodal_of_arises`
- Dependency: [D5/S3/Combinatorics/RealRootedPermutations/Defs](Defs.md)
