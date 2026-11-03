# Exact first reversal and the complete final pre-wrap band

## Abstract

The first strict reversal and all subsequent even return counts before the next wrap are determined on the actual quotient maps.

**Theorem 1.1 (The competing oblique relation outweighs the two horizontal endpoint fibers).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyBoundaryReturnDefect.first_return_reversal`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyBoundaryReturnDefect.first_return_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p,t be integers with p>=3 odd and t>=2. Put m=6t-1, n=p(m-3), L=p(m-1), and P=p.toNat. Use the actual integer-plane quotient maps of K19 spanned by (p(m-1)/2,p(m+1)/2), (p(m-9)/2,-p(m+9)/2), and K33 spanned by (p(m-3)/2,p(m+3)/2), (p(m-3)/2,-p(m+3)/2). W counts returns of four signed coordinate-step words. All natural conversions are justified by the proved positivity bounds; composite odd p are included.

The theorem proves W(F19,l)<=W(F33,l) for every natural l<L, the exact balance W(F33,L)+2 choose(L,4P)=W(F19,L)+2 choose(L,P)^2, and W(F33,L)<W(F19,L). Thus L is the first length where the comparison is strictly reversed; the first unequal return counts still occur earlier at n. It addresses precisely r=p in the length n+2r excluded by the short-band theorem. The earlier positive short-band difference therefore cannot extend through this boundary.

Since L<pm, the existing rank-one short-lattice relation mechanism still applies. In K19 the only vectors of Lee norm at most L are zero and plus/minus (p(m-5),-4p). In K33 they are zero and plus/minus (n,0): L<2n excludes larger multiples. Positivity of each first coordinate makes the three endpoint fibers disjoint, and the endpoint Lee bound supplies both directions of the actual quotient-return decomposition.

The two horizontal endpoint fibers each have size choose(L,P)^2. The oblique endpoint has transformed subset sizes 4P and zero; its negative has complementary sizes L-4P and L. The existing word/subset equivalence and binomial symmetry therefore give choose(L,4P) for each oblique fiber. Cancelling the common zero-endpoint fiber gives the exact balance identity.

For every natural P>=2 and L>=10P, the proof establishes choose(L,P)^2<choose(L,4P). A strict paired-factor product comparison first gives choose(M+5P,P)<choose(M,2P) for M>=5P; a nonnegative Vandermonde summand and the standard choose-product identity yield the stated inequality. Here t>=2 supplies L>=10P, so the exact fiber balance gives the strict return-count reversal. This argument introduces no assumed word count or lattice classification.

For lengths below n, reuse the already proved first-return defect theorem, which gives equality on the same quotient maps. For every even n<=l<L, n is even and l uniquely has the form n+2r with r<p; reuse the exact short-band formula, whose extra term is nonnegative. For odd l<L<pm, every short lattice relation is a multiple of the generator sum, with even coordinate sum p(m-b). A length-l signed word has endpoint coordinate sum congruent to l modulo two. These parity conditions are incompatible, so both return fibers are empty. The three cases cover every smaller natural length, with no omitted odd lengths.

The first-reversal theorem locates the initial strict negative comparison on the displayed quotient maps. It makes no assertion about eigenvalue ordering or literature novelty.

**Theorem 1.2 (Both return counts and strict reversal throughout the final even pre-wrap band).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyBoundaryReturnDefect.prewrap_return_reversal`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyBoundaryReturnDefect.prewrap_return_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same actual quotient maps, odd p>=3 and t>=2. Put m=6t-1, P=p.toNat, L=(p(m-1)).toNat. For every natural s with 2s<P, let l=L+2s. The hypothesis gives l<pm. No word count, lattice kernel classification or comparison is assumed.

Put Z=choose(l,l/2)^2, A=choose(l,4P+s) choose(l,s), and B=choose(l,P+s)^2. The theorem proves the individual formulas W(F19,l)=Z+2A and W(F33,l)=Z+2B, the exact balance W(F33,l)+2A=W(F19,l)+2B, and W(F33,l)<W(F19,l). Thus the first strict reversal persists at every even length from L up to the next wrap pm. This includes s=0 and composite odd p.

Strengthen the existing short-relation argument to every Lee norm strictly below pm. A relation is a multiple of the same generator sum; twice either nonzero generator norm exceeds pm, leaving precisely zero and the two opposite shortest relations in each lattice. The signed-word Lee bound and the disjoint three-fiber decomposition then apply at every l in this band.

At an oblique endpoint the two transformed sign-subset sizes are 4P+s and s. Its negative has the complementary sizes l-(4P+s) and l-s, giving the same product by binomial symmetry. The horizontal endpoints similarly give choose(l,P+s)^2. Since l is even, the zero endpoint has both subset sizes l/2 and hence contributes Z. These are counts of the actual return fibers, rather than a difference formula with an unspecified common term.

The strict estimate choose(L+2s,P+s)^2 < choose(L+2s,4P+s) choose(L+2s,s) starts from the already proved s=0 inequality for L>=10P. The two-step choose recurrences advance the top index by two and each lower index by one. With u=s+1 and B0=u(L+u), A0=B0+P(L-P), C0=B0+4P(L-4P), a polynomial factorization proves B0*C0<A0^2 for 2u<=P and L>=7P. A division-free cross multiplication and induction propagate strictness; all positivity and index bounds are proved. The boundary helper now directly consumes this theorem at s=0, so its fiber proof is shared.

The bound l<pm is essential to the stated short-kernel classification. The theorem makes no claim at or beyond the next wrap and no literature novelty claim.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyBoundaryReturnDefect.first_return_reversal`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyBoundaryReturnDefect.prewrap_return_reversal`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyShortReturnBand](BajnokBeattyShortReturnBand.md)
