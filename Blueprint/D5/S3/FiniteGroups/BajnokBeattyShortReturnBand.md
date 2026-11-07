# Exact first even return band for the two lattice quotients

## Abstract

The two actual lattice quotients have an exact return-count difference throughout their first even return band.

**Theorem 1.1 (Each of the two horizontal endpoint fibers contributes one binomial square).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyShortReturnBand.short_return_band`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyShortReturnBand.short_return_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p,t be integers with p>=3 odd and t>=2, and put m=6t-1 and n=p(m-3)>0. The result covers every such odd p, including composite values. Let K19 be the integer lattice spanned by (p(m-1)/2,p(m+1)/2) and (p(m-9)/2,-p(m+9)/2). Let K33 be spanned by (p(m-3)/2,p(m+3)/2) and (p(m-3)/2,-p(m+3)/2). The maps F19 and F33 are the actual quotient maps from the integer plane to the groups modulo these lattices.

Use the existing four signed coordinate steps and their endpoint sum. W(F,L) counts length-L words whose endpoint is zero under F. For every natural r with r<p, the theorem gives W(F33,n+2r)=W(F19,n+2r)+2 choose(n+2r,r)^2. In Lean n is the toNat of the displayed positive integer; its integer cast is proved equal to p(m-3). There are no assumed kernel classifications, word-count formulas, or alternative quotient maps in the statement.

The existing asymmetric_rank_one_actual_data theorem supplies the short lattice relation mechanism: before Lee norm pm, every lattice vector is an integer multiple of the sum of the two displayed generators. For K19 this sum is (p(m-5),-4p) and its Lee norm is p(m-1). Consequently the only K19 vector of norm strictly below p(m-1) is zero. For K33 the sum is (n,0). Since p(m-1)<2n, the only K33 vectors strictly below the same bound are zero, (n,0), and (-n,0). The rank-one supplier is directly reused, rather than reproved.

A word endpoint has Lee norm at most its length. The hypothesis r<p makes L=n+2r strictly less than p(m-1). Therefore the K19 return fiber is exactly the common zero-endpoint fiber, while the K33 return fiber is the disjoint union of that same fiber and the fibers at (n,0) and (-n,0). Positivity of n makes the three endpoints pairwise distinct. The proof checks this decomposition on the actual quotient maps and adds the three fiber cardinalities.

PlaneWordEndpointCount.endpoint_card identifies each horizontal fiber with a product of two fixed-cardinality position-subset fibers. At (n,0), each size is r. At (-n,0), each size is n+r, whose binomial coefficient equals choose(n+2r,r) by symmetry. Hence the two additional fibers contribute exactly two copies of the same binomial square. The word-count input is classical; this exact short-band comparison is the repository consequence of that count and the reused lattice relation theorem, with no literature novelty claim.

At r=0 the formula recovers the already established first-return difference of two; it does not present that specialization as another independent result. The theorem extends the exact count to every later even length n+2r with r<p. The boundary r=p, which has length p(m-1), is excluded because nonzero K19 lattice relations then appear. No boundary sign reversal, odd-length formula, new graph-moment theorem, orbit-isometry statement, or spectral classification is asserted by this increment.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyShortReturnBand.short_return_band`
- Dependency: [D5/S3/FiniteGroups/PlaneWordEndpointCount](PlaneWordEndpointCount.md)
