# Rank assembly for the odd cyclic trace support

## Abstract

Cyclic overlap constraints bound the constant-derivative space and assemble the complete odd-length affine-support theorem.

For positive m, each topVariables(m,i) has exactly one adjacent cyclic pair, at i+2m-1 and i+2m. The prefix itself contains no adjacent pair, including across the cyclic boundary. Deleting any other coordinate a leaves this pair intact, so any top variable set containing the deletion must have the same index i. Applying the degree-m derivative equation at that deletion therefore proves b_i u_a=0. This establishes the interior-deletion constraints for every odd length at least five, and the same implication at length three where there is no interior coordinate. An endpoint deletion is a full prefix. A prefix has no adjacent pair, so an equal-cardinality prefix contained in a top set must be obtained by deleting one of its adjacent pair. The two possible top indices are i and i+2, and coefficient extraction gives b_i u_(i-1)=b_(i+2) u_i at every positive m.

For m≥2 and an active mask bit, the interior constraints fix every prefix of length less than m under translation by u. Differentiating the shifted inverse expression leaves two degree-m sums, which cancel by the endpoint equation after a cyclic reindexing. The remaining expression is the sum over i and r<m of b_i u_(i+2r) P_(i,r), plus the sum over i of b_i u_(i-2)(1+u_(i-1)) P_(i,m-1). Every proper nonempty step-two prefix has a unique start: its first coordinate is present and its predecessor by two is absent. Prefix cardinalities separate different lengths. Extracting these actual Boolean function coefficients gives (A): b_i u_(i+r)=0 for 1≤r≤2m-3, and (C): b_i[u_(i-3)+u_(i-2)(1+u_(i-1))]=0. Empty earlier ranges at m=2 are preserved.

For m≥2, a nonzero mask is either all-one or has a coordinate i with b_i=1 and b_(i-2)=0. The latter alternative follows by propagating active bits backwards by two around the odd cycle if no such boundary exists. The all-one mask makes every derivative direction zero by (A). At a boundary, (B) gives u_(i-2)=0, then (C) gives u_(i-3)=0, while u_(i-1)=b_(i+2) u_i. Equation (A) kills every remaining coordinate. Thus evaluation at i is an injective linear map from the derivative subspace into ZMod 2, proving dimension at most one. This argument covers length five directly and requires no orientation-uniqueness assumption.

At length three, choose any active mask coordinate i. The same endpoint equation determines both other direction coordinates from u_i, so coordinate evaluation is again injective. Length one has the required lower bound zero. For every other odd length, combine the derivative-space dimension bound with constantDerivative_affineSpan_duality and the dimension 2m+1 of the full binary word space. The exact sourceTrace_eq_phase_sum and inverse_phase_sum identities identify the literal trace support with the inverse-component Walsh support, giving the original affine-dimension inequality.

**Theorem 1.1 (The complete odd-length trace-support bound).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {b \ne 0} \Rightarrow {{2} \cdot {m} \le \mathrm{finrank}\left(\mathrm{ZMod}\left(2\right), \mathrm{direction}\left(\mathrm{affineSpan}\left(\mathrm{ZMod}\left(2\right), \mathrm{traceSupport}\left(b\right)\right)\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly.affine_trace_support_dimension` (`✓ std3`). ∎

*Resolves.* `Problems/mathoverflow-512655-cyclic-sign-trace-affine-support` (proved) by `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly.affine_trace_support_dimension`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathoverflow-512655-cyclic-sign-trace-affine-support","declaration_gid":"D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly.affine_trace_support_dimension","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every natural m and every nonzero binary word b of length 2m+1, the affine span over ZMod 2 of all a with nonzero literal ordered integer sourceTrace(b,a) has direction dimension at least 2m. All positive odd lengths, including one and three, and every nonzero mask are retained. The proof assumes neither the direction classification nor a coefficient-uniqueness or dimension conclusion. This is the complete assertion defined by claim.

The literal trace model follows ricardorr, MathOverflow question 512655, original revision E06A6743-2C15-41CD-9390-04D1862ABA02, https://mathoverflow.net/questions/512655, attributed under CC-BY-SA 4.0. The inverse argument above is a direct derivation for this cyclic map.

The theorem establishes the full mathematical inequality for the specified model. It does not assert that every support is a hyperplane or classify all masks attaining equality. The source attribution and library reuse do not establish a novelty or priority claim.

## References

- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly.affine_trace_support_dimension`
- Dependency: [D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients](BooleanCoefficients.md)
- Dependency: [D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude](Prelude.md)
- Dependency: [D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Trace](Trace.md)
