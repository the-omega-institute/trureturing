# Original interior weighted spectral roots

## Abstract

Both original retained memory graphs have a unique interior weighted spectral root whose binary logarithm is their actual weighted factor rate.

The graphs retain the original finite-past vertices, strict lower and closed upper guards, both letter labels and their weights twenty and six. All vertices and allowed edges on bilateral paths remain, including parallel labels, reducible components and transient bridges. The threshold d is any real number. Interior roots require n at least K at least two; the separate K=1 closed-root boundary is preserved.

**Definition 1.1 (LowCapLanguage).**

$$\forall K \in Nat,\; \operatorname{LowCapLanguage}\left(K\right) = \operatorname{setOf}\left(\left(\forall i \in Int,\; \neg \left(\forall k \in \operatorname{Fin}\left(K\right),\; \operatorname{omega}\left(\operatorname{add}\left(i, \operatorname{toInt}\left(k\right)\right)\right) = c\right)\right)_{omega \in Int \to CuLetter}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.LowCapLanguage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The low cap is the full bilateral language with no forward c run of length K. It is the original cap K minus one; it has no threshold or supplied entropy parameter.

**Definition 1.2 (lowBlock).**

$$\forall b \in Bool,\; \operatorname{lowBlock}\left(b\right) = \operatorname{ifThenElse}\left(b, \operatorname{list}\left(c, u, u, c, u\right), \operatorname{list}\left(c, u, c, u, u\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.lowBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The true and false binary choices select precisely the two distinct five-letter words. Both words have two c letters and three u letters, so their original total weight is fifty-eight.

**Definition 1.3 (lowSequence).**

$$\forall choices \in Int \to Bool, i \in Int,\; \operatorname{lowSequence}\left(choices, i\right) = \operatorname{ifThenElse}\left(\operatorname{intMod}\left(i, 5\right) = 0 \lor \operatorname{intMod}\left(i, 5\right) = \operatorname{ifThenElse}\left(\operatorname{choices}\left(\operatorname{intDivide}\left(i, 5\right)\right), 3, 2\right), c, u\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.lowSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integer quotient and remainder choose the bilateral block and its position. Position zero is c; the second c is at position three for true and position two for false. All other positions are u.

**Theorem 1.4 (original low cap inclusion).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \operatorname{lt}\left(0, K\right) \Rightarrow \operatorname{subset}\left(\operatorname{LowCapLanguage}\left(K\right), \operatorname{MemoryLanguage}\left(side, n, K, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_low_cap_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete language with no c run of length K lies in both memories. A run of length K+1 would contain a forbidden K run. Reversing the high-run test excludes every high guard, independently of its threshold and strictness.

**Theorem 1.5 (literal bilateral low codebook).**

$$\forall choices \in Int \to Bool, K \in Nat,\; \operatorname{le}\left(2, K\right) \Rightarrow \left(\left(\forall j \in Int, k \in \operatorname{Fin}\left(5\right),\; \operatorname{lowSequence}\left(choices, \operatorname{add}\left(\operatorname{multiply}\left(5, j\right), \operatorname{toInt}\left(k\right)\right)\right) = \operatorname{get}\left(\operatorname{lowBlock}\left(\operatorname{choices}\left(j\right)\right), k\right)\right) \land \operatorname{member}\left(\operatorname{lowSequence}\left(choices\right), \operatorname{LowCapLanguage}\left(K\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.literal_bilateral_low_codebook` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal blocks c u c u u and c u u c u occupy fixed five-letter cuts. Integer quotient and remainder construct one sequence for every bilateral binary choice, including negative indices. Adjacent c letters are impossible within a block or across its final u and the next initial c. Thus every K at least two has the required low-cap realization.

**Theorem 1.6 (original memory envelopes).**

$$\forall omega \in Int \to CuLetter, i \in Int, n \in Nat,\; \operatorname{le}\left(\operatorname{finitePast}\left(omega, i, n, 0\right), \operatorname{finitePast}\left(omega, i, \operatorname{add}\left(n, 1\right), 0\right)\right) \land \left(\operatorname{le}\left(\operatorname{finitePast}\left(omega, i, \operatorname{add}\left(n, 1\right), \operatorname{hSide}\left(high\right)\right), \operatorname{finitePast}\left(omega, i, n, \operatorname{hSide}\left(high\right)\right)\right) \land \left(\operatorname{le}\left(\operatorname{finitePast}\left(omega, i, n, 0\right), \operatorname{pastState}\left(omega, i\right)\right) \land \left(\operatorname{le}\left(\operatorname{pastState}\left(omega, i\right), \operatorname{finitePast}\left(omega, i, n, \operatorname{hSide}\left(high\right)\right)\right) \land \operatorname{le}\left(\operatorname{subtract}\left(\operatorname{finitePast}\left(omega, i, n, \operatorname{hSide}\left(high\right)\right), \operatorname{finitePast}\left(omega, i, n, 0\right)\right), \operatorname{multiply}\left(\operatorname{hSide}\left(high\right), \operatorname{power}\left(rho, n\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_memory_envelopes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Increasing memory raises the zero-seed image and lowers the h-seed image. Positive slopes and the invariant interval prove these finite inequalities. The existing bilateral limits place the actual state between the two images; the exact weighted contraction bounds their difference by h times rho to n.

**Theorem 1.7 (original memory language nesting).**

$$\forall n \in Nat, K \in Nat, d \in Real,\; \operatorname{subset}\left(\operatorname{MemoryLanguage}\left(lower, n, K, d\right), \operatorname{MemoryLanguage}\left(lower, \operatorname{add}\left(n, 1\right), K, d\right)\right) \land \left(\operatorname{subset}\left(\operatorname{MemoryLanguage}\left(lower, \operatorname{add}\left(n, 1\right), K, d\right), \operatorname{AuxiliaryLanguage}\left(K, d\right)\right) \land \left(\operatorname{subset}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right), \operatorname{MemoryLanguage}\left(upper, \operatorname{add}\left(n, 1\right), K, d\right)\right) \land \operatorname{subset}\left(\operatorname{MemoryLanguage}\left(upper, \operatorname{add}\left(n, 1\right), K, d\right), \operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_memory_language_nesting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower language at n is contained in the lower language at n+1, then in the original auxiliary language. The auxiliary language is contained in the upper language at n+1, then in the upper language at n. Each implication applies the corresponding actual envelope to the same pre-transition high guard.

**Theorem 1.8 (original upper memory intersection).**

$$\forall K \in Nat, d \in Real,\; \operatorname{setOf}\left(\left(\forall n \in Nat,\; \operatorname{le}\left(K, n\right) \Rightarrow \operatorname{member}\left(omega, \operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right)\right)_{omega \in Int \to CuLetter}\right) = \operatorname{AuxiliaryLanguage}\left(K, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_upper_memory_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Passing to the actual limit of all upper-seed images gives precisely the closed auxiliary guard. Conversely that actual guard lies below every upper envelope. Equality at the guard threshold is therefore retained in every upper memory.

**Theorem 1.9 (original literal codebook growth).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall q \in Nat,\; \operatorname{le}\left(2, K\right) \Rightarrow \operatorname{le}\left(\operatorname{power}\left(2, q\right), \operatorname{factorCount}\left(\operatorname{MemoryLanguage}\left(side, n, K, d\right), \operatorname{multiply}\left(q, 58\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_literal_codebook_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every q-bit choice extends to a bilateral sequence using the two literal blocks. Both blocks have weight fifty-eight. Equal positive weighted cuts recover the ordered blocks, and their different third letters recover the bits. This constructs an injection of all 2 to q choices into factors of weight 58q, including q=0.

**Theorem 1.10 (original positive weighted rate).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \operatorname{le}\left(2, K\right) \Rightarrow \operatorname{le}\left(\operatorname{divide}\left(1, 58\right), \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(side, n, K, d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_positive_weighted_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Counts at all multiples of fifty-eight give a lower bound of one over fifty-eight for the original max-one weighted factor limsup. The bound uses actual source-step weights, rather than the five-letter block length.

**Theorem 1.11 (original memory rate nesting).**

$$\forall n \in Nat, K \in Nat, d \in Real,\; \operatorname{le}\left(\operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(lower, n, K, d\right)\right), \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(lower, \operatorname{add}\left(n, 1\right), K, d\right)\right)\right) \land \left(\operatorname{le}\left(\operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(lower, \operatorname{add}\left(n, 1\right), K, d\right)\right), \operatorname{weightedFactorRate}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right)\right)\right) \land \left(\operatorname{le}\left(\operatorname{weightedFactorRate}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right)\right), \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(upper, \operatorname{add}\left(n, 1\right), K, d\right)\right)\right) \land \operatorname{le}\left(\operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(upper, \operatorname{add}\left(n, 1\right), K, d\right)\right), \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_memory_rate_nesting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factor inclusion injects each fixed-weight dictionary. Nonnegative series comparison and the exact weighted convergence abscissa transfer this inclusion to rates. Applying it to the constructed language nesting gives the two rate monotonicities and the auxiliary sandwich.

**Theorem 1.12 (original all u cycle).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall z \in Real,\; \operatorname{le}\left(0, z\right) \Rightarrow \left(\exists v \in \operatorname{CoreVertex}\left(side, n, K, d\right),\; \operatorname{MemoryEdge}\left(side, K, d, \operatorname{val}\left(v\right), u, \operatorname{val}\left(v\right)\right) \land \left(\forall k \in Nat,\; \operatorname{le}\left(\operatorname{power}\left(\operatorname{power}\left(z, 6\right), k\right), \operatorname{pathMass}\left(side, n, K, d, z, k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_all_u_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant u memory is an actual retained vertex and has an allowed u self-edge for every defined memory and threshold. Its k-step CorePath contributes exactly z to 6k. Every other monomial is nonnegative when z is nonnegative, so the full path mass dominates this cycle.

**Theorem 1.13 (original spectral positive).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall z \in Real,\; \operatorname{lt}\left(0, z\right) \Rightarrow \operatorname{le}\left(\operatorname{ENNRealOfReal}\left(\operatorname{power}\left(z, 6\right)\right), \operatorname{weightedRadius}\left(side, n, K, d, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_spectral_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A spectral radius below z to six would give a geometric bound with a strictly smaller rate. The actual u-cycle monomials contradict that bound as k grows. Hence every positive z has positive spectral radius.

**Definition 1.14 (radiusValue).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall z \in Real,\; \operatorname{radiusValue}\left(side, n, K, d, z\right) = \operatorname{toReal}\left(\operatorname{weightedRadius}\left(side, n, K, d, z\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.radiusValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RadiusValue is the real value of the original complex spectral radius. The actual all-u vertex makes the retained carrier nonempty, and the norm bound proves that the spectral radius is finite.

**Theorem 1.15 (original radius scaling).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \forall x \in Real, y \in Real,\; \left(\operatorname{lt}\left(0, x\right) \land \operatorname{le}\left(x, y\right)\right) \Rightarrow \left(\operatorname{le}\left(\operatorname{multiply}\left(\operatorname{power}\left(\operatorname{divide}\left(y, x\right), 6\right), \operatorname{radiusValue}\left(side, n, K, d, x\right)\right), \operatorname{radiusValue}\left(side, n, K, d, y\right)\right) \land \operatorname{le}\left(\operatorname{radiusValue}\left(side, n, K, d, y\right), \operatorname{multiply}\left(\operatorname{power}\left(\operatorname{divide}\left(y, x\right), 20\right), \operatorname{radiusValue}\left(side, n, K, d, x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_radius_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each genuine k-letter monomial has weight between 6k and 20k. Comparing their sums bounds the actual power masses. The norm sandwich and geometric power estimates pass these bounds to spectral radii through Gelfand's formula, without any irreducibility condition.

**Theorem 1.16 (original radius strict increase).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \operatorname{StrictMonoOn}\left(\left(\operatorname{radiusValue}\left(side, n, K, d, z\right)\right)_{z \in Real}, \operatorname{Ioi}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_radius_strict_increase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For y greater than x greater than zero, the factor (y/x) to six exceeds one. The lower scaling bound and actual spectral positivity make the original real spectral radius strictly increase.

**Theorem 1.17 (original adjacency zero continuous).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \operatorname{complexAdjacency}\left(side, n, K, d, 0\right) = 0 \land \operatorname{Continuous}\left(\left(\operatorname{complexAdjacency}\left(side, n, K, d, z\right)\right)_{z \in Real}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_adjacency_zero_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All actual edge exponents are positive, so the matrix at zero is zero. Each entry is a fixed finite sum of the two real monomials, carried into the complex numbers, and is continuous.

**Theorem 1.18 (original radius continuous).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \operatorname{ContinuousOn}\left(\left(\operatorname{radiusValue}\left(side, n, K, d, z\right)\right)_{z \in Real}, \operatorname{Ici}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_radius_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a positive parameter, the scaling bounds squeeze the radius between the minimum and maximum of the sixth and twentieth powers of the parameter ratio. Both envelopes meet the same radius. At zero, the continuous matrix norm tends to zero and dominates the nonnegative radius. These two arguments give continuity on the full nonnegative half-line.

**Theorem 1.19 (original spectral at one).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \left(\operatorname{le}\left(2, K\right) \land \operatorname{le}\left(K, n\right)\right) \Rightarrow \operatorname{lt}\left(1, \operatorname{radiusValue}\left(side, n, K, d, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_spectral_at_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal weighted rate bound forces divergence at a positive binary parameter strictly below one. The exact original factor-series boundary makes its spectral radius at least one; strict increase then makes the radius at one exceed one.

**Theorem 1.20 (original interior root).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \left(\operatorname{le}\left(2, K\right) \land \operatorname{le}\left(K, n\right)\right) \Rightarrow \operatorname{existsUnique}\left(\left(\operatorname{lt}\left(0, z\right) \land \left(\operatorname{lt}\left(z, 1\right) \land \operatorname{weightedRadius}\left(side, n, K, d, z\right) = 1\right)\right)_{z \in Real}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_interior_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual spectral radius is zero at zero and exceeds one at one. Continuity supplies an interior radius-one parameter, and strict increase makes it unique. The construction applies to both full retained graphs and every real d whenever n is at least K and K is at least two.

**Theorem 1.21 (original weighted interior root).**

$$\forall side \in MemorySide, n \in Nat, K \in Nat, d \in Real,\; \left(\operatorname{le}\left(2, K\right) \land \operatorname{le}\left(K, n\right)\right) \Rightarrow \operatorname{existsUnique}\left(\left(\operatorname{lt}\left(0, z\right) \land \left(\operatorname{lt}\left(z, 1\right) \land \left(\operatorname{weightedRadius}\left(side, n, K, d, z\right) = 1 \land \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(side, n, K, d\right)\right) = \operatorname{negate}\left(\operatorname{logb}\left(2, z\right)\right)\right)\right)\right)_{z \in Real}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_weighted_interior_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let gamma be minus log base two of the constructed root. Positivity and the root's upper bound make gamma positive. Strict increase identifies the actual convergence exponents with the open interval above gamma. The already established weighted factor-rate infimum therefore equals gamma, including sparse unsupported weights and the max-one convention.

**Theorem 1.22 (original root rate families).**

$$\forall K \in Nat, d \in Real,\; \operatorname{le}\left(2, K\right) \Rightarrow \left(\exists roots \in MemorySide \to \left(Nat \to Real\right),\; \left(\forall side \in MemorySide, n \in Nat,\; \operatorname{le}\left(K, n\right) \Rightarrow \left(\operatorname{lt}\left(0, \operatorname{roots}\left(side, n\right)\right) \land \left(\operatorname{lt}\left(\operatorname{roots}\left(side, n\right), 1\right) \land \left(\operatorname{weightedRadius}\left(side, n, K, d, \operatorname{roots}\left(side, n\right)\right) = 1 \land \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(side, n, K, d\right)\right) = \operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{roots}\left(side, n\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall n \in Nat,\; \operatorname{le}\left(K, n\right) \Rightarrow \left(\operatorname{le}\left(\operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{roots}\left(lower, n\right)\right)\right), \operatorname{weightedFactorRate}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right)\right)\right) \land \operatorname{le}\left(\operatorname{weightedFactorRate}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right)\right), \operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{roots}\left(upper, n\right)\right)\right)\right)\right)\right) \land \left(\operatorname{MonotoneOn}\left(\left(\operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{roots}\left(lower, n\right)\right)\right)\right)_{n \in Nat}, \operatorname{Ici}\left(K\right)\right) \land \operatorname{AntitoneOn}\left(\left(\operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{roots}\left(upper, n\right)\right)\right)\right)_{n \in Nat}, \operatorname{Ici}\left(K\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_root_rate_families` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the unique interior root at every admissible memory length for both sides. Its logarithmic rate equals the actual memory-language rate. The proven lower and upper language nesting gives the auxiliary-rate sandwich, increasing lower root rates and decreasing upper root rates on n at least K. Values below K are only a total-function convention and carry no interior-root claim.

The auxiliary rate is the original actual-list rate under the fixed transition-budget assumptions and the complete actual-language rate bridge. This identifies the sandwich with eta_b for both prescribed actual initial states. Fixed-graph common margins, pressure convergence, eventual even-length asymptotics and the remaining canonical-path, storage and optimum conclusions require their respective further results.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.LowCapLanguage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.literal_bilateral_low_codebook`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.lowBlock`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.lowSequence`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_adjacency_zero_continuous`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_all_u_cycle`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_interior_root`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_literal_codebook_growth`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_low_cap_inclusion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_memory_envelopes`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_memory_language_nesting`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_memory_rate_nesting`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_positive_weighted_rate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_radius_continuous`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_radius_scaling`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_radius_strict_increase`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_root_rate_families`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_spectral_at_one`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_spectral_positive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_upper_memory_intersection`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.original_weighted_interior_root`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.radiusValue`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping](WordWeightRegrouping.md)
