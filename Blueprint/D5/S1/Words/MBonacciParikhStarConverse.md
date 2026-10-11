# The Uniform m-bonacci Parikh and Greedy Characterization

## Abstract

Exact all-start sentinel Parikh vectors and the full actual greedy converse.

The alphabet is Fin m. The original literal substitution phi sends a below m minus one to [0,a+1] and sends the terminal letter to [0]. word is the original unbounded limit of its nested iterates. boundary, factor, letterCount, parikhImage, T, U, S, fullGreedy and periodicDigits are reused at their original definitions. Every factor start is a natural q, including zero; k has no finite upper bound. S(k) is one plus the sum of the actual image lengths U(j) below k.

Let L_a(a)=[a] and L_a(b)=[a,b] otherwise. The actual phi is L_0 after rot on the same source letters. For a predecessor r and a length-|r|+1 source window v with the vector of r plus one excess letter b, write y=phi(v) and N=|phi(r)|+2. The true first source block determines the output offset delta, either zero or one. If rot(b)=0, y has length N-1; otherwise y has length N. At delta zero the singleton-excess window is y followed by zero and the two-letter-excess window is y. At delta one the two-letter-excess window is tail(y) followed by zero, while the singleton-excess window is tail(y) followed by zero and a next letter c. These are the four elementary windows; delta describes the first block, independently of the excess letter.

The next zero and its following output letter are supplied by the original right_extension_occurrence_iff on the actual source extension v followed by its next letter. If that following source image is a singleton, its following block supplies the second output letter. No image-length-two assumption is imposed. In the offset-one singleton-excess branch, c is the rotation of this next source letter and may differ from the previous excess letter. The proof keeps the same actual infinite word and boundary throughout.

Equal predecessor counts give an exact List.Perm between v and r followed by b. The pinned List permutation flatMap supplier transports it through phi, supplying both image length and counts. For a clipped initial zero, the private consumed clipping helper directly applies the pinned append permutation and cons cancellation suppliers to zero followed by t and y followed by zero. The other finite rearrangements use exact counts and additive cancellation. The proof uses neither a truncated-natural-subtraction identity nor cyclic conjugacy. The m=5 start-29 length-four factor 1001 obstructs a cyclic-conjugacy proxy, while the abelian statement remains the exact goal.

The Star property is used only for the induction predecessor. The empty predecessor is discharged by the actual one-letter factor at every start. Original boundary_window and the original strict/block laws locate each output q, including zero. Applying the four cases proves the successor Star upper inclusion. Original sentinel_frs, star_subset and star_injective then give every one of the m distinct vectors. A constant word illustrates why the upper inclusion by itself is insufficient.

The output is MSB-first and continues through U(0), keeping every trailing zero and the final partial period. k=0 gives n=1 and the list [1]. The proof covers k<m, k=m and k>m uniformly, and never uses rho(n)=m to infer a sentinel from periodic digits. Sentinel sufficiency holds already for m at least two. The integrated equivalences here retain m at least five; they do not claim the same full equivalence below five. No balance, finite sample completeness, cyclic conjugacy or alternative fixed word is a premise.

The sentinel converse is literature-attested in Ondrej Turek, Abelian complexity and Abelian co-decomposition, Theoretical Computer Science 469 (2013), pages 77–91, DOI 10.1016/j.tcs.2012.10.034, arXiv:1201.2109v1. The necessity is supplied by the existing source-bound formalization. The new work here is a Lean proof of the exact all-start transport and complete scanner inverse integrated with those original results; no mathematical novelty is claimed.

**Theorem 1.1 (A positive complete scan reconstructs its input).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall count \in \mathbb{N},\; 0 < count \Rightarrow Injective\left(greedyScan\left(m, count\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciParikhStarConverse.greedyScan_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two and every positive count, greedyScan(count) is injective on all natural remainders. At count one the quotient is the remainder because U(0) equals one. At a larger count, equal complete lists give equal leading quotients and equal remaining scans. Induction recovers equal remainders modulo the current weight; the exact quotient-plus-remainder identity recovers the input. No assumption on abelian complexity enters this direction. The count-zero scan is excluded because it is constant.

**Theorem 1.2 (Exact all-start sentinel Parikh range).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall k \in \mathbb{N},\; parikhImage\left(m, S\left(m, k\right)\right) = range\left(star\left(sentinelIter\left(m, k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciParikhStarConverse.sentinel_parikh_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two and every k, parikhImage(S(k)) equals the range of star(sentinelIter(k)). The upper inclusion is induction from the empty original sentinel. The lower inclusion uses the original fully right-special sentinel and star_subset. The original star_injective distinguishes every excess letter, so exactly m different vectors are attained. An upper Star inclusion alone does not imply attainment.

**Theorem 1.3 (Uniform literal-word and complete-digit characterization).**

$$\forall m \in \mathbb{N},\; \left(2 \le m \land 5 \le m\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\left(ncard\left(parikhImage\left(m, n\right)\right) = m \Leftrightarrow \left(\exists k \in \mathbb{N},\; n = S\left(m, k\right)\right)\right) \land \left(ncard\left(parikhImage\left(m, n\right)\right) = m \Leftrightarrow \left(\exists k \in \mathbb{N},\; fullGreedy\left(m, n\right) = periodicDigits\left(m, k\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciParikhStarConverse.uniform_minimum_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and every n at least one, the complete all-start Parikh cardinality equals m if and only if n equals S(k) for some natural k, and if and only if the complete fullGreedy(n) list equals periodicDigits(k) for some natural k. Necessity is the direct original minimal_abelian_complexity_greedy result. Sentinel sufficiency uses the exact range theorem. Periodic digits imply the same sentinel count by the new positive scanner inverse: full output lengths identify a common top index, sentinel_top and scan_sentinel give the comparison list, and scanner injectivity recovers n. This is one endpoint with both transport and inverse on its live proof paths.

## References

- Truth anchor: `D5/S1/Words/MBonacciParikhStarConverse.greedyScan_injective`
- Truth anchor: `D5/S1/Words/MBonacciParikhStarConverse.sentinel_parikh_image`
- Truth anchor: `D5/S1/Words/MBonacciParikhStarConverse.uniform_minimum_characterization`
- Dependency: [D5/S1/Words/MBonacciMinimumGreedy](MBonacciMinimumGreedy.md)
