# Distance of Prescribed Circular Deletions

## Abstract

The actual k-label circular deletion code has minimum distance k-2; uniform recovery from t whole-readout errors and e known erasures holds exactly when 2t+e<k-2.

Status: task-private canonical source proposal. The Lean source has actual MacStudio HECA compilation and standard axiom-closure receipts. No repository admission or registration is claimed. The two theorems below are checked in private scratch, and the decoding application is checked in a separate temporary source, without an additional permanent Lean declaration.

Let T be any label type with decidable equality, A a finite support of size n>=4, and J a subset of A with k=|J|>=3. States are SupportedCircle A: nodup oriented circles, identified only up to rotation. The output at x is the actual delete x C. ReadoutAlphabet A x is exactly the image of that deletion map, encoded as a subtype of Cycle T. The word is a dependent tuple indexed by J. Equality is tested only within a fixed coordinate. No assumption that T is finite is used. Feasibility requires k<=n.

**Theorem 1.1 (The Exact Minimum Distance Is k-2).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall J \in \mathrm{Finset}\left(T\right),\; ((4 \le \mathrm{card}\left(A\right)) \land ((\mathrm{Subset}\left(J, A\right)) \land (3 \le \mathrm{card}\left(J\right)))) \Rightarrow ((\forall C \in \mathrm{SupportedCircle}\left(A\right),\; \forall D \in \mathrm{SupportedCircle}\left(A\right),\; (\neg (C = D)) \Rightarrow (\mathrm{card}\left(J\right) - 2 \le \mathrm{readoutDistance}\left(J, C, D\right))) \land (\exists C \in \mathrm{SupportedCircle}\left(A\right),\; \exists D \in \mathrm{SupportedCircle}\left(A\right),\; (\neg (C = D)) \land ((\mathrm{card}\left(\{x \in J \mid \mathrm{delete}\left(x, C\right) = \mathrm{delete}\left(x, D\right)\}\right) = 2) \land (\mathrm{readoutDistance}\left(J, C, D\right) = \mathrm{card}\left(J\right) - 2))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/PrescribedDeletionDistance.exact_prescribed_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two distinct supported circles agreed at three distinct labels of J, ThreeSpecifiedDeletions.reconstruct_three would identify them. Thus their agreement set has at most two elements. The agreement and disagreement sets partition J, giving distance at least k-2. Choose distinct a,b in J and apply the existing two_deletions_insufficient theorem. Its actual supported collision agrees at a and b. A third agreeing label is impossible by reconstruct_three, so this pair has exactly two agreements and distance k-2. Both existing proofs are reused without reconstruction or finite enumeration. The new finite-set bound and attainment calculation are the substantive missing composition.

**Theorem 1.2 (A Failed Budget Has an Actual Legal Ambiguity Witness).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall J \in \mathrm{Finset}\left(T\right),\; \forall t \in \mathrm{Nat},\; \forall e \in \mathrm{Nat},\; ((4 \le \mathrm{card}\left(A\right)) \land ((\mathrm{Subset}\left(J, A\right)) \land ((3 \le \mathrm{card}\left(J\right)) \land (\mathrm{card}\left(J\right) - 2 \le 2 \times t + e)))) \Rightarrow (\exists C \in \mathrm{SupportedCircle}\left(A\right),\; \exists D \in \mathrm{SupportedCircle}\left(A\right),\; (\neg (C = D)) \land (\exists E \in \mathrm{Finset}\left(T\right),\; (\mathrm{Subset}\left(E, J\right)) \land ((\mathrm{card}\left(E\right) \le e) \land (\exists r \in \mathrm{ReadoutSection}\left(A\right),\; (\mathrm{errorCount}\left(J, E, r, C\right) \le t) \land (\mathrm{errorCount}\left(J, E, r, D\right) \le t)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/PrescribedDeletionDistance.ambiguity_of_failed_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ReadoutSection A is the dependent function type assigning an actual deletion-image value at every label. Only its restriction to J outside E is received; the candidate fills unused coordinates with C's own readout. errorCount counts labels in J outside E where the section value differs from the given state's deletion. The proof chooses an attaining pair, erases min(e,k-2) disagreements, and partitions the remaining disagreements into two error sets. At each coordinate it constructs a subtype value with witness C or D. Exact filter identities identify the two error sets, proving the bounds without requiring any third symbol in any alphabet.

For decoding, choose a bijection i -> x_i from Fin k to J and embed each ReadoutAlphabet A x_i into Cycle T by subtype value. This preserves coordinate equality and hence Hamming distance. Let Ccode be the range of the actual deletion-word map. Apply ErrorErasureUniqueDecoding.error_erasure_unique_decoding with its alphabet alpha=Cycle T, length n=k, distance d=k-2, error parameter e=t and erasure parameter s=e. Its erased finset is the reindexed known erased-label set. A received value at an unerased label must belong to ReadoutAlphabet A x_i; erased coordinates may be filled with the true word for this existence/uniqueness argument, because those values are never compared. The theorem gives a unique codeword under 2t+e<k-2. Three-label reconstruction transfers codeword uniqueness to circle uniqueness. This is an exact application of an existing generic theorem and should be checked transiently, not retained as a bind-only declaration.

Sharpness uses the same actual attaining pair C,D. Let Delta be its k-2 disagreeing labels. If 2t+e>=k-2, erase min(e,k-2) labels in Delta. Partition the remaining q<=2t labels into P,Q of sizes at most t. At labels in P receive D's readout and elsewhere receive C's readout. The received tuple differs from C on P and from D on Q. Both are compatible; no decoder can recover the transmitted object uniformly. Every received coordinate is an actual same-label deletion output of C or D and so belongs to its stipulated alphabet. This construction also covers equality, zero errors, zero erasures and erasure budgets greater than k by using at most the budget. ArbitraryErrorCorrectionCapacity contains a related split-disagreement construction, but its public capacity theorem assumes residue-code moduli and cannot be applied to circular words.

The exact minimum prescribed observation budget is 2t+e+3 when that number is at most n; otherwise no choice of distinct deletion labels can provide the uniform guarantee. Without erasures the guaranteed error radius is floor((k-3)/2), using the existing UniqueDecodingRadius.unique_decoding_radius theorem with d=k-2. With no errors, at most k-3 erasures are guaranteed. Boundary k=3 has distance one and guarantees only exact readouts.

For a particular known erasure set E and received partial word r, the exact criterion is that the set of supported circles differing from r at at most t unerased labels is a singleton. The global threshold concerns every state and every admissible noise pattern; its failure supplies an ambiguous instance, not ambiguity of each received word. For a fixed circle C and E, define its local punctured separation as the minimum, over D!=C, of the number of their disagreeing labels outside E. Every radius-t corruption of C is uniquely compatible precisely when twice t is smaller than that local separation. These are exact mathematical criteria, not a classification of all local separations. No claim concerns character edits, mislabeled coordinates, unlabeled decks, marginal laws, running time, sample complexity, adaptive sampling or literature novelty.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/PrescribedDeletionDistance.ambiguity_of_failed_budget`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/PrescribedDeletionDistance.exact_prescribed_distance`
- Dependency: [D5/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions](ThreeSpecifiedDeletions.md)
