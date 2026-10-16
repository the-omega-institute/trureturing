# History Payload Factorization

## Abstract

A summary recovers a payload exactly when the payload is constant on its fibers. Global admission and complete local completion sets are two such payloads.

## Clocks on realized observation fibers

Let X be any set of complete finite histories, R a readout into Y, and t a natural-valued clock. The realized-image factorization applies with beta = R and payload = t: a unique function on range(R) recovers t precisely when R(x) = R(y) implies t(x) = t(y). This includes an empty X; no arbitrary output at an unrealized value of Y is required.

For serial group-valued gate readout, the literal word [g, inverse(g)] and the empty word both have product one, but their lengths are two and zero. Thus product readout alone does not determine length. The joint readout (R,t) determines both components. If Q has decoders r and c with R = r composed with Q and t = c composed with Q, then z maps to (r(z),c(z)) is a decoder for the joint readout. This universal property does not assert that the joint readout is injective on histories.

## Multiplicity at a fixed clock value

Let c assign r distinct literal words of width two to the alphabet of neutral blocks. Represent a width-two word by a function on Fin(2), and a sequence of k choices by s on Fin(k). The history at position 2i+j is c(s(i))(j). The product equivalence between Fin(k) times Fin(2) and Fin(2k), followed by List.ofFn, represents precisely the concatenation of these blocks; List.ofFn_mul supplies the equality with the flattened block list.

Equality of the histories gives equality at every position 2i+j, hence equality of each selected block, and injectivity of c gives equality of s. There are r to the power k choices. All histories have length 2k. If the product readout of each block is the monoid identity, List.prod_flatten makes every concatenation neutral. These facts use literal distinctness of blocks, independently of their common operator value.

On this family, a memory M that reconstructs history together with the constant product and clock must be injective. Its realized range has at least r to the power k elements. A fixed b-bit memory has 2 to the power b values, so b is at least the ceiling of k times log base two of r. The bound concerns exact recovery on the entire family.

## Support-covered assignment gluing

Let V index possibly dependent value types. For each constraint c, let K(c) be its support and let its allowed relation be a predicate on complete assignments on K(c). An assignment on A is legal when every constraint with support contained in A holds. Suppose subsets U(i) cover A, each local assignment is legal, and the assignments agree pointwise on all overlaps.

The sheaf of dependent functions on the discrete space V supplies the unique underlying assignment on A. If each support K(c) contained in A lies entirely inside some U(i), its restriction equals the corresponding local restriction, so local legality gives the constraint on the glued assignment. No pairwise reduction of a constraint is used. The argument works even for infinite supports when the same containment hypothesis holds; finite supports give the stated local-constraint setting.

Support containment is essential. On three Boolean coordinates impose that their exclusive-or is false. The three regions obtained by omitting one coordinate cover all positions, but none contains the ternary support. Restricting (false,false,true) to those regions gives legal local records with matching overlaps, while their unique union violates the ternary constraint. The general sheaf gluing condition is the standard one described in the Stacks Project, tag 006S.

## Linear boundary recovery

Let M and P be linear maps on a finite-dimensional vector space over a field, with legal interior S equal to kernel(M) and boundary readout the restriction of P to S. LinearMap.injective_domRestrict_iff identifies injectivity with disjointness of kernel(M) and kernel(P), equivalently their intersection is zero.

The paired map x maps to (M(x),P(x)) has kernel equal to that intersection by LinearMap.ker_prod. Rank-nullity therefore identifies injectivity on S with full column rank of the vertically stacked matrix [M;P]. For domain K to the power n the rank is n. These equivalent conditions give uniqueness only for boundary values in P(S); they do not imply that P(S) is the entire boundary space. For a target function on S, the earlier realized-image factorization instead requires only that the target be constant on the boundary fibers.

**Theorem 1.1 (Unique recovery on the realized image).**

$$\operatorname{ker}\left(beta\right) \subseteq \operatorname{ker}\left(P\right) \iff \exists! phi: \operatorname{range}\left(beta\right) \to Z, P = phi \circ \operatorname{rangeFactorization}\left(beta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.ker_beta_subset_ker_payload_iff_unique_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source, summary, and payload carriers have independent universes and may be empty. The factor is defined only on realized summary values. Existence and uniqueness follow by applying the split-surjection factorization theorem to the canonical range map and its section.

**Theorem 1.2 (Admission on complete raw global records).**

$$(\exists! phi: \operatorname{range}\left(beta\right) \to Bool, \operatorname{admissionIndicator}\left(J, K\right) = phi \circ \operatorname{rangeFactorization}\left(beta\right)) \iff \forall x, y: J, \operatorname{beta}\left(x\right) = \operatorname{beta}\left(y\right) \to (x \in K \iff y \in K)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain is the subtype J, the raw global join. Its Boolean payload is the indicator of K restricted to J. The actual worlds are J intersect K.

**Theorem 1.3 (Actual worlds are a union of whole restricted fibers).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_iff_union_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_iff_union_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem identifies J intersect K with the image in the ambient record carrier of all complete J-records sharing a summary with an admitted J-record. This equality is equivalent to unique admission factorization.

**Theorem 1.4 (The recovered admission test remains a constraint).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.admission_factor_test`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.admission_factor_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each complete raw record, the recovered Boolean test is true exactly when the record belongs to J intersect K. Factorization does not assert that the test is constantly true or authorize removing it.

**Theorem 1.5 (Canonical singleton empty join).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.rawJoin_empty`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.rawJoin_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty raw join is exactly the singleton containing emptyAssignment, transported back along componentScope_empty. This proves membership and uniqueness for the dependent Value family without any inhabited value fiber or local relation premise.

**Theorem 1.6 (Completion payloads use complete compatible records).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.mem_completion_payload_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.mem_completion_payload_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An assignment supplies a value for every variable in its scope and requires no value outside that scope. The raw join consists of assignments whose restriction to each node lies in that node's local relation. The complement join also enforces consistency of variables shared between its components.

The completion payload contains precisely those complete complement records matching the entire overlap assignment and whose union with the component record belongs to K. Membership is equivalent to one admitted raw global record having both specified restrictions. The restriction maps and compatible union are explicit.

**Theorem 1.7 (Recovery of the entire local completion set).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The payload codomain is the power set of the complete complement join. It factors uniquely through the realized component summary exactly when equal summaries give equal completion sets.

**Theorem 1.8 (Global-record pointwise completion tests).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_global_tests`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_global_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each summary fiber and complete complement record, completion membership is characterized by existence of an admitted complete raw global record with both exact restrictions. The membership equivalence uses the sheaf of dependent functions to construct the common assignment.

**Theorem 1.9 (The equivalent pointwise completion tests).**

Lean statement: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_tests`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set equality is equivalent to agreement of the membership test for every complete complement record. Each test includes both full boundary compatibility and membership of the union in K.

BoundaryOutputRetention names the additional requirement for later gluing: equal summaries preserve the entire boundary and every specified raw result on compatible complete complements. Results are read on the raw global join. Payload factorization alone does not establish that requirement or gluing congruence.

Source identifiers, dependency sets, and other requested payloads use the same arbitrary-target kernel criterion. Preserving a result image by existential witnesses is a separate contract; it does not recover a discarded payload.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.admission_factor_test`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.global_admission_iff_union_fibers`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.ker_beta_subset_ker_payload_iff_unique_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_global_tests`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.local_completion_tests`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.mem_completion_payload_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.rawJoin_empty`
- Dependency: [D5/S0/Rewriting/Quotients/SplitSurjectionFactorization](../../../S0/Rewriting/Quotients/SplitSurjectionFactorization.md)
