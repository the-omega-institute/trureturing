# Native state and the original writers

## Abstract

Literal acquired seed and payload state with all live numeric banks.

The fixed source has one acquired seed bit and four payload markers. Letters 0 and 1 mean alpha and beta. NativeControl is seed with an optional first letter, early with completed count t in Fin 3 and active phase, or fourth with the original active, pending and delivered controls. Its completedCount is respectively 0, t, 3 or 4. No clock or marker archive is a runtime field.

FiniteFields contains control and Registers. The latter retains an optional acquired seed, weight in Fin 5, optional syndrome in Fin 2, the actual ordered records QOne and QTwo, first-marker Z and optional ThirdSnapshot. The snapshot has fixed ell=2 and completed count 3, retaining its seed, weight and syndrome. The seed and syndrome are unset initially; all records are empty, weight and Z are zero. NativeSourceState also retains S=payloadReturns in Nat. AcquiredNativeState adds live alpha and beta counts initialized at zero. The full state has no finite-state assertion and installs no selected count bank.

Read has only the actual Letter as input. In seed control, equal pairs reject and return to seed-ready; unequal alpha-beta and beta-alpha pairs acquire seed 0 and 1. Acceptance initializes weight zero and syndrome 1+rho. Every Read increments exactly its acquired-letter count. In payload p, alpha completes marker 0 and beta suspends; in payload beta, alpha completes a return and beta completes marker 1. Every return increments S, including in segment four. Stop increments no count and preserves S; only the pending matching color is permitted, and delivered admits no operation.

Marker transactions route with old t and weight w. The first and second zero events are a and c; the first and second one events are b and d. At completions with old t<3, including the third completion, each is appended to scopes {a,c,d} and {b,c}. An unmatched third occurrence holds the records. Only the first marker writes Z. Weight adds the marker and syndrome adds its coefficient in (1,rho,1,rho), including rho=0. The third marker writes these fields before retaining the new bare snapshot; thereafter QOne, QTwo, Z and snapshot hold while live weight, syndrome, S and counts continue.

**Theorem 1.1 (Unbounded native return execution).**

$$\forall t:Nat, ((t\le3)\Rightarrow(\forall r:Registers, (\forall s:Nat, (\forall c:Counts, (\forall j:Nat, (\forall ops:\operatorname{List}(Operation), (\operatorname{execute}(\operatorname{atPhase}(t,r,s,c,p),\operatorname{append}(\operatorname{reads}(\operatorname{loopWord}(j)),ops))=\operatorname{execute}(\operatorname{atPhase}(t,r,s+j,\operatorname{Counts}(\operatorname{alpha}(c)+j,\operatorname{beta}(c)+j),p),ops))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.execute_payload_loops` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here atPhase(t,r,s,c,p) assembles the indicated original control, registers and banks; Counts(a,b) is the pair of numeric banks. For every t at most 3, every register and bank value, every natural j and every suffix ops, executing j beta-alpha returns preserves registers and phase, adds j to S and each count, then executes the same suffix from that actual successor. Induction over j follows two paid native Reads per return.

**Theorem 1.2 (Operations commute with finite projection).**

$$\forall c:AcquiredNativeState, (\forall op:Operation, (\operatorname{map}(pi,\operatorname{nativeStep}(c,op))=\operatorname{finiteStep}(\operatorname{pi}(c),op)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.finite_projection_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projection pi(c)=c.source.finiteFields erases S and counts. Map denotes Option.map. Both legal successors and failures agree with the independently defined finiteStep, so the projection preserves permissions. This is a projection of the full source, rather than reconstruction of its numeric banks.

**Theorem 1.3 (Written records recover the selected marker prefix).**

$$\forall rho:Letter, (\forall bs:\operatorname{List}(Letter), (\operatorname{recoverMarkers}(\operatorname{markerCut}(rho,bs))=\operatorname{take}(3,bs)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.marker_fields_recover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite marker word bs, markerCut(rho,bs) pairs the total writer fold markerRegisters(rho,bs) with payloadControl(length(bs),p) when length(bs)<4, and with pending(getLastD(bs,0)) otherwise. recoverMarkers reads completedCount and Registers only. It returns bs.take(3): at length zero the empty word, at length one Z, at length two Z and weight, and at every larger length the first-three QOne,QTwo,Z address. Induction through any remaining writer suffix proves that these selected fields hold. The total writer comparison at lengths greater than four does not make those lengths legal native executions.

**Theorem 1.4 (Exact bare fields and third latch).**

$$\forall rho:Letter, (\forall bs:\operatorname{List}(Letter), (\operatorname{FoldWrittenFields}(rho,bs,\operatorname{markerRegisters}(rho,bs))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.marker_fields_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FoldWrittenFields states that seed is some rho, live weight is markerWeight(bs) modulo five, syndrome is some (1+rho plus the full indexed coefficient sum), and Z is headD(bs,0). Here markerWeight is the sum of the natural bit values; the coefficient at zero-based index k is one for even k and rho for odd k. QOne and QTwo equal their writers on bs.take(3). Snapshot is none before three writes and otherwise retains rho, markerWeight(bs.take(3)) modulo five and markerSyndrome(rho,bs.take(3)). Arbitrary-length write-update induction establishes the live weight and syndrome formulas. After the third write, another arbitrary-length induction preserves records, Z and latch. For legal four-slot prefixes the existing weight bound removes the modulus and gives the original exact WrittenFields predicate.

PrefixForm is separate proof data: an ordered list of rejected-pair kinds followed by seed-ready, one first seed letter, or an acquired seed with PayloadForm. PayloadForm uses independent concatenations of loopWord and pWord, optional pending beta, exactly four completion slots, matching pending Stop and delivered. render concatenates these words. reconstruct calculates banks and marker writes from this data without executing Read. No form or rejected-pair list occurs in native state.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.execute_payload_loops`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.finite_projection_commutes`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.marker_fields_exact`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.marker_fields_recover`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw](FourthSegmentStoppedLaw.md)
