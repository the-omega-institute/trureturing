# Exact Original Source Orbit Certificates

## Abstract

Finite original-source orbit guards characterize truthful chronological execution and correct termination without assuming legality.

Fix any universe-polymorphic finite complete nominal carrier E, original Observer E and immutable original FreeMagma Bool source U. Queries are unrestricted literal Boolean words; the raw reply type has alpha, beta, branch and absent. The certificate is an external mathematical check on installed rows and original source reads. It adds no source, target, fuel or history port to the observer.

**Definition 1.1 (Finite raw row certificate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.SourceCertificate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.SourceCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let n=card E and F=ActualObserverAbsorbingNormalization.sourceStep M U. This existing step uses the original queryReply at a query and fixes a halt row. SourceCertificate requires decoder(e0)=[], an index j in Fin n with action(F iterated j at e0)=Halt(finiteDecision U), and guards at every i in Fin n. Each guard checks raw CacheTruth of the complete ordered decoder and, at its installed query q, the literal equality decoder(transition(e,queryReply(decoder(e),q,U)))=cacheUpdate(decoder(e),q,queryReply(decoder(e),q,U)). This includes the terminal cache and every repeated occurrence of a halt in the rest of the window. A cache hit keeps its first raw report and still makes a logical query. No coarse cache equality is used.

**Definition 1.2 (Decision on finite explicit data).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.sourceCertificateDecidable`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.sourceCertificateDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite indices and finite raw decoded lists supply all tests. The apparently unbounded query implication reduces to the one literal address installed at that row; a halt makes it vacuous. The checker never asks Legal, Admissible, Run or PairReach for a truth value. The original finiteDecision compares all candidate original substitution preimages of leaf count at most U.length through the existing boundedSources enumeration. Its correctness is the frozen acquisition_foundation; it is a verifier operation, not an observer readout. Noncomputable finite-type enumeration does not assert an efficient executable implementation.

**Definition 1.3 (Boolean acceptance).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.sourceCheck`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.sourceCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceCheck is decide applied to SourceCertificate using its explicit finite decision instance. It accepts exactly the finite n-row certificate. Nonhalting cycles cannot pass the halt clause; unreachable cycles impose no extra rejection condition. All nominal rows still count toward n.

**Theorem 1.4 (Exact legality and original correct termination).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Observer}\left(E\right), (\forall U: Source, ((\operatorname{sourceCheck}\left(M, U\right) = \operatorname{true}\left(\right)) \iff ((\operatorname{Legal}\left(M, U\right)) \land (\exists t: RawHistory, (\exists f: E, (\exists b: Bool, ((\operatorname{Run}\left(M, U, \operatorname{eZero}\left(M\right), t, f, b\right)) \land ((b = \operatorname{true}\left(\right)) \iff (\operatorname{Positive}\left(U\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.sourceCheck_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Soundness first proves, without Legal, that every original ActualPrefix of length k reaches F iterated k at e0. If the certificate halts at j, an ActualPrefix has length at most j: extending a prefix of length j would require its halt row to be a query. Thus every actual prefix lies in the checked finite window. The raw guards earn Legal on all actual prefixes, rather than using legality to justify the test. An induction on the halt index constructs an original finite Run, and acquisition_foundation identifies its finiteDecision bit with literal third-substitution image membership.

Completeness directly consumes the original run_length_bound and run_orbit declarations. A terminating trace has length strictly less than card E and its terminal row is the matching orbit row. Every earlier orbit row is an actual prefix, and every later row is the same absorbing halt with its terminal prefix witness. Legal therefore supplies every raw guard, including after the first halt. The new prefix-to-window bridge is live in the sound direction; the existing suppliers requiring Legal do not supply it.

This result is sourcewise and assumes no global Strategy, source budget, price or all-history factorization. For a bounded source class, apply it to every member of allowedSources N. Independently test a finite closed subset of E times E containing the initial pair, closed under every coarse-equal raw reply pair, with equal actions at every member. The frozen pairReach_iff_equal_coarse_response_words characterization and Mathlib List.rel_foldl propagate certificate membership and prove soundness; the finite set of generated pairs witnesses completeness. The original pairActionInvariant_iff_allHistoryFactorization then supplies the separate all-history obligation, including impossible histories. A passing source check alone does not supply that obligation.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.SourceCertificate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.sourceCertificateDecidable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.sourceCheck`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks.sourceCheck_iff`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable](ActualObserverFiniteTable.md)
