# Same-seed stopping-law rigidity and sharp actual-read bounds

## Abstract

Same-seed stopping-law rigidity and sharp actual-read bounds

The probability space is the original source law times an arbitrary probability measure nu on an arbitrary measurable seed space U. No atomlessness, standard Borel assumption or extra randomizer is required. The full joint law retains the unchanged seed together with the hidden endpoint, output, return indicator and paid count. A seed-independent input observation has no seed argument.

The witness stoppingRule(j,k) reads j+2i+1 for i from one through k, returns a1 at the first one reply and returns a0 after k zero replies. Its addresses and decisions depend on neither the bias nor the seed. Write W for this original-rule witness and T(n)=(1-p)^n+p^n.

The nonzero stopping masses, for each Boolean s, are pi(s)*d(i)/2 at (b(s),a(true),true,i) for 1 <= i <= k; pi(s)*T(k+1)/2 at (b(s),a(false),true,k); and pi(s)/2 at (a(s),a(false),true,k). Every other observation has mass zero, including every nonreturn and zero-count observation. Here d(i)=T(i)-T(i+1)=pi(false)^i*pi(true)+pi(true)^i*pi(false), which is strictly positive.

**Theorem 1.1 (Full joint equality determines almost every seed section).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{nu} : \operatorname{Measure} (\operatorname{U})), (\forall (\operatorname{Q} : \operatorname{RawRule} (\operatorname{U})), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{w} : (\operatorname{SourcePoint} \to \operatorname{Observation})), ([\operatorname{IsProbabilityMeasure} (\operatorname{nu})] ((\operatorname{CompletionLawful} (\operatorname{Q}, \operatorname{nu})) \land (\operatorname{TotalCap} (\operatorname{Q}, \operatorname{k})) \land (\operatorname{Measurable} (\operatorname{w})) \land (\operatorname{fullLaw} (\operatorname{Q}, \operatorname{beta}, \operatorname{j}, \operatorname{nu}) = \operatorname{independentJointLaw} (\operatorname{beta}, \operatorname{nu}, \operatorname{w}))) \to (\operatorname{AE} (\operatorname{nu}, \operatorname{fun} \operatorname{u} \mapsto (\forall (\operatorname{z} : \operatorname{Observation}), (\operatorname{fullMass} (\operatorname{beta}, \operatorname{lawWindow} (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{u})), \operatorname{j}, \operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{u}), \operatorname{z}) = \operatorname{real} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{fiber} (\operatorname{w}, \operatorname{z})))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.full_same_seed_law_forces_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

independentJointLaw(beta,nu,w) is the pushforward of sourceLaw(beta).prod(nu) by (source,u) mapped to (u,w(source)); fiber(w,z) is its source observation fiber. Positive-measure countable tree fibers permit cancellation of their seed mass. Null fibers are discarded by one countable union. All observation equalities hold simultaneously, without conditioning on singleton seeds.

**Theorem 1.2 (Exact witness law on every seed rectangle).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{nu} : \operatorname{Measure} (\operatorname{U})), (\forall (\operatorname{B} : \operatorname{Set} (\operatorname{U})), (\forall (\operatorname{z} : \operatorname{Observation}), ([\operatorname{IsProbabilityMeasure} (\operatorname{nu})] ((1 \le \operatorname{k}) \land (\operatorname{MeasurableSet} (\operatorname{B}))) \to (\operatorname{real} (\operatorname{fullLaw} (\operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{beta}, \operatorname{j}, \operatorname{nu}), \operatorname{rectangleSingleton} (\operatorname{B}, \operatorname{z})) = (\operatorname{real} (\operatorname{nu}, \operatorname{B}) * \operatorname{stoppingMass} (\operatorname{beta}, \operatorname{k}, \operatorname{z}))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.stopping_witness_full_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

rectangleSingleton(B,z) is B times the singleton observation z. stoppingMass gives every listed atom and gives zero to every unlisted tuple. In the opposite phase the witness reads only separators and returns a0 at depth k; in the active phase its first one reply ends the run, so early terminal depths are exact.

**Theorem 1.3 (Almost every raw seed has the exact stopping path).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{nu} : \operatorname{Measure} (\operatorname{U})), (\forall (\operatorname{Q} : \operatorname{RawRule} (\operatorname{U})), ([\operatorname{IsProbabilityMeasure} (\operatorname{nu})] ((1 \le \operatorname{k}) \land (\operatorname{CompletionLawful} (\operatorname{Q}, \operatorname{nu})) \land (\operatorname{TotalCap} (\operatorname{Q}, \operatorname{k})) \land (\operatorname{SameFullLaw} (\operatorname{Q}, \operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{beta}, \operatorname{j}, \operatorname{nu}))) \to (\operatorname{AE} (\operatorname{nu}, \operatorname{fun} \operatorname{u} \mapsto (\exists (\operatorname{es} : \operatorname{List} (\operatorname{Int})), ((\operatorname{length} (\operatorname{es}) = \operatorname{k}) \land (\operatorname{Nodup} (\operatorname{es})) \land (\exists (\operatorname{L} : \operatorname{Int}), ((\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{u}) = \operatorname{stopComb} (\operatorname{mapAddresses} (\operatorname{es}, \operatorname{not} (\operatorname{j})))) \land (\operatorname{toFinset} (\operatorname{es}) = \operatorname{pathEdges} (\operatorname{L}, \operatorname{k})) \land (\operatorname{notMem} (\operatorname{toInt} (\operatorname{j}), \operatorname{pathVertices} (\operatorname{L}, \operatorname{k})))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_stopping_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This statement quantifies arbitrary completion-lawful raw rules with the all-path total cap and the same full joint law as W. Almost every normalized seed tree is the k-node stopping comb on a duplicate-free consecutive edge interval detached from the original target. It does not identify arbitrary exceptional seed versions pointwise.

**Theorem 1.4 (Sharp bound and witness attainment for actual paid reads).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{nu} : \operatorname{Measure} (\operatorname{U})), (\forall (\operatorname{Q} : \operatorname{RawRule} (\operatorname{U})), ([\operatorname{IsProbabilityMeasure} (\operatorname{nu})] ((1 \le \operatorname{k}) \land (\operatorname{CompletionLawful} (\operatorname{Q}, \operatorname{nu})) \land (\operatorname{TotalCap} (\operatorname{Q}, \operatorname{k})) \land (\operatorname{SameFullLaw} (\operatorname{Q}, \operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{beta}, \operatorname{j}, \operatorname{nu}))) \to (((\frac{(1 + \operatorname{T} (\operatorname{beta}, \operatorname{k}))}{2} \le \operatorname{real} (\operatorname{prod} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{nu}), \operatorname{remote} (\operatorname{Q}, \operatorname{j}, ((2 * \operatorname{k}) + 1)))) \land (\operatorname{real} (\operatorname{prod} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{nu}), \operatorname{remote} (\operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{j}, ((2 * \operatorname{k}) + 1))) = \frac{(1 + \operatorname{T} (\operatorname{beta}, \operatorname{k}))}{2})) \land ((\operatorname{k} = 1) \to (\operatorname{real} (\operatorname{prod} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{nu}), \operatorname{remote} (\operatorname{Q}, \operatorname{j}, ((2 * \operatorname{k}) + 1))) = 1)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_sharp_remote_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The event remote(Q,j,2k+1) asks whether an actual original-rule read has distance at least 2k+1 from the unchanged endpoint j. The same witness attains the lower bound exactly. At k=1 every preserving competitor has remote-read probability one. Repeated and separator calls remain included in the cap.

**Theorem 1.5 (Lawfulness, cap, all branch returns, full law and radius).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{nu} : \operatorname{Measure} (\operatorname{U})), ([\operatorname{IsProbabilityMeasure} (\operatorname{nu})] (1 \le \operatorname{k}) \to ((\operatorname{Lawful} (\operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}))) \land (\operatorname{TotalCap} (\operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{k})) \land (\forall (\operatorname{v} : \operatorname{Execution}), ((\operatorname{mem} (\operatorname{v}, \operatorname{formalRuns} (\operatorname{witnessTree} (\operatorname{j}, \operatorname{k})))) \to ((\operatorname{returned} (\operatorname{v}) = \operatorname{true}) \land (1 \le \operatorname{paid} (\operatorname{v})) \land (\operatorname{paid} (\operatorname{v}) \le \operatorname{k})))) \land (\forall (\operatorname{B} : \operatorname{Set} (\operatorname{U})), (\forall (\operatorname{z} : \operatorname{Observation}), ((\operatorname{MeasurableSet} (\operatorname{B})) \to (\operatorname{real} (\operatorname{fullLaw} (\operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{beta}, \operatorname{j}, \operatorname{nu}), \operatorname{rectangleSingleton} (\operatorname{B}, \operatorname{z})) = (\operatorname{real} (\operatorname{nu}, \operatorname{B}) * \operatorname{stoppingMass} (\operatorname{beta}, \operatorname{k}, \operatorname{z})))))) \land (\operatorname{WithinActualRadius} (\operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{j}, ((2 * \operatorname{k}) + 1)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.stopping_witness_original_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arbitrary measurable probability seed space, permitted bias, endpoint j and k at least one, W is lawful, has total cap k on every source and seed, and every formal branch returns with a paid count between one and k. For every measurable seed set B and every observation z its full-law rectangle mass is nu(B) times stoppingMass(beta,k,z). Every actual read of W has distance at most 2k+1 from j.

**Theorem 1.6 (Every raw preserving actual radius is at least 2k+1).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{nu} : \operatorname{Measure} (\operatorname{U})), (\forall (\operatorname{Q} : \operatorname{RawRule} (\operatorname{U})), (\forall (\operatorname{R} : \operatorname{Nat}), ([\operatorname{IsProbabilityMeasure} (\operatorname{nu})] (((1 \le \operatorname{k}) \land (\operatorname{CompletionLawful} (\operatorname{Q}, \operatorname{nu})) \land (\operatorname{TotalCap} (\operatorname{Q}, \operatorname{k})) \land (\operatorname{SameFullLaw} (\operatorname{Q}, \operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{beta}, \operatorname{j}, \operatorname{nu}))) \land (\operatorname{WithinActualRadius} (\operatorname{Q}, \operatorname{j}, \operatorname{R}))) \to (((2 * \operatorname{k}) + 1) \le \operatorname{R}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_radius_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

WithinActualRadius quantifies every acquired actual read record, including null and nonreturn paths. A smaller radius makes the positive-mass remote event empty and contradicts the sharp probability bound. Together with the witness contract this proves an attained least natural radius, rather than merely a lower-bound predicate.

**Theorem 1.7 (Ambient completed versions admit the same ordinary sections).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{nu} : \operatorname{Measure} (\operatorname{U})), (\forall (\operatorname{Q} : \operatorname{CompletedRule} (\operatorname{U})), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{w} : (\operatorname{SourcePoint} \to \operatorname{Observation})), ([\operatorname{IsProbabilityMeasure} (\operatorname{nu})] ((\operatorname{Lawful} (\operatorname{Q}, \operatorname{prod} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{nu}))) \land (\operatorname{TotalCap} (\operatorname{Q}, \operatorname{k})) \land (\operatorname{Measurable} (\operatorname{w})) \land (\operatorname{fullLaw} (\operatorname{Q}, \operatorname{beta}, \operatorname{j}, \operatorname{nu}) = \operatorname{independentJointLaw} (\operatorname{beta}, \operatorname{nu}, \operatorname{w}))) \to (\exists (\operatorname{T} : (\operatorname{U} \to \operatorname{CappedTrees} (\operatorname{k}))), ((\operatorname{Measurable} (\operatorname{T})) \land (\operatorname{AE} (\operatorname{prod} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{nu}), \operatorname{fun} \operatorname{p} \mapsto (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{p}) = \operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{snd} (\operatorname{p})))))) \land (\operatorname{AE} (\operatorname{nu}, \operatorname{fun} \operatorname{u} \mapsto ((\operatorname{AE} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{fun} \operatorname{s} \mapsto (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{pair} (\operatorname{s}, \operatorname{u})) = \operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{u}))))) \land (\forall (\operatorname{z} : \operatorname{Observation}), (\operatorname{fullMass} (\operatorname{beta}, \operatorname{lawWindow} (\operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{u}))), \operatorname{j}, \operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{u})), \operatorname{z}) = \operatorname{real} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{fiber} (\operatorname{w}, \operatorname{z}))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.full_law_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arbitrary probability seed space U, bias beta, endpoint j, ambient-lawful CompletedRule Q, natural k with Q.TotalCap(k), and measurable source observation w whose seed joint law equals Q.fullLaw, there is a measurable selector T:U to trees of height at most k. Q.normalize equals T(seed) product-almost everywhere; for almost every seed the equality holds source-almost everywhere and every observation mass equals the source mass of w. No everywhere selector identity is asserted for ambient null changes.

**Theorem 1.8 (Completed competitors have rigidity and the sharp read bound).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{j} : \operatorname{Bool}), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{nu} : \operatorname{Measure} (\operatorname{U})), (\forall (\operatorname{Q} : \operatorname{CompletedRule} (\operatorname{U})), ([\operatorname{IsProbabilityMeasure} (\operatorname{nu})] ((1 \le \operatorname{k}) \land (\operatorname{Lawful} (\operatorname{Q}, \operatorname{prod} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{nu}))) \land (\operatorname{TotalCap} (\operatorname{Q}, \operatorname{k})) \land (\operatorname{fullLaw} (\operatorname{Q}, \operatorname{beta}, \operatorname{j}, \operatorname{nu}) = \operatorname{fullLaw} (\operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{beta}, \operatorname{j}, \operatorname{nu}))) \to ((\exists (\operatorname{T} : (\operatorname{U} \to \operatorname{CappedTrees} (\operatorname{k}))), ((\operatorname{Measurable} (\operatorname{T})) \land (\operatorname{AE} (\operatorname{nu}, \operatorname{fun} \operatorname{u} \mapsto ((\operatorname{AE} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{fun} \operatorname{s} \mapsto (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{pair} (\operatorname{s}, \operatorname{u})) = \operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{u}))))) \land (\exists (\operatorname{es} : \operatorname{List} (\operatorname{Int})), ((\operatorname{length} (\operatorname{es}) = \operatorname{k}) \land (\operatorname{Nodup} (\operatorname{es})) \land (\exists (\operatorname{L} : \operatorname{Int}), ((\operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{u})) = \operatorname{stopComb} (\operatorname{mapAddresses} (\operatorname{es}, \operatorname{not} (\operatorname{j})))) \land (\operatorname{toFinset} (\operatorname{es}) = \operatorname{pathEdges} (\operatorname{L}, \operatorname{k})) \land (\operatorname{notMem} (\operatorname{toInt} (\operatorname{j}), \operatorname{pathVertices} (\operatorname{L}, \operatorname{k})))))))))))) \land (\frac{(1 + \operatorname{T} (\operatorname{beta}, \operatorname{k}))}{2} \le \operatorname{real} (\operatorname{prod} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{nu}), \operatorname{remote} (\operatorname{Q}, \operatorname{j}, ((2 * \operatorname{k}) + 1)))) \land (\operatorname{real} (\operatorname{prod} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{nu}), \operatorname{remote} (\operatorname{stoppingRule} (\operatorname{j}, \operatorname{k}), \operatorname{j}, ((2 * \operatorname{k}) + 1))) = \frac{(1 + \operatorname{T} (\operatorname{beta}, \operatorname{k}))}{2}) \land ((\operatorname{k} = 1) \to (\operatorname{real} (\operatorname{prod} (\operatorname{sourceLaw} (\operatorname{beta}), \operatorname{nu}), \operatorname{remote} (\operatorname{Q}, \operatorname{j}, ((2 * \operatorname{k}) + 1))) = 1)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_stopping_results` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arbitrary measurable probability seed space, permitted bias, endpoint j, k at least one, ambient-lawful completed Q with total cap k and the full law of W, there is one measurable bounded tree selector. Almost every seed has source-almost-everywhere agreement with the actual completed expansion and the exact detached k-node stopping-path geometry. The actual completed remote probability is at least (1+T(k))/2; W attains equality, and when k=1 the competitor probability is one.

For both raw and ambient completed competitors, the natural radii admitting a lawful total-cap-k representative with this same full law have least element 2k+1. The witness realizes membership on the same U and nu, and the actual remote event excludes each smaller radius. This is the minimum for the witness law at fixed k; it does not assert universal all-k radius nonemptiness for arbitrary inputs.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.full_law_sections`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.full_same_seed_law_forces_sections`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_radius_lower`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_sharp_remote_probability`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_stopping_results`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.original_rule_stopping_rigidity`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.stopping_witness_full_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SeedLaw.stopping_witness_original_contract`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore](FiniteCore.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization](SemanticNormalization.md)
