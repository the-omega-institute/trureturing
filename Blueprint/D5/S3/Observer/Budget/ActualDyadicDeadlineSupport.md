# Actual Dyadic Deadline Support

## Abstract

Primitive forward executions realize exactly the allowed dyadic final reads.

In the formulas, record(N,past) has event count N and read history past. Execution and ReachedRecord display their period index P while suppressing proof arguments. div and mod denote natural-number quotient and remainder; val unwraps finite values.

A record consists of an event count and chronological time/raw-bit reads. A policy takes only that record and chooses one forward event, a read, or a stop. Execution denotes a finite physical run from a supplied record. No source or future noise is an input to the policy. Fix d>=0, P=2^(d+1), a known b in Fin 2, and E(t)=P-1+P wt(t)-2t. The original query parameter is j=d+1.

**Theorem 1.1 (Physical read order).**

$$\forall P: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall policy: \left(\left(Record\right) \to \left(\operatorname{Action}\left(P\right)\right)\right), \left(\forall r: \left(\operatorname{Fin}\left(P\right)\right), \left(\forall start: \left(Record\right), \left(\forall word: \left(\operatorname{List}\left(\operatorname{Fin}\left(2\right)\right)\right), \left(\forall terminal: \left(\left(Record\right) \times \left(\operatorname{Fin}\left(P\right)\right)\right), \left(\left(\left(0 < P\right) \land \left(\operatorname{Execution}\left(P, b, policy, r, start, word, terminal\right)\right)\right) \implies \left(\left(\operatorname{events}\left(start\right) \le \operatorname{events}\left(\operatorname{fst}\left(terminal\right)\right)\right) \land \left(\exists trace: \left(\operatorname{List}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \left(\left(\operatorname{reads}\left(\operatorname{fst}\left(terminal\right)\right) = \operatorname{append}\left(\operatorname{reads}\left(start\right), trace\right)\right) \land \left(\left(\operatorname{length}\left(trace\right) = \operatorname{length}\left(word\right)\right) \land \left(\left(\forall item: \left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right), \left(\left(item \in trace\right) \implies \left(\left(\operatorname{events}\left(start\right) \le \operatorname{fst}\left(item\right)\right) \land \left(\operatorname{fst}\left(item\right) \le \operatorname{events}\left(\operatorname{fst}\left(terminal\right)\right)\right)\right)\right)\right) \land \left(\operatorname{Pairwise}\left(trace, \lambda x: \left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\lambda y: \left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\operatorname{fst}\left(x\right) \le \operatorname{fst}\left(y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.execution_read_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any positive period and any primitive run, events never decrease. The new read trace has the read word's length, lies between the starting and reporting clocks, and is pairwise ordered by time. Silent events after the final read are permitted; the reporting clock need not be the final-read clock.

**Theorem 1.2 (All-source causal realization).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall D: \left(\mathbb{N}\right), \left(\forall t: \left(\mathbb{N}\right), \left(\forall u: \left(\mathbb{N}\right), \left(\forall K: \left(\mathbb{N}\right), \left(\left(\left(\left(\operatorname{sharpWait}\left(\left(d\right) + \left(1\right)\right) \le D\right) \land \left(t < \left(2\right)^{d}\right)\right) \land \left(\left(u < 2\right) \land \left(\left(\operatorname{earliestTime}\left(d, t\right)\right) + \left(\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right) \cdot \left(K\right)\right) \le D\right)\right)\right) \implies \left(let P: \mathbb{N} := \left(2\right)^{\left(d\right) + \left(1\right)}; \left(\exists policy: \left(\left(Record\right) \to \left(\operatorname{Action}\left(P\right)\right)\right), \left(\left(\forall r: \left(\operatorname{Fin}\left(P\right)\right), \left(\exists word: \left(\operatorname{List}\left(\operatorname{Fin}\left(2\right)\right)\right), \left(\exists terminal: \left(\left(Record\right) \times \left(\operatorname{Fin}\left(P\right)\right)\right), \left(\left(\left(\operatorname{Execution}\left(P, b, policy, r, \operatorname{record}\left(0, \operatorname{nil}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), word, terminal\right)\right) \land \left(\left(\operatorname{length}\left(word\right) \le \left(d\right) + \left(1\right)\right) \land \left(\operatorname{snd}\left(terminal\right) = r\right)\right)\right) \land \left(\operatorname{events}\left(\operatorname{fst}\left(terminal\right)\right) \le D\right)\right)\right)\right)\right) \land \left(\exists r: \left(\operatorname{Fin}\left(P\right)\right), \left(\exists word: \left(\operatorname{List}\left(\operatorname{Fin}\left(2\right)\right)\right), \left(\exists terminal: \left(\left(Record\right) \times \left(\operatorname{Fin}\left(P\right)\right)\right), \left(\exists before: \left(\operatorname{List}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \left(\exists bit: \left(\operatorname{Fin}\left(2\right)\right), \left(\left(\operatorname{val}\left(r\right) = \left(\left(2\right) \cdot \left(t\right)\right) + \left(u\right)\right) \land \left(\left(\left(\operatorname{Execution}\left(P, b, policy, r, \operatorname{record}\left(0, \operatorname{nil}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), word, terminal\right)\right) \land \left(\left(\operatorname{length}\left(word\right) \le \left(d\right) + \left(1\right)\right) \land \left(\operatorname{snd}\left(terminal\right) = r\right)\right)\right) \land \left(\left(\operatorname{events}\left(\operatorname{fst}\left(terminal\right)\right) = \left(\operatorname{earliestTime}\left(d, t\right)\right) + \left(\left(P\right) \cdot \left(K\right)\right)\right) \land \left(\operatorname{reads}\left(\operatorname{fst}\left(terminal\right)\right) = \operatorname{append}\left(before, \operatorname{singletonList}\left(\left(\operatorname{events}\left(\operatorname{fst}\left(terminal\right)\right), bit\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.deadline_allowed_primitive_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If D>=sharpWait(d+1), t<2^d, u<2, and E(t)+PK<=D, one record-only policy succeeds on every source in at most d+1 reads and reports by D. On source 2t+u it stops immediately after its literal final read at E(t)+PK.

**Theorem 1.3 (Physical final-read normal form).**

$$\forall P: \left(\mathbb{N}\right), \left(\forall d: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall policy: \left(\left(Record\right) \to \left(\operatorname{Action}\left(P\right)\right)\right), \left(\forall r: \left(\operatorname{Fin}\left(P\right)\right), \left(\forall word: \left(\operatorname{List}\left(\operatorname{Fin}\left(2\right)\right)\right), \left(\forall terminal: \left(\left(Record\right) \times \left(\operatorname{Fin}\left(P\right)\right)\right), \left(\left(\left(0 < P\right) \land \left(\left(P = \left(2\right)^{\left(d\right) + \left(1\right)}\right) \land \left(\left(\forall r: \left(\operatorname{Fin}\left(P\right)\right), \left(\exists word: \left(\operatorname{List}\left(\operatorname{Fin}\left(2\right)\right)\right), \left(\exists terminal: \left(\left(Record\right) \times \left(\operatorname{Fin}\left(P\right)\right)\right), \left(\left(\operatorname{Execution}\left(P, b, policy, r, \operatorname{record}\left(0, \operatorname{nil}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), word, terminal\right)\right) \land \left(\left(\operatorname{length}\left(word\right) \le \left(d\right) + \left(1\right)\right) \land \left(\operatorname{snd}\left(terminal\right) = r\right)\right)\right)\right)\right)\right) \land \left(\left(\operatorname{Execution}\left(P, b, policy, r, \operatorname{record}\left(0, \operatorname{nil}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), word, terminal\right)\right) \land \left(\operatorname{length}\left(word\right) \le \left(d\right) + \left(1\right)\right)\right)\right)\right)\right) \implies \left(\exists past: \left(\operatorname{List}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \left(\exists N: \left(\mathbb{N}\right), \left(\exists bit: \left(\operatorname{Fin}\left(2\right)\right), \left(\exists K: \left(\mathbb{N}\right), \left(\left(\operatorname{length}\left(past\right) = d\right) \land \left(\left(\operatorname{acquiredPrefix}\left(P, b, past, 0\right) = \operatorname{div}\left(\operatorname{val}\left(r\right), 2\right)\right) \land \left(\left(\operatorname{reads}\left(\operatorname{fst}\left(terminal\right)\right) = \operatorname{append}\left(past, \operatorname{singletonList}\left(\left(N, bit\right)\right)\right)\right) \land \left(\left(\operatorname{ReachedRecord}\left(P, b, policy, r, \operatorname{record}\left(0, \operatorname{nil}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \operatorname{record}\left(N, past\right)\right)\right) \land \left(\left(\operatorname{policy}\left(\operatorname{record}\left(N, past\right)\right) = read\right) \land \left(\left(\operatorname{val}\left(bit\right) = \operatorname{mod}\left(\left(\left(\operatorname{val}\left(b\right)\right) + \left(\operatorname{div}\left(N, P\right)\right)\right) + \left(\operatorname{mod}\left(\operatorname{val}\left(r\right), 2\right)\right), 2\right)\right) \land \left(\left(N = \left(\operatorname{earliestTime}\left(d, \operatorname{div}\left(\operatorname{val}\left(r\right), 2\right)\right)\right) + \left(\left(P\right) \cdot \left(K\right)\right)\right) \land \left(N \le \operatorname{events}\left(\operatorname{fst}\left(terminal\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_final_time_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every all-source successful policy under the dyadic read budget, each bounded actual execution has exactly d pre-final reads. Their normalized chronological fold is floor(r/2). The pre-final record is physically reached, the policy reads there, and raw Y=(b+floor(N/P)+r mod 2) mod 2. Its literal final time is E(floor(r/2))+PK for a nonnegative K and is no later than reporting.

DeadlineObservation(d,b,D,policy,r,past,N,Y) means that a correct primitive execution from (0,[]) uses at most d+1 reads, ends its read trace in past++[(N,Y)], and has N<=D. The all-source family requires such an observation for every source. SupportedTime ranges over all policies in this family and all observations with floor(r/2)=t. The deadline always bounds N, rather than any later reporting event.

**Theorem 1.4 (Reached deadline observations).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall D: \left(\mathbb{N}\right), \left(let P: \mathbb{N} := \left(2\right)^{\left(d\right) + \left(1\right)}; \left(\forall policy: \left(\left(Record\right) \to \left(\operatorname{Action}\left(P\right)\right)\right), \left(\forall r: \left(\operatorname{Fin}\left(P\right)\right), \left(\forall past: \left(\operatorname{List}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \left(\forall N: \left(\mathbb{N}\right), \left(\forall bit: \left(\operatorname{Fin}\left(2\right)\right), \left(\left(\left(\operatorname{actualDeadlineFamily}\left(d, b, D, policy\right)\right) \land \left(\operatorname{DeadlineObservation}\left(d, b, D, policy, r, past, N, bit\right)\right)\right) \implies \left(\left(\operatorname{length}\left(past\right) = d\right) \land \left(\left(\operatorname{acquiredPrefix}\left(P, b, past, 0\right) = \operatorname{div}\left(\operatorname{val}\left(r\right), 2\right)\right) \land \left(\left(\operatorname{ReachedRecord}\left(P, b, policy, r, \operatorname{record}\left(0, \operatorname{nil}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \operatorname{record}\left(N, past\right)\right)\right) \land \left(\left(\operatorname{policy}\left(\operatorname{record}\left(N, past\right)\right) = read\right) \land \left(\left(\operatorname{val}\left(bit\right) = \operatorname{mod}\left(\left(\left(\operatorname{val}\left(b\right)\right) + \left(\operatorname{div}\left(N, P\right)\right)\right) + \left(\operatorname{mod}\left(\operatorname{val}\left(r\right), 2\right)\right), 2\right)\right) \land \left(\exists K: \left(\mathbb{N}\right), \left(N = \left(\operatorname{earliestTime}\left(d, \operatorname{div}\left(\operatorname{val}\left(r\right), 2\right)\right)\right) + \left(\left(P\right) \cdot \left(K\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_observation_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a policy in actualDeadlineFamily(d,b,D), each deadline observation has the acquired prefix, reached pre-final record, read action, literal raw bit, and nonnegative period-delay normal form. The history in this statement is the history actually appearing in that observation.

**Theorem 1.5 (One policy and one history for both siblings).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall D: \left(\mathbb{N}\right), \left(\forall t: \left(\mathbb{N}\right), \left(\forall K: \left(\mathbb{N}\right), \left(\left(\left(\left(\operatorname{sharpWait}\left(\left(d\right) + \left(1\right)\right) \le D\right) \land \left(t < \left(2\right)^{d}\right)\right) \land \left(\left(\operatorname{earliestTime}\left(d, t\right)\right) + \left(\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right) \cdot \left(K\right)\right) \le D\right)\right) \implies \left(let P: \mathbb{N} := \left(2\right)^{\left(d\right) + \left(1\right)}; \left(let N: \mathbb{N} := \left(\operatorname{earliestTime}\left(d, t\right)\right) + \left(\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right) \cdot \left(K\right)\right); \left(\exists policy: \left(\left(Record\right) \to \left(\operatorname{Action}\left(P\right)\right)\right), \left(\left(\operatorname{actualDeadlineFamily}\left(d, b, D, policy\right)\right) \land \left(\exists past: \left(\operatorname{List}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \left(\left(\operatorname{length}\left(past\right) = d\right) \land \left(\left(\operatorname{acquiredPrefix}\left(P, b, past, 0\right) = t\right) \land \left(\left(\operatorname{policy}\left(\operatorname{record}\left(N, past\right)\right) = read\right) \land \left(\forall u: \left(\operatorname{Fin}\left(2\right)\right), \left(\exists r: \left(\operatorname{Fin}\left(P\right)\right), \left(\exists bit: \left(\operatorname{Fin}\left(2\right)\right), \left(\left(\operatorname{val}\left(r\right) = \left(\left(2\right) \cdot \left(t\right)\right) + \left(\operatorname{val}\left(u\right)\right)\right) \land \left(\left(\operatorname{ReachedRecord}\left(P, b, policy, r, \operatorname{record}\left(0, \operatorname{nil}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \operatorname{record}\left(N, past\right)\right)\right) \land \left(\left(\operatorname{val}\left(bit\right) = \operatorname{mod}\left(\left(\left(\operatorname{val}\left(b\right)\right) + \left(\operatorname{div}\left(N, P\right)\right)\right) + \left(\operatorname{val}\left(u\right)\right), 2\right)\right) \land \left(\operatorname{DeadlineObservation}\left(d, b, D, policy, r, past, N, bit\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_pair_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume D>=sharpWait(d+1), t<2^d, and E(t)+PK<=D for a natural K. For each such allowed time, the same all-source policy and reached pre-final history realize both final source bits. The writer's acquired prefix and read action are fixed before either final bit is obtained. The final raw bit is retained.

**Theorem 1.6 (Exact actual supported times).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall D: \left(\mathbb{N}\right), \left(\forall t: \left(\mathbb{N}\right), \left(\forall N: \left(\mathbb{N}\right), \left(\left(\left(\operatorname{sharpWait}\left(\left(d\right) + \left(1\right)\right) \le D\right) \land \left(t < \left(2\right)^{d}\right)\right) \implies \left(\left(\operatorname{actualSupportedTime}\left(d, b, D, t, N\right)\right) \iff \left(\exists K: \left(\mathbb{N}\right), \left(\left(N = \left(\operatorname{earliestTime}\left(d, t\right)\right) + \left(\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right) \cdot \left(K\right)\right)\right) \land \left(N \le D\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_time_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With D at least the sharp common waiting bound and t<2^d, the supported times of each prefix are exactly E(t)+PK with K a natural number and E(t)+PK<=D.

**Theorem 1.7 (Raw clock quotient).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall t: \left(\mathbb{N}\right), \left(\forall K: \left(\mathbb{N}\right), \left(\left(t < \left(2\right)^{d}\right) \implies \left(\operatorname{div}\left(\left(\operatorname{earliestTime}\left(d, t\right)\right) + \left(\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right) \cdot \left(K\right)\right), \left(2\right)^{\left(d\right) + \left(1\right)}\right) = \left(\operatorname{length}\left(\operatorname{bitIndices}\left(t\right)\right)\right) + \left(K\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_raw_clock_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t<2^d, floor((E(t)+PK)/P)=wt(t)+K. Thus raw clock parity is (wt(t)+K) mod 2. The delay tag K mod 2 alone is a different quantity.

**Theorem 1.8 (Singleton and double raw-parity support).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall D: \left(\mathbb{N}\right), \left(\forall t: \left(\mathbb{N}\right), \left(\forall nu: \left(\operatorname{Fin}\left(2\right)\right), \left(\left(\left(\operatorname{sharpWait}\left(\left(d\right) + \left(1\right)\right) \le D\right) \land \left(t < \left(2\right)^{d}\right)\right) \implies \left(\left(nu \in \operatorname{actualParitySupport}\left(d, b, D, t\right)\right) \iff \left(\left(\operatorname{val}\left(nu\right) = \operatorname{mod}\left(\operatorname{length}\left(\operatorname{bitIndices}\left(t\right)\right), 2\right)\right) \lor \left(\left(\operatorname{earliestTime}\left(d, t\right)\right) + \left(\left(2\right)^{\left(d\right) + \left(1\right)}\right) \le D\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_raw_parity_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If D>=sharpWait(d+1) and t<2^d, the actual support B_D(t) contains wt(t) mod 2. It contains both parities exactly when E(t)+P<=D. Its definition ranges over all realizing policies and their actual histories, rather than a fixed controller.

**Theorem 1.9 (Exact primitive type staircase).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall h: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(let D: \mathbb{N} := \left(\operatorname{sharpWait}\left(\left(d\right) + \left(1\right)\right)\right) + \left(h\right); \left(let q: \operatorname{Finset}\left(\mathbb{N}\right) := \operatorname{filter}\left(\operatorname{Icc}\left(1, \left(d\right) + \left(1\right)\right), \lambda i: \left(\mathbb{N}\right) \mapsto \left(\left(2\right)^{i} \le h\right)\right); \left(\left(\forall t: \left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right), \left(\operatorname{actualParitySupport}\left(d, b, D, \operatorname{val}\left(t\right)\right) = if t \in \operatorname{eligiblePrefixes}\left(d, D\right) then \operatorname{univ}\left(\operatorname{Fin}\left(2\right)\right) else \operatorname{singleton}\left(\langle\operatorname{mod}\left(\operatorname{length}\left(\operatorname{bitIndices}\left(\operatorname{val}\left(t\right)\right)\right), 2\right)\rangle:\operatorname{Fin}\left(2\right)\right)\right)\right) \land \left(\left(\operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}\left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right), \lambda t: \left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right) \mapsto \left(\operatorname{card}\left(\operatorname{actualParitySupport}\left(d, b, D, \operatorname{val}\left(t\right)\right)\right) = 1\right)\right)\right) = \left(\left(d\right) + \left(1\right)\right) - \left(\operatorname{card}\left(q\right)\right)\right) \land \left(\operatorname{card}\left(\operatorname{actualTypes}\left(d, b, D\right)\right) = \left(\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right) - \left(\left(d\right) + \left(1\right)\right)\right) + \left(\operatorname{card}\left(q\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_staircase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For D=sharpWait(d+1)+h, q counts 1<=i<=d+1 with 2^i<=h. There are L=d+1-q singleton prefixes and M=2^(d+1)-(d+1)+q actual types. Equivalently, n=2^d and M=2n-L. A singleton whose raw parity is one still contributes one type. This counts actual supported types; it does not determine the noisy hidden-schedule label minimum.

## References

- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_observation_normal_form`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_pair_realization`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_raw_parity_support`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_staircase`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_deadline_time_support`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_final_time_normal_form`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.actual_raw_clock_quotient`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.deadline_allowed_primitive_realization`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineSupport.execution_read_bounds`
- Dependency: [D5/S3/ConceptDynamics/Coding/ActualDyadicCausalPrefixRepairCapacity](../../ConceptDynamics/Coding/ActualDyadicCausalPrefixRepairCapacity.md)
- Dependency: [D5/S3/Observer/Budget/DyadicDeadlineStaircase](DyadicDeadlineStaircase.md)
