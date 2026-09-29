# Dyadic Prefix Completion Times

## Abstract

A dyadic sensor's successful causal controllers have exact prefix completion times, and one controller realizes every prescribed nonnegative period-delay table.

Fix d>=0, P=2^(d+1), and a known initial high bit b. A prefix t<P/2 has two sources 2t and 2t+1. The earliest midpoint controller finishes either source at E(t)=P-1+P wt(t)-2t, where wt(t) is the number of nonzero binary digits of t. Controllers receive only raw high-bit observations and their own elapsed clock.

**Theorem 1.1 (Delay-table execution on both final-bit siblings).**

$$\forall P: \mathbb{N}, \left(\forall K: \mathbb{N} \to \mathbb{N}, \left(\forall read: \mathbb{N} \to \mathbb{N} \to \operatorname{Fin}\left(2\right), \left(\left(\forall n: \mathbb{N}, \left(\forall r: \mathbb{N}, \left(\forall k: \mathbb{N}, \left(\left(r < P\right) \implies \left(\operatorname{read}\left(n + P \times k, r\right) = \operatorname{read}\left(n, r\right)\right)\right)\right)\right)\right) \implies \left(\left(\forall n: \mathbb{N}, \left(\forall r: \mathbb{N}, \left(\left(r < P\right) \implies \left(\operatorname{read}\left(n, r\right) = \operatorname{threshold}\left(P, n, r\right)\right)\right)\right)\right) \implies \left(\forall d: \mathbb{N}, \left(\forall a: \mathbb{N}, \left(\forall now: \mathbb{N}, \left(\forall r: \mathbb{N}, \left(\left(\left(\operatorname{mod}\left(a, 2\right) = 0\right) \land \left(\left(a + \operatorname{pow}\left(2, d + 1\right) \le P\right) \land \left(\left(a \le r\right) \land \left(r < a + \operatorname{pow}\left(2, d + 1\right)\right)\right)\right)\right) \implies \left(\left(\operatorname{fst}\left(\operatorname{execute}\left(read, \operatorname{delayedMidpoint}\left(P, K, d + 1, a, now\right), now, r\right)\right) = \operatorname{fst}\left(\operatorname{execute}\left(read, DyadicForwardWaitingOptimality.midpoint\left(P, d + 1, a, now\right), now, r\right)\right)\right) \land \left(\operatorname{snd}\left(\operatorname{execute}\left(read, \operatorname{delayedMidpoint}\left(P, K, d + 1, a, now\right), now, r\right)\right) = \operatorname{snd}\left(\operatorname{execute}\left(read, DyadicForwardWaitingOptimality.midpoint\left(P, d + 1, a, now\right), now, r\right)\right) + P \times \operatorname{K}\left(\operatorname{div}\left(r, 2\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/DyadicPrefixDelayRange.delayed_midpoint_execute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any P, delay table K, and readout agreeing with the threshold below P and invariant under addition of P periods, the recursively delayed midpoint tree returns the same answer as the earliest tree. Its actual last-read time adds exactly P K(floor(r/2)). The source interval has even start a, length 2^(d+1), and lies below P; r ranges over that whole interval, with arbitrary initial time now.

**Theorem 1.2 (One causal controller realizes an entire delay table).**

$$\forall d: \mathbb{N}, \left(\forall b: \operatorname{Fin}\left(2\right), \left(\forall K: \mathbb{N} \to \mathbb{N}, \left(\exists p: \operatorname{Protocol}\left(d + 1\right), \left(\left(\operatorname{CorrectOn}\left(\operatorname{rawBit}\left(\operatorname{pow}\left(2, d + 1\right), b\right), p, 0, 0, \operatorname{pow}\left(2, d + 1\right)\right)\right) \land \left(\forall t: \mathbb{N}, \left(\forall u: \mathbb{N}, \left(\left(\left(t < \operatorname{pow}\left(2, d\right)\right) \land \left(u < 2\right)\right) \implies \left(\operatorname{terminalTime}\left(\operatorname{pow}\left(2, d + 1\right), b, p, 2 \times t + u\right) = \operatorname{earliestTime}\left(d, t\right) + \operatorname{pow}\left(2, d + 1\right) \times \operatorname{K}\left(t\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/DyadicPrefixDelayRange.arbitrary_prefix_delay_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The midpoint questions before the final query distinguish the prefix t. At that query the controller adds P K(t) to its waiting increment. The added interval leaves the threshold unchanged, and raw-bit transport preserves both the answer and the completion time. Thus the same tree succeeds on every source and realizes every entry of K simultaneously.

**Theorem 1.3 (Every successful controller has a nonnegative period correction).**

$$\forall d: \mathbb{N}, \left(\forall b: \operatorname{Fin}\left(2\right), \left(\forall p: \operatorname{Protocol}\left(d + 1\right), \left(\left(\operatorname{CorrectOn}\left(\operatorname{rawBit}\left(\operatorname{pow}\left(2, d + 1\right), b\right), p, 0, 0, \operatorname{pow}\left(2, d + 1\right)\right)\right) \implies \left(\forall t: \mathbb{N}, \left(\forall u: \mathbb{N}, \left(\left(\left(t < \operatorname{pow}\left(2, d\right)\right) \land \left(u < 2\right)\right) \implies \left(\exists k: \mathbb{N}, \left(\operatorname{terminalTime}\left(\operatorname{pow}\left(2, d + 1\right), b, p, 2 \times t + u\right) = \operatorname{earliestTime}\left(d, t\right) + \operatorname{pow}\left(2, d + 1\right) \times k\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/DyadicPrefixDelayRange.arbitrary_protocol_prefix_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Binary capacity forces each query to cut its current interval at the midpoint. The first forward occurrence of that phase is no later than any successful controller's corresponding query. Induction along every source path gives the earliest-time lower bound; the terminal sibling phase then makes the nonnegative difference an integer multiple of P. Both possible last source bits are included.

For deadline D, F_D is the family of actual successful depth-(d+1) raw-bit protocols whose last read is at most D on every source r<P. Write W=sharpWait(d+1), E(t)=P-1+P wt(t)-2t, N_p(r) for the actual last-read time, and Y_p(r) for the raw final bit. The family range result below proves no controller exists below W. For D>=W it characterizes each reachable prefix time and gives an operational same-raw-bit collision when E(t)+P<=D. It does not assert the full minimum clock alphabet.

**Theorem 1.4 (Exact deadline times and a cross-controller collision).**

$$\forall d: \mathbb{N}, \left(\forall b: \operatorname{Fin}\left(2\right), \left(\forall D: \mathbb{N}, \left(\left(\left(D < \operatorname{sharpWait}\left(d + 1\right)\right) \implies \left(\neg\exists p: \operatorname{Protocol}\left(d + 1\right), \left(\operatorname{deadlineFamily}\left(d, b, D, p\right)\right)\right)\right) \land \left(\left(\left(\operatorname{sharpWait}\left(d + 1\right) \le D\right) \implies \left(\forall t: \mathbb{N}, \left(\forall u: \mathbb{N}, \left(\forall k: \mathbb{N}, \left(\left(\left(t < \operatorname{pow}\left(2, d\right)\right) \land \left(u < 2\right)\right) \implies \left(\left(\exists p: \operatorname{Protocol}\left(d + 1\right), \left(\left(\operatorname{deadlineFamily}\left(d, b, D, p\right)\right) \land \left(\operatorname{terminalTime}\left(\operatorname{pow}\left(2, d + 1\right), b, p, 2 \times t + u\right) = \operatorname{earliestTime}\left(d, t\right) + \operatorname{pow}\left(2, d + 1\right) \times k\right)\right)\right) \iff \left(\operatorname{earliestTime}\left(d, t\right) + \operatorname{pow}\left(2, d + 1\right) \times k \le D\right)\right)\right)\right)\right)\right)\right) \land \left(\forall t: \mathbb{N}, \left(\left(\left(t < \operatorname{pow}\left(2, d\right)\right) \land \left(\left(\operatorname{sharpWait}\left(d + 1\right) \le D\right) \land \left(\operatorname{earliestTime}\left(d, t\right) + \operatorname{pow}\left(2, d + 1\right) \le D\right)\right)\right) \implies \left(\exists p0: \operatorname{Protocol}\left(d + 1\right), \left(\exists p1: \operatorname{Protocol}\left(d + 1\right), \left(\left(\operatorname{deadlineFamily}\left(d, b, D, p0\right)\right) \land \left(\left(\operatorname{deadlineFamily}\left(d, b, D, p1\right)\right) \land \left(\left(\operatorname{terminalTime}\left(\operatorname{pow}\left(2, d + 1\right), b, p1, 2 \times t + 1\right) = \operatorname{terminalTime}\left(\operatorname{pow}\left(2, d + 1\right), b, p0, 2 \times t\right) + \operatorname{pow}\left(2, d + 1\right)\right) \land \left(\left(\operatorname{terminalRecord}\left(\operatorname{pow}\left(2, d + 1\right), b, p0, 2 \times t\right)\right).2 = \left(\operatorname{terminalRecord}\left(\operatorname{pow}\left(2, d + 1\right), b, p1, 2 \times t + 1\right)\right).2\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/DyadicPrefixDelayRange.deadline_prefix_time_range_and_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A one-prefix delay table reaches each permitted time while the earliest tree keeps every other source within W. A controller below W contradicts the sharp waiting lower bound. For an eligible prefix, the zero-delay even source and one-period-delayed odd source have the same actual raw final read, although their source residues differ and their terminal times differ by P.

**Theorem 1.5 (One decoder for every deadline-family controller).**

$$\forall d: \mathbb{N}, \left(\forall b: \operatorname{Fin}\left(2\right), \left(\forall D: \mathbb{N}, \left(\left(\left(D < \operatorname{sharpWait}\left(d + 1\right)\right) \implies \left(\neg\exists p: \operatorname{Protocol}\left(d + 1\right), \left(\operatorname{deadlineFamily}\left(d, b, D, p\right)\right)\right)\right) \land \left(\left(\operatorname{sharpWait}\left(d + 1\right) \le D\right) \implies \left(\left(\forall Z: Type, \left(\forall phi: \mathbb{N} \to Z, \left(\forall recover: Z \to \operatorname{Fin}\left(2\right) \to \mathbb{N}, \left(\left(\forall p: \operatorname{Protocol}\left(d + 1\right), \left(\left(\operatorname{deadlineFamily}\left(d, b, D, p\right)\right) \implies \left(\forall r: \mathbb{N}, \left(\left(r < \operatorname{pow}\left(2, d + 1\right)\right) \implies \left(recover\left(phi\left(\operatorname{terminalTime}\left(\operatorname{pow}\left(2, d + 1\right), b, p, r\right)\right)\right)\left(\left(\operatorname{terminalRecord}\left(\operatorname{pow}\left(2, d + 1\right), b, p, r\right)\right).2\right) = r\right)\right)\right)\right)\right) \implies \left(\operatorname{pow}\left(2, d\right) + \operatorname{card}\left(\operatorname{eligiblePrefixes}\left(d, D\right)\right) \le \operatorname{card}\left(\operatorname{familyClockLabels}\left(d, b, D, phi\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall p: \operatorname{Protocol}\left(d + 1\right), \left(\left(\operatorname{deadlineFamily}\left(d, b, D, p\right)\right) \implies \left(\forall r: \mathbb{N}, \left(\left(r < \operatorname{pow}\left(2, d + 1\right)\right) \implies \left(\operatorname{tagDecode}\left(d, b\right)\left(\operatorname{clockTag}\left(d\right)\left(\operatorname{terminalTime}\left(\operatorname{pow}\left(2, d + 1\right), b, p, r\right)\right)\right)\left(\left(\operatorname{terminalRecord}\left(\operatorname{pow}\left(2, d + 1\right), b, p, r\right)\right).2\right) = r\right)\right)\right)\right)\right) \land \left(\operatorname{card}\left(\operatorname{familyClockLabels}\left(d, b, D, \operatorname{clockTag}\left(d\right)\right)\right) = \operatorname{pow}\left(2, d\right) + \operatorname{card}\left(\operatorname{eligiblePrefixes}\left(d, D\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/DyadicPrefixDelayRange.deadline_family_operational_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Labels are counted only when attained at a terminal time of a successful controller in the common-deadline family. For D below the sharp wait the family is empty. Otherwise any time-only encoder admitting one decoder for every controller and source uses at least 2^d plus the number of prefixes whose earliest time plus one period meets D. The explicit time tag records the prefix and delay parity, and one decoder combines it with the original uncorrected raw final bit. Its actual label image has exactly that cardinality. This proves the deadline-family operational part of source section 9.2; the closed-form slack staircase remains separate.

## References

- Truth anchor: `D5/S3/Observer/Budget/DyadicPrefixDelayRange.arbitrary_prefix_delay_table`
- Truth anchor: `D5/S3/Observer/Budget/DyadicPrefixDelayRange.arbitrary_protocol_prefix_time`
- Truth anchor: `D5/S3/Observer/Budget/DyadicPrefixDelayRange.deadline_family_operational_capacity`
- Truth anchor: `D5/S3/Observer/Budget/DyadicPrefixDelayRange.deadline_prefix_time_range_and_collision`
- Truth anchor: `D5/S3/Observer/Budget/DyadicPrefixDelayRange.delayed_midpoint_execute`
- Dependency: [D5/S3/Observer/Budget/TerminalClockCompression](TerminalClockCompression.md)
