# Actual Dyadic Deadline Repair Minimum

## Abstract

The original causal deadline repair contract has the exact mixed-demand cyclic capacity.

In the formulas, div denotes natural-number division, real is the real coercion, and record(N,past) has event count N and read history past. The displayed writer and decoder condition expands CommonRepairFeasible. In support ranking, equivFin bijects each finite parity support with the ranks below its cardinality.

Let P=2^(d+1), n=2^d, and b be a known bit. A primitive policy chooses only forward events, noiseless nondisturbing reads, and stops from its acquired record. The deadline family includes every deterministic policy successful on every source in at most d+1 reads with literal final query N<=D. Reporting delay is unrestricted. A supported type (t,nu) retains the actual raw parity nu=floor(N/P) mod 2 and the phase center P-1-2t.

**Definition 1.1 (Actual support demand).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall D: \left(\mathbb{N}\right), \left(\forall t: \left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right), \left(\operatorname{actualDemand}\left(d, b, D, t\right) = \operatorname{card}\left(\operatorname{actualParitySupport}\left(d, b, D, \operatorname{val}\left(t\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.actualDemand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The demand at t is the cardinality of its actual raw-parity support. For D>=sharpWait(d+1) and t<n this is one or two.

**Definition 1.2 (Lossless support ranking).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall D: \left(\mathbb{N}\right), \left(\left(\operatorname{supportedTypeRankEquiv}\left(d, b, D\right): \operatorname{Equiv}\left(\{x: \left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right) \times \left(\operatorname{Fin}\left(2\right)\right) \mid x \in \operatorname{actualTypes}\left(d, b, D\right)\}, \operatorname{Vertex}\left(\operatorname{actualDemand}\left(d, b, D\right)\right)\right)\right) \land \left(\left(\forall x: \left(\{x: \left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right) \times \left(\operatorname{Fin}\left(2\right)\right) \mid x \in \operatorname{actualTypes}\left(d, b, D\right)\}\right), \left(\operatorname{apply}\left(\operatorname{supportedTypeRankEquiv}\left(d, b, D\right), x\right) = \left(\operatorname{fst}\left(\operatorname{val}\left(x\right)\right), \operatorname{apply}\left(\operatorname{equivFin}\left(\operatorname{actualParitySupport}\left(d, b, D, \operatorname{val}\left(\operatorname{fst}\left(\operatorname{val}\left(x\right)\right)\right)\right)\right), \langle\operatorname{snd}\left(\operatorname{val}\left(x\right)\right)\rangle:\{nu: \operatorname{Fin}\left(2\right) \mid nu \in \operatorname{actualParitySupport}\left(d, b, D, \operatorname{val}\left(\operatorname{fst}\left(\operatorname{val}\left(x\right)\right)\right)\right)\}\right)\right)\right)\right) \land \left(\left(\forall v: \left(\operatorname{Vertex}\left(\operatorname{actualDemand}\left(d, b, D\right)\right)\right), \left(\operatorname{apply}\left(\operatorname{symm}\left(\operatorname{supportedTypeRankEquiv}\left(d, b, D\right)\right), v\right) = \langle\left(\operatorname{fst}\left(v\right), \operatorname{val}\left(\operatorname{apply}\left(\operatorname{symm}\left(\operatorname{equivFin}\left(\operatorname{actualParitySupport}\left(d, b, D, \operatorname{val}\left(\operatorname{fst}\left(v\right)\right)\right)\right)\right), \operatorname{snd}\left(v\right)\right)\right)\right)\rangle:\{x: \left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right) \times \left(\operatorname{Fin}\left(2\right)\right) \mid x \in \operatorname{actualTypes}\left(d, b, D\right)\}\right)\right) \land \left(\left(\forall x: \left(\{x: \left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right) \times \left(\operatorname{Fin}\left(2\right)\right) \mid x \in \operatorname{actualTypes}\left(d, b, D\right)\}\right), \left(\operatorname{apply}\left(\operatorname{symm}\left(\operatorname{supportedTypeRankEquiv}\left(d, b, D\right)\right), \operatorname{apply}\left(\operatorname{supportedTypeRankEquiv}\left(d, b, D\right), x\right)\right) = x\right)\right) \land \left(\forall v: \left(\operatorname{Vertex}\left(\operatorname{actualDemand}\left(d, b, D\right)\right)\right), \left(\operatorname{apply}\left(\operatorname{supportedTypeRankEquiv}\left(d, b, D\right), \operatorname{apply}\left(\operatorname{symm}\left(\operatorname{supportedTypeRankEquiv}\left(d, b, D\right)\right), v\right)\right) = v\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.supportedTypeRankEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is a prefix-preserving equivalence between actual supported raw types and demand-ranked types. Each finite raw-parity support is bijected with the ranks below its cardinality. Both inverse laws hold. A singleton has rank zero even when its sole raw parity is one. Double support has two ranks; unranking recovers the actual raw parity.

**Theorem 1.3 (Exact closed error shell).**

$$\forall d: \left(\mathbb{N}\right), \left(\forall _: \operatorname{Fin}\left(2\right), \left(\forall D: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall eps: \left(\mathbb{R}\right), \left(\forall i: \left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right), \left(\forall j: \left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right), \left(\left(\left(\operatorname{sharpWait}\left(\left(d\right) + \left(1\right)\right) \le D\right) \land \left(\left(2 \le m\right) \land \left(\left(\left(\operatorname{real}\left(m\right)\right) - \left(1\right) \le eps\right) \land \left(eps < \operatorname{real}\left(m\right)\right)\right)\right)\right) \implies \left(\left(\exists phase: \left(\operatorname{AddCircle}\left(\operatorname{real}\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right)\right)\right), \left(\left(\operatorname{dist}\left(phase, \operatorname{prefixPhase}\left(d, i\right)\right) \le eps\right) \land \left(\operatorname{dist}\left(phase, \operatorname{prefixPhase}\left(d, j\right)\right) \le eps\right)\right)\right) \iff \left(\operatorname{Near}\left(m, i, j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.actual_phase_overlap_near` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume D>=sharpWait(d+1), m>=2, and m-1<=eps<m. Two prefix phase balls intersect exactly when the circular integer distance of their prefixes is less than m. A realized all-source schedule supplies the phase-distance scaling by two. Closed-ball intersection includes equality at eps=m-1. The circular seam and equal prefixes are included.

**Theorem 1.4 (Both coloring transports).**

$$\forall Z: \left(Type\right), \left(\forall d: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall D: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall eps: \left(\mathbb{R}\right), \left(\left(\left(\operatorname{sharpWait}\left(\left(d\right) + \left(1\right)\right) \le D\right) \land \left(\left(2 \le m\right) \land \left(\left(\left(\operatorname{real}\left(m\right)\right) - \left(1\right) \le eps\right) \land \left(eps < \operatorname{real}\left(m\right)\right)\right)\right)\right) \implies \left(\left(\exists color: \left(\left(\left(\operatorname{Fin}\left(\left(2\right)^{d}\right)\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right) \to \left(Z\right)\right), \left(\operatorname{ActualTypeColoring}\left(d, b, D, eps, color\right)\right)\right) \iff \left(\exists color: \left(\left(\operatorname{Vertex}\left(\operatorname{actualDemand}\left(d, b, D\right)\right)\right) \to \left(Z\right)\right), \left(\operatorname{Proper}\left(m, \operatorname{actualDemand}\left(d, b, D\right), color\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.actual_supported_coloring_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same deadline and error-shell assumptions, for any label type Z the actual supported types admit a proper Z-coloring exactly when the ranked mixed-demand cyclic graph does. The equivalence preserves prefixes and distinct supported raw types in both directions. Unsupported pairs are given an existing supported color when extending to a total function. Different raw parities at the same prefix remain distinct adjacent types.

**Theorem 1.5 (Original prefix-window size).**

$$\forall j: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\left(\left(2 \le j\right) \land \left(\left(2 \le m\right) \land \left(\left(3\right) + \left(\operatorname{log2}\left(m\right)\right) \le j\right)\right)\right) \implies \left(\left(2\right) \cdot \left(m\right) < \left(2\right)^{\left(j\right) - \left(1\right)}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.original_window_size` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j>=2 and m>=2, the original logarithmic size condition 3+floor(log2(m))<=j implies 2m<2^(j-1).

**Theorem 1.6 (Exact original shared-decoder minimum).**

$$\forall j: \left(\mathbb{N}\right), \left(\forall h: \left(\mathbb{N}\right), \left(\forall m: \left(\mathbb{N}\right), \left(\forall a: \left(\mathbb{N}\right), \left(\forall rho: \left(\mathbb{N}\right), \left(\forall b: \left(\operatorname{Fin}\left(2\right)\right), \left(\forall eps: \left(\mathbb{R}\right), \left(\left(\left(2 \le j\right) \land \left(\left(2 \le m\right) \land \left(\left(\left(\operatorname{real}\left(m\right)\right) - \left(1\right) \le eps\right) \land \left(\left(eps < \operatorname{real}\left(m\right)\right) \land \left(\left(\left(3\right) + \left(\operatorname{log2}\left(m\right)\right) \le j\right) \land \left(\left(\left(2\right)^{\left(j\right) - \left(1\right)} = \left(\left(m\right) \cdot \left(a\right)\right) + \left(rho\right)\right) \land \left(\left(rho < m\right) \land \left(\left(2\right) \cdot \left(rho\right) \le a\right)\right)\right)\right)\right)\right)\right)\right) \implies \left(let d: \mathbb{N} := \left(j\right) - \left(1\right); \left(let n: \mathbb{N} := \left(2\right)^{d}; \left(let D: \mathbb{N} := \left(\left(\left(\left(j\right) - \left(1\right)\right) \cdot \left(\left(2\right)^{j}\right)\right) + \left(1\right)\right) + \left(h\right); \left(let q: \mathbb{N} := \operatorname{card}\left(\{i: \mathbb{N} \mid \left(1 \le i\right) \land \left(\left(i \le j\right) \land \left(\left(2\right)^{i} \le h\right)\right)\}\right); \left(let L: \mathbb{N} := \left(j\right) - \left(q\right); \left(let capacity: \mathbb{N} := \operatorname{max}\left(\left(2\right) \cdot \left(m\right), \operatorname{div}\left(\left(\left(\left(\left(2\right) \cdot \left(n\right)\right) - \left(L\right)\right) + \left(a\right)\right) - \left(1\right), a\right)\right); \left(\left(\operatorname{IsLeast}\left(\{c: \mathbb{N} \mid \exists writer: \left(\left(\left(Record\right) \to \left(\operatorname{Action}\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right)\right)\right) \to \left(\left(Record\right) \to \left(\operatorname{Fin}\left(c\right)\right)\right)\right), \left(\exists decoder: \left(\left(\operatorname{AddCircle}\left(\operatorname{real}\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right)\right)\right) \to \left(\left(\operatorname{Fin}\left(2\right)\right) \to \left(\left(\operatorname{Fin}\left(c\right)\right) \to \left(\mathbb{N}\right)\right)\right)\right), \left(\forall policy: \left(\left(Record\right) \to \left(\operatorname{Action}\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right)\right)\right), \left(\left(\operatorname{actualDeadlineFamily}\left(d, b, D, policy\right)\right) \implies \left(\forall r: \left(\operatorname{Fin}\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right)\right), \left(\forall past: \left(\operatorname{List}\left(\left(\mathbb{N}\right) \times \left(\operatorname{Fin}\left(2\right)\right)\right)\right), \left(\forall N: \left(\mathbb{N}\right), \left(\forall bit: \left(\operatorname{Fin}\left(2\right)\right), \left(\left(\operatorname{DeadlineObservation}\left(d, b, D, policy, r, past, N, bit\right)\right) \implies \left(\forall phase: \left(\operatorname{AddCircle}\left(\operatorname{real}\left(\left(2\right)^{\left(d\right) + \left(1\right)}\right)\right)\right), \left(\left(\operatorname{dist}\left(phase, \operatorname{terminalPhase}\left(r\right)\right) \le eps\right) \implies \left(\operatorname{decoder}\left(phase, bit, \operatorname{writer}\left(policy, \operatorname{record}\left(N, past\right)\right)\right) = \operatorname{val}\left(r\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\}, capacity\right)\right) \land \left(capacity = \left(\left(2\right) \cdot \left(m\right)\right) + \left(if L < \left(2\right) \cdot \left(rho\right) then 1 else 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.original_operational_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j>=2, h>=0, known b, P=2^j, n=2^(j-1), and D=(j-1)P+1+h, assume m>=2, m-1<=eps<m, j>=3+floor(log2(m)), n=ma+rho, rho<m, and a>=2rho. Put q=#{1<=i<=j:2^i<=h} and L=j-q. The least alphabet cardinality is max(2m,ceil((2n-L)/a))=2m+indicator(L<2rho). The logarithmic hypothesis supplies n>2m and a consecutive m-prefix window with double demand; these are consequences, not extra premises. Feasibility means a writer receiving only policy and actual pre-final record and one common receiver recovering every source for every deadline-family policy and every closed phase error. The label precedes the final read and future error. The receiver sees only phase, exact raw Y, label, and fixed public parameters; policy, N, and past reads are hidden. All-history label separation and the two coloring transports give both attainment and the universal lower bound.

## References

- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.actualDemand`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.actual_phase_overlap_near`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.actual_supported_coloring_iff`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.original_operational_minimum`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.original_window_size`
- Truth anchor: `D5/S3/Observer/Budget/ActualDyadicDeadlineRepairMinimum.supportedTypeRankEquiv`
- Dependency: [D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring](../../Combinatorics/Graph/CyclicMixedDemandColoring.md)
- Dependency: [D5/S3/Observer/Budget/ActualDyadicDeadlineLabelSupport](ActualDyadicDeadlineLabelSupport.md)
