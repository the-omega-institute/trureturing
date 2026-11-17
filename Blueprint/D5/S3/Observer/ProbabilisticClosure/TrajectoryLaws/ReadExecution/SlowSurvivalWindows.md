# Ordered waiting windows from slow survival decay

## Abstract

Ordered waiting windows from slow survival decay

**Theorem 1.1 (Jointly ordered finite windows).**

$$\forall (S: \mathbb{N} \to \mathbb{R}), (\forall (j: \mathbb{N}), 0 < \operatorname{S}(j)) \Rightarrow (\operatorname{Tendsto}(S, atTop, \operatorname{nhds}(0))) \Rightarrow (\operatorname{Tendsto}(\lambda (j: \mathbb{N}) \mapsto (\frac{\operatorname{S}(j + 1)}{\operatorname{S}(j)}), atTop, \operatorname{nhds}(1))) \Rightarrow \forall (K: \mathbb{N}), \forall (theta: \mathbb{R}), (0 < theta) \Rightarrow \exists (H: \mathbb{N}), \exists (n: \operatorname{Fin}(K) \to \mathbb{N}), \exists (b: \operatorname{Fin}(K + 1) \to \mathbb{N}), (\operatorname{b}(0) = 0) \land ((\operatorname{b}(\operatorname{last}(K)) = H) \land (((K = 0) \iff (H = 0)) \land ((\operatorname{StrictMono}(b)) \land ((\operatorname{StrictMono}(n)) \land (\forall (i: \operatorname{Fin}(K)), (0 < \operatorname{n}(i)) \land ((\operatorname{b}(\operatorname{castSucc}(i)) < \operatorname{b}(\operatorname{succ}(i))) \land ((\operatorname{b}(\operatorname{succ}(i)) \le H) \land (1 - 2 \cdot theta < \frac{\operatorname{S}(\operatorname{n}(i) + \operatorname{b}(\operatorname{castSucc}(i))) - \operatorname{S}(\operatorname{n}(i) + \operatorname{b}(\operatorname{succ}(i)))}{\operatorname{S}(\operatorname{n}(i))}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/SlowSurvivalWindows.finite_waiting_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive real sequence S tending to zero whose successive ratios tend to one, every natural K and every positive real theta admit the displayed finite witnesses. The single strictly increasing boundary vector b encodes L(i)=b(i.castSucc), U(i)=b(i.succ) and H=b(last K). Thus the first lower endpoint is zero, successive windows meet exactly, and every upper endpoint is at most the same H. The selected positive ages n(i) are strictly increasing. When K is zero, the age family is empty, the boundary vector has its single zero entry and H is zero; otherwise H and every window length are positive.

At each fixed length L, the quotient S(n+L)/S(n) tends to one by multiplying the L successive ratios; the empty product is one. At fixed n, S(n+U)/S(n) tends to zero because S(n) is positive. A recursive witness construction first chooses an age larger than the previous age with early ratio greater than 1-theta, then an upper endpoint beyond the previous boundary with tail ratio less than theta. Subtracting these inequalities gives the strict bound 1-2*theta. No rate, uniform limit or monotonicity of S is used. Positivity of theta suffices, so the theorem also applies in the source range theta less than 1/16.

The conclusion concerns an arbitrary positive scalar sequence with the two stated limits. Applying it to a diffusion survival sequence requires proving those hypotheses for that diffusion; cylinder probabilities, stationary laws and full-history conditional distributions are additional data. The scalar inequalities alone do not assert a diffusion realization or a bound on a finite bank of predictive distributions.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/SlowSurvivalWindows.finite_waiting_windows`
