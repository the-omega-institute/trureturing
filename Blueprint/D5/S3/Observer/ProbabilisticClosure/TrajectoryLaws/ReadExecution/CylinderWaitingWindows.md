# Full-word waiting windows from primitive cylinder data

## Abstract

Full-word waiting windows from primitive cylinder data

**Definition 1.1 (survivalFutures).**

$$\forall (H: \mathbb{N}), \forall (j: \mathbb{N}), \operatorname{survivalFutures}(H, j) = \operatorname{filter}(\lambda (v: \operatorname{Fin}(H) \to \operatorname{Fin}(4)) \mapsto (\forall (k: \operatorname{Fin}(H)), (\operatorname{val}(k) < j) \Rightarrow \operatorname{v}(k) \neq 3), univ)$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.survivalFutures` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural horizon H and length j, retain the full four-label future words v for which every coordinate k with k.val less than j has v(k) different from the marker 3. At j zero every future word is retained, including the unique empty word when H is zero. If j exceeds H, the condition examines every available coordinate, so the set equals survivalFutures(H,H).

**Definition 1.2 (waitingFutures).**

$$\forall (H: \mathbb{N}), \forall (L: \mathbb{N}), \forall (U: \mathbb{N}), \operatorname{waitingFutures}(H, L, U) = \operatorname{sdiff}(\operatorname{survivalFutures}(H, L), \operatorname{survivalFutures}(H, U))$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.waitingFutures` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set difference survivalFutures(H,L) minus survivalFutures(H,U) is the event that the first marker lies strictly after L and at or before U. This first-marker interpretation uses L less than U and U at most H, as in the theorem. The definition also includes arbitrary natural endpoints: the set is empty if U is at most L or H is zero, and endpoints beyond H retain their stated coordinate conditions.

**Definition 1.3 (noMarkerWord).**

$$\forall (n: \mathbb{N}), \forall (w: \operatorname{Fin}(n) \to \operatorname{Fin}(3)), \operatorname{noMarkerWord}(w) = \operatorname{ofFn}(\lambda (i: \operatorname{Fin}(n)) \mapsto (\operatorname{castSucc}(\operatorname{w}(i))))$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.noMarkerWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complete length-n word over the three nonmarker labels is embedded coordinate by coordinate by Fin.castSucc into Fin 4 and converted to a list. Label B is 2 and the marker is 3.

**Definition 1.4 (prefixed).**

$$\forall (m: \mathbb{N}), \forall (w: \operatorname{List}(\operatorname{Fin}(4))), \operatorname{prefixed}(m, w) = \operatorname{append}(\operatorname{replicate}(m, 2), w)$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.prefixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Append the complete word w to m copies of B. The copies remain part of the actual full history.

**Theorem 1.5 (finite_full_word_common_cut).**

$$\forall (S: \mathbb{N} \to \mathbb{R}), (\forall (m: \mathbb{N}), 0 < \operatorname{S}(m)) \Rightarrow (\operatorname{Tendsto}(S, atTop, \operatorname{nhds}(0))) \Rightarrow (\operatorname{Tendsto}(\lambda (m: \mathbb{N}) \mapsto (\frac{\operatorname{S}(m + 1)}{\operatorname{S}(m)}), atTop, \operatorname{nhds}(1))) \Rightarrow \forall (p: \operatorname{List}(\operatorname{Fin}(4)) \to \mathbb{R}), \forall (q: \operatorname{List}(\operatorname{Fin}(4)) \to \mathbb{R}), (\forall (z: \operatorname{List}(\operatorname{Fin}(4))), 0 \le \operatorname{p}(z)) \Rightarrow (\forall (z: \operatorname{List}(\operatorname{Fin}(4))), \forall (H: \mathbb{N}), \sum_{v: \operatorname{Fin}(H) \to \operatorname{Fin}(4)} (\operatorname{p}(\operatorname{append}(z, \operatorname{ofFn}(v)))) = \operatorname{p}(z)) \Rightarrow (\forall (r: \mathbb{N}), \forall (z: \operatorname{Fin}(r) \to \operatorname{Fin}(3)), 0 < \operatorname{q}(\operatorname{noMarkerWord}(z))) \Rightarrow (\forall (r: \mathbb{N}), \sum_{z: \operatorname{Fin}(r) \to \operatorname{Fin}(3)} (\operatorname{q}(\operatorname{noMarkerWord}(z))) = \operatorname{S}(r)) \Rightarrow (\forall (r: \mathbb{N}), \forall (H: \mathbb{N}), \forall (j: \mathbb{N}), (j \le H) \Rightarrow \sum_{z: \operatorname{Fin}(r) \to \operatorname{Fin}(3)} (\sum_{v \in \operatorname{survivalFutures}(H, j)} (\operatorname{q}(\operatorname{append}(\operatorname{noMarkerWord}(z), \operatorname{ofFn}(v))))) = \operatorname{S}(r + j)) \Rightarrow (\forall (z: \operatorname{List}(\operatorname{Fin}(4))), \operatorname{Tendsto}(\lambda (m: \mathbb{N}) \mapsto (4^{m} \cdot \operatorname{p}(\operatorname{prefixed}(m, z))), atTop, \operatorname{nhds}(\operatorname{q}(z)))) \Rightarrow \forall (K: \mathbb{N}), \forall (theta: \mathbb{R}), ((0 < theta) \land (theta < \frac{1}{16})) \Rightarrow \exists (H: \mathbb{N}), \exists (t: \mathbb{N}), \exists (n: \operatorname{Fin}(K) \to \mathbb{N}), \exists (b: \operatorname{Fin}(K + 1) \to \mathbb{N}), \exists (w: \forall (i: \operatorname{Fin}(K)), \operatorname{Fin}(\operatorname{n}(i)) \to \operatorname{Fin}(3)), (\operatorname{b}(0) = 0) \land ((\operatorname{b}(\operatorname{last}(K)) = H) \land (((K = 0) \iff (H = 0)) \land ((\operatorname{StrictMono}(b)) \land ((\operatorname{StrictMono}(n)) \land ((0 < t) \land ((\forall (i: \operatorname{Fin}(K)), (0 < \operatorname{n}(i)) \land ((\operatorname{n}(i) \le t) \land ((\operatorname{b}(\operatorname{castSucc}(i)) < \operatorname{b}(\operatorname{succ}(i))) \land ((\operatorname{b}(\operatorname{succ}(i)) \le H) \land ((\operatorname{length}(\operatorname{prefixed}(t - \operatorname{n}(i), \operatorname{noMarkerWord}(\operatorname{w}(i)))) = t) \land ((1 - 2 \cdot theta < \frac{\sum_{v \in \operatorname{waitingFutures}(H, \operatorname{b}(\operatorname{castSucc}(i)), \operatorname{b}(\operatorname{succ}(i)))} (\operatorname{q}(\operatorname{append}(\operatorname{noMarkerWord}(\operatorname{w}(i)), \operatorname{ofFn}(v))))}{\operatorname{q}(\operatorname{noMarkerWord}(\operatorname{w}(i)))}) \land ((0 < \operatorname{p}(\operatorname{prefixed}(t - \operatorname{n}(i), \operatorname{noMarkerWord}(\operatorname{w}(i))))) \land (1 - 3 \cdot theta < \frac{\sum_{v \in \operatorname{waitingFutures}(H, \operatorname{b}(\operatorname{castSucc}(i)), \operatorname{b}(\operatorname{succ}(i)))} (\operatorname{p}(\operatorname{append}(\operatorname{prefixed}(t - \operatorname{n}(i), \operatorname{noMarkerWord}(\operatorname{w}(i))), \operatorname{ofFn}(v))))}{\operatorname{p}(\operatorname{prefixed}(t - \operatorname{n}(i), \operatorname{noMarkerWord}(\operatorname{w}(i))))})))))))) \land (\operatorname{Injective}(\lambda (i: \operatorname{Fin}(K)) \mapsto (\operatorname{prefixed}(t - \operatorname{n}(i), \operatorname{noMarkerWord}(\operatorname{w}(i))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.finite_full_word_common_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The data are real functions p and q on all finite four-label words. The masses p are nonnegative, may vanish on unselected histories, and satisfy every finite continuation partition, including horizon zero. Each comparison nonmarker word has positive q mass, including the empty word. The nonmarker-word sum equals S(n), and the joint nonmarker-past/no-marker-future cylinder sum equals S(n+j) whenever j is at most H. For every full word z, the raw rescaled masses 4^m*p(B^m z) converge to q(z). These are primitive cylinder assumptions, not conditional-row convergence or a packing premise. The conclusion constructs positive ordered ages, adjacent windows at one horizon, complete selected nonmarker words and distinct positive original histories B^(t-n(i))*w(i) of the same positive length t. For each selected word, the comparison event sum divided by its positive q mass exceeds 1-2*theta. For each selected full history, the continuation event sum divided by its positive p mass exceeds 1-3*theta. Every natural K and every real theta strictly between zero and 1/16 are allowed. When K is zero, H is zero, t is positive, the age and word families are empty, and the boundary vector has its single zero entry; strict monotonicity and injectivity then have their usual vacuous meaning. When K is positive, H and every window length are positive. No positive lower bound is assumed for p on all words.

Apply finite_waiting_windows to obtain the scalar windows. Taking differences of the two primitive no-marker-future sums gives the scalar window mass. Finset.exists_lt_of_sum_lt selects one complete nonmarker word for each window; an event-conditioned mixture is never substituted for that word. Finite summation of the raw prefix limits and division by the positive limiting word mass derive the conditional event limits. Intersecting the finitely many eventual conditions supplies one cut for the finitely many selected words, with t at least every selected age. Nonnegative continuation partitions normalize each actual row; two disjoint window masses greater than one half rule out coincident histories. This uses event masses directly and asserts no additional uniform-in-horizon convergence rate or TV modulus.

The conclusion holds under the displayed scalar and cylinder hypotheses. An application to an infinite diffusion requires identifying its entire word laws with p and q, proving the survival hypotheses, the stationary cylinder identities and the raw B-prefix limits on the full diffusion domain. The abstract construction alone does not establish those diffusion identities, a convex-bank obstruction or marked acquisition certificates.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.finite_full_word_common_cut`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.noMarkerWord`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.prefixed`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.survivalFutures`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CylinderWaitingWindows.waitingFutures`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/SlowSurvivalWindows](SlowSurvivalWindows.md)
