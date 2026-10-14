# Nested bilateral languages and the original upper limit

## Abstract

Compact decreasing bilateral languages stabilize at every fixed word length; their pressures and weighted zeros converge to those of the actual intersection.

Configurations are functions from the integers to the two letters u and c, with literal weights six and twenty. Occurs is the original occurrence relation at an arbitrary integer position. The pressure and weighted factor rate are those of the actual occurring words. For the memory instance, the windows are indexed from the most recent past letter, while memoryValue evaluates the reversed chronological word; the current Kth-c guard uses the prestate before the current letter. The upper guard retains equality.

**Definition 1.1 (anchoredCylinder).**

$$\forall w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{anchoredCylinder}\left(w\right) = \operatorname{setOf}\left((omega : Int \to CuLetter \mapsto \forall k \in \operatorname{Fin}\left(\operatorname{length}\left(w\right)\right),\; \operatorname{apply}\left(omega, \operatorname{toInt}\left(\operatorname{val}\left(k\right)\right)\right) = \operatorname{getElem}\left(w, \operatorname{val}\left(k\right)\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.anchoredCylinder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cylinder fixes every letter of w at coordinates zero through length w minus one. The empty word gives the entire configuration space.

**Theorem 1.2 (persistent word intersection).**

$$\forall Y \in Nat \to \operatorname{Set}\left(Int \to CuLetter\right),\; \left(\left(\forall j \in Nat,\; \operatorname{IsCompact}\left(\operatorname{apply}\left(Y, j\right)\right)\right) \land \left(\operatorname{Antitone}\left(Y\right) \land \left(\forall j \in Nat,\; \forall omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{apply}\left(Y, j\right)\right) \Rightarrow \left(\forall a \in Int,\; \operatorname{member}\left((i : Int \mapsto \operatorname{apply}\left(omega, \operatorname{add}\left(i, a\right)\right)), \operatorname{apply}\left(Y, j\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall w \in \operatorname{List}\left(CuLetter\right),\; \left(\forall j \in Nat,\; \exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{apply}\left(Y, j\right)\right) \land \operatorname{Occurs}\left(omega, w\right)\right) \Rightarrow \left(\exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{iInter}\left(Y\right)\right) \land \operatorname{member}\left(omega, \operatorname{anchoredCylinder}\left(w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.persistent_word_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translate each occurrence to zero using shift invariance. The intersections of the compact languages with this closed cylinder form nonempty nested compact closed sets. Their common point realizes w in the actual intersection even when the original occurrence positions vary arbitrarily.

**Theorem 1.3 (nested language stabilization).**

$$\forall Y \in Nat \to \operatorname{Set}\left(Int \to CuLetter\right),\; \left(\left(\forall j \in Nat,\; \operatorname{IsCompact}\left(\operatorname{apply}\left(Y, j\right)\right)\right) \land \left(\operatorname{Antitone}\left(Y\right) \land \left(\forall j \in Nat,\; \forall omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{apply}\left(Y, j\right)\right) \Rightarrow \left(\forall a \in Int,\; \operatorname{member}\left((i : Int \mapsto \operatorname{apply}\left(omega, \operatorname{add}\left(i, a\right)\right)), \operatorname{apply}\left(Y, j\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall k \in Nat,\; \exists J \in Nat,\; \forall j \in Nat,\; \operatorname{le}\left(J, j\right) \Rightarrow \left(\forall w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{length}\left(w\right) = k \Rightarrow \left(\left(\exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{apply}\left(Y, j\right)\right) \land \operatorname{Occurs}\left(omega, w\right)\right) \Leftrightarrow \left(\exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{iInter}\left(Y\right)\right) \land \operatorname{Occurs}\left(omega, w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.nested_language_stabilization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A word either persists and has a common realization, or disappears permanently. Finitely many binary words of one fixed length give one common eventual index. This proves equality of the actual word languages at every fixed length, including zero.

**Theorem 1.4 (pressure mono).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right), Z \in \operatorname{Set}\left(Int \to CuLetter\right), theta \in Real,\; \left(\operatorname{Nonempty}\left(X\right) \land \left(\operatorname{Nonempty}\left(Z\right) \land \operatorname{subset}\left(X, Z\right)\right)\right) \Rightarrow \operatorname{le}\left(\operatorname{pressure}\left(X, theta\right), \operatorname{pressure}\left(Z, theta\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.pressure_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inclusion injects the actual finite dictionaries, preserving every positive monomial. Passing their logarithmic quotients to the pressure limit gives the comparison for every real exponent.

**Theorem 1.5 (nested pressure limit).**

$$\forall Y \in Nat \to \operatorname{Set}\left(Int \to CuLetter\right),\; \left(\left(\forall j \in Nat,\; \operatorname{IsCompact}\left(\operatorname{apply}\left(Y, j\right)\right)\right) \land \left(\left(\forall j \in Nat,\; \operatorname{Nonempty}\left(\operatorname{apply}\left(Y, j\right)\right)\right) \land \left(\operatorname{Antitone}\left(Y\right) \land \left(\forall j \in Nat,\; \forall omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{apply}\left(Y, j\right)\right) \Rightarrow \left(\forall a \in Int,\; \operatorname{member}\left((i : Int \mapsto \operatorname{apply}\left(omega, \operatorname{add}\left(i, a\right)\right)), \operatorname{apply}\left(Y, j\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall theta \in Real,\; \operatorname{Nonempty}\left(\operatorname{iInter}\left(Y\right)\right) \land \left(\operatorname{Antitone}\left((j : Nat \mapsto \operatorname{pressure}\left(\operatorname{apply}\left(Y, j\right), theta\right))\right) \land \left(\operatorname{iInf}\left((j : Nat \mapsto \operatorname{pressure}\left(\operatorname{apply}\left(Y, j\right), theta\right))\right) = \operatorname{pressure}\left(\operatorname{iInter}\left(Y\right), theta\right) \land \operatorname{Tendsto}\left((j : Nat \mapsto \operatorname{pressure}\left(\operatorname{apply}\left(Y, j\right), theta\right)), atTop, \operatorname{nhds}\left(\operatorname{pressure}\left(\operatorname{iInter}\left(Y\right), theta\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.nested_pressure_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real theta, minus twenty times its absolute value bounds all positive-length logarithmic quotients uniformly in the language index and length. This bounds both product index orders and permits the two infima to commute. Stabilization identifies each fixed-length infimum with the intersection partition sum, so the pressures decrease to the exact intersection pressure.

**Theorem 1.6 (nested rate limit).**

$$\forall Y \in Nat \to \operatorname{Set}\left(Int \to CuLetter\right),\; \left(\left(\forall j \in Nat,\; \operatorname{IsCompact}\left(\operatorname{apply}\left(Y, j\right)\right)\right) \land \left(\left(\forall j \in Nat,\; \operatorname{Nonempty}\left(\operatorname{apply}\left(Y, j\right)\right)\right) \land \left(\operatorname{Antitone}\left(Y\right) \land \left(\forall j \in Nat,\; \forall omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{apply}\left(Y, j\right)\right) \Rightarrow \left(\forall a \in Int,\; \operatorname{member}\left((i : Int \mapsto \operatorname{apply}\left(omega, \operatorname{add}\left(i, a\right)\right)), \operatorname{apply}\left(Y, j\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{Antitone}\left((j : Nat \mapsto \operatorname{weightedFactorRate}\left(\operatorname{apply}\left(Y, j\right)\right))\right) \land \operatorname{Tendsto}\left((j : Nat \mapsto \operatorname{weightedFactorRate}\left(\operatorname{apply}\left(Y, j\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{weightedFactorRate}\left(\operatorname{iInter}\left(Y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.nested_rate_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inclusion bounds each zero below by the intersection zero. At that zero plus any positive a, the literal upper pressure slope gives pressure at most minus six a. Pressure convergence makes the approximating pressure negative there, which bounds its zero above. No positive-entropy hypothesis is needed.

**Theorem 1.7 (upper memory subshift).**

$$\forall n \in Nat, K \in Nat, d \in Real,\; \operatorname{le}\left(1, K\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right) \land \left(\operatorname{IsClosed}\left(\operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right) \land \left(\operatorname{IsCompact}\left(\operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right) \land \left(\forall omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right) \Rightarrow \left(\forall a \in Int,\; \operatorname{member}\left((i : Int \mapsto \operatorname{apply}\left(omega, \operatorname{add}\left(i, a\right)\right)), \operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.upper_memory_subshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-u configuration satisfies the finite constraints. Each run condition is clopen, and window_value expresses the guard as a continuous finite-window value with a weak lower inequality. The complete constraints are closed, hence compact in the bilateral finite-letter product. Translating the constraints proves shift invariance, including at n equal to K.

**Theorem 1.8 (original upper rate limit).**

$$\forall K \in Nat, d \in Real,\; \operatorname{le}\left(1, K\right) \Rightarrow \left(\operatorname{Antitone}\left((n : Nat \mapsto \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right))\right) \land \operatorname{Tendsto}\left((n : Nat \mapsto \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(upper, n, K, d\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{weightedFactorRate}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.original_upper_rate_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the nested result to Y j equal to MemoryLanguage upper (K+j) K d. The original upper-memory intersection is exactly AuxiliaryLanguage K d. Removing the finite initial segment gives the upper rate limit along every n at least K.

**Theorem 1.9 (original upper root limit).**

$$Ownership \to \left(\forall b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists roots \in MemorySide \to \left(Nat \to Real\right),\; \left(\forall side \in MemorySide, n \in Nat,\; \operatorname{le}\left(K, n\right) \Rightarrow \left(\operatorname{lt}\left(0, \operatorname{apply}\left(roots, side, n\right)\right) \land \left(\operatorname{lt}\left(\operatorname{apply}\left(roots, side, n\right), 1\right) \land \left(\operatorname{weightedRadius}\left(side, n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{apply}\left(roots, side, n\right)\right) = 1 \land \operatorname{weightedFactorRate}\left(\operatorname{MemoryLanguage}\left(side, n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right) = \operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{apply}\left(roots, side, n\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall n \in Nat,\; \operatorname{le}\left(K, n\right) \Rightarrow \left(\operatorname{le}\left(\operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{apply}\left(roots, lower, n\right)\right)\right), \operatorname{etaB}\left(K, b\right)\right) \land \operatorname{le}\left(\operatorname{etaB}\left(K, b\right), \operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{apply}\left(roots, upper, n\right)\right)\right)\right)\right)\right) \land \left(\operatorname{MonotoneOn}\left((n : Nat \mapsto \operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{apply}\left(roots, lower, n\right)\right)\right)), \operatorname{Ici}\left(K\right)\right) \land \left(\operatorname{AntitoneOn}\left((n : Nat \mapsto \operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{apply}\left(roots, upper, n\right)\right)\right)), \operatorname{Ici}\left(K\right)\right) \land \left(\operatorname{Tendsto}\left((n : Nat \mapsto \operatorname{negate}\left(\operatorname{logb}\left(2, \operatorname{apply}\left(roots, upper, n\right)\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{etaB}\left(K, b\right)\right)\right) \land \left(\forall model \in Model, strict \in Bool,\; \operatorname{actualRate}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict\right) = \operatorname{etaB}\left(K, b\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.original_upper_root_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both original source-budget inequalities and K at least two, the exact spectral root families retain their radius-one equations, rate identities, sandwich and monotonicity on n at least K. Their upper logarithmic rates converge downward to the same eta_b supplied by the actual count bridge. This eta_b is also the actual rate for each source model and each strict or weak guard flag. The conclusion holds for every ownership assignment.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.anchoredCylinder`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.nested_language_stabilization`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.nested_pressure_limit`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.nested_rate_limit`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.original_upper_rate_limit`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.original_upper_root_limit`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.persistent_word_intersection`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.pressure_mono`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.upper_memory_subshift`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge](ActualCountRateBridge.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure](WeightedPressure.md)
