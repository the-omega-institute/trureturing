# Finite Start Five Mode Source

## Abstract

Coherent finite word laws and exact acquired-history source updating.

States are Fin 5. Visible symbols are Fin 4, with code 2 denoted B. The observation vector is [0,1,2,3,2]. The transition rows are [1-p-q-r,p,0,q,r], [q,1-p-q,p,0,0], [0,q,1-p-q,p,0], [p,0,q,1-p-q,0], [r,0,0,0,1-r]. Put a=1-p-q and b=1-r. Admissibility means p>0, q>0, r>0 and p+q+r<1; it includes p=q and r=p+q.

The first acquired read filters the uniform vector pi directly. Later reads advance through the literal matrix and then filter. acquiredStateWeights retains unnormalized current-state weights, historyMass is their sum, and acquiredPosterior divides them by that sum. initialWordWeight begins at Y0; futureWordWeight advances before its first read. A word w is converted to its chronological list by ofFn. Append denotes chronological concatenation, and snoc appends one final symbol.

**Theorem 1.1 (Every literal row sums to one).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall i: State,\ \sum_{j\in State} (\operatorname{transition}\left(p, q, r, i, j\right)) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.transition_row_stochastic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Row sums are one for every real parameter triple. Nonnegativity is a separate condition.

**Theorem 1.2 (Admissible entries are nonnegative).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall i: State,\ \forall j: State,\ 0 \leq \operatorname{transition}\left(p, q, r, i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.transition_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict parameter inequalities make each of the displayed entries nonnegative.

**Theorem 1.3 (The uniform law is stationary).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall j: State,\ \sum_{i\in State} (\operatorname{uniformPi}\left(i\right)*\operatorname{transition}\left(p, q, r, i, j\right)) = \operatorname{uniformPi}\left(j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.uniform_stationary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every column preserves weight one fifth, for arbitrary real parameters.

**Theorem 1.4 (State weights represent literal chronological words).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall n: \mathbb{N},\ \forall w: \operatorname{Fin}\left(n\right)\to Visible,\ \operatorname{historyMass}\left(p, q, r, \operatorname{ofFn}\left(w\right)\right) = \operatorname{initialWordWeight}\left(p, q, r, uniformPi, n, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.acquired_mass_eq_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mass of the acquired state-weight recursion equals the independently defined literal initialized word weight.

**Theorem 1.5 (Finite future word weights are nonnegative).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall v: State\to \mathbb{R},\ (\forall i: State,\ 0 \leq \operatorname{v}\left(i\right)) \Rightarrow \forall n: \mathbb{N},\ \forall w: \operatorname{Fin}\left(n\right)\to Visible,\ 0 \leq \operatorname{futureWordWeight}\left(p, q, r, v, n, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.future_word_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Advancement, observation filtering and finite summation preserve nonnegative weights.

**Theorem 1.6 (The actual sum over all future words).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall v: State\to \mathbb{R},\ \forall n: \mathbb{N},\ \sum_{w\in \operatorname{Fin}\left(n\right)\to Visible} (\operatorname{futureWordWeight}\left(p, q, r, v, n, w\right)) = \sum_{i\in State} (\operatorname{v}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.sum_future_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum ranges over every function Fin n to Visible. Its proof connects this enumeration to the recursive total.

**Theorem 1.7 (The actual initialized word sum is one).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall n: \mathbb{N},\ \sum_{w\in \operatorname{Fin}\left(n\right)\to Visible} (\operatorname{initialWordWeight}\left(p, q, r, uniformPi, n, w\right)) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.sum_initial_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initialized law is normalized on the full finite word space at every horizon, including zero.

**Theorem 1.8 (Each future prefix has its final-symbol marginal).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall v: State\to \mathbb{R},\ \forall n: \mathbb{N},\ \forall w: \operatorname{Fin}\left(n\right)\to Visible,\ \sum_{y\in Visible} (\operatorname{futureWordWeight}\left(p, q, r, v, (n+1), \operatorname{snoc}\left(w, y\right)\right)) = \operatorname{futureWordWeight}\left(p, q, r, v, n, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.final_symbol_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed chronological prefix w, summing over its last appended symbol gives exactly the weight of w.

**Theorem 1.9 (Each initialized prefix has its final-symbol marginal).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall n: \mathbb{N},\ \forall w: \operatorname{Fin}\left(n\right)\to Visible,\ \sum_{y\in Visible} (\operatorname{initialWordWeight}\left(p, q, r, uniformPi, (n+1), \operatorname{snoc}\left(w, y\right)\right)) = \operatorname{initialWordWeight}\left(p, q, r, uniformPi, n, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.initial_final_symbol_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same pointwise marginal identity holds for the recording-boundary law.

**Theorem 1.10 (Stationarity identifies the complete empty law).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall H: \mathbb{N},\ \forall w: \operatorname{Fin}\left(H\right)\to Visible,\ \operatorname{initialWordWeight}\left(p, q, r, uniformPi, H, w\right) = \operatorname{futureWordWeight}\left(p, q, r, uniformPi, H, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.empty_boundary_and_positive_timing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity piP=pi equates initial and future weights word by word. The empty query still begins with Y0.

**Theorem 1.11 (Actual positive histories determine every future cylinder).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall h: \operatorname{List}\left(Visible\right),\ ((h \neq [] \land 0 < \operatorname{historyMass}\left(p, q, r, h\right))) \Rightarrow \forall H: \mathbb{N},\ \forall w: \operatorname{Fin}\left(H\right)\to Visible,\ (\frac{\operatorname{historyMass}\left(p, q, r, \operatorname{append}\left(h, \operatorname{ofFn}\left(w\right)\right)\right)}{\operatorname{historyMass}\left(p, q, r, h\right)} = \operatorname{futureWordWeight}\left(p, q, r, \operatorname{acquiredPosterior}\left(p, q, r, h\right), H, w\right) \land (\sum_{u\in \operatorname{Fin}\left(H\right)\to Visible} (\operatorname{futureWordWeight}\left(p, q, r, \operatorname{acquiredPosterior}\left(p, q, r, h\right), H, u\right)) = 1 \land 0 \leq \operatorname{futureWordWeight}\left(p, q, r, \operatorname{acquiredPosterior}\left(p, q, r, h\right), H, w\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.actual_positive_conditional_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive nonempty acquired history, the joint-cylinder quotient is its normalized posterior future law. That law is normalized and nonnegative at every finite horizon.

**Theorem 1.12 (Conditioning in literal fixed-length word notation).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall n: \mathbb{N},\ \forall hword: \operatorname{Fin}\left(n\right)\to Visible,\ ((0 < n \land 0 < \operatorname{initialWordWeight}\left(p, q, r, uniformPi, n, hword\right))) \Rightarrow \forall H: \mathbb{N},\ \forall w: \operatorname{Fin}\left(H\right)\to Visible,\ \frac{\operatorname{initialWordWeight}\left(p, q, r, uniformPi, n+H, \operatorname{append}\left(hword, w\right)\right)}{\operatorname{initialWordWeight}\left(p, q, r, uniformPi, n, hword\right)} = \operatorname{futureWordWeight}\left(p, q, r, \operatorname{acquiredPosterior}\left(p, q, r, \operatorname{ofFn}\left(hword\right)\right), H, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.literal_conditional_future` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same identity applies directly to the original initialized word law on concatenated Fin-indexed words.

**Theorem 1.13 (The total source update tracks every positive acquired history).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall h: \operatorname{List}\left(Visible\right),\ (0 < \operatorname{historyMass}\left(p, q, r, h\right)) \Rightarrow \operatorname{acquiredPosterior}\left(p, q, r, h\right) = \operatorname{sourceProfile}\left(p, q, r, \operatorname{sourceRun}\left(h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.positive_history_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

sourceRun iterates sourceUpdate from Start on the actual symbols. Its normalized source profile equals the acquired posterior. Singletons reset to their pure states; B advances startup tags or the appropriate pure branch.

**Theorem 1.14 (All-B cylinders have two literal hidden paths).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall k: \mathbb{N},\ \operatorname{initialWordWeight}\left(p, q, r, uniformPi, (k+1), \operatorname{constant}\left(B\right)\right) = \frac{(\operatorname{a}\left(p, q\right))^{k}+(\operatorname{b}\left(r\right))^{k}}{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.all_b_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initialized all-B word of length k+1 has mass (a^k+b^k)/5. This algebraic identity holds for every real parameter triple.

**Theorem 1.15 (The acquired all-B posterior has the power coordinates).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall k: \mathbb{N},\ \operatorname{acquiredPosterior}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right) = [0,0,\frac{(\operatorname{a}\left(p, q\right))^{k}}{(\operatorname{a}\left(p, q\right))^{k}+(\operatorname{b}\left(r\right))^{k}},0,\frac{(\operatorname{b}\left(r\right))^{k}}{(\operatorname{a}\left(p, q\right))^{k}+(\operatorname{b}\left(r\right))^{k}}]$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.actual_all_B_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the posterior of the actual acquired cylinder, supported on states 2 and 4. Both coordinates are positive.

**Theorem 1.16 (Positive histories are exhaustively startup or pure).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ \forall h: \operatorname{List}\left(Visible\right),\ ((h \neq [] \land 0 < \operatorname{historyMass}\left(p, q, r, h\right))) \Rightarrow (\exists k: \mathbb{N},\ (h = \operatorname{replicate}\left((k+1), B\right) \land (\operatorname{sourceRun}\left(h\right) = \operatorname{startup}\left(k\right) \land \operatorname{acquiredStateWeights}\left(p, q, r, h\right) = \operatorname{startupVector}\left(p, q, r, k\right))) \lor \exists i: State,\ (\operatorname{sourceRun}\left(h\right) = \operatorname{pure}\left(i\right) \land \operatorname{acquiredPosterior}\left(p, q, r, h\right) = \operatorname{pureVector}\left(i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.positive_history_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A word with no singleton is an initial all-B run. The first singleton identifies its state, and every subsequent acquired symbol preserves purity. This covers all positive nonempty words.

**Theorem 1.17 (Every pure B transition is an actual positive extension).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall h: \operatorname{List}\left(Visible\right),\ ((h \neq [] \land 0 < \operatorname{historyMass}\left(p, q, r, h\right))) \Rightarrow \forall j: State,\ (\operatorname{acquiredPosterior}\left(p, q, r, h\right) = \operatorname{pureVector}\left(j\right)) \Rightarrow (\operatorname{historyMass}\left(p, q, r, \operatorname{append}\left(h, [B]\right)\right) = \operatorname{historyMass}\left(p, q, r, h\right)*\operatorname{pureBMass}\left(p, q, r, j\right) \land (0 < \operatorname{historyMass}\left(p, q, r, \operatorname{append}\left(h, [B]\right)\right) \land \operatorname{acquiredPosterior}\left(p, q, r, \operatorname{append}\left(h, [B]\right)\right) = \operatorname{pureVector}\left(\operatorname{pureBSuccessor}\left(j\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.actual_pure_B_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The B successor is 4 from states 0 and 4, and 2 from states 1,2,3. The corresponding positive masses are r,b,p,a,q respectively. The statement applies to every positive pure history.

**Theorem 1.18 (All five pure witnesses have positive self-loop padding).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall j: State,\ \forall n: \mathbb{N},\ (\operatorname{historyMass}\left(p, q, r, \operatorname{append}\left(\operatorname{pureWitness}\left(j\right), \operatorname{replicate}\left(n, \operatorname{observation}\left(j\right)\right)\right)\right) = \operatorname{pureWitnessMass}\left(p, r, j\right)*(\operatorname{transition}\left(p, q, r, j, j\right))^{n} \land (0 < \operatorname{historyMass}\left(p, q, r, \operatorname{append}\left(\operatorname{pureWitness}\left(j\right), \operatorname{replicate}\left(n, \operatorname{observation}\left(j\right)\right)\right)\right) \land \operatorname{acquiredPosterior}\left(p, q, r, \operatorname{append}\left(\operatorname{pureWitness}\left(j\right), \operatorname{replicate}\left(n, \operatorname{observation}\left(j\right)\right)\right)\right) = \operatorname{pureVector}\left(j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.positive_pure_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pure witnesses are [0], [1], [1,B], [3], [0,B] in state order. Their base masses are 1/5,1/5,p/5,1/5,r/5. Padding by n copies of the state's visible symbol multiplies the mass by the nth power of its diagonal transition, and the posterior remains pure. Every finite padding length has positive mass.

**Theorem 1.19 (Rare transitions admit arbitrary positive B extensions).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall n: \mathbb{N},\ (\operatorname{historyMass}\left(p, q, r, \operatorname{append}\left([1,B], \operatorname{replicate}\left(n, B\right)\right)\right) = \frac{p*(\operatorname{a}\left(p, q\right))^{n}}{5} \land (0 < \operatorname{historyMass}\left(p, q, r, \operatorname{append}\left([1,B], \operatorname{replicate}\left(n, B\right)\right)\right) \land (\operatorname{acquiredPosterior}\left(p, q, r, \operatorname{append}\left([1,B], \operatorname{replicate}\left(n, B\right)\right)\right) = \operatorname{pureVector}\left(2\right) \land (\operatorname{historyMass}\left(p, q, r, \operatorname{append}\left([0,B], \operatorname{replicate}\left(n, B\right)\right)\right) = \frac{r*(\operatorname{b}\left(r\right))^{n}}{5} \land (0 < \operatorname{historyMass}\left(p, q, r, \operatorname{append}\left([0,B], \operatorname{replicate}\left(n, B\right)\right)\right) \land \operatorname{acquiredPosterior}\left(p, q, r, \operatorname{append}\left([0,B], \operatorname{replicate}\left(n, B\right)\right)\right) = \operatorname{pureVector}\left(4\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.rare_B_extension_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending n B's after 1B gives mass p a^n/5 and posterior e2. Appending n B's after 0B gives mass r b^n/5 and posterior e4.

**Theorem 1.20 (Every source tag has an actual positive history).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall z: SourceTag,\ \exists h: \operatorname{List}\left(Visible\right),\ (\operatorname{sourceRun}\left(h\right) = z \land (0 < \operatorname{historyMass}\left(p, q, r, h\right) \land (\operatorname{acquiredPosterior}\left(p, q, r, h\right) = \operatorname{sourceProfile}\left(p, q, r, z\right) \land (h = [] \iff z = Start))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.complete_source_tag_reachability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start is realized by the empty history, each startup k by B^(k+1), and each pure state by its literal witness. The realization has its stated normalized acquired source profile.

**Theorem 1.21 (One coherent conditional family on every actual history).**

$$\forall p: \mathbb{R},\ \forall q: \mathbb{R},\ \forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right)) \Rightarrow \forall h: \operatorname{List}\left(Visible\right),\ (0 < \operatorname{historyMass}\left(p, q, r, h\right)) \Rightarrow \forall H: \mathbb{N},\ \forall w: \operatorname{Fin}\left(H\right)\to Visible,\ (0 \leq \operatorname{actualFutureWordWeight}\left(p, q, r, h, H, w\right) \land (\sum_{u\in \operatorname{Fin}\left(H\right)\to Visible} (\operatorname{actualFutureWordWeight}\left(p, q, r, h, H, u\right)) = 1 \land \sum_{y\in Visible} (\operatorname{actualFutureWordWeight}\left(p, q, r, h, (H+1), \operatorname{snoc}\left(w, y\right)\right)) = \operatorname{actualFutureWordWeight}\left(p, q, r, h, H, w\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.actual_law_probability_and_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive history, actualFutureWordWeight uses the initialized law at empty history and the posterior future law otherwise. Every horizon is normalized and nonnegative, with pointwise consistency under deletion of its final read.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.acquired_mass_eq_word`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.actual_all_B_posterior`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.actual_law_probability_and_coherence`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.actual_positive_conditional_law`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.actual_pure_B_transition`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.all_b_mass`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.complete_source_tag_reachability`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.empty_boundary_and_positive_timing`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.final_symbol_coherence`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.future_word_nonnegative`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.initial_final_symbol_coherence`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.literal_conditional_future`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.positive_history_classification`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.positive_history_invariant`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.positive_pure_padding`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.rare_B_extension_masses`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.sum_future_words`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.sum_initial_words`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.transition_nonnegative`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.transition_row_stochastic`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.uniform_stationary`
