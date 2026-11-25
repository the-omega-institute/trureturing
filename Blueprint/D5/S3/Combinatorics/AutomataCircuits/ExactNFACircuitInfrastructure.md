# Exact automata and circuit obstructions

## Abstract

Exact automata, bounded circuit polynomials and finite-grid support estimates.

**Definition 1.1 (Exact acceptance).**

$$\forall Alphabet \in Type,\; \forall k \in \mathbb{N},\; \forall M \in \operatorname{NFA}\left(Alphabet, \operatorname{Fin}\left(k\right)\right),\; \forall w \in \operatorname{List}\left(Alphabet\right),\; \operatorname{exactlyAccepts}\left(M, w\right) = \left((w \in \operatorname{NFA}.\operatorname{accepts}\left(M\right)) \land (\forall y \in \operatorname{List}\left(Alphabet\right),\; (\operatorname{List}.\operatorname{length}\left(y\right) = \operatorname{List}.\operatorname{length}\left(w\right)) \Rightarrow ((y \in \operatorname{NFA}.\operatorname{accepts}\left(M\right)) \Rightarrow (y = w)))\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.exactlyAccepts` (`✓ std3`).

*Citation.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Definition 1.1, p. 2: “Let x ∈ Σ∗. An automaton M exactly accepts x if M accepts x, and whenever both y ≠ x and |y| = |x| then M rejects y.” Words are Lists; NFA has no epsilon transitions. Accepting paths need not be unique.

**Definition 1.2 (A state-count realization).**

$$\forall Alphabet \in Type,\; \forall w \in \operatorname{List}\left(Alphabet\right),\; \forall k \in \mathbb{N},\; \operatorname{realizesStateCount}\left(w, k\right) = \left(\exists M \in \operatorname{NFA}\left(Alphabet, \operatorname{Fin}\left(k\right)\right),\; \exists initial \in \operatorname{Fin}\left(k\right),\; (\operatorname{NFA}.\operatorname{start}\left(M\right) = \{initial\}) \land (\operatorname{exactlyAccepts}\left(M, w\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.realizesStateCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

A realization uses Fin k as its state set and a singleton initial-state set. Its accepting-state set is unrestricted.

**Definition 1.3 (Non-deterministic automatic complexity).**

$$\forall Alphabet \in Type,\; \forall w \in \operatorname{List}\left(Alphabet\right),\; \operatorname{A}_{Ne}\left(w\right) = \operatorname{sInf}\left(\{v:\operatorname{ENat} \mid \exists k \in \mathbb{N},\; (v = (k:\operatorname{ENat})) \land (\operatorname{realizesStateCount}\left(w, k\right))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.A_Ne` (`✓ std3`).

*Citation.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Definition 1.6, p. 3: “Let x ∈ Σ∗. The non-deterministic automatic complexity of x is Aₙₑ(x) = min{ k ∈ ℕ : there exists an NFA of k states which exactly accepts x }.” A_Ne is the infimum of the displayed natural state counts in ℕ∞; an empty set has infimum infinity.

**Definition 1.4 (The strict threshold language).**

$$\forall Alphabet \in Type,\; \forall q \in \mathbb{Q},\; \operatorname{Lq}\left(Alphabet := Alphabet, q\right) = \{w:\operatorname{List}\left(Alphabet\right) \mid \exists k \in \mathbb{N},\; (\operatorname{A}_{Ne}\left(w\right) = (k:\operatorname{ENat})) \land ((k:\mathbb{Q}) < q \cdot (\operatorname{List}.\operatorname{length}\left(w\right):\mathbb{Q}))\}$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.Lq` (`✓ std3`).

*Citation.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Definition 1.8, p. 3: “For q ∈ (0,1/2), define Lq = {x ∈ Σ∗ : Aₙₑ(x) < q|x|}.” Length counts original letters. The finite attained state count is coerced into ℚ before comparison.

**Definition 1.5 (Finite circuit data).**

$$\forall R \in Type,\; \forall I \in Type,\; \operatorname{Circuit}\left(R, I\right) = \{nodes:\mathbb{N}; gate:\operatorname{Fin}\left(nodes\right) \to \operatorname{Sum}\left((I)\times (Bool), \operatorname{Sum}\left(R, \operatorname{Sum}\left(\operatorname{List}\left(\operatorname{Fin}\left(nodes\right)\right), \operatorname{List}\left(\operatorname{Fin}\left(nodes\right)\right)\right)\right)\right); output:\operatorname{Fin}\left(nodes\right); level:\operatorname{Fin}\left(nodes\right) \to \mathbb{N}\}$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.Circuit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

The four fields describe a finite directed circuit. A gate is a literal, a constant, a finite addition list or a finite multiplication list. The Bool flag negates only input literals.

**Definition 1.6 (Depth and multiplication fan-in).**

$$\forall R \in Type,\; \forall I \in Type,\; \forall C \in \operatorname{Circuit}\left(R, I\right),\; \forall h \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{bounded}\left(C, h, b\right) = \left(\forall v \in \operatorname{Fin}\left(\operatorname{Circuit}.\operatorname{nodes}\left(C\right)\right),\; (\operatorname{Circuit}.\operatorname{level}\left(C, v\right) \le h) \land (\begin{aligned}match \operatorname{Circuit}.\operatorname{gate}\left(C, v\right) with\\| \operatorname{Sum}.\operatorname{inl}\left(literal\right) \mapsto True\\| \operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inl}\left(a\right)\right) \mapsto True\\| \operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inl}\left(inputs\right)\right)\right) \mapsto \forall u \in \operatorname{Fin}\left(\operatorname{Circuit}.\operatorname{nodes}\left(C\right)\right),\; (u \in inputs) \Rightarrow (\operatorname{Circuit}.\operatorname{level}\left(C, u\right) < \operatorname{Circuit}.\operatorname{level}\left(C, v\right))\\| \operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inr}\left(inputs\right)\right)\right) \mapsto (\operatorname{List}.\operatorname{length}\left(inputs\right) \le b) \land (\forall u \in \operatorname{Fin}\left(\operatorname{Circuit}.\operatorname{nodes}\left(C\right)\right),\; (u \in inputs) \Rightarrow (\operatorname{Circuit}.\operatorname{level}\left(C, u\right) < \operatorname{Circuit}.\operatorname{level}\left(C, v\right)))\end{aligned})\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.bounded` (`✓ std3`).

*Citation.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Definition 4.4, p. 16: “Each Ci is defined over the basic set {∧, ⊕} and accepts negative literals.” “The family (Ci)i<ω has constant depth.” “Each Ci has unbounded fan-in-⊕ and bounded fan-in-∧.” “Each Ci accepts words of length i.” Levels strictly increase along every wire; h bounds all levels and b bounds only multiplication input-list lengths.

**Definition 1.7 (Synchronous gate evaluation).**

$$\forall R \in Type,\; \forall I \in Type,\; [\operatorname{CommRing}\left(R\right)], \forall C \in \operatorname{Circuit}\left(R, I\right),\; \forall x \in I \to R,\; (\forall v \in \operatorname{Fin}\left(\operatorname{Circuit}.\operatorname{nodes}\left(C\right)\right),\; \operatorname{evalRounds}\left(C, x, 0, v\right) = 0) \land (\forall t \in \mathbb{N},\; \forall v \in \operatorname{Fin}\left(\operatorname{Circuit}.\operatorname{nodes}\left(C\right)\right),\; \operatorname{evalRounds}\left(C, x, t + 1, v\right) = \begin{aligned}match \operatorname{Circuit}.\operatorname{gate}\left(C, v\right) with\\| \operatorname{Sum}.\operatorname{inl}\left((i,negative)\right) \mapsto if negative then 1 - x\left(i\right) else x\left(i\right)\\| \operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inl}\left(a\right)\right) \mapsto a\\| \operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inl}\left(inputs\right)\right)\right) \mapsto \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{evalRounds}\left(C, x, t\right), inputs\right)\right)\\| \operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inr}\left(inputs\right)\right)\right) \mapsto \operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{evalRounds}\left(C, x, t\right), inputs\right)\right)\end{aligned})$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.evalRounds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Round zero is zero at every node. Each following round reads the preceding round at the gate's input nodes. Empty sums and products have values zero and one.

**Definition 1.8 (Circuit output).**

$$\forall R \in Type,\; \forall I \in Type,\; [\operatorname{CommRing}\left(R\right)], \forall C \in \operatorname{Circuit}\left(R, I\right),\; \forall x \in I \to R,\; \operatorname{evaluate}\left(C, x\right) = \operatorname{evalRounds}\left(C, x, \operatorname{Circuit}.\operatorname{nodes}\left(C\right) + 1, \operatorname{Circuit}.\operatorname{output}\left(C\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.evaluate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

The output is read after nodes + 1 synchronous rounds. For the acyclic circuits described by bounded this suffices to evaluate every input dependency.

**Definition 1.9 (Prime-field recognition on the alphabet).**

$$\forall Alphabet \in Type,\; \forall p \in \mathbb{N},\; \forall e \in Alphabet \to \operatorname{ZMod}\left(p\right),\; \forall L \in \operatorname{Set}\left(\operatorname{List}\left(Alphabet\right)\right),\; \operatorname{arithmeticRecognizable}\left(p, e, L\right) = \left(\exists h \in \mathbb{N},\; \exists b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \exists C \in \operatorname{Circuit}\left(\operatorname{ZMod}\left(p\right), \operatorname{Fin}\left(n\right)\right),\; (\operatorname{bounded}\left(C, h, b\right)) \land (\forall x \in \operatorname{Fin}\left(n\right) \to Alphabet,\; (\operatorname{List}.\operatorname{ofFn}\left(x\right) \in L) \Leftrightarrow (\operatorname{evaluate}\left(C, fun (i:\operatorname{Fin}\left(n\right)) \mapsto e\left(x\left(i\right)\right)\right) \ne 0))\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.arithmeticRecognizable` (`✓ std3`).

*Citation.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Arithmetic interpretation, p. 16: “To extend this equivalence beyond binary alphabets, take the field Fₚ for some prime p > 2. By interpreting (⊕, ∧) as (+, ×) mod p, we extend SAC⁰-recognisability to alphabets of prime cardinality.” Here the alphabet is embedded in ZMod p. The bounds h and b precede all lengths. At each length one circuit precedes all input words. Addition fan-in, circuit size and nonuniformity have no bound. Only values on the embedded alphabet are constrained; negative literals evaluate as 1 − Xi.

**Definition 1.10 (Recognition of valid Boolean blocks).**

$$\forall Alphabet \in Type,\; \forall t \in \mathbb{N},\; \forall e \in Alphabet \to \left(\operatorname{Fin}\left(t\right) \to Bool\right),\; \forall L \in \operatorname{Set}\left(\operatorname{List}\left(Alphabet\right)\right),\; \operatorname{booleanRecognizable}\left(t, e, L\right) = \left(\exists h \in \mathbb{N},\; \exists b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \exists C \in \operatorname{Circuit}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(n\right))\times (\operatorname{Fin}\left(t\right))\right),\; (\operatorname{bounded}\left(C, h, b\right)) \land (\forall x \in \operatorname{Fin}\left(n\right) \to Alphabet,\; (\operatorname{List}.\operatorname{ofFn}\left(x\right) \in L) \Leftrightarrow (\operatorname{evaluate}\left(C, fun (i:(\operatorname{Fin}\left(n\right))\times (\operatorname{Fin}\left(t\right))) \mapsto if e\left(x\left(i.1\right), i.2\right) then 1 else 0\right) \ne 0))\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.booleanRecognizable` (`✓ std3`).

*Citation.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Definition 4.4 is interpreted over ZMod 2. One alphabet symbol occupies t bits; the original word has n letters and the circuit has Fin n × Fin t input coordinates. Correctness is imposed on valid encoded words only.

**Definition 1.11 (Finite attained minima).**

$$\forall Alphabet \in Type,\; \operatorname{complexityTotal}\left(Alphabet\right) = \left(\forall w \in \operatorname{List}\left(Alphabet\right),\; \exists k \in \mathbb{N},\; (\operatorname{realizesStateCount}\left(w, k\right)) \land (\operatorname{A}_{Ne}\left(w\right) = (k:\operatorname{ENat}))\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.complexityTotal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Every word has a finite exact-NFA state minimum and an automaton attaining it.

**Definition 1.12 (A length-section cardinality).**

$$\forall A \in Type,\; [\operatorname{Fintype}\left(A\right)], \forall L \in \operatorname{Set}\left(\operatorname{List}\left(A\right)\right),\; \forall n \in \mathbb{N},\; \operatorname{languageCount}\left(L, n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(fun (x:\operatorname{Fin}\left(n\right) \to A) \mapsto \operatorname{List}.\operatorname{ofFn}\left(x\right) \in L, \operatorname{Finset}.\operatorname{univ}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.languageCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Count the length-n words using the bijection between lists of length n and functions Fin n → A.

**Definition 1.13 (Finite-scale sparsity with a witness).**

$$\forall A \in Type,\; [\operatorname{Fintype}\left(A\right)], \forall L \in \operatorname{Set}\left(\operatorname{List}\left(A\right)\right),\; \operatorname{sparseNonempty}\left(L\right) = \left(\forall D \in \mathbb{N},\; \exists n \in \mathbb{N},\; (\exists x \in \operatorname{Fin}\left(n\right) \to A,\; \operatorname{List}.\operatorname{ofFn}\left(x\right) \in L) \land (\operatorname{languageCount}\left(L, n\right) \cdot \operatorname{Fintype}.\operatorname{card}\left(A\right)^{D} < \operatorname{Fintype}.\operatorname{card}\left(A\right)^{n})\right)$$

*Formalization.* `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseNonempty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

At each degree D there is a nonempty length section whose cardinality times the alphabet size to the Dth power is strictly below the size of all words of that length.

**Theorem 1.14 (The word-chain realization).**

$$\forall Alphabet \in Type,\; \forall w \in \operatorname{List}\left(Alphabet\right),\; \operatorname{realizesStateCount}\left(w, \operatorname{List}.\operatorname{length}\left(w\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.realizesWordLengthSucc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

A chain with one state for each prefix, including both endpoints, accepts exactly the given word.

**Theorem 1.15 (Attainment of a finite realization minimum).**

$$\forall Alphabet \in Type,\; \forall w \in \operatorname{List}\left(Alphabet\right),\; (\exists k \in \mathbb{N},\; \operatorname{realizesStateCount}\left(w, k\right)) \Rightarrow (\exists k \in \mathbb{N},\; (\operatorname{realizesStateCount}\left(w, k\right)) \land (\operatorname{A}_{Ne}\left(w\right) = (k:\operatorname{ENat})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.minimumAttained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Any nonempty set of realizing natural state counts has a least member, and its coercion equals the infimum used in A_Ne.

**Theorem 1.16 (Every word has finite exact complexity).**

$$\forall Alphabet \in Type,\; \forall w \in \operatorname{List}\left(Alphabet\right),\; \exists k \in \mathbb{N},\; (\operatorname{realizesStateCount}\left(w, k\right)) \land (\operatorname{A}_{Ne}\left(w\right) = (k:\operatorname{ENat}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.complexityTotalProof` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

The word-chain realization makes the set of admissible state counts nonempty. Natural-number well-ordering then supplies the minimum.

**Theorem 1.17 (Injective alphabet relabelling).**

$$\forall A \in Type,\; \forall B \in Type,\; \forall f \in A \to B,\; (\operatorname{Function}.\operatorname{Injective}\left(f\right)) \Rightarrow (\forall q \in \mathbb{Q},\; \forall w \in \operatorname{List}\left(A\right),\; (\operatorname{List}.\operatorname{map}\left(f, w\right) \in \operatorname{Lq}\left(Alphabet := B, q\right)) \Leftrightarrow (w \in \operatorname{Lq}\left(Alphabet := A, q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.memLqMapIff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Pulling an NFA back along an injection and pushing it forward with no transitions on unused labels preserve exact acceptance and the number of states. Both directions preserve the strict threshold.

**Theorem 1.18 (Sparse arithmetic-language obstruction).**

$$\forall A \in Type,\; [\operatorname{Fintype}\left(A\right)], (2 \le \operatorname{Fintype}.\operatorname{card}\left(A\right)) \Rightarrow (\forall L \in \operatorname{Set}\left(\operatorname{List}\left(A\right)\right),\; (\operatorname{sparseNonempty}\left(L\right)) \Rightarrow (\forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow (\forall e \in A \to \operatorname{ZMod}\left(p\right),\; (\operatorname{Function}.\operatorname{Injective}\left(e\right)) \Rightarrow (\neg (\operatorname{arithmeticRecognizable}\left(p, e, L\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseArithmeticNotRecognizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

A bounded circuit family has a uniform total-degree bound. Reducing a polynomial on the finite alphabet grid and inducting on a leading coefficient gives a positive support fraction whenever the support is nonempty. This contradicts sparseNonempty.

**Theorem 1.19 (Complement arithmetic-language obstruction).**

$$\forall A \in Type,\; [\operatorname{Fintype}\left(A\right)], (2 \le \operatorname{Fintype}.\operatorname{card}\left(A\right)) \Rightarrow (\forall L \in \operatorname{Set}\left(\operatorname{List}\left(A\right)\right),\; (\operatorname{sparseNonempty}\left(L\right)) \Rightarrow (\forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow (\forall e \in A \to \operatorname{ZMod}\left(p\right),\; (\operatorname{Function}.\operatorname{Injective}\left(e\right)) \Rightarrow (\neg (\operatorname{arithmeticRecognizable}\left(p, e, (L)^{c}\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseArithmeticComplementNotRecognizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

Over ZMod p, the polynomial 1 − (P^(p−1)) is nonzero precisely where P vanishes. Its degree is bounded by (p−1) times the original degree. Apply the same sparse-language obstruction.

**Theorem 1.20 (Restriction to two Boolean codewords).**

$$\forall A \in Type,\; \forall t \in \mathbb{N},\; \forall e \in A \to \left(\operatorname{Fin}\left(t\right) \to Bool\right),\; \forall L \in \operatorname{Set}\left(\operatorname{List}\left(A\right)\right),\; \forall labels \in Bool \to A,\; (\operatorname{sparseNonempty}\left(\{w:\operatorname{List}\left(Bool\right) \mid \operatorname{List}.\operatorname{map}\left(labels, w\right) \in L\}\right)) \Rightarrow (\neg (\operatorname{booleanRecognizable}\left(t, e, L\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseBooleanNotRecognizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

For each block coordinate the two chosen codewords give an affine polynomial in one Boolean input. Substitution preserves the uniform degree bound, and a sparse nonempty binary pullback contradicts recognition.

**Theorem 1.21 (The Boolean complement obstruction).**

$$\forall A \in Type,\; \forall t \in \mathbb{N},\; \forall e \in A \to \left(\operatorname{Fin}\left(t\right) \to Bool\right),\; \forall L \in \operatorname{Set}\left(\operatorname{List}\left(A\right)\right),\; \forall labels \in Bool \to A,\; (\operatorname{sparseNonempty}\left(\{w:\operatorname{List}\left(Bool\right) \mid \operatorname{List}.\operatorname{map}\left(labels, w\right) \in L\}\right)) \Rightarrow (\neg (\operatorname{booleanRecognizable}\left(t, e, (L)^{c}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseBooleanComplementNotRecognizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joey Chen; Bjørn Kjos-Hanssen; Ivan Koswara; Linus Richter; Frank Stephan (2025). *Languages of Words of Low Automatic Complexity Are Hard to Compute*. DOI: [10.48550/arXiv.2510.07696](https://doi.org/10.48550/arXiv.2510.07696). URL: <https://arxiv.org/abs/2510.07696v1>.

*Commentary.*

The same two-codeword restriction applied to the complement is converted by 1 − P over ZMod 2. The original binary pullback supplies the nonempty sparse sections.

## References

- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.A_Ne`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.Circuit`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.Lq`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.arithmeticRecognizable`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.booleanRecognizable`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.bounded`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.complexityTotal`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.complexityTotalProof`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.evalRounds`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.evaluate`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.exactlyAccepts`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.languageCount`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.memLqMapIff`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.minimumAttained`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.realizesStateCount`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.realizesWordLengthSucc`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseArithmeticComplementNotRecognizable`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseArithmeticNotRecognizable`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseBooleanComplementNotRecognizable`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseBooleanNotRecognizable`
- Truth anchor: `D5/S3/Combinatorics/AutomataCircuits/ExactNFACircuitInfrastructure.sparseNonempty`
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
