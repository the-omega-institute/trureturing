# Feedback Normalization Criterion

## Abstract

Finite feedback normalization is equivalent to prefix causality and sequential kernel factorization.

**Definition 1.1 (Dependent output and action prefixes).**

$$\forall T: \mathbb {N}, X: (\operatorname {Fin}(T)) \to \operatorname {Type}, n: \mathbb {N},\\{}\operatorname {Prefix}(X, n) = (i: \operatorname {Below}(\operatorname {Fin}(T), n)) \to X_{i}.$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.Prefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A prefix of length n is a dependent word on precisely the rounds whose indices are below n.

**Definition 1.2 (Restriction to an initial prefix).**

$$\forall T: \mathbb {N}, X: (\operatorname {Fin}(T)) \to \operatorname {Type}, x: (t: \operatorname {Fin}(T)) \to X_{t}, n: \mathbb {N}, i: \operatorname {Below}(\operatorname {Fin}(T), n),\\{}\operatorname {restrictPrefix}(x, n)(i) = x(i).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.restrictPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complete dependent word restricts to a prefix by evaluation at the underlying round index.

**Definition 1.3 (Splicing at a round cut).**

$$\forall T: \mathbb {N}, X: (\operatorname {Fin}(T)) \to \operatorname {Type}, n: \mathbb {N}, u: \operatorname {Prefix}(X, n), v: (i: \operatorname {From}(\operatorname {Fin}(T), n)) \to X_{i},\\{}\forall i: \operatorname {Fin}(T), \operatorname {spliceWords}(n, u, v)(i) = \operatorname {if} i<n \operatorname {then} u_{i} \operatorname {else} v_{i}.$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.spliceWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A prefix and a suffix beginning at the cut determine a complete dependent word.

**Definition 1.4 (Actions selected by causal feedback).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, f: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(Y, t)) \to A_{t}, y: (t: \operatorname {Fin}(T)) \to Y_{t},\\{}\forall t: \operatorname {Fin}(T), \operatorname {feedbackActions}(f, y)(t) = f(t)(\operatorname {restrictPrefix}(y, t)).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.feedbackActions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At round t, the feedback action is the strategy value on the output prefix strictly before t.

**Definition 1.5 (Fed-back total mass).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, [\operatorname {FintypeFamily}(Y)], P: ((t: \operatorname {Fin}(T)) \to Y_{t}) \to ((t: \operatorname {Fin}(T)) \to A_{t}) \to \mathbb {R}, f: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(Y, t)) \to A_{t},\\{}\operatorname {feedbackMass}(P, f) = \sum _{y} P(y)(\operatorname {feedbackActions}(f, y)).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.feedbackMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fed-back mass sums the response table over output words after substituting the causal action word.

**Definition 1.6 (Point prefix marginal).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, [\operatorname {FintypeFamily}(Y)], [\operatorname {DecidableEqFamily}(Y)], P: ((t: \operatorname {Fin}(T)) \to Y_{t}) \to ((t: \operatorname {Fin}(T)) \to A_{t}) \to \mathbb {R}, n: \mathbb {N}, x: \operatorname {Prefix}(Y, n), a: (t: \operatorname {Fin}(T)) \to A_{t},\\{}\operatorname {prefixMarginal}(P, n, x, a) = \sum _{y} mathbf_{{\operatorname {restrictPrefix}(y, n)=x}} P(y)(a).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.prefixMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The point prefix marginal sums the response table over complete output words with the specified restriction.

**Definition 1.7 (Event prefix marginal).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, [\operatorname {FintypeFamily}(Y)], [\operatorname {DecidableEqFamily}(Y)], P: ((t: \operatorname {Fin}(T)) \to Y_{t}) \to ((t: \operatorname {Fin}(T)) \to A_{t}) \to \mathbb {R}, n: \mathbb {N}, E: \operatorname {Set}(\operatorname {Prefix}(Y, n)), a: (t: \operatorname {Fin}(T)) \to A_{t},\\{}\operatorname {prefixEventMarginal}(P, n, E, a) = \sum _{y} mathbf_{{\operatorname {restrictPrefix}(y, n) \in E}} P(y)(a).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.prefixEventMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The event prefix marginal sums over complete output words whose restriction belongs to the event.

**Definition 1.8 (Single-cut feedback switch).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, n: \mathbb {N}, u: \operatorname {Prefix}(A, n), v: \operatorname {Suffix}(A, n), w: \operatorname {Suffix}(A, n), E: \operatorname {Set}(\operatorname {Prefix}(Y, n)),\\{}\forall t: \operatorname {Fin}(T), x: \operatorname {Prefix}(Y, t), \operatorname {singleCutSwitch}(n, u, v, w, E)(t)(x) = \operatorname {if} t<n \operatorname {then} u_{t} \operatorname {else} \operatorname {if} \operatorname {restrictPrefix}(x, n) \in E \operatorname {then} v_{t} \operatorname {else} w_{t}.$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.singleCutSwitch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Before the cut the strategy follows u; from the cut onward it selects v or w according to the observed prefix event.

**Theorem 1.9 (Feedback normalization, prefix causality, and sequential kernels).**

$$\forall T: \mathbb {N}, 1 \leq T,\\{}A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type},\\{}[\operatorname {FintypeFamily}(A)], [\operatorname {NonemptyFamily}(A)], [\operatorname {DecidableEqFamily}(A)],\\{}[\operatorname {FintypeFamily}(Y)], [\operatorname {NonemptyFamily}(Y)], [\operatorname {DecidableEqFamily}(Y)],\\{}P: ((t: \operatorname {Fin}(T)) \to Y_{t}) \to ((t: \operatorname {Fin}(T)) \to A_{t}) \to \mathbb {R}, (\forall y: (t: \operatorname {Fin}(T)) \to Y_{t}, a: (t: \operatorname {Fin}(T)) \to A_{t}, 0 \leq P(y)(a)),\\{}(\forall a: (t: \operatorname {Fin}(T)) \to A_{t}, \sum _{y: (t: \operatorname {Fin}(T)) \to Y_{t}} P(y)(a) = 1),\\{}\operatorname {TFAE}([(\forall f: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(Y, t)) \to A_{t}, \operatorname {feedbackMass}(P, f) = 1),\\{}(\forall n: \mathbb {N}, (1 \leq n \land n<T) \Rightarrow \forall u: \operatorname {Prefix}(A, n), v: \operatorname {Suffix}(A, n), w: \operatorname {Suffix}(A, n), E: \operatorname {Set}(\operatorname {Prefix}(Y, n)), \operatorname {feedbackMass}(P, \operatorname {singleCutSwitch}(n, u, v, w, E)) = 1),\\{}(\forall n: \mathbb {N}, n \leq T \Rightarrow \forall x: \operatorname {Prefix}(Y, n), a: (t: \operatorname {Fin}(T)) \to A_{t}, b: (t: \operatorname {Fin}(T)) \to A_{t}, (\forall t: \operatorname {Fin}(T), t<n \Rightarrow a(t) = b(t)) \Rightarrow \operatorname {prefixMarginal}(P, n, x, a) = \operatorname {prefixMarginal}(P, n, x, b)),\\{}(\exists q: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(A, t+1)) \to (\operatorname {Prefix}(Y, t)) \to (Y_{t}) \to \mathbb {R}, (\forall t: \operatorname {Fin}(T), a: \operatorname {Prefix}(A, t+1), h: \operatorname {Prefix}(Y, t), z: Y_{t}, 0 \leq q(t)(a)(h)(z)) \land (\forall t: \operatorname {Fin}(T), a: \operatorname {Prefix}(A, t+1), h: \operatorname {Prefix}(Y, t), \sum _{z: Y_{t}} q(t)(a)(h)(z) = 1) \land (\forall y: (t: \operatorname {Fin}(T)) \to Y_{t}, a: (t: \operatorname {Fin}(T)) \to A_{t}, P(y)(a) = \prod _{t: \operatorname {Fin}(T)} q(t)(\operatorname {restrictPrefix}(a, t+1))(\operatorname {restrictPrefix}(y, t))(y(t))))]).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.feedback_normalization_prefix_causality_sequential_kernels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty dependent round alphabets and a nonnegative normalized response table, the four displayed conditions are equivalent.

A single-cut switch has mass one plus the difference of its two prefix-event marginals. Singleton events therefore force future-action independence of every prefix marginal.

Recursive marginalization yields normalized ratio kernels on positive parent prefixes and one fixed normalized extension on null parents. Conversely, backward summation of normalized kernels makes every causal feedback mass equal to one.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.Prefix`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.feedbackActions`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.feedbackMass`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.feedback_normalization_prefix_causality_sequential_kernels`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.prefixEventMarginal`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.prefixMarginal`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.restrictPrefix`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.singleCutSwitch`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.spliceWords`
