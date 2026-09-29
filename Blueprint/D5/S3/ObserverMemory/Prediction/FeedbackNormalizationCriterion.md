# Feedback Normalization Criterion

## Abstract

Finite feedback normalization is equivalent to prefix causality and sequential kernel factorization.

**Definition 1.1 (Dependent output and action prefixes).**

$$\forall T: \mathbb {N}, X: (\operatorname {Fin}(T)) \to \operatorname {Type}, n: \mathbb {N},\\{}\operatorname {Prefix}(X, n) = (i: \{i: \operatorname {Fin}(T) // i.val < n\}) \to X(i.1).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.Prefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A prefix of length n is a dependent word on precisely the rounds whose indices are below n.

**Definition 1.2 (Restriction to an initial prefix).**

$$\forall T: \mathbb {N}, X: (\operatorname {Fin}(T)) \to \operatorname {Type}, x: (t: \operatorname {Fin}(T)) \to X(t), n: \mathbb {N}, i: \{i: \operatorname {Fin}(T) // i.val < n\},\\{}\operatorname {restrictPrefix}(x, n)(i) = x(i.1).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.restrictPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complete dependent word restricts to a prefix by evaluation at the underlying round index.

**Definition 1.3 (Splicing at a round cut).**

$$\forall T: \mathbb {N}, X: (\operatorname {Fin}(T)) \to \operatorname {Type}, n: \mathbb {N}, u: \operatorname {Prefix}(X, n), v: (i: \{i: \operatorname {Fin}(T) // n \leq i.val\}) \to X(i.1),\\{}\forall i: \operatorname {Fin}(T), \operatorname {spliceWords}(n, u, v)(i) = \text{if} i.val < n \text{then} u(\langle i, i.val < n\rangle) \text{else} v(\langle i, n \leq i.val\rangle).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.spliceWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A prefix and a suffix beginning at the cut determine a complete dependent word.

**Definition 1.4 (Actions selected by causal feedback).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, f: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(Y, t.val)) \to A(t), y: (t: \operatorname {Fin}(T)) \to Y(t),\\{}\forall t: \operatorname {Fin}(T), \operatorname {feedbackActions}(f, y)(t) = f(t)(\operatorname {restrictPrefix}(y, t.val)).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.feedbackActions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At round t, the feedback action is the strategy value on the output prefix strictly before t.

**Definition 1.5 (Fed-back total mass).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, [\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(Y(t))], P: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, f: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(Y, t.val)) \to A(t),\\{}\operatorname {feedbackMass}(P, f) = \sum _{y: (t: \operatorname {Fin}(T)) \to Y(t)} P(y)(\operatorname {feedbackActions}(f, y)).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.feedbackMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fed-back mass sums the response table over output words after substituting the causal action word.

**Definition 1.6 (Point prefix marginal).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, [\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(Y(t))], [\forall t: \operatorname {Fin}(T), \operatorname {DecidableEq}(Y(t))], P: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, n: \mathbb {N}, x: \operatorname {Prefix}(Y, n), a: (t: \operatorname {Fin}(T)) \to A(t),\\{}\operatorname {prefixMarginal}(P, n, x, a) = \sum _{y: (t: \operatorname {Fin}(T)) \to Y(t)} \text{if} \operatorname {restrictPrefix}(y, n) = x \text{then} P(y)(a) \text{else} 0.$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.prefixMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The point prefix marginal sums the response table over complete output words with the specified restriction.

**Definition 1.7 (Event prefix marginal).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, [\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(Y(t))], [\forall t: \operatorname {Fin}(T), \operatorname {DecidableEq}(Y(t))], P: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, n: \mathbb {N}, E: \operatorname {Set}(\operatorname {Prefix}(Y, n)), a: (t: \operatorname {Fin}(T)) \to A(t),\\{}\operatorname {prefixEventMarginal}(P, n, E, a) = \sum _{y: (t: \operatorname {Fin}(T)) \to Y(t)} \text{if} \operatorname {restrictPrefix}(y, n) \in E \text{then} P(y)(a) \text{else} 0.$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.prefixEventMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The event prefix marginal sums over complete output words whose restriction belongs to the event.

**Definition 1.8 (Single-cut feedback switch).**

$$\forall T: \mathbb {N}, A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type}, n: \mathbb {N}, u: \operatorname {Prefix}(A, n), v: (i: \{i: \operatorname {Fin}(T) // n \leq i.val\}) \to A(i.1), w: (i: \{i: \operatorname {Fin}(T) // n \leq i.val\}) \to A(i.1), E: \operatorname {Set}(\operatorname {Prefix}(Y, n)),\\{}\forall t: \operatorname {Fin}(T), history: \operatorname {Prefix}(Y, t.val), \operatorname {singleCutSwitch}(n, u, v, w, E)(t)(history) = \text{if} t.val < n \text{then} u(\langle t, t.val < n\rangle) \text{else} \text{let} x: \operatorname {Prefix}(Y, n) := \lambda i \mapsto history(\langle i.1, i.1.val < t.val\rangle); \text{if} x \in E \text{then} v(\langle t, n \leq t.val\rangle) \text{else} w(\langle t, n \leq t.val\rangle).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.singleCutSwitch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Before the cut the strategy follows u; from the cut onward it selects v or w according to the observed prefix event.

**Theorem 1.9 (Feedback normalization, prefix causality, and sequential kernels).**

$$\forall T: \mathbb {N}, 1 \leq T,\\{}A: (\operatorname {Fin}(T)) \to \operatorname {Type}, Y: (\operatorname {Fin}(T)) \to \operatorname {Type},\\{}[\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(A(t))], [\forall t: \operatorname {Fin}(T), \operatorname {Nonempty}(A(t))], [\forall t: \operatorname {Fin}(T), \operatorname {DecidableEq}(A(t))],\\{}[\forall t: \operatorname {Fin}(T), \operatorname {Fintype}(Y(t))], [\forall t: \operatorname {Fin}(T), \operatorname {Nonempty}(Y(t))], [\forall t: \operatorname {Fin}(T), \operatorname {DecidableEq}(Y(t))],\\{}P: ((t: \operatorname {Fin}(T)) \to Y(t)) \to ((t: \operatorname {Fin}(T)) \to A(t)) \to \mathbb {R}, (\forall y: (t: \operatorname {Fin}(T)) \to Y(t), a: (t: \operatorname {Fin}(T)) \to A(t), 0 \leq P(y)(a)),\\{}(\forall a: (t: \operatorname {Fin}(T)) \to A(t), \sum _{y: (t: \operatorname {Fin}(T)) \to Y(t)} P(y)(a) = 1),\\{}List.TFAE([(\forall f: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(Y, t.val)) \to A(t), \operatorname {feedbackMass}(P, f) = 1),\\{}(\forall n: \mathbb {N}, (1 \leq n) \Rightarrow ((n < T) \Rightarrow (\forall u: \operatorname {Prefix}(A, n), v: (i: \{i: \operatorname {Fin}(T) // n \leq i.val\}) \to A(i.1), w: (i: \{i: \operatorname {Fin}(T) // n \leq i.val\}) \to A(i.1), E: \operatorname {Set}(\operatorname {Prefix}(Y, n)), \operatorname {feedbackMass}(P, \operatorname {singleCutSwitch}(n, u, v, w, E)) = 1))),\\{}(\forall n: \mathbb {N}, (n \leq T) \Rightarrow (\forall x: \operatorname {Prefix}(Y, n), a: (t: \operatorname {Fin}(T)) \to A(t), b: (t: \operatorname {Fin}(T)) \to A(t), (\forall i: \operatorname {Fin}(T), (i.val < n) \Rightarrow (a(i) = b(i))) \Rightarrow (\operatorname {prefixMarginal}(P, n, x, a) = \operatorname {prefixMarginal}(P, n, x, b)))),\\{}(\exists q: (t: \operatorname {Fin}(T)) \to (\operatorname {Prefix}(A, t.val + 1)) \to (\operatorname {Prefix}(Y, t.val)) \to (Y(t)) \to \mathbb {R}, (\forall t: \operatorname {Fin}(T), a: \operatorname {Prefix}(A, t.val + 1), h: \operatorname {Prefix}(Y, t.val), z: Y(t), 0 \leq q(t)(a)(h)(z)) \land (\forall t: \operatorname {Fin}(T), a: \operatorname {Prefix}(A, t.val + 1), h: \operatorname {Prefix}(Y, t.val), \sum _{z: Y(t)} q(t)(a)(h)(z) = 1) \land (\forall y: (t: \operatorname {Fin}(T)) \to Y(t), a: (t: \operatorname {Fin}(T)) \to A(t), P(y)(a) = \prod _{t: \operatorname {Fin}(T)} q(t)(\operatorname {restrictPrefix}(a, t.val + 1))(\operatorname {restrictPrefix}(y, t.val))(y(t))))]).$$

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
