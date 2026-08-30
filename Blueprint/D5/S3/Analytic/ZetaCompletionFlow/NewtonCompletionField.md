# Newton Completion Field

## Abstract

The Newton completion vector is scale invariant, detects roots under a regular derivative, and exactly completes affine zero models in one step.

**Theorem 1.1 (Newton Completion Vector eq Zero iff).**

$$\forall K: Type, F: K \to K, dF: K \to K, s: K, [\operatorname{Field}\left(K\right)],\\{}(dF s \neq 0) \Rightarrow\\{}(newtonCompletionVector F dF s = 0 \Leftrightarrow F s = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.newton_completion_vector_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a regular point, the Newton vector vanishes exactly at a root.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Newton Completion Vector Scale Invariant).**

$$\forall K: Type, c: K, F: K \to K, dF: K \to K, s: K, [\operatorname{Field}\left(K\right)],\\{}(c \neq 0) \land (dF s \neq 0) \Rightarrow\\{}(newtonCompletionVector (\lambda z \mapsto c \times F z) (\lambda z \mapsto c \times dF z) s = newtonCompletionVector F dF s).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.newton_completion_vector_scale_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Common nonzero rescaling of a function and its derivative field leaves the Newton vector unchanged.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Affine Newton Completion Vector).**

$$\forall K: Type, a: K, root: K, s: K, [\operatorname{Field}\left(K\right)],\\{}(a \neq 0) \Rightarrow\\{}(newtonCompletionVector (\lambda z \mapsto a \times (z - root)) (\lambda value \mapsto a) s = root - s).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.affine_newton_completion_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Newton vector of an affine simple-zero model points exactly from the current point to its root.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Affine Newton Completion Step).**

$$\forall K: Type, a: K, root: K, s: K, [\operatorname{Field}\left(K\right)],\\{}(a \neq 0) \Rightarrow\\{}(newtonCompletionStep (\lambda z \mapsto a \times (z - root)) (\lambda value \mapsto a) s = root).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.affine_newton_completion_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consequently, an affine simple-zero model completes in one Newton step.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Root Fixed By Newton Completion).**

$$\forall K: Type, F: K \to K, dF: K \to K, root: K, [\operatorname{Field}\left(K\right)],\\{}(F root = 0) \Rightarrow\\{}(newtonCompletionStep F dF root = root).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.root_fixed_by_newton_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A genuine regular root is fixed by the Newton completion step.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.affine_newton_completion_step`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.affine_newton_completion_vector`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.newton_completion_vector_eq_zero_iff`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.newton_completion_vector_scale_invariant`
- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.root_fixed_by_newton_completion`
