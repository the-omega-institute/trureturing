# First Break Order

## Abstract

The first nonzero normal jet order is totalized in WithTop Nat, with infinity recording threads whose every finite jet remains unbroken.

**Theorem 1.1 (First Break Order eq Top iff).**

$$\forall breaks: \mathbb{N} \to Prop,\\{}(firstBreakOrder breaks = top \Leftrightarrow \neg \exists k, IsBreakOrder breaks k).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.first_break_order_eq_top_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absence of every positive finite break is represented exactly by ⊤.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (First Break Order Of Exists).**

$$\forall breaks: \mathbb{N} \to Prop,\\{}(\exists k, IsBreakOrder breaks k) \Rightarrow\\{}(firstBreakOrder breaks = (\mathbb{N}.find h : WithTop \mathbb{N})).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.first_break_order_of_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under an existence witness, the totalized order is the ordinary least natural-number witness.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (First Break Order Spec).**

$$\forall breaks: \mathbb{N} \to Prop,\\{}(\exists k, IsBreakOrder breaks k) \Rightarrow\\{}(IsBreakOrder breaks (\mathbb{N}.find h)).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.first_break_order_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected finite order is a genuine positive break.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (No Break Before First).**

$$\forall breaks: \mathbb{N} \to Prop, j: \mathbb{N},\\{}(\exists k, IsBreakOrder breaks k) \land (j < \mathbb{N}.find h) \Rightarrow\\{}(\neg IsBreakOrder breaks j).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.no_break_before_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No smaller order is an admissible break.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (First Order Break Characterization).**

$$\forall breaks: \mathbb{N} \to Prop,\\{}(breaks 1) \Rightarrow\\{}(firstBreakOrder breaks = (1 : WithTop \mathbb{N})).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.first_order_break_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A first-order break means that order one is the least positive nonzero jet.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Quadratic Break Characterization).**

$$\forall breaks: \mathbb{N} \to Prop,\\{}(\neg breaks 1) \land (breaks 2) \Rightarrow\\{}(firstBreakOrder breaks = (2 : WithTop \mathbb{N})).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.quadratic_break_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If order one vanishes and order two breaks, the first break is quadratic.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.first_break_order_eq_top_iff`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.first_break_order_of_exists`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.first_break_order_spec`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.first_order_break_characterization`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.no_break_before_first`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.quadratic_break_characterization`
