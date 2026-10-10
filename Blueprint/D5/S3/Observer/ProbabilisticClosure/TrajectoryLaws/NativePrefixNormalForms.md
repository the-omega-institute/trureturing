# Ordered retries and partial payload words

## Abstract

Unique independently concatenated forms for all paid native prefix cuts.

A PrefixForm contains an arbitrary ordered list u of rejected equal pairs. retryWord replaces each bit x in u by [x,x]. The tail is seed-ready, one pending first seed letter, or an acquired seed rho followed by PayloadForm with four remaining slots. The accepted seed word is [0,1] for rho=0 and [1,0] for rho=1. These concatenations define render independently of native execution.

With positive remaining slots, PayloadForm is an active cut after j beta-alpha returns, with phase p or one pending beta, or a completed pWord(j,b) followed by a form with one fewer slot. With no slots it is pending or delivered. Pending renders empty; delivered renders exactly Stop of the last completed bit. Every j is a natural number. Thus empty and partial seed histories, every payload cut, both final colors and the original delivery boundary are represented.

**Theorem 1.1 (The complete concatenation is injective).**

$$\operatorname{Injective}(render)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePrefixNormalForms.prefix_form_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

parseSeed scans actual equal-pair retry order and the first unequal pair. parsePayload independently decodes concatenated segment words and active suffixes. Induction proves that parsing each rendered form returns that same form, including all natural return counts and terminal cuts. Therefore equal rendered operation words have equal forms. This decoder does not define native legality or store any archive in native state.

**Theorem 1.2 (Right extension preserves concatenation).**

$$\forall nf:PrefixForm, (\forall ng:PrefixForm, (\forall op:Operation, ((\operatorname{appendForm}(nf,op)=\operatorname{some}(ng))\Rightarrow(\operatorname{render}(ng)=\operatorname{append}(\operatorname{render}(nf),\operatorname{singleton}(op))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePrefixNormalForms.render_append_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

appendForm extends the proof form by one original Read or Stop. A same-letter second seed Read appends that rejection to u; an unequal second Read acquires its seed. Payload beta-alpha adds a return, while a completing letter adds a segment and its fresh successor. Only a pending matching Stop extends to delivered. Whenever extension succeeds with ng, render(ng) is render(nf) followed by precisely op. Induction follows the independent payload grammar.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePrefixNormalForms.prefix_form_unique`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePrefixNormalForms.render_append_form`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState](NativeAcquiredPrefixState.md)
