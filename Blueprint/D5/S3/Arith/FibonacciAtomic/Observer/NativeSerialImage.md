# NativeSerialImage

## Abstract

NativeSerialImage

**Theorem 1.1 (Prefix-free terminal reply words).**

$$\forall C, O: Type, (\forall delta: C \to \operatorname{Op}\left(C, O\right), (\forall c: C, (\forall N: Nat, (\forall u, v: Source, (\forall t, s: Trace, (\forall o, p: O, ((\operatorname{Run}\left(delta, c, N, u, t, o\right)) \implies ((\operatorname{Run}\left(delta, c, N, v, s, p\right)) \implies ((\operatorname{IsPrefix}\left(\operatorname{answers}\left(t\right), \operatorname{answers}\left(s\right)\right)) \implies ((t = s) \land (o = p)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage.terminal_prefix_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A terminal reply word cannot be a proper prefix of another terminal word for the same source-free control and initial epoch. A prefix relation forces equality of the entire physical action traces and complete outputs, including every silent step and update.

**Definition 1.2 (Fixed-length reply padding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage.pad`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage.pad` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pad a bounded terminal reply word with absent symbols to length K. This is a proof construction on words, not a physical register operation. Prefix-freeness makes the padding injective on actual terminal words.

**Theorem 1.3 (Sharp whole-output image bound).**

$$\forall C, O: Type, (\forall delta: C \to \operatorname{Op}\left(C, O\right), (\forall c: C, (\forall N, K: Nat, (\forall U: \operatorname{Set}\left(Source\right), ((\operatorname{Nonempty}\left(U\right)) \implies (\forall F: Source \to O, ((\forall u: Source, ((u \in U) \implies (\exists t: Trace, ((\operatorname{Run}\left(delta, c, N, \operatorname{iterate}\left(substitution, N, u\right), t, \operatorname{F}\left(u\right)\right)) \land (\operatorname{length}\left(\operatorname{answers}\left(t\right)\right) \leq K))))) \implies (\exists labels: \operatorname{Finset}\left(O\right), ((\operatorname{card}\left(labels\right) \leq \operatorname{power}\left(4, K\right)) \land (\forall u: Source, ((u \in U) \implies (\operatorname{F}\left(u\right) \in labels))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage.bounded_serial_output_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terminal words inject into the length-K four-valued words. The entire terminal output image therefore lies in a finite set of cardinality at most four to the power K. K equal to zero is included; repeated reads are counted separately. No finite source or output universe and no uniform runtime hypothesis is used.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage.bounded_serial_output_image`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage.pad`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialImage.terminal_prefix_free`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine](NativeSerialMachine.md)
