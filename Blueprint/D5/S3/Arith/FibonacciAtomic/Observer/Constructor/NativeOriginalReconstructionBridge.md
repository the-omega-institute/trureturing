# Original coordinates of a passing native image mode

## Abstract

Exact epoch transport, canonical original rigidity and executable original prefixes.

An EpochInput I has n original natural parameters, k affine atomic indices, m state names, an optional equation at each name, a head power a(i), the original Presburger guard, and every original actual-image filter. A defined equation is rho to power a(i) of X(i) equal to its stored right side. Expressions contain arbitrary finite grounds, finite parameter atoms with fixed offsets, the explicit Omega token, decorated state occurrences and ordered pairs. A Potential s is a natural tuple satisfying a(i) at most s(i) and s(j) at most b+s(i)-a(i) at each occurrence rho to power b of X(j). These are the natural form of NIS.11 supplied by Theorem 3.3. No semantic identity or inverse is a field of the input.

imageValues(s,v)(i) is rho to power s(i) of v(i). transport(s,t,E) distributes a shift t through finite grounds, token offsets and pairs, replacing an occurrence rho to power b of X(j) by rho to power b+t-s(j) of Y(j). ShiftLegal checks every exponent before its use. commonShift(s) is the maximum of zero and all s(i), computed by a finite fold; it works for every reconstruction and additional filter and is independent of the requested depth and parameters.

**Theorem 1.1 (The entire decorated solution relation is transported in both directions).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall I: \operatorname{EpochInput}\left(n, k, m\right), (\forall s: \operatorname{Fin}\left(m\right) \to Nat, (\forall valid: \operatorname{Potential}\left(I, s\right), (\forall p: \operatorname{Fin}\left(n\right) \to Nat, (\forall w: \operatorname{Fin}\left(m\right) \to CompletionTree, (((\operatorname{Legal}\left(\operatorname{functionalInput}\left(I, s\right), p\right)) \land ((\operatorname{SourceSatisfies}\left(\operatorname{functionalInput}\left(I, s\right), p, w\right)) \land (\operatorname{SourcePasses}\left(\operatorname{functionalInput}\left(I, s\right), p, w\right)))) \iff (\exists v: \operatorname{Fin}\left(m\right) \to CompletionTree, (((\operatorname{OriginalAdmissible}\left(I, p, v\right)) \land (\operatorname{imageValues}\left(s, v\right) = w)) \land (\forall u: \operatorname{Fin}\left(m\right) \to CompletionTree, (((\operatorname{OriginalAdmissible}\left(I, p, u\right)) \land (\operatorname{imageValues}\left(s, u\right) = w)) \implies (u = v)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge.epoch_solution_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

functionalInput applies the head shift s(i)-a(i) to each defined equation. It retains a state-image filter Y(i) in L at threshold s(i) for every name, including undefined states. An original filter C in L at threshold r becomes transport(s,t,C) in L at threshold r+t with t=commonShift(s). Every occurrence and repetition remains in the list. The affine indices and original legal domain are unchanged. OriginalAdmissible means the original legal domain, every decorated equation, and every original image filter, jointly.

Structural induction proves the literal evaluation identity for transport on every legal shift. Native injectivity recovers the original decorated equations from the shifted equations. The state-image filters provide every actual preimage, and injectivity makes their joint tuple unique. Applying injectivity once more proves both directions for every additional shifted filter. The result concerns entire completed assignments; arbitrary infinite and non-rational values are included.

**Theorem 1.2 (Every original reconstruction has its actual common-shift image).**

$$\forall k: Nat, (\forall m: Nat, (\forall s: \operatorname{Fin}\left(m\right) \to Nat, (\forall p: \operatorname{Fin}\left(k\right) \to Nat, (\forall v: \operatorname{Fin}\left(m\right) \to CompletionTree, (\forall E: \operatorname{Expression}\left(k, m\right), ((\operatorname{evaluate}\left(p, \operatorname{imageValues}\left(s, v\right), \operatorname{transport}\left(s, \operatorname{commonShift}\left(s\right), E\right)\right) = \operatorname{rhoPower}\left(\operatorname{commonShift}\left(s\right), \operatorname{evaluate}\left(p, v, E\right)\right)) \land (\operatorname{NativeImage}\left(\operatorname{commonShift}\left(s\right), \operatorname{evaluate}\left(p, \operatorname{imageValues}\left(s, v\right), \operatorname{transport}\left(s, \operatorname{commonShift}\left(s\right), E\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge.reconstruction_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite native expression E and every original assignment v, the distributed expression is exactly rho to power commonShift(s) of the original evaluation. Its actual-image membership is proved by that original evaluation as witness. This includes zero states, zero shift, mixed pairs, repeated names, arbitrary grounds and the explicit Omega. The expression identity and image membership are conclusions of the syntax induction, rather than assumptions about a reconstruction context.

**Theorem 1.3 (The finite guarded evaluator denotes the actual original image).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall r: Nat, (\forall I: \operatorname{EpochInput}\left(n, k, m\right), (\forall s: \operatorname{Fin}\left(m\right) \to Nat, (\forall valid: \operatorname{Potential}\left(I, s\right), (\forall mode: \operatorname{EffectiveMode}\left(\operatorname{functionalInput}\left(I, s\right)\right), (\forall R: \operatorname{Fin}\left(r\right) \to \operatorname{Expression}\left(k, m\right), (\forall p: \operatorname{Fin}\left(n\right) \to Nat, (\forall passing: \operatorname{holds}\left(\operatorname{originalImageGuard}\left(\operatorname{functionalInput}\left(I, s\right), mode\right), \operatorname{environment}\left(p\right)\right), (\forall i: \operatorname{Fin}\left(r\right), (\operatorname{value}\left(\operatorname{tokenKind}\left(k\right), \operatorname{tokenRank}\left(\operatorname{ranks}\left(\operatorname{base}\left(I\right), p\right)\right), \operatorname{canonicalSolution}\left(\operatorname{canonicalSystem}\left(I, s, mode\right), \operatorname{tokenKind}\left(k\right), \operatorname{tokenRank}\left(\operatorname{ranks}\left(\operatorname{base}\left(I\right), p\right)\right)\right), \operatorname{reconstructionImages}\left(I, s, R, i\right)\right) = \operatorname{rhoPower}\left(\operatorname{commonShift}\left(s\right), \operatorname{evaluate}\left(\operatorname{ranks}\left(\operatorname{base}\left(I\right), p\right), \operatorname{canonicalOriginal}\left(I, s, valid, mode, p, passing\right), \operatorname{R}\left(i\right)\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge.canonical_reconstruction_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

presentation is the existing executable root-link normalization of functionalInput, retaining both reconstruction and projection maps. reconstructionImages substitutes its retained reconstruction into the distributed common-shift expression. canonicalSystem fixes each exceptional finite normalized free atom by a ground equation and leaves live free names undefined. Its existing leaf-limit canonicalSolution therefore assigns Omega to live names. Guarded uniqueness identifies this solution with the saturation canonical extension.

Passing is the actual computed originalImageGuard of functionalInput at the same original parameter tuple. The existing exact image-guard theorem supplies legality and every retained filter. The epoch correspondence then supplies canonicalOriginal as the unique original preimage of effectiveCanonical. The displayed equality connects the symbolic finite-forcing and finite prefix APIs to this actual original reconstruction. No rational presentation is required.

**Theorem 1.4 (Decidable canonical finiteness, same-parameter rigidity and effective original prefixes).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall r: Nat, (\forall I: \operatorname{EpochInput}\left(n, k, m\right), (\forall s: \operatorname{Fin}\left(m\right) \to Nat, (\forall valid: \operatorname{Potential}\left(I, s\right), (\forall mode: \operatorname{EffectiveMode}\left(\operatorname{functionalInput}\left(I, s\right)\right), (\forall R: \operatorname{Fin}\left(r\right) \to \operatorname{Expression}\left(k, m\right), (\forall p: \operatorname{Fin}\left(n\right) \to Nat, (\forall passing: \operatorname{holds}\left(\operatorname{originalImageGuard}\left(\operatorname{functionalInput}\left(I, s\right), mode\right), \operatorname{environment}\left(p\right)\right), ((\operatorname{OriginalAdmissible}\left(I, p, \operatorname{canonicalOriginal}\left(I, s, valid, mode, p, passing\right)\right)) \land (\forall i: \operatorname{Fin}\left(r\right), (((\operatorname{IsFinite}\left(\operatorname{evaluate}\left(\operatorname{ranks}\left(\operatorname{base}\left(I\right), p\right), \operatorname{canonicalOriginal}\left(I, s, valid, mode, p, passing\right), \operatorname{R}\left(i\right)\right)\right)) \iff (i \in \operatorname{finiteReconstructions}\left(I, s, mode, R\right))) \land (((i \in \operatorname{finiteReconstructions}\left(I, s, mode, R\right)) \implies (\exists g: Source, ((\operatorname{evaluate}\left(\operatorname{ranks}\left(\operatorname{base}\left(I\right), p\right), \operatorname{canonicalOriginal}\left(I, s, valid, mode, p, passing\right), \operatorname{R}\left(i\right)\right) = \operatorname{embed}\left(g\right)) \land (\forall v: \operatorname{Fin}\left(m\right) \to CompletionTree, ((\operatorname{OriginalAdmissible}\left(I, p, v\right)) \implies ((\operatorname{EffectiveInMode}\left(\operatorname{functionalInput}\left(I, s\right), mode, p, \operatorname{imageValues}\left(s, v\right)\right)) \implies (\operatorname{evaluate}\left(\operatorname{ranks}\left(\operatorname{base}\left(I\right), p\right), v, \operatorname{R}\left(i\right)\right) = \operatorname{embed}\left(g\right)))))))) \land (\forall h: Nat, (\operatorname{originalPrefixProgram}\left(I, s, mode, p, R, h, i\right) = \operatorname{cutoff}\left(h+1, \operatorname{evaluate}\left(\operatorname{ranks}\left(\operatorname{base}\left(I\right), p\right), \operatorname{canonicalOriginal}\left(I, s, valid, mode, p, passing\right), \operatorname{R}\left(i\right)\right)\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge.original_classification_rigidity_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

finiteReconstructions is the existing finite symbolic pass, applied to canonicalSystem and reconstructionImages. It is executable and independent of p. Native powers preserve and reflect finiteness, so membership decides exactly the finiteness of each canonical original reconstruction. For each finite member the theorem produces one finite Source g equal to that reconstruction and to the reconstruction in every original admissible solution whose shifted assignment belongs to the same projected normalized mode. All such solutions use the same original p.

Only exceptional finite free values are fixed in canonicalSystem. Every original alternative in that mode satisfies these equations; live free states remain unrestricted. Existing symbolic_finite_forcing therefore fixes the common-shift image, and injectivity fixes its original value. This clause does not say that an alternative value of a canonically infinite coordinate is infinite. Symbolic finite inversion with an original-parameter Presburger partition is supplied by NativeFiniteNormalInversion.original_symbolic_finite_value.

originalPrefixProgram runs the existing finite guarded image prefix program at inclusive depth H(t)+h and decodes its result at output cutoff h+1. Pattern d observes addresses of length strictly less than d; hence the image cutoff is H(t)+h+1=H(t)+(h+1). The existing decoder proves equality with the original cutoff for every supplied h and p, including h=0 and t=0. This constructs prefixes offline and asserts no physical inverse port, query cost or uniform runtime bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge.canonical_reconstruction_image`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge.epoch_solution_correspondence`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge.original_classification_rigidity_prefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge.reconstruction_transport`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveImageGuard](NativeEffectiveImageGuard.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalCoordinatePrefix](NativeOriginalCoordinatePrefix.md)
