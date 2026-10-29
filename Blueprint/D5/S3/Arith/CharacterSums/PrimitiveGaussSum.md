# Primitive Gauss sum nonvanishing

## Abstract

Primitive Dirichlet Gauss sums are nonzero by finite Fourier injectivity.

**Theorem 1.1 (Nonvanishing at every nonzero modulus).**

$$\forall N:Nat, [\operatorname{NeZero}\left(N\right)] \forall chi:\operatorname{DirichletCharacter}\left(C, N\right), \operatorname{IsPrimitive}\left(chi\right) \implies \operatorname{gaussSum}\left(chi, \operatorname{stdAddChar}\left(N\right)\right) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PrimitiveGaussSum.primitive_gaussSum_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural modulus N with NeZero N and every primitive complex Dirichlet character chi modulo N, the standard additive-character Gauss sum is nonzero. The statement includes N=1 and composite moduli.

If the Gauss sum vanished, Mathlib's primitive Fourier-transform formula would force the discrete Fourier transform of chi to vanish. Injectivity of ZMod.dft would then make chi identically zero, contradicting its value one at one. This is a supporting API lemma using the classical finite Fourier theory already in Mathlib, with no claim of new mathematical novelty.

The intended consumer is nonzero normalization of the modular Dirichlet translation twist; its q-expansion coefficient law remains future work. The Reg candidate is kernel checked but sourceSelection is absent and declared_validated enrollment is not claimed. The remaining source-audit obligation is tracked at https://github.com/the-omega-institute/trureturing/issues/23614.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PrimitiveGaussSum.primitive_gaussSum_ne_zero`
