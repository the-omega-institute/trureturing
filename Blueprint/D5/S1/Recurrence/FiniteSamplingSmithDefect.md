# Finite Fibonacci Sampling Smith Defect

## Abstract

Strictly increasing Fibonacci samples have an integral rectangular normal form and an exact modular kernel defect.

**Theorem 1.1 (Fibonacci sampling has a gcd controlled Smith defect).**

$$\forall m\in \mathbb{N},\ \forall t: \operatorname{Fin}\left(m\right) \to \mathbb{N},\ (2 \leq m \land \operatorname{StrictMono}\left(t\right) \Rightarrow let i0 = \operatorname{zero}\left(\operatorname{Fin}\left(m\right)\right), let g = \operatorname{gcd}\left(\operatorname{erase}\left(\operatorname{univ}\left(\operatorname{Fin}\left(m\right)\right), i0\right), fun i \Rightarrow \operatorname{t}\left(i\right) - \operatorname{t}\left(i0\right)\right), let H : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(2\right), \mathbb{Z}\right) = fun i \Rightarrow \operatorname{row}\left(\operatorname{IntCast}\left(\operatorname{fib}\left(\operatorname{t}\left(i\right)\right)\right), \operatorname{IntCast}\left(\operatorname{fib}\left(\operatorname{t}\left(i\right) + 1\right)\right)\right), let D : \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(2\right), \mathbb{Z}\right) = fun i, j \Rightarrow \operatorname{if}\left((\operatorname{val}\left(i\right) = 0) \land (j = 0), 1, \operatorname{if}\left((\operatorname{val}\left(i\right) = 1) \land (j = 1), \operatorname{IntCast}\left(\operatorname{fib}\left(g\right)\right), 0\right)\right), in 0 < \operatorname{fib}\left(g\right) \land \exists U: \operatorname{Units}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{Z}\right)\right), \exists V: \operatorname{Units}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{Z}\right)\right),\ (\operatorname{mul}\left(\operatorname{val}\left(U\right), H, \operatorname{val}\left(V\right)\right) = D) \land (\forall N\in \mathbb{N}, (0 < N \Rightarrow ((\operatorname{card}\left(\operatorname{ker}\left(\operatorname{mulVecLin}\left(\operatorname{map}\left(H, \operatorname{castRingHom}\left(\operatorname{ZMod}\left(N\right)\right)\right)\right)\right)\right) = \operatorname{gcd}\left(N, \operatorname{fib}\left(g\right)\right)) \land (\operatorname{Injective}\left(\operatorname{mulVec}\left(\operatorname{map}\left(H, \operatorname{castRingHom}\left(\operatorname{ZMod}\left(N\right)\right)\right)\right)\right) \iff \operatorname{gcd}\left(N, \operatorname{fib}\left(g\right)\right) = 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FiniteSamplingSmithDefect.finite_sampling_smith_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be at least two and let t : Fin(m) -> N be strictly increasing. The first sample index is i0 = 0, and g is the finite gcd of all noninitial differences t(i) - t(i0). The actual row at i is (Nat.fib(t(i)), Nat.fib(t(i)+1)) over Z; no abstract replacement matrix is used.

The theorem supplies units U and V over the displayed rectangular integer matrix spaces. Their product with H is the displayed D: a 1 at (0,0), Nat.fib(g) at (1,1), and zero elsewhere. Nat.fib(g) is positive as the second factor, including the smallest admissible time configuration.

For every positive natural modulus N, including N = 1, reduce the same actual matrix by Int.castRingHom into ZMod(N). Its mulVecLin kernel has cardinality gcd(N, Nat.fib(g)), and its mulVec is injective exactly when that gcd is one. The proof clears the first row, applies the finite Bezout column automorphism, and transports the scalar kernel through the unit matrices.

The statement records the integral normal form and the modular kernel and injectivity consequences only; it makes no claim about a cokernel or free-part decomposition.

## References

- Truth anchor: `D5/S1/Recurrence/FiniteSamplingSmithDefect.finite_sampling_smith_defect`
- Dependency: [D5/S1/Recurrence/FibVajda](FibVajda.md)
- Dependency: [D5/S1/Recurrence/FiniteColumnGcdNormalization](FiniteColumnGcdNormalization.md)
- Dependency: [D5/S1/Recurrence/LucasCompanion](LucasCompanion.md)
