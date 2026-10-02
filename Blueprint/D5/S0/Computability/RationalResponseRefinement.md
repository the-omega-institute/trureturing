# Total Rational Response Refinement

## Abstract

Every raw ternary response executes to a canonical binary word in linear time.

**Theorem 1.1 (Whole-word execution, arithmetic recovery and exact fault output).**

$$\forall w \in \operatorname{List}\left(\mathit{ResponseSymbol}\right),\; \operatorname{Nonempty}\left(\operatorname{TM2OutputsInTime}\left(\mathit{postMachine}, w, \operatorname{some}\left(\operatorname{binaryWord}\left(\operatorname{totalPostOutput}\left(w\right)\right)\right), 3 \cdot \operatorname{length}\left(w\right) + 10\right)\right) \land \left(\left(\forall xs \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall e \in \mathit{Nat},\; w = \operatorname{responseWord}\left(\mathit{xs}, e\right) \Rightarrow \left(3 \mid \operatorname{msbValue}\left(\operatorname{cons}\left(\mathit{true}, \mathit{xs}\right)\right) \Rightarrow \left(\left(0 < e \Rightarrow \operatorname{Odd}\left(\operatorname{msbValue}\left(\operatorname{cons}\left(\mathit{true}, \mathit{xs}\right)\right)\right)\right) \Rightarrow \begin{aligned}e = 0 \Rightarrow \operatorname{msbValue}\left(\operatorname{totalPostOutput}\left(w\right)\right) = 2 \cdot \left\lfloor\frac{\operatorname{msbValue}\left(\operatorname{cons}\left(\mathit{true}, \mathit{xs}\right)\right)}{3}\right\rfloor\\0 < e \Rightarrow \operatorname{msbValue}\left(\operatorname{totalPostOutput}\left(w\right)\right) = \left\lfloor\frac{\left\lfloor\frac{\operatorname{msbValue}\left(\operatorname{cons}\left(\mathit{true}, \mathit{xs}\right)\right)}{3}\right\rfloor}{2^{e - 1}}\right\rfloor\end{aligned}\right)\right)\right) \land \left(\left(\left(\neg \operatorname{suitableResponse}\left(w\right)\right) \Rightarrow \operatorname{totalPostOutput}\left(w\right) = \operatorname{singleton}\left(\mathit{false}\right)\right) \land \left(\operatorname{totalPostOutput}\left(w\right) = \operatorname{singleton}\left(\mathit{false}\right) \lor \left(\exists bs \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{totalPostOutput}\left(w\right) = \operatorname{cons}\left(\mathit{true}, \mathit{bs}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/RationalResponseRefinement.post_word_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word over zero, one and slash, the fixed four-stack, eleven-label machine reaches the exact clean haltList output in at most three times the input length plus ten actual transitions. All scratch is empty and the finite control is restored.

Arithmetic suitability means a positive binary numerator, exactly one slash and a denominator one followed by e zeros. The numerator is divisible by three and is odd when e is positive. Suitable words yield twice p divided by three when e is zero, and otherwise the integer quotient of p divided by three and then by two to the power e minus one. Every unsuitable word produces exactly one zero. Every output is one zero or begins with one.

Suitability is an arithmetic condition, independent of the physical trace. The word 11/1 is suitable and yields two; the physical dummy response 11/100 yields zero. Count correctness requires the separate physical response relation. Zero output does not characterize rejection.

## References

- Truth anchor: `D5/S0/Computability/RationalResponseRefinement.post_word_run`
- Dependency: [D5/S0/Computability/RationalMalformedCleanup](RationalMalformedCleanup.md)
- Dependency: [D5/S0/Computability/RationalPostprocessor](RationalPostprocessor.md)
