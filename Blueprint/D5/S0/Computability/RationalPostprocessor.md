# Ordinary Rational Response Processing

## Abstract

An ordinary dyadic rational word is decoded by a fixed finite stack machine.

**Theorem 1.1 (Clean native run and numerical decoding).**

$$\forall xs \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall e \in \mathit{Nat},\; \left(3 \mid \operatorname{msbValue}\left(\operatorname{cons}\left(\mathit{true}, \mathit{xs}\right)\right) \land \left(0 < e \Rightarrow \operatorname{Odd}\left(\operatorname{msbValue}\left(\operatorname{cons}\left(\mathit{true}, \mathit{xs}\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{TM2OutputsInTime}\left(\mathit{postMachine}, \operatorname{responseWord}\left(\mathit{xs}, e\right), \operatorname{some}\left(\operatorname{binaryWord}\left(\operatorname{responseOutput}\left(\mathit{xs}, e\right)\right)\right), 4 \cdot \operatorname{length}\left(\operatorname{responseWord}\left(\mathit{xs}, e\right)\right) + 4\right)\right) \land \begin{aligned}e = 0 \Rightarrow \operatorname{msbValue}\left(\operatorname{responseOutput}\left(\mathit{xs}, e\right)\right) = 2 \cdot \left\lfloor\frac{\operatorname{msbValue}\left(\operatorname{cons}\left(\mathit{true}, \mathit{xs}\right)\right)}{3}\right\rfloor\\0 < e \Rightarrow \operatorname{msbValue}\left(\operatorname{responseOutput}\left(\mathit{xs}, e\right)\right) = \left\lfloor\frac{\left\lfloor\frac{\operatorname{msbValue}\left(\operatorname{cons}\left(\mathit{true}, \mathit{xs}\right)\right)}{3}\right\rfloor}{2^{e - 1}}\right\rfloor\end{aligned}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/RationalPostprocessor.dyadic_response_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator is a positive binary word beginning with one. The denominator is one followed by e zeros, with a slash between the two words. The numerator p is divisible by three and is odd when e is positive. The fixed machine has four stacks, eleven labels, twenty-four control states and the alphabet zero, one, slash.

The actual step relation starts at the library's clean input configuration and reaches its exact clean halt configuration. The input, quotient and shift stacks are empty and the finite state is reset. The run uses at most four times the complete response length plus four transitions.

The emitted canonical binary word denotes twice p divided by three when e is zero. Otherwise it denotes the integer quotient of p divided by three and then by two to the power e minus one. Division uses three remainder states; each denominator shift is a physical stack mark. Zero is represented by one zero digit.

The theorem concerns the stated positive dyadic inputs. Universal malformed-input correctness and the relation to a physical oracle are separate obligations.

## References

- Truth anchor: `D5/S0/Computability/RationalPostprocessor.dyadic_response_run`
