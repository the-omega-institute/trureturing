# Native event integrality and arithmetic resource bounds

## Abstract

Native event integrality and arithmetic resource bounds

**Theorem 1.1 (Integral raw event masses exclude both reference-comparison values).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{Events}\left(T\right), ((\operatorname{IsIntegral}\left(\operatorname{Int}\left(\right), \operatorname{eventMass}\left(T, e\right)\right) \land \operatorname{eventMass}\left(T, e\right) \ne \frac{13-5\sqrt{5}}{22}) \land \operatorname{eventMass}\left(T, e\right) \ne \frac{9\sqrt{5}-19}{22}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolEventArithmetic.original_event_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

For every type L of terminal labels, every finite full-menu native tree T and every Boolean event e on its complete terminal path and terminal sixteen-bit word, the raw mass p=eventMass(T,e) is an algebraic integer over the ordinary integers. All fourteen actual gate addresses, deterministic feedback, complete diagonal zero-one measurements, zero outcomes, stops and expanded inverse calls are included. The input is the same fixed computational root Omega; no arbitrary input vector or external probability weights occur.

The scalars t, beta and zeta of the actual matrices are algebraic integers: rational-angle exponential and cosine integrality give zeta and t, and beta squared equals t. Every number projection and bit flip has integer entries. Finite matrix addition, multiplication and powers therefore preserve entrywise integrality. Induction through the actual tree gives integral branch-matrix entries. Applying the fixed root, multiplying each amplitude by its physical complex conjugate and summing the selected raw events preserve integrality. The real event mass is reflected from its injective complex embedding. No success normalization is performed.

Set q=(13-5 sqrt(5))/22 and w=(9 sqrt(5)-19)/22. In the existing quadratic golden field with generator phi, these are the images of coordinate pairs (9/11,-5/11) and (-14/11,9/11). Their field norms are respectively 1/11 and -1/11. Integrality would force an integer field norm; both rational values fail that condition. Consequently p differs from both q and w. This argument only needs absolute algebraic integrality of p and does not assert that p lies in the quadratic field.

These exclusions apply directly to any original-record event formed by the stop-aware graft in NativeProtocolGraft. They do not establish that the actual chi preparation and its faithful-support Petz pullback have ideal masses q and w. Quadratic integer coordinates, the whole-tree nonphysical-conjugate estimate and the arithmetic factor-eleven bounds are supplied by NativeProtocolEventCoordinates and NativeProtocolEventArithmetic. The actual reference-state realization, original-record comparison and total-variation consumers remain separate obligations. Total Born-mass normalization and the equality of the ninth gate power with its inverse are not used or proved here.

**Theorem 1.2 (Positive-event and factor-eleven arithmetic resource bounds).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{Events}\left(T\right), (((0 < \operatorname{eventMass}\left(T, e\right) \Rightarrow {({(\operatorname{kappa}\left(\right))}^{2*\operatorname{maxCalls}\left(T\right)})}^{-1} \le \operatorname{eventMass}\left(T, e\right)) \land \frac{1}{11*({(\operatorname{kappa}\left(\right))}^{2*\operatorname{maxCalls}\left(T\right)}+\frac{13+5\sqrt{5}}{22})} \le \operatorname{abs}\left(\operatorname{eventMass}\left(T, e\right)-\operatorname{emptyTarget}\left(\right)\right)) \land \frac{1}{11*({(\operatorname{kappa}\left(\right))}^{2*\operatorname{maxCalls}\left(T\right)}+\frac{19+9\sqrt{5}}{22})} \le \operatorname{abs}\left(\operatorname{eventMass}\left(T, e\right)-\operatorname{referenceTarget}\left(\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolEventArithmetic.original_event_resource_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

The bounds apply to every actually computed eventMass of the same original tree T. K denotes kappa to twice Tree.maxCalls(T). Every positive raw event mass is at least one divided by K. For q=emptyTarget=(13-5 sqrt(5))/22 and w=referenceTarget=(9 sqrt(5)-19)/22, the two displayed discrepancy bounds use exactly the source constants and the same K. These are arithmetic bounds for raw masses, without conditioning or a probability-normalization premise.

For x=A+B tau the integer norm is A squared minus A B minus B squared, and the product of its two real evaluations equals that norm. Its nonvanishing is reused from the existing golden-integer norm theorem through the coordinate correspondence (A-B,B). For u=11q=(4,-5) and u=11w=(-5,9), the norms are 11 and minus 11. Direct expansion proves that the norm of 11x-u is divisible by 11. The existing original_event_arithmetic theorem supplies non-equality with q and w. Thus the nonzero norm has absolute value at least 11. The whole-tree conjugate bound and the triangle inequality give the stated denominators.

The arithmetic inequalities do not identify q or w as the ideal probabilities of the actual chi/Petz experiments. Their empty-prefix and five-call source-history realization, preservation of original records and failure zeros, graft resource identities and total-variation comparison still require the specified original-object consumers. The cut determinant and spectral clauses of V88 theorem 24.1 remain outside this event result.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolEventArithmetic.original_event_arithmetic`
- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolEventArithmetic.original_event_resource_bounds`
- Dependency: [D5/S3/Quantum/Dynamics/NativeProtocolEventCoordinates](NativeProtocolEventCoordinates.md)
