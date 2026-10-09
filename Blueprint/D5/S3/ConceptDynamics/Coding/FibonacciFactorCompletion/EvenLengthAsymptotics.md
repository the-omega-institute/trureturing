# Actual complete counts on all even lengths

## Abstract

The raw logarithms of actual strict and weak complete-list counts equal eta_b times the literal weight plus a little-o error on all even weights. Actual histories and both literal sources retain the same coefficient at the original observation offsets twenty-six and fifty-two.

Return lists are in execution order from the literal tail outward. Their literal weights are six times m plus twenty times r. The two models start at X_H and Y_H on the high side and at the corresponding X_L and Y_L on the low side. All source supplies use the original U/V and C blocks, the same stems and paid anchors, and the original literal tails. The external source reverses the return list without reversing the labels inside any block. Natural-number division and subtraction below use the natural quotient and truncated subtraction.

The weak complete-list count uses the non-strict high guard. It corresponds to the closed source contract when the nearest high endpoint is owned, o(0)=true; otherwise the closed contract uses the strict high guard. The strict and recordMargin source contracts always use the strict high guard.

**Definition 1.1 (fillerJ).**

$$\forall F \in Nat,\; \operatorname{fillerJ}\left(F\right) = \operatorname{ifThenElse}\left(\operatorname{mod}\left(\operatorname{divide}\left(F, 2\right), 3\right) = 0, 3, \operatorname{mod}\left(\operatorname{divide}\left(F, 2\right), 3\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.fillerJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The residue zero is represented by three; the other two residues are represented by one and two.

**Definition 1.2 (fillerQ).**

$$\forall F \in Nat,\; \operatorname{fillerQ}\left(F\right) = \operatorname{divide}\left(\operatorname{subtract}\left(\operatorname{divide}\left(F, 2\right), \operatorname{multiply}\left(13, \operatorname{fillerJ}\left(F\right)\right)\right), 3\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.fillerQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For even F at least seventy-eight, the numerator is nonnegative and divisible by three.

**Definition 1.3 (lowReturn).**

$$\forall q \in Nat,\; \operatorname{m}\left(\operatorname{lowReturn}\left(q\right)\right) = \operatorname{add}\left(1, q\right) \land \operatorname{r}\left(\operatorname{lowReturn}\left(q\right)\right) = 1$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.lowReturn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the positive return (1+q,1), of literal weight twenty-six plus six times q.

**Definition 1.4 (lowFiller).**

$$\forall F \in Nat,\; \operatorname{lowFiller}\left(F\right) = \operatorname{cons}\left(\operatorname{lowReturn}\left(\operatorname{fillerQ}\left(F\right)\right), \operatorname{replicate}\left(\operatorname{subtract}\left(\operatorname{fillerJ}\left(F\right), 1\right), \operatorname{lowReturn}\left(0\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.lowFiller` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first return carries all additional six-letter blocks. The remaining j-1 returns are (1,1). This one filler depends only on F.

**Theorem 1.5 (actual list weight even).**

$$\forall xs \in \operatorname{List}\left(Return\right),\; \operatorname{Even}\left(\operatorname{listWeight}\left(xs\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.actual_list_weight_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every summand six times m plus twenty times r is even. The empty list has weight zero.

**Theorem 1.6 (low filler geometry).**

$$\forall F \in Nat,\; \left(\operatorname{Even}\left(F\right) \land \operatorname{le}\left(78, F\right)\right) \Rightarrow \left(\operatorname{le}\left(1, \operatorname{fillerJ}\left(F\right)\right) \land \left(\operatorname{le}\left(\operatorname{fillerJ}\left(F\right), 3\right) \land \left(\left(\forall i \in Nat,\; \left(\operatorname{le}\left(1, i\right) \land \left(\operatorname{le}\left(i, 3\right) \land \operatorname{mod}\left(\operatorname{divide}\left(F, 2\right), 3\right) = \operatorname{mod}\left(i, 3\right)\right)\right) \Rightarrow i = \operatorname{fillerJ}\left(F\right)\right) \land \left(\operatorname{mod}\left(\operatorname{divide}\left(F, 2\right), 3\right) = \operatorname{mod}\left(\operatorname{fillerJ}\left(F\right), 3\right) \land \left(\operatorname{le}\left(\operatorname{multiply}\left(13, \operatorname{fillerJ}\left(F\right)\right), \operatorname{divide}\left(F, 2\right)\right) \land \left(\operatorname{dvd}\left(3, \operatorname{subtract}\left(\operatorname{divide}\left(F, 2\right), \operatorname{multiply}\left(13, \operatorname{fillerJ}\left(F\right)\right)\right)\right) \land \left(\operatorname{add}\left(\operatorname{multiply}\left(26, \operatorname{fillerJ}\left(F\right)\right), \operatorname{multiply}\left(6, \operatorname{fillerQ}\left(F\right)\right)\right) = F \land \left(\operatorname{listWeight}\left(\operatorname{lowFiller}\left(F\right)\right) = F \land \left(\left(\forall a \in Return,\; \operatorname{member}\left(a, \operatorname{lowFiller}\left(F\right)\right) \Rightarrow \operatorname{r}\left(a\right) = 1\right) \land \left(\forall K \in Nat,\; \operatorname{le}\left(2, K\right) \Rightarrow \left(\forall d \in Real, strict \in Bool, side \in Side, D \in Real,\; \operatorname{GuardTrace}\left(K, d, strict, side, \operatorname{lowFiller}\left(F\right), D\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.low_filler_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F=2v at least seventy-eight, v is at least thirty-nine. The unique representative j lies between one and three, so 13j is at most v. Dividing v-13j by three gives q and the exact weight 26j+6q=F. Every return has r=1<K, hence its guard passes for either strictness flag, either side and every input displacement. The three smallest residues are F=78 with (j,q)=(3,0), F=80 with (1,9), and F=82 with (2,5).

**Definition 1.7 (paddingCopies).**

$$\forall L \in Nat, T \in Nat,\; \operatorname{paddingCopies}\left(L, T\right) = \operatorname{divide}\left(\operatorname{subtract}\left(T, 78\right), L\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.paddingCopies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The number of complete reset codewords is the quotient of T-78 by L.

**Definition 1.8 (paddingWeight).**

$$\forall L \in Nat, T \in Nat,\; \operatorname{paddingWeight}\left(L, T\right) = \operatorname{subtract}\left(T, \operatorname{multiply}\left(\operatorname{paddingCopies}\left(L, T\right), L\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.paddingWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remainder includes the reserved seventy-eight units for the outer filler.

**Theorem 1.9 (even padding arithmetic).**

$$\forall L \in Nat, T \in Nat,\; \left(\operatorname{lt}\left(0, L\right) \land \left(\operatorname{Even}\left(L\right) \land \left(\operatorname{le}\left(78, T\right) \land \operatorname{Even}\left(T\right)\right)\right)\right) \Rightarrow \left(\operatorname{Even}\left(\operatorname{paddingWeight}\left(L, T\right)\right) \land \left(\operatorname{le}\left(78, \operatorname{paddingWeight}\left(L, T\right)\right) \land \left(\operatorname{lt}\left(\operatorname{paddingWeight}\left(L, T\right), \operatorname{add}\left(78, L\right)\right) \land \operatorname{add}\left(\operatorname{multiply}\left(\operatorname{paddingCopies}\left(L, T\right), L\right), \operatorname{paddingWeight}\left(L, T\right)\right) = T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.even_padding_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact decomposition is T=kL+F with even F in [78,78+L). At T=78, k is zero. At T=78+L, k is one and F returns to seventy-eight.

**Definition 1.10 (paddedExecution).**

$$\forall R \in Return, words \in \operatorname{List}\left(\operatorname{List}\left(Return\right)\right), F \in Nat,\; \operatorname{paddedExecution}\left(R, words, F\right) = \operatorname{append}\left(\operatorname{resetConcatenation}\left(R, words\right), \operatorname{lowFiller}\left(F\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.paddedExecution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The filler follows all codewords in execution order. It therefore precedes the original codeword list in the external source, on its outer side.

**Theorem 1.11 (same reset all even counts).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in Return,\; \operatorname{r}\left(R\right) = 1 \land \left(\operatorname{lt}\left(\operatorname{max}\left(\operatorname{max}\left(\operatorname{xSide}\left(high\right), \operatorname{ySide}\left(high\right)\right), \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right)\right) \land \left(\forall sourceModel \in Model, N \in Nat,\; \left(\operatorname{lt}\left(0, N\right) \land \operatorname{le}\left(1, \operatorname{actualCount}\left(sourceModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, N\right)\right)\right) \Rightarrow \left(\operatorname{Even}\left(N\right) \land \left(\operatorname{Even}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{divide}\left(\operatorname{min}\left(\operatorname{subtract}\left(b, \operatorname{actualAutomaticCost}\left(K\right)\right), \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right), 2\right)\right) \land \left(\forall targetModel \in Model, T \in Nat,\; \left(\operatorname{le}\left(78, T\right) \land \operatorname{Even}\left(T\right)\right) \Rightarrow \left(\left(\operatorname{Even}\left(\operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \land \left(\operatorname{le}\left(78, \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \land \left(\operatorname{lt}\left(\operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right), \operatorname{add}\left(78, \operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right)\right) \land \operatorname{add}\left(\operatorname{multiply}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right), \operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) = T\right)\right)\right) \land \left(\operatorname{Injective}\left((z : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \to \operatorname{Subtype}\left((xs : \operatorname{List}\left(Return\right) \mapsto \operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N)\right) \mapsto \operatorname{paddedExecution}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right))\right) \land \left(\left(\forall z \in \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \to \operatorname{Subtype}\left((xs : \operatorname{List}\left(Return\right) \mapsto \operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N)\right),\; \operatorname{listWeight}\left(\operatorname{paddedExecution}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right)\right) = T \land \left(\operatorname{GuardTrace}\left(K, \operatorname{add}\left(\operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right), false, high, \operatorname{paddedExecution}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right), \operatorname{initial}\left(high, targetModel\right)\right) \land \left(\operatorname{ActualPairSupply}\left(targetModel, o, \operatorname{subtract}\left(b, \operatorname{divide}\left(\operatorname{min}\left(\operatorname{subtract}\left(b, \operatorname{actualAutomaticCost}\left(K\right)\right), \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right), 2\right)\right), strict, \operatorname{paddedExecution}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right)\right) \land \left(\left(\forall contract \in Contract,\; \operatorname{ActualPairSupply}\left(targetModel, o, b, contract, \operatorname{paddedExecution}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right)\right)\right) \land \left(\left(\forall before \in \operatorname{List}\left(Return\right), a \in Return, after \in \operatorname{List}\left(Return\right),\; \left(\operatorname{paddedExecution}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) = \operatorname{append}\left(before, \operatorname{cons}\left(a, after\right)\right) \land \operatorname{r}\left(a\right) = K\right) \Rightarrow \left(\exists rest \in \operatorname{List}\left(Return\right),\; \operatorname{resetConcatenation}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right)\right) = \operatorname{append}\left(before, \operatorname{cons}\left(a, rest\right)\right)\right)\right) \land \left(\forall side \in Side,\; \operatorname{externalWord}\left(side, \operatorname{paddedExecution}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right)\right) = \operatorname{append}\left(\operatorname{externalWord}\left(side, \operatorname{lowFiller}\left(\operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right)\right), \operatorname{externalWord}\left(side, \operatorname{resetConcatenation}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\left(\forall strict \in Bool,\; \operatorname{le}\left(\operatorname{power}\left(\operatorname{actualCount}\left(sourceModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, N\right), \operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right), \operatorname{actualCount}\left(targetModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, T\right)\right)\right) \land \left(\forall contract \in Contract,\; \operatorname{le}\left(\operatorname{power}\left(\operatorname{actualCount}\left(sourceModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, N\right), \operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right), \operatorname{contractCount}\left(targetModel, o, b, contract, T\right)\right)\right)\right) \land \left(\operatorname{Injective}\left((z : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \to \operatorname{Subtype}\left((xs : \operatorname{List}\left(Return\right) \mapsto \operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N)\right) \mapsto \operatorname{history}\left(targetModel, \operatorname{paddedExecution}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right)\right))\right) \land \left(\forall side \in Side,\; \operatorname{Injective}\left((z : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \to \operatorname{Subtype}\left((xs : \operatorname{List}\left(Return\right) \mapsto \operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N)\right) \mapsto \operatorname{source}\left(side, targetModel, \operatorname{paddedExecution}\left(R, \operatorname{ofFn}\left((i : \operatorname{Fin}\left(\operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right) \mapsto \operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right))\right), \operatorname{paddingWeight}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right)\right))\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.same_reset_all_even_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The budget inequalities fix d=(lambda-b)/(g squared times chi to K). One low reset R is fixed before all source models and all N. Its floor B exceeds X_H, Y_H and d. For the full nonempty weak exact-N codebook, delta=B-D0, gamma=delta times g to N, and epsilon is half the minimum of b-C_auto and g squared times chi to K times gamma. Nonemptiness gives even N from an actual list, so L=N+20+6m(R) is positive and even. Append the same filler to every k-tuple. Every old high return has exactly its old execution prefix, while all filler returns are low. The original actual supply at b-epsilon extends to the same literal sources and zero-error futures. Cancelling the common filler and applying the reset parser with positive cumulative-weight cuts recovers all choices even when codeword letter lengths differ. The resulting exact-T actual dictionaries, every source contract, the color histories and both literal source sides all preserve those distinct choices.

**Theorem 1.12 (odd actual counts).**

$$\forall T \in Nat,\; \operatorname{Odd}\left(T\right) \Rightarrow \left(\left(\forall model \in Model, K \in Nat, d \in Real, strict \in Bool,\; \operatorname{actualCount}\left(model, K, d, strict, T\right) = 0\right) \land \left(\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract,\; \operatorname{contractCount}\left(model, o, b, contract, T\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.odd_actual_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No list of positive actual returns can have odd literal weight. Every strict, weak and source-contract dictionary at an odd weight is empty.

**Theorem 1.13 (even actual positivity).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall T \in Nat,\; \left(\operatorname{Even}\left(T\right) \land \operatorname{le}\left(78, T\right)\right) \Rightarrow \left(\operatorname{listWeight}\left(\operatorname{lowFiller}\left(T\right)\right) = T \land \left(\left(\forall model \in Model, contract \in Contract,\; \operatorname{ActualPairSupply}\left(model, o, b, contract, \operatorname{lowFiller}\left(T\right)\right) \land \operatorname{lt}\left(0, \operatorname{contractCount}\left(model, o, b, contract, T\right)\right)\right) \land \left(\forall model \in Model, strict \in Bool,\; \operatorname{lt}\left(0, \operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, T\right)\right) \land \operatorname{actualLogRate}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, T\right) = \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, T\right)\right)\right), \operatorname{toReal}\left(T\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.even_actual_positivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standalone low filler is strictly feasible from both models and supplies all original contracts. Every raw even count is positive at T at least seventy-eight. On this range, positivity permits max-one normalization to be removed from the logarithm.

**Theorem 1.14 (full even floor ratio).**

$$\forall L \in Nat,\; \left(\operatorname{lt}\left(0, L\right) \land \operatorname{Even}\left(L\right)\right) \Rightarrow \operatorname{Tendsto}\left((v : Nat \mapsto \operatorname{divide}\left(\operatorname{toReal}\left(\operatorname{paddingCopies}\left(L, \operatorname{multiply}\left(2, v\right)\right)\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{divide}\left(1, \operatorname{toReal}\left(L\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.full_even_floor_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bounded filler weight divided by T tends to zero on all T=2v. The exact decomposition kL+F=T gives k/T tending to 1/L on this full even filter.

**Theorem 1.15 (original finite even bridge).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall T \in Nat,\; \operatorname{Odd}\left(T\right) \Rightarrow \left(\left(\forall model \in Model, strict \in Bool,\; \operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, T\right) = 0\right) \land \left(\forall model \in Model, contract \in Contract,\; \operatorname{contractCount}\left(model, o, b, contract, T\right) = 0\right)\right)\right) \land \left(\left(\forall T \in Nat,\; \left(\operatorname{Even}\left(T\right) \land \operatorname{le}\left(78, T\right)\right) \Rightarrow \left(\operatorname{listWeight}\left(\operatorname{lowFiller}\left(T\right)\right) = T \land \left(\left(\forall model \in Model, contract \in Contract,\; \operatorname{ActualPairSupply}\left(model, o, b, contract, \operatorname{lowFiller}\left(T\right)\right) \land \operatorname{lt}\left(0, \operatorname{contractCount}\left(model, o, b, contract, T\right)\right)\right) \land \left(\forall model \in Model, strict \in Bool,\; \operatorname{lt}\left(0, \operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, T\right)\right) \land \operatorname{actualLogRate}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, T\right) = \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, T\right)\right)\right), \operatorname{toReal}\left(T\right)\right)\right)\right)\right)\right) \land \left(\exists R \in Return,\; \operatorname{r}\left(R\right) = 1 \land \left(\operatorname{lt}\left(\operatorname{max}\left(\operatorname{max}\left(\operatorname{xSide}\left(high\right), \operatorname{ySide}\left(high\right)\right), \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right)\right) \land \left(\forall sourceModel \in Model, N \in Nat,\; \left(\operatorname{lt}\left(0, N\right) \land \operatorname{le}\left(1, \operatorname{actualCount}\left(sourceModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, N\right)\right)\right) \Rightarrow \left(\operatorname{Even}\left(N\right) \land \left(\operatorname{Even}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right) \land \left(\left(\forall targetModel \in Model, T \in Nat,\; \left(\operatorname{le}\left(78, T\right) \land \operatorname{Even}\left(T\right)\right) \Rightarrow \left(\left(\forall strict \in Bool,\; \operatorname{le}\left(\operatorname{power}\left(\operatorname{actualCount}\left(sourceModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, N\right), \operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right), \operatorname{actualCount}\left(targetModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, T\right)\right)\right) \land \left(\forall contract \in Contract,\; \operatorname{le}\left(\operatorname{power}\left(\operatorname{actualCount}\left(sourceModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, N\right), \operatorname{paddingCopies}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right), T\right)\right), \operatorname{contractCount}\left(targetModel, o, b, contract, T\right)\right)\right)\right)\right) \land \left(\forall targetModel \in Model, strict \in Bool,\; \operatorname{le}\left(\operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{actualCount}\left(sourceModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, N\right)\right)\right), \operatorname{toReal}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right)\right), \operatorname{liminf}\left((v : Nat \mapsto \operatorname{actualLogRate}\left(targetModel, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, \operatorname{multiply}\left(2, v\right)\right)), atTop\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.original_finite_even_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Odd counts vanish, and all even raw counts are positive from weight seventy-eight onward. The same reset works for every fixed nonempty full weak codebook, for both target starts and both guard flags. Its exact-T power counts imply the normalized full-even liminf is at least log base two of a_N divided by N+C_R. The fixed-codebook bound holds on the entire even-weight filter. Positive-count codebook slopes approaching eta_b therefore bound this same liminf from below.

**Theorem 1.16 (actual even raw asymptotics).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall model \in Model, strict \in Bool,\; \operatorname{Tendsto}\left((v : Nat \mapsto \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{etaB}\left(K, b\right)\right)\right) \land \operatorname{IsLittleO}\left(atTop, (v : Nat \mapsto \operatorname{subtract}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{multiply}\left(\operatorname{etaB}\left(K, b\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)\right)), (v : Nat \mapsto \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.actual_even_raw_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix one reset of the all-even construction before choosing any source weight or target model. An unbounded positive-count sequence of original weak actual dictionaries has raw slope log2(a_N)/N tending to eta_b. For this exact fixed reset, N/(N+C_R) tends to one, so its codebook slopes also tend to eta_b. The full-even liminf is at least every one of these slopes for both target models and both guard flags. Boundedness of the original normalized sequence gives a full-even limsup at most its unrestricted limsup eta_b. The two bounds give the limit. The actual low filler makes every raw count positive at even T at least seventy-eight; only there is max-one normalization removed. Subtracting eta_b from the raw quotient gives zero limit, exactly the stated little-o error.

**Definition 1.17 (ObservedContractDictionary).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract, Nobs \in Nat,\; \operatorname{ObservedContractDictionary}\left(model, o, b, contract, Nobs\right) = \operatorname{Subtype}\left((xs : \operatorname{List}\left(Return\right) \mapsto \operatorname{ActualPairSupply}\left(model, o, b, contract, xs\right) \land \operatorname{length}\left(\operatorname{history}\left(model, xs\right)\right) = Nobs)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.ObservedContractDictionary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The indexing length is the length of the original color history. The underlying list has the original ActualPairSupply contract, including both source sides and their literal zero-error futures.

**Definition 1.18 (ActualHistoryImage).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract, Nobs \in Nat,\; \operatorname{ActualHistoryImage}\left(model, o, b, contract, Nobs\right) = \operatorname{range}\left((xs : \operatorname{ObservedContractDictionary}\left(model, o, b, contract, Nobs\right) \mapsto \operatorname{history}\left(model, \operatorname{val}\left(xs\right)\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.ActualHistoryImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This set contains exactly the original color histories obtained from the actual contract lists at the specified departure length.

**Definition 1.19 (ActualSourceImage).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract, Nobs \in Nat,\; \forall side \in Side,\; \operatorname{ActualSourceImage}\left(side, model, o, b, contract, Nobs\right) = \operatorname{range}\left((xs : \operatorname{ObservedContractDictionary}\left(model, o, b, contract, Nobs\right) \mapsto \operatorname{source}\left(side, model, \operatorname{val}\left(xs\right)\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.ActualSourceImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image uses the original full literal source constructor on a chosen side. Its prefix includes the original stem and the paid anchor precisely when the model is anchored; its tail is the prescribed original tail.

**Definition 1.20 (ActualSourcePairImage).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract, Nobs \in Nat,\; \operatorname{ActualSourcePairImage}\left(model, o, b, contract, Nobs\right) = \operatorname{range}\left((xs : \operatorname{ObservedContractDictionary}\left(model, o, b, contract, Nobs\right) \mapsto \operatorname{pair}\left(\operatorname{source}\left(high, model, \operatorname{val}\left(xs\right)\right), \operatorname{source}\left(low, model, \operatorname{val}\left(xs\right)\right)\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.ActualSourcePairImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The high and low sources are constructed from the same execution list and share its color history. The two respective literal future tails are retained.

**Definition 1.21 (historyImageCount).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract, Nobs \in Nat,\; \operatorname{historyImageCount}\left(model, o, b, contract, Nobs\right) = \operatorname{card}\left(\operatorname{ActualHistoryImage}\left(model, o, b, contract, Nobs\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.historyImageCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the cardinality of the actual history image at observation length Nobs.

**Definition 1.22 (sourceImageCount).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract, Nobs \in Nat,\; \forall side \in Side,\; \operatorname{sourceImageCount}\left(side, model, o, b, contract, Nobs\right) = \operatorname{card}\left(\operatorname{ActualSourceImage}\left(side, model, o, b, contract, Nobs\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.sourceImageCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the cardinality of one actual full-source image at observation length Nobs.

**Definition 1.23 (sourcePairImageCount).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract, Nobs \in Nat,\; \operatorname{sourcePairImageCount}\left(model, o, b, contract, Nobs\right) = \operatorname{card}\left(\operatorname{ActualSourcePairImage}\left(model, o, b, contract, Nobs\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.sourcePairImageCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the cardinality of the actual same-list high and low source-pair image.

**Theorem 1.24 (actual observation count correspondence).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall model \in Model, contract \in Contract, T \in Nat,\; \operatorname{Finite}\left(\operatorname{ObservedContractDictionary}\left(model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right)\right) \land \left(\left(\operatorname{historyImageCount}\left(model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right) = \operatorname{contractCount}\left(model, o, b, contract, T\right) \land \left(\left(\forall side \in Side,\; \operatorname{sourceImageCount}\left(side, model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right) = \operatorname{contractCount}\left(model, o, b, contract, T\right)\right) \land \operatorname{sourcePairImageCount}\left(model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right) = \operatorname{contractCount}\left(model, o, b, contract, T\right)\right)\right) \land \left(\operatorname{contractCount}\left(model, o, b, contract, T\right) = \operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{contractStrict}\left(o, contract\right), T\right) \land \left(\forall xs \in \operatorname{ObservedContractDictionary}\left(model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right),\; \operatorname{listWeight}\left(\operatorname{val}\left(xs\right)\right) = T \land \left(\forall side \in Side,\; \operatorname{length}\left(\operatorname{observedPrefix}\left(side, model, \operatorname{val}\left(xs\right)\right)\right) = \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right) \land \left(\operatorname{OperationRecord}\left(o, b, contract, \operatorname{source}\left(side, model, \operatorname{val}\left(xs\right)\right), \operatorname{OperationPairedRecord}\left(model, o, \operatorname{val}\left(xs\right), side\right)\right) \land \left(\operatorname{OperationFiniteSource}\left(\operatorname{source}\left(side, model, \operatorname{val}\left(xs\right)\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{apply}\left(\operatorname{source}\left(side, model, \operatorname{val}\left(xs\right)\right), \operatorname{add}\left(\operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right), p\right)\right) = \operatorname{address}\left(\operatorname{tailPrefix}\left(side\right), p\right)\right) \land \left(\exists err \in Nat \to Real,\; \operatorname{ErrorBound}\left(b, contract, err\right) \land \left(\left(\forall p \in Nat,\; \operatorname{lt}\left(p, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right) \Rightarrow \operatorname{observe}\left(o, \operatorname{coordinate}\left(\operatorname{sourcePrefix}\left(side, model, \operatorname{val}\left(xs\right)\right), p\right), \operatorname{apply}\left(err, p\right)\right) = \operatorname{getElem}\left(\operatorname{history}\left(model, \operatorname{val}\left(xs\right)\right), p\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{le}\left(\operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right), p\right) \Rightarrow \operatorname{apply}\left(err, p\right) = 0\right) \land \left(\forall p \in Nat,\; \operatorname{observe}\left(o, \operatorname{coordinate}\left(\operatorname{sourcePrefix}\left(side, model, \operatorname{val}\left(xs\right)\right), \operatorname{add}\left(\operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right), p\right)\right), \operatorname{apply}\left(err, \operatorname{add}\left(\operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right), p\right)\right)\right) = \operatorname{observe}\left(o, \operatorname{coordinate}\left(\operatorname{tailPrefix}\left(side\right), p\right), 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.actual_observation_count_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original reconstruction gives both the history length and each observed source-prefix length as Delta+T, with Delta=26 for the original model and Delta=52 for the anchored model. The equivalence fixes the return list itself. The original history parser is injective on all lists; the original source parser is injective at fixed list weight T. The high projection also makes the same-list source-pair map injective. Consequently all three image cardinalities are exactly the original contract count. The closed contract selects the weak dictionary precisely when o(0) is true, while strict and recordMargin select the strict dictionary. Every literal source in these images is a legal eventually-empty source with its actual record, and each supplied error is zero from the unobserved terminal onward.

**Theorem 1.25 (contract even raw asymptotics).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall model \in Model, contract \in Contract,\; \operatorname{Tendsto}\left((v : Nat \mapsto \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{contractCount}\left(model, o, b, contract, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{etaB}\left(K, b\right)\right)\right) \land \operatorname{IsLittleO}\left(atTop, (v : Nat \mapsto \operatorname{subtract}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{contractCount}\left(model, o, b, contract, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{multiply}\left(\operatorname{etaB}\left(K, b\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)\right)), (v : Nat \mapsto \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.contract_even_raw_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact contract dictionary equivalence transfers the raw limit and its little-o error to every original contract and every endpoint ownership vector. No additional positive-rate assumption is required.

**Theorem 1.26 (observation even reindexing).**

$$\forall model \in Model,\; \operatorname{Even}\left(\operatorname{observationOffset}\left(model\right)\right) \land \left(\operatorname{Tendsto}\left((v : Nat \mapsto \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), \operatorname{multiply}\left(2, v\right)\right)), atTop, atTop\right) \land \left(\operatorname{Tendsto}\left((v : Nat \mapsto \operatorname{subtract}\left(v, \operatorname{divide}\left(\operatorname{observationOffset}\left(model\right), 2\right)\right)), atTop, atTop\right) \land \operatorname{Eventually}\left((v : Nat \mapsto \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), \operatorname{multiply}\left(2, \operatorname{subtract}\left(v, \operatorname{divide}\left(\operatorname{observationOffset}\left(model\right), 2\right)\right)\right)\right) = \operatorname{multiply}\left(2, v\right)), atTop\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.observation_even_reindexing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both literal offsets are even. The indices Delta+2v are cofinal. For every sufficiently large even observation length 2v, subtracting half the offset gives the nonnegative list half-weight v-Delta/2, and Delta+2(v-Delta/2)=2v. Thus the shifted indexing covers the entire eventual even observation support.

**Theorem 1.27 (actual observation length asymptotics).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall model \in Model, contract \in Contract,\; \left(\forall Nobs \in Nat,\; \operatorname{Odd}\left(Nobs\right) \Rightarrow \left(\operatorname{historyImageCount}\left(model, o, b, contract, Nobs\right) = 0 \land \left(\left(\forall side \in Side,\; \operatorname{sourceImageCount}\left(side, model, o, b, contract, Nobs\right) = 0\right) \land \operatorname{sourcePairImageCount}\left(model, o, b, contract, Nobs\right) = 0\right)\right)\right) \land \left(\left(\forall T \in Nat,\; \operatorname{historyImageCount}\left(model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right) = \operatorname{contractCount}\left(model, o, b, contract, T\right) \land \left(\left(\forall side \in Side,\; \operatorname{sourceImageCount}\left(side, model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right) = \operatorname{contractCount}\left(model, o, b, contract, T\right)\right) \land \operatorname{sourcePairImageCount}\left(model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right) = \operatorname{contractCount}\left(model, o, b, contract, T\right)\right)\right) \land \left(\left(\forall T \in Nat,\; \left(\operatorname{Even}\left(T\right) \land \operatorname{le}\left(78, T\right)\right) \Rightarrow \left(\operatorname{lt}\left(0, \operatorname{historyImageCount}\left(model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right)\right) \land \left(\left(\forall side \in Side,\; \operatorname{lt}\left(0, \operatorname{sourceImageCount}\left(side, model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right)\right)\right) \land \operatorname{lt}\left(0, \operatorname{sourcePairImageCount}\left(model, o, b, contract, \operatorname{add}\left(\operatorname{observationOffset}\left(model\right), T\right)\right)\right)\right)\right)\right) \land \left(\left(\operatorname{Tendsto}\left((v : Nat \mapsto \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{historyImageCount}\left(model, o, b, contract, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{etaB}\left(K, b\right)\right)\right) \land \operatorname{IsLittleO}\left(atTop, (v : Nat \mapsto \operatorname{subtract}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{historyImageCount}\left(model, o, b, contract, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{multiply}\left(\operatorname{etaB}\left(K, b\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)\right)), (v : Nat \mapsto \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right))\right)\right) \land \left(\left(\forall side \in Side,\; \operatorname{Tendsto}\left((v : Nat \mapsto \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{sourceImageCount}\left(side, model, o, b, contract, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{etaB}\left(K, b\right)\right)\right) \land \operatorname{IsLittleO}\left(atTop, (v : Nat \mapsto \operatorname{subtract}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{sourceImageCount}\left(side, model, o, b, contract, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{multiply}\left(\operatorname{etaB}\left(K, b\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)\right)), (v : Nat \mapsto \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right))\right)\right) \land \left(\operatorname{Tendsto}\left((v : Nat \mapsto \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{sourcePairImageCount}\left(model, o, b, contract, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{etaB}\left(K, b\right)\right)\right) \land \operatorname{IsLittleO}\left(atTop, (v : Nat \mapsto \operatorname{subtract}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{sourcePairImageCount}\left(model, o, b, contract, \operatorname{multiply}\left(2, v\right)\right)\right)\right), \operatorname{multiply}\left(\operatorname{etaB}\left(K, b\right), \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right)\right)\right)), (v : Nat \mapsto \operatorname{toReal}\left(\operatorname{multiply}\left(2, v\right)\right))\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.actual_observation_length_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each image count at Delta+T equals the actual contract count at T. On even T at least seventy-eight, the low filler makes all these raw image counts positive; odd observed lengths have no lists because the offset and every list weight are even. Multiplying the raw list quotient by T/(T+Delta), which tends to one, preserves eta_b. The exact cofinal inverse indexing then gives convergence on every sufficiently large even observed length Nobs, for histories, each original source side and the same-list pair. Subtracting eta_b times Nobs yields a little-o error relative to Nobs in every case.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.ActualHistoryImage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.ActualSourceImage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.ActualSourcePairImage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.ObservedContractDictionary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.actual_even_raw_asymptotics`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.actual_list_weight_even`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.actual_observation_count_correspondence`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.actual_observation_length_asymptotics`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.contract_even_raw_asymptotics`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.even_actual_positivity`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.even_padding_arithmetic`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.fillerJ`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.fillerQ`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.full_even_floor_ratio`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.historyImageCount`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.lowFiller`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.lowReturn`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.low_filler_geometry`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.observation_even_reindexing`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.odd_actual_counts`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.original_finite_even_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.paddedExecution`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.paddingCopies`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.paddingWeight`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.same_reset_all_even_counts`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.sourceImageCount`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.sourcePairImageCount`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge](ActualCountRateBridge.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/LowerRateLimit](LowerRateLimit.md)
