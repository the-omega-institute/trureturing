# Original window even sector

## Abstract

The original complex AE-even window sector and parity of the symmetric finite prime action.

The carrier WindowL2(a) is complex L2 for Lebesgue measure restricted to Ioc(-a,a]. Evenness is defined by the actual whole-line zero extension before any cosine span is considered. The results in this module allow arbitrary real a; the later normalized cosine completeness and projection estimates require a>0. All mode and prime cutoffs here are natural numbers, and coefficient families are complex.

**Definition 1.1 (Isometric zero extension of L2 classes).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.zeroIsometry`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalWindowEven.zeroIsometry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex linear isometry sends the window class to its indicator zero extension in whole-line complex L2. The construction uses the existing interval zero-extension result with length 2*a and origin -a. Its norm equality uses the indicator/restricted-measure identity; no endpoint trace is selected.

**Definition 1.2 (Original AE-even subspace).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Whole-line reflection is composition with x |-> -x and is complex linear, without conjugating the values. originalEven is the kernel of reflection after zero extension minus zero extension. This definition includes the full original AE-even sector independently of any Fourier or cosine completeness statement.

**Theorem 1.3 (Closedness of the original even sector).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven_isClosed`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven_isClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sector is closed as the kernel of a continuous complex linear map. Its subtype is therefore complete, supplying the Hilbert-space projection framework used later.

**Theorem 1.4 (Membership means AE reflection invariance).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.mem_originalEven_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalWindowEven.mem_originalEven_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any window L2 class u, membership is equivalent to equality almost everywhere for whole-line Lebesgue measure between its zero extension at -x and at x. Reflection turns Ioc into Ico; the two exceptional endpoints have measure zero. No pointwise equality of the endpoint indicators is asserted.

**Theorem 1.5 (Independence of the chosen representative).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis identifies u and a function f almost everywhere for the restricted window measure. Under precisely that hypothesis, membership can be tested using the original zero extension of f. Arbitrary representative values at the endpoints do not change the criterion.

**Theorem 1.6 (Every finite complex cosine head is originally even).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.head_mem_originalEven`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalWindowEven.head_mem_originalEven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each real cosine mode is even, so its complex L2 class lies in the sector. Closure under complex scalar multiplication and finite sums puts headL2(a,N,v), with indices 0 through the natural N, in the same original sector for every complex family v. This inclusion does not assume completeness of the modes.

**Theorem 1.7 (Reflection reverses an actual compressed shift).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.compression_reflection_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalWindowEven.compression_reflection_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real a and s and a function whose original zero extension is AE-even, reflecting compression(a,s,f) equals compression(a,-s,f) almost everywhere. Both the inner zero extension before translation and the outer compression to Ioc(-a,a] remain in the identity. Translation preserves the null sets needed for this argument.

**Theorem 1.8 (Parity of the original symmetric finite prime action).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.primeAction_even`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalWindowEven.primeAction_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural cutoff K, the exact sum over r in Icc(1,K) retains weight vonMangoldt(r)/sqrt(r) and both compressed shifts by log(r) and -log(r). AE-evenness of the input zero extension makes their sum AE-even. Prime powers remain present; there is no primality-only filter, real-coefficient restriction or cancellation assumption. The separate support identity says that applying zero extension again leaves this action unchanged.

**Theorem 1.9 (The actual finite prime image lies in the original even sector).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.primeHead_mem_originalEven`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalWindowEven.primeHead_mem_originalEven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

primeHeadL2 uses the arithmetic cutoff primeCutoff(a)=floor(exp(2*a)), independently of the natural head cutoff N. Its representative is the exact primeAction on the complex cosine profile. The representative criterion, support identity and parity of the paired shifts place that L2 class in originalEven, without any separation condition on N.

These are applications of standard Lp zero extension, measure-preserving reflection and closed-kernel Hilbert-space methods. They provide analytic parity and carrier facts, with no literature novelty, canonical full Weil arithmetic/operator identification, signed positivity or Riemann-hypothesis conclusion claimed.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.compression_reflection_ae`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.head_mem_originalEven`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.mem_originalEven_iff`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven_isClosed`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.originalEven_representative`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.primeAction_even`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.primeHead_mem_originalEven`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalWindowEven.zeroIsometry`
- Dependency: [D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection](PhysicalCosineTailProjection.md)
- Dependency: [D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport](../ZetaGamma/PeriodicEnergyTransport.md)
