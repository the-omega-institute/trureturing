# A bin-count reversal for cyclic multinomial dispersion

## Abstract

At four draws, a fourth bin increases cyclic multinomial dispersion.

**Definition 1.1 (Bounded count vectors).**

$$C_{n,N} = \mathrm{Fin}(n) \to \mathrm{Fin}(N + 1)$$

*Formalization.* `D5/S3/TotalVariation/BanicR312Settlement.CountVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural n and N, a vector supplies one count between zero and N for each bin. The carrier includes all such vectors. Write kᵢ for the natural value of the count in bin i.

**Definition 1.2 (Measurable sets of count vectors).**

$$\mathcal{A}_{n,N} = \mathcal{P}(C_{n,N})$$

*Formalization.* `D5/S3/TotalVariation/BanicR312Settlement.countVectorMeasurableSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n and N the named instance is the top measurable space on the carrier. Its measurable sets are all subsets of that carrier.

**Definition 1.3 (Uniform multinomial point mass).**

$$m_{n,N}(k) = \begin{cases}\frac{N!}{\prod_{i \in \mathrm{Fin}(n)} k_{i}!}\,\left(\frac{1}{n}\right)^{N},&\sum_{i \in \mathrm{Fin}(n)} k_{i} = N\\0,&\sum_{i \in \mathrm{Fin}(n)} k_{i} \ne N\end{cases}$$

*Formalization.* `D5/S3/TotalVariation/BanicR312Settlement.multinomialMass` (`✓ std3`).

*Citation.* Nikola Banić and Neven Elezović (2026). *Discrete total variation under the multinomial, Part 5: cyclic total variation*. DOI: [10.48550/arXiv.2611.14735](https://doi.org/10.48550/arXiv.2611.14735). URL: <https://arxiv.org/abs/2611.14735v1>.

*Commentary.*

For natural n and N and each vector k in the carrier, the mass is in the extended nonnegative reals. Interpret the factorials and reciprocal in that type. The zero case enforces the total N, and the factor (1/n) to the power N specializes equation (2.2) to uniform bins.

**Definition 1.4 (Measure of the count vector).**

$$\mu_{n,N} = \sum_{k \in C_{n,N}} m_{n,N}(k)\,\delta_{k}$$

*Formalization.* `D5/S3/TotalVariation/BanicR312Settlement.multinomialLaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nikola Banić and Neven Elezović (2026). *Discrete total variation under the multinomial, Part 5: cyclic total variation*. DOI: [10.48550/arXiv.2611.14735](https://doi.org/10.48550/arXiv.2611.14735). URL: <https://arxiv.org/abs/2611.14735v1>.

*Commentary.*

For natural n and N the measure is the finite sum over the whole count carrier. Each coefficient scales the Dirac measure at its own vector. This realizes the uniform count law on the domain of Remark 3.12.

**Definition 1.5 (Cyclic variation of a count vector).**

$$D_{n,N}(k) = \sum_{i \in \mathrm{Fin}(n)} \left|k_{\operatorname{finRotate}(n,i)} - k_{i}\right|$$

*Formalization.* `D5/S3/TotalVariation/BanicR312Settlement.cyclicVariation` (`✓ std3`).

*Citation.* Nikola Banić and Neven Elezović (2026). *Discrete total variation under the multinomial, Part 5: cyclic total variation*. DOI: [10.48550/arXiv.2611.14735](https://doi.org/10.48550/arXiv.2611.14735). URL: <https://arxiv.org/abs/2611.14735v1>.

*Commentary.*

For natural n and N and each vector k in the carrier, take differences of the natural counts after casting them to the reals. The permutation finRotate advances around the bins and sends the last bin to the first, giving the closing edge in equation (2.17).

**Definition 1.6 (Variance per draw).**

$$v(n,N) = \frac{\operatorname{Var}_{\mu_{n,N}}(D_{n,N})}{N}$$

*Formalization.* `D5/S3/TotalVariation/BanicR312Settlement.dispersionSquared` (`✓ std3`).

*Citation.* Nikola Banić and Neven Elezović (2026). *Discrete total variation under the multinomial, Part 5: cyclic total variation*. DOI: [10.48550/arXiv.2611.14735](https://doi.org/10.48550/arXiv.2611.14735). URL: <https://arxiv.org/abs/2611.14735v1>.

*Commentary.*

For natural n and N, take the real variance of the cyclic variation under the count-vector measure and divide by the real cast of N. The definition uses Lean's total real division. Corollary 3.5 uses this normalization for positive N.

**Definition 1.7 (Cyclic dispersion).**

$$\sigma_{c}(n,N) = \sqrt{v(n,N)}$$

*Formalization.* `D5/S3/TotalVariation/BanicR312Settlement.dispersion` (`✓ std3`).

*Citation.* Nikola Banić and Neven Elezović (2026). *Discrete total variation under the multinomial, Part 5: cyclic total variation*. DOI: [10.48550/arXiv.2611.14735](https://doi.org/10.48550/arXiv.2611.14735). URL: <https://arxiv.org/abs/2611.14735v1>.

*Commentary.*

For natural n and N, apply the nonnegative real square root to the variance per draw. Remark 3.12 compares this quantity on the stated positive-sample domain.

**Definition 1.8 (Proposed monotonicities).**

$$[\forall n,N \in \mathbb{N}, 3 \le n \Rightarrow 1 \le N \Rightarrow \sigma_{c}(n + 1,N) \le \sigma_{c}(n,N)] \land [\forall n,N \in \mathbb{N}, 3 \le n \Rightarrow 1 \le N \Rightarrow \sigma_{c}(n,N) \le \sigma_{c}(n,N + 1)]$$

*Formalization.* `D5/S3/TotalVariation/BanicR312Settlement.claim` (`✓ std3`).

*Citation.* Nikola Banić and Neven Elezović (2026). *Discrete total variation under the multinomial, Part 5: cyclic total variation*. DOI: [10.48550/arXiv.2611.14735](https://doi.org/10.48550/arXiv.2611.14735). URL: <https://arxiv.org/abs/2611.14735v1>.

*Commentary.*

Nikola Banić and Neven Elezović ask whether the exact dispersion decreases as the bin count grows and increases as the draw count grows. Each adjacent comparison ranges independently over natural n at least three and N at least one. See Remark 3.12, arXiv:2611.14735v1, PDF p. 15. https://arxiv.org/pdf/2611.14735v1#page=15

**Theorem 1.9 (Refutation of the joint monotonicity claim).**

$$\neg \left([\forall n,N \in \mathbb{N}, 3 \le n \Rightarrow 1 \le N \Rightarrow \sigma_{c}(n + 1,N) \le \sigma_{c}(n,N)] \land [\forall n,N \in \mathbb{N}, 3 \le n \Rightarrow 1 \le N \Rightarrow \sigma_{c}(n,N) \le \sigma_{c}(n,N + 1)]\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/BanicR312Settlement.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nikola Banić and Neven Elezović (2026). *Discrete total variation under the multinomial, Part 5: cyclic total variation*. DOI: [10.48550/arXiv.2611.14735](https://doi.org/10.48550/arXiv.2611.14735). URL: <https://arxiv.org/abs/2611.14735v1>.

*Commentary.*

For each bin count, sum the integer multinomial weight times D to powers zero, one and two over the bounded count vectors. At (3,4) these sums are (81,312,1488) and at (4,4) they are (256,1120,5888). The zeroth sums give total probability one after division by n to the power N. The first and second sums give the corresponding moments under the same measure.

Subtracting the squared first moment from the second moment and dividing by N gives normalized variances 644/729 and 247/256, respectively. Taking the square root preserves the strict increase from three to four bins at four draws. This contradicts the bin-count clause of the conjunction.

The original exact calculation also gives variance per draw 3835/4096 at four bins and five draws. In the separate compiled BothReversals proof this gives a strict decrease from four to five draws, refuting the draw-count clause directly. Remark 3.13 asks separately about modes across all bin counts for a fixed draw count. The historical calculation examines that profile at four draws.

Claude Code session 07b67e50-10a4-41b3-9622-660f37c654a5 coordinated the historical research. Codex CLI research flight 8964c4b7bb607dfbb7e139d9 screened sources, prepared the exact experiment and mathematical derivation, and compiled the definitions. GPT Pro search seat gptpro-search-s1318 contributed literature search. Loning authored the commits for the exact experiment. https://github.com/the-omega-institute/trureturing/issues/31389

Codex CLI flight 6b02a23c137ce8bf24560049 wrote the original Lean proof with both strict comparisons, recorded at Git checkpoint 23991cf8468c1. Codex CLI Stage A flight 6b02a69d3e9dff94a3d5d1b7 integrated the direct bin-count proof and its initial exposition and compiled the separate BothReversals proof. MacStudio2 is the Git author on the original proof checkpoint and the integration commit c9b9d86c09b7. Codex CLI flight 6b02ad5d9985be77a04c7d34 authored this expanded Scribe exposition. https://github.com/the-omega-institute/trureturing/issues/31389#issuecomment-7076300413

## References

- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.CountVector`
- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.claim`
- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.countVectorMeasurableSpace`
- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.cyclicVariation`
- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.dispersion`
- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.dispersionSquared`
- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.multinomialLaw`
- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.multinomialMass`
- Truth anchor: `D5/S3/TotalVariation/BanicR312Settlement.result`
