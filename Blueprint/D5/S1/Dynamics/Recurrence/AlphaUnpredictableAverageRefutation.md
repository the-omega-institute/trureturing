# Alpha unpredictability does not ensure an average

## Abstract

A smooth even alpha-unpredictable function has neither ordinary Cesaro mean.

**Definition 1.1 (A sequence of uniform returns on bounded intervals).**

$$\forall (f: \mathbb{R} \to \mathbb{R}), (\forall (q: \mathbb{N} \to \mathbb{R}), (\operatorname{PoissonReturn}\left(f, q\right) = ((\operatorname{UniformContinuous}\left(f\right)) \land ((\exists (M: \mathbb{R}), (\forall (t: \mathbb{R}), (\left|f\left(t\right)\right| \le M))) \land ((\operatorname{StrictMono}\left(q\right)) \land ((\operatorname{Tendsto}\left(q, \operatorname{Filter.atTop}, \operatorname{Filter.atTop}\right)) \land (\forall (a: \mathbb{R}), (\forall (b: \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), ((a \le b) \Rightarrow ((0 < \varepsilon) \Rightarrow (\exists (N: \mathbb{N}), (\forall (n: \mathbb{N}), ((N \le n) \Rightarrow (\forall (t: \mathbb{R}), ((t \in \operatorname{Set.Icc}\left(a, b\right)) \Rightarrow (\left|f\left(t + q\left(n\right)\right) - f\left(t\right)\right| < \varepsilon)))))))))))))))))$$

*Formalization.* `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.PoissonReturn` (`✓ std3`).

*Citation.* Marat Akhmet; Nurlan Tilessov (2026). *Integral of an Alpha Unpredictable Function*. DOI: [10.3390/math14183391](https://doi.org/10.3390/math14183391). URL: <https://arxiv.org/abs/2608.09809v2>.

*Commentary.*

Journal §2, Definition 1, page 2 of 8: “Definition 1 ([4,10]). A uniformly continuous and bounded on the real axis function f(t) is said to be Poisson stable if there exists a strictly increasing sequence tₙ that approaches infinity, such that the sequence of shifts f(t+tₙ) converges uniformly to the function f(t) on every bounded interval.”

PoissonReturn keeps the real return sequence q explicit. Uniform convergence is written as an eventual epsilon estimate on each closed bounded interval. Uniform continuity implies continuity, and the real number M bounds the absolute value on the whole real line.

**Definition 1.2 (Poisson stability).**

$$\forall (f: \mathbb{R} \to \mathbb{R}), (\operatorname{IsPoissonStable}\left(f\right) = (\exists (q: \mathbb{N} \to \mathbb{R}), (\operatorname{PoissonReturn}\left(f, q\right))))$$

*Formalization.* `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.IsPoissonStable` (`✓ std3`).

*Citation.* Marat Akhmet; Nurlan Tilessov (2026). *Integral of an Alpha Unpredictable Function*. DOI: [10.3390/math14183391](https://doi.org/10.3390/math14183391). URL: <https://arxiv.org/abs/2608.09809v2>.

*Commentary.*

Journal §2, Definition 1, page 2 of 8: “Definition 1 ([4,10]). A uniformly continuous and bounded on the real axis function f(t) is said to be Poisson stable if there exists a strictly increasing sequence tₙ that approaches infinity, such that the sequence of shifts f(t+tₙ) converges uniformly to the function f(t) on every bounded interval.”

IsPoissonStable existentially quantifies the real return sequence in PoissonReturn.

**Definition 1.3 (Alpha unpredictability with the same return sequence).**

$$\forall (f: \mathbb{R} \to \mathbb{R}), (\operatorname{IsAlphaUnpredictable}\left(f\right) = (\exists (q: \mathbb{N} \to \mathbb{R}), ((\operatorname{PoissonReturn}\left(f, q\right)) \land (\exists (s: \mathbb{N} \to \mathbb{R}), (\exists (\varepsilon_{0}: \mathbb{R}), (\exists (\delta: \mathbb{R}), ((\operatorname{StrictMono}\left(s\right)) \land ((\operatorname{Tendsto}\left(s, \operatorname{Filter.atTop}, \operatorname{Filter.atTop}\right)) \land ((0 < \varepsilon_{0}) \land ((0 < \delta) \land (\forall (n: \mathbb{N}), (\forall (t: \mathbb{R}), ((t \in \operatorname{Set.Icc}\left(s\left(n\right), s\left(n\right) + \delta\right)) \Rightarrow (\varepsilon_{0} < \left|f\left(t + q\left(n\right)\right) - f\left(t\right)\right|))))))))))))))$$

*Formalization.* `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.IsAlphaUnpredictable` (`✓ std3`).

*Citation.* Marat Akhmet; Nurlan Tilessov (2026). *Integral of an Alpha Unpredictable Function*. DOI: [10.3390/math14183391](https://doi.org/10.3390/math14183391). URL: <https://arxiv.org/abs/2608.09809v2>.

*Commentary.*

Journal §2, Definition 2, page 2 of 8: “Definition 2 ([9]). A Poisson-stable function f(t) is defined as alpha unpredictable if, in addition to having a convergent sequence, there exist a strictly increasing sequence sₙ that tends to infinity, and positive numbers ϵ₀ and δ such that for each index n, the following inequality is satisfied:”

“|f(t+tₙ)-f(t)|>ϵ₀ for all t∈[sₙ,sₙ+δ].”

The displayed source interval is [s n, s n + delta]. Its following prose instead describes a symmetric interval; the formula above follows the displayed inequality. The real sequence q is shared by recurrence and separation. Both q and s are strictly increasing and tend to positive infinity; the positive separation threshold and interval length are independent of n.

**Definition 1.4 (Universal existence of an ordinary average).**

$$claim = ((\forall (f: \mathbb{R} \to \mathbb{R}), ((\operatorname{IsAlphaUnpredictable}\left(f\right)) \Rightarrow (\exists (m: \mathbb{R}), (\operatorname{Tendsto}\left(\lambda (T: \mathbb{R}) \mapsto (\frac{\int_{0}^{T} f\left(t\right) dt}{T}), \operatorname{Filter.atTop}, \operatorname{nhds}\left(m\right)\right))))) \lor (\forall (f: \mathbb{R} \to \mathbb{R}), ((\operatorname{IsAlphaUnpredictable}\left(f\right)) \Rightarrow (\exists (m: \mathbb{R}), (\operatorname{Tendsto}\left(\lambda (T: \mathbb{R}) \mapsto (\frac{\int_{-T}^{T} f\left(t\right) dt}{2 \cdot T}), \operatorname{Filter.atTop}, \operatorname{nhds}\left(m\right)\right))))))$$

*Formalization.* `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.claim` (`✓ std3`).

*Citation.* Marat Akhmet; Nurlan Tilessov (2026). *Integral of an Alpha Unpredictable Function*. DOI: [10.3390/math14183391](https://doi.org/10.3390/math14183391). URL: <https://arxiv.org/abs/2608.09809v2>.

*Commentary.*

Journal §3, Remark 1, page 7 of 8: “Remark 1. We see that the constant c in (8)—paired with a bounded function g(t)—exists if and only if it equals to the average of f(t). Nevertheless, whether every alpha unpredictable function possesses an average is still an open question.”

The source does not define average. The two alternatives quantify ordinary one-sided and symmetric Cesàro limits, respectively. Negating their disjunction denies each universal assertion. The functions and both sequences are real-valued; indices are natural numbers. The value at T = 0 is irrelevant to a limit at positive infinity, and continuity ensures integrability on every compact interval. The question occurs in the journal article; it is absent from arXiv:2608.09809v2. The bounded-remainder assertion in the first sentence is a separate statement.

**Theorem 1.5 (Neither universal average-existence assertion holds).**

$$\neg ((\forall (f: \mathbb{R} \to \mathbb{R}), ((\operatorname{IsAlphaUnpredictable}\left(f\right)) \Rightarrow (\exists (m: \mathbb{R}), (\operatorname{Tendsto}\left(\lambda (T: \mathbb{R}) \mapsto (\frac{\int_{0}^{T} f\left(t\right) dt}{T}), \operatorname{Filter.atTop}, \operatorname{nhds}\left(m\right)\right))))) \lor (\forall (f: \mathbb{R} \to \mathbb{R}), ((\operatorname{IsAlphaUnpredictable}\left(f\right)) \Rightarrow (\exists (m: \mathbb{R}), (\operatorname{Tendsto}\left(\lambda (T: \mathbb{R}) \mapsto (\frac{\int_{-T}^{T} f\left(t\right) dt}{2 \cdot T}), \operatorname{Filter.atTop}, \operatorname{nhds}\left(m\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/akhmet-tilessov-alpha-unpredictable-average` (refuted) by `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"akhmet-tilessov-alpha-unpredictable-average","declaration_gid":"D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marat Akhmet; Nurlan Tilessov (2026). *Integral of an Alpha Unpredictable Function*. DOI: [10.3390/math14183391](https://doi.org/10.3390/math14183391). URL: <https://arxiv.org/abs/2608.09809v2>.

*Commentary.*

Start with the empty binary word. At stage n + 1, append the concatenation of all binary words of length n + 1, followed by a constant block of length (n + 1) squared times one plus the length already written. Its letter is Nat.bodd (n + 1). Each stage extends its predecessor, and its length is at least its index. Reading a fixed position from a sufficiently long stage therefore defines one infinite binary sequence. Every finite word occurs arbitrarily late, while the fraction of ones at a stage endpoint differs from that stage's final letter by at most 1/(n squared + 1).

Reflect the unit cells across zero by sending an integer k below zero to -k-1. Cast each binary letter using Bool.toNat to form a bounded measurable step function. Convolve it with the normalized even ContDiffBump centered at zero with inner radius 1/8 and outer radius 1/4. Mathlib's convolution smoothness, normalized mass, plateau and reflection results give an even smooth function bounded in absolute value by one. A uniform integral bound on its derivative gives uniform continuity.

Arbitrarily late copies of each reflected central word supply an increasing integer return sequence. The smoothed function agrees exactly with its translate on each sufficiently small central interval. For each of those same shifts q n, an arbitrarily late copy of q n zeroes followed by one supplies a zero plateau whose translate is a one plateau. Choosing increasing plateau centers plus 1/2 gives the divergence sequence, with separation threshold 1/2 and interval length 1/8.

Translating an interval changes the integral of the step function by at most twice the translation distance. Fubini and the kernel's radius bound therefore show that smoothing changes each integrated total from zero to T by at most 1/2. At the growing stage endpoints the mean differs from the alternating letter by at most 2/n. A hypothetical limit would then make the constant zero and constant one subsequences have the same limit. Evenness identifies the symmetric mean with the one-sided mean, so this single function defeats both alternatives.

Symbolic sequence constructions and convolution realizations of unpredictability appear in Akhmet–Fen, Poincaré chaos and unpredictable functions (arXiv:1608.07301), and Akhmet–Fen–Alejaily, A randomly determined unpredictable function (arXiv:1910.12758v2). Nonconvergent time averages are also part of classical historic behavior. The argument here combines arbitrarily late word occurrences with alternating occupation proportions and an even smooth realization. Exhaustive literature completeness remains ASSUMED-UNVERIFIED; the full Sigmund article and the relevant IOP monograph chapters were not verified in the literature screen.

The exact finite checker is in the-omega-institute/trureturing-experiments at commit 8a5ad4a43297e68ef131028eddf08d0eb60c04f2, docs/reports/akhmet-tilessov-2026-alpha-unpredictable-average/check.py, SHA-256 28eafdc7ea3bdac010b391cae6d106e24cba1e51b1e7a7d2f20c27a462349a43; python3 check.py exited 0. It checks finite counts, rational samples and support containment using a polynomial test kernel. It does not establish infinite limits or smoothness, and its enumeration order and sample shifts need not equal those of the noncomputable Lean function.

## References

- Truth anchor: `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.IsAlphaUnpredictable`
- Truth anchor: `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.IsPoissonStable`
- Truth anchor: `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.PoissonReturn`
- Truth anchor: `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.claim`
- Truth anchor: `D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation.result`
