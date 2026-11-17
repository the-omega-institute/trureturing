---
bibkey: akhmettilessov2026integral
authors: Marat Akhmet; Nurlan Tilessov
year: 2026
title: Integral of an Alpha Unpredictable Function
doi: 10.3390/math14183391
url: https://arxiv.org/abs/2608.09809v2
claim: "Journal Definitions 1–2 specify Poisson stability and alpha unpredictability with the same return sequence; Remark 1 asks whether every alpha unpredictable function possesses an average."
strata_touched:
  - D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation
license: citation-only
triage: anchor
---

# Integral of an Alpha Unpredictable Function

## Verified locator

DOI: https://doi.org/10.3390/math14183391

Source: https://arxiv.org/abs/2608.09809v2

Journal: Mathematics 14(18), 3391. The average-existence question occurs on page 7 of the journal article, but is absent from arXiv v2. The journal PDF is https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03391/article_deploy/mathematics-14-03391.pdf.

## Source statements

**Journal §2, PDF page 2 of 8, scope and Definitions 1–2:**

> In the present research, we consider continuous real-valued functions that are determined and uniformly bounded on the real axis.

> Definition 1 ([4,10]). A uniformly continuous and bounded on the real axis function $f(t)$ is said to be Poisson stable if there exists a strictly increasing sequence $t_n$ that approaches infinity, such that the sequence of shifts $f(t+t_n)$ converges uniformly to the function $f(t)$ on every bounded interval.

> The set $t_n$ is called a convergence or Poisson sequence. One can also use the phrase a sequence of return.

> Definition 2 ([9]). A Poisson-stable function $f(t)$ is defined as alpha unpredictable if, in addition to having a convergent sequence, there exist a strictly increasing sequence $s_n$ that tends to infinity, and positive numbers $\epsilon_0$ and $\delta$ such that for each index $n$, the following inequality is satisfied:
>
> $|f(t+t_n)-f(t)|>\epsilon_0\quad\text{for all }t\in[s_n,s_n+\delta].$

> The sequence $s_n$ is referred to as a divergence sequence, while the intervals $[s_n-\delta,s_n+\delta]$ are known as divergence intervals.

The displayed inequality uses [s_n,s_n+delta], whereas the following prose uses a symmetric interval. The formal predicate follows the displayed inequality.

**Journal §3, Remark 1, PDF page 7 of 8:**

> Remark 1. We see that the constant $c$ in (8)—paired with a bounded function $g(t)$—exists if and only if it equals to the average of $f(t)$. Nevertheless, whether every alpha unpredictable function possesses an average is still an open question.


The source leaves “average” unspecified. The formalization treats both ordinary one-sided and symmetric Cesàro limits and negates the disjunction of their universal existence assertions. It does not assess the bounded-primitive theorem or the bounded-remainder assertion in Remark 1's first sentence.

## Mathematical attribution and boundary

Akhmet–Fen, *Poincaré chaos and unpredictable functions*, arXiv:1608.07301, §§4–5, and Akhmet–Fen–Alejaily, *A randomly determined unpredictable function*, arXiv:1910.12758v2, Definitions 1.1–1.2 and §2, give prior symbolic and convolution constructions. The simultaneous late-word recurrence and alternating occupation construction, with an even smooth scalar realization, is derived in the repository. Historic behavior and nonconvergent time averages are classical; no claim of inventing these phenomena is made.

The literature screen on #26750 located no verified settlement within its reported scope. Exhaustive completeness and novelty remain ASSUMED-UNVERIFIED: the full Sigmund article *Time averages for unpredictable orbits of deterministic systems* (10.1007/BF02071057), the relevant Levitan–Shcherbakov works, and the full IOP monograph chapters were not independently verified.

## Supplementary exact finite computation

The checker is `docs/reports/akhmet-tilessov-2026-alpha-unpredictable-average/check.py` in `the-omega-institute/trureturing-experiments`, commit `8a5ad4a43297e68ef131028eddf08d0eb60c04f2`, SHA-256 `28eafdc7ea3bdac010b391cae6d106e24cba1e51b1e7a7d2f20c27a462349a43`. The reported `python3 check.py` exit is 0. Its rational samples, finite counts and support certificates use a polynomial test kernel; they do not prove infinite limits or smoothness. Its enumeration order and sampled shifts are not claimed to coincide with the literal noncomputable Lean witness.
