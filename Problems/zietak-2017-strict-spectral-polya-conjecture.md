---
slug: zietak-2017-strict-spectral-polya-conjecture
bibkey: zietak2017strictspectral
doi: 10.4064/bc112-0-16
url: https://doi.org/10.4064/bc112-0-16
triage: theorem
motivation_gids:
  - D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.result
---

# Ziętak's strict spectral approximant convergence conjecture

## Problem

K. Ziętak, “From the strict Chebyshev approximant of a vector to the strict spectral approximant of a matrix,” Banach Center Publications 112 (2017), Conjecture 1.1, asks whether Schatten-p approximant residuals converge to the residual of a strict spectral approximant for every complex matrix subspace.

The source statement is:

> Let M be a linear subspace of Cᵐˣⁿ and let Bₚ ∈ M be the cₚ-approximant to A ∈ Cᵐˣⁿ. As p tends to ∞, the matrix Rₚ = A − Bₚ converges to A − B⁽ˢᵗ⁾, where B⁽ˢᵗ⁾ is the strict spectral approximant to A.

### Statement echo

The Lean `claim` quantifies over all natural dimensions, complex matrix subspaces, targets, strict spectral approximants, and real-parameter functions of approximants. Its hypotheses require strict spectral minimality and a Schatten-p minimizing approximant for every p > 1; its conclusion is convergence of residual matrices. The module's `result` is the literal negation `¬ claim`.

## Motivation

Ziętak's conjecture is a named published open problem. Grover–Gupta, “Properties of best approximations with respect to the Ky Fan p-k norm, and the strict spectral approximant of a matrix,” LAA 743 (2026), Theorem 3.7, restates the convergence question and proves the case min(m,n) ≤ 2. The present 3×3 settlement supplies a counterexample outside that range.

## Gap

The source's Conjecture 1.1 was open in preregistration issue #15746. The source and Grover–Gupta were checked for a prior counterexample; no settlement of the linear matrix-subspace statement was found in that literature screen. The Egger–Huotari (1989) vector witnesses were not readable, so their possible matrix-subspace relevance remains an ASSUMED-UNVERIFIED boundary.

## Route

Set A = I₃, H = [[1,0,1],[0,−2,0],[1,0,0]], E = Matrix.diagonal (Pi.single 2 1), and M = span_ℂ {H,E}. Every residual is R(s,t) = [[1+s,0,s],[0,1−2s,0],[s,0,t]]. The two leading diagonal bounds force s = 0 on the spectral-optimal face, and the lexicographic minimum on that face is t = 0, so E is a strict spectral approximant.

For every p > 1, a Schatten-p minimizer exists. Hermitian projection reduces a complex minimizer to the real comparison. A moving competitor and power estimates show that every minimizer eventually has real last residual entry below −1/4. This is separated from the strict residual's last entry 0, so the universal convergence claim fails.

## Falsifier

A proof that every admissible function of Schatten-p approximants converges to every strict spectral residual would falsify the result. For this instance, a minimizer with real last residual entry eventually at least −1/4, or a failure of the strict-minimality or minimizer-existence hypotheses, would falsify the supplied route.

## Evidence

The kernel-checked settlement is `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.lean`, with `result : ¬ claim` and standard axiom closure `{propext, Classical.choice, Quot.sound}`. The corresponding Scribe node carries `OpenProblemResolutionClaim` with `ResolutionKind.Refuted` for issue #15746.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The owner publications add no new theorem.

The numerical reading is the experiment entry [`docs/reports/zietak-2017-strict-spectral-polya-conjecture/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/2b5379616c9b15e648489b590d9b3dbacf9783a9/docs/reports/zietak-2017-strict-spectral-polya-conjecture), pinned to commit `2b5379616c9b15e648489b590d9b3dbacf9783a9`. Running `python3 check.py` exited 0 with final line `bad= 0`; the script SHA-256 is `770c269a194d78eb323be7dc404dcca70eef294006c008fbbb16506b9394581d`. The 3×3 samples are (q,c) ∈ {(2,1),(1.5,0.5),(3,2),(1.1,0.1)} at p ∈ {10,50,200,1000,3000}; each parameter pair also has 20,000 random complex disk tests, and each exponent has 200 local complex perturbation tests. The 4×4 samples are (q,c,δ) ∈ {(2,1,1/2),(3,2,1/4)} at the same exponents. These are finite computed readings, including t₃₀₀₀ < −0.99 for the 3×3 samples and |t₃₀₀₀ − (δ−1)| < 0.02 for the 4×4 samples.

## Triage

- **Proved in Lean — the refuted instance.** For q = 2 and c = 1, the strict spectral approximant is E, every p > 1 has a cₚ-approximant, and every such minimizer is eventually separated from E. The declarations are `strict_approximant`, `exists_cp_approximant`, `cp_minimizers_separated`, and `result`.
- **Proved in prose — coupling mechanism.** The strict residual diag(1,1,0) has a repeated leading singular-value cluster. H does not commute with E: (HE)₁₃ = 1 whereas (EH)₁₃ = 0. A finite-p optimizer can split that cluster while increasing the third residual magnitude. The uniform separation itself is kernel-checked by `real_minimizers_separated`; the mechanism description is an explanation of this construction.
- **Computed — family and limit readings.** The experiment checks the samples specified in Evidence. Its finite results support the proposed all-q>1,c>0 limit Bₚ → 2E; neither that all-parameter statement nor the exact limit is kernel-checked here.
- **Computed — 4×4 extension readings.** For A = diag(1,1,3δ/4,δ/4), 0 < δ < 1, and T = diag(0,0,1,−1), take M = span{H ⊕ 0,T}. The target is positive definite. The strict residual diag(1,1,δ/2,δ/2) is invertible, with strict approximant (δ/4)T. The tested finite-p values approach the proposed different limit (1−δ/4)T. The stated convergence for arbitrary δ,q,c remains unverified beyond the sampled values.
- **Literature — surviving special case.** Grover–Gupta Theorem 3.7 proves convergence for min(m,n) ≤ 2; this Refuted instance has min(m,n) = 3 and does not alter that theorem.
- **Proved in prose — fixed-competitor boundary.** Eventual comparison with each fixed competitor has quantifier order ∀X ∃p₀ ∀p≥p₀. It supplies no uniform threshold ∃p₀ ∀X ∀p≥p₀ for moving minimizers. Ziętak's 1997 fixed-competitor theorem therefore does not supply the uniform comparison needed for the conjecture.
- **Open — neighbouring questions.** Which subspaces satisfy the conjecture, including commuting subspaces, and the exact general limit of Bₚ remain unresolved.
- **Open — source dependence.** Ziętak's other statements that rely on Conjecture 1.1 require re-examination where they use convergence rather than a fixed-competitor result.

### What the settlement shows

The refutation applies to the universal linear-subspace claim by exhibiting a 3×3 subspace with a strict residual and uniformly separated finite-p minimizers. It does not refute the low-dimensional theorem or establish the exact general limit Bₚ → 2E; those are separate statements.

The proposed exact-limit route for all q > 1 and c > 0 uses stationarity. Write d = 1+sₚ, h = 1−qsₚ and let the coupled 2×2 block have eigenvalues λₚ and −bₚ. With rₚ = csₚ/(d+bₚ), the proposed identities are bₚ^(p−1) = λₚ^(p−1)rₚ² and λₚ^(p−1)(1−rₚ²+2crₚ) = qh^(p−1). If bₚ stays bounded below 1 along a subsequence, the first identity forces sₚ and rₚ to be exponentially small. Dividing the second identity by h^(p−1) then gives 1 = q in the limit, contradicting q > 1. This yields bₚ → 1 and tₚ → −1 once minimizer reality, the bounds, and these stationarity identities are established. Those obligations and the analogous unrestricted 4×4 limit are not proved by this module or by the finite experiment.

## ASSUMED-UNVERIFIED

The Egger–Huotari (1989) witnesses were not readable, so their possible realization by complex linear matrix subspaces is unverified. Literature completeness beyond the cited Ziętak and Grover–Gupta sources is not claimed.
