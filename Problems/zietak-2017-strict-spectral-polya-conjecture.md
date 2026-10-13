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

The numerical reading is the experiment entry [`docs/reports/zietak-2017-strict-spectral-polya-conjecture/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/2b5379616c9b15e648489b590d9b3dbacf9783a9/docs/reports/zietak-2017-strict-spectral-polya-conjecture), pinned to commit `2b5379616c9b15e648489b590d9b3dbacf9783a9`. Running `python3 check.py` exited 0 with final line `bad= 0`; the script SHA-256 is `770c269a194d78eb323be7dc404dcca70eef294006c008fbbb16506b9394581d`. Its tested scope covers the strict face, the 3×3 parameter samples, and the stated 4×4 extension; these readings are computed evidence.

## Triage

- **Proved in Lean — the refuted instance.** For q = 2 and c = 1, the strict spectral approximant is E, every p > 1 has a cₚ-approximant, and every such minimizer is eventually separated from E. The declarations are `strict_approximant`, `exists_cp_approximant`, `cp_minimizers_separated`, and `result`.
- **Proved in Lean — failure mechanism.** The repeated leading singular-value cluster is split by the off-diagonal coupling in H, which does not commute with E; `real_minimizers_separated` supplies the uniform separation estimate.
- **Computed — family and limit readings.** The experiment checks q,c samples and the 4×4 positive-definite extension at the ranges recorded by `check.py`. It does not prove the all-q,c limit or a general 4×4 theorem.
- **Open — surviving special case.** Grover–Gupta's min(m,n) ≤ 2 convergence theorem remains outside this refuted 3×3 instance.
- **Open — neighbouring questions.** Which subspaces satisfy the conjecture, including commuting subspaces, and the exact general limit of Bₚ remain unresolved.
- **Open — source dependence.** Ziętak's other statements that rely on Conjecture 1.1 require re-examination where they use convergence rather than a fixed-competitor result.

### What the settlement shows

The refutation applies to the universal linear-subspace claim by exhibiting a 3×3 subspace with a strict residual and uniformly separated finite-p minimizers. It does not refute the low-dimensional theorem or establish the exact general limit Bₚ → 2E; those are separate statements.

## ASSUMED-UNVERIFIED

The Egger–Huotari (1989) witnesses were not readable, so their possible realization by complex linear matrix subspaces is unverified. Literature completeness beyond the cited Ziętak and Grover–Gupta sources is not claimed.
