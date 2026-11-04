---
slug: critch-morton-2014-open-boundary-mps-marginal-birationality
bibkey: critchmorton2014mps
doi: 10.3842/SIGMA.2014.095
url: https://arxiv.org/abs/1210.2812v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.result
---

# Every three-site improper marginalization is birational for open-boundary binary bond-two MPS

## Problem

A. Critch and J. Morton, *Algebraic geometry of matrix product states*, SIGMA 10 (2014), 095, state Conjecture 8 in the source TeX `sigma14-095.tex`, lines 430–434:

> For $N\geq 4$, a~generic~$N$-qubit state can be recovered from its improper margina\-li\-zation to any three consecutive states.
> That is, each improper marginalization map $\overline\OB(2,2,N)\to\overline\OB(2,2,3)$ is
> a~birational equivalence of varieties.

The paper defines an open-boundary state by $\Psi_{i_1\dots i_N}=b_0^TA_{i_1}\cdots A_{i_N}b_1$ and defines $\overline\OB(2,2,N)$ as the Zariski closure of these states (source lines 349–363). Its improper marginalization sums amplitudes over all indices outside a chosen consecutive triple (lines 419–426). The Lean reading uses `closure n` for the affine zero locus of the vanishing ideal and `improperMarginal n a h` for this coherent amplitude sum, where $h:a+3\le n$.

## Motivation

The source's Theorem 7 identifies the three-site open-boundary binary bond-two model with a quartic hypersurface (lines 378–406). If every longer state can be recovered rationally from any consecutive three-site marginal, then the three-site algebraic model is an identifiable local chart for all lengths $n\ge4$. This concerns coherent amplitudes over $\mathbb C$; the map is not the reduced-density partial trace discussed separately in the source.

## Gap

The bounded check recorded in preregistration issue [#25722](https://github.com/the-omega-institute/trureturing/issues/25722) found no prior treatment of Conjecture 8 in the searched scope. Czapliński, Michałek and Seynnaeve, *Uniform matrix product states from an algebraic geometer's point of view* (arXiv:1904.07563), discuss Critch–Morton conjectures for uniform periodic MPS but not this open-boundary marginalization. The issue records searches of arXiv:2204.10363v3, 2212.13806v2, 2010.10653v1, 1803.08220v2, the OpenCitations records for the paper, and repository searches without a settlement. OpenAlex and Semantic Scholar citation endpoints returned HTTP 429 in that check, so those portions remain bounded and incomplete.

## Route

1. For every $n$, `parameter_image` identifies `openBoundaryMPS n` with the range of a polynomial parameterization. `polynomial_image_prime` applies to an arbitrary polynomial map `f : σ → MvPolynomial ι ℂ` with no extra hypothesis and identifies the vanishing ideal with the kernel of an evaluation homomorphism; the kernel is prime. `model_prime (n)` therefore proves `(vanishingPolys n).IsPrime`, which is used at both $n$ and $3$.

2. `quartic_parameter_identity` is an unconditional polynomial identity for the determinant of `kernelMatrix`. `quartic_image (t) (ht : t ∈ openBoundaryMPS 3)` transfers that identity to every parametrized three-site tensor. `quartic_closure (t) (ht : t ∈ closure 3)` then gives `MvPolynomial.eval t kernelMatrix.det = 0`. The unconditional `kernel_cramer_identity` gives the Cramer kernel vector. `chart_scalars (t) (hg : MvPolynomial.eval t chartPoly ≠ 0)` supplies the nonzero reconstructed basis and sum determinants and the corresponding scalar identities. `chart_reconstruction (t) (hquartic : MvPolynomial.eval t kernelMatrix.det = 0) (hg : MvPolynomial.eval t chartPoly ≠ 0)` uses those identities to reconstruct the three-site MPS and proves that the reconstructed sum matrix has nonzero determinant.

3. `chart_denominator (n) (t) (hg : MvPolynomial.eval t chartPoly ≠ 0)` proves the denominator used by `rationalInverse` is nonzero. `inverse_formula (n a) (hn : 4 ≤ n) (h : a + 3 ≤ n) (t) (hg : MvPolynomial.eval t chartPoly ≠ 0)` identifies that rational map with an MPS state whose boundaries contain the inverse powers of the reconstructed sum matrix. For arbitrary matrices and boundary vectors, `outside_sum (n a) (h : a + 3 ≤ n) (a₀ a₁) (b₀ b₁)` computes the improper marginal as the corresponding three-site state with the sum matrix powers on its two boundaries. Consequently, `inverse_on_chart (n a) (hn : 4 ≤ n) (h : a + 3 ≤ n) (t) (ht : t ∈ closure 3) (hg : MvPolynomial.eval t chartPoly ≠ 0)` proves nonzero denominator, membership of `rationalInverse n a t` in `closure n`, and exact recovery of $t$.

4. For uniqueness on the parametrized model, `triple_gauge (a₀ a₁) (l r) (hg : MvPolynomial.eval (mpsState 3 a₀ a₁ l r) chartPoly ≠ 0)` produces a nonzero scalar and an invertible gauge matrix relating the reconstructed matrices and boundary vectors to the original ones. With `hn : 4 ≤ n`, `h : a + 3 ≤ n`, `ψ ∈ openBoundaryMPS n`, and `hg : MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0`, `gauge_uniqueness_image (n a) (hn) (h) (ψ) (hψ) (hg)` proves `rationalInverse n a (improperMarginal n a h ψ) = ψ`. Finally, `uniqueness_closure (n a) (h : a + 3 ≤ n) (himage)` assumes `himage : ∀ ψ ∈ openBoundaryMPS n, MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0 → rationalInverse n a (improperMarginal n a h ψ) = ψ`; for `ψ ∈ closure n` with `MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0`, it proves both nonzero denominator and equality with `ψ`.

5. `chart_nonempty` proves that some three-site state in `closure 3` has nonzero `chartPoly`. The theorem `result` combines this witness, `inverse_on_chart`, `gauge_uniqueness_image`, and `uniqueness_closure` to establish `claim` for every $n,a$ with $4\le n$ and $a+3\le n$.

## Falsifier

The settlement would not address the source conjecture if the formal model used a different state or map. The module uses independent complex $2\times2$ matrices and two complex boundary vectors, the affine closure of that parametrized amplitude set, and a sum over all words whose selected consecutive triple equals the target word. It does not use a density matrix, a partial trace, a phase quotient, periodic boundary conditions, or larger bond or physical dimension; $n=3$ appears only as the three-site target, while the recovered source length is required to satisfy $n\ge4$. The formal result is the explicit `IsBirationalVia` formulation with polynomial $g,q,p$, nonempty chart, both rational-inverse identities, and the two primeness assertions; a claim of global recovery outside the nonzero chart would be a different statement.

## Evidence

The canonical source is `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality.lean.json`.

Declaration statements:
- `result`: `sha256:2a81251654d9fb0a56c39929a01cf0a6860094493d2d6b1e3ea40e1523d357b3`;
- `claim`: `sha256:b83408a88775ac353e9cdd99a9abc4f49f3422f94672129c37704dcf7418eb86`.

- **Proof.** The module contains the compiled declaration `result : claim`.
- **Axioms.** `#print axioms` on `result` reports `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom in the module.

## Triage

Tier 1 conjecture of Critch and Morton (2014), preregistered in issue #25722 before any Lean; `theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every $n,a\in\mathbb N$ with $4\le n$ and every $h:a+3\le n$, `(vanishingPolys n).IsPrime` and `(vanishingPolys 3).IsPrime` hold, and `IsBirationalVia n a h` holds. Thus there exist $g,q\in\operatorname{MvPolynomial}(\operatorname{Fin}3\to\operatorname{Fin}2,\mathbb C)$ and $p:(\operatorname{Fin}n\to\operatorname{Fin}2)\to\operatorname{MvPolynomial}(\operatorname{Fin}3\to\operatorname{Fin}2,\mathbb C)$ such that some $\psi\in\mathrm{closure}(n)$ has $g(\operatorname{improperMarginal}(\psi))\ne0$; every $t\in\mathrm{closure}(3)$ with $g(t)\ne0$ has $q(t)\ne0$, the state $w\mapsto p(w)(t)/q(t)$ lies in `closure n`, its marginal has nonzero $g$-value, and its marginal equals $t$; and every $\psi\in\mathrm{closure}(n)$ whose marginal has nonzero $g$-value has nonzero $q$ at that marginal and is recovered by the same rational formula. These are exactly the clauses of `IsBirationalVia`; no assertion about points outside the stated chart is made.

**Computed, not formalized:** None.

**Argued, not formalized.** The usual geometric reading of `IsBirationalVia` as a birational equivalence uses the prime ideals and the nonempty principal chart to obtain dense open subsets; that translation to the conventional variety-theoretic definition is not a separate Lean declaration. The exceptional locus where `chartPoly` vanishes is not classified, and whether a larger chart or a simpler exceptional-set description exists remains open. The source's nearby reduced-density conjecture for an open-boundary three-site reduced density operator (lines 443–458) is a different map involving conjugation and phase and is neither proved nor refuted here; the periodic four-site reduced-density conjecture (lines 460–463) is also outside the result. The source's hidden-Markov-model analogy and any extension to other bond or physical dimensions are not consequences of this declaration. No source statement relying on a reduced-density or periodic interpretation is settled by this result.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and citation routes recorded in issue #25722; it does not establish exhaustive worldwide novelty or priority. The issue's reports on the cited arXiv papers, OpenCitations, and web searches are accepted as bounded records, while the OpenAlex and Semantic Scholar endpoint results were rate-limited. The term-by-term identification of `kernelMatrix.det` with the displayed 22-term polynomial in Critch and Morton (2014), and the conventional algebraic-geometric equivalence between the `IsBirationalVia` formulation and the phrase “birational equivalence of varieties,” are not separately formalized declarations. The exceptional chart, reduced-density questions, periodic boundary case, and higher dimensions remain unverified here.
