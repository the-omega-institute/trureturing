---
slug: camilo-landi-eliens-2019-fermionic-gaussian-renyi-strong-subadditivity
bibkey: camilolandieliens2019renyissa
doi: 10.1103/PhysRevB.99.045155
url: https://arxiv.org/abs/1810.07070v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.result
---

# Strong subadditivity of fermionic Gaussian Rényi entropy for $0<\alpha<1$

## Problem

G. Camilo, G. T. Landi and S. Eliëns, *On the Strong Subadditivity of the Rényi entropies for bosonic and fermionic Gaussian states*, arXiv:1810.07070v2 (Phys. Rev. B 99, 045155, 2019), Section IV.B, `RenyiGaussian_v2.tex`, line 498:

> Again, we lack a formal proof for SSA to hold for $\alpha \in [0,1]$, but we conjecture it to be true.

The covariance condition and entropy formula are in Section II.B, lines 265–285 and Eq. `renyi_fermionic_1`, lines 297–301; the conditional mutual information is Eq. `RCMI`, lines 122–125. These locators refer to the v2 TeX source, md5 `760f1a7a3c5020d2403ae875d5cdf1eb`.

Issue [#26328](https://github.com/the-omega-institute/trureturing/issues/26328) fixes the following reading. For every $n\in\mathbb N$, let $\Gamma$ be a real matrix indexed by $\mathrm{Fin}\,n\times\mathrm{Fin}\,2$, with $\Gamma^{\mathsf T}=-\Gamma$ and every eigenvalue of the Hermitian matrix $i\Gamma$ in $[-1,1]$. For a mode set $X$, retain both Majorana indices of each selected mode to obtain the principal block $\Gamma_X$. Define

$$S_\alpha(\Gamma_X)=\frac{1}{2(1-\alpha)}\sum_{k=1}^{2|X|}\ln\left[\left(\frac{1+\lambda_k}{2}\right)^\alpha+\left(\frac{1-\lambda_k}{2}\right)^\alpha\right],$$

where the $\lambda_k$ are all the eigenvalues of $i\Gamma_X$, with multiplicity, and the empty sum is zero. For every three pairwise disjoint mode sets $A,B,C$ and every $0<\alpha<1$, the claim is

$$S_\alpha(\Gamma_{A\cup B})+S_\alpha(\Gamma_{B\cup C})\ge S_\alpha(\Gamma_{A\cup B\cup C})+S_\alpha(\Gamma_B).$$

This open-interval covariance statement is proved. The endpoint orders and the construction of a Fock-space density operator are outside the Lean claim.

## Motivation

The source introduces the entropy combination in Eq. `RCMI` to quantify conditional correlations, but its nonnegativity requires strong subadditivity. The conjecture identifies a fermionic Gaussian range where that necessary condition survives despite the failure of Rényi strong subadditivity for general states. Proving the covariance inequality replaces the numerical evidence for this range by a uniform statement in the number of modes and the subsystem sizes.

## Gap

The bounded literature check recorded in #26328 and its companion [#26322](https://github.com/the-omega-institute/trureturing/issues/26322) reports:

- The v2 source retains the fermionic conjecture.
- The search worker's readings of 14 of the 20 INSPIRE citing records, restricted to records with arXiv versions, found no proof of the fermionic interval.
- Ferro–Pfeiffer–Spitzer, arXiv:2404.07068, Section 4.1, was reported as prior art for a scalar integral representation, without this SSA conclusion; that comparison is `ASSUMED-UNVERIFIED`.
- The preregistration's repository search found no existing dossier or settlement of this conjecture.

`not-found-in-searched-scope`. The source conjecture was checked directly; the reported citing-paper readings are not independently reproduced.

## Route

Write $K_u(G)=I+iuG$. The scalar definitions and the lemmas `weight_pos` and `stieltjes_representation` below belong to `D5/S3/Quantum/Analysis/FermionicRenyiStieltjes`; `log_koteljanskii` belongs to `D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity`. The other named lemmas belong to the settlement module.

1. **Physical principal blocks and positive interpolation.** For any physical covariance $\Gamma$ and any mode set $X$, `reduced_physical` gives antisymmetry of $\Gamma_X$ and a Hermiticity witness for $i\Gamma_X$ whose eigenvalues have absolute value at most one. For a real matrix $G$ on any finite index type, a Hermiticity witness $h$ for $iG$, the bound $|\lambda_k(h)|\le1$ for every eigenvalue, and $0\le u<1$, `interpolation_posDef` gives $K_u(G)>0$.
2. **The logarithmic determinant.** For a real antisymmetric matrix $G$ on any finite index type, a Hermiticity witness $h$ for $iG$, $|\lambda_k(h)|\le1$ for every eigenvalue, and $0\le u<1$, `determinant_log_identity` gives
   $\ln\det K_u(G)=\tfrac12\sum_k\ln(1-u^2\lambda_k(h)^2)$.
   The determinant is a positive real number under these hypotheses; Lean uses its real part. The proof uses transposition to equate the determinants at $u$ and $-u$, without requiring an explicit pairing of eigenvalues.
3. **Positive scalar mixture.** For $0<\alpha<1$, $|\sigma|\le1$, `stieltjes_representation` proves integrability of the displayed integrand and
   $e_\alpha(\sigma)=\ln2+\int_0^1v_\alpha(u)\ln(1-u^2\sigma^2)\,du$,
   where $e_\alpha$ is `fermionicRenyiFunction` and

   $$v_\alpha(u)=\frac{2\alpha\sin(\pi\alpha)(1-u^2)^{\alpha-1}}{\pi(1-\alpha)\left[(1+u)^{2\alpha}+(1-u)^{2\alpha}+2(1-u^2)^\alpha\cos(\pi\alpha)\right]}.$$

   For $0<\alpha<1$ and $0\le u<1$, `weight_pos` proves $v_\alpha(u)>0$. The scalar representation includes $\sigma=0$ and $\sigma=\pm1$.
4. **Entropy mixture.** For a physical covariance $\Gamma$, any mode set $X$, and $0<\alpha<1$, `entropy_mixture` proves both integrability on $(0,1)$ and
   $S_\alpha(\Gamma_X)=|X|\ln2+\int_0^1v_\alpha(u)\ln\det K_u(\Gamma_X)\,du$.
   In this identity the integral is with respect to Lebesgue measure restricted to $(0,1)$.
5. **A common determinant inequality.** For a complex positive definite matrix $H$ and three pairwise disjoint finite index sets, `log_koteljanskii` bounds the sum of the $ABC$ and $B$ principal log determinants by the sum for $AB$ and $BC$, including empty blocks. Apply it to the same $K_u(\Gamma)$ for $0\le u<1$ and to the Majorana sets of the pairwise disjoint mode sets $A,B,C$. For any mode set $X$, Majorana index set $Y$ satisfying $p\in Y\iff p.1\in X$ for every $p$, and real $u$, `mode_interpolation_det` identifies the determinant of the $Y$ principal block of $K_u(\Gamma)$ with $\det K_u(\Gamma_X)$.
6. **Integration and cancellation.** For physical $\Gamma$, pairwise disjoint $A,B,C$, and $0<\alpha<1$, `settlement_main` multiplies the pointwise inequality by the nonnegative weight and integrates using the four integrability conclusions of `entropy_mixture`. The identity $|A\cup B|+|B\cup C|=|A\cup B\cup C|+|B|$ cancels the constants. `result : claim` is this conclusion.

## Falsifier

A physical covariance, pairwise disjoint mode sets and an order $0<\alpha<1$ with a negative displayed entropy difference would contradict `claim`. The source-to-formal correspondence also matters:

- `physicalCovariance` requires real antisymmetry and the full Hermitian spectral bound, including pure modes with eigenvalues $\pm1$.
- `fermionicGaussianRenyiEntropy` is half the sum over the complete Majorana spectrum; `fermionicRenyiFunction` unfolds to the binary Rényi formula in the Problem section. The factor one half agrees with Eq. `renyi_fermionic_1`, since the scalar function is even and each mode contributes two opposite eigenvalues, as described in the source at lines 279–320.
- `reducedCovariance` takes a principal block retaining both Majorana indices, rather than an independently chosen covariance for each subsystem.
- The entropy definition assigns zero to non-Hermitian inputs, but `reduced_physical` excludes that branch for every block in `claim`. Empty blocks have zero entropy; neither nonempty blocks nor strict mixedness are hypotheses.

The covariance-to-density-operator correspondence is a source-level interpretation, not a separate Lean theorem in this settlement. Numerical violations outside $0<\alpha<1$ do not contradict `result`.

## Evidence

The canonical source is `D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity.lean.json`.

Declaration statements:

- `result`: `sha256:1b4b0e4fee05f0fc3a14647392ac5b408b11a556ea13059095b3278bff3e4e7d`;
- `claim`: `sha256:3660c22e35b91f1774aacf94498881eb095b5b87fd2c4e6cdbb7457a883406ce`.

## Triage

Tier 1 conjecture of a 2018 preprint published in 2019, preregistered in issue #26328 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural number of modes, every real antisymmetric covariance whose Hermitian matrix $i\Gamma$ has all eigenvalues in $[-1,1]$, every three pairwise disjoint mode sets $A,B,C$, and every real order $0<\alpha<1$, the covariance entropies of $A\cup B$ and $B\cup C$ sum to at least those of $A\cup B\cup C$ and $B$.

**Computed, not formalized.** None.

**Argued, not formalized.**

- *Decisive mechanism and scope.* For a real antisymmetric covariance with Hermitian spectrum in $[-1,1]$, `interpolation_posDef` makes $I+iu\Gamma$ positive definite for $0\le u<1$; for such a physical covariance, any mode set $X$ and $0<\alpha<1$, `entropy_mixture` supplies an integrable positive-weight mixture of its principal log determinants. Thus the lack of positivity of $\Gamma$ itself, identified by the source at lines 495–496, is avoided by the positive interpolation. Eigenvalues $\pm1$ are allowed, so strict mixedness is unnecessary.
- *Endpoint limits.* Put $p=(1+\lambda)/2\in[0,1]$. As $\alpha\to0^+$, the single-eigenvalue entropy tends to $\ln2$ when $0<p<1$, and to zero when $p=0$ or $p=1$. As $\alpha\to1^-$, differentiating $\ln(p^\alpha+(1-p)^\alpha)$ at one gives the limit $-p\ln p-(1-p)\ln(1-p)$, with zero endpoint terms. Each block has a finite spectrum, so taking these limits in its finite entropy sum and in the four-term inequality preserves nonnegativity. This gives endpoint extensions of the covariance formula; the limits, their identification with log rank and von Neumann entropy of a density operator, and endpoint SSA are not formalized by `result`.
- *Sharpness in value.* At $\Gamma=0$, all eigenvalues of every reduced covariance vanish, each mode contributes $\ln2$, and the cardinality identity in Route makes the entropy difference zero. Thus a strictly positive universal lower bound on this difference cannot replace zero. This does not determine sharpness of the order interval: whether violations occur for every $\alpha>1$, especially in the source's unresolved window $1<\alpha\lesssim1.3$, remains open here.
- *Neighbouring statement.* Setting $B=\varnothing$ reduces the displayed inequality to subadditivity for disjoint $A,C$ at $0<\alpha<1$, because the empty entropy is zero. This is within the source's already established fermionic subadditivity range and does not establish any extension beyond it.
- *Effect on the paper.* The fermionic nonnegativity conjecture for Eq. `RCMI` in Section IV.B and the fermionic part of the request in Final remarks, line 532, obtain a covariance proof on the open interval. This supplies the nonnegativity needed for the proposed conditional-correlation expression there; it does not establish further axioms of a correlation measure. The source's separate subadditivity conclusions do not depend on this conjecture. The bosonic conjecture, the exact fermionic violation threshold, and extensions to non-Gaussian states or tensor-network classes are not settled by this result.

## ASSUMED-UNVERIFIED

The bounded literature check is `not-found-in-searched-scope`, not exhaustive worldwide novelty or priority. The 14 citing-paper readings and the Ferro–Pfeiffer–Spitzer scalar-prior-art comparison are reports attributed to the search worker in #26328 and #26322; those readings are not independently reproduced.

The covariance-to-Fock-space density-operator construction, its entropy and reduction correspondence, the endpoint-limit arguments, sharpness example and other arguments labelled above are not separately formalized in this settlement. The order-zero endpoint uses a limit, not substitution of $\alpha=0$ into Lean's totalized real-power formula. No formal conclusion here identifies the optimal upper order threshold or settles any order above one.
