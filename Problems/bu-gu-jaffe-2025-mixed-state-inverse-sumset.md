---
slug: bu-gu-jaffe-2025-mixed-state-inverse-sumset
bibkey: bugujaffe2025ruzsa
doi: 10.1109/TIT.2025.3543276
url: https://arxiv.org/abs/2401.14385v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.result
---

# The Bu–Gu–Jaffe mixed-state quantum inverse sumset bound is false

## Problem

K. Bu, W. Gu and A. Jaffe, *Quantum Ruzsa Divergence to Quantify Magic*, IEEE Transactions on Information Theory 71(4) (2025) 2726–2740, DOI 10.1109/TIT.2025.3543276; arXiv:2401.14385v3, Remark 45, equation (58). The v3 source `IEEE_Final_BGJ.tex`, line 2106, states verbatim:

> In addition, we also expect that the property (2) in Theorem \ref{thm:QIST} holds, which  has the following form

The reference is to Theorem 44. Its proposed mixed-state inequality, at lines 2107–2109, is

$D(\rho\|\mathcal M(\rho))\leq\dfrac{\log R(\rho)}{\log R(\rho)-\log[1+\lambda(R(\rho)\operatorname{Tr}[\rho^2]-1)]}\log C.\qquad(58)$

Here $R(\rho)=\operatorname{rank}\mathcal M(\rho)$ and $\lambda=(1-MG(\rho))^2$. The characteristic function is $\Xi_\rho(p,q)=\operatorname{Tr}[\rho w(-p,-q)]$; the mean state retains exactly its coefficients of modulus one. The magic gap $MG$ is one minus the largest modulus among the nonzero coefficients whose modulus is not one, with $MG=0$ if that finite set is empty. The source definitions and their locations are in [the literature note](../Library/Divergence/bugujaffe2025ruzsa.md).

Issue [#24984](https://github.com/the-omega-institute/trureturing/issues/24984) fixes the single-qudit reading encoded by `claim`: for every nonzero prime dimension $d$, every nonzero $s,t\in\mathbb Z_d$ with $s^2+t^2=1$, every three density matrices $\rho,\sigma,\tau$ with $\sigma=\mathcal M(\rho)$ and $\tau=\rho\boxtimes_{s,t}\rho$, and every real $C$, require (58) whenever

$1<\delta_q[\rho]=\exp(S(\tau)-S(\rho))\leq C,\qquad A=1+\lambda(R(\rho)\operatorname{Tr}[\rho^2]-1)>0,\qquad\log R(\rho)-\log A>0.$

Density matrices are positive semidefinite complex matrices of trace one. Entropy and relative entropy are the natural-logarithm trace expressions $S(\rho)=-\operatorname{Tr}(\rho\log\rho)$ and $D(\rho\|\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$. The two positivity assumptions restrict to a positive logarithm argument and denominator. This restriction of the expected universal bound is refuted.

## Motivation

The quantum inverse sumset problem asks how the entropy increase under self-convolution controls distance to the mean state. Bu, Gu and Jaffe (2025, arXiv:2401.14385v3, Theorem 44) give the corresponding bound for pure states; Remark 45 proposes the purity-dependent mixed-state extension (58). Its validity would make the quantum-doubling constant a quantitative control on relative entropy to the mean state for mixed inputs as well.

## Gap

The literature check before any Lean is recorded in #24984:

- The v3 source retains the expectation and gives only the weaker mixed-state estimate (59).
- The orchestrator reports a Semantic Scholar listing of 15 citing records and TeX searches of arXiv:2607.16653, arXiv:2609.40211 and arXiv:2610.38401 without finding a proof or counterexample to (58); the remaining records were screened by the search contributor.
- The orchestrator reports web searches for the mixed-state inverse sumset bound and a quantum-doubling counterexample, a Zenodo query returning no records for the quantum-doubling constant, and no related repository record.

`not-found-in-searched-scope`.

## Route

All witness identities below concern only $d=7$, $s=t=2$, and the fixed density matrices

$\rho=\tfrac12(|0\rangle\langle0|+|1\rangle\langle1|),\qquad\sigma=I/7,\qquad\tau=\tfrac14|0\rangle\langle0|+\tfrac12|2\rangle\langle2|+\tfrac14|4\rangle\langle4|.$

The parameters are nonzero and satisfy $2^2+2^2=1$ in $\mathbb Z_7$. Choose $C=\exp(\tfrac12\log2)$.

1. **Convolution and doubling.** `convolution_eq` identifies $\rho\boxtimes_{2,2}\rho=\tau$. The witness-specific lemmas `rho_entropy` and `tau_entropy` give $S(\rho)=\log2$ and $S(\tau)=\tfrac32\log2$. Thus `doubling_eq` and `doubling_gt_one` give $\delta_q[\rho]=C>1$.
2. **Mean state and divergence.** For $p,q\in\mathbb Z_7$ with $q\ne0$, `characteristic_off_axis` gives $\Xi_\rho(p,q)=0$; for every $p\in\mathbb Z_7$, `characteristic_axis` gives $\Xi_\rho(p,0)=(1+\omega_7^{-p})/2$. For every $x\in\mathbb Z_7^2$, `characteristic_norm_one` gives $|\Xi_\rho(x)|=1$ exactly when $x=(0,0)$. The witness-specific lemmas `mean_eq`, `rank_eq`, `purity_eq`, `divergence_eq` and `gap_bounds` give $\mathcal M(\rho)=\sigma$, $R(\rho)=7$, $\operatorname{Tr}\rho^2=1/2$, $D(\rho\|\sigma)=\log7-\log2$, and $0\leq\lambda\leq1$.
3. **Positive domain and upper bound.** For every real $\ell$ with $0\leq\ell\leq1$, `numerical_bound` proves that $A_\ell=1+\ell(7/2-1)>0$, that $\log7-\log A_\ell>0$, and that $\dfrac{\log7}{\log7-\log A_\ell}\log(\exp(\tfrac12\log2))\leq\tfrac12\log7$. Apply it with $\ell=\lambda$ using `gap_bounds`.
4. **Contradiction.** `strict_violation` proves $\tfrac12\log7<\log7-\log2$. Specializing `claim` to these parameters, density matrices and $C$ contradicts this inequality, giving `result : ¬ claim`.

## Falsifier

The refutation would not settle the expectation if its operators or quantifiers differed from the source's. The module uses:

- `weyl` with the source's clock-before-shift phase convention at the odd prime $d=7$, and `charFun` with the negative Weyl argument;
- `meanState` as the Weyl reconstruction of precisely the modulus-one coefficients, `meanRank` as its matrix rank, and `magicGap` with the source's empty-set convention;
- `convolution` as conjugation by $U_{s,t}|i,j\rangle=|si+tj,-ti+sj\rangle$ followed by the partial trace over the right factor;
- `purity` as the real trace of the square, and explicit density matrices representing both the mean state and self-convolution in `claim`.

The Lean entropy, relative-entropy and purity definitions take the real parts of the corresponding traces. The witness meets both positivity assumptions. Its mean state is full rank, so the relative-entropy trace expression agrees with the usual relative entropy without a support singularity. The module does not formalize the paper's separate qubit convolution.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:21b6f50ff1013ead15ef520161f922bab856802a0389e37209bdf7b271714bce`;
- `claim`: `sha256:6477d91091fb1a86b0a2e75254409afc6a4199375db3e460132493b918ee900f`.

## Triage

Tier 1 expectation in a remark of a 2025 journal paper, preregistered in issue #24984 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal single-qudit inequality `claim`, with exactly the parameter, density-matrix, doubling and positivity hypotheses stated in Problem, is false.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Failure mechanism.* At the fixed seven-dimensional witness, `numerical_bound` applies for every real $\ell\in[0,1]$ and `gap_bounds` puts its actual gap factor in that interval: no more precise choice of the magic gap can overcome the upper bound $\tfrac12\log7$, which `strict_violation` puts below the witness divergence. The state is diagonal by its definition, and `convolution_eq` identifies its convolution with the diagonal state $\tau$, so noncommutativity is unnecessary for this obstruction.
- *The missing entropy correction.* Write $x=\log R$, $y=\log R-\log A$ and $a=S(\rho)$. The source's estimate (59) uses $(x-a)/(y-a)$ instead of $x/y$, on the additional domain $y>a$. For $x\geq y>a\geq0$, their difference is $a(x-y)/(y(y-a))\geq0$. Removing the entropy term from both numerator and denominator therefore demands a stronger estimate; the purity term inside $A$ does not supply that estimate. Retaining (59), with its stricter denominator condition, avoids the claimed strengthening. Restricting to pure states sets $a=0$ and purity to one, recovering the source's Theorem 44; neither source result is formalized here.
- *Parameter scope.* For the equal mixture of levels zero and one at an odd prime dimension, the four equally likely left outputs are $0,s,t,s+t$. If nonzero admissible parameters satisfy $s=t$ or $s=-t$, there are three distinct outputs with weights $1/4,1/2,1/4$, so the doubling constant is $\sqrt2$. If $s\ne t$ and $s\ne-t$, all four outputs are distinct and the doubling constant is $2$. Consequently the preregistration's extension of the $\sqrt2$ argument to every admissible pair in every prime dimension is not justified; it does not follow from the formal refutation. Whether a different mixed-state bound holds uniformly on the unequal-parameter subfamily is open here.
- *Effect on the paper.* Equation (58) cannot serve as a universal mixed-state bound, including in the source's multi-qudit formulation, which includes the single-qudit case. The subsequent quantum-doubling corollary is proved from the quantum Ruzsa-divergence properties, and the later balanced-convolution comparison is conditional on the separate convolutional strong-subadditivity conjecture; neither argument uses (58). This refutation does not settle that separate conjecture, the qubit bounds or the Rényi versions.

## ASSUMED-UNVERIFIED

The bounded literature check in #24984 does not establish exhaustive worldwide novelty or priority. Its citing-paper readings, external search results and repository-search readings were not independently reproduced. The source conjecture and definitions were checked in the v3 TeX; the journal PDF was not compared independently. The statements in “Argued, not formalized” are not additional Lean results. In particular, the exact trigonometric value of the gap factor, other dimensions and other convolution parameters are not asserted by `result`; the preregistration's extension to every admissible pair in every prime dimension holds only for $s=\pm t$ and is corrected in a comment on #24984. A corrected uniform mixed-state replacement beyond the source's (59) remains open here.
