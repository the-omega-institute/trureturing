---
slug: graydon-skanes-norman-wallman-2022-qutrit-stochastic-unitality
bibkey: graydon2022stochastic
doi: null
url: https://arxiv.org/abs/2201.07156v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.result
---

# A stochastic qutrit channel that is not unital

## Problem

M. Graydon, J. Skanes-Norman and J. J. Wallman, *Designing Stochastic
Channels*, arXiv:2201.07156v1, Section II, ask:

> We leave open the question of whether or not all stochastic channels are unital for d = 3.

Eq. (2) defines the normalized Choi state
$J(\Phi)=d^{-1}(\Phi\otimes\mathrm{id})(\operatorname{col}(I_d)
\operatorname{col}(I_d)^\dagger)$. Eq. (11) requires that $\Phi$ be
completely positive and trace preserving and that
$J(\Phi)\operatorname{col}(I_d)=\lambda\operatorname{col}(I_d)$ for
some real $0<\lambda\leq1$. Unitality means $\Phi(I_d)=I_d$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Complex-linear maps on qutrit matrices | `claim` quantifies over `MatrixMap (Fin 3) (Fin 3) ℂ` | Exact dimension and carrier |
| CPTP | Frozen `CoPRelativeQuantumnessRefutation.IsCPTP` within `IsStochastic` | Complete positivity and trace preservation on every matrix |
| Some real $0<\lambda\leq1$ | The existential real parameter and both inequalities in `IsStochastic` | No endpoint or sign clause dropped |
| Normalized Choi state and identity vector | Their preregistered bodies are inlined in `IsStochastic` | Output-first Choi coordinates; vector entries are one exactly on equal indices |
| Every stochastic channel is unital | The implication in `claim` concludes $\Phi(I_3)=I_3$ | Literal universal question |
| Refutation | `result` has type `¬ claim` | A counterexample suffices |

The definition also admits dimension zero as a total Lean expression; the
question and its refutation use dimension three. Proofs use the existing
`ProductUnitaryChoiSpectrum.omega` and
`PassiveMemoryNonclassicalRefutation.choi`, with correspondence by unfolding.

## Motivation

The source supplies a nonunital example at dimension four and every even
dimension greater than two, and Appendix A proves unitality at dimension
two. The qutrit case separates the identity-vector Choi eigen-condition
from preservation of the identity matrix.

## Gap

Preregistration [#16492](https://github.com/the-omega-institute/trureturing/issues/16492)
records a Tier-1 published open question. Its source and citation screen
are attributed to the Claude Code orchestrator: all seven citing works
2512.23586, 2306.07418, 2402.07866, 2607.04584, 2305.16507,
2205.11512 and 2108.11343 were read, and none answers the dimension-three
question. Completeness beyond that citation graph is
`ASSUMED-UNVERIFIED`. The independent implementation search finds no
repository owner of this settlement in its searched revision and scope.

## Route

For zero-based matrix units $E_{ij}$, use the four Kraus matrices
$K_0=I_3/\sqrt2$,
$K_1=\operatorname{diag}(1,-1/2,-1/2)/\sqrt2$,
$K_2=\sqrt{3/8}E_{01}$ and $K_3=\sqrt{3/8}E_{02}$.
The private `phi_eq_kraus` identifies the rational-entry channel with
`MatrixMap.of_kraus K K`. The private `phi_cptp` applies
`MatrixMap.of_kraus_isCompletelyPositive` and uses `Matrix.trace_mul_cycle`
with the right Gram sum equal to the identity. The private
`phi_choi_eigen` proves the normalized Choi eigen-equation at $\lambda=1/2$.
The private `phi_one_entry` proves $(\Phi(I_3))_{00}=7/4$ and
`phi_not_unital` turns this entry into failure of unitality. Their public
consumer is `result`.

## Falsifier

The claim would force the same explicitly stochastic map to preserve
$I_3$, contradicting $7/4\ne1$ at entry $(0,0)$. The witness has all the
source's hypotheses; it does not use a zero eigenvalue, a nonpositive map
or a failure of trace preservation.

## Evidence

The Lean module and its Blueprint mirror are
`D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.lean` and
`Blueprint/D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.scribe.cs`.
The settling declaration is
`D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.result`.
Its admission basis is `open-problem-resolution (#16492; Refuted)` and
its utility is `certified-instance` under `basis=refutes`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The pinned experiment is
[the qutrit stochastic-unitality check](https://github.com/the-omega-institute/trureturing-experiments/tree/2ac17ecf92b83b478dca03d792bc99389146d327/docs/reports/graydon-skanes-norman-wallman-2022-qutrit-stochastic-unitality).
Command from that repository: `python3 docs/reports/graydon-skanes-norman-wallman-2022-qutrit-stochastic-unitality/check.py`.
Exit code: 0; final result: `ALL_OK`.
Script SHA-256: `3c0510bbe9082cb8af6d31194916deb0db15ecf7ec74e6b1c3ac2954db68b187`.
The exact rational tested scope is $d=3,4,5,6,7,8$ and
$\lambda\in\{1/2,1/3,9/10\}$, eighteen cases. The check establishes the
right Gram identity, traceless error operators, the Choi eigenvalue and
nonunitality in those cases; at $(d,\lambda)=(3,1/2)$ its output diagonal
is $(7/4,5/8,5/8)$. No experiment program is embedded here.

## Triage

### What the settlement shows

- **Mechanism, kernel-checked at $d=3$, $\lambda=1/2$.**
  `phi_cptp`, `phi_choi_eigen`, `phi_one_entry`, `phi_not_unital` and
  their public consumer `result` check a CPTP stochastic qutrit map that
  is not unital. The mechanism is explained by
  $J(\Phi)\operatorname{col}(I)=d^{-1}\sum_k
  \operatorname{col}(K_k)\overline{\operatorname{Tr}K_k}$:
  the Choi eigen-condition sees only the traces of the Kraus matrices.
  In the counterexample the error matrices are traceless, but
  $E_{0j}^\dagger E_{0j}=E_{jj}$ and
  $E_{0j}E_{0j}^\dagger=E_{00}$ place completeness weight on columns
  and unitality weight on row zero. These general explanatory identities
  are prose calculations; they are not additional public Lean theorems.
- **Why dimension two differs, source-attested.** Appendix A, Theorem 5
  proves stochastic qubit unitality. The $SU(2)$ two-complex-parameter
  conjugate pairing (A5) yields (A7) and (A8). For nonzero parameters,
  (A9) forces $-\kappa_z^2=\kappa_x^2+\kappa_y^2$, hence all real
  translations vanish; the zero-parameter cases are handled there too.
  A general $SU(3)$ matrix has no corresponding two-parameter pairing,
  so this argument supplies no qutrit conclusion. No qubit theorem is
  added to this Lean module.
- **Family, computed in the experiment's finite scope.** Put $m=d-1$,
  $D=\operatorname{diag}(1,-1/m,\ldots,-1/m)$ and
  $c^2=1-1/m^2$. The proposed family is
  $\Phi=\lambda\mathrm{id}+(1-\lambda)\Psi_d$, where
  $\Psi_d(X)=DXD+c^2\sum_{j=1}^{d-1}E_{0j}XE_{j0}$.
  The experiment checks the eighteen cases stated in Evidence, giving
  $\Phi(I)=\operatorname{diag}(1+(1-\lambda)(m-1/m),
  \lambda+(1-\lambda)/m^2,\ldots)$.
  The all-$d\geq3$, all-$0<\lambda<1$ extension is **open as a Lean
  formalization**; neither the finite computation nor `result` certifies
  that uniform extension.
- **What survives, computed analytically in prose.** For a finite Kraus
  representation of a CPTP map by normal matrices,
  $K_kK_k^\dagger=K_k^\dagger K_k$ for each $k$, and therefore
  $\Phi(I)=\sum_kK_kK_k^\dagger=\sum_kK_k^\dagger K_k=I$.
  Stochasticity is unnecessary for this calculation. A stochastic
  decomposition with scalar-identity noiseless operator and Hermitian
  error operators satisfies the same normality condition. This is not
  a theorem formalized in this module. The witness's transfer matrices
  are nonnormal and escape that sufficient condition.
- **Mixed-unitary literature status, open verification boundary.**
  The source's separate question about every stochastic qutrit channel
  being mixed unitary has a claimed published answer in
  Kribs–Levick–Pereira–Rahaman, arXiv:2306.04077. That report is
  `ASSUMED-UNVERIFIED`; this delivery does not certify its attribution.
  Analytically, every mixed-unitary map is unital because
  $\sum_kp_kU_kIU_k^\dagger=(\sum_kp_k)I=I$.
  Thus this nonunital instance also obstructs a mixed-unitary
  representation. This consequence is a prose calculation, not another
  Lean settlement.
- **Consequences for the source, source-attested scope.** The source's
  qubit theorem and its even-dimensional counterexamples concern
  different dimensions and remain compatible with this refutation.
  Its diamond-distance and twirling theorems do not assume the open
  qutrit-unitality question. The refutation excludes universal qutrit
  unitality; it does not invalidate those independent results or provide
  a classification of all stochastic channels.

## ASSUMED-UNVERIFIED

Literature completeness beyond the preregistration's citation graph and
the reported attribution to arXiv:2306.04077 are unverified here. The
uniform family and a classification of stochastic channels are not
formalized by this dimension-three, half-mixture settlement.
