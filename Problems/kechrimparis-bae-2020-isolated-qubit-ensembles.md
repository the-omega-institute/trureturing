---
slug: kechrimparis-bae-2020-isolated-qubit-ensembles
bibkey: kechrimparisbae2020omp
doi: 10.1088/1367-2630/abcc9b
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.result
url: https://arxiv.org/abs/2006.16366
---

## Problem

Spiros Kechrimparis and Joonwoo Bae, *Optimal measurement preserving qubit
channels*, New Journal of Physics 22, 123024, DOI 10.1088/1367-2630/abcc9b,
arXiv:2006.16366v2, Conclusions:

> We expect that no isolated ensembles exist but we have not managed to establish the result in general.

Their Definition 1 calls a channel optimal measurement preserving (OMP) when
one POVM is optimal for both the original and output ensembles. Isolation means
that only the identity CPTP map shares any optimal POVM. Preregistration: #15684.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite qubit ensemble | Natural label count, real priors, complex two-by-two matrices in `claim` | Literal preregistered convention |
| Probabilities of physical states | Strictly positive priors with sum one; frozen `IsDensity` | No extra hypothesis |
| Minimum-error optimum | `IsOptimalPOVM`: frozen `IsPOVM` and score comparison with every POVM | The complete defining expression |
| One optimum before and after the channel | `IsOMP`: an existential shared POVM | Does not require all optima to be preserved |
| Only the identity preserves an optimum | `IsIsolated`: every frozen `IsCPTP` map satisfying `IsOMP` equals `LinearMap.id` | The source's trivial OMP set |
| No isolated ensembles | Universal `claim` | Refuted by `result : ¬ claim` at four states |

The real part of the trace reads the real discrimination score; complete
positivity and trace preservation are those of the frozen channel owner.
A unique original optimum makes sharing any optimum equivalent to preserving
that optimum. The journal title differs from the separate JSAC paper *Channel
Coding of a Quantum Measurement*.

## Motivation

The settling declaration is
`D5/S3/Quantum/Measurement/IsolatedQubitEnsemble.result`.
It exhibits an isolated four-state qubit ensemble, answering the published
question and refuting the expectation. The supporting declaration
`D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity`
provides a first-order necessary condition for an arbitrary finite matrix POVM.

## Gap

Two citing works remain outside the readable full-text literature screen:
Ko et al., JSAC 43(8), 2798–2809, DOI 10.1109/JSAC.2025.3568037, and Suzuki,
IEICE IT2022-13. No claim of exhaustive literature exclusion is made.
Isolation in higher dimensions and the minimal number of states remain open.
The Lean instance is $G=19$; the family argument below is a reading, not a
kernel-checked theorem uniform in $G$.

## Route

The four Pauli directions are
$s_{1,2}=(\pm3/5,0,4/5)$ and $s_{3,4}=(0,\pm3/5,-4/5)$.
Write $S_i=s_i\cdot\sigma$, $P_i=(I+S_i)/2$, and $Q_i=(I-S_i)/2$.
At $G=19$ the priors are $(9,9,5,5)/28$, the states are
$(I-S_i/18)/2$ for the first pair and $(I-9S_i/10)/2$ for the second,
and $M_i=Q_i/2=(I-S_i)/4$.

The dual certificate $K=19I/112$ satisfies
$K-q_i\rho_i=(a_i/56)P_i$ with $a=(1,1,9,9)$ and $P_iM_i=0$.
For any POVM $F$, its score is $\operatorname{tr}K$ minus the sum of
nonnegative slack traces. Equality forces $F_i$ into the rank-one kernel of
$P_i$; completeness fixes the four coefficients and gives $F=M$.

Positive quadratic effect variations give eight first-order stationarity
equalities. Bloch coordinates solve these equalities to an affine map with
translation $t=(t_x,t_y,t_z)$ and linear part

$$
T=\begin{pmatrix}
1-9\epsilon&0&t_x\\
0&1-\epsilon&t_y\\
0&0&1-9\epsilon/5+t_z
\end{pmatrix}.
$$

The four states span the complex two-by-two matrix space, so their images
fix the whole complex-linear channel. Complete positivity makes its Choi
matrix positive semidefinite. The Lean Choi convention uses the unnormalized
maximally entangled vector. Two quadratic forms sum to $-33\epsilon/10$;
a second pair sums to $36\epsilon$, forcing $\epsilon=0$. A quadratic form
and a diagonal entry then force $t_z=0$, and a zero diagonal forces the
remaining off-diagonal entries to vanish, hence $t_x=t_y=0$.
The result is the identity channel. The experiment uses twice the Choi matrix and the opposite tensor-factor
ordering, with correspondingly permuted test vectors; its first sum is
$-33\epsilon/5$.

## Falsifier

A nonidentity CPTP map sharing an optimal POVM with the exhibited ensemble
would contradict `isolated` and thus the settling proof. A mismatch with the
literal definitions of #15684 would invalidate the source correspondence.
A prior publication settling the source question would invalidate the
literature novelty claim, while leaving the kernel statement intact.

## Evidence

The designated refutation `result` and supporting `quadratic_stationarity`
are compiled in the pinned Lean environment. Their axiom closures are
contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The optimality, uniqueness, stationarity, affine reconstruction and Choi
arguments are private consumed declarations in the settling module.

The public result is the designated refutation result (`basis=refutes`) and
is exempt from four-slot escape registration (CLAUDE.md §3.9).
The escape audit of `quadratic_stationarity` is unfinished under
[#15773](https://github.com/the-omega-institute/trureturing/issues/15773).
The arbitrary dependent matrix/real telescope needs complete source
reconstruction, lawful enrolled readout and source selection, and variation,
sensitivity and observational-dependence proofs. No Reg registration is
delivered. Its actual four-slot reading is `DTR-Unregistered` (SL-031, Observe).

### Experiment

[Experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/f38d88fdb3b3610abc71f4f281b1e696ca7e9b4b/docs/reports/kechrimparis-bae-2020-isolated-qubit-ensembles).
Command: `python3 check.py`, with NumPy and SymPy; exit 0; script SHA-256
`a791ade275b5cd2b55c1e95200ce9b376f7982629c658d6ab0f04289aebd625a`.
The exact rational certificate at $G=19$ passes and its score is $19/56$.
At each $G\in\{19,25,60\}$ the identity passes the optimality test;
zero of 2000 random channels and zero of 12 named channels pass.
The symbolic Choi matrix matches the independently rebuilt affine matrix,
and the two specified quadratic forms sum to $-33\epsilon/5$.
The final reading is `bad=0`. Sampling does not establish universal isolation.

## Triage

- **Proved in Lean — the instance $G=19$.** `priors_valid` checks the positive
  normalized priors $(9,9,5,5)/28`; `states_valid` checks the density matrices;
  `measurement_valid` and `optimal_measurement` prove that $M_i=(I-S_i)/4$
  is optimal. `slack` and `complementary` verify the dual-slack certificate.
  `unique_optimal` proves uniqueness. `isolated` proves that only
  the identity CPTP channel preserves an optimum. `result` refutes `claim`.
- **Proved in Lean — first-order reconstruction at $G=19$.**
  `QuadraticPovmStationarity.quadratic_stationarity` supplies the first-order
  equality. `stationarity_constraints`, `images_affine` and `channel_affine`
  reconstruct every channel preserving the fixed optimum.
- **Proved in Lean — complete positivity at $G=19$.** `choi_positive`,
  `choi_sum`, `choi_eps_nonneg` and `choi_identity` force the reconstructed
  CPTP map to be the identity, as used by `isolated`.
- **Computed — the pinned experiment above.** The exact certificate is
  checked at $G=19$. At each $G=19,25,60$, the identity passes and zero of
  2000 random and zero of 12 named channels pass the optimality test.
  The symbolic Choi calculation gives $-33\epsilon/5$. These readings have
  exit 0 under `python3 check.py`; sampling proves no universal statement.
- **Proved in prose — family reading for all $G>18$, not kernel-checked.**
  Put $L=4G-20$ and $a=(1,1,9,9)$, and take $q_i=(G-a_i)/L$ and
  $\rho_i=(I-a_iS_i/(G-a_i))/2$, with $P_i=(I+S_i)/2$.
  The directions have squared norm $9/25+16/25=1$. The Pauli product
  identity gives $S_i^2=I$, and each Pauli matrix is traceless, so
  $\operatorname{tr}S_i=0$. Consequently $P_i^2=P_i$,
  $Q_i^2=Q_i$, $P_iQ_i=0$, and $\operatorname{tr}P_i=
  \operatorname{tr}Q_i=1$. The four directions sum to zero, giving
  $\sum_iQ_i/2=I$. At $G=19$, $L=56$ and the prior pairs are
  $18/56=9/28$ and $10/56=5/28$; the state coefficients are $1/18$
  and $9/10$.
  Each prior is positive, their sum is one,
  and $0<a_i/(G-a_i)<1$ makes each state positive with trace one:
  $S_i^2=I$ and $\operatorname{tr}S_i=0$, so the state eigenvalues are
  $(1\pm a_i/(G-a_i))/2$. The prior sum is $(4G-20)/L=1$.
  For a trace-preserving complex-linear channel $N$ and any POVM $F$, write
  $p_G(N,F)=\sum_iq_i\operatorname{Re}\operatorname{tr}(N(\rho_i)F_i)$.
  The identities $q_i\rho_i=((G-a_i)I-a_iS_i)/(2L)
  =(GI-2a_iP_i)/(2L)$, completeness
  $\sum_iF_i=I$, and $\operatorname{tr}(N(I))=2$ give

  $$
  p_G(N,F)=\frac{G}{L}-\frac{1}{L}
  \sum_i a_i\operatorname{Re}\operatorname{tr}(N(P_i)F_i)
  =\frac{56}{L}p_{19}(N,F)+\frac{G-19}{L}.
  $$

  Indeed, linearity gives
  $N(q_i\rho_i)=(GN(I)-2a_iN(P_i))/(2L)$, and
  $\sum_i\operatorname{Re}\operatorname{tr}(N(I)F_i)
  =\operatorname{Re}\operatorname{tr}(N(I))=2$.
  The quantity $\sum_i a_i\operatorname{Re}\operatorname{tr}(N(P_i)F_i)$
  is independent of $G$; its value is $19-56p_{19}(N,F)$, which gives
  the second equality.

  Since $56/L>0$, the optimizing POVMs are exactly the same at $G$ and
  $19$, both before and after every CPTP channel. Thus the family has the
  same OMP set as the kernel-checked $G=19$ instance, namely the identity.
  Put $c=1/(G-1)>0$ and $d=9/(G-9)>0$. Their Bloch vectors are
  $-cs_1,-cs_2,-ds_3,-ds_4$. The first pair difference is
  $(-6c/5,0,0)$ and the second is $(0,-6d/5,0)$, while the pair means
  have $z$ coordinates $-4c/5$ and $4d/5$ and differ by
  $4(c+d)/5>0$. These three differences are linearly independent.
  Thus the four states are affinely
  independent and span the trace-one Hermitian affine space. The stationarity and Choi mechanism
  described above therefore applies throughout this family. This
  mathematical correspondence is proved here in prose; no uniform Lean
  theorem is asserted. The experiment checks only $G=19,25,60$ and the
  symbolic Choi identity.
- **ASSUMED-UNVERIFIED — literature.** The full texts of Ko et al. (JSAC 2025)
  and Suzuki (IEICE IT2022-13) were not readable; their exclusion as prior
  settlements is unverified.
- **Open — higher dimensions.** The delivered theorem has two-dimensional
  state space and supplies no higher-dimensional construction.
- **Open — minimal number of states.** The witness has four states and
  does not establish minimality. The source excludes two-state ensembles;
  that is a literature reading, not a Lean lower-bound theorem here.

### What the settlement shows

**Proved in prose — the slack asymmetry.** The certificate has coefficients
$1/56,1/56,9/56,9/56$, so the two slack weights have ratio $9$. The resulting
first-order constraints are incompatible with any nonidentity CPTP map.
The unique optimum makes the shared-measurement and fixed-optimum readings
coincide for this witness. The source's expectation fails for unequal priors
and four states. Its non-isolation results for two states and equal priors
survive, because this witness has neither property. The generalized
stationarity theorem allows arbitrary natural dimension and label count;
it alone does not settle higher-dimensional isolation or state minimality.

## ASSUMED-UNVERIFIED

The two unread full texts prevent an exhaustive prior-settlement exclusion.
The $G>18$ family has no uniform kernel-checked theorem in this delivery.
The unfinished escape audit is disclosed under #15773; no completed
registration status is asserted.
