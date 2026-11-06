---
slug: spin-one-rotation-boxes
bibkey: aloygalleyjonesludeschermuller2024rotationboxes
doi: 10.1007/s00220-024-05123-2
url: https://arxiv.org/abs/2312.09278v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.result
---

# Finite multi-outcome spin-one rotation correlations are quantum

## Problem

Aloy, Galley, Jones, Ludescher and Müller, *Spin-Bounded Correlations: Rotation Boxes Within and Beyond Quantum Theory*, arXiv:2312.09278v2, §4.2.3, page 17, asks:

> This is also the reason why we do not currently know whether $\mathcal{Q}_1^\mathcal{A}=\mathcal{R}_1^\mathcal{A}$ for $|\mathcal{A}|\geq 3$.

The answer is proved by `D5.S3.Quantum.Measurement.RotationBoxes.SpinOneRotationBoxes.result`. The source definitions and the unnumbered question are transcribed in [the Library note](../Library/Fourier/aloygalleyjonesludeschermuller2024rotationboxes.md). Preregistration: [#22872](https://github.com/the-omega-institute/trureturing/issues/22872).

### Statement echo

For every finite outcome type $A$ with $3\leq |A|$ and every family $p:A\to\mathbb R\to\mathbb R$, `QuantumSpinOne p` is equivalent to `RotationSpinOne p`.

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Every finite outcome set, cardinality at least three | `claim` quantifies over `A`, its `Fintype` instance and the cardinality inequality | No fixed alphabet or cardinality upper bound |
| All probability functions in the family | Universal $p:A\to\mathbb R\to\mathbb R$ | No regularity or realizability assumption on $p$ |
| Equation (4), frequencies $-1,0,1$ with arbitrary finite multiplicities | Sigma carrier indexed by `Fin 3`, with arbitrary natural multiplicity function | Zero multiplicities are permitted |
| One density state and one POVM, valid for every angle and outcome | `QuantumSpinOne`, reusing `FiniteStateChannel.DensityState`; positivity, sum and Born conditions are literal | Neither state nor measurement varies with angle |
| Real trigonometric polynomials of degree at most two | `RotationSpinOne`, five real coefficient functions and the cosine/sine expansion | The source's Lemma 5 gives this real coefficient convention |
| Both pointwise probability bounds and normalization | The two remaining conjuncts of `RotationSpinOne` | Every real angle and every outcome |
| Equality of the two correlation sets | `claim` and `result` assert the membership equivalence | The predicates are defined for all finite types; the public claim restricts to the source's requested cardinalities |

The finite direct sum is the sigma type itself. The POVM condition is inlined rather than introducing a forwarding definition. Typeclass arguments supply finite sums; they impose no additional mathematical restriction on finite outcome sets.

## Motivation

The source proves the binary spin-one equality but distinguishes the full general probabilistic theory from quantum theory. Equality of the correlation families for a separately chosen state and measurement does not imply a single embedding of that entire theory. This result answers the source's finite multi-outcome question within its stated model.

## Gap

Individually chosen positive Gram representatives of the nonnegative probability polynomials need not have a diagonal sum. A joint normalization is needed before converting them into one complete quantum measurement. Invertibility cannot be assumed: a diagonal sum can have zero entries.

The module has `generality: I`, `utility: none`, and `admission_basis: open-problem-resolution (#22872; Proved)`. Its declaration classifications are bind-only after expansion; the external named settlement is the admission basis. The auxiliary declarations are private and consumed by the settling proof. This classification claims no independent escape witness.

## Route

A scalar degree-two trigonometric factorization supplies positive semidefinite three-by-three Gram matrices $Q_a$. Write $J$ for coordinate reversal and $B_a=(Q_a+JQ_a^{\mathsf T}J)/2$. This averaging preserves each probability polynomial and makes the two first-superdiagonal entries equal. Uniqueness of the five Fourier coefficients and $\sum_a p_a=1$ force $\sum_a B_a$ to be diagonal of trace one.

Write that diagonal as $c_i\geq0$, set $D=\operatorname{diag}(\sqrt{c_i})$, and let $P$ project onto the coordinates with $c_i>0$. Positivity forces every $B_a$ to vanish off this support. With $M=\operatorname{diag}((\sqrt{c_i})^{-1})$, where inverse zero is zero, and $m=|A|>0$, set

$$E_a=MB_aM+\frac{I-P}{m}.$$

These matrices are positive semidefinite, sum to the identity, and satisfy $DE_aD=B_a$. The vector $v_i=\sqrt{c_i}$ has squared norm one. Its pure density matrix $vv^\dagger$ and one copy of each frequency give the required Born trace. Conversely, arbitrary finite multiplicities produce only frequency differences $-2,-1,0,1,2$; positivity and trace normalization give the probability bounds and total one.

The private helpers `normalized_nonnegative_trig2_grams`, `diagonal_whitening_povm`, `gram_family_quantum`, `rotation_quantum` and `quantum_rotation` implement these steps inside the settling module.

## Falsifier

A normalized nonnegative degree-two finite probability family with no quantum realization would contradict `result`. The theorem retains arbitrary finite multiplicities in the reverse inclusion and every real angle in both definitions. A failure of the same averaging argument in degree three is a boundary of this method, not a counterexample to the spin-one equality.

## Evidence

The formal evidence is the settling module and its frozen state record at `Golden/Frozen/state/D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes.lean.json`. The Scribe displays all three public definitions and the full proposition of `result`, with one `OpenProblemResolutionClaim` of kind `Proved`.

The escape audit is unfinished for the sole public theorem `D5.S3.Quantum.Measurement.RotationBoxes.SpinOneRotationBoxes.result`: [#26845](https://github.com/the-omega-institute/trureturing/issues/26845). No Reg registration is delivered. Arbitrary finite types and real function families require a faithful dependent-family realization, enrolled readout and whole-family sensitivity evidence; those obligations are not discharged by a Boolean encoding of the theorem's truth value.

### Exact independent experiment

[Experiment directory at commit 25ea29e05ee22f1b0da6ac37e64a553b6b1ef961](https://github.com/the-omega-institute/trureturing-experiments/tree/25ea29e05ee22f1b0da6ac37e64a553b6b1ef961/docs/reports/aloy-et-al-spin-one-rotation-boxes).

The committed `check.py` was retrieved with `git show 25ea29e05ee22f1b0da6ac37e64a553b6b1ef961:docs/reports/aloy-et-al-spin-one-rotation-boxes/check.py` from the experiments clone. Command: `python3 /Users/auric/.sshx/7a46e1b9deae27e0baa33fef/attempt-1/experiment-check.py`; exit 0. Script SHA-256: `d8952849a7eb1251eca2cf091b4f9f4401b5216ff5396a36205896f7d9dde0e9`. Python 3.14.8; SymPy 1.14.0.

The checks cover the source's $\sin^4(\theta/2)$ realization, the symbolic three-by-three reversal identity, all seven nonempty supports, and exactly the specified finite rank-one catalog. For three outcomes, 5,984 multisets contain 91 normalized families with support-rank counts $(3,15,73)$. For four outcomes, 52,360 multisets contain 575 normalized families with counts $(4,29,542)$. All checks pass. The catalog neither exhausts arbitrary coefficients nor supplies the universal formal proof.

## Triage

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Exact requested finite multi-outcome equality | Proved; kernel-checked | `result`, with no hypothesis beyond finite $A$ and $3\leq |A|$ |
| Equality for every nonempty finite outcome set | Proved; kernel-checked | The private `quantum_rotation` and `rotation_quantum` establish the two inclusions under these hypotheses. The pure realization with multiplicities $(1,1,1)$ is the explicit construction in the proof of `gram_family_quantum`; the construction is described in Route, rather than claimed as an additional public theorem |
| Singular total Grams and arbitrary finite matrix index sets | Proved; kernel-checked | Private `diagonal_whitening_povm`: arbitrary finite matrix index type, nonempty finite outcome type, nonnegative diagonal sum; no invertibility hypothesis |
| Degree-three reversal/constant-polynomial implication fails | Proved in prose | The exact rational calculation below proves the finite matrix claim; it is not a Lean theorem or a counterexample to a rotation-box equality |
| One family-independent embedding of the entire GPT | Open | The state in `QuantumSpinOne` can depend on $p$; the theorem supplies no family-independent embedding |
| New higher-spin equalities or a characterization of their gaps | Open | Neither `result` nor the degree-three method boundary asserts such a conclusion |

### Degree-three method boundary

Consider the symmetric four-by-four matrix

$$C=\begin{pmatrix}
1/4&1/32&0&0\\
1/32&1/4&-1/16&0\\
0&-1/16&1/4&1/32\\
0&0&1/32&1/4
\end{pmatrix}.$$

This finite boundary has a direct proof by rational identities, so its evidence kind is proved in prose. For the leading tridiagonal minors, let $d_0=1$ and use $d_k=\tfrac14d_{k-1}-b_{k-1}^2d_{k-2}$, with successive off-diagonal entries $b_1=1/32$, $b_2=-1/16$, $b_3=1/32$. The four minors are

$$d_1=1/4,\qquad d_2=63/1024,\qquad d_3=59/4096,\qquad d_4=3713/1048576.$$

They are all positive, so Sylvester's criterion gives positive definiteness. Coordinate reversal satisfies $JC^{\mathsf T}J=C$ because the first superdiagonal is palindromic. The trace is one; the sums on the three upper off-diagonals are $1/32-1/16+1/32=0$, $0$, and $0$. Consequently $\varphi(\theta)^\dagger C\varphi(\theta)=1$ for $\varphi(\theta)=(1,e^{i\theta},e^{2i\theta},e^{3i\theta})^{\mathsf T}$ and every real angle. But $C_{01}=1/32\neq0$, and averaging leaves $C$ unchanged. Thus these hypotheses do not force diagonality at degree three. This statement concerns that averaging implication only.

### What the settlement shows

The decisive degree-two mechanism combines reversal-transpose invariance with Fourier normalization: two first-superdiagonal entries become equal and have zero sum, hence both vanish. Support whitening extends the construction to singular totals and arbitrary finite matrix index sets. The two inclusions extend to every nonempty finite outcome set; no alphabet bound enters their proof. The pure state may depend on the family.

The source's distinction between whole GPT systems remains intact, and its established higher-spin gaps are not altered. This theorem settles the previously open multi-outcome equality; it does not turn a correlation-set equality into an embedding theorem. The exact four-dimensional matrix above shows why this particular averaging argument alone does not settle higher spin.

### Literature status

The preregistration records a targeted screen of nine citing works, later same-author papers and public Lean/OEIS problem indexes. In particular arXiv:2507.06912v2, equations (45)–(48), retains a diagonal-sum constraint in an SDP characterization; that constraint is not the simultaneous-normalization conclusion. No prior settlement was identified in that inspected scope. These literature readings are attributed to the preregistration producers. Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness, a global arXiv full-text search and exhaustive coverage of public Lean settlements are `ASSUMED-UNVERIFIED`. The preregistration records unavailable OpenAlex citation/author queries and bounded search inventories. The finite experiment is independent evidence within its exact tested scope, not a universal theorem. The four-slot escape audit remains unfinished under #26845; no `declared_validated` status is asserted.
