---
slug: alsing-birrittella-2024-log-negativity-sandwich
bibkey: alsingbirrittella2024lognegativity
doi: 10.3390/foundations5020019
url: https://arxiv.org/abs/2404.13725v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.result
---

# The Alsing–Birrittella logarithmic-negativity sandwich

## Problem

P. M. Alsing and R. J. Birrittella, *Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization*, arXiv:2404.13725v1, Section IV, p. 11, Equation (22), state:

> we have numerically found that 𝓛𝓝_a^avg(ρ_ab) ≤ LN_e(ρ_ab) ≤ LN_a(ρ_ab) when the mixed state is written as a pure state decomposition (PSD) ρ_ab = Σ_i p_i |ψ_i⟩⟨ψ_i|, and in addition the quantum amplitude matrix C_i of each pure state component |ψ_i⟩ = Σ_nm C_i,nm |n,m⟩ is uniformly generated (over the Haar measure) as a positive Hermitian matrix, C_i = C_i† ≥ 0.

> Further, we find that the second inequality is surprisingly saturated, i.e. LN_e(ρ_ab) = LN_a(ρ_ab) in Eq.(22), if the uniformly randomly generated C_i matrices above are real, i.e. C_i = C_i^T.

The settling theorem proves both inequalities and the real-amplitude equality for every finite ensemble of positive semidefinite complex amplitude matrices, with nonnegative weights summing to one and $\operatorname{tr}(C_iC_i^\dagger)=1$. Different amplitudes need not commute. Zero weights and singular amplitudes are allowed.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite bipartite amplitudes $C_i$ | `d K : ℕ`, `C : Fin K → Matrix (Fin d) (Fin d) ℂ` in `claim` | Every finite dimension and ensemble size; no sampling restriction. |
| $\rho=\sum_i p_i|\psi_i\rangle\langle\psi_i|$ | `ensembleState` | `Function.uncurry` is the literal amplitude vector; `Matrix.vecMulVec` forms its outer product, with real weights embedded in $\mathbb C$. |
| Probabilities and normalized pure components | Nonnegative weights, sum one, and trace normalization in `claim` | State and ensemble normalization made explicit. |
| Positive Hermitian amplitudes | `(C i).PosSemidef` | Includes Hermitian symmetry and permits zero eigenvalues. |
| Exact logarithmic negativity | `exactLogNegativity` | `Real.logb 2` of the existing trace norm of the existing second-factor partial transpose. |
| Equations (11a)–(11b) | `pureApproxNegativity`, `pureApproxLogNegativity` | Literal half-sum over ordered unequal pairs and base-two logarithm. |
| Equations (17b)–(17c) | `mixedApproxNegativity`, `mixedApproxLogNegativity` | Literal mixed entry difference, half-sum and logarithm. |
| Average of the pure logarithms | First inequality in `claim` | Weighted sum of logarithms, with the logarithm inside the ensemble average. |
| Upper inequality and real-case equality | Second inequality and guarded equality in `claim` | For Hermitian matrices, transpose symmetry expresses real entries. |

The public definition bodies are the conventions in [#19208](https://github.com/the-omega-institute/trureturing/issues/19208). The universal positive-semidefinite class contains the randomly generated source class. No simultaneous diagonalization, invertibility or positive-weight assumption is added.

## Motivation

The settling GID is `D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich.result`, with `admission_basis: open-problem-resolution (#19208; Proved)`. This named external problem has no anchor atom. One `OpenProblemResolutionClaim` records `Proved` on the settling declaration. The [source note](../Library/Entropy/alsingbirrittella2024lognegativity.md) owns the paper's DOI.

## Gap

The source reports numerical evidence for the mixed-state sandwich and real-case saturation. The formal result supplies a proof for the whole finite positive-Hermitian amplitude class. The broader conjecture concerning arbitrary pure-state amplitude matrices is outside this settlement.

## Route

Write $F$ for the swap and $Q=\sum_i p_i(C_i\otimes C_i)$. The private `factorization`, `positiveFactor_psd` and `factor_commutes` prove $\rho^\Gamma=QF$, $Q\ge0$ and $QF=FQ$. The existing `HaarTwoCopyTwirl.replicaSwap_commutes` supplies tensor-square commutation. The private `swap_selfAdjoint` and `swap_square` establish that $F$ is a self-adjoint involution. Thus $(\rho^\Gamma)^\dagger\rho^\Gamma=Q^2$; `trace_norm_evaluation` uses `CFC.sqrt_unique` to identify the positive square root and obtains

$$\|\rho^\Gamma\|_1=\sum_i p_i(\operatorname{Re}\operatorname{tr}C_i)^2=:T.$$

Positive principal two-by-two minors give `pure_value`:

$$1+2N_a(C_i)=(\operatorname{Re}\operatorname{tr}C_i)^2.$$

`logb_jensen` applies logarithmic concavity for the lower bound. `minor_le_difference_re`, `mixed_pair_bound` and `mixed_bound` compare each mixed entry norm with the weighted nonnegative principal minors, giving the upper bound. `mixed_pair_real` and `mixed_real` give equality for transpose-symmetric amplitudes. `result` combines these statements.

All newly delivered proofs are classified `bind-only`; no escape witness is claimed. Each private helper is consumed by subsequent helpers or `result`. The settling conclusion is admitted by the named external open-problem-resolution basis. The existing frozen swap-commutation proof is published unchanged and used directly.

## Falsifier

A normalized positive-semidefinite finite ensemble violating either inequality, or a real such ensemble violating upper equality, would contradict `result`. A factorization, trace-norm or minor calculation that fails under the stated hypotheses would invalidate the indicated route. The compiled proofs cover these identities and inequalities; random sampling alone establishes none of their universal forms.

## Evidence

The kernel-checked public conclusion is `D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich.result`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit is unfinished under [#19279](https://github.com/the-omega-institute/trureturing/issues/19279). The targets are `D5.S3.Quantum.Information.AlsingBirrittellaLogNegativitySandwich.result` and the published `D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.replicaSwap_commutes`. No Reg mirror or `declared_validated` registration is asserted. Faithful whole-telescope source reconstruction, realization and source-selection bridges, a lawful enrolled-template readout, whole-family variation, per-role sensitivity and actual observational dependence remain required.

### Numerical experiment

[Experiment directory at `532cdf553566058b70b756281a3058c46b013a27`](https://github.com/the-omega-institute/trureturing-experiments/tree/532cdf553566058b70b756281a3058c46b013a27/docs/reports/alsing-birrittella-2024-log-negativity-sandwich). The pinned `check.py` has SHA-256 `bc2eab656465172aca4063a4b6322034ac417cde912bc78e0a83dbeeaf511832`.

The command `python3 /Users/auric/trureturing-experiments/docs/reports/alsing-birrittella-2024-log-negativity-sandwich/check.py` exits 0 with `RESULT PASS`. The local script is byte-identical to the pinned file. The portable command is `python3 check.py` from that directory with NumPy installed.

Exactly 3,000 random ensembles are tested, with $d\in\{2,3,4,5\}$, one to five components, and every third trial real. The maximum sandwich violation is $9.524\times10^{-16}$; the maximum real upper-equality error is $9.524\times10^{-16}$; the factorization error is $1.112\times10^{-16}$; the trace-norm formula error is $2.220\times10^{-15}$. The check tolerance is $10^{-10}$.

For $p=(1/2,1/2)$, $C_1=\operatorname{diag}(3/5,4/5)$ and $C_2=\left(\begin{smallmatrix}237&84i\\-84i&188\end{smallmatrix}\right)/325$, the checker finds strict ordering of the three logarithmic expressions and agreement with $\log_2(119/65)$, $\log_2(7753/4225)$ and $\log_2(207937/105625)$ to $2.220\times10^{-16}$. This is a floating-point check of the displayed illustration, not a separate kernel proof of its exact values or strictness.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Settlement | Proved, kernel-checked: `result` | The complete finite positive-Hermitian ensemble class satisfies the sandwich and real upper equality, including noncommuting complex amplitudes. |
| Admission | Proved conclusion, kernel-checked: `result`; classification and source evidence in #19208 | The basis is `open-problem-resolution (#19208; Proved)`. Proof shapes are `bind-only`, with consumed helpers; no escape witness is asserted. |
| Scope boundary | Open here | Arbitrary pure-state amplitude matrices are not covered. Exact strict-example certification and full lower/upper equality characterizations are not separately formalized. |
| Integration and independent review | Open for integration review | The settlement source, Scribe, source note and dossier are supplied. The Draft delivery does not certify completed independent integration review. |
| Exact formula and noncommuting extent | Proved, kernel-checked: private `trace_norm_evaluation` and the equality `he` inside `result` | $LN_e(\rho)=\log_2 T$ for the whole stated class. No commutation between different amplitudes or numerical eigensolver enters this identity. |
| Lower-gap formula | Open as a separate kernel-checked statement; prose derivation from the preceding identities | Put $t_i=(\operatorname{Re}\operatorname{tr}C_i)^2\ge1$. Substituting the exact and pure formulas gives $LN_e-\mathcal{LN}_a^{avg}=\log_2(\sum_i p_it_i)-\sum_i p_i\log_2 t_i$, the Jensen defect. A separate exact equality classification is open in this delivery. |
| Quantitative upper-gap mechanism | Open as a separate kernel-checked statement; prose entry calculation below | The negativity gap is at least $2\sum_{k,n<m}p_k(\operatorname{Im}C_{k,nm})^2$. This quantitative strengthening is not a separate Lean declaration. |
| Real saturation | Proved, kernel-checked: `result` | Every real amplitude ensemble in the stated class attains the upper equality; no assertion of lower equality for all such ensembles is made. |
| Strict illustration | Computed, pinned experiment | The displayed two-component example has strict numerical gaps with the tested tolerance above. Exact certification is not separately formalized. |
| Literature | Open completeness, literature reading in #19208 | The examined source, journal and citation-index records and later author postings yielded no settlement. Completeness is `ASSUMED-UNVERIFIED`. |

For the quantitative upper-gap calculation, fix $n\ne m$ and let $z_k=C_{k,nm}$. Hermitian symmetry gives

$$\operatorname{Re}\bigl(\rho_{nn,mm}-\rho_{nm,mn}\bigr)
=\sum_kp_k\bigl(C_{k,nn}C_{k,mm}-|z_k|^2\bigr)
+2\sum_kp_k(\operatorname{Im}z_k)^2.$$

Diagonal entries are real, principal minors are nonnegative, and $|w|\ge\operatorname{Re}w$. Taking the ordered-pair half-sum therefore gives

$$N_a(\rho)-\frac{T-1}{2}\ge
\sum_{n\ne m,k}p_k(\operatorname{Im}C_{k,nm})^2
=2\sum_{k,n<m}p_k(\operatorname{Im}C_{k,nm})^2.$$

Here the weighted pure-minor identity supplies $(T-1)/2$. This prose derivation explains the real-case saturation without asserting a separately kernel-checked quantitative theorem. The source's numerical observation on this class has an analytic proof; no other source theorem is asserted to depend on this observation, and its arbitrary-amplitude pure-state witness question remains outside scope.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The screen recorded in #19208 examined the arXiv record, the journal version, Crossref and OpenAlex citation counts, and 24 later author postings. This is the searched scope, not an exhaustive global priority claim. The DOI resolves through Crossref to the cited title; the source note does not attest a fresh reading of the publisher text.

The broader arbitrary-amplitude conjecture, separate exact strict-example certification, full equality classifications and four-slot escape registration remain unresolved in this delivery. Numerical experiment ranges do not extend the formal theorem's hypotheses.
