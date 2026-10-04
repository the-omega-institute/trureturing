---
slug: cha-2026-equiprobable-pgm-active-set
bibkey: cha2026structural
doi: 10.1007/s11128-026-05335-6
url: https://arxiv.org/abs/2507.05778v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.result
---

# The equiprobable pretty-good-measurement comparison of Cha and Lee

## Problem

H. Cha and J. Lee, *Structural perspectives from quantum states and
measurements in optimal state discrimination*, Quantum Information Processing
25, 310 (2026), arXiv:2507.05778v2. For an ensemble
$\tilde\sigma_i=p_i\sigma_i$, $I_+$ is the set of labels whose optimal
minimum-error effect is nonzero, and

> $P_\mathcal{E}^{\text{PGM}+} = \sum_{i \in \text{I}_+(\mathcal{E})} \text{tr}(\Tilde{\sigma}_i E_i)$, where $S \equiv \sum_{i \in \text{I}_+(\mathcal{E})} \Tilde{\sigma}_i$ and $E_i \equiv S^{-1 / 2} \Tilde{\sigma}_i S^{-1 / 2}$.

For equal priors the paper conjectures (journal Eq. (18)):

> $(|\text{I}_+(\mathcal{E})| - 1) \left( P_\mathcal{E}^{\text{PGM}+} - \frac{1}{N} \right) \leq (N - 1) \left( P_\mathcal{E}^{\text{PGM}} - \frac{1}{N} \right).$ […] Consequently, we conjecture that it holds universally for equiprobable states.

## Motivation

Eq. (18) is the equal-prior form of the statement that the upper bound on
the optimal success probability obtained from the pretty good measurement on
the active set is at least as tight as Renes's bound from the pretty good
measurement on all states. The frozen declaration
`D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.result` shows
that it fails.

## Gap

Issue #12997 classifies the conjecture as Tier 1. Before any Lean it recorded
the following checks:

- The journal version keeps Eq. (18) and the conjecture sentence, and defines
  $I_+$ by nonzero optimal effects (seat-reported from the publisher PDF);
  the arXiv text writes "positive definite" but assigns $\text{I}_+=\{1,2\}$
  to rank-one effects in its own example (l. 526).
- Renes, PRA 96, 042328 (2017), Eq. (12), bounds $P^{\rm PGM}$ below by
  $P_{\rm opt}^2+(1-P_{\rm opt})^2/(N-1)$ for one ensemble; Barnum–Knill and
  Montanaro (2007) concern other statements; the paper's unequal-prior
  counterexamples do not transfer to equal priors.
- QIQCOP Zoo and this repository have no record of the paper.

These are seat-reported readings checked against the cited statements,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty.

## Route

1. $N=3$, equal priors, $\rho_1=\frac1{401}\begin{pmatrix}400&18\\18&1\end{pmatrix}$,
   $\rho_2=\frac1{401}\begin{pmatrix}400&-18\\-18&1\end{pmatrix}$,
   $\rho_3=\frac1{48922}\operatorname{diag}(47963,959)$, all positive
   definite; $\tilde\sigma_i=\rho_i/3$.
2. $\Gamma=\frac1{1203}\operatorname{diag}(418,19)$ has
   $\Gamma-\tilde\sigma_1=\frac6{401}(1,-1)(1,-1)^{\mathsf T}$,
   $\Gamma-\tilde\sigma_2=\frac6{401}(1,1)(1,1)^{\mathsf T}$ and
   $\Gamma-\tilde\sigma_3=\frac1{48922}\operatorname{diag}(1011,453)$, so
   every POVM scores $\operatorname{tr}\Gamma-\sum_i\operatorname{tr}((\Gamma-\tilde\sigma_i)E_i)
   \le437/1203$, attained by $\frac12(1,1)(1,1)^{\mathsf T}$,
   $\frac12(1,-1)(1,-1)^{\mathsf T}$, $0$.
3. For an optimal POVM each term $\operatorname{tr}((\Gamma-\tilde\sigma_i)E_i)$
   vanishes. As $\Gamma-\tilde\sigma_3\succeq\frac{453}{48922}I$, $E_3=0$;
   $E_1=0$ or $E_2=0$ would leave $\operatorname{tr}(\Gamma-\tilde\sigma_j)=12/401$.
   So $I_+=\{1,2\}$ for every optimal POVM.
4. $S=\frac1{122}\operatorname{diag}(121,1)$ and
   $S_+=\frac2{1203}\operatorname{diag}(400,1)$ have diagonal inverse square
   roots, and $P^{\rm PGM}=20192347/58370763$,
   $P^{\rm PGM}_+=2167/6015$; LHS − RHS $=168714/97284605>0$.

## Falsifier

The kernel-checked `result` is the negation of the following statement. For
all $d,N$ and every family of positive definite $d\times d$ matrices
$\rho_i$ of trace $1$, some POVM $E$ (positive semidefinite effects summing
to $I$) maximizes $\sum_i\operatorname{Re}\operatorname{tr}(\rho_iE_i/N)$ over
all POVMs and satisfies
$(|A|-1)(P_A-\tfrac1N)\le(N-1)(P-\tfrac1N)$ for $A=\{i:E_i\ne0\}$, where
$P_A=\sum_{i\in A}\operatorname{Re}\operatorname{tr}(\tilde\sigma_iS_A^{-1/2}\tilde\sigma_iS_A^{-1/2})$
with $S_A=\sum_{j\in A}\tilde\sigma_j$ and the continuous-functional-calculus
power, and $P=P_{\text{all}}$.

"Some optimal POVM" is the weakest reading of "the optimal POVM"; step 3 shows
that all optimal POVMs share the active set here. Positive definite states
make every nonempty $S_A$ invertible, so no pseudo-inverse convention enters.

## Evidence

- Values (Python `fractions`, exact): as in step 4; the dual slacks and the
  optimal value $437/1203$.
- The two bounds compared by Eq. (18), evaluated in double precision:
  Renes's bound from all states is $0.424982$, the bound from the active set
  is $0.428083$, and $P_{\rm opt}=0.363259$.

The canonical source is
`D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.lean`.
- Public declarations: `IsPOVM`, `success`, `pgmScore`, `claim`, `rho` and
  `result`.
- Reuse: the frozen `RHLinalg.trace_mul_nonneg_of_posSemidef` of
  `D5/S3/Weil/ZetaLinear/RankTrace` gives $\operatorname{tr}((\Gamma-\tilde\sigma_i)E_i)\ge0$.
- Freeze identities:
  - module statement `sha256:6fa6bba96d8acf3cbb06287980ae92f44124b4be885ea6579f6d201ef34a47a1`;
  - `result` statement `sha256:f104b8902c769f052711b726d8c3c1c94e515fbee68913c5de2896f0c00ca752`;
  - Freeze event `sha256:95daba5c358368d02a87504a08cd435bf3bd320e476459428fb9fd49dba82704`.
    Its project-level frozen prerequisite is the Freeze event of
    `D5/S3/Weil/ZetaLinear/RankTrace`,
    `sha256:2545e42281a81b560d4722b6cfad7faa69d374292d088017884c95478fc1c5ee`.
- Axioms: the proof uses only `propext`, `Classical.choice` and
  `Quot.sound`. It contains no `sorry`, no `native_decide` and no new axiom.

## Triage

Tier 1 conjecture of a 2026 journal article. Resolution: `Refuted`, by
`D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.result`.

- `proof_shape: bind-only`. The settlement of the named conjecture is the new
  content; there is no escape witness.
- `admission_basis: open-problem-resolution` (issue #12997).
- Utility kind `certified-instance`, basis `refutes` the module's `claim`.

### What the settlement shows

- **Proved by `result`:** for three positive definite qubit states with equal
  priors, every optimal POVM has active set $\{1,2\}$ and Eq. (18) fails.
- **Proved inside the proof of `result`:** the dual certificate and the
  complementary-slackness argument fixing the active set, and the inverse
  square roots of the two diagonal matrices $S$, $S_+$ through the continuous
  functional calculus.
- **Where the gap comes from (computed, not stated in Lean):** adding the
  inactive $\tilde\sigma_3$ changes the ratio of the diagonal entries of
  the averaged matrix from $400$ ($S_+$) to $121$ ($S$). The pretty good
  measurement on all states therefore weights the $|1\rangle$ component,
  where $\rho_1$ and $\rho_2$ differ, by $\sqrt{121}=11$ instead of
  $\sqrt{400}=20$ relative to $|0\rangle$, and its score per active state
  drops below what Eq. (18) requires.
- **Effect on the paper's other conclusions (read from the arXiv source):**
  - Both upper bounds on $P_{\rm opt}$ stay valid; Eq. (18) only compares
    them, and the example shows that the active-set bound can be the weaker
    one also for equal priors (Evidence above).
  - The paper's equal-prior statement for the pure mirror-symmetric family
    (its Appendix B) and its pure-state reduction for $(d,N)=(2,3)$,
    Eq. (inequality_pgm_dN23), concern pure states and are untouched; the
    example uses mixed states.
- **Open here:**
  - whether Eq. (18) holds for equiprobable pure states;
  - for which $(d,N)$ mixed equiprobable counterexamples exist beyond
    $(2,3)$.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority; the journal
wording is seat-reported, and the quotations are from the arXiv v2 source.
The Lean kernel verifies the encoded statement and its axiom closure. Its
correspondence to the paper, including the nonzero-effect reading of $I_+$,
the real parts of the traces and the weakest reading of "the optimal POVM",
is checked by reading the source and the definitions.
