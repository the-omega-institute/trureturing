---
slug: wallner-krupke-schmidt-fekete-2026-token-spectral-contraction
bibkey: wallner2026passbucket
doi: 10.48550/arXiv.2608.27085
url: https://arxiv.org/abs/2608.27085v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.result
---

# Token-1 spectral contraction for every finite positive-velocity chain

## Problem

T. Wallner, D. Krupke, A. Schmidt and S. P. Fekete, *Pass the Bucket: Efficient, Robust, Local Load Balancing for Teams of Heterogeneous Robots*, arXiv:2608.27085v1, Section IV.B.1, page 4:

> Conjecture 1 (Spectral contraction): The damped transfer map Mα is repeatedly applied and its spectral radius satisfies ρ(Mα) < 1, such that u → 0 for 0 < α < 1.

The statement concerns the paper's centered linear map in its rotational regime. There are $n=m+1$ robots, $m\ge1$ pair coordinates and positive velocities $v_1,\ldots,v_n$. The same damping parameter $\alpha\in(0,1)$ is used at every step. The delivered `claim` contains both the strict bound for every complex spectral value and convergence $M_\alpha^k u\to0$ for every real initial vector.

The binding source identifiers $B_\alpha$ and $M_\alpha$ are spelled `Balpha` and `Malpha` in Lean, as authorized by [#14768](https://github.com/the-omega-institute/trureturing/issues/14768#issuecomment-6082771002).

## Motivation

The source's Lemma 3 bounds $|\det M_\alpha|$ strictly below one. That product bound alone allows individual eigenvalues of modulus at least one. Conjecture 1 requires a bound on every spectral value and consequently on every centered trajectory. The frozen motivation declaration is `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.result`.

## Gap

The source leaves the full spectral contraction proof open. Lemma 2 identifies an undamped isometry, and Remark 2 places its spectrum on the unit circle, without proving the damped strict inequality. Preregistration [#14768](https://github.com/the-omega-institute/trureturing/issues/14768) specifies the literal matrices, the complete claim and the Proved settlement criterion. The scoped literature searches recorded there found no prior settlement of this exact conjecture; exhaustive absence of prior work is unverified.

## Route

Use centered endpoint values $z_0=z_n=0$ and the positive Hermitian quadratic form

$$Q(z)=\sum_{j=1}^{n}\frac{|z_j-z_{j-1}|^2}{v_j}.$$

For pair $i$, write $a=v_i$, $b=v_{i+1}$, $L=z_{i-1}$, $R=z_{i+1}$ and $c=(bL+aR)/(a+b)$. The two adjacent terms have the decomposition

$$\frac{|t-L|^2}{a}+\frac{|R-t|^2}{b}
 =\frac{a+b}{ab}|t-c|^2+\frac{|R-L|^2}{a+b}.$$

The event $E_i$ replaces $t=z_i$ by $2c-t$. Its center does not depend on $z_i$, so $E_i^2=I$; its fixed hyperplane is $t=c$. The decomposition shows $Q(E_i z)=Q(z)$. Polarization therefore makes $E_i$ a $Q$-orthogonal reflection. These claims have an algebraic paper proof from the displayed identity; the energy identity is also checked by the private `local_energy_decomposition`, `Q_dampedEvent_loss` and `Q_event` helpers.

The Token-1 event replaces the first reflection by

$$E_{1,\alpha}=(1-\theta)I+\theta E_1,
\qquad \theta=\frac{\alpha(v_1+v_2)}{v_2+\alpha v_1}\in(0,1).$$

Its loss is

$$Q(E_{1,\alpha}z)=Q(z)-4\theta(1-\theta)
 \frac{v_1+v_2}{v_1v_2}|z_1-c|^2.$$

The remaining odd events and the even phase preserve $Q$. The stacked-row identities identify the literal $A^{-1}B_\alpha$ with this damped sweep. Thus a nonzero eigenvector with eigenvalue $\mu$ satisfies $|\mu|\le1$. Equality in the loss fixes $E_1z=z$ and turns it into an undamped eigenvector. If $\mu=1$, equality of all weighted slopes, their telescoping sum and $\sum_jv_j>0$ force $z=0$. If $\mu\ne1$, the first coordinate is zero and the two-coordinate row recurrence propagates zeros through the path. Both contradict a nonzero eigenvector. Hence every spectral modulus is strictly below one.

The finite-dimensional spectrum supplies eigenvectors. Gelfand's formula supplies an eventual geometric envelope for the complex matrix powers, and continuity of matrix-vector evaluation and real parts gives every real trajectory limit. These steps are on the live proof path of `result`.

## Falsifier

A positive velocity vector, $m\ge1$, $0<\alpha<1$ and a complex spectral value of the literal $A^{-1}B_\alpha$ with modulus at least one would refute the strict spectral conclusion. A real initial vector whose powers fail to approach zero would refute the second conjunct. Matrices with a different first-row relation, nonpositive velocities or damping outside the open interval are outside this claim.

## Evidence

- Supporting module: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean`; independent content is `harmonic_dirichlet_zero` and `boundary_zero_observability`.
- Convergence helpers: `powers_tendsto_zero_of_spectralRadius_lt_one`, `complex_matrix_powers_tendsto_zero` and `real_mulVec_powers_tendsto_zero` each have `proof_shape: bind-only`. Their respective live consumers are `complex_matrix_powers_tendsto_zero`, `real_mulVec_powers_tendsto_zero` and `TokenDampedSweepContraction.result`. They instantiate pinned Mathlib spectrum, Gelfand-formula, geometric-limit and squeeze results with normalization; the supporting module retains `admission_basis: escape-witness` through its two content theorems.
- Settling module: `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean`; public definitions are `A`, `B`, `Balpha`, `Malpha`, `claim`, followed by `result : claim`.
- The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. The mathematical module build exits 0, and the exact binding-convention and inhabited-hypothesis checks exit 0.
- Both modules carry `utility: none`: their statements quantify over arbitrary dimensions and positive velocities and contain no fixed-parameter numerical certificate, enumeration, checker or numerical reduction premise.
- The Library note `Library/Dynamics/wallner2026passbucket.md` locates Lemma 2, Remark 2, Lemma 3 and Conjecture 1.

The six public theorem targets have unfinished four-slot escape audits, tracked by [#14784](https://github.com/the-omega-institute/trureturing/issues/14784). The enrollment modules compile, but no compiled source-bound `Contract.Registration` reconstructs the complete statements and supplies their four-slot and binding evidence. `result` proves the conjecture; it is not the exempt designated refutation. `DTR-Unregistered` is an observation and does not assert a mathematical failure.

## Triage

`theorem`: **Proved**, by `D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.result`, for the source's repeated Token-1 linear map.

### What the settlement shows

| Lane target item | Status | Evidence |
| --- | --- | --- |
| Events are $Q$-orthogonal reflections | proved | The algebraic paper proof in Route: the center is unchanged, $E_i^2=I$, and the local decomposition preserves $Q$. Private kernel-checked `Q_event` supplies the energy identity. |
| The damped event is $(1-\theta)I+\theta E_1$ with $\theta=\alpha(v_1+v_2)/(v_2+\alpha v_1)$ | proved | Literal first-row algebra in `damped_first_formula`, positivity in `theta_pos_lt_one`, and `source_factorization`; all are private helpers on `result`'s path. |
| Nonexpansiveness and observability exclude unit-modulus eigenvalues | proved | Private `Q_sweepTheta_le`, `Q_sweepTheta_eq_iff`, `damped_sweep_eigen_norm_lt_one`; public supporting `harmonic_dirichlet_zero`, `boundary_zero_observability`; public settling `result`. |
| Source Lemma 2 and Remark 2 hold for the same $Q$ | proved | Algebraic paper proof below, using the checked `Q_phase` and `sweep_stacked` identities. No separate public undamped-spectrum theorem is claimed. |
| Token-all and products mixing $M$ and $M_\alpha$ | open | The claim uses powers of one fixed Token-1 map. It does not quantify over switching sequences or the all-token event rule. |
| RQ1: eventual rotational, catch-up-free regime | open | The collision process's entry into the linear regime is outside `claim`. |
| Contraction rate against damping and velocities | computed | The pinned experiment entry below, script SHA-256 and command exit 0; the sample covers 4,400 instances with $2\le n\le12$. A certified uniform rate is open. |

For the undamped map $M=A^{-1}B$, `sweep_stacked` gives $A\,\mathrm{sweep}(z)=Bz$, while `A_isUnit` gives invertibility. Hence $M=E_{\rm even}E_{\rm odd}$. Two applications of `Q_phase` give $Q(Mz)=Q(z)$. The form is positive definite: $Q(z)=0$ makes each adjacent difference zero, and the zero endpoints force the whole path to vanish (`Q_eq_zero_imp`). Its real matrix has diagonal entries $1/v_i+1/v_{i+1}$ and adjacent entries $-1/v_{i+1}$. Thus $M^TGM=G$, supplying the source's Lemma 2 with this explicit $G$. For a nonzero eigenvector, $Q(Mz)=|\mu|^2Q(z)$ forces $|\mu|=1$, supplying Remark 2. This is a paper argument using the checked identities, rather than a new public Lean statement.

Conjecture 1 now supplies the source's asymptotic centered convergence conclusion within its rotational regime. It also supplies the strict determinant bound of Lemma 3 by the finite product of eigenvalue moduli. It supplies no entry-time bound, switching-product convergence or optimal damping parameter. The endpoint values $\alpha=0,1$ are excluded; at $\alpha=1$ the source has the undamped unit-circle spectrum, so the open damping interval is material. No uniform spectral gap over all dimensions and all positive velocity vectors is asserted.

### Numerical contraction-rate scope

Experiment: [pinned numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/wallner-krupke-schmidt-fekete-2026-token-spectral-contraction). Command in that directory: `python3 check.py` (NumPy); exit 0. Script SHA-256: `e32edd6fcaf0d309de0eef158a0d65e530b5fc82f635756f870194e78672eedd`.

The program fixes seed 7, uses 400 instances at each $n=2,\ldots,12$, mixes velocities sampled uniformly from $[0.05,20]$ with values in $\{1,2,3,0.5\}$, and chooses damping from a uniform sample in $(0.001,0.999)$ or the values $0.5,0.01,0.99$. Its final readings are:

| Reading | Value |
| --- | --- |
| Instances | 4400 |
| Maximum computed $\rho(M_\alpha)$ | 0.9999999999972705 |
| Maximum computed undamped modulus deviation $\max \bigl\lvert\lvert\mu\rvert-1\bigr\rvert$ | $4.218847493575595\cdot10^{-15}$ |
| Consistency $B_1=B$ | Every instance satisfies the program's `np.allclose` assertion |

These are floating-point sample readings, with no certified error bound or uniform contraction rate. The program prints no optimizer or per-instance damping recommendation.

## ASSUMED-UNVERIFIED

The literature search is scoped and does not establish exhaustive publication priority. NumPy rounding has no certified error envelope. Token-all, mixed products, certified quantitative rates and RQ1 remain open in this delivery. The original model presumes the rotational linear regime; convergence of the full collision process into that regime is not established. The escape audit is unfinished at #14784; no `declared_validated` registration is claimed.
