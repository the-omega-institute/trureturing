---
slug: davino-et-al-2025-energy-constrained-deterministic-violation
bibkey: davinoetal2025energyconstrained
doi: 10.48550/arXiv.2510.27559
url: https://arxiv.org/abs/2510.27559v3
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.result
---

# Deterministic-input violations exist at every positive energy budget below one half

## Problem

R. D'Avino, G. Senno, M. Alimuddin and A. Acín, *Entanglement in the energy-constrained prepare-and-measure scenario: applications to randomness certification and channel discrimination*, arXiv:2510.27559v3 (2025 preprint; v3, 2026), Section IV.A, state:

> We conjecture that this holds for all $\omega > 0$.

This is verbatim from `paper_Quantum.tex`, line 284 (MD5 `012a72f4d8cfd30e14dc3813eda8f546`). The preceding sentence's assertion is the existence of behaviors allowing entanglement that are deterministic for input $x=0$ but violate the separable deterministic-input inequality. The global restriction is $\omega\in[0,1/2)$ (line 154), so the conjecture concerns every $0<\omega<1/2$.

The paper considers a shared state $\sigma_{PM}$, local channels $\Lambda_x:P\to S$ for $x\in\{0,1\}$, and a binary POVM $\{\Pi^0,\Pi^1\}$ on $S\otimes M$. Its behavior formula is $p(b|x)=\operatorname{Tr}[\Pi^b(\Lambda_x\otimes\mathrm{id}_M)(\sigma_{PM})]$ (lines 137–148), and $E_x=p(0|x)-p(1|x)$ (lines 165–166). For separable devices with $p(0|0)=1$, its displayed inequality is:

> $E_1\geq 2(1-2\omega)^2-1=:I_\mathrm{det}^{\omega,\mathrm{sep}}$

This is line 268, equation labelled `eq:deterministic-ineq-for-fixed-input-0`. The source defines $\mathcal Q_\omega^{\mathrm{ent}}$ by allowing entanglement, rather than by requiring an additional entanglement test (line 158).

Issue [#22022](https://github.com/the-omega-institute/trureturing/issues/22022) fixes the following finite-dimensional reading, which is proved. For every real $0<\omega<1/2$, there exist natural dimensions $d_p,d_s,d_m$, a complex matrix $\sigma$ on $P\otimes M$, two complex-linear matrix maps $\Lambda_x:P\to S$, a matrix $H$ and vector $g$ on $S$, and two effects $\Pi^b$ on $S\otimes M$, such that:

- $\sigma\succeq0$ and $\operatorname{Tr}\sigma=1$;
- each $\Lambda_x$ is completely positive and preserves the trace of every complex matrix;
- $H=H^\dagger$, $g^\dagger g=1$, $Hg=0$, and $H-(I-|g\rangle\langle g|)\succeq0$;
- $\Pi^b\succeq0$ for both outcomes and $\Pi^0+\Pi^1=I$;
- $\operatorname{Re}\operatorname{Tr}[H\Lambda_x(\operatorname{Tr}_M\sigma)]\leq\omega$ for both inputs;
- $p(0|0)=1$ and $p(0|1)-p(1|1)<2(1-2\omega)^2-1$.

Here the Lean definition `probability` takes the real part of the Born trace displayed above. The claim has no separate separability or entanglement predicate. The source permits arbitrary, including infinite, dimensions; finite witnesses are sufficient for its existential question. See also [the literature note](../Library/Entropy/davinoetal2025energyconstrained.md).

## Motivation

The source uses energy constraints to certify randomness without specifying the devices' internal implementation. Section IV.A asks whether violating the separable deterministic-input inequality still certifies randomness on input zero when the devices may share entanglement. A device with $p(0|0)=1$ has a perfectly predictable outcome on that input. Producing such a device beyond the inequality's bound at every admissible positive budget establishes the scope of that warning, including budgets arbitrarily close to zero.

## Gap

The bounded literature check recorded in #22022 reports:

- the v3 source retains the conjecture and supports it numerically;
- the orchestrator's web search found the source and Ranu, Wooltorton, Abbott and Fawzi (2026), arXiv:2608.27357v1, whose full-text reading was reported to concern SDP lower bounds on randomness rather than a settlement of this conjecture;
- the preregistration's additional literature report found no settlement in D'Alessandro, Karlsson and Roch i Carceller (2026), arXiv:2608.09667v1, or Li, Wu, Chiribella and Ramanathan (2026), arXiv:2606.12173v1;
- in the repository, `Library/QuantumChannels/rochicarcellertavakoli2025energyentanglement.md` and `Problems/roch-i-carceller-tavakoli-2025-energy-restricted-unitary-encoding.md` cite the source only for its two-input resourcelessness theorem, and no repository record settles or duplicates this conjecture; the preregistration's search report records zero OpenAlex citing works and no MathDB or formal-conjectures match.

`not-found-in-searched-scope`. These are bounded search reports, with the unreproduced readings identified below.

## Route

All parameters in the following lemmas are real. The auxiliary lemmas are private to the module.

1. **Positive parameters and a strict overlap bound.** `parameters` assumes precisely $0<\omega$ and $\omega<1/2$. Its construction sets $t=(1-2\omega)/8$ and
   $s=\sqrt{1-\omega}$, $r=\sqrt{\omega(1/2-t)}$, $q=\sqrt{\omega(1/2+t)}$, $a=\sqrt{1-\omega-2\omega t}$, $h=\sqrt{2\omega t}$.
   It supplies $s,r,q,a,h>0$, $s^2=1-\omega$, $r^2+q^2=\omega$, $q^2-r^2=h^2$, $a^2+h^2=s^2$, and $(sa-2rq)^2<(1-2\omega)^2$. In this proof, $X=sa$ and $Y=2rq$ satisfy $X\geq1-\omega-2\omega t$, $Y\leq\omega$, $X<1-\omega-\omega t$, and $Y\geq\omega(1-4t^2)$. With $0<t<1/8$, these give $0<X-Y<1-2\omega$.

2. **State and measurement.** Take $d_p=d_s=d_m=2$, $\psi=s|00\rangle+r|10\rangle+q|11\rangle$, $\sigma=|\psi\rangle\langle\psi|$, $\Pi^0=\sigma$, and $\Pi^1=I-\sigma$. For any real $s,r,q$ satisfying $s^2+r^2+q^2=1$, `state_measurement` gives $\sigma\succeq0$, $\operatorname{Tr}\sigma=1$, positivity of both effects, and their sum equal to $I$.

3. **Channels.** Input zero uses Kraus operators $I,0$. Input one uses
   $K_0=\begin{pmatrix}-a/s&0\\h^2/(sq)&r/q\end{pmatrix}$ and
   $K_1=\begin{pmatrix}-hr/(sq)&h/q\\0&0\end{pmatrix}$.
   For real $s,r,q,a,h$ with $s\ne0$, $q\ne0$, $q^2-r^2=h^2$, $a^2+h^2=s^2$, and either input $x\in\{0,1\}$, `kraus_complete` proves $\sum_kK_{x,k}^\dagger K_{x,k}=I$; with exactly these hypotheses, `channels` gives complete positivity and trace preservation on every matrix for $\Lambda_x(\rho)=\sum_kK_{x,k}\rho K_{x,k}^\dagger$.

4. **Hamiltonian and energies.** The hypothesis-free `ground_energy` supplies the Hermitian matrix $H=\operatorname{diag}(0,1)$ and unit vector $g=(1,0)$, with $Hg=0$ and $H-(I-|g\rangle\langle g|)\succeq0$. For real $s,r,q,a,h$ with $s\ne0$, $q\ne0$, $q^2-r^2=h^2$, and either input $x$, `energies` gives $\operatorname{Re}\operatorname{Tr}[H\Lambda_x(\operatorname{Tr}_M\sigma)]=r^2+q^2$. The parameters from item 1 make this exactly $\omega$.

5. **Joint outputs and probabilities.** For real $s,r,q,a,h$ with $s\ne0$, $q\ne0$, $q^2-r^2=h^2$, and either input $x$, `joint_output` gives $\sigma$ for input zero and $|v\rangle\langle v|+h^2|01\rangle\langle01|$ for input one, where $v=-a|00\rangle+q|10\rangle+r|11\rangle$. For real $s,r,q,a,h$ with $s\ne0$, $q\ne0$, $s^2+r^2+q^2=1$, $q^2-r^2=h^2$, and $a^2+h^2=s^2$, `probabilities` gives $p(0|0)=1$, $p(0|1)=(sa-2rq)^2$, and $p(1|1)=1-(sa-2rq)^2$. Thus, with the parameters from item 1, the input-one correlator is strictly below $2(1-2\omega)^2-1$. `result` assembles these certificates into `claim`.

## Falsifier

The construction would not settle the conjecture if its channels, energy condition, or probabilities differed from the source's model. The formal claim imposes complete positivity under every finite identity amplification, trace preservation on every complex matrix, the local energy of $\Lambda_x(\operatorname{Tr}_M\sigma)$, and a joint binary positive measurement. Its Hamiltonian conditions encode a unit ground vector at energy zero and a gap of at least one on its orthogonal complement. Its probabilities are the real parts of the source's local-channel Born traces.

There is no optimization, infimum, or supremum in `claim`: the theorem supplies actual finite witnesses for every real budget in the open interval. It proves no optimum, no positive lower bound on violation independent of $\omega$, and no separate entanglement predicate. The connection to the source's entanglement-allowed set uses the displayed model conditions; nonseparability of the explicit pure state is addressed as an argument below.

## Evidence

The canonical source is `D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.lean` (326 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.lean.json`, statement `sha256:63a4f6f270dc2bd08a8583e45fe96373ae2c6aa91a3693d994bad64995724e5c`.

Declaration statements:

- `result`: `sha256:326ad616c355993d9d3de4baac9911ce635103a53c20f519accb3fac8e6c1380`;
- `claim`: `sha256:410a42dc9a7b62e07eb5472e4cea6519a43d0eb96aa5ccdfd154f07739f3d8c3`.

## Triage

Tier 1 conjecture of a 2025 preprint, retained in its 2026 v3, preregistered in issue #22022 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every real $0<\omega<1/2$, there exist finite dimensions, a positive trace-one shared matrix, two completely positive complex-linear maps preserving every matrix's trace, a Hermitian Hamiltonian and unit ground vector satisfying the stated zero-energy and gap conditions, and a binary positive measurement, such that both local output energies are at most $\omega$, $p(0|0)=1$, and $p(0|1)-p(1|1)<2(1-2\omega)^2-1$.

**Computed, not formalized**. A 90-digit Decimal calculation evaluates the displayed Kraus construction at the eight budgets $10^{-12}$, $10^{-6}$, $1/100$, $1/10$, $1/4$, $49/100$, $1/2-10^{-6}$, and $1/2-10^{-12}$. The largest absolute residual among Kraus completeness, state and output normalization, input-zero determinism, both energy equalities, the joint-output identity, and the input-one probability formula is $3\cdot10^{-90}$. Strict violations are observed in all eight tested cases; the smallest computed correlator margin is approximately $9.6875\cdot10^{-25}$. For this tested family, replacing $t$ by $t(1+\omega/100)$ also gives a smaller $p(0|1)$ in all eight cases. These finite-precision readings establish no statement about untested budgets.

**Argued, not formalized**.

- *Decisive mechanism.* For real $0<\omega<1/2$, the overlap estimate in `parameters` turns the parameter imbalance $q^2-r^2=h^2>0$ into strict cancellation: $0<sa-2rq<1-2\omega$. The mixed output's extra $|01\rangle$ component is orthogonal to $\psi$, so it contributes no outcome-zero probability. Precisely, `joint_output` applies for real $s,r,q,a,h$ with $s\ne0$, $q\ne0$, $q^2-r^2=h^2$ and either input; `probabilities` additionally requires $s^2+r^2+q^2=1$ and $a^2+h^2=s^2$. This separates local energy control from the joint overlap controlling the measurement.

- *Entanglement and nonunitarity.* For the positive parameters supplied by `parameters` under $0<\omega<1/2$, the coefficient matrix of $\psi$ is $\begin{pmatrix}s&0\\r&q\end{pmatrix}$ with determinant $sq>0$. A product vector has coefficient rank one, so $\psi$ is not a product vector. A separable rank-one density would force every product vector in a positive decomposition to lie in its one-dimensional range, which would make $\psi$ a product vector. Thus the displayed state is entangled. The two orthogonal nonzero components $v$ and $h|01\rangle$ of the input-one output give rank two, whereas the input-zero output has rank one. A local unitary preserves joint rank, so the input-one channel is nonunitary. These conclusions are not separate predicates or conclusions in `result`.

- *The parameter choice is sufficient, not optimal.* Fix $0<\omega<1/2$ and let $f(t)=\sqrt{(1-\omega)(1-\omega-2\omega t)}-\omega\sqrt{1-4t^2}$. The square-root formulas in Route satisfy its normalization and channel-completeness identities, with nonzero $s,q$, throughout $0<t<1/8$. Writing $X=\sqrt{(1-\omega)(1-\omega-2\omega t)}$, one has $0<X<1-\omega$ and
  $f'(t)=-\omega(1-\omega)/X+4\omega t/\sqrt{1-4t^2}< -\omega+2\omega/\sqrt{15}<0$.
  At $t_0=(1-2\omega)/8$, the bounds in item 1 give $0<f(t_0)<1-2\omega$. Continuity preserves positivity and admissibility for a sufficiently small increase of $t_0$ within $(0,1/8)$, and the negative derivative decreases $f(t)^2$, hence decreases $E_1=2f(t)^2-1$. Consequently, the explicit parameter choice does not attain the best violation even within this family. The exact minimum over this family or all allowed devices remains open here.

- *Endpoint obstruction.* At $\omega=1/2$ the proposed strict bound would require $E_1<-1$, impossible for normalized nonnegative binary probabilities. At $\omega=0$, the gap and zero-energy condition force each transmitted marginal onto the same one-dimensional ground space. Positivity then forces each joint output to be $|g\rangle\langle g|\otimes\tau_M$; local trace-preserving channels leave the memory marginal $\tau_M$ unchanged. The joint outputs therefore coincide, so $p(0|0)=1$ implies $p(0|1)=1$ and $E_1=1$. Thus neither endpoint admits the same strict violation. This endpoint argument is not included in `result`.

- *Effect on the paper and neighbouring questions.* The universal warning in D'Avino et al. (2025), arXiv:2510.27559v3, Section IV.A, line 284, follows for the entire admissible positive interval: violation of the separable deterministic-input bound can coexist with a certain input-zero outcome. An adversary can guess that outcome without side information. This does not determine the source's guessing-probability optimum at a prescribed correlation value, nor assert zero randomness for every allowed behavior. The separate Section III conjecture about optimal dimensions for the unrestricted correlator, and the quantitative channel-discrimination comparisons in Section IV.B, are not settled or quantitatively strengthened by this theorem. The qubit witness construction in Route supplies an existence mechanism, not a characterization of the full behavior set.

## ASSUMED-UNVERIFIED

The bounded literature check in #22022 does not establish exhaustive worldwide novelty or priority. Its Crossref query, web-search coverage, OpenAlex count, MathDB and formal-conjectures searches, and repository search are reported readings rather than independently reproduced searches. Full-text non-settlement readings of Ranu et al. (2026), arXiv:2608.27357v1, D'Alessandro et al. (2026), arXiv:2608.09667v1, and Li et al. (2026), arXiv:2606.12173v1, remain reports in #22022; their arXiv abstracts and author metadata are independently checked. The issue's orchestrator reports a floating-point scan of 405 budgets; that scan is not reproduced by the eight-budget calculation above. The source's seesaw curves and numerical optima are not independently reproduced.

The primary conjecture, its surrounding model, and the relevant operational discussion are checked against the v3 TeX with the MD5 given in Problem. The source's general separable bound is used as a literature statement and is not proved by this module. The DOI above is the arXiv DOI displayed by the source record; no journal DOI is asserted.

The statements in “Computed, not formalized” and “Argued, not formalized” are not additional Lean conclusions. In particular, separate entanglement and nonunitarity predicates, the improved parameter choice, its optimality analysis, both endpoint obstructions, and the operational randomness interpretation are not formalized here. No optimal violation, complete behavior-region description, guessing-probability optimum, or dimension-optimality result is claimed.
