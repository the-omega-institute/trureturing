---
slug: wei-liu-2024-ccz-magic-capacity-threshold
bibkey: wei2024magicnoise
doi: null
url: https://arxiv.org/abs/2410.21215v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/CCZMagicCapacityThreshold.result
---

# Wei–Liu CCZ magic-capacity threshold

## Problem

Fuchuan Wei and Zi-Wen Liu, *Noise robustness and threshold of many-body quantum magic*, arXiv:2410.21215v1, Section VII:

> We conjecture that the magic capacity threshold for $\mathrm{CC}Z$ under local depolarizing noise is $1/3$.

The capacity maximizes robustness of magic over pure six-qubit stabilizer inputs, with $\mathrm{CC}Z$ and independent single-qubit depolarizing noise acting on the three system qubits $A$ and the three reference qubits $B$ untouched. Robustness is faithful: it equals one exactly on the real convex hull $\mathrm{STAB}_6$ of pure stabilizer density matrices. The single-qubit channel is $\rho\mapsto(1-\lambda)\rho+\lambda\operatorname{Tr}(\rho)I_2/2$.

The literal `claim` has two conjuncts: every pure stabilizer output belongs to `STAB 6` for $\lambda\in[1/3,1]$, and a pure stabilizer input with output outside `STAB 6` exists for every $\lambda\in[0,1/3)$. Noise follows the gate. The result contradicts the first conjunct at $\lambda=1/2$.

## Motivation

The gate's reference-assisted magic capacity and the magic of the three-qubit state $\mathrm{CC}Z\ket{+++}$ have different depolarizing thresholds. The six-qubit stabilizer input $\Omega=8^{-1/2}\sum_x\ket{x,x}$ retains magic at $\lambda=1/2>1/3$.

## Gap

[Preregistration #15085](https://github.com/the-omega-institute/trureturing/issues/15085) specifies the source statements, complete quantifiers, Tier 1 status, binding Lean conventions and literature screen. The source has one arXiv version. The recorded citation screen covers eight citing papers and searches the sources of arXiv:2503.20873, 2605.22603, 2506.18976 and 2608.25950, together with Wei's later papers. No settlement was found in that scope. This is an orchestrator-reported literature reading, not an exhaustive priority claim.

## Route

Use the pure stabilizer density matrix $\ket\Omega\bra\Omega$ and a separating matrix $W$. For a pure stabilizer amplitude $\phi$, set $\xi(x)=\phi(x,x)$. The module proves
$\operatorname{Tr}(W\ket\phi\bra\phi)=\frac9{16}\|\xi\|^2-|\langle\mathrm{CC}Z{+++}\mid\xi\rangle|^2\ge0$.

Diagonal restriction of a six-qubit stabilizer normal form is either zero or a scalar multiple of a three-qubit normal form. Its restricted binary phase is $b'_i=b_{A,i}+b_{B,i}$, and its quadratic phase is
$q'(x)=q(x,x)+\sum_i b_{A,i}b_{B,i}x_i^2$.
The carry term is necessary because $i^{1+1}=-1$ while binary addition gives $1+1=0$.

Proper affine supports have at most four points. For full support, an exact finite certificate over 64 quadratic coefficient strings and eight linear phase strings bounds the squared phase sum by 36. Normalization yields the squared overlap bound $9/16$. Convexity extends witness nonnegativity to `STAB 6`. The actual channel output at $\lambda=1/2$ has witness value $-7/1024$, so it is outside that convex hull.

## Falsifier

The refutation would fail if the source's capacity omitted the reference, if the stabilizer normal form or channel were mistranscribed, or if witness nonnegativity or the negative value failed. The binding conventions include the reference, nonempty affine support, quadratic binary phases, integer lifts in the exponent of $i$, and noise on $A$ only. No extra restriction is added to either quantified clause of `claim`.

## Evidence

`D5/S3/Quantum/Information/CCZMagicCapacityThreshold.result` proves `¬ claim`. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. The Scribe has one `OpenProblemResolutionClaim` with resolution `Refuted` on this settling declaration. The admission basis is `open-problem-resolution (#15085; Refuted)`, with `proof_shape: bind-only`, `escape_witness: none` and `certified-instance` utility under `refutes`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The escape audit for the newly public owner declaration `D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized` is unfinished. Issue [#15364](https://github.com/the-omega-institute/trureturing/issues/15364) records the missing lawful four-slot template and realization bridge; no `declared_validated` registration is claimed.

Experiment entry: [check.py and its directory](https://github.com/the-omega-institute/trureturing-experiments/tree/6b30824de8a244c7a672b17b9ac492bd774c9500/docs/reports/wei-liu-2024-ccz-magic-capacity-threshold). Run `python3 check.py` in that directory; exit code 0. The script's SHA-256 is `408fb9a2f4c60946504445e1d980f794336be93d3eee43b392c581a80326e052`. It enumerates 1080 pure three-qubit stabilizer states; evaluates the after-gate witness at $\lambda\in\{0,0.1,1/3,0.4,0.5,0.51,0.52\}$; checks negativity in exact rationals at $\lambda=k/1000$ for $0\le k\le500$; samples 3000 six-qubit stabilizer states with 80 Clifford generators per sample; and evaluates the before-gate witness at $\lambda\in\{1/3,1/2\}$. Numerical state enumeration and sampling are checks, not substitutes for the kernel proof.

## Triage

Tier 1; external named conjecture; settlement Refuted. This is a deposit-uncovered settlement without an atom or coverage step.

### What the settlement shows

- **Mechanism — proved in this module, with a paper interpretation.** `diagonal_normal_form`, `diagonal_overlap_bound`, `witness_pure` and `witness_nonneg` establish the diagonal restriction and separation for all stabilizer mixtures. In the Clifford measurement interpretation, CNOTs from $A$ onto $B$ followed by conditioning $B$ on $000$ flag every $X/Y$ error; only $I/Z$ errors survive. The conditional identity probability is $(4-3\lambda)/(4-2\lambda)$. The module proves the resulting matrix inequality and its strict violation at $\lambda=1/2$; it does not separately formalize a CNOT circuit API.
- **Range — computed, proved at $\lambda=1/2$.** The experiment above gives the witness polynomial $w(\lambda)=\frac9{16}(1-\lambda/2)^3-(1-3\lambda/4)^3$ at its seven after-gate sample points and exact negativity on its 501-point rational grid. `witness_value` proves $w(1/2)=-7/1024$ for the literal channel. On paper, the ratio $(1-3\lambda/4)/(1-\lambda/2)$ decreases on $[0,1]$, and cubing its value at $1/2$ gives $125/216>9/16$, proving negativity throughout $[0,1/2]$. The polynomial changes sign between $0.51$ and $0.52$; its root is $4(1-r)/(3-2r)$ for $r=(9/16)^{1/3}$, approximately $0.517$. The threshold lower bound of approximately $0.517$ uses the paper witness formula and this computed sign bracket; the uniform polynomial identity and bound beyond $1/2$ are not additional Lean theorems here.
- **Order of noise and gate — computed, with a paper explanation.** The same experiment checks equal witness values for before/after composition at $\lambda\in\{1/3,1/2\}$. On paper, Pauli errors on $A$ of the maximally entangled input transfer to $B$, where they commute with the gate on $A$. The uniform composition-order equivalence is not formalized in this module.
- **Normal form — proved in this module.** `diag_phase_certificate`, `diag_phase`, `diag_quadratic` and `diagonal_normal_form` prove the corrected diagonal restriction, including $\sum_i b_{A,i}b_{B,i}x_i^2$. The source's normal-form statement does not state this restriction rule.
- **Readings — computed.** The pinned experiment entry, command, exit code, SHA-256 and exact tested scopes are given in Evidence. The enumerated maximum squared overlap is $9/16$, the sampled six-qubit witness minimum is zero within the script's tolerance, and both composition-order checks exit 0.
- **Exact capacity threshold — open.** The witness gives a paper lower bound of approximately $0.517$; an upper bound matching it and the exact capacity threshold are unresolved here.
- **Reference assistance for $\mathrm C^{n-1}Z$ — open.** Whether its reference-assisted threshold always exceeds the state threshold is unresolved; the present settlement treats $n=3$.
- **Dephasing — open.** The source's numerical capacity threshold of approximately $0.645$ is not certified here.

The source's three-qubit state threshold $1/3$ concerns a different input and is not contradicted. The gate-capacity conjecture cannot support further consequences requiring all reference-assisted outputs to be stabilizer mixtures above $1/3$. No other dependent result of the source is refuted in this module.

## ASSUMED-UNVERIFIED

The MathDB Solutions count is unverified in the preregistration. Literature priority outside the recorded search scope is unverified. The uniform witness polynomial and the extension to approximately $0.517$ are paper deductions supported by the stated numerical readings, not kernel-checked declarations in this delivery.
