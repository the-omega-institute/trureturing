---
slug: sekatski-guryanova-kothakonda-skotiniotis-2025-amplitude-damping-measure-prepare-cloning
bibkey: sekatskiguryanovakothakondaskotiniotis2025cloning
doi: 10.48550/arXiv.2509.08059
url: https://arxiv.org/abs/2509.08059v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.result
---

# No finite measure-and-prepare process perfectly clones the amplitude-damping family

## Problem

P. Sekatski, Y. Guryanova, N. B. T. Kothakonda and M. Skotiniotis, *Cloning Quantum Channels*, arXiv:2509.08059v1 (2025), Section V, amplitude-damping channels, performance comparison, state:

> In particular, it achieves ${\rm F}_{\rm CJ}^{\ADset|\rm
> coh}=1$ at $N=M$, which, for amplitude-damping channels, we conjecture to be impossible for any measure-and-prepare process.

This quotation is from the downloaded v1 source `arxiv_v1.tex`, lines 1684–1685, md5 `abcdd29ea99d1c5adf0206c6b9a9d211`. The source macro `\ADset` denotes the amplitude-damping family; the coherent process is the subject of “it”. The arXiv abstract page supplies the arXiv-issued DOI in the front matter.

The source defines measure-and-prepare processes as a measurement consuming $N$ channel queries, followed by an outcome-dependent global $M$-qubit channel preparation (TeX lines 1094–1103). Its preparations need not be tensor powers of an estimated channel; that narrower class is introduced separately at lines 1105–1115.

Issue [#20683](https://github.com/the-omega-institute/trureturing/issues/20683) fixes the target as impossibility of one such process reproducing $\mathcal E_\gamma^{\otimes N}$ for every $\gamma\in[0,1]$, at $N=M\geq1$. This is proved for finite outcome sets with the trace-pairing interpretation specified below. The compiled statement also allows every $N\geq0$ and every $M\geq1$ independently.

Precisely, the module defines the following objects:

- `adChoi` is the unnormalized, reference-first Choi matrix $J_\gamma$ of the source's Kraus operators $A_0=\operatorname{diag}(1,\sqrt{1-\gamma})$ and $A_1=\begin{pmatrix}0&\sqrt\gamma\\0&0\end{pmatrix}$ (source TeX lines 1538–1553). Its entry at $((r,o),(r',o'))$ is $\sum_{k=0}^1 A_k(o,r)\overline{A_k(o',r')}$.
- `D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap (H := fun _ => Fin 2 × Fin 2) (fun _ : Fin n => J_γ)` supplies the coordinate tensor power: for assignments $x,y:\operatorname{Fin}n\to\operatorname{Fin}2\times\operatorname{Fin}2$, its entry is $\prod_i J_\gamma(x_i,y_i)$. At $n=0$ this is the one-dimensional matrix with entry one.
- `IsChannelChoi` requires a preparation matrix to be positive semidefinite and to have reference marginal equal to the identity: $\sum_o K((r,o),(r',o))=\delta_{r,r'}$, where $r,r',o:\operatorname{Fin}M\to\operatorname{Fin}2$ and each pair denotes its sitewise assignment.
- `claim` says that, for every pair of natural numbers $N,M$ with $M\geq1$, there are no finite $L$, fixed complex matrices $T_\ell$ on the $N$-fold Choi space and fixed preparation matrices $K_\ell$ on the $M$-fold Choi space satisfying `IsChannelChoi`, such that for every $\gamma\in[0,1]$ the numbers $p_\ell(\gamma)=\operatorname{tr}(T_\ell J_\gamma^{\otimes N})$ are real and nonnegative, sum to one, and satisfy $\sum_{\ell=0}^{L-1}p_\ell(\gamma)K_\ell=J_\gamma^{\otimes M}$. The real nonnegative requirement is expressed using the complex order. No further positivity or tester constraints are imposed on $T_\ell$.

The definitions and the source quotations are also described in [the literature note](../Library/QuantumContext/sekatskiguryanovakothakondaskotiniotis2025cloning.md).

## Motivation

The conjecture asks whether passing the unknown channels coherently can achieve an exact task that extracting a classical outcome and preparing a channel cannot. The source's coherent construction retains the $N$ queried channels and is exact at $M=N$ (TeX lines 1639–1658). A finite-outcome impossibility result supplies the corresponding obstruction to measure-and-prepare realization, including arbitrary global preparations rather than only copies of an estimate. Exactness is a separate question from the source's approximate cloning rates and numerical comparisons.

## Gap

The bounded literature check recorded in #20683 reports:

- arXiv lists only v1, whose conjecture remains in the source text;
- INSPIRE record 2968672 lists four citing works, arXiv:2610.06723, 2607.29054, 2606.25124 and 2603.23628, with no settlement identified; OpenAlex W4416069009 reports zero citations;
- MathDB searches by title words and author surnames and a search of google-deepmind/formal-conjectures found no matching problem;
- the recorded search of `Problems/`, `Library/` and repository issues found no prior record on dev.

The v1 text and the single-version listing are directly checked. The other readings retain the attribution and limits of the issue report.

`not-found-in-searched-scope`.

## Route

Put $\gamma=1-s^2$ with $s\in[0,1]$, and write $J_s=\operatorname{adChoi}(1-s^2)$. In the ordered basis $(00,01,10,11)$ this unnormalized matrix is $J_s=w_sw_s^\dagger+(1-s^2)uu^\dagger$, with $w_s=(1,0,0,s)^{\mathsf T}$ and $u=(0,0,1,0)^{\mathsf T}$.

1. **One-qubit reduction.** For $M=n+1$, fix the last $n$ reference inputs to zero and trace their output sites. This sends every global channel Choi matrix $K_\ell$ to a qubit channel Choi matrix $R_\ell$ and sends $J_s^{\otimes M}$ to $J_s$. It commutes with finite weighted sums.
2. **Extremality.** In a decomposition $J_s=\sum_\ell q_\ell R_\ell$ with nonnegative weights and channel Choi matrices, every summand of nonzero weight annihilates the kernel vectors $e_{01}$ and $s e_{00}-e_{11}$ of $J_s$. Positivity gives these kernel relations; Hermitian symmetry and the identity reference marginal determine all remaining entries, forcing that summand to equal $J_s$. This includes $s=0$ and $s=1$.
3. **Polynomial probabilities.** Every entry of $J_s$ is polynomial in $s$. Thus $p_\ell(1-s^2)$ is the evaluation of a complex polynomial. If it is nonzero, the fixed $R_\ell$ must equal $J_s$. The $(00,11)$ entry of $J_s$ is $s$, so this can occur at at most one point for each outcome.
4. **Contradiction.** Each outcome polynomial vanishes on the interval except possibly at one point, hence has infinitely many roots and is zero. At $s=0$, equivalently $\gamma=1$, all outcome weights are therefore zero, contradicting their sum being one.

## Falsifier

The settlement would not answer the preregistered reading if the matrices or the measurement representation changed the task. The relevant boundaries are:

- **Normalization.** The source defines channel fidelity through normalized Choi states (TeX lines 400–407). The module uses $J_\gamma$, of trace two and reference marginal $I_2$; the source's state is $J_\gamma/2$, and its $M$-qubit target is $J_\gamma^{\otimes M}/2^M$. Scaling both sides preserves equality. Identifying fidelity one with equality of the normalized Choi states, and hence equality of channels, is an interpretive bridge, not a declaration of this module.
- **Measurement stage.** Applying the result to a physical finite-outcome $N$-query tester assumes that each probability has the form $\operatorname{tr}(T_\ell J_\gamma^{\otimes N})$ for a fixed matrix $T_\ell$, with any convention-dependent transpose or scaling absorbed into $T_\ell$. This tester representation is a modeling premise in #20683, not a theorem of the module. In particular, $T_\ell$ is not restricted to a POVM obtained by measuring parallel Choi states.
- **Preparations and outcomes.** Preparations are arbitrary positive semidefinite global Choi matrices with the identity reference marginal. They are fixed independently of $\gamma$. The outcome set is exactly finite, indexed by `Fin L`; arbitrary continuous outcome spaces are not quantified over.
- **Exactness.** The conclusion excludes one process that is exact throughout $[0,1]$. It does not provide a quantitative fidelity deficit uniform over processes or a strict upper bound on their fidelity supremum.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.lean` (258 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning.lean.json`, statement `sha256:7e7bdea6c385b54c5bc13eeb1bfd75c72c021137e234c6b70c839654d65982bd`.

Declaration statements:

- `result`: `sha256:37c62e80be4817f0ea53a2bf11fe854fd1b42cca1ffb84c29ffe807c2c542658`;
- `claim`: `sha256:7cc9162707ea84842faf01e9ec6a62dac85b70369dc7650876f52d6164ad3f96`.

## Triage

Tier 1 conjecture of a 2025 preprint, preregistered in issue #20683 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural query count $N$, including zero, and every natural output count $M\geq1$, no finite family of fixed matrices $T_\ell$ and global channel Choi preparations $K_\ell$ has nonnegative trace-pairing weights $\operatorname{tr}(T_\ell J_\gamma^{\otimes N})$ summing to one and weighted output equal to $J_\gamma^{\otimes M}$ for every $\gamma\in[0,1]$.

**Computed, not formalized.** None. No numerical computation is reported here; #20683 records no numerical cloning test.

**Argued, not formalized.**

- *Decisive mechanism and extension.* The obstruction is already present in one output channel: extremality prevents averaging different fixed preparations into an amplitude-damping target. In fact, for finite outcomes, the same extremality gives a stronger prose argument that needs no polynomial assumption on the weights. For each $s$, normalization supplies an outcome of positive weight, whose reduced preparation must be $J_s$. Consequently the finite set of reduced preparations would have to contain the infinitely many distinct $J_s$. This is impossible. The argument applies to any infinite subfamily of distinct amplitude-damping channels and to arbitrary nonnegative normalized weight functions; that extension is not the type of `result`.
- *Boundaries and sharpness.* Positive output count is essential: at $N=M=0$, one scalar tester and one scalar preparation, both equal to one, give weight one and the empty target exactly. Nor does impossibility for the entire interval imply impossibility for every restricted family. For the two-point family $\gamma\in\{0,1\}$, one query on input $|1\rangle$ gives $|1\rangle$ or $|0\rangle$, respectively. Measuring in that basis identifies the channel and permits any number of perfect prepared outputs. These are explicit mathematical constructions, not additional compiled declarations.
- *Neighbouring questions.* The formal result covers arbitrary finite $N$ and all positive $M$, including $M<N$, $M=N$ and $M>N$. It supplies no numerical approximation bound. Removing the finite-outcome restriction, proving the tester and fidelity bridges in Lean, and bounding the optimal fidelity away from one remain outside this settlement; no conclusion on those questions is asserted.
- *Effect on the paper.* With the stated tester and fidelity bridges, the conjectured exactness separation at $N=M\geq1$ is established for finite-outcome processes: the coherent construction is exact, while each such measure-and-prepare process misses at least one amplitude-damping channel. The source's approximate comparisons near $M=N$ (TeX lines 1687–1695), its separate SDP/PPT comparison for $1\to2$ (lines 1088 and 2898–2912), and its asymptotic replication estimates (lines 1574–1607 and 1673–1679) receive no quantitative verification from this result. No theorem conditional on the conjecture is identified in the source's performance-comparison and conclusion passages (lines 1662–1771); the settlement supplies the exact finite-outcome separation proposed there.

### Application to finite adaptive testers in a fixed causal order

The [existing quantum-network source](../Library/QuantumChannels/chiribella2009networks.md)
supplies the following modeling bridge for the operational class specified
here. This is an ordinary source-backed application of its comb results
to `claim`, not an additional declaration or kernel verification. The
formal statement and evidence above retain their stated scope.

**Operational assumptions.** Fix finite $N\geq1$, finite $L$, finite
input and output spaces $A,B$, and fixed product bases. There are exactly
$N$ chronological slots, each invoking the same unknown memoryless CPTP
map $\mathcal E:A\to B$. Every invocation has fresh inaccessible
environment: a device with persistent hidden memory need not meet this
contract. The initial state, finite-dimensional quantum memories, finite
classical record registers, controls and final measurement are fixed
independently of $\mathcal E$. A fixed finite adaptive policy may
condition controls on earlier records. Its record probabilities depend
on $\mathcal E$; its control table does not. The final outcome set is
$\{1,\ldots,L\}$, with all outcomes, including failures, retained and
total probability one. There is no source-dependent postselection in
this normalized tester.

After outcome $\ell$, prepare a fixed global CPTP channel
$\mathcal F_\ell:C\to D$, independently of the unknown parameter and
with no further call to $\mathcal E$. For the cloning application,
$A=B=\mathbb C^2$ and $C=D=(\mathbb C^2)^{\otimes M}$.
These are channel preparations, not preparations of Choi states, and
need not be tensor powers of a one-qubit channel.

**Source and convention map.** CDP §II.A, Eqs. (1)–(4) and Lemmas 1
and 3, use the unnormalized output-first operator
$C_{\mathcal E}=(\mathcal E\otimes\mathrm{id}) (|\Omega\rangle\langle\Omega|)$.
The module instead uses

$$
J_{\mathcal E}=(\mathrm{id}\otimes\mathcal E)
 (|\Omega\rangle\langle\Omega|),\qquad
|\Omega\rangle=\sum_a|a,a\rangle,\qquad
\operatorname{Tr}_{B}J_{\mathcal E}=I_A.
$$

Thus $\operatorname{Tr}J_{\mathcal E}=\dim A$, with no normalization
factor. The two conventions differ by a swap, not a partial transpose.
Label the tested ports $H_{2j-2}=A_j,\ H_{2j-1}=B_j$,
$1\leq j\leq N$, and choose the source factor order

$$
D_N=B_N\otimes A_N\otimes\cdots\otimes B_1\otimes A_1.
$$

The module's sitewise assignment coordinates correspond to
$F_N=\bigotimes_{j=1}^N(A_j\otimes B_j)$. Fix the real permutation
unitary $U_N:F_N\to D_N$ by

$$
|a_1,b_1,\ldots,a_N,b_N\rangle
 \longmapsto |b_N,a_N,\ldots,b_1,a_1\rangle.
$$

Disjoint memoryless channel slots have tested comb

$$
R_{\mathcal E}=U_NJ_{\mathcal E}^{\otimes N}U_N^\dagger
$$

by the link product on disjoint ports (CDP §II.B, Eq. (15)).
This tensor expression describes the inserted process; the adaptive
surrounding circuit need not run in parallel.

CDP Corollary 2 and Eq. (38) give the forward composition-to-probability
rule. Definition 11/Eq. (66), Lemma 8 and Theorem 11 (§IV.E, PDF p. 17)
characterize and realize the finite testers: the surrounding experiment
has fixed $P_\ell\succeq0$ with

$$
p_\ell(\mathcal E)=\operatorname{Tr}(P_\ell^{\mathsf T}R_{\mathcal E})
 =\operatorname{Tr}(T_\ell J_{\mathcal E}^{\otimes N}),\qquad
T_\ell=U_N^\dagger P_\ell^{\mathsf T}U_N\succeq0.
$$

Here ${\mathsf T}$ is full ordinary matrix transpose in the fixed
product basis, not an adjoint or a partial transpose. All $T_\ell$
are independent of $\mathcal E$. Finite adaptive records can be
included as orthogonal memory states: an instrument writes a record,
and later fixed CPTP controls read it. Coarse-graining the final
histories sums positive tester elements. This is within CDP's
finite-dimensional network and instrument realization (§III.C,
Theorems 3–4; §IV.D, Definition 10 and Theorem 10).

**Causal normalization.** Use Lemma 8 with the general deterministic
comb recursion, CDP Eq. (25), equivalently Theorem 5/Eq. (40).
The tester's own ports are
$\widetilde H_0=\mathbb C,\ \widetilde H_{2j-1}=A_j,\ \widetilde H_{2j}=B_j,\ \widetilde H_{2N+1}=\mathbb C$.
Removing these scalar endpoints gives

$$
\begin{aligned}
\sum_\ell P_\ell&=I_{B_N}\otimes\Theta_N,&
\Theta_k&\succeq0,\\
\operatorname{Tr}_{A_k}\Theta_k
 &=I_{B_{k-1}}\otimes\Theta_{k-1}\quad(2\leq k\leq N),&
\operatorname{Tr}\Theta_1&=1,
\end{aligned}
$$

where, for $2\leq k\leq N$, $\Theta_k$ acts on
$A_k\otimes B_{k-1}\otimes A_{k-1}\otimes\cdots\otimes B_1\otimes A_1$,
and $\Theta_1$ on $A_1$. Consequently, with $X_k=\Theta_k^{\mathsf T}$,

$$
\sum_\ell T_\ell=U_N^\dagger(I_{B_N}\otimes X_N)U_N,\qquad
\operatorname{Tr}_{A_k}X_k=I_{B_{k-1}}\otimes X_{k-1}
 \quad(2\leq k\leq N),\qquad
\operatorname{Tr}X_1=1.
$$

Each $X_k\succeq0$. These identities are obtained by the stated port relabeling of the
general recursion; the pairing consistently follows Eqs. (38) and
(66). They are not the ordinary POVM condition
$\sum_\ell T_\ell=I_{F_N}$.
Indeed, for a deterministic tested comb,
$\operatorname{Tr}_{B_k}R^{(k)}=I_{A_k}\otimes R^{(k-1)}$.
In the total pairing, first trace $B_N$, then use
$\operatorname{Tr}_{A_N}X_N=I_{B_{N-1}}\otimes X_{N-1}$, and repeat.
The total reduces to $\operatorname{Tr}X_1=1$.
Positive $T_\ell$ and $J_{\mathcal E}^{\otimes N}$ make the weights
real and nonnegative. At $N=1$ the normalization is
$\sum_\ell T_\ell=X_1\otimes I_B$, with $X_1$ a density matrix.

The [single-slot super-instrument source](../Library/QuantumContext/burniston2020necessary.md)
also gives this scalar-output pairing and its parallel grouped-slot
specialization. Its common-preprocessor theorem is not being used as
an adaptive $N$-slot theorem.

**Application to the existing obstruction.** Let $K_\ell=J_{\mathcal F_\ell}$,
with the fixed shuffle to sitewise reference/output coordinates.
Positivity and $\operatorname{Tr}_{D}K_\ell=I_C$ are exactly
`IsChannelChoi` at the chosen $M$. Linearity gives

$$
J_{\mathrm{out}}(\mathcal E)
 =\sum_{\ell=1}^L\operatorname{Tr}
       (T_\ell J_{\mathcal E}^{\otimes N})K_\ell.
$$

Physical testers therefore supply a sufficient subclass of the
module's allowed arbitrary $T_\ell$: they obey additional positivity
and causal normalization that `claim` does not require.
Specialize $\mathcal E=\mathcal E_\gamma$ to amplitude damping.
Under the operational assumptions above, `result` excludes a single
such measure-and-prepare process reproducing
$\mathcal E_\gamma^{\otimes M}$ for every $\gamma\in[0,1]$,
for any finite $N\geq1$ and $M\geq1$, including $M=N$.
For $N=0$, the separate scalar pairing
$J_{\mathcal E}^{\otimes0}=1,\ T_\ell=p_\ell$, with fixed normalized
probabilities, connects the same no-query class to `claim`.

This supplies the stated tester modeling premise for this finite
operational class; its physical-to-matrix correspondence remains an
ordinary derivation outside the Lean module. Theorem 11's existence of
a realization supplies no bound meeting a separately prescribed memory,
gate, time or efficiency budget. No continuous outcomes, unbounded
records, infinite memory, indefinite causal order, coherently controlled
unknown dilation or fidelity gap/rate are included. Retaining and
normalizing only successful outcomes would change the probability
contract; failures here remain part of the deterministic mixture.
The native same-source state task in
[VIII, §§248–250](../docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VIII.md)
has no supplied callable-channel interface. This application grants it
no queries, state-to-channel conversion or resources and settles neither
its uniform conditional error nor its polynomial original success
$P_q^k s_{\mathcal E}(q)$.


## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The INSPIRE, OpenAlex, MathDB, formal-conjectures, citing-work and historical repository-search readings are reported in #20683 and are not independently reproduced. The source reading covers arXiv:2509.08059v1; no journal publication is identified on its abstract page. The DOI is the arXiv-issued DOI, recorded also in the Library note.

The representation of physical testers by fixed trace-pairing matrices, the correspondence between positive Choi matrices with identity reference marginal and physical channel preparations, and the fidelity-one/equality bridge are not formalized in this module. No reduction of arbitrary continuous-outcome measure-and-prepare processes to its finite-outcome statement is established. The stronger arbitrary-weight and infinite-subfamily argument, the boundary constructions, and the consequences for the source under the modeling bridges are prose arguments, not additional formal results. No uniform fidelity gap, optimal fidelity, asymptotic rate, continuous-outcome impossibility, or SDP numerical reading is verified by the settlement.
