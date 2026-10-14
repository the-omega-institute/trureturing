---
slug: bae-bera-chruscinski-hiesmayr-mcnulty-2022-four-mub-bound-entanglement
bibkey: baebera2022mubbound
doi: 10.1088/1751-8121/acaa16
url: https://arxiv.org/abs/2108.01109
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.result
---

# Four MUBs detect a PPT state in dimension eight

## Problem

J. Bae, A. Bera, D. Chruściński, B. C. Hiesmayr and D. McNulty,
*How many mutually unbiased bases are needed to detect bound entangled
states?*, Journal of Physics A 55 (2022), 505303,
[arXiv:2108.01109v2](https://arxiv.org/pdf/2108.01109v2),
Section VIII, Conjecture 1:

> Conjecture 1. If d = 2^r and r > 1, the minimal number of MUBs required for bound entanglement detection equals m = d/2 + 1 = 2^{r−1} + 1.

The preceding sentence specifies the witness $W^\Gamma(\mathcal M_m,s)$.
Equation (4) defines $W(\mathcal M_m,s)=((d+m-1)/d)I-B(\mathcal M_m,s)$;
partial transposition conjugates the second factor of each equal-column
tensor projector. The computational term pairs $\ell$ with $\ell+s$
modulo $d$. The source's Eqs. (2)–(3) establish nonnegative expectation
on separable states. This source result supplies the interpretation of
negative expectation as entanglement detection; this module does not
formalize separability or the separable-state bound.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $d=2^r$, $r>1$ | `claim` quantifies over natural `r` with `2 ≤ r` and dimension `Fin (2 ^ r)` | The same integer range |
| Fewer than $2^{r-1}+1$ MUBs cannot detect bound entanglement | Every natural `m` below the threshold in `claim` | Necessity half of the minimum equality |
| Pairwise mutually unbiased orthonormal bases | `IsMUBFamily`: unitary matrices and all distinct-basis squared overlaps equal to $1/d$ | Columns are the basis vectors |
| Canonical basis $B_0$ | `IsMUBFamily` sets basis zero to the identity whenever `0 < m` | Source convention; no nonempty-family assumption is added |
| Source witness and modular shift | `witnessGamma` with every `s : Fin d` | Literal Eq. (4) after partial transposition; column projectors use `Matrix.vecMulVec` directly |
| PPT density matrix with negative expectation | `DetectsBoundEntanglement` uses the existing `IsDensity` and `partialTransposeB`, and the real trace is strictly negative | Literal binding convention in #16454 |
| Refutation of the universal necessity statement | `result : ¬ claim`, using $r=3$, $m=4$, $s=1$ | One counterexample refutes the equality; optimality of four is not asserted |

The four public definitions have complete defining formulas in the
Blueprint. Natural subtraction in $r-1$ is harmless under $2\le r$.
The predicates are total at zero dimension and zero family size, but
the refutation uses dimension eight and four bases. The computational
basis convention is from the source, and positivity, normalization and
strict negativity all remain requirements.

## Motivation

This is the source's measurement-resource question for its own witness.
At $d=8$ the conjectured lower bound is five. Four bases with a PPT
state of negative witness expectation therefore invalidate that lower
bound. Strict positivity and full rank are additionally checked by exact
computation; the Lean settlement needs only positive semidefiniteness.

## Gap

Preregistration [#16454](https://github.com/the-omega-institute/trureturing/issues/16454)
identifies the published Tier-1 conjecture and its literal conventions.
The source and literature checks in that issue are attributed to the
Claude Code orchestrator. The codex-cli literature examination reports
no prior answer within its examined scope: eighteen indexed citing works,
with seventeen full texts read, plus the PARTIQAL presentation, GETF
witnesses, the Quantum 2026 network-witness paper, the mirrored-witness
paper and the two Vienna theses. The GETF and worked mirrored examples
concern dimension three; the Kilian thesis uses complete MUB sets in
dimension eight; the Freiler thesis concerns qutrits. None of these
reported readings supplies this source-witness, four-basis counterexample.
Citation-index completeness remains `ASSUMED-UNVERIFIED`; the full text
of *Optimality of generalized Choi maps in M3* is inaccessible in the
reported screen. Repository searches by names, defining expressions and
conclusion shapes identify no existing owner of this settlement in the
examined dev revision.

## Route

Take the four bases $I$, $H/\sqrt8$, $\operatorname{diag}(a)H/\sqrt8$
and $\operatorname{diag}(b)H/\sqrt8$, with
$H[x,k]=(-1)^{x\cdot k}$ on the three binary coordinates,
$a=(1,1,i,i,i,-i,-1,1)$ and
$b=(1,1,1,-1,i,i,-i,i)$.
The private `fourBases_mub` certifies the unitary and overlap conditions.
The rational state is $\rho=M/10134$, arranged over the eight XOR sectors
$h=x\mathbin{\mathrm{xor}}z$. Each sector is
$\left[\begin{smallmatrix}A&B\\B&A\end{smallmatrix}\right]$.
The private `ldl_certificate` assembles thirty-two separate exact LDL
identities for the $4\times4$ matrices $A\pm B$ of the state and its
partial transpose; `pivots_positive` verifies 128 positive pivots.
The existing private owner `ConstructionReduction.Blocks.psd_block`
is used directly in `sector_psd`. Congruence, finite sums, submatrices
and nonnegative scaling produce `rho_density` and `rho_ppt`.
The private `witness_trace` gives
$\operatorname{Tr}(W^\Gamma(\mathcal M_4,1)\rho)=-14/563$.
The sole public theorem `result` combines these facts to refute `claim`.

## Falsifier

At $r=3$ the claim forbids detection with $4<5$ bases for every shift.
The certified family at $s=1$ has a density matrix, positive partial
transpose and strictly negative real expectation. It contradicts that
instance of the universal statement. Neither a non-MUB family nor
failure of positivity or normalization is used.

## Evidence

The settling declaration is
`D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.result`,
in `D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.lean`.
Its canonical exposition is
`Blueprint/D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation.scribe.cs`.
The admission basis is `open-problem-resolution (#16454; Refuted)`;
the computational utility is `certified-instance` under `basis=refutes`.
The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment:
[exact four-MUB certificate check](https://github.com/the-omega-institute/trureturing-experiments/tree/9989ac1b82e94db46ed3fe76da5605c2bb662060/docs/reports/bae-bera-chruscinski-hiesmayr-mcnulty-2022-four-mub-bound-entanglement/).
Command from that repository:
`python3 docs/reports/bae-bera-chruscinski-hiesmayr-mcnulty-2022-four-mub-bound-entanglement/check.py`.
Exit code: 0; result: `ALL_OK`.
`check.py` SHA-256:
`23624b3e279a9f224adb8386cd9d21f06d2dfda15ef487b2136c908d4efde18d`.
`certificate.json` SHA-256:
`a4f94159eeb609dcca0e8a3017d73d5d2cb2de69f43ff830a9c4bcc6f41cfa05`.
The exact Gaussian-rational tested scope is this one four-basis family
at $d=8$, shift $s=1$ and state $\rho=M/10134$. It checks all basis
overlaps, trace one, positive definiteness of the $64\times64$ state and
its partial transpose, and the exact expectation $-14/563$. It does not
enumerate other families, dimensions or mixed-state parameters.

## Triage

### What the settlement shows

- **Mechanism, kernel-checked at $d=8$, $m=4$, $s=1$.** The state
  retains coherence within several XOR sectors. `fourBases_mub`,
  `ldl_certificate`, `pivots_positive`, `rho_density`, `rho_ppt` and
  `witness_trace`, consumed by `result`, certify a MUB family, density
  and PPT positivity, and expectation $-14/563$. The thirty-two LDL
  identities keep the sector blocks positive while the three MUB
  correlators and the shifted diagonal term yield negative expectation.
  As an explanatory trace calculation, their total normalized reading
  equals $11/8+14/563>11/8$, exceeding the source's separable bound.
  This displayed total is an explanation of `witness_trace`, rather
  than an additional public Lean theorem.
- **Full rank, computed.** The pinned experiment's exact positive
  LDL pivots certify positive definiteness of both $\rho$ and
  $\rho^\Gamma$ in the tested instance. Strict positivity and full
  rank are computation results; Lean's stated detection predicate
  requires positive semidefiniteness.
- **Mixture threshold, computed by exact trace arithmetic; family
  consequence proved in prose.** For
  $\rho_\lambda=(1-\lambda)\rho+\lambda I/64$, the witness has trace
  $(11/8)64-8-3\cdot8=56$: each normalized rank-one tensor projector
  has trace one. Hence
  $\operatorname{Tr}(W^\Gamma\rho_\lambda)
  =-(1-\lambda)14/563+7\lambda/8
  =(-112+4053\lambda)/4504$.
  Its zero is $112/4053=16/579$, so it is negative for
  $0\le\lambda<16/579$. Convexity preserves trace one, positivity
  and PPT on $0\le\lambda\le1$; applying the source's separable
  bound gives detection throughout that interval below the zero.
  These trace and convexity derivations establish the originally
  seat-reported family consequence in prose. The pinned program
  tests $\lambda=0$ only, and no Lean theorem for the parameter
  family is asserted.
- **Three bases at $d=8$, open.** This counterexample does not decide
  whether a three-basis family and the source's witness can detect a
  PPT entangled state in dimension eight.
- **The true minimum for every $d=2^r$, open.** `result` supplies
  a four-basis upper bound at $r=3$ via its explicit instance; it
  supplies no optimality proof or general-dimension classification.
- **Source sufficiency, source-attested and unaffected.** Theorem 1
  proves non-decomposability for $m>d/2+1$ under $d>2$, $s>0$ and
  $2s\ne d$. Its proof does not assume Conjecture 1. Refuting the
  conjectured necessity half does not invalidate that theorem or
  the source's dimension-four examples. Statements requiring the
  conjectured minimum as a universal lower bound cannot retain
  that lower bound at $d=8$.
- **Literature status, bounded reading.** No prior answer is reported
  in the examined works described in Gap. This is a scope-limited
  literature conclusion, not proof of complete novelty or of the
  absence of a result elsewhere.

## ASSUMED-UNVERIFIED

Completeness outside the examined literature and citation index is
unverified. The inaccessible Choi-map full text and the visual
typesetting of the two university theses remain unverified; thesis
text was read through the university index. The Lean theorem does not
formalize separability, the separable-state witness bound, strict
positivity, the mixture family or the optimal number of bases. The
physical interpretation uses the source's witness bound, and the
remaining minimum questions are open.
