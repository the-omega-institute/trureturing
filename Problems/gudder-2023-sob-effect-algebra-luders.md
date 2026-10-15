---
slug: gudder-2023-sob-effect-algebra-luders
bibkey: gudder2023dual
doi: null
url: https://arxiv.org/abs/2302.12243v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/LudersSubObservableClosure.result
---

# An unsharp qubit Lüders image violates ambient Sob sum closure

## Problem

Stanley Gudder, *Dual Quantum Instruments and Sub-Observables*, arXiv:2302.12243v1, Section 3, after Theorem 3.1:

> If $\mathcal I\in\operatorname{In}(H)$ and $U_{\mathcal I}=\{\mathcal I_a^*:a\in\mathcal E(H)\}$, then we conjecture that $U$ need not be a Sob effect algebra.

Example 3 asks:

> If $\mathcal L_x(\rho)=a_x\circ\rho$ is an arbitrary Lüders instrument, we do not know whether $U_{\mathcal L}$ is a Sob effect algebra. However, in the case where $a_x$ are projections (we then call $\mathcal L$ sharp) we can show that it is.

This is a Tier 1, explicitly published conjecture and question, preregistered as [#16759](https://github.com/the-omega-institute/trureturing/issues/16759). The conjecture is **Proved** by a finite counterexample to universal closure; the arbitrary Lüders question is answered negatively. The universal closure assertion is `claim`, and the settling theorem is `result : ¬ claim`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Common outcome space, positive additive outcome values, total at most $I$ | `Fin n`, finite event sums, `IsSubObservable` | Each outcome is PSD and the complement of the total is PSD. Finite all-events space suffices for an existential counterexample. |
| Effect $0\le a\le I$ | PSD body in `ludersImage`; `TypedEscapeNeedsPositivity.IsEffect` in the proofs | Both $a$ and $I-a$ are PSD, equivalently $0 \le a \le I$ under `MatrixOrder`. |
| $U\subseteq\operatorname{Sob}(H)$ | First conjunct of `IsSobEffectAlgebra` | Every member is a sub-observable. |
| (S1) an observable $Z\in U$ | Existential $Z$, with sub-observability and total $I$ | The observable body is inlined literally; no duplicate `IsObservable` definition is added. |
| (S2) $Z-A\in U$ for $A\in U$ | Complement conjunct with the same $Z$ | No separate choice of $Z$ is allowed. |
| (S3) $A,B\in U$ and $A+B\in\operatorname{Sob}(H)$ imply $A+B\in U$ | Final conjunct | Pointwise addition with ambient sub-observability as antecedent. |
| Lüders action $K_xaK_x$, $K_x=a_x^{1/2}$ | `ludersImage`; PSD $K_x$ and $\sum_x K_xK_x=I$ in `claim` | A single effect supplies every outcome; the image equality has the preregistered orientation. |
| Image need not be a Sob effect algebra | `result` | Refutes universal closure at $d=n=2$; it proves the existential conjecture. |

All binders describe the source's finite matrix representation. There is no additional mathematical hypothesis on the settling theorem and no dropped clause.

## Motivation

The settling declaration is `D5/S3/Quantum/Measurement/LudersSubObservableClosure.result`. Its module is [the Lean source](../D5/S3/Quantum/Measurement/LudersSubObservableClosure.lean), with [the Blueprint](../Blueprint/D5/S3/Quantum/Measurement/LudersSubObservableClosure.md). The literature source is [gudder2023dual](../Library/QuantumChannels/gudder2023dual.md).

The image of effects has an induced notion of orthogonality, but ambient sub-observable addition can be weaker than simultaneous addition of effect preimages. A concrete failure of (S3) separates those notions.

## Gap

The source proves Sob closure for sharp Lüders instruments in Example 3 and leaves the arbitrary Lüders case open. The fixed witness below resolves existence of a failure. A classification of all instruments with ambient Sob sum closure remains open.

## Route

Take
$K_0=\operatorname{diag}(4/5,3/5)$,
$K_1=\operatorname{diag}(3/5,4/5)$,
$E=\frac1{400}\begin{pmatrix}151&50\\50&151\end{pmatrix}$,
and $A_x=K_xEK_x$.

The private proofs `k_psd` and `k_complete` establish a Lüders instrument. `e_effect` proves that $E$ is an effect from positive Gram decompositions, and `a_mem` puts $A$ in its image. `double_subobservable` proves that $A+A$ is a sub-observable. `preimage_eq` uses invertibility of $K_0$ to force any preimage of $A+A$ to be $E+E$. `double_quadratic_form` gives the value $-1/100$ for the complement's quadratic form on $(1,1)$; `double_not_effect` excludes that preimage. `double_not_mem` and `not_sob` refute (S3), and `result` refutes `claim`.

Every private theorem is a consumed bind-only helper; the public settling theorem is also bind-only after expansion into pinned Mathlib and normalization. Its admission basis is `open-problem-resolution (#16759; Proved)`, with no claimed escape witness and uses the frozen generic effect owner `D5.S0.Diagonal.Lawvere.TypedEscapeNeedsPositivity.IsEffect` under `MatrixOrder`.

## Falsifier

A violation of Kraus completeness, failure of positivity of $E$ or the doubled sub-observable, a distinct effect preimage, or failure of the negative quadratic-form evaluation would invalidate this witness. The named private theorems above discharge these obligations and feed `result`. No claim about all unsharp instruments is inferred from the fixed instance.

## Evidence

The settling theorem has no hypotheses. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The Scribe has one `OpenProblemResolutionClaim`, with status `Proved`, on `result`.

### Experiment

[Exact rational check](https://github.com/the-omega-institute/trureturing-experiments/tree/020c3fb674c9a7cc5168f749cfed91ef126317cf/docs/reports/gudder-2023-sob-effect-algebra-luders), commit `020c3fb674c9a7cc5168f749cfed91ef126317cf`, file `check.py`, SHA-256 `2e5c2183a925de64aad74cb3f222cd83af6a9eba758516b51f76df92f9843aa8`. Command: `python3 /tmp/op-gud/check.py`, using the script bytes extracted from that pinned commit; exit 0, `ALL_OK`.

The program checks Kraus completeness, strict positivity of $E$ and $I-E$, positivity of both doubled outcomes and the complement of their total, non-effecthood of $2E$, and nonzero $\det K_0$. Its exact tested scope is the displayed witness plus five family members with
$(u,v)=(3/5,4/5),(5/13,12/13),(8/17,15/17),(7/25,24/25),(20/29,21/29)$.
The unique-preimage conclusion combines the checked nonzero determinant with cancellation; the program does not quantify over all matrices or all real parameters.

### Escape audit

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mechanism at the witness | Proved, kernel-checked: `e_effect`, `a_mem`, `double_subobservable`, `preimage_eq`, `double_quadratic_form`, `double_not_effect`, `double_not_mem`, `not_sob`, `result` | Ambient summed positivity accepts $A+A$, while the invertible outcome forces the non-effect preimage $2E$. |
| Coherence factor $r=24/25$ | Proved in prose by matrix multiplication below | Explains the summed map at this fixed witness; it is not a separately stated Lean theorem. |
| Diagonal family samples | Computed by the pinned experiment, exit 0 | For $u,v>0$, $u^2+v^2=1$, $u\ne v$, the proposed family uses $r=2uv$ and $E_r=((7-r)/16)I+(1/8)X$. Exactly the five listed rational pairs are checked; no parameterized Lean theorem is claimed. |
| Uniform extension of that family | Open as a formalization target | The finite computation does not certify all real $u,v$. |
| Sharp boundary | Proved in published literature: Gudder, Example 3 | Closure holds when the effects $a_x$ are projections. The argument uses orthogonal projection supports and a pinched-total preimage; sharp pinching can also remove coherence. |
| Scope of the unsharp conclusion | Open beyond the displayed witness and tested family samples | The phrase “fails as soon as the Lüders effects are not projections” has no universal force here. The displayed unequal positive diagonal family is the candidate scope; arbitrary unsharp instruments are not classified. |
| Characterization of instruments with ambient Sob sum closure | Open | No necessary-and-sufficient criterion is supplied. |
| Numerical evidence | Computed: the experiment entry above | Six exact cases, including the witness; `ALL_OK`. |
| Literature status | Literature reading: #16759 | The preregistration records a screen of seven later Gudder papers (2303.15640, 2305.17584, 2307.11223, 2307.16327, 2308.09785, 2403.08126 and 2403.18925) without a settlement. Completeness is `ASSUMED-UNVERIFIED`. |
| Consequences for the source's other results | Published literature boundary: Theorems 3.1–3.4 and Example 3 | Their stated hypotheses remain in force. In Theorem 3.2, orthogonality of preimages differs from ambient sum compatibility, so failure of (S3) does not contradict its induced effect-algebra assertion. |

For the coherence calculation, if $M=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ then
$\sum_xK_xMK_x=\begin{pmatrix}a&(24/25)b\\(24/25)c&d\end{pmatrix}$:
the diagonal coefficient is $(4/5)^2+(3/5)^2=1$ and the off-diagonal coefficient is $2(4/5)(3/5)=24/25$. Thus the doubled total has diagonal $151/200$ and off-diagonal $6/25$. Its complement is positive, while $I-2E$ has quadratic form $-1/100$ on $(1,1)$. The latter two properties are kernel-checked in `double_subobservable` and `double_quadratic_form`; the general matrix display in this paragraph is a prose derivation.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The seven-paper screen recorded in #16759 is finite and does not exclude every unpublished or uncatalogued settlement; citation APIs and Firecrawl availability limited the source screen recorded in #16759. The universal real-parameter family and a full instrument classification are not proved by this module. No assertion is made that every nonprojective instrument fails closure.
