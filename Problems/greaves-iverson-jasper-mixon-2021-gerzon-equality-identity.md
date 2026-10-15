---
slug: greaves-iverson-jasper-mixon-2021-gerzon-equality-identity
bibkey: greavesiversonjaspermixon2021orthogonalframes
doi: 10.48550/arXiv.2012.13642
url: https://arxiv.org/abs/2012.13642v2
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.result
---

# Gerzon equality fixes the equiangular parameters in every dimension at least two

## Problem

G. R. W. Greaves, J. W. Iverson, J. Jasper and D. G. Mixon, *Frames over finite fields: Equiangular lines in orthogonal geometry*, arXiv:2012.13642v2, Example 5.8, page 21, asks:

> The authors do not know how to construct an ETF with any of the parameters given in Table 4. In particular, every instance of Gerzon equality that we currently know satisfies the identity a² = (d + 2)b, but this equation does not occur anywhere in Table 4 (where b = 1). Proposition 2.10 implies that a² = (d + 2)b whenever Gerzon’s bound is saturated, d ≢ₚ 0, and d ≢ₚ 1. The authors do not know if these conditions can be removed.

The answer is affirmative for every $d\ge2$. Preregistration: [#16342](https://github.com/the-omega-institute/trureturing/issues/16342). The [Library note](../Library/QuadraticForms/greavesiversonjaspermixon2021orthogonalframes.md) records Definition 2.8, Propositions 2.9–2.10 and the source locator.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite field of odd characteristic | `F : Type`, `Field F`, `Fintype F`, `ringChar F ≠ 2` in `claim` | Exact source scope |
| Dimension $d\ge2$ | `d : ℕ`, `2 ≤ d` | Explicit boundary of the affirmative answer |
| Quadratic space | `B : LinearMap.BilinForm F (Fin d → F)`, `B.IsSymm`, `B.Nondegenerate` | Arbitrary symmetric nondegenerate form in coordinates |
| $N=\binom{d+1}{2}$ vectors | `φ : Fin ((d + 1).choose 2) → Fin d → F` | Exact Gerzon cardinality |
| $(a,b)$-equiangular | `IsEquiangularSystem B φ a b` | Every diagonal pairing equals $a$; every distinct squared pairing equals $b$ |
| $a^2\ne b$ | `a ^ 2 ≠ b` | Retained hypothesis of Proposition 2.9 |
| Remove both dimension congruences | No assumption that $d$ or $d-1$ is nonzero in $F$ | Neither restriction retained |
| Parameter identity | `result : claim` | $a^2=((d:F)+2)b$ |

The two public definitions are the literal conventions of #16342. `Fin n` indexes from zero instead of one without changing the pairwise conditions. A choice of basis identifies any $d$-dimensional space with these coordinates; that transport is the coordinate interpretation, not an additional public theorem of this module.

## Motivation

The settling node is `D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.result`. Its module has admission basis `open-problem-resolution (#16342; Proved)` and `utility: none`: the result is field-parametric and dimension-unbounded, with no fixed numerical certificate.

The source's known identity excludes two characteristic classes of dimensions. The theorem includes both, and includes isotropic vectors with $a=0$.

## Gap

The identity must be obtained without assuming that $d$ or $d-1$ can be inverted. In the isotropic case the rank-one operators need not be a basis: they span the trace-zero hyperplane. An argument that assumes their independence would omit this case.

Shi–Liu–Kim–Solé, *Frames over finite fields and self-dual codes*, DOI 10.1007/s00200-023-00630-6, was read in full in the supplied literature screen; no answer to Example 5.8 was found. Wei–Luo, *Finite Tight Frames for Vector Spaces Over Finite Fields*, WCONF 2025, DOI 10.1109/WCONF64849.2025.11233785, is `ASSUMED-UNVERIFIED`: no arXiv copy was found, the IEEE page was blocked and Firecrawl returned HTTP 402. The novelty statement is only “not found in the searched scope”.

## Route

Let $P_i(x)=B(\varphi_i,x)\varphi_i$ and let $S$ be the space of $B$-selfadjoint endomorphisms. In orthogonal coordinates $\dim S=\binom{d+1}{2}$. Their trace pairings are $a^2$ on the diagonal and $b$ off it. Any linear relation between the $P_i$ has constant coefficients.

For $a\ne0$, the $P_i$ form a basis and their sum is $cI$ with $c\ne0$. For $a=0$, their sum is zero and their span is exactly $\ker(\operatorname{tr})$. The fourth-moment map $T(X)=\sum_i\operatorname{tr}(P_iX)P_i$ has the form $AX+\beta\operatorname{tr}(X)I$. Comparing a diagonal matrix unit with a selfadjoint off-diagonal pair gives $A=2\beta$. The resulting scalar equations give the identity in both cases.

In the zero-trace case the proof first derives $N=1$ in $F$ and then proves $d\ne0$ in $F$ before using $1/d$. Thus invertibility of $d$ is a derived fact in that branch, not an extra hypothesis; no invertibility of $d-1$ is required. The consumed private `parameter_identity` works over every field of characteristic different from two; `result` specializes it to the source's finite fields.

## Falsifier

A counterexample would be a field of characteristic different from two, a dimension $d\ge2$, a symmetric nondegenerate form and exactly $\binom{d+1}{2}$ vectors satisfying the two equiangular conditions and $a^2\ne b$, with $a^2\ne(d+2)b$. `result` rules out such a counterexample in the stated finite-field scope.

The restriction $d\ge2$ is necessary. At $d=1$ over $\mathbf F_5$, take $B(x,y)=xy$, the single vector $1$, $a=1$ and $b=0$. The off-diagonal condition is empty and $a^2\ne b$, but $1\ne3\cdot0$. This boundary is a prose verification, not a separate Lean theorem.

## Evidence

The mathematical source is [GerzonEqualityParameterIdentity.lean](../D5/S3/QuadraticForms/GerzonEqualityParameterIdentity.lean); its public theorem is `D5.S3.QuadraticForms.GerzonEqualityParameterIdentity.result`. All theorem proof shapes are conservatively classified `bind-only` after same-delivery expansion. The settling conclusion is admitted as the preregistered external open-problem resolution; private helpers have actual consumers. All imports are pinned Mathlib, so there are no direct frozen D5 dependencies.

The escape audit of `result` is unfinished: [#16531](https://github.com/the-omega-institute/trureturing/issues/16531). No validated Reg mirror is delivered. The attempted dependent-family registration lacks whole-family variation, slot sensitivity, dependent observational dependence, raw-source selection and current compiler binding evidence. Its failure does not change the proved mathematical statement.

Experiment: [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/5ba5d46980ad7adabdf9a7540ac583767108355b/docs/reports/greaves-iverson-jasper-mixon-2021-gerzon-equality-identity). Command: `python3 check.py` in that directory, exit 0, `ALL_OK`. Script `check.py` SHA-256: `82300fb7e6875af80e669002e8119dd4e26948e4f672b421f583ff4c4b9b3b6f`. The implementation seat independently reran the exact pinned script.

The exhaustive clique search checks both discriminant classes of diagonal forms, for $(d,p)=(3,3),(4,3),(5,5),(2,3),(2,5),(3,5),(2,7),(3,7)$. It enumerates nonzero vector representatives modulo sign with all admissible $(a,b)$, and checks every Gerzon-sized clique it finds. Every system found satisfies the identity. These eight pairs are the entire tested scope; the universal conclusion rests on the Lean proof.

## Triage

### What the settlement shows

1. **Kernel-checked — decisive mechanism.** The consumed private theorems `independent_nonzero_trace` and `span_zero_trace` give the basis and trace-zero-span alternatives, and `scalar_frame_nonzero_trace` gives the scalar frame operator in the nonzero case. `moment_nonzero_trace` and `moment_zero_trace` give the two fourth-moment formulas; `fourthMoment_coefficient` forces $A=2\beta$. `diagonal_identity`, `parameter_identity` and public `result` give $a^2=(d+2)b$ without assuming $d\ne0$ or $d-1\ne0$ in the field. These are statements and steps of the existing proof, not additional public identities.

2. **Kernel-checked — zero scalar-frame branch.** Inside `diagonal_identity`, $a=0$ gives $\sum_iP_i=0$, the trace-zero span, $N=1$ in $F$ and $d\ne0$. The local coefficient equation is $-b=2b/d$, with $b\ne0$ and $d\ne0$. **Proved in prose — characterization from those equations:** multiplication by $d$ and cancellation of $b$ give $d=-2$ in $F$. Conversely, the nonzero-$a$ branch yields $c\ne0$ in `scalar_frame_nonzero_trace`. Thus, among the systems under consideration, $c=0$ occurs exactly in the $a=0$, $d=-2$ branch. The span and coefficient equations are kernel-checked inside the consumed helpers and `diagonal_identity`; this displayed iff is their algebraic consequence, not a separate Lean theorem.

3. **Computed — zero-branch examples.** The pinned experiment finds one system modulo sign with $(a,b)=(0,1)$ at $(d,p)=(4,3)$ in the nonsquare-discriminant form, and two with $(a,b)=(0,4)$ and two with $(a,b)=(0,1)$ at $(3,5)$ in the two forms. Both dimensions satisfy $d=-2$ in the field. The command, script identity and full tested scope are in Evidence.

4. **Literature reading — explicit frame.** Jorquera–King, arXiv:2505.12175, Example 6.8, displays a $4\times10$ $(0,1,0)$-ETF over $\mathbf F_3$ with Gram form $\operatorname{diag}(1,1,1,2)$. This is a published example, not a construction formalized in this module.

5. **Proved in prose — SRG consequence through the source's Theorem 4.6.** The four Table 4 rows give the following ETF parameters, with $b=1$:

   | SRG in Table 4 | $p$ | $d$ | $a$ | $a^2$ versus $d+2$ in $\mathbf F_p$ |
   | --- | --- | --- | --- | --- |
   | $(351,210,113,144)$ | 5 | 26 | 0 | $0\ne3$ |
   | $(703,520,372,420)$ | 3 | 37 | 2 | $1\ne0$ |
   | $(1081,486,177,252)$ | 5 | 46 | 2 | $4\ne3$ |
   | $(1275,728,379,464)$ | 7 | 50 | 0 | $0\ne3$ |

   For the first and last rows, Theorem 4.6 initially gives only an upper bound on $d$; a strict decrease would violate Proposition 2.9 because $N=\binom{d+1}{2}$ at the displayed dimension. Hence equality of dimensions is forced, as Example 5.8 explains. In every row $a^2\ne b$, so Theorem 4.6's graph-to-frame implication followed by `result` contradicts the displayed residues. Taking graph complements gives the parameter sets $(351,140,73,44)$, $(703,182,81,35)$, $(1081,486,177,252)$ and $(1275,546,281,198)$ as well. This graph-to-frame transport and nonexistence deduction are argued here and not formalized. The supplied reading of [Brouwer's table](https://aeb.win.tue.nl/graphs/srg/) marks all four “?”. No prior nonexistence proof was found in the supplied search; priority is limited to that scope. These graph statements are candidates for a separate lane.

6. **Open — infinite occurrence of the isotropic case.** Existence of $a=0$ systems for infinitely many $(d,p)$ is not settled. The parameter identity supplies a necessary condition, not an existence theorem.

7. **Proved scope and surviving source results.** `result` removes the two congruence restrictions for $d\ge2$; the source's Propositions 2.9–2.10 remain applicable. The source's Table 4 constructions are obstructed by the parameter identity through its Theorem 4.6 as explained above. No general classification or construction of Gerzon-equality systems follows. The $d=1$ boundary remains as stated in Falsifier.

## ASSUMED-UNVERIFIED

Wei–Luo's contents, literature completeness and priority remain `ASSUMED-UNVERIFIED`. The source and literature checks in #16342 are attributed to the orchestrator and the supplied search/proof seats; the implementation seat's independent measurements cover the Lean delivery and the pinned experiment. The SRG implication is a prose argument using the source, not a kernel-checked graph theorem. No validated four-slot escape registration is claimed; the missing evidence is tracked in #16531.
