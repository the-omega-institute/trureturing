---
slug: gledhill-hanany-2023-coulomb-branch-poisson-bracket-refutation
bibkey: gledhillhanany2023poissoncoulomb
doi: 10.1007/JHEP03(2023)154
url: https://arxiv.org/abs/2210.02966v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.result
---

# Jacobi and reducedness obstruct the second E6 and truck Poisson bracket conjectures

## Problem

Kirsty Gledhill and Amihay Hanany, *Poisson brackets for some Coulomb branches*, JHEP 03 (2023) 154, arXiv:2210.02966v2, conjecture bracket tables for the second E6 family and the truck family. The v2 TeX source `main.tex` has md5 `e6664eac5bf9635a3684d84de4e80a97`.

For the $E_{6,n}^{II}$ family, `main.tex`, lines 1845–1856, display labelled `final e62 pbs`:

> We conjecture that the non-zero Poisson brackets of (\ref{gens of e6 II fam}) are given by:

The spinor entries of that display, lines 1851–1853, are:

> $\{C_1,s^{\alpha}\}=+ \, s^{\alpha}$
>
> $\{C_1,s_\alpha\}=- \, s_\alpha$
>
> $\{s^{\alpha},s_\beta\} = {C_1}^{n-1} \, {\delta^{\alpha}}_{\beta}$

The sentence following the display is:

> where $C_1$ is normalised such that there are no additional numerical coefficients in (\ref{final e62 pbs}). All other Poisson brackets between (\ref{gens of e6 II fam}) that are not listed in (\ref{final e62 pbs}) vanish.

For the truck family, `main.tex`, lines 2185–2197, display labelled `final truck pbs`:

> We conjecture that the non-zero Poisson brackets of (\ref{gens of truck fam}) are given by:

The two weight brackets are the same, and the mixed entry, lines 2193–2194, is:

> $\{ s^{\alpha}, s_{\beta} \} = {C_1}^{n+\sigma-1} \, {\delta^{\alpha}}_{\beta}$

The following sentence specifies:

> All other Poisson brackets between (\ref{gens of truck fam}) that are not listed in (\ref{final truck pbs}) vanish.

The second E6 table concerns $n\ge3$ (line 1807); the truck quiver has $n\ge2$ and hypermultiplet multiplicity $\sigma$ (line 2149). The spinor indices have $N=2^{2n}$ values (lines 1843 and 2185). Appendix A, line 2237, states:

> A Poisson bracket $\{ \cdot , \cdot \}$ is simply a bilinear map which obeys anticommutativity, Leibniz and the Jacobi identity.

The source context is collected in [the literature note](../Library/QuantumContext/gledhillhanany2023poissoncoulomb.md).

Issue [#21464](https://github.com/the-omega-institute/trureturing/issues/21464) fixes the proposition `claim` as $\mathrm{ConjE6}\lor\mathrm{ConjTruck}$. Here `ConjE6` requires, for every natural $n\ge3$, a reduced commutative complex algebra $R$, a Poisson bracket, a nonzero element $h$, and two spinor families indexed by $\mathrm{Fin}(2^{2n})$ satisfying the displayed spinor rules with exponent $e=n-1$. `ConjTruck` requires the same for every natural $n\ge2$ and every natural $\sigma\ge1$, with $e=n+\sigma-1$. The algebra and bracket may depend on these parameters. This disjunction of universal family assertions is refuted.

## Motivation

The paper seeks Poisson algebra presentations of Coulomb branch chiral rings, including magnetic quivers describing Higgs branches of five-dimensional theories at infinite coupling. A highest weight generating function constrains the representation content and degrees of operators; a proposed bracket must also satisfy Jacobi. The two tables make a particularly restrictive choice: every mixed spinor bracket is a power of the same $U(1)$ invariant times the identity tensor, while all equal-charge spinor brackets vanish. Their compatibility is necessary for the tables to describe the claimed Poisson algebras.

## Gap

The literature check before any Lean is recorded in #21464:

- The source reading retains both conjectures in arXiv v2; the search report also records that the JHEP version retains the second E6 conjecture.
- The quick-track search report records seven INSPIRE citing full texts searched without finding a correction or settlement, and searches of MathDB and `google-deepmind/formal-conjectures`.
- The orchestrator records three citing works in OpenAlex record `W4353085763`, and repository searches for `2210.02966`, `Gledhill` and `Hanany` with no existing issue, module, Library note or Problems dossier on the source.

`not-found-in-searched-scope`.

## Route

Write $\{a,b\}$ for `br a b`. `IsPoissonBracket` means complex bilinearity, antisymmetry, the right Leibniz rule and cyclic Jacobi; antisymmetry supplies the left Leibniz rule. `SpinorBrackets` consists of the two weight rules, the mixed rule $\{s^\alpha,s_\beta\}=h^e\delta^\alpha_\beta$, and vanishing brackets between two upper or two lower components.

1. **The local obstruction (`bracket_forces_zero`, private).** Let $R$ be a reduced commutative complex algebra, let `IsPoissonBracket br` hold, let $e\in\mathbb N$ satisfy $1\le e$, and let $h,x,y,z,w\in R$ satisfy
   $\{h,x\}=x$, $\{h,y\}=-y$, $\{x,y\}=h^e$, $\{z,w\}=h^e$, $\{x,w\}=0$ and $\{x,z\}=0$.
   These are all the lemma's hypotheses; its conclusion is $h=0$. Under these hypotheses, `hamiltonian` makes $b\mapsto\{a,b\}$ a complex derivation, and `bracket_mul_left` supplies $\{ab,c\}=a\{b,c\}+\{a,c\}b$. Put $e=k+1$. Jacobi on $(x,z,w)$ gives $0=-(k+1)h^kx$, so cancellation of the nonzero complex scalar $k+1$ gives $h^kx=0$. Expanding $\{h^kx,y\}=0$ and multiplying by $h$ gives $h^{2(k+1)}=0$: for $k=0$ the correction term has coefficient zero; for $k\ge1$ it is $k(h^kx)y=0$. Reducedness gives $h=0$.
2. **Two components (`spinor_forces_zero`, private).** Let $R$ be a reduced commutative complex algebra, $N\in\mathbb N$ with $2\le N$, `IsPoissonBracket br`, $h\in R$, $sUp,sDn:\mathrm{Fin}\,N\to R$, and $e\in\mathbb N$ with $1\le e$. Assume `SpinorBrackets br h sUp sDn e`. For the distinct indices $i=0$ and $j=1$, put $x=sUp(i)$, $y=sDn(i)$, $z=sUp(j)$ and $w=sDn(j)$. The two weights, two diagonal mixed brackets, off-diagonal mixed vanishing and upper-upper vanishing supply exactly the six equations in item 1, yielding $h=0$.
3. **The universal assertions (`not_conjE6` and `not_conjTruck`, private).** `ConjE6` supplies all the hypotheses of item 2 and $h\ne0$ at $n=3$, with $N=64$ and $e=2$. `ConjTruck` supplies them at $n=2$, $\sigma=1$, with $N=16$ and $e=2$. Each contradicts $h=0$. The theorem `result` rules out either side of `claim`.

## Falsifier

The source-to-formal bridge uses the coordinate ring of an affine complex variety as a reduced commutative complex algebra, and reads the displayed generating representation $C_1$ as a nonzero function. The source identifies the branches as algebraic varieties in Appendix A, line 2231, and lists $C_1$ among the generators in lines 1823 and 2165. Nonzero charged generators also force $C_1\ne0$ through the weight relation and bilinearity.

The formal definitions impose only necessary spinor conditions. They do not require finite generation of $R$, algebraic independence or nonvanishing of individual spinor components, an adjoint action, or a construction identifying $R$ with a Coulomb branch. The omitted adjoint generators cannot repair a contradiction involving only the retained elements. The unlisted-bracket vanishing sentence is essential: it supplies the upper-upper vanishing used in item 2. The formal truck range is the preregistered positive natural multiplicity range. The coordinate-ring interpretation, generator nonvanishing and physical parameter correspondence are not formalized in this module.

## Evidence

The canonical source is `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.lean` (165 lines).

- **Proof.** It proves `result : ¬ claim`, with `claim : Prop` defined as `ConjE6 ∨ ConjTruck`.
- **Reuse.** The proof uses mathlib's `Derivation.leibniz_pow`, complex scalar cancellation and the fact that a nilpotent element of a reduced ring is zero.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.lean.json`, statement `sha256:a8f207af54fdaab38ba03af6bb3f82a392cb42b74db20f5aaae2f08e8fa49a3d`.

Declaration statements:

- `result`: `sha256:00b655992c009f5604638c55060cae4f50eb994de823b08c7528827074c2e787`;
- `claim`: `sha256:0e504e9587e10964fb00cb4cdda155445b1d1ac3ba37870393d2b5a89db752a3`.

## Triage

Tier 1 explicitly stated conjectures of a 2023 journal paper, preregistered in issue #21464 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none: derivation power rules, scalar cancellation, ring identities and reducedness instantiate existing algebraic results | open-problem-resolution |
| `IsPoissonBracket`, `SpinorBrackets`, `ConjE6`, `ConjTruck`, `claim` | bind-only | none | definitions used by `claim` |
| the Hamiltonian, Leibniz, obstruction and family-refutation helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** neither universal family-existence assertion `ConjE6` (every natural $n\ge3$) nor `ConjTruck` (every natural $n\ge2$ and natural $\sigma\ge1$) is true, where existence means a reduced commutative complex algebra with a complex Poisson bracket, $h\ne0$, and the respective `SpinorBrackets` relations defined above. This is precisely $\neg(\mathrm{ConjE6}\lor\mathrm{ConjTruck})$.

**Computed, not formalized** (the orchestrator's hand computation):

- For the canonical bracket $\{f,g\}=\partial_pf\,\partial_qg-\partial_qf\,\partial_pg$ on $\mathbb C[p,q]$, substitution of $h=-pq$, $x=p$ and $y=p^2q^3/3$ gives $\{h,x\}=x$, $\{h,y\}=-y$ and $\{x,y\}=h^2$, with both self-brackets zero.

**Argued, not formalized**

- *Mechanism and repair.* For a reduced commutative complex algebra with `IsPoissonBracket br`, $N\ge2$, $e\ge1$ and `SpinorBrackets br h sUp sDn e`, `spinor_forces_zero` gives the obstruction described in Route. The Hamiltonian derivative of the shared diagonal entry $h^e$ along the selected upper component is $-e h^{e-1}x$. The second component supplies a Jacobi triple whose other two terms vanish, forcing this derivative to be zero; Leibniz and reducedness then force $h=0$. Keeping reducedness, nonzero $h$ and the two weight rules therefore requires changing at least one of the mixed-bracket or equal-charge vanishing prescriptions. Adding only adjoint-generator relations cannot change that Jacobi triple. A correct replacement table, including whether additional representation components are needed, remains open.
- *Nearby surviving relations.* With only one upper and one lower component, the canonical polynomial example in the computed group is a reduced complex Poisson algebra with nonzero $h$ and exponent two satisfying all the one-component spinor relations: the polynomial ring is a domain and $h$ is a nonzero monomial; differentiation gives bilinearity, Leibniz and the listed relations, while commuting second derivatives cancel in pairs in the Jacobi expansion. Thus the two-component hypothesis cannot simply be dropped. If the condition $h\ne0$ is dropped instead, $R=\mathbb C$ with zero bracket, $h=0$ and all spinor components zero satisfies the relations for every $N$ and $e\ge1$; every right-hand side and every bracket is zero. This degenerate solution does not realize the source's nonzero generating representations.
- *Effect on the source's simplification.* At `main.tex`, line 1402, the paper motivates its conjectures by selecting the simplest representation among allowed bracket outputs. These two bracket tables show that representation content and conformal degree alone do not guarantee Jacobi compatibility. Any Poisson presentation or further calculation using these two tables requires corrected bracket data. The omission of already-covered quivers at line 1876 also needs that qualification whenever it relies on the second E6 table.
- *Effect on physical conclusions and neighbouring questions.* The paragraph “The breaking of conformality” (lines 1404–1405) uses Casimir factors in the conjectured brackets to infer a scale preserving flavour symmetry. For these two families, the refuted tables cannot establish that inference; the physical conclusion itself is not decided by `result`. The module does not refute the existence of the Coulomb branches, verify or refute their highest weight generating functions, or settle the trapezium, pyramid, kite, first E6, E7 or E8 bracket conjectures. The source treats the second E6 family's $n=1,2$ symmetry-enhanced cases separately at line 1807; those presentations are outside `ConjE6`.

## ASSUMED-UNVERIFIED

The bounded literature check establishes only `not-found-in-searched-scope`, not exhaustive novelty or priority. The arXiv v2 TeX passages quoted above are directly checked; the preregistration's readings of arXiv v1, the JHEP text, the seven INSPIRE citing full texts, MathDB and `google-deepmind/formal-conjectures`, its OpenAlex citation count, Crossref metadata lookup and its repository-wide absence check are not independently reproduced here. Different citation services' counts are not a census of all relevant literature.

The coordinate-ring and nonzero-generator bridge, the physical interpretation of the registered parameter ranges, the hand computation and all arguments in “Argued, not formalized” are not formalized by `result`. The single-component example is a polynomial Poisson algebra, not a construction of a source Coulomb branch. Corrected tables, extensions to other conjectures, and the physical claims about conformal symmetry remain open here. No construction or classification of the actual Coulomb branch coordinate rings is supplied by this settlement.
