---
slug: gross-goedicke-2025-kite-shaped-quadratic-forms
bibkey: grossgoedicke2025artisanal
doi: 10.48550/arXiv.2504.15401
url: https://arxiv.org/abs/2504.15401v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.result
---

# The binary kite construction works exactly when $n$ is not one modulo three

## Problem

D. Gross and P. Goedicke, *Thirty-six officers, artisanally entangled* (2025), arXiv:2504.15401v2, subsection “Construction of doubly perfect functions”, Remarks after Theorem 5 (`artisanal.tex`, line 2316):

> As a concrete example, computer experiments indicate that the matrices with ``kite-shaped support'', $A_{ij}=B_{ij}=1$ iff $i+j\leq n+1$, give a solution for all $n$ not congruent to $1$ modulo $3$.

The quotation is from the downloaded v2 TeX source `artisanal.tex`, MD5 `29b677f0287fbbb335cd79eb4f5f33d2`. Its surrounding paragraph (lines 2304–2316) takes $A,B$ to be nonsingular symmetric binary matrices with $AB-I$ also nonsingular, and uses $N=\operatorname{diag}(A,B)$ as the coefficient matrix of a quadratic exponential. See [the literature note](../Library/QuadraticForms/grossgoedicke2025artisanal.md).

For $n\in\mathbb N$, let $K_n\in M_n(\mathbb F_2)$ have entry $1$ exactly when $i+j\le n+1$, with indices $1,\ldots,n$, and entry $0$ otherwise; at $n=0$ this is the empty matrix. Put $N_n=\operatorname{diag}(K_n,K_n)$ and $J_n=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$.

Issue [#20969](https://github.com/the-omega-institute/trureturing/issues/20969) fixes the following reading, including the converse to the source's observation: for every $n\ge1$,

- $K_n$ is symmetric and has trivial right kernel;
- $N_n$ has trivial right kernel;
- $K_n^2-I_n$ has trivial right kernel if and only if $n\not\equiv1\pmod3$;
- $N_n+J_n$ has trivial right kernel if and only if $n\not\equiv1\pmod3$.

This matrix statement is proved.

## Motivation

For every symmetric integer coefficient matrix $N$ on the phase space $\mathbb Z_d^{2n}$, Gross and Goedicke (2025, arXiv:2504.15401v2, `artisanal.tex`, lines 2226–2230) characterize the quadratic exponential $\lambda(a)=\tau_d^{a^{\mathsf T}Na}$ as doubly perfect exactly when the reductions of $N$ and $N+J$ over $\mathbb Z_d$ have trivial kernel. Their Theorem 2 turns doubly perfect functions into complex Hadamard matrices proportional to two-unitaries (statement at lines 505–526; proof at lines 2144–2202). The kite matrices give an explicit binary input to this construction. The formal settlement supplies the matrix criterion; these function and quantum-information consequences use the source's external results.

## Gap

The bounded literature check recorded in #20969 reports:

- The v2 TeX retains the numerical observation. The search report also records it in v1; v1 was not independently reread for this dossier.
- The quick-track search report records zero citing works in OpenAlex record W4414630634. Broader OpenAlex title queries returned HTTP 429, and MathDB returned HTTP 403, so those searches are incomplete.
- The same report found no entry for this family in `google-deepmind/formal-conjectures`; its `OpenQuantumProblems/35.lean` concerns the distinct general AME-existence problem.
- The orchestrator's web search on 24 October 2026 for the kite-shaped two-unitary family returned only the source, and its repository search found no prior issue, module or problem dossier on the family.

`not-found-in-searched-scope`.

## Route

All matrices below are over $\mathbb F_2$. Unqualified lemma names refer to the settlement module; its helper lemmas are private.

1. **Symmetry and inverse.** For every $n\in\mathbb N$, `kite_symmetric` proves symmetry. With zero-based indices $i,j\in\{0,\ldots,n-1\}$, define $H_n$ by adding the indicators of $i+j+1=n$ and $i+j=n$. For every $n\in\mathbb N$, `kite_inverse` proves $K_nH_n=I_n$, and `kite_det` proves $\det K_n=1$.
2. **Tridiagonal reduction.** For every $n\in\mathbb N$, `inverse_square` proves $T_n=I_n+H_n^2$, where $T_n$ is `tridiagonal n`. For $n\ge1$, its diagonal is $(0,1,\ldots,1)$, its adjacent off-diagonal entries are $1$, and all remaining entries are $0$. The inverse identity gives $K_n^2T_n=K_n^2+I_n$. For every $n\in\mathbb N$, `square_det` concludes $\det(K_n^2-I_n)=\det T_n$, using $\det K_n=1$ and characteristic two.
3. **Determinant recurrence.** For every $m\in\mathbb N$, `tridiagonal_recurrence` proves $d_{m+2}=d_{m+1}+d_m$, where $d_n=\det T_n$. The reversed $(m+2)\times(m+2)$ matrix has its first-row and first-column entries zero outside positions $0,1$. These are precisely the two vanishing hypotheses needed to apply `ForbiddenNeighbourDeterminant.det_sparse_front` over $\mathbb F_2$. The two minors are the reversed matrices of sizes $m+1$ and $m$. With $d_0=1$ and $d_1=0$, two-step induction gives `tridiagonal_det_zero`: for every $n\in\mathbb N$, $\det T_n=0$ if and only if $n\equiv1\pmod3$.
4. **Block assembly.** For every $n\in\mathbb N$, `quadratic_det` proves $\det N_n=1$. Over $\mathbb F_2$, $N_n+J_n=\begin{pmatrix}K_n&I_n\\I_n&K_n\end{pmatrix}$. Using the invertibility of $K_n$ supplied by `kite_inverse`, `symplectic_det` proves, for every $n\in\mathbb N$, $\det(N_n+J_n)=\det(K_n^2-I_n)$. For finite square matrices over $\mathbb F_2$, `Matrix.separatingRight_iff_det_ne_zero` identifies right-separation with nonzero determinant. `result` combines these identities and the residue criterion under the stated hypothesis $1\le n$.

## Falsifier

The proof would not answer the source's observation if the support, field, block construction or kernel predicate differed. The correspondence is:

- `kite n i j` uses the condition $i.\mathrm{val}+j.\mathrm{val}+2\le n+1$ on `Fin n`. Adding one to each index gives exactly the source's support.
- `quadraticForm n` is the block matrix with two copies of `kite n` on the diagonal and zero off-diagonal blocks; `Fin n ⊕ Fin n` indexes its $2n$ coordinates.
- `Matrix.SeparatingRight` means that a vector annihilated against every left test vector is zero. For these finite matrices this is equivalent to $Mw=0\Rightarrow w=0$, by `Matrix.separatingRight_iff_forall_mulVec_eq_zero`.
- Mathlib's `Matrix.J` has blocks $0,-I,I,0$, while the source's symplectic matrix has blocks $0,I,-I,0$ (`artisanal.tex`, lines 349–358). They coincide over $\mathbb F_2$.

The formal claim fixes the binary field and positive $n$. It contains no predicate asserting double perfection of a complex-valued function or two-unitarity of a complex matrix.

## Evidence

The canonical source is `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.lean` (160 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.lean.json`, statement `sha256:acc19a170ebdfb23539dc133ac68fd8a027a6087f0c762ecc2ace223c71cc75e`.

Declaration statements:

- `result`: `sha256:bff76359b305197dc6d6066993fd5d0e0c378006280e9cb171cdb8be92d6e345`;
- `claim`: `sha256:2fb4d74ba855df50a265d084d4d3e761a776bc7d4e8c7a3026ae39438086d12f`.

## Triage

Tier 1 numerical observation of a 2025 paper, preregistered in issue #20969 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural number $n\ge1$, $K_n$ is symmetric, $K_n$ and $N_n$ have trivial right kernel, and each of $K_n^2-I_n$ and $N_n+J_n$ has trivial right kernel if and only if $n\not\equiv1\pmod3$.

**Argued, not formalized.**

- *Mechanism and defect.* The dense support is controlled by a sparse inverse: `kite_inverse` and `inverse_square`, both valid for every natural $n$, give $K_nH_n=I_n$ and $T_n=I_n+H_n^2$. Hence $K_n^2T_n=K_n^2+I_n$, so multiplication by the invertible $K_n^2$ identifies $\ker T_n$ with $\ker(K_n^2-I_n)$. For $n\ge2$, the equations $T_nx=0$ start with $x_1=0$; the interior rows give $x_{i+1}=x_i+x_{i-1}$ for $1\le i\le n-2$; the last row gives $x_{n-2}+x_{n-1}=0$. Writing $x_0=t$, the sequence is $(t,0,t,t,0,t,\ldots)$. The last equation is automatic when $n\equiv1\pmod3$ and forces $t=0$ in the other two residues. At $n=1$, $T_1$ is zero, giving the same one-dimensional defect. Finally, the block equations for $N_n+J_n$ give $y=K_nx$ and $(I_n+K_n^2)x=0$. Thus both exceptional kernels have dimension exactly one. The nullity assertion and these explicit kernel descriptions are not statements of `result`.
- *Extension of scalars.* For every field $F$ of characteristic two and every $n\ge1$, the canonical embedding $\mathbb F_2\to F$ preserves the $0,1$ entries and determinants. The identities in `kite_det`, `quadratic_det`, `square_det`, `symplectic_det` and `tridiagonal_det_zero` (each valid for every natural $n$ over $\mathbb F_2$) therefore give the same nonsingularity classification over $F$, since a finite square matrix over a field is nonsingular exactly when its determinant is nonzero. This extension is not formalized in the module; it makes no assertion in odd characteristic.
- *Link to the source's functions.* Lift $N_n$ to the symmetric integer matrix with entries $0,1$, and put $\lambda_n(a)=i^{a^{\mathsf T}N_na}$ for binary representatives $a$. For binary $a,b$, expanding the quadratic exponent gives $\lambda_n(a+b)\overline{\lambda_n(b)}=i^{a^{\mathsf T}N_na}(-1)^{a^{\mathsf T}N_nb}$; reducing $a+b$ modulo two changes the exponent by a multiple of four. Twisting adds $(-1)^{a^{\mathsf T}J_nb}$. A nonzero binary linear character sums to zero: pair each $b$ with $b+e_j$ for a coordinate with coefficient $1$. The zero character sums to $2^{2n}$. Consequently both autocorrelations have the required delta form exactly when $N_n$ and $N_n+J_n$ have trivial left kernel, equivalently trivial right kernel for these finite square matrices. Since $\lambda_n$ is unimodular, this recovers the source's quadratic-phase criterion (`artisanal.tex`, lines 1012–1032 and 2226–2230) and explains the double-perfection interpretation of the matrix settlement. This character-sum bridge is not formalized here.
- *Effect on the paper and neighbouring questions.* The kite example in the remarks now has an exact matrix classification, including its excluded sizes. The source's Theorem 5 already supplies a separate trace-orthonormal-basis construction for every $n>1$ (`artisanal.tex`, lines 2254–2296), including $n=4,7,\ldots$; failure of the kite choice at those sizes is no obstruction to that broader existence result. Applying the source's Theorem 2 to the successful kite choices supplies explicit Hadamard two-unitaries through the external function criterion. The tensor-product existence discussion already uses the all-size construction, so the kite classification does not enlarge the orders covered there. The further construction problem for orders $d=2d_1$ with $d_1$ divisible by neither $2$ nor $3$ (lines 2325–2332) is not settled here.

## ASSUMED-UNVERIFIED

The literature check is bounded by the sources and searches recorded in #20969 and does not establish exhaustive worldwide novelty or priority. The v2 TeX and its quoted passage were checked directly; the v1 reading, OpenAlex citation count, formal-conjectures comparison, web searches and prior-repository search are attributed reports from the preregistration and were not independently reproduced for this dossier. The broader OpenAlex and MathDB checks remain incomplete because of the reported HTTP 429 and 403 responses.

The general kernel-dimension argument, extension to other fields of characteristic two, character-sum interpretation, and applications of the source's function-to-Hadamard theorem are not formalized in this module. No formal conclusion about other coefficient characteristics, other symmetric block choices or the source's remaining order-existence problem is claimed.
