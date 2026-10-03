---
slug: ahn-corcoran-staudacher-2021-hypereclectic-non-shortening
bibkey: ahn2022eclectic
doi: 10.1007/JHEP03(2022)028
url: https://arxiv.org/abs/2112.04506v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result
---

# Non-shortening in the one-wall hypereclectic spin chain

## Problem

C. Ahn, L. Corcoran and M. Staudacher, *Combinatorial Solution of the Eclectic Spin Chain*,
arXiv:2112.04506v1, JHEP 03 (2022) 028, Appendix A, Eq. (A.4):

> “We claim that the rank of A^(k) is always maximal:”
>
> “rank(A^(k)) = min(d_{S−k}, d_S).”

Here $A^{(k)}$ is the matrix of $H^k:W_S^{L,M}\to W_{S-k}^{L,M}$ in the elementary bases,
and $d_S=\dim W_S^{L,M}$. The settled statement is the rational encoding of the $K=1$
static sector, for every $1\le M\le L$, every natural level $S$ and every $k\le S$.
The rightmost letter is the fixed wall $3$; the other $L-1$ letters consist of $L-M$ ones
and $M-1$ twos.

## Motivation

Section 3.2, Eqs. (3.14)–(3.19), grades elementary states by
$S=\sum_{j=1}^{M-1}j n_j$, the number of pairs in which a $2$ precedes a $1$.
The Hamiltonian replaces each adjacent $21$ by $12$ with coefficient one and decreases
this level by one. Maximal rank excludes unexpected shortening of its chains between
levels. The frozen declaration
`D5/S3/Quantum/SpinChains/HypereclecticNonShortening.result` proves this rank equality.

## Gap

Issue #12310 preregisters the full quantified rational statement and classifies it as Tier 1.
C. Ahn and M. Staudacher, *Spectrum of the Hypereclectic Spin Chain and Pólya Counting*,
arXiv:2207.02885v1, doi:10.1016/j.physletb.2022.137533, introduction, states:

> “They rest on a compelling and extensively checked but unfortunately still unproven non-shortening conjecture.”

The issue records a ChatGPT-Pro search of citing works and an orchestrator check of the
source quotations, MathDB and the repository. Those literature readings are reported by
their named producers; they establish `not-found-in-searched-scope`, not exhaustive
worldwide novelty. The implementation independently checks the available arXiv versions,
DOI locators and repository collisions. No prior proof is asserted from these searches.

## Route

1. Represent an elementary state by a Boolean word of length $N=L-1$, with `true` meaning
   $2$. Reuse the frozen binary count `OddTopWeight.ones`; define its inversion level,
   the fixed-count sector and the span of delta basis states at each level over $\mathbb Q$.
2. On rational coordinate functions, sum the adjacent $21\to12$ moves to obtain $H$.
   Define reverse moves with coefficient $(p+1)(N-p-1)$ at zero-based bond $p$, and use
   pointwise multiplication by the weight $G(w)=2S-b(N-b)$, where $b=M-1$.
   The local facts in `result` verify $[R,H]=G$, $[G,H]=-2H$, $[G,R]=2R$ for $N\ge2$.
   The positional cancellation directly uses `Finset.sum_range_sub'`.
3. Finite dimensionality terminates the raising orbit of a weight vector. Induction on
   its remaining raising length proves the sharp lowering-kernel lemma; the terminal
   case directly applies Mathlib's primitive-vector chain nonvanishing theorem.
4. If $b(N-b)+k\le2S$, this lemma makes the restricted $H^k$ injective.
   In the complementary case its contragredient makes the restricted map surjective.
   The range dimension is therefore the smaller level dimension. Empty and one-site
   bins are handled directly.

## Falsifier

The statement includes every allowed $L,M,S,k$, with no dimension, nilpotence or maximal-rank
assumption. A rational static-sector map whose range dimension differs from the smaller
level dimension would contradict `result`. The independent elementary-state generators
and adjacent-move operator are specified before the rank proposition; maximal rank is
not built into their definitions.

## Evidence

The source is `D5/S3/Quantum/SpinChains/HypereclecticNonShortening.lean`; its public declarations
are `level`, `sector`, `W`, `H`, `restrict`, `claim` and `result`. The only retained private
theorems are the inversion-weight identity and the sharp lowering-kernel induction.
The direct repository import is `D5.S1.Words.ParityCode.OddTopWeight`; the Lie API is
`Mathlib.Algebra.Lie.Sl2`. The canonical Scribe mirror displays all seven public declarations.
The proof uses the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
There is no `sorry`, new axiom or finite enumeration certificate.

## Triage

Tier 1; resolution `Proved` for the preregistered $K=1$ rank claim (A.4) over $\mathbb Q$.
`proof_shape: content`; `admission_basis: open-problem-resolution` (issue #12310);
`utility: none`. Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** the unrestricted family of rational static-sector maps has
  maximal rank between every pair of levels joined by $H^k$.
- **Proved in the private inversion-weight theorem and local facts of `result`:** the
  inversion grading is the diagonal weight $2S-b(N-b)$, and the quadratic reverse moves
  complete the adjacent-move Hamiltonian to an $\mathfrak{sl}_2$ triple for $N\ge2$.
- **Proved in `lowering_kernel_zero_aux` and used in `result`:** sharp upper-weight
  injectivity follows by induction on the raising length; the dual provides the
  complementary surjectivity. This mechanism requires no assumed irreducible decomposition.
- **Open as further formalization:** identify the fixed-count sector with
  $\Lambda^b$ of the $N$-dimensional irreducible representation, derive its irreducible
  decomposition, and certify that Jordan block sizes equal irreducible summand dimensions
  and that the generating function is its character. These are the representation-theoretic
  interpretation of the route, not additional conclusions of `result`.
  The candidate correspondence sends a word to the ordered wedge of its occupied sites.
  A single-particle adjacent move either meets an occupied site and vanishes, or moves
  without crossing another occupied site; the wedge coefficient then has positive sign.
  This explains the expected operator correspondence. Its linear equivalence and
  intertwining identities remain open formal obligations. In an irreducible summand,
  a lowering string has the summand's full dimension, which would identify its Jordan
  block and character contribution; the decomposition and character identities are
  also open formal obligations.
- **Open:** tensor the triples over bins and prove the multi-wall assertions; then prove
  the compatibility of that construction with cyclic projection and the cyclic
  generating-function statements of arXiv:2207.02885. Tensor products alone do not
  certify the required cyclic restriction. On an actual tensor product of fixed bins,
  operators on different factors commute, so sums of the three factor operators are
  the candidate total triple. Connecting that tensor product to the source's complete
  multi-wall space remains open. A cyclic projection must preserve all three operators,
  not only the Hamiltonian, before this argument applies on the projected sector;
  the required equivariance and the cyclic counting formulas remain open.
- **Proved scope and source consequence:** the rank premise used for the one-wall
  non-shortening argument is discharged in the rational elementary-state model.
  **Open:** formal certification of the paper's remaining Jordan and generating-function
  formulas and scalar extension of the rank statement to arbitrary characteristic-zero
  fields. The separate eclectic-universality conjecture is also open here.

## ASSUMED-UNVERIFIED

The literature checks reported in issue #12310 are not an exhaustive proof of absence of
prior work. The journal versions have not been independently compared with the cited
arXiv v1 texts. No exterior-power equivalence, scalar-extension theorem, multi-wall or
cyclic settlement is claimed by this module.
