---
slug: han-liu-2023-twirling-phase-retrievability
bibkey: hanliu2023twirling
doi: 10.1016/S0034-4877(24)00012-0
url: https://arxiv.org/abs/2311.16349v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.result
---

# Han–Liu's twirling phase-retrievability conjecture

## Problem

D. Han and K. Liu, *Zero-Error Correctibility and Phase Retrievability for
Twirling Channels*, arXiv:2311.16349v1 (27 November 2023), published in
*Reports on Mathematical Physics* 93(1) (2024), 87–102, DOI
10.1016/S0034-4877(24)00012-0, state the final conjecture of Section 5:

> Let $\pi = m_1\pi_1\oplus\dots\oplus m_d\pi_d$ be a unitary representation
> of $G$ such that $\pi_i$ and $\pi_j$ are inequivalent irreducible
> representations for all $i\ne j$ and $\mathcal I_k\le d<\mathcal I_{k+1}$.
> Then $pr(\Phi_\pi)=\max\{\beta(\Phi_\pi),k\}$.

Issue [#15229](https://github.com/the-omega-institute/trureturing/issues/15229)
preregistered the source, the finite-group specialization, the route, the
readings and the settlement criteria. The frozen Lean declaration
D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.result
refutes the universal statement.

## Motivation

The source defines the twirling channel
$\Phi_{\pi,\sigma}(T)=\int_G\pi(g)T\sigma(g^{-1})\,d\mu(g)$,
phase retrievability by pure-state injectivity, the phase-retrievability index
$pr$, the frame length $\mathcal I_n$, and the code dimension $\beta$. Its
Theorem 3.4 gives $\beta(\Phi_\pi)=\max_i m_i$. The finite-group Lean
conventions use the normalized sum, Matrix.vecMulVec x (star x), natural
suprema and infima, and the block representation
$\bigoplus_i I_{m_i}\otimes\rho_i$.

For $G=C_3$ with the three characters each of multiplicity $2$, the
conjecture has $d=3$, $k=1$, and predicts $pr\le2$ because $\beta=2$.
The counterexample supplies a phase-retrievable subspace of dimension $3$.

## Gap

The preregistration's source and literature check found the conjecture stated
in arXiv:2311.16349v1 and the journal version, with no settlement in the
searched literature. Han and Liu's later survey, arXiv:2608.30006v2, proves
the multiplicity-one character case and lists exact indices with nontrivial
multiplicity spaces as open. This dossier records that scoped literature
reading; it does not claim exhaustive worldwide priority.

## Route

1. Character orthogonality identifies the C3 twirl with three-block pinching.
2. The map
   $V(u,v,w)=((u,v),(u,w),(v,w))/\sqrt2$ is an isometry from $\mathbb C^3$
   into the six-dimensional multiplicity space. Its three surviving
   $2\times2$ compressions contain every entry of a $3\times3$ operator, so
   the induced map is injective and $pr\ge3$.
3. Knill–Laflamme compression into a block gives $\beta\le2$, while a whole
   block gives $\beta\ge2$.
4. One frame vector retrieves $\mathbb C$, while three intensity functionals
   on the four-dimensional real space of Hermitian $2\times2$ matrices have
   an indefinite common kernel element; hence $\mathcal I_2\ge4$ and
   $k=1$.
5. The direct collision construction is by $u+v,u-v$ when a subspace meets a
   block, and otherwise by $x,Dx$ with
   $D=\operatorname{diag}(1,\omega,\omega^2)$.

The Lean elaboration uses Matrix.conjTranspose for the rectangular encoding and
the nonzero-dimension clause in Irreducible; both repairs preserve the source's
mathematical meaning. Square matrices continue to use star.

## Falsifier

The result is the negation of the finite-group specialization of the
conjecture, at $G=\operatorname{Multiplicative}(\mathbb Z/3\mathbb Z)$,
$d=3$, $n(i)=1$, $m(i)=2$, the three characters, and $k=1$. Changing the
finite normalized twirl, the pure-state outer product, the positivity
condition on multiplicities, or either frame-length inequality changes the
formalized question.

## Evidence

The canonical source is
D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.lean.
Its public declarations are the source definitions, claim, and result : ¬ claim;
all other declarations are consumed private helpers. The Freeze event is
sha256:65be1f4a0a0c9a9727f326a6ec2754a76b92ca11a92089d0fd6e937e953f2eba,
and the module statement identity is
sha256:25c50d810d9dd88c0661fffddc0a0f58265351511af9afdac38bde900743c272.
The result declaration identity is
sha256:00c9ac82b501261a08ded9df1527298e9299aec7b80e3e9d05ee746d7704e74a.
The Freeze event has no prerequisite frozen node IDs. The public result is the
designated refutation result (basis=refutes) and is exempt from four-slot
escape registration (CLAUDE.md §3.9). No other public theorem is introduced.

The experiment entry
[docs/reports/han-liu-2023-twirling-phase-retrievability/check.py](https://github.com/the-omega-institute/trureturing-experiments/tree/f6ee5dbb27030c3554ff6fb42385288a0451685e/docs/reports/han-liu-2023-twirling-phase-retrievability)
in the-omega-institute/trureturing-experiments at
f6ee5dbb27030c3554ff6fb42385288a0451685e was run as python3 check.py
(exit 0, bad= 0); its SHA-256 is
ab6b97bfc28e73a2f109da1133b6568d963be30cf5767d70b4d758e5d992f8ca.
The computation checks the twirl identity on four block triples, the encoding
on all 24 triples with $N\le12$ and $\lfloor N/2\rfloor>\max m_i$, 80
random upper-bound subspaces, 200 random triples for $\mathcal I_2$, four
generic frame vectors, and 200 random three-dimensional code subspaces.

## Triage

The settlement is Refuted and carries OpenProblemResolutionClaim(Refuted) on
the settling declaration. Every item below is stated as proved, computed or
open with its evidence kind.

### What the settlement shows

- **Mechanism — proved, kernel-checked:** result proves that the C3 twirl is
  three-block pinching and that the overlapping-pair encoding gives
  $pr\ge3>2=\max\{\beta,k\}$ on multiplicities $(2,2,2)$. The off-diagonal
  coherence crossing blocks is retained by the three compressions, while the
  code bound sees only the block dimensions.
- **$s=1$ — proved, kernel-checked:** result refutes the conjecture at
  multiplicities $(2,2,2)$ by establishing $pr\ge3>2=\max\{\beta,k\}$.
  The exact value $pr=3$ also uses the prose upper bound below; the Lean
  delivery establishes only this $s=1$ counterexample.
- **$(2s,2s,2s)$ for every $s\ge1$ — proved in prose:**
  $pr=3s>2s=\max\{\beta,k\}$ for the $C_3$ twirl with its three characters
  each of multiplicity $2s$.

  For the lower bound, let $u,v,w\in\mathbb C^s$ and
  $V(u,v,w)=((u,v),(u,w),(v,w))/\sqrt2$, with
  $H_i=\mathbb C^{2s}$. Each coordinate occurs twice, so
  $\|V(u,v,w)\|^2=\|u\|^2+\|v\|^2+\|w\|^2$ and $V$ is an isometry.
  The three compressions of $\Phi(VXV^*)$ are half the principal
  compressions on $(u,v)$, $(u,w)$ and $(v,w)$; together they contain every
  block entry of $X$. Thus $X\mapsto\Phi(VXV^*)$ is injective. In particular,
  equality of the outputs for $Vz,Vt$ implies $zz^*=tt^*$ and hence
  $(Vz)(Vz)^*=(Vt)(Vt)^*$, exactly the source's PhaseRetrievable condition.
  Therefore $\operatorname{ran}V$, of dimension $3s$, gives $pr\ge3s$.

  For the upper bound, let $M$ have dimension $q>3s$. If
  $M\cap H_i$ contains $u\ne0$, rank-nullity gives
  $\dim(M\cap\ker P_i)\ge q-2s>0$; choose a nonzero $v$ in that kernel.
  The orthogonal, nonzero vectors $u,v$ make $u+v,u-v\in M$ collide under
  pinching, because all cross terms join different blocks. They are not
  phase multiples: their $H_i$ components force the phase to be $1$, while
  their complementary components force it to be $-1$.
  Otherwise $M\cap H_i=\{0\}$ for every $i$. With
  $\omega=e^{2\pi i/3}$ and $D=\operatorname{diag}(1,\omega,\omega^2)$
  acting by scalars on the three blocks,
  $\dim(M\cap D^{-1}M)\ge2q-6s>0$. Choose a nonzero $x$ in this intersection;
  both $x,Dx$ lie in $M$, and $\Phi(Dxx^*D^*)=\Phi(xx^*)$. The distinct
  block phases imply that a phase multiple $Dx$ of $x$ would put $x$ in one
  block, contradicting $M\cap H_i=\{0\}$. In both cases the equal-norm
  vectors have distinct rank-one matrices, so $M$ is not PhaseRetrievable.
  By the source's definition of $pr$ as the largest admissible dimension,
  $pr\le3s$.

  The source's Theorem 3.4 gives $\beta=\max_i m_i=2s$. The number of
  inequivalent characters remains $d=3$, and the same frame-length facts
  $\mathcal I_1=1\le3<4\le\mathcal I_2$ as for $s=1$ give $k=1$.
- **Family encoding tests — computed, numerical rank and dimension readings:**
  the pinned script's 24-triple rank tests include $(2,2,2)$ and $(4,4,4)$,
  with logical dimensions $3$ and $6$. It also prints the logical dimension
  $9$ for $(6,6,6)$, but does not rank-test that triple. Its rank tests use
  numerical matrix rank; it does not compute exact symbolic ranks for
  $s=1,2,3$. The dimensions and injectivity for every $s\ge1$ are established
  by the prose argument above.
- **Three-block classification — proved in prose:** for positive integer
  block dimensions $m_1,m_2,m_3$, let $N=m_1+m_2+m_3$,
  $r=\max_i m_i$ and $T=\lfloor N/2\rfloor$. Then
  $pr=\max\{r,T\}$ for three-block pinching.

  A single block is PhaseRetrievable because pinching leaves its operators
  unchanged, giving $pr\ge r$. When $T\ge r$, start with
  $(a,b,c)=(T-m_3,T-m_2,T-m_1)$, whose entries are nonnegative and whose
  sum is $3T-N=T-(N-2T)$. Add the slack $\delta=N-2T\in\{0,1\}$ to $a$.
  The resulting integers satisfy $a+b+c=T$,
  $a+b=m_1$, $a+c=m_2$, and $b+c=m_3-\delta\le m_3$.
  Embed $((u,v),(u,w),(v,w))/\sqrt2$ for
  $u\in\mathbb C^a$, $v\in\mathbb C^b$, $w\in\mathbb C^c$ into the
  three blocks, padding unused coordinates by zero. This is an isometry,
  and its compressions contain every entry of an operator on
  $\mathbb C^a\oplus\mathbb C^b\oplus\mathbb C^c$, including when a
  summand has dimension zero. The same pure-state-injectivity argument
  gives a PhaseRetrievable subspace of dimension $T$, so $pr\ge\max\{r,T\}$.

  For the upper bound, let $q>\max\{r,T\}$. If $M$ meets $H_i$ nontrivially,
  $\dim(M\cap\ker P_i)\ge q-m_i>0$ and the $u\pm v$ construction above
  violates PhaseRetrievable. Otherwise
  $\dim(M\cap D^{-1}M)\ge2q-N>0$, since $q>\lfloor N/2\rfloor$; the
  $x,Dx$ construction above gives the violation. Thus no admissible
  dimension exceeds $\max\{r,T\}$, proving the classification.
- **Three-block encoding and collision tests — computed:** python3 check.py,
  exit 0, $bad=0$, with the SHA-256 and pinned experiment entry in Evidence,
  numerically rank-tests the encoding's injectivity for all 24 triples with
  $N\le12$ and $T>r$. It samples collisions on 80 random subspaces: 20 each
  for $(2,2,2)$, $(3,2,2)$, $(3,3,2)$ and $(4,3,3)$, at dimension
  $q=\max\{r,T\}+1$. These are numerical tests of the encoding and the
  collision construction; the script computes neither the exact index nor
  the universal upper bound. The exact classification rests on the prose
  proof, not on the samples.
- **What survives — proved by the source literature:** the multiplicity-one
  character case remains compatible with the source's formula. This delivery
  does not claim a new Lean theorem for the general character case.
- **Exact scope beyond three blocks — open:** the exact index for more than
  three blocks and for noncommutative groups with nontrivial multiplicity
  spaces remains unresolved. Han and Liu's survey lists this class as open.

The computation was rerun from the pinned script with python3 check.py, exit 0,
and the SHA-256 above. Its tested scope is exactly the finite list and sample
counts stated in Evidence; the uniform family and classification use the
prose proofs, not a computational extension of that scope.

## ASSUMED-UNVERIFIED

The literature search is scoped to the cited source, the authors' survey and
the related readings recorded in issue #15229. The more-than-three-block case
and noncommutative multiplicity spaces remain open. The family and three-block
classification are proved in prose, not kernel-checked generalizations.
The two elaboration repairs
are semantic translations of the source notation, checked by the
kernel-verified result.
