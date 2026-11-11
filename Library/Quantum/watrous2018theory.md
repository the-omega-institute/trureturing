---
bibkey: watrous2018theory
authors: John Watrous
year: 2018
title: The Theory of Quantum Information
doi: 10.1017/9781316848142
claim: Finite-dimensional quantum channels admit complete Kraus and isometric Stinespring representations; positive trace-preserving maps admit invariant density operators.
strata_touched:
  - D5/S3/Quantum/ChannelFixedState
  - D5/S3/Quantum/Entanglement/FiniteSectorChannelOptimality
license: citation-only
triage: anchor
---

# The Theory of Quantum Information

John Watrous's book supplies the literature anchor for fixed points of
finite-dimensional quantum channels in Section 4.4. The result represented by
`D5/S3/Quantum/ChannelFixedState.channel_fixed_state_exists` is the standard
invariant-density-operator existence statement for a positive trace-preserving
complex-linear map on a nonempty finite-dimensional matrix algebra.

The repository proof uses Cesaro averages and finite-dimensional compactness.
This note does not attribute that proof method, the pure-fixed-point premise of
Theorem 4.5, complete positivity, the tangent factor, or equivalence with an
interior faithful invariant state to the cited section.

## Search log

- 2026-08-07: The review correction identified John Watrous, *The Theory of
  Quantum Information*, Cambridge University Press (2018), DOI
  `10.1017/9781316848142`, Section 4.4, as the literature source for the
  finite-dimensional channel fixed-point setting and invariant states.
- 2026-08-07: The scope was cross-checked against the Lean declaration: the
  repository theorem assumes a complex-linear map, positivity, and trace
  preservation on matrices indexed by a finite nonempty type. It does not
  assume complete positivity.
- 2026-08-07: No specific theorem number is attributed because none was
  verified in this worktree.

## Verified locator

- DOI: https://doi.org/10.1017/9781316848142
- Cambridge University Press, Section 4.4

## Complete channel representations

The author-hosted pre-publication copy at
https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf gives the following precise
locators. Page numbers are printed pages, followed by one-based PDF pages.

- Theorem 2.22, pp. 82-83 (PDF 90-91): complete positivity is equivalent
  to positive Choi representation, a Kraus representation with identical
  left and right operators, and a Stinespring representation with identical
  left and right dilation operators. The proof applies complete positivity
  to the unnormalized maximally entangled operator and factors the resulting
  positive Choi operator spectrally.
- Theorem 2.26, pp. 87-89 (PDF 95-97): trace preservation is equivalent
  to completeness of every Kraus representation and to the identity
  A* B = I for every Stinespring representation.
- Corollary 2.27, p. 89 (PDF 97), equations (2.129)-(2.130): a quantum
  channel admits a complete Kraus family and an isometric Stinespring
  dilation, each representing its action on every input operator.

The proof of `FiniteSectorChannelOptimality.result` applies this
finite-dimensional representation theorem internally in the canonical
matrix channel interface. Its Kraus/environment index has cardinality
equal to the product of input and output dimensions; zero Kraus operators
pad the spectral representation. They do not assert that this is the
minimal Choi-rank environment. The internal representation also includes empty
coordinate types; those cases follow from the empty matrix identities,
and are not attributed to the book's nonzero-map statement in Theorem 2.22.

The finite representation theorem alone does not establish the optimum over
local channels in the spectral coarse-graining problem, or its stabilized
trace-norm error formula.


## Instrument composition and predictive intertwining

The book's finite-dimensional channel and measurement formalism supplies the standard setting below.
The displayed simulation lemma is derived here by composition; it is not attributed to a numbered theorem in the source.
Let $\mathcal I_{t,a,y}$ and $\mathcal J_{t,a,y}$ be CP, trace-nonincreasing instrument branches,
whose sums over $y$ are trace preserving for every legal action $a$.
Let $\mathcal E_t$ be CPTP summaries between the respective finite-dimensional matrix or classical–quantum block algebras.
Assume the initial target state is $\widehat\sigma_\emptyset=\mathcal E_0(\sigma_\emptyset)$ and, on all reachable unnormalized states,

$$
\mathcal E_{t+1}\mathcal I_{t,a,y}=\mathcal J_{t,a,y}\mathcal E_t.
$$

Use the same policy $a=\pi(h)$ determined by the recorded history $h$, and preserve action-legality guards.
For unnormalized post-record states, induction gives

$$
\widehat\sigma_h=\mathcal E_{|h|}(\sigma_h),\qquad
\Pr_{\mathcal J}(h)=\operatorname{tr}\widehat\sigma_h
=\operatorname{tr}\sigma_h=\Pr_{\mathcal I}(h).
$$

Indeed, apply the branch identity after each step; the trace of an unnormalized branch state is its outcome-history probability.
Matched histories select the same next action. At positive probability, dividing by the common trace gives the corresponding conditional-state identity.
This establishes all finite transcript laws, not an efficient method to obtain or evaluate a summary.
For infinite or continuous classical registers, an additional measurable channel/instrument framework is needed;
finite block algebras alone do not supply it.

The project-specific substitution, including program, optimizer memory and native gate choice, is in
[Self-Generated Predictive Memory §11](../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md).

## One actual self-reference for finite sector operations

This is an application of Theorems 2.22 and 2.26 to the actual finite
sector product in the
[comparison reconstruction](../QuantumStates/barnumhilgert2019spectral.md#a-complete-finite-comparison-candidate).
It assumes that reconstruction's common matrix coordinates and retains
all of its conditional paper bridges. It neither derives those coordinates
from endpoint reciprocity alone nor adds a new Choi or Kraus theorem.
The author-hosted chapter is
https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf; the theorem numbers and
printed pages agree with the locators above.

### Carrier, operation and its uniquely determined spectator action

Fix a nonempty finite set $I$, positive integers $n_i$, and the same actual
local and self-composite ordered spaces

$$
A=\bigoplus_{i\in I}\operatorname{Herm}(\mathbb C^{n_i}),\qquad
D=\bigoplus_{i,k\in I}\operatorname{Herm}
 (\mathbb C^{n_i}\otimes\mathbb C^{n_k}).
$$

The cones are the blockwise PSD cones, $u_A(x)=\sum_i\operatorname{Tr}x_i$,
and the actual product is $m(x,y)_{ik}=x_i\otimes y_k$.
These products span $D$ as a real vector space. A real-linear map
$T:A\to A$ has blocks $T_{ji}$; each has a unique complex-linear,
Hermiticity-preserving extension to all matrices. The unique real-linear
map $L_T:D\to D$ agreeing with $m(Tx,y)$ on every product $m(x,y)$ is

$$
(L_T X)_{jk}=\sum_i(T_{ji}\otimes\mathrm{id}_{n_k})(X_{ik}).
$$

The right side acts on the first tensor factor and leaves the actual
reference factor fixed. No positivity of $T$ or $L_T$ is assumed here.

### A single reference state retains the input-sector label

Choose $w_i>0$, $\sum_iw_i=1$, and a basis in each sector. Set

$$
|\phi_i\rangle={1\over\sqrt{n_i}}\sum_{r=1}^{n_i}|r\rangle\otimes|r\rangle,
\qquad Q_i=|\phi_i\rangle\langle\phi_i|.
$$

Let $\Omega_w\in D$ have block $w_iQ_i$ at $(i,i)$ and zero at $(i,k)$
when $i\ne k$. This is one normalized state of the actual self-composite.
Its reference marginal is the faithful state
$\sigma_w=\bigoplus_i(w_i/n_i)I_i$. Although $\sigma_w$ is faithful,
$\Omega_w$ need not have full matrix rank.

For $F_T=L_T(\Omega_w)$ and the unnormalized Choi matrix

$$
C_{ji}=\sum_{r,s=1}^{n_i}T_{ji}(|r\rangle\langle s|)
                 \otimes|r\rangle\langle s|,
$$

the actual output block is exactly

$$
(F_T)_{ji}={w_i\over n_i}C_{ji}. \tag{R1}
$$

Different input sectors do not average into the same block: the untouched
reference label is $i$. Thus positivity of this one output tests every
$C_{ji}$ separately, including cross-sector transitions. Keeping that
label is essential to the argument.

**Finite reference criterion.** The following are equivalent:

1. $F_T\succeq0$.
2. Every $T_{ji}$ is completely positive.
3. $L_T$ preserves the full positive cone of this actual $D$.
4. For every finite matrix reference dimension $r$, the block extension
   $T\otimes\mathrm{id}_r$ is positive on
   $\bigoplus_i\operatorname{Herm}(\mathbb C^{n_i}\otimes\mathbb C^r)$.

**Proof.** By (R1) and $w_i/n_i>0$, item 1 is exactly positivity of every
Choi matrix. Apply Watrous Theorem 2.22 to each nonzero rectangular block;
a zero block has the empty Kraus representation and is CP directly.
This gives item 2. For CP blocks, every summand in the formula for $L_T$
is PSD on PSD inputs, giving item 3, and the same argument with arbitrary
$r$ gives item 4. Item 3 implies item 1 because $\Omega_w\succeq0$.
Item 4 implies positivity of each $C_{ji}$ by taking $r=n_i$ and an input
supported in sector $i$ equal to $Q_i$. This closes the equivalences.

Consequently, a single specified state in one actual self-composite
replaces a test over all matrix-reference sizes in this finite model.
This counts one specified input state, while still testing positivity of its
full joint output; it is not one binary measurement or an efficient
certification claim. The conclusion does not assert the existence or the
correct composition law of independently supplied higher physical composites.

### Operations become positive correlations with a marginal constraint

The Choi correspondence in each block also makes $T\mapsto F_T$ a
real-linear bijection from real-linear maps $A\to A$ to $D$. In the
chosen bases its inverse is

$$
T_{ji}(X)={n_i\over w_i}\operatorname{Tr}_{\rm ref}
 \bigl[(F_T)_{ji}(I_j\otimes X^{\mathsf T})\bigr]. \tag{R2}
$$

Let $E_i=\sum_jT_{ji}^*(I_j)$, where $*$ denotes the Hilbert--Schmidt
adjoint. The output partial trace, retaining only the reference, satisfies

$$
\bigl(\operatorname{Tr}_{\rm out}F_T\bigr)_i
 =\sum_j\operatorname{Tr}_{\mathbb C^{n_j}}(F_T)_{ji}
 ={w_i\over n_i}E_i^{\mathsf T}. \tag{R3}
$$

For positive $T$, $u_A(Tx)\le u_A(x)$ for every $x\succeq0$ is equivalent
to $E_i\le I_i$ for every $i$, by testing arbitrary PSD inputs in each
input sector. Equality of traces is equivalent to $E_i=I_i$.
Transposition preserves PSD order, so (R3) gives the exact descriptions

$$
\begin{aligned}
\text{CP, trace-nonincreasing branches}
 &\longleftrightarrow
 \{F\succeq0:\operatorname{Tr}_{\rm out}F\preceq\sigma_w\},\\
\text{CP, trace-preserving channels}
 &\longleftrightarrow
 \{F\succeq0:\operatorname{Tr}_{\rm out}F=\sigma_w\}.
\end{aligned} \tag{R4}
$$

These are convex sets of correlations inside the same actual $D$;
the first is an inequality slice of its PSD cone, and the second an
affine slice. Normalization $\operatorname{Tr}F=1$ alone is insufficient
for a channel: the full reference marginal must equal $\sigma_w$.
For a finite outcome family $(T_a)$, an instrument is equivalently
$F_a\succeq0$ with $\sum_a\operatorname{Tr}_{\rm out}F_a=\sigma_w$.
Each branch then has the marginal inequality automatically.

By the same rectangular Choi/Kraus theorem, these statements are also
equivalent to block Kraus families

$$
(T_a x)_j=\sum_{i,\alpha}V_{a,ji\alpha}x_iV_{a,ji\alpha}^*,
\qquad
\sum_{a,j,\alpha}V_{a,ji\alpha}^*V_{a,ji\alpha}=I_i
\quad\text{for each input }i.
$$

For a single branch, the condition is
$\sum_{j,\alpha}V_{ji\alpha}^*V_{ji\alpha}\le I_i$ for each $i$. Each nonzero block
needs at most $n_in_j$ Kraus operators. The existing rectangular Lean
source `D5/S3/Quantum/Foundation/FiniteKrausRepresentation.lean`
provides the matrix-factor theorem; the direct-sum and actual-reference
correspondence here is a paper application, not a new kernel check.

For a normalized input $x$, outcome $a$ has probability
$p_a=u_A(T_ax)$; when $p_a>0$, its conditional state is $T_ax/p_a$.
Successive finite instruments have branches $S_b\circ T_a$, with block
Kraus operators $W_{b,j\ell\beta}V_{a,\ell i\alpha}$; their outcome sum
is trace preserving by composition. Coarse-graining outcomes adds their
positive correlations. These are the usual finite sequential probability
and update rules, and impose no commutation of successive branches.

### Sharp neutral branches reuse the existing uniqueness argument

Let $P=(P_i)$ be a tuple of projections. Suppose a positive real-linear
branch $K:A\to A$ satisfies

$$
u_A(Kx)=\sum_i\operatorname{Tr}(P_ix_i),
$$

for all $x\succeq0$, and fixes every normalized state with certain-yes
probability $\sum_i\operatorname{Tr}(P_ix_i)=1$. Then
$K(x)_i=P_ix_iP_i$ for every $x\in A$.

This is the sector application of
[Proposition 13.4.1](../../docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md).
For input sector $i$, a rank-one state in $\operatorname{Ran}P_i$ is
fixed as an actual state of $A$, including zero in every other output
sector. A rank-one state in $\ker P_i$ has positive output with total
trace zero, so its output is zero in every sector. The same closed-cone
argument of that proposition, applied to
$\sqrt\epsilon u+e^{i\theta}v$ with $u\in\operatorname{Ran}P_i$ and
$v\in\ker P_i$, kills the cross terms in every output sector.
Rank-one projectors span the two diagonal Hermitian subspaces, giving
the stated block compression. Cases $P_i=0$ and $P_i=I_i$ are included.
No CP premise or new single-factor uniqueness theorem is needed.

### Scope, missing labels and insufficient local tests

For $n_i=1$, $Q_i$ is the scalar unit. If every sector is scalar,
(R4) reduces to nonnegative transition matrices with column sums at most
one or exactly one. Thus the reference criterion includes classical
stochastic theory; it does not itself select a nonclassical sector.

If a reference weight is zero in a nonscalar sector, the identity and
transpose on that input sector give identical outputs on $\Omega_w$,
while transpose fails full reference positivity. Strictly positive
weights prevent this blind sector. Also, a faithful marginal alone does
not suffice: for a single sector $n\ge2$, the product probe
$(I_n/n)\otimes(I_n/n)$ is unchanged by transpose on the first factor,
but the entangled $Q$ is sent to $F_{\rm swap}/n$, with eigenvalue
$-1/n$ on an antisymmetric vector. A product probe can therefore miss
an operation forbidden by the full joint cone. Testing only product
effects on that latter output also misses its negative joint direction.

Even a CP instrument's static effects do not determine its update.
For $P_b=|b\rangle\langle b|$ on $\mathbb C^2$, the branches
$P_bxP_b$ and $XP_bxP_bX^*$, where $X$ swaps the basis states,
have identical effects and normalized outcome sums, but send an input
$P_0$ after outcome 0 to $P_0$ and $P_1$, respectively. They are
distinguished by a subsequent measurement in that basis. Certain-yes
pointwise neutrality excludes the second branch. This is also the
mechanism of the existing `same_effects_different_two_step_joint_law`
in `D5/S3/Quantum/Measurement/StaticEffectSequentialSeparation.lean`.

Discarding reference labels can hide the failure even in a normalized
output. For two dimension-two input sectors and one fixed output sector
$j$, take $T_{j1}(X)=X^{\mathsf T}$ and
$T_{j2}(X)=\operatorname{Tr}(X)I_2/2$, with other output blocks zero.
The normalized reference outputs are $F_{\rm swap}/2$ and $I_4/4$.
Choose weights $1/10$ and $9/10$. The actual labelled output retains
$(1/10)F_{\rm swap}/2$, with negative eigenvalue $-1/20$. If the two
reference sector labels are erased and their equal-size matrix outputs
added, the result is

$$
{1\over20}F_{\rm swap}+{9\over40}I_4,
$$

whose antisymmetric and symmetric eigenvalues are $7/40$ and $11/40$.
It is a normalized positive matrix although one original block is not
CP. Full labelled output positivity prevents this cancellation.

### Complete finite candidate and its compressed reading

Retain the full-effect least-confirmation condition S on every actual
carrier, the bilinear state/effect product and pairing contract, and
the three-copy common-record condition of the linked comparison
candidate. Under its stated conditional geometry and sector bridges,
fix the resulting actual matrix coordinates and $\Omega_w$ above.
Define the mathematically admissible branches by the positive-correlation
and marginal inequality in (R4), instruments by its finite-outcome sum,
and ideal sharp branches by certain-yes pointwise neutrality.
This gives the finite direct-sum CP instrument theory and the sharp
Lüders update, with Born probabilities from the previous pairing.
The identity channel, finite block Kraus instruments and the sharp
compressions give nonempty examples; the characterization is exact
within this specified finite model.

Calling every such map admissible is a model closure convention.
The existence of physical devices realizing all those maps does not
follow from the static comparison relations or from Choi's theorem.
The reference condition compresses the matrix positivity tests; it
does not remove the earlier independent geometry/composition inputs.
A clock, a chosen Hamiltonian, independently realized higher composites,
infinite-dimensional extension and experimental correspondence remain
outside this characterization.

In ordinary words, compare pure endpoints reciprocally and require
comparison of a random pure preparation to agree with the reversed
weighted comparisons. The two actual triple brackets must have the same complete legal
record set. One fixed swap of the first two labels must send every legal
record to a legal record, over all sectors and entangled inputs; individual
entries of a record need not stay equal. Once those relations have the stated
finite matrix representation, keep one reference that remembers every
input sector. A proposed operation is mathematically admissible exactly
when its action on that reference leaves a positive joint correlation
and does not increase the untouched reference marginal; the outcomes
of a complete instrument exhaust that marginal. A sharp yes-filter is
ideal when it leaves every certain-yes state unchanged. These conditions
concern consistent comparisons and records; they do not require physical
measurements performed in opposite time orders to agree.
