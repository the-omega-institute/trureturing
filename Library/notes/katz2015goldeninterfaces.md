---
bibkey: katz2015goldeninterfaces
authors: Nicholas M. Katz
year: 2015
title: Wieferich past and future
doi: 10.1090/conm/632/12632
claim: Katz's torus equidistribution conjecture has an exact fixed-golden specialization; macroscopic equidistribution alone does not force a WSS zero.
strata_touched: []
license: citation-only
triage: anchor
---

# Original WSS arithmetic across geometric realizations

## Verified locator

Nicholas M. Katz, *Wieferich past and future*, Contemporary Mathematics 632
(2015), 253-270, DOI 10.1090/conm/632/12632.
Author-hosted paper:
https://web.math.princeton.edu/~nmk/wieferich42.pdf

## 1. The geometric equidistribution conjecture

Source scope: Sections 2-6, including Conjectures 3.1, 4.7 and 6.1,
the Lie-algebra exact sequence, and Section 5's lattice warning.

Conjecture 4.7 concerns a torus over Z[1/N], a point generating a Zariski-dense
cyclic subgroup, and an integral Lie lattice. It predicts Haar-equidistribution
of the Wieferich fractions in the compact real torus of that lattice.
Conjecture 6.1 gives a framed formulation. Section 5 cautions that an arbitrary
change of lattice is not an automatic equidistribution-preserving operation.

CG.1 and CG.7 choose the norm-one torus of O=Z[phi], the SAME point
u=phi/(1-phi)=-phi^2, and Lie lattice Z*sqrt(5). For p>5, N_p=p-(5/p),
and original q_p=F_(N_p)/p mod p, the computed defect is

`(u^N_p-1)/p = (5/p)*q_p*sqrt(5) mod p`.

Hence the actual Katz fraction is c_p/p, where c_p is the least nonnegative
residue of (5/p)*q_p. Its zero set is exactly the original WSS set. The point
is nontorsion and therefore Zariski dense in this one-dimensional torus.
This is a specialization of an existing conjecture, not a randomness theorem.

CG.7 proves that even prime-denominator equidistribution need not hit zero.
Its artificial countermodel is not a Fibonacci sequence or a refutation of
Katz. The exact Fourier zero-counting identity is recorded separately. Its
full nonconstant-frequency error would need a genuinely new estimate on the
log-log scale; no such estimate is supplied. Fixed-frequency macroscopic
cancellation is not silently strengthened to shrinking-target control.

## 2. p-rationality and actual local geometry

Zakariae Bouazzaoui, *Fibonacci Sequences And Real Quadratic p-Rational Fields*,
arXiv:1902.04795.
https://arxiv.org/abs/1902.04795
https://arxiv.org/pdf/1902.04795

Source scope: Corollary 2.2, Remark 2.3, Proposition 3.2 and Theorem 3.4,
with their discriminant and class-number conditions. For the fixed
field Q(sqrt(5)), class number one and p>5 give: p is WSS iff the field is not
p-rational. Corollary 2.2 also relates this to divisibility of L(2-p,chi_5).
Nonvanishing of a p-adic logarithm is weaker than initial valuation exactly
one and cannot settle WSS. In the split case O/pO is a product of fields;
CG.2-CG.4 use its norm-one group, not a falsely cyclic full
unit group.

CG.2-CG.4 prove their local formulas directly. Exactly one of the p lifts of
a norm-one residue preserves the N_p return. The derivative U_(N_p)'(1) is
-2/5 modulo p, always nonzero. The unique Hensel root a_p in 1+p Z_p has
v_p(a_p-1)=h_p and first displacement (5/2)q_p. Varying the coefficient to
this root does not produce a WSS prime for the fixed coefficient one.
The local orbit closure has index p^(h_p-1) in the principal norm-one group.
These are complete local descriptions retaining the unknown actual h_p.

Rigoberto Florez, Robinson A. Higuita and Alexander Ramirez,
*The Resultant, the Discriminant, and the Derivative of Generalized Fibonacci
Polynomials*, Journal of Integer Sequences 22 (2019), Article 19.4.4.
https://cs.uwaterloo.ca/journals/JIS/VOL22/Florez/florez23.html

The paper provides classical polynomial-derivative context. CG.4
proves its displayed identity; no unverified theorem number or first-discovery
claim is used.

## 3. An exact integral-basis transfer

Lenny Jones, *A new condition for k-Wall-Sun-Sun primes*, arXiv:2302.10357v4,
revised July 15, 2023; author PDF dated July 18, 2023.
https://arxiv.org/abs/2302.10357
https://arxiv.org/pdf/2302.10357

Source scope: the definition of polynomial monogenicity, Theorem 1.1,
Proposition 2.5 and the index-criterion argument. At k=1 the
hypotheses hold, giving

`p is WSS iff X^(2p)-X^p-1 is non-monogenic`.

For a root theta_p with theta_p^p=phi, K_p=Q(theta_p) contains the original
fixed golden field. Non-monogenic here concerns the SPECIFIED power basis:
Z[theta_p] is not the full ring of integers. It does not assert that no other
generator of K_p has a power integral basis. The displayed polynomial
discriminant has absolute value 5^p p^(2p), and equals the square of that
index times disc(K_p). Its p-divisibility, and the reduction to
(X^2-X-1)^p mod p, occur for every p and alone do not decide the index.
No new global index constraint is proved here.

## 4. Arithmetic derivatives and cohomology

Alexandru Buium and Santiago R. Simanca, *Arithmetic partial differential
equations*, arXiv:math/0605107v2.
https://arxiv.org/abs/math/0605107

The abstract describes Fermat-quotient operators and usual derivations on
arithmetic groups; the full technical development is outside this note's
source scope. CG.6
defines delta_p(x)=(sigma_p(x)-x^p)/p on the unramified golden algebra,
proves its multiplication law, and computes its value at phi as a unit
multiple of original q_p. No arithmetic Ricci-flow theorem or WSS existence
result is attributed to this paper.

Gebhard Boeckle, David-A. Guiraud, Sudesh Kalyanswamy and Chandrashekhar Khare,
*Wieferich Primes and a mod p Leopoldt Conjecture*, arXiv:1805.00131v2.
https://arxiv.org/abs/1805.00131

The primary introduction and real-quadratic discussion connect regulator
congruences with Galois representations, cohomology and deformation theory.
No statistical hypothesis there is used as a proved golden-unit theorem.

## 5. The actual three-manifold bridge and its limit

CG.5 uses A=[[1,1],[1,0]], B=A^2 and S=2A-I. For every positive EVEN n,
it proves B^n-I=F_n S A^n and computes the actual integer cokernel with Smith
factors F_n and 5F_n. Abelianizing the actual torus mapping-torus group gives
H1=Z plus that cokernel. At n=p-(5/p), its p-primary torsion is (Z/p^h_p)^2.
This is a literal continuous three-manifold realization of the original WSS
depth. No new bound on that depth follows merely from real hyperbolicity,
entropy, or the topological identification.

## 6. Related results and boundaries

Nic Fellini and M. Ram Murty, *Wieferich primes in number fields and the
conjectures of Ankeny-Artin-Chowla and Mordell*, arXiv:2508.08472v2.
https://arxiv.org/html/2508.08472v2

Theorem 1.2 gives conditional non-Wieferich infinitude under number-field abc.
Theorem 1.3 instead assumes finitely many super-Wieferich primes. Neither is
an unconditional WSS-existence theorem. The same source reports AAC and
Mordell counterexamples in VARYING quadratic fields; they are not fixed-golden
WSS examples. The Pell-height route remains conditional and
points primarily toward non-WSS results.

The p-rational and integral-basis formulations are established transfers, not
additional independent problems counted on top of WSS. The remaining
arithmetic obligation is a constraint on actual original q_p/h_p, a WSS
witness, or a new global distribution theorem. Rephrasing the same unknown
in multiple spaces does not supply such a result.

## 7. Exact Zeckendorf predictive states at the original prime-square scale

This section keeps the original Fibonacci numbers and the same WSS problem
family. It connects the least-significant-first residue transducer to the
completed-future viewpoint and to an explicitly specified probability law.
The state count concerns an autonomous finite-state input reader. Reading
time supplied by an external clock is a different resource model.

### 7.1 Actual words, tasks, and the observable state

Fix an integer M>=2. A finite binary word w=b_0...b_(n-1) is read from its
least significant position, with value

$$V(w)=\sum_{j=0}^{n-1}b_jF_{j+2}.$$

It is legal if it has no adjacent ones. The empty word represents zero;
arbitrary zero padding on the HIGH end, which is the right end in this
orientation, is permitted. Invalid words are rejected. This is not the
self-delimiting Fibonacci code with a terminal11 marker.

Let T=pi(M) be the least period of the pair (F_j,F_(j+1)) modulo M, and
R=rho(M) the least positive index at which M divides F_R. Both exist:
S(u,v)=(v,u+v) is invertible, with inverse (v-u,u), on a finite set.
Returning the pair (0,1) gives the period. Necessarily T>=3. The actual
reader state is

$$(r,k,l),\qquad r\in\mathbb Z/M,\quad k\in\mathbb Z/T,\quad l\in\{0,1\},$$

with next weights (u,v)=(F_(k+2),F_(k+3)) modulo M. Reading b updates

$$(r,u,v,l)\longmapsto(r+bu,v,u+v,b),$$

unless l=b=1, which leads to one absorbing rejecting state. Start at
(0,1,2,0). These are the recurrence coordinates of the existing
`D5/S1/Digit/ZeckendorfResidueTransducer.lean`. That owner is formulated
for prime moduli; the arithmetic here explicitly includes composite M.

Two tasks must be separated. The full-residue task outputs the entire r
at every finite termination and an invalid symbol at the rejecting state.
The divisibility task outputs only whether termination is legal and r=0.
Two prefixes have the same task-complete future if every finite suffix
produces the same corresponding output. This includes the empty suffix.
It is stronger than equality of the current output.

### 7.2 A constructive supply of every legal arithmetic probe

**Theorem ZP1.** At any incoming boundary bit and any consecutive weight
row (u,v), every coefficient pair (A,B) modulo M is realized by a finite
legal continuation with added residue Au+Bv. The continuation can restore
the entire weight clock. A word of length at most4T(M-1) suffices. An
additional initial block0^T can reset the boundary bit when required.

**Proof.** The exact return F_T=0,F_(T+1)=1 implies S^T=I on every row.
For example induction gives

$$S^{n+1}(u,v)=(F_nu+F_{n+1}v,F_{n+1}u+F_{n+2}v),$$

and F_(T-1)=1 follows from the recurrence. Define two literal words

$$B_0=0^T1\,0^{T-1},\qquad B_1=0^{T+1}1\,0^{T-2}.$$

Both have length2T, begin and end with zero, and contain a single one.
They are legal after either boundary bit. The one in B_0 is at positionT
and contributes u; the one in B_1 is at positionT+1 and contributes v.
Both restore S's clock. If A_0,B_0' are the least representatives of A,B,
concatenate A_0 copies of the first word and B_0' copies of the second.
Its value is Au+Bv for every initial row simultaneously, its clock returns,
and its length is at most4T(M-1). The empty concatenation is legal too;
prefixing0^T resets a possibly nonzero boundary without changing the value
or clock. This proves unbounded controllability by actual legal words,
not by arbitrary coefficient queries that were never realizable.

### 7.3 The exact future kernel over composite residue rings

A row (u,v) is unimodular if eu+fv=1 for some e,f modulo M. Every actual
consecutive Fibonacci row is unimodular by consecutive coprimality.

**Theorem ZP2.** Two live reader states (r,u,v,l) and (r',u',v',l') have
the same complete divisibility future if and only if

$$\boxed{l=l'\quad\text{and}\quad
(r',u',v')=a(r,u,v)\text{ for some unit }a\bmod M.} \tag{ZP1}$$

This holds for every M>=2, including rings with zero divisors.

**Proof.** If the boundary bits differ, append a one to the state with
boundary zero. That state remains legal; by ZP1 and unimodularity of its
new row, an additional guarded continuation makes the terminal residue
zero. The other state rejects already at the first one. Thus equal futures
force equal boundary bits. Every live state has an accepting continuation
by the same argument, so it is distinguishable from the absorbing rejector.

With a common boundary, ZP1 implies equality of the two affine zero sets

$$r+Au+Bv=0\quad\Longleftrightarrow\quad r'+Au'+Bv'=0$$

for EVERY pair A,B in Z/M. Choose eu+fv=1 and define a=eu'+fv'.
The pair (A,B)=(-re,-rf) forces r'=ar. The pair (-re+v,-rf-u)
then forces vu'-uv'=0. Combining this relation with eu+fv=1 gives
u'=au and v'=av. Choose e'u'+f'v'=1 for the second row; then

$$a(e'u+f'v)=1,$$

so a is a unit. No field division was used. Conversely, scaling all
three coordinates by a unit commutes with the actual input recurrence
and preserves a zero terminal residue. Common boundary bits give the
same legality on every suffix. Induction on the word proves the reverse
implication, and hence the exact future kernel.

The companion `ZeckendorfFutureKernel.result` constructs ZP1 from the
literal Fibonacci return and proves the same-boundary equivalence with
explicit Bezout certificates. Boundary separation and the counting
consequences below are the ordinary deductions just displayed. This
scope is not enlarged by calling every consequence kernel-certified.

### 7.4 Exact minimal autonomous memory, not merely an upper bound

**Theorem ZP3.** With the stated orientation and padding convention, the
minimal COMPLETE deterministic observer has exactly

$$\boxed{2M\pi(M)+1\quad\text{states for full residue output},}$$

$$\boxed{2M\rho(M)+1\quad\text{states for divisibility}.} \tag{ZP2}$$

In each expression the added one is the absorbing invalid-word state.

**Proof of reachability.** ZP1 from (1,2) can add any desired residue,
restore phase zero and leave boundary zero. Append zeroes to choose any
phase with final bit zero. To obtain phase k and final bit one, first
choose phase k-1 modulo T by zeroes, and then append one; subtract its
known weight in the originally programmed residue. Thus all2MT live
states are reachable. The word11 reaches the rejector.

For the full output, the empty suffix identifies r. Suffix1 distinguishes
the two boundary bits through validity. With boundary zero, suffixes1
and01 identify u and v. With boundary one, the legal suffixes01 and001
identify v and u+v, hence u. No two different live states can merge.
There are exactly T different weight rows, proving the first count.

For the binary task, ZP2 describes every possible merger. The scalar
subgroup of the clock consists precisely of shifts d for which F_d=0
modulo M. Indeed, at the initial row, scalarity is equivalent to

$$F_{d+3}-2F_{d+2}=-F_d=0.$$

Its scalar is then F_(d+1), a unit by consecutive coprimality. Invertibility
of S transports this characterization to every other phase. Strong
Fibonacci divisibility shows that the zero indices are exactly the
multiples of R: gcd(F_R,F_d)=F_gcd(R,d), so minimality of R forces R|d
at every zero, and the converse is ordinary index divisibility.
Consequently the scalar clock subgroup has size kappa=T/R.

Each live future-equivalence class has exactly kappa members. Its action
is free on the T distinct clock phases, and the residue scales by the
same unit. There are therefore2MT/kappa=2MR live classes. These classes
are distinct future languages and are reachable, so the minimality
lower bound is exact, by the deterministic future-equivalence criterion.
Adding the separate rejector proves the second formula.

The same kappa=pi(p)/rho(p) that organized the scalar stationary phases
in the conic Fourier calculation is thus the EXACT compression factor
between these two arithmetic reading tasks. This is a concrete common
quotient; no assumption of independent observational channels is involved.

**Orientation boundary.** Charlier, Rampersad, Rigo and Waxweiler proved
2M^2 states for the trim minimal Fibonacci divisibility automaton with
most-significant-first input. Moradi, Rampersad and Shallit's2026 survey
uses that orientation and recalls that result. The present language is
read in the reverse direction and counts the rejector explicitly.
Formula ZP2 does not contradict or improve the2M^2 theorem in its own
model. Least-significant reading can require either more or fewer states,
depending on rho(M). Merely forgetting to charge for a clock would change
the comparison again.

### 7.5 A specified probability process preserves the same exact quotient

**Theorem ZP4.** Feed the reader with the legal golden Markov digit source

$$P=\begin{pmatrix}\phi^{-1}&\phi^{-2}\\1&0\end{pmatrix}.$$

Observe the actual future bits jointly with the terminal divisibility
answer, for every finite horizon. The exact predictive equivalence of
live states is still ZP1. The quotient has2M rho(M) states and a unique
stationary probability law, with mass

$$\boxed{\Pr([(r,k,l)])=\frac{\pi_l}{M\rho(M)},\qquad
\pi_0=\frac{\phi^2}{\phi^2+1},\quad
\pi_1=\frac1{\phi^2+1}.} \tag{ZP3}$$

Each expression [(r,k,l)] denotes one quotient state, not a low-prefix
cylinder in an infinite Zeckendorf sequence.

**Proof.** Both allowed transitions out of zero have positive probability,
and the one-to-zero transition has probability one. Every finite legal
word therefore has positive probability. Two states with equal boundary
and equal deterministic futures give the same joint bit-and-answer laws.
If ZP1 fails with equal boundary, the separating legal word in ZP2 has
positive probability, and its terminal answers differ. If boundaries
are different, the very next bit laws already differ. Thus the equivalence
is exact for this specified observed process. If only the digit process
were observed and the divisibility answers were omitted, the conclusion
would be different; only the boundary bit would be needed.

On the full live state space the stationary mass is pi_l/(MT). To verify
it, fix a target phase k and bit b. Each allowed predecessor boundary has
exactly one predecessor residue, since adding b times the old weight is
a permutation of Z/M. The predecessor phase is k-1. Summing incoming
weights therefore reduces to pi P=pi. Every scalar equivalence fibre
has kappa elements and a fixed boundary bit, so its total mass is ZP3.
Transition probabilities depend only on that boundary and the input bit,
while the deterministic transitions preserve ZP1. Hence this is a valid
quotient Markov chain. ZP1's guarded controls, with phase adjustment,
reach every live state from every other using positive-probability words.
The finite chain and its quotient are irreducible, proving uniqueness.
They can be periodic; time-by-time convergence from an arbitrary start
is not asserted. Stationarity or Cesaro averaging is sufficient here.

Writing H(pi)=-sum_l pi_l log pi_l, the finite stationary entropies are

$$H(\text{full state})=\log(M\pi(M))+H(\pi),$$

$$\boxed{H(\text{predictive state})=\log(M\rho(M))+H(\pi),
\qquad H(\text{full state}\mid\text{predictive state})=\log\kappa.}$$

The last equality follows because every fibre has kappa equal-mass states.
It measures task-irrelevant information under the stated source, not an
observer-independent physical entropy or a count of unknown WSS primes.

This source is positional digit generation. It is NOT the Bernoulli
arithmetic-successor kernel (1-a)Id+aT studied in RRO Section36. That
section's no-autonomous-finite-prefix-kernel theorem remains unchanged.
Here the finite state includes a modular accumulator and its clock, and
is proved sufficient for a different, explicitly finite arithmetic task.
The Parry source is also different from a uniform distribution on fixed-
length finite legal words, which has endpoint-conditioned probabilities.

### 7.6 WSS becomes a two-regime exact memory growth law

Let p>5 be prime and h_p=v_p(F_(p-(5/p))). The classical initial-depth
valuation formula and the exact rank imply

$$\rho(p^s)=\rho(p)p^{\max(0,s-h_p)}.$$

Indeed every zero index is a multiple of rho(p), and its Fibonacci
valuation is h_p plus the valuation of that multiplier. The least
positive multiplier attaining depth s is p^max(0,s-h_p). This reasoning
retains arbitrary actual h_p; it does not use Wall's conjectured growth.

**Corollary ZP5.** If K_s is the minimal number of LIVE divisibility
states at modulus p^s, then

$$\boxed{K_s=2\rho(p)p^{s+\max(0,s-h_p)},\qquad
\frac{K_{s+1}}{K_s}=\begin{cases}p,&s<h_p,\\p^2,&s\ge h_p.\end{cases}} \tag{ZP4}$$

In particular p is WSS if and only if K_2/K_1=p; for a non-WSS prime
the ratio is p^2. The stationary predictive entropy increases by log p
or2log p under the same two conditions. For p=7 the complete binary
counts at7 and49 are113 and5489, so the live-state ratio is49; for p=11
they are221 and26621, with live-state ratio121.

This is an exact operational realization of the original depth. It does
not independently constrain that depth: computing rho(p^2), or minimizing
the full exact reader, may already require the same initial arithmetic.
No faster WSS decision algorithm, original WSS witness or unbounded
exception/exclusion family is claimed. The autonomous-clock convention
is essential. If the current input position is given for free by an
external clock, one may update a residue and boundary with a time-dependent
transition using2M live states. That clock carries the missing arithmetic
phase; the autonomous lower bound must not be cited for the uncharged model.

### 7.7 Finite completion versus infinite-prefix topology

**Corollary ZP6.** No continuous map from the infinite legal digit space
K to the discrete set Z/M agrees with value modulo M on every finite
Zeckendorf word followed by zeroes. In fact any such extension is
continuous at no point. The analogous divisibility-valued extension
has the same property.

**Proof.** Fix any legal finite prefix. Its current consecutive row is
unimodular. After that prefix, ZP1 realizes every target final residue
by an actual legal finite continuation, and padding its high end with
zeroes gives a finite natural Zeckendorf row in the same cylinder.
Thus every nonempty cylinder contains finite rows of all M residues,
and contains both divisibility answers. A continuous map into a finite
discrete target would be constant on some cylinder about a continuity
point, a contradiction. This is compatible with a finite sequential
reader: the reader answers at a supplied finite termination. It does
not continuously decide an unterminated infinite input from a prefix.

This makes the link to the completed-future viewpoint concrete. A current
residue alone does not predict all continuations; the clock and boundary
must be retained until their task-preserving scalar quotient is taken.
Conversely, an infinite-prefix topology and a time-complete task interface
are different observations. The existing abstract predictive-memory
quotient does not by itself compute this arithmetic kernel; ZP1-ZP3 do.

### 7.8 Source and formalization boundary

The actual current sources inspected are ZeckendorfResidueTransducer,
PredictiveMemoryMinimalQuotient and the golden hard-core Markov discussion
in the contextual spacetime theory. The actual RRO Section36 proof from
#8335, mirrored by loning's #8397, and the temporal-query Section47 from
#8408 were read. Their successor, finite-prefix and time-query claims are
not silently replaced by the positional digit dynamics used here.

Relevant primary literature: E. Charlier, N. Rampersad, M. Rigo and
L. Waxweiler, *The minimal automaton recognizing mN in a linear numeration
system*, Integers11B(2011),A4, https://arxiv.org/abs/1008.1668 ;
D. Moradi, N. Rampersad and J. Shallit, *Complexity of Linear Subsequences
of Fibonacci-Automatic Sequences*, arXiv:2603.21645v1, Section2 and
Section3.2, https://arxiv.org/html/2603.21645v1 ; and I. Ben-Ari and
S. J. Miller, *A Probabilistic Approach to Generalized Zeckendorf
Decompositions*, https://arxiv.org/abs/1405.2379 . The last source's
finite-word conditioning is not identified with the stationary source ZP3.
The WSS rank-lifting input is the classical valuation formula recorded
by Medina-Rowland, https://arxiv.org/abs/0910.2907 .

Searches for least-significant-first Fibonacci divisibility, minimal
states, reversed input, and rank of apparition located the known
most-significant-first theorem and related automatic-sequence work.
They did not establish priority of the exact combined formulation above;
no first-ever mathematical claim or new externally solved open problem
is attached. Myhill-Nerode equivalence, finite Markov stationarity and
Fibonacci rank theory are classical. The contribution is the explicit
legal-word construction and the exact task-specific arithmetic quotient,
with its stated probability and WSS interfaces.

The new Lean/Scribe pair is `D5/S3/Arith/ZeckendorfFutureKernel.lean`
and its Blueprint companion. It proves legal coefficient saturation and
the full fixed-boundary future equivalence, rather than assuming that
all affine tests can be realized. It is a proof-script candidate pending
actual elaboration. The state-count, stationary-law, entropy and topology
results above are complete ordinary proofs and are not additional
kernel-certified declarations. No source or conclusion assumes h_p=1.
