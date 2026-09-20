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

## 8. Probability-state completion: terminal rank and two-read tomography

Section7 classified individual deterministic states. It did not assert
that mixtures on those distinct states have different future laws. This
section computes the additional probability kernel and proves that a family
of TWO successive arithmetic readings removes it. The number of readings
per specified experiment is separated from the number of experiments,
word lengths, and statistical samples needed to learn their probabilities.

### 8.1 The exact terminal response and its closed input update

Fix M=p^s with p prime and s>=1, and a known incoming digit boundary.
Let D_s be the projective Fibonacci orbit: the distinct unit-scaling
classes of rows (F_(k+2),F_(k+3)) modulo M. Choose a unimodular representative
v_d=(u_d,v_d) for each d, scaling the accumulated residue at the same time.
Write R_s=rho(p^s). By ZP2-ZP3, |D_s|=R_s and the fixed-boundary live
quotient states are (d,r), d in D_s and r in Z/M. There are M R_s of them.
Only in formulas where it is unambiguous, v_d denotes the entire row.

Let mu(d,r) be a real signed mass, with total S. For probabilities S=1.
Define its one-terminal response table

$$f_\mu(A,B)=\sum_{d\in D_s}\mu(d,-A u_d-B v_d). \tag{PT1}$$

This is the probability that the actual residue is zero after a word with
coefficient pair (A,B). Every such pair is implemented by the guarded legal
words of ZP1, and every legal word has some pair. Thus equality of PT1 is
EXACTLY equality of all single-terminal acceptance predictions at this
fixed boundary. For the specified golden Markov input source, equality is
also equality of the joint word-and-terminal-answer laws: each legal word
has the same known positive input probability for both initial mixtures.
This statement includes no intermediate divisibility measurement.

**Theorem PT1.** After consuming an allowed bit b in {0,1}, the response
of the pushed-forward mass satisfies

$$\boxed{f_{\mu^+}(A,B)=f_\mu(b+B,A+B).} \tag{PT2}$$

The new boundary is b, and the terminal acceptance probability is
f_mu(0,0). The response table is therefore a closed predictive state for
this single-terminal task, with an explicitly invertible affine pullback.

**Proof.** The actual update sends (r,u,v) to (r+b u,v,u+v). Substituting
in the next test gives r+(b+B)u+(A+B)v. Summing its indicator against the
original mass proves PT2. Selecting other projective representatives only
scales the whole equality by a unit and does not change its zero set.
Illegal input is handled by the known boundary and the rejecting state.
No hidden-state reconstruction is assumed in this update.

### 8.2 All prime-power probability blind directions

For a row mass write its unnormalized finite Fourier transform as

$$\widehat\mu_d(t)=\sum_{r\bmod M}\mu(d,r)e_M(tr),\qquad
 e_M(x)=\exp(2\pi i x/M).$$

Use the normalized two-dimensional transform

$$\widehat f(\xi)=M^{-2}\sum_{A,B\bmod M}f(A,B)e_M(-\xi\cdot(A,B)).$$

**Theorem PT2.** The full terminal kernel has the exact description

$$\boxed{\widehat f_\mu(\xi)=\frac1M
 \sum_{\substack{d\in D_s,\ t\bmod M\\t v_d=\xi}}\widehat\mu_d(t).} \tag{PT3}$$

Its real linear rank is

$$\boxed{L_s=1+\sum_{j=1}^s(p-1)p^{j-1}\rho(p^j).} \tag{PT4}$$

Consequently the invisible signed subspace has dimension M R_s-L_s.
The image of the probability simplex has affine dimension L_s-1.
This is a linear/affine dimension, not a number of classical states or a
lower bound on arbitrary discontinuous encodings into real numbers.

**Proof.** Fourier inversion of each row mass at -v_d dot (A,B) gives
M^(-1) sum_t muhat_d(t)e_M(t v_d dot (A,B)). Character orthogonality gives
PT3. At frequency zero, t=0 for every unimodular row, so fhat(0)=S/M.

A nonzero frequency of additive order p^j has the unique form
p^(s-j) eta, with eta primitive modulo p^j. It lies on a row's Fourier
line exactly when that row reduces to the projective class of eta modulo
p^j. The actual projective orbit reduces ONTO D_j. To see its size and
fibres directly, the determinant of two clock rows with index difference
a is plus or minus F_a. Vanishing modulo p^j is therefore equivalent to
rho(p^j)|a. Its reduction fibres have size R_s/rho(p^j). Each direction
in D_j contains exactly (p-1)p^(j-1) primitive vector representatives,
and these representatives are disjoint for distinct directions. Counting
by j, together with zero, gives PT4.

Each coordinate muhat_d(t) occurs in exactly one output sum in PT3.
Every output frequency in the counted set has a nonempty preimage.
The map is therefore onto all these Fourier coordinates over C, with
one independent equation per coordinate for its kernel. Its original
matrix has real entries, so real and complex ranks agree. Conjugate
symmetry gives the same real dimension directly. The total mass is
recovered from fhat(0), and the positive simplex has nonempty relative
interior in its mass-one hyperplane. Its image consequently has affine
dimension L_s-1, as stated. The probability constraint does not remove
the linear blind directions near a strictly positive prior.

PT3 retains every sum over coincident low-conductor directions. Replacing
it by separate equations muhat_d(t)=0 would incorrectly discard those
cancellations when different directions coincide modulo a lower p-power.

### 8.3 At prime precision: a constructive inverse and a stability identity

For M=p let m_d=sum_r mu(d,r). Distinct projective directions have
nonzero determinant over F_p. Put

$$\mathcal L_{d,r}=\{(A,B):A u_d+B v_d=-r\}.$$

**Theorem PT3.** The centered row probabilities are reconstructed by

$$\boxed{\mu(d,r)-m_d/p=
 \frac1p\sum_{(A,B)\in\mathcal L_{d,r}} f_\mu(A,B)-S/p.} \tag{PT5}$$

In particular, two probability laws mu,nu have all the same one-terminal
responses if and only if mu(d,r)-nu(d,r) is constant in r for every d,
and these row constants have zero total mass across d. At prime precision
L_1=1+rho(p)(p-1), and the blind dimension is rho(p)-1.

**Proof.** On the indicated line, the d-th summand is constantly mu(d,r).
For every other direction e, its linear form is bijective from that line
to F_p, because the determinant is nonzero. Summing that term along the
line therefore gives m_e. The entire line sum is
p mu(d,r)+S-m_d, proving PT5 and the kernel assertion.

For equal-total-mass signed mu,nu, let

$$b_d(r)=\mu(d,r)-\nu(d,r)-(m_d^\mu-m_d^\nu)/p.$$

Their centered rows have zero sums. Uniform (A,B) makes linear readings
in two distinct directions independent and uniform, so cross terms vanish.
Expanding the square yields the exact stability identity

$$\boxed{\frac1{p^2}\sum_{A,B}|f_\mu-f_\nu|^2
 =\frac1p\sum_{d,r}|b_d(r)|^2.} \tag{PT6}$$

This controls the observable centered component. It supplies no recovery
of the invisible row totals. It is a finite linear-algebra statement;
physical measurement noise and how the response table is estimated must
be specified separately.

### 8.4 Two same-trajectory reads recover the entire probability law

We now ENLARGE the task by permitting two exact, non-destructive tests of
whether the current residue is zero, on the same arithmetic run. Between
them the reader consumes a chosen guarded word. Returning the weight clock
by a word of length divisible by T is not a reset of the accumulated residue
or of the hidden initial state. The two tests are correlated observations.

**Theorem PT4.** For every modulus M>=2 and each fixed-boundary quotient
state (d,r), there is a specified pair of legal clock-restoring probes whose
joint success indicator is exactly the point indicator of (d,r). Hence the
FAMILY of these two-read experiments determines every mass mu(d,r), including
for composite M. The span of their joint-success functions is the entire
function space on the M rho(M) fixed-boundary states.

**Proof.** Choose e,f with eu_d+fv_d=1, and set

$$x=(-re,-rf),\qquad y=(v_d,-u_d). \tag{PT7}$$

Implement x by ZP1, read Y_1, implement y by ZP1 from the returned clock,
and read Y_2. For a candidate state (d',r'), joint success means

$$r'+x\cdot v_{d'}=0,\qquad r'+(x+y)\cdot v_{d'}=0.$$

Subtracting gives v_d u_(d')-u_d v_(d')=0. Two unimodular rows with zero
determinant over Z/M are unit-proportional: with a=e u_(d')+f v_(d'),
the Bezout relation gives v_(d')=a v_d, and a has an inverse because the
second row is unimodular. Thus d'=d as projective classes. With the chosen
representative fixed, the first equation then says r'=r. Conversely the
target clearly makes both equations zero. Therefore

$$\boxed{\Pr_\mu(Y_1=1,Y_2=1\mid x,y)=\mu(d,r).} \tag{PT8}$$

Both guarded words are explicit finite legal words from ZP1. Each has
length at most4T(M-1); adding0^T when necessary ensures positive separation
between reads and boundary zero while leaving residue and clock unchanged.
Thus no unimplemented arbitrary affine oracle is being introduced.
Their point indicators prove the asserted full span and injectivity.
This is not a claim that two observed bits reveal an arbitrary distribution:
there is one designed experiment for each target, and its probability
requires repeated samples or other specified statistical information.

**Corollary.** The one-terminal response state PT1 is generally NOT closed
under conditioning on an intermediate divisibility answer. Input-update
closure PT2 and Bayesian posterior closure are distinct requirements.

**Proof by actual probability laws.** Fix two different projective directions
d,e, and take a uniform residue r in each, with known boundary zero. Both
laws give f(A,B)=1/M for every terminal query. Conditional on the initial
zero test succeeding, they instead become the distinct point states (d,0)
and (e,0). A subsequent tangent probe from PT7 distinguishes them. Thus no
posterior updater using only the common response table and the observed
zero answer can produce all the correct subsequent predictions. This does
not contradict ZP4, whose equivalence concerns individual initial states,
or the general predictive-state representation theory with its FULL joint
experiment family.

At M=7, the actual initial clock rows have projective representatives
(1,2) and (1,5). Use the two tests with x=(0,0), y=(2,-1). Under the first
uniform-residue law, the joint distribution has masses1/7 at11 and6/7 at00.
Under the second, it has masses1/7 at10 and01 and5/7 at00. Both individual
read marginals are Bernoulli(1/7), but the joint laws differ.

### 8.5 The observation budget is not the algebraic rank

For the preceding two-direction uniform-residue example at M>=3, the
joint total-variation distance is exactly2/M, where total variation has
its one-half-L1 convention. With equal prior odds and n INDEPENDENT
repetitions of this specified two-read experiment, the optimal Bayes
error is

$$\boxed{\frac12(1-2/M)^n.} \tag{PT9}$$

**Proof.** Choose a tangent to the first direction, which is not a tangent
to the second. The first law only produces11 or00; the second only10,01,
or00. Every record containing a non-00 trial identifies its law. The sole
common n-trial record is all00, whose masses are (1-1/M)^n and (1-2/M)^n.
The binary Bayes overlap formula gives PT9. The common-record calculation
also gives distance2/M when n=1. Fixed small Bayes error therefore requires
order M repetitions for this pair, despite having only two reads per run.
This is the exact risk for this specified experiment, not a minimax claim
over all adaptive protocols or arbitrary preparations.

If the input words are generated passively by the golden Markov source,
the same identifying words have positive probability but can be rare.
Dividing their joint event probability by their known word probability
recovers PT8 in principle; no uniform sample-efficiency claim follows.
Neither an independent-copy assumption nor a reset operation is silently
added to the repository's single-nonresettable-trajectory observation model.

### 8.6 Original WSS depth in linear probability dimension

For p>5 write R=rho(p), h=h_p and let L_0=1. Applying the classical
rank-depth formula of Section7 to PT4 gives

$$\boxed{L_s=1+R(p-1)\sum_{j=1}^s
 p^{j-1+\max(0,j-h)}.} \tag{PT10}$$

For s<=h this is1+R(p^s-1). For s>h it is

$$1+R(p^h-1)+\frac{R p^{h+1}(p^{2(s-h)}-1)}{p+1}.$$

The increments obey

$$\boxed{\frac{L_{s+1}-L_s}{L_s-L_{s-1}}=
\begin{cases}p,&s<h,\\p^2,&s\ge h.\end{cases}} \tag{PT11}$$

At the decisive square scale,

$$L_2=\begin{cases}
1+R(p-1)(1+p^2),&h=1,\\
1+R(p^2-1),&h\ge2.
\end{cases}$$

Thus the single-terminal probability rank and the deterministic state
count are different arithmetic invariants, although both retain the same
initial-depth breakpoint. For p=7, the fixed-boundary state counts at7 and49
are56 and2744, but the terminal ranks are49 and2401; the invisible signed
dimensions are7 and343. For p=11 the prime-level counts are110 and101,
respectively. These are dimensions of a response matrix, not numbers of
samples and not quantum Hilbert-space dimensions.

PT10 is an exact reformulation, not a new bound on h_p. Neither the rank
calculation nor the two-read identity forces a prime with h_p>=2. Tests on
composite prime powers do not create WSS examples. New arithmetic progress
would require independent control of the actual response rank or its
correlated point probabilities as p varies, without assuming the unknown
rank-lifting breakpoint. No new WSS occurrence or unbounded exclusion
family is concluded here.

### 8.7 Research and formalization scope

This continues the current spacetime work on task-relative state,
probability, joint observations and finite-word Zeckendorf arithmetic.
It adds an explicit response operator, the complete conductor-layer kernel,
a prime-level stable inverse, and a two-read family recovering all masses.
It does not identify positional digit generation with the arithmetic
successor or its binomial mixing law. The abstract future-quotient theorem
alone does not compute this probability kernel or guarantee Bayesian closure.

Primary source roles are recorded in
`Library/notes/singh2004zeckendorfprobability.md`: Singh-James-Rudary,
UAI2004, arXiv:1207.4167, for predictive-state/system-dynamics-matrix scope;
Kingston, Signal Processing86(2006),2040-2050,
DOI10.1016/j.sigpro.2005.09.024, for established prime-power Radon/Fourier
redundancy; and Ben-Ari-Miller, arXiv:1405.2379, for conditioned finite-word
probability models. The exact arithmetic proofs above are supplied here.
The inspected abstracts do not establish priority for our combined result.

The formal companion `ZeckendorfTwoReadTomography` certifies the explicit
modular two-test separating event and its finite-mass reconstruction. The
literal word implementation is justified by the earlier guarded compiler
and the ordinary composition proof in PT4. The Fourier rank, affine image
dimension, prime inverse, sampling risk and WSS formulas remain ordinary
proofs rather than additional claims of kernel certification. No new
external open problem is marked resolved and no new problem entry is opened.
