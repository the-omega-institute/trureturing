---
bibkey: singh2004zeckendorfprobability
authors: Satinder Singh, Michael James and Matthew Rudary
year: 2004
title: "Predictive State Representations: A New Theory for Modeling Dynamical Systems"
doi: 10.48550/arXiv.1207.4167
url: https://arxiv.org/abs/1207.4167
claim: "The system-dynamics-matrix approach represents state through specified observable tests; its linear dimension must be distinguished from a deterministic state count."
strata_touched:
  - D5/S3/Arith/ZeckendorfTwoReadTomography
license: citation-only
triage: anchor
---

# Probability-state scope for the original Zeckendorf/WSS interface

Primary source inspected: the arXiv abstract and metadata for Singh, James
and Rudary, *Predictive State Representations: A New Theory for Modeling
Dynamical Systems*. The paper appeared at UAI2004; its arXiv deposit is2012.
The source introduces the system-dynamics matrix and predictions of
observable experimental outcomes. This note does not attribute our exact
Fibonacci rank formulas or two-read constructions to that paper. No theorem
number from its uninspected full text is asserted.

Related finite-ring Fourier background was checked through the author's
institutional publication records:

Andrew Kingston, *Orthogonal discrete Radon transform over p^n x p^n images*,
Signal Processing86(8)(2006),2040-2050, DOI10.1016/j.sigpro.2005.09.024.
https://researchportalplus.anu.edu.au/en/publications/orthogonal-discrete-radon-transform-over-psupnsup-psupnsup-images

The institutional abstract describes prime-power modular projections,
Fourier-slice structure, and redundancy at composite moduli. The restricted
full PDF was not used. Radon inversion and finite Fourier redundancy are
established mechanisms; they are not claimed as new. Our construction uses
only the projective Fibonacci orbit, rather than every projective direction.
Its exact conductor counts are proved in the existing golden-interface note.

For the probability source, Ben-Ari and Miller, *A Probabilistic Approach
to Generalized Zeckendorf Decompositions*, arXiv:1405.2379v2, identifies
uniform finite expansions with a conditioned Markov process. Its abstract
was inspected. This does not identify uniform finite-word sampling with
the stationary golden Markov source used in the repository.
https://arxiv.org/abs/1405.2379

## Results to which this source note is attached

The mathematical continuation belongs to Section8 of the EXISTING
`Library/notes/katz2015goldeninterfaces.md`, within the single WSS/Wieferich
problem family. No second problem entry is introduced.

It separates three tasks on the same finite arithmetic reader:

1. Distinguishing individual deterministic states by all legal suffixes.
2. Predicting one terminal divisibility answer from an unknown probability
   distribution on those states, for all legal suffixes.
3. Observing two non-destructive divisibility answers on the same trajectory.

The terminal response is closed under input updates but, in general, is
not sufficient for Bayes conditioning on an intermediate divisibility
answer. Two controlled, clock-restoring legal continuations give a joint
success event isolating each deterministic quotient state. This is a FAMILY
of two-read experiments. Two individual observed bits do not determine a
whole distribution. Estimating its probabilities needs repeated samples or
additional statistical assumptions. No quantum state-copying operation is
assumed.

Searches for Zeckendorf with Radon, divisibility with Hankel rank, and
prime-power modular projection redundancy did not establish global priority
for the combined formulation. The classical tools and the exact experiment
scope are retained. No new external open-problem resolution or integer WSS
prime is claimed by this note.

## TS. Written closure: the spectrum and stability of correlated Zeckendorf observations

This appendix continues Section 8 of `katz2015goldeninterfaces.md` in the
same Wieferich/WSS problem family. It has three connected aims: determine
all singular directions of the actual observation operator; decide whether
the two-read completion is stable; and distinguish input prediction from
conditioning on an actual recorded history. No new formal declaration or
independent problem entry is introduced.

The relevant draft sources actually read were #8170 at c0aa219e8d0fbce1ff41b28e77a539ac9eadc18e,
#8899 at e300b5df71f5ce08d857e8f2000a9e495813cdaf (the full mathematical patch,
especially Sections 3.5 and 5-6), and #8707 at
80cee065d80715c8493825531508cf5fa0ce9743 (the explicit finite-history law,
recorded-prefix sigma-algebra, and conditional-expectation statement).
The last is a macstudio-3 authored draft requesting loning's review; no
review approval is inferred from that request. The present arithmetic
proofs do not assume a quantum tensor factorization or a Gaussian prior.

### TS.1 The actual experiment and the norms being compared

Fix a prime p>5, s>=1, M=p^s, and a known incoming admissibility bit.
Let D_s be the projective classes of the actual consecutive Fibonacci
weight rows (F_(k+2),F_(k+3)) modulo M. Put R_j=rho(p^j) for 1<=j<=s,
R_0=1, and n_j=R_s/R_j. The fixed-boundary state space is
X_s=D_s x Z/M, of size M R_s. A state i=(d,r) uses the representative
v_d=(u_d,v_d). To avoid conflicting uses of v, vector notation v_d means
the whole row and its components are written u_d and v_d when needed.

Choose representatives canonically: if the first component is a unit,
make it one; otherwise make the second component one. Thus every row is
of form (1,a), or (p b,1). This choice commutes with reduction to every
p^j. It is a coordinate choice, not a change of the future equivalence.
For a coefficient query x=(A,B), set

$$a_i(x)=1_{r+v_d\cdot x=0}.$$

For k>=1 define the k-read all-success response on real signed masses by

$$({\cal T}_k\mu)(x_1,\ldots,x_k)
 =\sum_{i\in X_s}\mu_i\prod_{t=1}^k a_i(x_t). \tag{TS1}$$

For probabilities this is a JOINT probability on the same hidden initial
state. It is not the product of k marginal probabilities. Implement it
by the existing guarded legal-word compiler: first add x_1, then add
x_t-x_(t-1). Each word returns the weight clock; none resets the residue.
Add an all-zero clock cycle when positive spacing is required. Thus all
coefficient sequences in TS1 are actual admissible finite experiments.
The number of reads, the length of these words, and the number of
independent experimental repetitions remain separate resources.

Unless stated otherwise, both domain and range have counting Euclidean
norms. The equally weighted query norm is explicitly

$$\|g\|_{\rm av,k}^2=M^{-2k}\sum_{x_1,\ldots,x_k}|g(x_1,\ldots,x_k)|^2.$$

This normalization is essential for interpreting statistical sensitivity.

### TS.2 Intersections, shared hidden states, and the exact Gram operator

For rows d,e define their agreement depth t(d,e) as the greatest j<=s
such that they have the same reduction in D_j; put t(d,d)=s. For distinct
rows, t(d,e)<s. Reduction D_s -> D_j is onto with equal fibres n_j.
Indeed the determinant of clock rows at phases k,l equals a sign times
F_(k-l); its divisibility by p^j is equivalent to R_j dividing k-l.
Projective classes are precisely these phase classes, so their reduction
fibres have the asserted sizes. This uses the actual Fibonacci orbit,
not an arbitrary collection of independently chosen directions.

**Theorem TS1 (integer intersection and Gram identities).** Let

$$K_{(d,r),(e,r')}=\sum_{x\in(Z/M)^2}a_{(d,r)}(x)a_{(e,r')}(x).$$

For d=e this equals M if r=r', and zero otherwise. For d!=e,

$$K_{(d,r),(e,r')}=p^{t(d,e)}1_{r=r'\ ({\rm mod}\ p^{t(d,e)})}. \tag{TS2}$$

For every k>=1,

$${\cal T}_k^*{\cal T}_k=K^{\circ k}, \tag{TS3}$$

where the power is ENTRYWISE, not matrix multiplication.

**Proof.** At agreement depth zero the two row equations have unit
determinant, hence exactly one solution, for every r,r'. At positive
agreement depth both canonical rows have the same unit pivot. Eliminate
that coordinate from the two affine equations. The remaining coefficient
has valuation exactly t(d,e), so the scalar equation has p^t solutions
precisely when p^t divides r-r', and none otherwise. For one fixed row
there are M solutions when the right-hand sides agree. This proves TS2.
In the Gram entry for TS1, the k query variables are summed separately:

$$\sum_{x_1,\ldots,x_k}\prod_{t=1}^k a_i(x_t)a_{i'}(x_t)
 =\left(\sum_x a_i(x)a_{i'}(x)\right)^k.$$

It is the query design that separates in this calculation. The hidden
state remains the same in every factor. This proves TS3.

### TS.3 Complete singular spectrum at every read depth and prime power

Define, for 1<=l<=s,

$$\Delta_l^{(k)}=p^{(k-1)l}-p^{(k-1)(l-1)},\qquad
b_0=1,\quad b_j=(p-1)p^{j-1}R_j\ (j>=1).$$

**Theorem TS2 (all squared singular values, including their zeros).**
For every j=0,...,s there are b_j blocks, each of dimension n_j.
In each such block the spectrum of T_k^*T_k consists of

$$\lambda_{j,*}^{(k)}
 =M\left[p^{(k-1)j}n_j+
       \sum_{l=j+1}^s\Delta_l^{(k)}n_l\right] \tag{TS4}$$

once, and, for each l=j+1,...,s,

$$\lambda_l^{(k)}=M\sum_{a=l}^s\Delta_a^{(k)}n_a \tag{TS5}$$

with multiplicity

$$n_j/n_l-n_j/n_{l-1}=(R_l-R_{l-1})/R_j.$$

Zero multiplicities are omitted. Repeated numerical eigenvalues from
different blocks have their multiplicities added. This list has exactly
M R_s entries. The theorem is valid for real signed masses: complex
Fourier coordinates are only a diagonalizing calculation.

**Proof.** Use the unitary Fourier transform in each residue r. A mode
of additive order p^j is coupled to another row only if their agreement
depth is at least j. TS2 gives the matrix coefficient M p^((k-1)t).
The zero residue mode has one block on all rows. For j>=1, there are
(p-1)p^(j-1) such modes and R_j direction fibres, giving b_j blocks.

Inside a fibre of D_s -> D_j let B_l be the zero-one matrix for agreement
modulo p^l, j<=l<=s. In particular B_j is the all-ones matrix and B_s=I.
The block divided by M is exactly

$$p^{(k-1)j}B_j+\sum_{l=j+1}^s\Delta_l^{(k)}B_l. \tag{TS6}$$

The matrices P_l=B_l/n_l are orthogonal averaging projections. Their
ranges are nested, and P_l P_a=P_min(l,a). Thus the whole block decomposes
orthogonally into its constant line and the contrasts
range(P_l) intersect ker(P_(l-1)). The former gives TS4. A level-l
contrast is killed by every earlier averaging and is fixed by every
later averaging, giving TS5. Its dimension is n_j/n_l-n_j/n_(l-1).
These statements are direct finite sums on equal-size fibres; no general
spectral estimate is assumed. Finally

$$n_0+\sum_{j=1}^s b_jn_j
 =R_s\left(1+\sum_{j=1}^s(p-1)p^{j-1}\right)=MR_s.$$

Unitary conjugation preserves eigenvalues; since the original Gram
matrix is real symmetric, its real eigenvalue multiplicities are the
same. This completes the spectrum.

**Corollary TS3 (two reads are the exact algebraic completion threshold).**
For k=1 the rank is

$$1+\sum_{j=1}^s(p-1)p^{j-1}R_j,$$

recovering PT4. For every k>=2 the rank is the full M R_s. In particular
no third or later read can add an identifiable linear direction to the
complete two-read experiment family.

**Proof.** At k=1 every Delta is zero, so only each block's constant
line survives. At k>=2 every Delta is positive, and every block includes
the positive diagonal term Delta_s I. Thus all eigenvalues are positive.
Since R_1>1 for the original p>5 Fibonacci problem, the one-read zero-mode
block has a nontrivial kernel, so the threshold is genuinely two.

This concerns linear identifiability of the ENTIRE experiment family.
It does not say that two observed bits reveal a distribution, or that
additional reads have no benefit for estimation under a fixed budget.

### TS.4 A stable inverse with exact extremal constants

Let h=h_p be the actual original Fibonacci initial depth and R=R_1.
Set H=min(s,h) and b=max(0,s-h). The standard rank formula is
R_j=R p^max(0,j-h); equivalently n_j=p^(b-max(0,j-h)) for j>=1.
This is used with h arbitrary, including h>=2.

**Theorem TS4 (two-read extremal eigenvalues).** For counting norms,

$$\lambda_{\max}({\cal T}_2^*{\cal T}_2)
 =M^2\left[1+(R-1)/p^H+b(1-1/p)\right], \tag{TS7}$$

and

$$\lambda_{\min}({\cal T}_2^*{\cal T}_2)=
\begin{cases}
M^2-M,&s<=h,\\
M^2(1-1/p),&s>h.
\end{cases} \tag{TS8}$$

Both are attained. Consequently, without knowing which case holds,

$$\boxed{
\|{\cal T}_2\delta\|_{\rm av,2}^2
 \ge\frac{1-1/p}{M^2}\|\delta\|_2^2
}\quad\text{for every real signed mass }\delta. \tag{TS9}$$

**Proof.** The zero-frequency constant eigenvalue in TS4 dominates all
other eigenvalues, since n_l is nonincreasing. At k=2 it is
M[R_s+sum_(l=1..s)(p^l-p^(l-1))n_l]. Substituting the displayed n_l
and summing below and above H gives TS7.

If s<=h, different direction rows already differ modulo p and there
is no further branching. The zero-frequency block is
(M^2-M)I+M times the all-ones matrix; every nonzero frequency has
eigenvalue M^2. Because R>1, the row-constant contrast eigenvalue
M^2-M is attained and is minimal. If s>h, the last direction level
branches. Every block is bounded below by
M(p^s-p^(s-1))I, and a last-level contrast attains this bound. This
proves TS8. Dividing by M^4 for the explicitly uniform query norm gives
TS9. The constants thus have no uncharged normalization factor.

The whole response table admits a constructive inverse: Fourier transform
in residue, take the nested fibre averages and their differences from
TS6, divide each component by TS4 or TS5, and transform back after
applying T_2^*. These are finite explicitly specified operations, but
acquiring a full table with M^4 query pairs is not claimed inexpensive.

For arbitrary additive table error e, the least-squares inverse satisfies

$$\|\widehat\mu-\mu\|_2
 \le\frac{M}{\sqrt{1-1/p}}\|e\|_{\rm av,2}. \tag{TS10}$$

Projection of the recovered vector onto the probability simplex cannot
increase this Euclidean error. A total-variation consequence incurs the
additional factor sqrt(MR_s)/2, by the finite l1-l2 comparison. Thus the
bound is neither dimension-free statistical recovery nor a sample count.

For M=7 the two-read Gram spectrum is
42 with multiplicity7, 49 with multiplicity48, and98 once. At M=49,
with the actual rho(7)=8, rho(49)=56, the extremal eigenvalues are2058
and6860. The original depths in these examples are one; neither is WSS.

### TS.5 The full recorded-history law with calibrated readout noise

The preceding definition idealizes each divisibility reading as exact
and non-destructive. Now specify independent binary readout flips with
known probabilities eta_1,eta_2 in [0,1/2], which do NOT alter the hidden
arithmetic state. The errors are conditionally independent given the
state and chosen queries. Write alpha_i=1-2eta_i.

At two absolute coefficient queries x,y, the ideal conditional record
probabilities for a mass-one mu are

$$(P_{11},P_{10},P_{01},P_{00})
 =(g,f(x)-g,f(y)-g,1-f(x)-f(y)+g),\quad
 g=({\cal T}_2\mu)(x,y). \tag{TS11}$$

The observed law is the tensor action of the two binary flip matrices
on this FOUR-OUTCOME record. It is not a tensor product of the unknown
marginal outcome distributions. Average the squared Euclidean norm of
this four-vector uniformly over x,y, and call the resulting norm av,rec.

**Theorem TS5 (noisy identifiability and a quantitative bound).** If
alpha_1 alpha_2 !=0, the complete noisy two-read family determines mu,
and for any real signed mass delta its response C_eta satisfies

$$\boxed{
\|{\cal C}_{\eta}\delta\|_{\rm av,rec}^2
 \ge\alpha_1^2\alpha_2^2\frac{1-1/p}{M^2}\|\delta\|_2^2.
} \tag{TS12}$$

Its linear rank is M R_s. If precisely one alpha_i vanishes, the rank
is the one-terminal rank L_s. If both vanish, the rank is one, retaining
only total mass. These last assertions concern this specified two-slot
experiment family, not all possible later reuse of a working sensor.

**Proof.** Each binary flip matrix is real symmetric with eigenvalues
1 and alpha_i. Its tensor product therefore has smallest singular
value |alpha_1 alpha_2|. The ideal four-outcome response includes its
11 component T_2 delta, so TS9 gives TS12. Invertibility gives the
same rank as the ideal full record, namely M R_s. If one sensor is
completely fair, its output is an independent fair bit and the remaining
law contains precisely the other one-terminal prediction. If both are
fair the record is uniform regardless of hidden state. This proves the
rank assertions, including the normalization coordinate.

An explicit unbiased statistic is

$$\mathbb E\left[
 \frac{(Y_1-\eta_1)(Y_2-\eta_2)}{\alpha_1\alpha_2}
 \mid x,y\right]=({\cal T}_2\mu)(x,y). \tag{TS13}$$

This follows by conditioning first on the true two bits. It requires
calibrated flip probabilities and conditional independence of the
readout noise. At nearly fair noise its variance can be large. A formal
inverse or a positive singular value alone does not grant inexpensive
sampling. Unknown calibration is outside this theorem.

For an adaptive sequence of queries, the actual likelihood at hidden
state i is the product of the successive Bernoulli factors with success
probability eta_t+(1-2eta_t)a_i(x_t(history)). For every fixed history
these are known nonnegative kernels summing to one. Multiplying by mu_i
and summing over i gives the recorded-history law and all its marginals.
At a history of positive mass, posterior mu is its normalized
likelihood-weighted initial law. At a null history no conditional law is
claimed. This is the explicit arithmetic instance of the history-law
scope read in #8707, with the hidden coordinate omitted from the observer's
record. Repeating experiments from a newly sampled prior is an additional
preparation resource; it is not inferred from this single-trajectory law.

### TS.6 Input closure and Bayesian closure are different algebraic tests

**Theorem TS6 (necessity of the full probability state for the enlarged task).**
Suppose a statistic S(mu) provides every permitted one-terminal prediction
and has an exact updater after every controlled read with positive
probability, so the same predictions can be computed after conditioning.
Then S is injective on the probability simplex over X_s. If calibrated
nonfair sensor noise is included, the same conclusion holds when both
slots of the allowed two-read family remain informative.

**Proof.** From S(mu) one obtains the first outcome probability, updates
on each positive-probability outcome, and obtains the second conditional
probability. Their product gives the corresponding joint probability;
a zero first probability gives joint probability zero without conditioning
on a null event. Thus S determines the complete two-read record law.
TS3 or TS5 then determines mu. Hence two distinct priors cannot share S.

For the noiseless language, the same result can be seen directly through
observable functions: the single-test span W_1 has dimension L_s, while
W_2=span{a_i(x)a_i(y) as functions of i} is the entire function space by
TS3. Conditioning introduces multiplication by the recorded-event
indicator, so W_1 is generally not invariant under that operation. The
actual controlled input pullbacks alone preserve W_1, as PT2 proved.
The arithmetic closure reaches the full function space at degree two.
Higher read degree adds no new linear directions, though it can change
statistical efficiency and admissible experimental designs.

There is a separate stability condition for conditioning itself. For a
fixed recorded event with likelihood ell_i in [0,1], let a=sum_i mu_i ell_i
and b=sum_i nu_i ell_i, both positive. With the half-l1 convention,

$$\|\mu(\cdot\mid E)-\nu(\cdot\mid E)\|_{\rm TV}
 \le\frac{\|\mu-\nu\|_{\rm TV}}{\max(a,b)}. \tag{TS15}$$

To prove it, assume a>=b and put P=sum_i ell_i(mu_i-nu_i)_+ and
N=sum_i ell_i(nu_i-mu_i)_+. The normalization triangle bound is
(P+N+|a-b|)/(2a)=P/a, since a-b=P-N. Moreover P is at most the prior
total variation. The other order is symmetric. Consequently a lower
bound on the recorded-event probability is needed for a uniform
posterior error guarantee, even after stable initial-state recovery.
This dependence is attained in the actual arithmetic state space: for
two directions d!=e, take priors
(1-epsilon)delta_(d,1)+epsilon delta_(d,0) and
(1-epsilon)delta_(d,1)+epsilon delta_(e,0), with 0<epsilon<1.
Their prior distance is epsilon, and the initial zero-residue event has
probability epsilon under both. Conditioning gives two distinct point
states of distance one. This is an ordinary exact-read example, not a
claim that calibrated noisy observations have a zero likelihood floor.

This is not a lower bound on arbitrary discontinuous real encodings.
It states precisely which priors an exact sufficient statistic may
identify. The companion result in #8899 similarly distinguishes a closed
linear observation space from a full observable algebra and uses the
Gramian spectrum, rather than rank alone, for noisy recovery. Our finite
classical indicator multiplication is not noncommutative quantum
measurement, and TS12 is not a Gaussian short-time or thermodynamic law.

### TS.7 Consequence for the original WSS scale, and the missing arithmetic

At s=2, the least two-read Gram eigenvalue is

$$\lambda_{\min}=
\begin{cases}
p^4-p^3,&h_p=1,\\
p^4-p^2,&h_p>=2.
\end{cases} \tag{TS14}$$

The largest eigenvalue is p^4[2+(rho(p)-2)/p] in the first case, and
p^4+p^2(rho(p)-1) in the second. These are spectral realizations of
the same actual rank-lifting breakpoint. The lower recovery estimate
TS9, in contrast, works uniformly for either breakpoint.

There is no contradiction: uniform stability compares perturbations
WITHIN the already specified experiment and state space. It does not
prove the dimension R_2, or determine which experiment the original
Fibonacci arithmetic produces. Estimating these spectra may itself
require the same rho(p^2) information. No new original WSS prime,
unbounded prime-family exclusion, or improved WSS-search complexity
follows from TS14. The completed problem here is noisy identifiability
and its exact finite-ring spectrum, not the integer existence question.

### TS.8 Literature roles and written-proof status

The old note's source statements are retained. Additional primary context:
Alex Kulesza, Nan Jiang and Satinder Singh, *Spectral Learning of Predictive
State Representations with Insufficient Statistics*, AAAI2015,
https://ojs.aaai.org/index.php/AAAI/article/view/9635 . Its abstract concerns
the consequential choice of insufficient tests and histories; no exact
Fibonacci spectrum is attributed to it. Kingston's2006 institutional
abstract was rechecked at https://openresearch-repository.anu.edu.au/items/e23345f6-0022-40d0-acad-744e20e4d5a1 .
It supplies prime-power Radon and redundancy background, not a proof of
the repeated-same-state Hadamard-power spectrum given here.

The classical mechanisms used here are finite Fourier orthogonality,
nested conditional averages, Gram matrices, and calibrated binary
channels. The full TS1-TS15 derivation is written explicitly above.
Bounded searches of finite Radon spectra, prime-power incidence matrices,
Hjelmslev eigenvalues and predictive-state identifiability did not establish
a prior statement of this exact combined Fibonacci-family theorem. They
also do not establish worldwide novelty. No externally posed conjecture
is declared solved, and no new Lean/Scribe or kernel status is attached.
This is a written-theory continuation for later independent review.
