# Fourth-to-second winding-cumulant bound for a unidirectional cycle

## 1. Cycle, current and normalized inverse rates

**Definition 1.1 (Clockwise cycle and winding count).** Let $N$ be any integer
with $N\geq2$. The phases are $1,\ldots,N$, with indices read cyclically.
At phase $i$ the process waits an exponential time of rate $k_i>0$ and then
jumps along the clockwise link $i\to i+1$. All holding times on successive
visits are independent. There are no counterclockwise links.
Mark the link $1\to2$ and let $W(t)$ count its crossings in $(0,t]$.
Starting immediately after a marked crossing makes $W(t)$ the number of
completed subsequent windings. Between consecutive marked crossings the
process visits every phase exactly once, so a winding time is distributed as

$$
T=E_1+\cdots+E_N,\qquad E_i\sim\operatorname{Exp}(k_i)
\quad\text{independently}.
$$

Transitions here are indexed by oriented cycle links. In particular, for
$N=2$ the forward links $1\to2$ and $2\to1$ are the two successive stages,
and only the first is marked. Subtracting their counts would measure bounded
endpoint displacement, not completed windings. For larger cycles the source
convention $\Pi_{21}-\Pi_{12}$ in [P, Section III E] reduces exactly to the
marked clockwise count because the reverse of the marked link has rate zero.
The cycle-link convention also gives the two-stage cycle without identifying
a forward link with a counterclockwise channel.

**Definition 1.2 (Scaled winding cumulants).** For real $z$ near zero, put

$$
\chi(z)=\lim_{t\to\infty}\frac{1}{t}\log\mathbb E[e^{zW(t)}],
\qquad C_j=\chi^{(j)}(0),\qquad K=\frac{C_4}{C_2}.
$$

The expectation may start in any fixed phase or any initial probability
law on the phases. The existence, analyticity and independence of the initial
law used in this definition follow in the proof of Theorem 2.1.
These are the long-time scaled current cumulants of [P, Section II]. Thus
$C_4$ subtracts three times the squared variance before division by time;
$K$ is neither a standardized fourth central moment nor $C_4/C_1$.

**Definition 1.3 (Inverse-rate moments).** For $j\geq1$ define

$$
a_i=k_i^{-1},\qquad R_j=\sum_{i=1}^N a_i^j,\qquad
x_i=\frac{a_i}{R_1},\qquad p_j=\sum_{i=1}^N x_i^j.
$$

Then $x_i>0$, $\sum_i x_i=1$, and $p_j=R_j/R_1^j$.
Conversely, every strictly positive vector with sum one occurs in this way:
take $k_i=1/x_i$. Thus this normalization loses no positive rate vectors.

## 2. Universal strict bound and sharp infimum

**Theorem 2.1 (All positive clockwise rates).** For every integer $N\geq2$
and every rate vector $(k_1,\ldots,k_N)\in(0,\infty)^N$ in Definition 1.1,

$$
\begin{aligned}
C_2&=\frac{R_2}{R_1^3},\\
C_4&=\frac{15R_2^3}{R_1^7}
       -\frac{20R_2R_3}{R_1^6}
       +\frac{6R_4}{R_1^5},\\
K&=\frac{15R_2^2}{R_1^4}
       -\frac{20R_3}{R_1^3}
       +\frac{6R_4}{R_1^2R_2}
   >c,\qquad c=-\frac{1+\sqrt5}{10}.
\end{aligned}
\tag{2.1}
$$

Moreover,

$$
\inf\left\{K(k_1,\ldots,k_N):
      N\in\mathbb Z,\ N\geq2,\ k_i>0\ \text{for all }i\right\}=c,
\tag{2.2}
$$

and no member of this set equals $c$. In particular, for every integer
$m\geq1$, the positive rates

$$
N=m+1,\qquad k_1=\frac{3-\sqrt5}{2m},\qquad
k_2=\cdots=k_{m+1}=1
\tag{2.3}
$$

satisfy $K\to c$ as $m\to\infty$.

The winding convention, renewal formulas and cumulant ratios in (2.1) are
supplied by [P, Sections II and III E and Appendix]. The constant $c$, the
one-slow-rate limiting construction and its scalar limiting optimization
are also supplied by [P, Section III E 1 and Appendix, Eq. (77)]. The choice
of denominator $m=N-1$ in (2.3) is asymptotically equivalent to the source's
$k_1\sim A/N$, $A=(3-\sqrt5)/2$. These are credited inputs, as are the
classical Cauchy–Schwarz and finite power-norm inequalities used below.
The repository-derived assertion relative to these suppliers is the
unconditional inference of $K>c$ for every finite positive rate vector,
without an extremal-topology hypothesis.

The relevant repository supplier [R] proves the sharp finite-$N$ minimum of
$C_3/C_1=3p_2^2-2p_3$. Its normalization and its private
`normalized_simplex`, `skewness_normalized`, `algebra_lower_bound`,
`simplex_lower_bound` and `attaining_rates` concern that third-cumulant
functional. They supply the simplex correspondence and the third-cumulant
comparison, rather than (2.1). In particular, its attaining normalized vector
has largest coordinate $1/2$, whereas the limiting vector in (2.3) has
largest coordinate $(5+\sqrt5)/10$. No assertion about the topology of
finite-$N$ fourth-cumulant minimizers is a premise of this theorem.

**Proof.** First identify the current and its cumulants, then prove the
inequality on the entire normalized rate domain, and finally establish
sharpness using (2.3).

For a winding time the Laplace transform and its logarithm are

$$
\widetilde w(s)=\mathbb E[e^{-sT}]
       =\prod_{i=1}^N\frac{k_i}{k_i+s},\qquad
F(s)=-\log\widetilde w(s)=\sum_{i=1}^N\log(1+a_i s),
\quad s>-\min_i k_i.
\tag{2.4}
$$

In particular, its ordinary cumulants are $(j-1)!R_j$. This is the
hypoexponential renewal input in [P, Appendix]; the following argument
also identifies its inverse relation with the original cycle current.
For the marked count the tilted backward generator acts on a vector $h$ by

$$
(L_z h)_i=k_i\big(e^{z\delta_i}h_{i+1}-h_i\big),
\qquad \delta_1=1,\quad \delta_i=0\ (i\ne1),\quad h_{N+1}=h_1.
\tag{2.5}
$$

Indeed, conditioning on the first jump gives
$u'(t)=L_z u(t)$ for $u_i(t)=\mathbb E_i[e^{zW(t)}]$, with
$u_i(0)=1$. This keeps one unit per winding, not one unit per stage.
For real $z$ near zero there is a unique $r>-\min_i k_i$ with

$$
F(r)=z,\qquad\text{equivalently}\qquad
\prod_{i=1}^N(1+a_i r)=e^z.
\tag{2.6}
$$

The function $F$ is strictly increasing on this interval, has limits
$-\infty$ and $+\infty$ at its two ends, and satisfies $F(0)=0$ and
$F'(0)=R_1>0$. Hence $r=r(z)$ is analytic near zero by the analytic
inverse function theorem. Choose $h_1=1$ and then set

$$
h_{i+1}=(1+a_i r)e^{-z\delta_i}h_i.
$$

All its entries are positive, and (2.6) makes the recursion cyclic. Equation
(2.5) gives $L_z h=rh$. Put
$\alpha=\min_i(1/h_i)>0$ and $\beta=\max_i(1/h_i)<\infty$.
The matrix $e^{tL_z}$ preserves coordinatewise nonnegativity: adding a
sufficiently large scalar multiple of the identity makes $L_z$ nonnegative,
and the exponential series then has nonnegative entries. Applying this
matrix to $\alpha h\leq\mathbf1\leq\beta h$ yields

$$
\alpha h_i e^{tr}\leq\mathbb E_i[e^{zW(t)}]
                \leq\beta h_i e^{tr}.
\tag{2.7}
$$

It follows that $\chi(z)=r(z)$, also for every initial mixture of phases.
Thus (2.6) is the current relation $F(\chi(z))=z$ for the actual cycle.
Marking a different clockwise link changes the count by at most one on
each path. The resulting exponential moments differ by factors between
$e^{-|z|}$ and $e^{|z|}$, so the scaled generating function is unchanged.
The count of all clockwise jumps $H(t)$ instead satisfies
$|H(t)-NW(t)|\leq N-1$; consequently its scaled generating function is
$\chi(Nz)$ and its fourth-to-second ratio is $N^2K$. That different
normalization is not used in (2.1).

For completeness, the derivatives of $\chi$ are also the limits of the
ordinary cumulants of $W(t)$ divided by $t$. Here one may use the classical
finite-state spectral argument underlying [P, Section II]: $e^{tL_0}$ has
strictly positive entries for $t>0$, since a path of positive probability
connects every pair of phases in that time. It is stochastic, so its
Perron eigenvalue $1$ is simple and all other eigenvalues have modulus
less than $1$. Thus $0$ is a simple eigenvalue of $L_0$, separated in real
part from all its other eigenvalues. Analytic perturbation of a simple
finite-matrix eigenvalue gives, uniformly in a complex neighborhood of
zero,

$$
\mathbb E[e^{zW(t)}]
 =e^{t r(z)}\big(b(z)+O(e^{-\eta t})\big),
 \qquad b(0)=1,\quad\eta>0,
\tag{2.8}
$$

after decreasing the neighborhood and $\eta$ if necessary. The coefficient
$b$ is analytic and nonzero there. Taking the local analytic logarithm,
dividing by $t$, and differentiating at zero proves the stated cumulant
limits; uniform analyticity justifies the differentiation. This also
shows explicitly why the initial law does not affect any $C_j$.

Expanding (2.4) near zero gives

$$
F(s)=R_1s-\frac{R_2}{2}s^2+\frac{R_3}{3}s^3
                  -\frac{R_4}{4}s^4+O(s^5).
$$

Successively differentiating $F(\chi(z))=z$ at zero therefore gives

$$
\begin{aligned}
R_1C_1&=1,\\
R_1C_2-R_2C_1^2&=0,\\
R_1C_3-3R_2C_1C_2+2R_3C_1^3&=0,\\
R_1C_4-R_2(4C_1C_3+3C_2^2)
       +12R_3C_1^2C_2-6R_4C_1^4&=0.
\end{aligned}
\tag{2.9}
$$

In particular $C_1=1/R_1$,
$C_3=3R_2^2/R_1^5-2R_3/R_1^4$, and solving the other two equations
produces the displayed $C_2$ and $C_4$ in (2.1), exactly as in [P, Appendix].
Since $R_1,R_2>0$, division by $C_2$ is legitimate and gives

$$
K=15p_2^2-20p_3+6\frac{p_4}{p_2}.
\tag{2.10}
$$

It remains to bound (2.10) for every $x_i>0$ with $\sum_i x_i=1$.
Write

$$
s=p_2,\qquad t=p_3,\qquad u=p_4,\qquad
q=\sqrt{s},\qquad v=\frac{t}{s}.
$$

These quantities come from the same vector $x$. The classical finite
Cauchy–Schwarz inequality applied to $(x_i)_i$ and $(x_i^2)_i$ gives

$$
t^2=\left(\sum_i x_i x_i^2\right)^2
       \leq\left(\sum_i x_i^2\right)\left(\sum_i x_i^4\right)=su.
\tag{2.11}
$$

Moreover $0<q<1$: the strict upper bound follows from
$1=(\sum_i x_i)^2=s+2\sum_{i<j}x_ix_j$ and $N\geq2$.
For every $i$, the other positive entries give $x_i^2<s$, hence
$x_i<q$. Multiplying by $x_i^2$ and summing yields the strict
power-norm comparison

$$
0<t<qs,\qquad 0<v<q,\qquad \frac{u}{s}\geq v^2.
\tag{2.12}
$$

Inserting (2.11) into (2.10) gives the universal two-moment estimate

$$
K\geq Q(q,v):=15q^4-20q^2v+6v^2.
\tag{2.13}
$$

If $0<q\leq3/5$, completion of the square gives

$$
Q(q,v)=6\left(v-\frac53q^2\right)^2-\frac53q^4
       \geq-\frac53\left(\frac35\right)^4=-\frac{27}{125}>c.
\tag{2.14}
$$

For the last strict comparison, $\sqrt5>2$ implies
$c<-3/10<-27/125$. Thus every vector in this case satisfies $K>c$.

If $3/5\leq q<1$, put $f(q)=15q^4-20q^3+6q^2$. Direct subtraction,
with the same $q$ and $v$ as in (2.12), gives

$$
Q(q,v)-f(q)
 =6(q-v)^2+4q(5q-3)(q-v)>0.
\tag{2.15}
$$

The square is strictly positive because $v<q$, and the other term is
nonnegative because $q\geq3/5$. To evaluate the remaining scalar bound,
let

$$
a=\frac{5-\sqrt5}{10},\qquad b=\frac{5+\sqrt5}{10}.
$$

The classical one-variable optimization already present in [P, Appendix]
can be written here as

$$
f'(q)=12q(5q^2-5q+1)=60q(q-a)(q-b).
\tag{2.16}
$$

Since $a<3/5<b<1$, this derivative is negative on $(3/5,b)$ and positive
on $(b,1)$. Hence $f(q)\geq f(b)$ on $[3/5,1]$.
Using $5b^2-5b+1=0$ gives

$$
f(b)=\frac25-b=-\frac{1+\sqrt5}{10}=c.
\tag{2.17}
$$

Equations (2.13), (2.15) and (2.17) prove $K>c$ also in this case,
including $q=3/5$. Together with (2.14), this proves the strict inequality
for all the quantified positive rate vectors. The argument has made no
assumption on how many distinct rates a minimizer could have.

Finally set $A=(3-\sqrt5)/2>0$. For (2.3), $a_1=m/A$ and the other
inverse rates equal $1$, so $R_1=m(1+1/A)$. Consequently

$$
x_1=\frac{1}{1+A}=b,\qquad
x_i=\frac{A}{m(1+A)}=\frac{1-b}{m}\quad(2\leq i\leq m+1),
$$

and the exact normalized moments are

$$
p_j=b^j+(1-b)^j m^{1-j}\quad(j\geq1).
\tag{2.18}
$$

For $j=2,3,4$ these tend respectively to $b^2,b^3,b^4$. Since
$b^2>0$, (2.10) and continuity of division at this limit give

$$
\lim_{m\to\infty}K
 =15b^4-20b^3+6b^2=f(b)=c.
\tag{2.19}
$$

This is exactly the supplied scalar limiting optimization: with
$q=1/(1+A)$, the source's expression
$(1-8A+6A^2)/(1+A)^4$ equals $f(q)$.
Every rate in (2.3) is positive and every $m+1\geq2$, so these are
members of the original admissible set, not merely formal moment triples.
The strict universal lower bound makes $c$ a lower bound of that set,
and (2.19) puts admissible values arbitrarily close to $c$.
This proves (2.2). The strictness already proved rules out attainment by
any finite $N$ and any positive rate vector. $\square$

## 3. Fixed-dimension boundary

**Definition 3.1 (The remaining fixed-dimension extremal problem).** For a
fixed integer $N\geq2$, let

$$
\begin{aligned}
\mathcal M_N&=\left\{
\left(\sum_{i=1}^N x_i^2,\sum_{i=1}^N x_i^3,\sum_{i=1}^N x_i^4\right):
 x_i>0,\ \sum_{i=1}^N x_i=1\right\},\\
\beta_N&=\inf_{(s,t,u)\in\mathcal M_N}
                 \left(15s^2-20t+\frac{6u}{s}\right).
\end{aligned}
$$

Theorem 2.1 determines the infimum over all $N$, rather than the exact
value or equality cases of $\beta_N$ for each fixed $N$. Its relaxation
uses $t^2\leq su$ and $t<s^{3/2}$; it does not characterize the entire
set $\mathcal M_N$. Determining $\beta_N$, the existence and form of its
minimizers, monotonicity in $N$, or a sharp finite-$N$ gap requires further
constraints on this common-vector moment set. No such classification or
finite-$N$ gap is asserted here.

The model in Definition 1.1 is essential to the cumulant reduction:
allowing counterclockwise transitions changes the winding-time law and
the tilted generator (2.5). Thus Theorem 2.1 is the unidirectional
lower-bound component only; it does not prove the complete bidirectional
interval asserted in [P, Eq. (22)]. Multicyclic networks, heat-weighted
currents, finite-time cumulants and standardized kurtosis are also outside
its hypotheses.

## 4. Mathematical citations and comparison of observables

[P] K. Ptaszyński, *Bounds on skewness and kurtosis of steady state currents*,
[arXiv:2204.08421v4](https://arxiv.org/abs/2204.08421v4), Sections II and
III E 1–2 and Appendix, especially Eq. (77); journal citation:
[Phys. Rev. E 106, 024119, DOI 10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119).
The citation and supplier comparison here concern the specified arXiv
version. The journal body is unavailable for this comparison; identity of
its proofs with the arXiv text and nonoverlap with its arguments remain
unverified. No additionality relative to that unread body is asserted.
In the arXiv argument, the topology with one exceptional rate is inferred
numerically before the scalar optimization; the unconditional
common-vector inference is (2.11)–(2.17).

[R] The repository's
[UnicyclicSkewnessMinimum](../../../D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.lean)
and its
[mathematical exposition](../../../Blueprint/D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.md),
with the corresponding
[Ptaszyński citation](../../../Library/StatisticalMechanics/ptaszynski2022skewness.md)
and [third-cumulant problem](../../../Problems/ptaszynski-2022-unicyclic-skewness-minimum.md).
Its complete result, including the private algebra and attaining-rate
suppliers named in Theorem 2.1, concerns $3p_2^2-2p_3$.
The distinct repository result
[BoundedKurtosisLimitRefutation](../../../D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.lean)
uses a probability law's standardized fourth central moment, with variance
squared in the denominator. That observable is not $K$ in Definition 1.2.

[B] A. C. Barato and U. Seifert, *Skewness and Kurtosis in Statistical Kinetics*,
[arXiv:1510.03279v1](https://arxiv.org/abs/1510.03279v1), Eqs. (5)–(6),
(12)–(13) and Supplemental Material, “Proof for $N=2$ and Numerical Evidence”;
[DOI 10.1103/PhysRevLett.115.188103](https://doi.org/10.1103/PhysRevLett.115.188103).
Its fourth-order observable is the standardized fourth central moment of
a cycle-completion time, $\mathbb E[(T-\mathbb ET)^4]/\operatorname{Var}(T)^2$,
not the fourth-to-second ratio of winding-count cumulant rates.

[W] Taylor Wampler and A. C. Barato, *Skewness and Kurtosis in Stochastic
Thermodynamics*, [arXiv:2110.14540v1](https://arxiv.org/abs/2110.14540v1),
Sections II B, III and IV C;
[DOI 10.1088/1751-8121/ac3b0c](https://doi.org/10.1088/1751-8121/ac3b0c).
Its kurtosis is a first-passage-time quantity $|J_t|\kappa_4/\kappa_2^2$.
The characteristic-polynomial relation between current and passage-time
generating functions does not identify that standardized observable with
$C_4/C_2$.

[G] *Random walks on modular chains: Detecting structure through statistics*,
[arXiv:2305.09759v1](https://arxiv.org/abs/2305.09759v1), Sections II–III,
especially the two-block rate specification and the fourth-cumulant formula
in Section III A 3;
[DOI 10.1103/PhysRevE.108.024135](https://doi.org/10.1103/PhysRevE.108.024135).
Its step-displacement cumulants on periodic two-rate chains require the
period-dependent current rescaling. Its specified rate families do not
supply the arbitrary-positive-rate inference in Theorem 2.1.

[H] *Critical heat current fluctuations in Curie-Weiss model in and out of
equilibrium*, [arXiv:2411.19643v3](https://arxiv.org/abs/2411.19643v3),
Sections III A and IV A;
[DOI 10.1103/PhysRevE.111.034125](https://doi.org/10.1103/PhysRevE.111.034125).
Its energy-weighted heat cumulants, normalized per spin, concern a
many-body critical limit and do not obey the phase-stage law (2.4).

[E] *Entropy Production in Mesoscopic Electronic Transport Beyond
Weak-Coupling*, [arXiv:2610.12652v1](https://arxiv.org/abs/2610.12652v1),
Sections II and III B. It uses $C_4/C_2$ for particle transfer, but its
single-channel transmission limit gives $1-6\tau+6\tau^2$ with
$0<\tau<1$, a different law and domain from (2.4).

[D] *Bounding Variance and Skewness of Fluctuations in Nonlinear Mesoscopic
Systems with Stochastic Thermodynamics*,
[arXiv:2208.14506v2](https://arxiv.org/abs/2208.14506v2), sections “White noise
processes,” “Local detailed balance and its consequences” and “Bounding the
Variance of Fluctuations”; and *Moments of Entropy Production in Dissipative
Devices*, [arXiv:2404.00422v1](https://arxiv.org/abs/2404.00422v1), the
local-detailed-balance moment construction and “Moments and cumulants of
white noise.” These constrain entropy-production moments and the first
three cumulant rates of thermodynamically consistent white noise with
independent increments. A multistage winding-count renewal process has
independent interarrival times, which does not make its increments on
disjoint fixed time intervals independent. Those hypotheses therefore do
not supply a fourth winding-cumulant bound for Definition 1.1.

## 追加锚（本行以下为增补区）
