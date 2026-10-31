# Relational observation on the literal FIB source: clock, entropy and retained memory

## 1. The common source and the native path target

**Convention 1.1 (objects and precision).** Put

$$
\phi=\frac{1+\sqrt5}{2},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
e=\binom10,
$$

$$
\Omega_F=\{\xi\in\{0,1\}^{\mathbb N}:\xi_j\xi_{j+1}=0\},
\qquad G=\widehat{\mathbb Z}^{2},\qquad K=\Omega_F\times G.
$$

The topology and Borel structure are those of the literal joint completion in
[FIB source §§2–5][FIB]. Its forward operation is the original total peel

$$
\delta(\xi,z)=\bigl(\sigma\xi,M^{-1}(z-\xi_0e)\bigr).
\tag{1.1}
$$

For a finite word $w=w_0\cdots w_{n-1}$, let

$$
t_w=\sum_{j<n}w_jM^je,\qquad
h_w(\eta,v)=(w\eta,t_w+M^nv).
\tag{1.2}
$$

The map $h_w$ is used only when $w\eta$ is legal. The source formula is

$$
\delta^n(\xi,z)
=\bigl(\sigma^n\xi,M^{-n}(z-t_{\xi|_n})\bigr).
\tag{1.3}
$$

In particular, each fibre of $\delta^n$ is finite, indexed by compatible legal
words of length $n$. There is no new shift or inverse oracle in this notation.
All logarithms below are natural. Entropy means the supremum of entropy rates
of finite measurable partitions, with the invariant probability explicitly
specified; it is not differential entropy or a static information capacity.

Let $\mu_H$ be normalized Haar probability on $G$, $\nu_P$ the one-sided Parry
probability of the golden-mean shift, and

$$
\lambda=\nu_P\otimes\mu_H,\qquad
\mu_0=\delta_{0^\infty}\otimes\mu_H.
\tag{1.4}
$$

Both probabilities are $\delta$-invariant. For $\lambda$ this is FIB 9.2;
for $\mu_0$, (1.1) reduces to the Haar-preserving automorphism $M^{-1}$.
FIB 9.8–9.10 gives, for every invariant Borel probability $\rho$ on $K$,

$$
h_\rho(\delta)=h_{\rho_{\rm sym}}(\sigma)\le\log\phi,
\qquad h_\lambda(\delta)=\log\phi,
\qquad h_{\mu_0}(\delta)=0.
\tag{1.5}
$$

The actual finite-source graph remains

$$
\Gamma=\{(b,\iota(x(b))): b\text{ is legal and eventually zero}\}.
\tag{1.6}
$$

It is a countable dense proper subset of $K$, rather than a replacement for $K$.

**Definition 1.2 (the retained native target).** The target is the original
program $\mathsf T(1^{10n})$ from its unique ready state, for every $n\ge1$,
under [III145.1–145.2 and III183–185][III]. Its configuration carrier is the
entire original set $E$, $|E|=89$. Write $q_0=q_{\rm r}$ and $q_1$ for the two
configurations in III183.1. Only these two are visited in this program; the
other $87$ configurations remain in the carrier. Put

$$
a=4\phi^{-3}\in(0,1),\qquad
\alpha=3\pi/5,\qquad P=2\pi/\alpha=10/3.
\tag{1.7}
$$

III183.2 supplies an iid sequence of cycle marks with space and probability

$$
\mathcal M=\{\star\}\sqcup(0,1)^2,\qquad
\vartheta=(1-a)\delta_\star+a\operatorname{Leb}_{(0,1)^2}.
\tag{1.8}
$$

The mark $\star$ means no jump during a cycle. A mark $(u,v)$ means two jumps,
at the relative times

$$
S(u)=\frac2\alpha\arcsin\sqrt u,\qquad
T(v)=P-\frac2\alpha\arcsin\sqrt{1-v},
\tag{1.9}
$$

so $0<S<P/2<T<P$. The path is $q_0$ before $S$, $q_1$ from $S$ until $T$,
and $q_0$ thereafter, using right-continuous values at jumps. Three consecutive
marks form a ten-call block. Thus set

$$
\mathcal B=\mathcal M^3,\qquad
\beta=\vartheta^{\otimes3},\qquad
\mathcal Z=\mathcal B^{\mathbb N},\qquad
\mathbf P=\beta^{\otimes\mathbb N}.
\tag{1.10}
$$

These are standard Borel spaces. Let $\Psi:\mathcal B\to D([0,10],E)$ concatenate
the three cycle paths. Here $D$ has its usual finite-state càdlàg path Borel
structure. The map $\Psi$ is Borel and injective: the path reveals whether each
cycle jumped and, when it did, its two jump times, whose inverse coordinates
are $u=\sin^2(\alpha S/2)$ and $v=1-\sin^2(\alpha T/2)$.

All blocks begin and end at $q_0$. The deterministic wavefunction is the original
$\psi(t)=e^{-itH_1}e_0$; it returns exactly to $e_0$ at cycle boundaries.
Integer call seams carry the original uninterrupted evolution and no new jump,
measurement or reset. In particular the mathematical cycles of length $P$ do
not authorize fractional calls. At the final integer time $10n$, the terminal
is the original $W(q_0)$ in the full $1024$-label space. All original failure,
refusal, stopping and leakage coordinates remain present with zero ideal
probability. The target here includes the complete configuration path and
continuous jump times, as well as the actual call word and these coordinates.
It chooses the allowed case of no additional stochastic fine archive in
III145.2(3); additional archive laws require their separately specified kernels
and drives. No claim below silently supplies those additional drives or the
counterfactual coupling of all other programs in III145.2(4).

**Definition 1.3 (the native finite-precision demand).** For $m\ge1$, code one
cycle by $\star$ or $(\lfloor mu\rfloor,\lfloor mv\rfloor)$. Denote the ordered
three-cycle code of block $k$ by $Y_{k,m}$. Its law, from III184.1–184.2, has

$$
H(Y_{0,m},\ldots,Y_{n-1,m})=nH_m,
\qquad H_m=3\bigl[h_b(a)+2a\log m\bigr],
\tag{1.11}
$$

where $h_b(a)=-a\log a-(1-a)\log(1-a)$. This is a joint path-law statement on
one common running source. The code is a mathematical projection of the full
hidden path; it is not an additional allowed native readout.

## 2. Exact entropy transfer for stationary countable controllers

**Definition 2.1 (the stationary clock class).** Let $C$ be any nonempty
countable discrete space and $Y=K\times C$. Let $\tau:Y\to\{1,2,\ldots\}$ and
$u:Y\to C$ be Borel maps, and define the deterministic Borel map

$$
J(x,s)=\bigl(\delta^{\tau(x,s)}x,u(x,s)\bigr).
\tag{2.1}
$$

Let $\nu$ be a $J$-invariant Borel probability, with

$$
c=\int_Y\tau\,d\nu<\infty.
\tag{2.2}
$$

The occupation probability on the literal source is

$$
\rho(A)=\frac1c\int_Y\sum_{i=0}^{\tau(x,s)-1}
\mathbf1_A(\delta^ix)\,d\nu(x,s).
\tag{2.3}
$$

The joint law $\nu$, rather than just its $K$ marginal, is required to be
invariant. The cost unit $\tau$ is one literal source peel; it is not a charge
for evaluating an arbitrary Borel decoder. Neither $C$ nor $\tau$ is assumed
finite or bounded. There is no assumption that the one-time controller
distribution has finite Shannon entropy, and there is no ergodicity assumption.

A positive integer roof given only as a completed-$\nu$-measurable variable
has a Borel representative with the same integral and occupation law. The
displayed joint formula then holds on a Borel conull set. Removing all its
$J$-inverse iterates of the exceptional set gives a forward-invariant Borel
conull domain on which the following proof applies unchanged. Thus choosing
Borel representatives imposes no further completed-measurable regularity
condition on the clock.

**Theorem 2.2 (literal FIB entropy transfer).** Under exactly Definition 2.1,
$\rho$ is $\delta$-invariant and

$$
\boxed{h_\nu(J)=c\,h_\rho(\delta)\le c\log\phi.}
\tag{2.4}
$$

Proof. Form the integrable tower

$$
\widehat Y=\{(y,i):y\in Y,\ 0\le i<\tau(y)\},
\qquad
\widehat\nu(F)=\frac1c\int_Y\sum_{i<\tau(y)}\mathbf1_F(y,i)\,d\nu(y),
\tag{2.5}
$$

with Borel transformation

$$
\widehat J(y,i)=
\begin{cases}
(y,i+1),&i+1<\tau(y),\\
(Jy,0),&i+1=\tau(y).
\end{cases}
\tag{2.6}
$$

It is a standard Borel probability space. For bounded Borel $f$, invariance of
$\nu$ gives

$$
\begin{aligned}
\int f\circ\widehat J\,d\widehat\nu
&=\frac1c\int_Y
\left[\sum_{1\le i<\tau(y)}f(y,i)+f(Jy,0)\right]d\nu(y)\\
&=\frac1c\int_Y
\left[\sum_{1\le i<\tau(y)}f(y,i)+f(y,0)\right]d\nu(y)
=\int f\,d\widehat\nu.
\end{aligned}
\tag{2.7}
$$

Define the source factor

$$
p((x,s),i)=\delta^ix.
\tag{2.8}
$$

At the top of a tower, (2.1) gives the same value as one further peel.
Consequently $p\widehat J=\delta p$ everywhere and
$p_*\widehat\nu=\rho$ by (2.3). This proves the asserted invariance of $\rho$.

The section $A_0=\{(y,0):y\in Y\}$ has measure $1/c$. Its first return time
is exactly $\tau(y)$, its induced map is $J$, and its normalized induced
probability is $\nu$. Every point reaches $A_0$ in finitely many forward
steps: a point at height $i>0$ reaches it after $\tau(y)-i$ steps. Thus the
section is spanning, even when the system is not ergodic. Apply the classical
spanning-section Abramov formula, in the noninvertible probability-preserving
scope of [Sarig §4.5, Theorem 4.6][Sarig], to obtain

$$
h_{\widehat\nu}(\widehat J)=\frac1c h_\nu(J).
\tag{2.9}
$$

All hypotheses here are on standard probability spaces and the actual first
return section. This use of Abramov does not treat an arbitrary speed-up as
an induced map on $K$, and does not replace the spanning condition by an
unasserted ergodicity hypothesis. The return-time distribution has finite
entropy automatically: if $p_n=\nu(\tau=n)$, comparison with $q_n=2^{-n}$
gives $-\sum p_n\log p_n\le(\log2)\sum np_n=c\log2$ by the elementary
entropy/cross-entropy inequality. This does not bound the entropy of $s$.

We next establish the exact entropy equality for the particular factor (2.8),
including the countable-fibre step. A tower point over $z\in K$ is determined
by the countable label

$$
\ell((x,s),i)=(i,s,\xi|_i),\qquad x=(\xi,v),
\tag{2.10}
$$

because $x=h_{\xi|_i}(z)$ by (1.2)–(1.3). Thus $(p,\ell)$ is a Borel
injection. Its image is Borel and its inverse on that image is Borel, either
directly by the displayed branch formula or by the standard Borel injection
theorem. In particular each $p$ fibre is countable. The state has not been
replaced by finitely many residues: the label retains the whole finite deleted
word, the tower height and the controller state.

For completeness, use only finite partitions to prove that this factor loses
no entropy. Let $\mathcal A$ be any finite Borel partition of $\widehat Y$,
with $k$ atoms, and let
$\mathcal A^{(n)}=\bigvee_{j<n}\widehat J^{-j}\mathcal A$.
Choose a finite set of labels $L$ with
$\widehat\nu(\ell\notin L)<\epsilon$, and put $r=|L|\ge1$.
Given $p$ and a label in $L$, the initial tower point and hence its entire
deterministic $n$-name are determined. Given $p$ and $\ell\notin L$, the
name still has at most $k^n$ possibilities. The chain rule, conditioning also
on $\mathbf1_{\{\ell\in L\}}$, therefore gives

$$
H_{\widehat\nu}(\mathcal A^{(n)}\mid p^{-1}\mathcal B_K)
\le\log2+\log r+\epsilon n\log k.
\tag{2.11}
$$

This argument only uses the probability of a finite set of labels, which
increases to one under any probability on a countable set. In particular it
does not use $H(\ell)<\infty$.

Here is the finite-partition bridge from (2.11) to ordinary entropy. For fixed
$n$ and $\eta>0$, choose a finite Borel partition $\mathcal D$ of $K$ such that

$$
H(\mathcal A^{(n)}\mid p^{-1}\mathcal D)
\le H(\mathcal A^{(n)}\mid p^{-1}\mathcal B_K)+\eta.
\tag{2.12}
$$

Such a partition exists: take increasing finite partitions generated by a
countable Borel generator of $K$. Conditional probabilities of the finitely
many atoms converge to their conditional probabilities given
$p^{-1}\mathcal B_K$; continuity and boundedness of $-t\log t$ on $[0,1]$
give convergence of their integrated conditional entropies. This is the usual
conditional-expectation approximation, not a finite generating-partition
assumption on the dynamics.

Split an $N$-name into $q=\lfloor N/n\rfloor$ blocks of length $n$ and a
remainder. Condition on the $N$-name of $p^{-1}\mathcal D$. That name contains
$\widehat J^{-jn}p^{-1}\mathcal D$ at every block start. The entropy chain rule,
decreasing conditional entropy, invariance and the factor relation imply

$$
\begin{aligned}
H(\mathcal A^{(N)})
&\le H_\rho\!\left(\bigvee_{t<N}\delta^{-t}\mathcal D\right)
 +qH_{\widehat\nu}(\mathcal A^{(n)}\mid p^{-1}\mathcal D)
 +n\log k.
\end{aligned}
\tag{2.13}
$$

Divide by $N$ and let $N\to\infty$. Equations (2.11)–(2.13) yield

$$
h_{\widehat\nu}(\widehat J,\mathcal A)
\le h_\rho(\delta)+\frac{\log2+\log r+\eta}{n}
 +\epsilon\log k.
\tag{2.14}
$$

First fix $\epsilon$ and its finite label set, then take arbitrarily large $n$
(choosing $\mathcal D$ anew for each $n$), and finally let $\epsilon\downarrow0$.
This proves $h_{\widehat\nu}(\widehat J,\mathcal A)\le h_\rho(\delta)$.
The reverse inequality for total entropy follows by pulling back every finite
partition of $K$ along $p$: all of its name probabilities are preserved.
Taking the supremum over $\mathcal A$ proves

$$
h_{\widehat\nu}(\widehat J)=h_\rho(\delta).
\tag{2.15}
$$

Finite partitions in completed spaces have Borel representatives modulo null
sets; countably many iterates preserve their equivalence under invariant
probabilities. Thus the proof covers the usual completed-space entropy too.
Combining (2.9), (2.15) and (1.5) gives (2.4). The nonstandard application bridge
is precisely the countable coding of the actual peel fibres and the finite
partition argument above. No controller Shannon bound, bounded roof or
ergodic decomposition is inserted. ∎

## 3. Native precision costs in the stationary class

**Theorem 3.1 (necessary cost at each native precision).** Suppose Definition
2.1 holds and a single Borel decoder $\mathcal R:Y\to D([0,10],E)$ is used at
all times, with block outputs $\mathcal R(J^ky)$ from one initial $y\sim\nu$.
If, for a fixed integer $m\ge1$, the resulting three-cycle quantile codes
have the native joint law for every finite number of blocks, then

$$
\boxed{c\log\phi\ \ge\ 3[h_b(a)+2a\log m].}
\tag{3.1}
$$

Consequently no such decoder in this finite-$c$ stationary class produces the
entire native continuous configuration-path law for every finite horizon.

Proof. Compose $\mathcal R$ with the finite quantile code of Definition 1.3,
extending the code arbitrarily on nonnative paths if necessary. It is a finite
partition $\mathcal Q_m$ of $Y$. The same decoder and the same update at all
cuts mean its $n$-name is exactly the output code sequence, rather than a family
of unrelated codes chosen at separate cuts. By the joint-law hypothesis and
(1.11),

$$
H_\nu\!\left(\bigvee_{k<n}J^{-k}\mathcal Q_m\right)=nH_m.
\tag{3.2}
$$

Hence $H_m=h_\nu(J,\mathcal Q_m)\le h_\nu(J)\le c\log\phi$ by Theorem 2.2.
Exact continuous-path laws would imply (3.2) for every $m$, whereas $a>0$
makes $H_m\to\infty$. This contradicts finite $c$. ∎

**Definition 3.2 (the scope of the cost).** Inequality (3.1) is a necessary
condition, not a construction or an optimal-cost assertion. A fixed precision
still demands its complete temporal joint law for all $n$; matching just one
block or its one-time configuration marginals does not supply (3.2).
The countable controller may depend on the complete present source, and the
decoder may be any Borel function. No claim of effective acquisition follows.
The relevant source law in the exact identity is the occupation law $\rho$,
which need not equal the $K$ marginal of $\nu$. The upper bound uses all
invariant $\rho$ in (1.5), so requires no identification of these probabilities.
Joint stationarity, positive integer advancement and finite ensemble mean
are the precise additional contracts beyond the literal peel formula.

## 4. A single arithmetic coding of the entire target path

**Definition 4.1 (a fixed conull code).** Fix once and for all Borel conull
sets $G_*\subseteq G$, $\mathcal Z_*\subseteq\mathcal Z$ and a probability
isomorphism

$$
B:G_*\longrightarrow\mathcal Z_*,\qquad
B_*\mu_H=\mathbf P,
\tag{4.1}
$$

with Borel inverse on $\mathcal Z_*$. Extend $B$ to a Borel map
$\bar B:G\to\mathcal Z$ by setting it equal to the all-$\star$ sequence off
$G_*$. Write $\bar B(z)_n\in\mathcal B$ for its block coordinates.

Existence here is a use of classical atomless standard probability-space
isomorphism, rather than a new general coding theorem. To check its precise
applicability, a point of $G$ lies in a residue cylinder of probability $m^{-2}$
for every $m$, so Haar probability has no point atoms. The product
$\mathbf P$ also has no point atoms: the only point atom of $\beta$ is the
all-$\star$ block, of mass $b=(1-a)^3<1$. A singleton in $\mathcal Z$ either has
some non-atomic block coordinate, hence zero probability, or is the all-$\star$
sequence, of probability $\lim_n b^n=0$. On a standard Borel probability space,
absence of point atoms is atomlessness. For example, nested finite partitions
from a countable separating generator would isolate a point in any purported
positive atom, giving the contrary point atom. The completions of both spaces
are perfect, countably separated, complete probability spaces, so satisfy
[Fremlin 344I and 344K(a)][Fremlin]. This is also the static conull-coding
machinery already used in [native certification §§63,67][Native].

For clarity, the completed-space result is converted to (4.1) without using
arbitrary bijections on null sets. Start with the measure-preserving maps
$f,g$ from Fremlin 344I proof (b), inverse almost everywhere, before the
null-set completion in proof (c). Choose Borel versions $f_0:G\to\mathcal Z$
and $g_0:\mathcal Z\to G$; standard Borel targets permit these versions.
They retain their pushforwards and the identities
$g_0f_0=\mathrm{id}$ and $f_0g_0=\mathrm{id}$ almost everywhere. Indeed the
sets on which versions differ are null, and the pushforward identities make
their inverse images null too. The set

$$
D=\{z:g_0(f_0(z))=z\}
\tag{4.2}
$$

is Borel and conull. The Borel map $f_0$ is injective on $D$, so its image
$f_0(D)$ is Borel by the standard Borel injection theorem, has probability one,
and its inverse is $g_0$ there. Take $G_*=D$, $\mathcal Z_*=f_0(D)$ and
$B=f_0|_D$. This proves the representative claims in (4.1).

The maps $B$ and $\Psi$ are fixed before choosing a cut or horizon. They need
not be continuous, computable or finitely obtainable from the declared source
ports. In particular, (4.1) is an isomorphism of initial probability spaces,
not an intertwining $B\delta=\operatorname{shift}B$. Such an intertwining in
the stationary finite-entropy class would contradict Theorem 3.1.

## 5. Unit peels, a growing counter and exact seed recovery

**Theorem 5.1 (stationary zero-tail source with a nonstationary joint clock).**
There is a deterministic Borel unit-peel map on $K\times\mathbb N$ and one fixed
Borel joint-state decoder that, from initial law $\mu_0\otimes\delta_0$,
produce all the native finite configuration-path joint laws of Definition 1.2.
At every cut the $K$ marginal is the same stationary law $\mu_0$, every source
advancement is exactly one, and the initial arithmetic seed is recovered
exactly from the current joint state. The infinite output alone recovers that
same seed almost surely. The initialized joint law is not stationary, and the
map admits no invariant probability on $K\times\mathbb N$.

Proof. On the whole space put

$$
J_0(x,n)=(\delta x,n+1),\qquad
\mathcal R_0((\xi,z),n)
=\Psi\bigl(\bar B(M^nz)_n\bigr).
\tag{5.1}
$$

Both maps are Borel; the countably indexed family $M^n$ poses no measurability
problem. Draw $Z\sim\mu_H$ once. The initialized orbit is exactly

$$
J_0^n((0^\infty,Z),0)=((0^\infty,M^{-n}Z),n).
\tag{5.2}
$$

Its source marginal is $\mu_0$ at every $n$, and the arithmetic reconstruction
$M^nM^{-n}Z=Z$ is pointwise exact. Substitution into the one fixed decoder gives

$$
\mathcal R_0(J_0^n((0^\infty,Z),0))
=\Psi(\bar B(Z)_n).
\tag{5.3}
$$

Thus the entire block sequence is the single draw $B(Z)$, with law
$\beta^{\otimes\mathbb N}$. No fresh seed is drawn between blocks, and neither
the decoder nor the code is changed with the horizon. Concatenating the first
$n$ blocks and retaining the original deterministic wavefunction, integer
call seams, final terminal and failure coordinates gives exactly the law of
$\mathsf T(1^{10n})$ in Definition 1.2. Equality follows from the full mark
product law in III183.2, not just from Born marginals. Endpoints at cycle
boundaries are already $q_0$, so no seam correction or deterministic-time jump
is introduced. Native path prefixes across different terminal horizons are
the restrictions of this same infinite running configuration path; a final
terminal is attached only at the requested end, not inserted into a longer run.

From the infinite output, invert $\Psi$ block by block to obtain $B(Z)$, and
then use $B^{-1}$ on $\mathcal Z_*$. This is a Borel almost-sure recovery of
$Z$, on the same full-measure set $\{Z\in G_*\}$ for every finite cut and the
infinite trajectory. Reconstructing $Z$ at each cut in (5.2) avoids any need
to assume $G_*$ itself is invariant under $M^{-1}$.

Finally, the counter is $n$ with probability one at cut $n$, so the joint laws
at successive cuts are different. If an invariant probability for $J_0$
existed, its counter marginal $\pi$ would be invariant under $n\mapsto n+1$.
Then $\pi(\{0\})=0$ and $\pi(\{n\})=\pi(\{n-1\})$ for $n\ge1$, giving zero
mass to every integer and contradicting total mass one. ∎

**Definition 5.2 (the sharp stationary boundary).** Theorem 5.1 retains unit
advancement, countable controller, a time-independent joint-state decoder,
one initial seed and a stationary source marginal. It removes joint
stationarity. It therefore refutes an extension of Theorem 3.1 that replaces
joint stationarity by source-marginal stationarity, even at advancement one
and source entropy zero. It does not refute (2.4), since the initialized joint
law is not invariant and $h_{\mu_0\otimes\delta_0}(J_0)$ is not an invariant
probability entropy in the sense of Convention 1.1. It also supplies no
finite-work decoder: the access to $\bar B$ in (5.1) remains an explicitly
stronger mathematical access contract.

## 6. Full Parry–Haar input and the actually deleted prefix

**Theorem 6.1 (full source-law version with retained memory).** The source
marginal in Theorem 5.1 can instead be prescribed to be the full original
Parry–Haar law $\lambda$, still with unit peels and one fixed Borel decoder,
by retaining the actual finite deleted prefix. At every finite cut the current
joint state recovers the whole initial source $(\Xi,Z)$ exactly. The resulting
native output has all the joint laws of Definition 1.2 and recovers $Z$
almost surely. Output alone does not recover the independent initial symbolic
source $\Xi$.

Proof. Let $C_{\rm w}=\{0,1\}^{<\mathbb N}$, including the empty word
$\varepsilon$, with its countable discrete structure. On $K\times C_{\rm w}$
put

$$
J_{\rm w}((\xi,z),w)=(\delta(\xi,z),w\xi_0).
\tag{6.1}
$$

The append operation records the actual symbol just deleted. It is not an
arbitrary external word. Define one Borel decoder everywhere by

$$
\mathcal R_{\rm w}((\xi,z),w)
=\Psi\!\left(\bar B\bigl(t_w+M^{|w|}z\bigr)_{|w|}\right).
\tag{6.2}
$$

The arithmetic polynomial $t_w$ is meaningful even on unreachable controller
words, so (6.2) needs no choice of a non-Borel exceptional extension. Initialize
$((\Xi,Z),\varepsilon)$ with $(\Xi,Z)\sim\lambda$. Formula (1.3) gives,
for all initial points and every $n$,

$$
J_{\rm w}^n((\Xi,Z),\varepsilon)
=\left(\left(\sigma^n\Xi,M^{-n}(Z-t_{\Xi|_n})\right),\Xi|_n\right).
\tag{6.3}
$$

Write this as $((\xi_n,z_n),w_n)$. The original source is recovered by

$$
\Xi=w_n\xi_n,\qquad Z=t_{w_n}+M^nz_n,
\qquad n=|w_n|.
\tag{6.4}
$$

All concatenations in (6.4) are legal on the reachable state set. The recovery
is the original branch inverse (1.2); its role here is to maintain the same
arithmetic seed for the decoder at every cut, not to introduce a new general
prefix-inversion theorem. The word length is the internal counter, so no
additional free time coordinate is supplied.

Since $\lambda$ is $\delta$-invariant, the source marginal in (6.3) is
exactly $\lambda$ at every cut. Substituting (6.4) into (6.2) gives

$$
\mathcal R_{\rm w}(J_{\rm w}^n((\Xi,Z),\varepsilon))
=\Psi(\bar B(Z)_n).
\tag{6.5}
$$

The initial product law makes $Z$ Haar and independent of $\Xi$, so the path
law is exactly the same iid native block law as in (5.3), for all horizons
on one common source. This proves the stronger prescribed-source-marginal
assertion: it holds for the full Parry–Haar law, not only a zero-symbol-tail
subsystem. The native carrier, original wavefunction, seams, terminal and
failure coordinates are retained exactly as in the proof of Theorem 5.1.

The infinite output is a function of $Z$ alone and determines $Z$ by (4.1).
It is therefore independent of $\Xi$. It cannot also determine $\Xi$ almost
surely. Indeed $A=\{\Xi_0=1\}$ has probability
$\nu_P(A)=1/(\phi^2+1)\in(0,1)$. If $\Xi$ were measurable from the output,
$A$ would be an output event independent of itself, forcing
$\nu_P(A)=\nu_P(A)^2$, a contradiction. Thus the output-alone recovery scope
is precisely the arithmetic seed asserted here, while current joint-state
recovery includes the symbolic source by (6.4).

The initialized joint law is not invariant, and no invariant probability
exists for (6.1): its word length increases by one everywhere, so the same
counter-marginal argument as in Theorem 5.1 applies. The archive at cut $n$
has finite length $n$, but there is no uniform bound on its length over the
whole run. The set of all such finite records is nevertheless countable. ∎

## 7. Whole-trajectory recovery, finite prefixes and finite acquisition

**Theorem 7.1 (finite native prefixes do not recover the seed).** In either
Theorem 5.1 or Theorem 6.1, for every fixed finite observation horizon $t$ and
every Borel estimator $g$ of the arithmetic seed from the complete native
output up to $t$,

$$
\Pr(g(\text{output}|_{[0,t]})=Z)=0.
\tag{7.1}
$$

The conclusion remains true if the estimator also receives any countable-valued
label, including a finite counter or finite deleted word. It also holds for a
procedure that chooses an almost surely finite prefix and a countable label
and then returns an exact seed. These statements concern output observations
and countable labels; they do not remove the current arithmetic coordinate
from the joint-state recovery formulas (5.2) or (6.4).

Proof. First observe the output through $10n$. Under (4.1) its complete block
marks are $A_n=(B(Z)_0,\ldots,B(Z)_{n-1})$. The tail
$T_n=(B(Z)_n,B(Z)_{n+1},\ldots)$ is independent of $A_n$ and has atomless law
$\mathbf P$, by the atomlessness argument in Definition 4.1. For any Borel
estimator $g_n(A_n)$, equality to $Z\in G_*$ would imply

$$
T_n=(\bar B(g_n(A_n))_n,\bar B(g_n(A_n))_{n+1},\ldots).
\tag{7.2}
$$

Conditional on $A_n$, the right side is a specified point and the left side
has the same atomless tail law. Its conditional probability is zero; integration
proves (7.1) for complete block prefixes. A prefix through any finite $t$ is
a Borel function of a sufficiently long complete block prefix, so it cannot
improve exact recovery.

For a countable label $L$, fix each possible value $l$. The estimator with
$L=l$ is one Borel function $g_{n,l}(A_n)$, and the event of correct recovery
with this label is contained in $\{g_{n,l}(A_n)=Z\}$, already null. A countable
union over $l$ remains null. This argument does not require independence of
$L$ and $Z$. Finally, any finite selected horizon is bounded by $10N$ for some
finite integer $N$. On $\{N=n,L=l\}$ the returned estimator is a function of
the $n$-block prefix and its specified label. Taking the countable union over
$(n,l)$ proves the last assertion. In particular this covers ordinary stopping
protocols, without needing an extra independence assertion at their stopping
times. ∎

**Definition 7.2 (finite source-port acquisition).** A source-blind
deterministic protocol chooses its instructions and final output only from
its initial fixed program and its finite transcript. Its source instructions
are exactly the finite-script contract of [FIB 4.1–4.2][FIB]: $R=h_0$, total
$\delta$, guarded $h_1$, and the declared integer-modulus readout
$q(z)\bmod m$ for $m\ge1$, with the specified success/failure marks and
termination on a failed guard. It may select subsequent instructions from
past replies, but is assumed to terminate almost surely after finitely many
instructions. The instruction set is countable and each declared modulus
has finitely many possible replies. It has no full real seed, history,
arbitrary Borel value or End oracle, and no additional random source. Access
to full state in (5.1) or (6.2) is not part of this port contract.

**Theorem 7.3 (exact finite-port obstruction for these source laws).** Under
Definition 7.2, on either initial source law $\mu_0$ or $\lambda$, a protocol's
exact returned values have countable range up to the null event of nontermination.
It therefore recovers the initial arithmetic seed with probability zero.
If its returned value is intended to be the exact complete native configuration
path over $10n$ calls, its output law $\eta$ satisfies

$$
d_{\rm TV}(\eta,\mathsf P_n)\ge1-(1-a)^{3n},
\tag{7.3}
$$

where $\mathsf P_n$ is the target law of Definition 1.2 and
$d_{\rm TV}(\eta,\zeta)=\sup_A|\eta(A)-\zeta(A)|$. In particular it cannot
have that target law exactly.

Proof. Finite transcripts form a countable union of finite words over a
countable instruction/reply alphabet, hence are countable. A deterministic
final value is a function of its terminal transcript and thus ranges over a
countable set. The Haar arithmetic coordinate has no atoms, so the probability
that it equals any of these countably many returned seed values is zero.

For the path assertion, a finite product of the mark law (1.8) has exactly one
point atom: the mark vector all of whose entries are $\star$, of mass
$(1-a)^{3n}$. Every other point fixes at least one continuously distributed
pair and therefore has probability zero. The concatenated path uniquely
recovers these marks, so the target configuration-path probability has exactly
the same single atom, namely the constant $q_0$ path. Appending the deterministic
call, wavefunction, terminal and failure coordinates changes none of these
atom masses. If $A$ is the countable support of the protocol's path output,
then $\eta(A)=1$ but $\mathsf P_n(A)\le(1-a)^{3n}$. This proves (7.3). ∎

**Definition 7.4 (the acquisition boundary).** Theorem 7.3 is conditional on
the declared source-blind deterministic finite-transcript access model. It
does not exclude exact outputs from an explicitly stronger continuous port,
externally supplied analog state, infinite transcript or additional random
drive. A finite quantile code has finite range, so the countability argument
does not by itself obstruct its acquisition. The stationary all-horizon cost
in (3.1) is a different condition.

For this program the native terminal report at $10n$ is simply $W(q_0)$.
Thus (7.3) concerns the complete hidden continuous path, not a purported
positive-error lower bound for generating this deterministic terminal alone.
Likewise the ability to decode hidden paths in Theorems 5.1 and 6.1 does not
place jump-time monitoring or seed recovery in III145.2's readable
$\mathcal G_t$. The actual $\Gamma$ is countable and has probability zero
under both (1.4); no atomless-source obstruction is thereby proved for every
possible sampling law on $\Gamma$. FIB 4.2's finite-trace equivalence describes
the available observations, not permission to read a completed point exactly.

## 8. Internal event counters and completion clocks

**Convention 8.1 (ensemble and pathwise peel clocks).** In the stationary
class of Definition 2.1, let $\mathcal I_J$ be the invariant sigma-field and

$$
L_n(y)=\sum_{k=0}^{n-1}\tau(J^ky),\qquad
\bar\tau(y)=\mathbb E_\nu[\tau\mid\mathcal I_J](y).
\tag{8.1}
$$

Then for $\nu$-almost every $y$,

$$
\frac{L_n(y)}n\longrightarrow\bar\tau(y),\qquad
1\le\bar\tau(y)<\infty,
\tag{8.2}
$$

and the inverse peel-budget clock

$$
N_y(b)=\max\{n:L_n(y)\le b\}
\tag{8.3}
$$

satisfies $N_y(b)/b\to1/\bar\tau(y)$ as integer $b\to\infty$.
The ensemble mean is $\int\bar\tau\,d\nu=c$. Without ergodicity one cannot
replace $\bar\tau(y)$ by $c$ in these pathwise statements.

These are standard intermediate clock facts: apply the integrable
probability-preserving Birkhoff theorem, in the nonergodic conditional-expectation
form of [Sarig §§2.2–2.3.1][Sarig], to $\tau$.
Its conditional expectation is finite almost everywhere and at least one,
since $\tau\ge1$ and $\int\tau=c<\infty$. This proves (8.2). For every such
path, strict growth of $L_n$ gives $N_y(b)\to\infty$ and

$$
L_{N_y(b)}(y)\le b<L_{N_y(b)+1}(y).
\tag{8.4}
$$

With $n=N_y(b)$, both $L_n/n$ and $L_{n+1}/n$ tend to $\bar\tau(y)$.
Divide (8.4) by $n$ and invert the resulting positive limit. The conditional
expectation identity gives the ensemble integral, but does not assert its
constancy. The following literal source example distinguishes the two means.

**Proposition 8.2 (a literal nonergodic distinction).** The class in Definition
2.1 contains a probability with $c=3/2$ for which pathwise advancement means
are $1$ and $2$ on two sets of probability $1/2$. Its pathwise inverse clock
limits are respectively $1$ and $1/2$, neither equal almost surely to $1/c$.

Proof. Take the actual fixed source point $x_*=(0^\infty,0)$, controller
$C=\{1,2\}$, $u(x,s)=s$, $\tau(x,s)=s$ and

$$
\nu=\tfrac12\delta_{(x_*,1)}+\tfrac12\delta_{(x_*,2)}.
\tag{8.5}
$$

Since $\delta x_*=x_*$, both supported joint states are fixed by $J$.
The law is invariant and $c=3/2$, while $L_n=ns$ on component $s$.
The asserted means and inverse limits follow. In particular even the
ensemble mean of the inverse limits is $3/4$, whereas $1/c=2/3$.
This example respects the literal FIB operation and has zero entropy;
it contradicts no part of (2.4). ∎

**Definition 8.3 (binding to internal memory and actual work).** In
[V57 §2][V57], a counter or archive is inside the total state, rather than a
free parameter external to the decoder. Equations (5.1) and (6.1) implement
that distinction with countable classical records. The fixed decoder reads
the joint state, so its time dependence is a state dependence. The source
coordinate alone does not supply the increasing event index or, in (6.4),
the deleted symbolic prefix. V57 7.4's within-history predictive sufficiency
requires equal retained summaries to give equal required future outputs.
Here the joint-state formulas give such well-defined fixed decoders; equal
current source marginals alone give no such assertion. Neither theorem is a
claim that this classical construction is a finite unitary implementation
of V57's Hilbert-space model.

V57 8.1–8.2 instead fixes actual work costs $d_j\ge1$, cumulative work
$D(k)=\sum_{j\le k}d_j$, and completion count
$K_D(b)=\max\{k:D(k)\le b\}$. Conditional on an implementation with these
measured costs, sequential work conservation and a pathwise limit
$D(k)/k\to\bar d$, the same inverse-sequence argument gives
$K_D(b)/b\to1/\bar d$ (zero for an infinite limit). Source peel count,
decoder evaluation, record acquisition, storage and other charged work
must be related by a separately specified cost contract before one can
substitute $\tau$ for $d_j$. The unit peel in Theorems 5.1 and 6.1 gives no
finite value of $d_j$ for evaluating $\bar B$ with exact continuous output.
In the finite-port contract of Definition 7.2, Theorem 7.3 already rules out
that exact finite acquisition. This leaves a conditional completion-clock
statement, rather than an unproved physical rate or a substitution of the
nonergodic ensemble $c$ for an actual pathwise average.

## 9. Mathematical suppliers and the remaining recovery contracts

**Definition 9.1 (source correspondence and mathematical attribution).** The
source-specific combined results here are repo-derived: the exact stationary
transfer for the literal FIB peel with an arbitrary integrable countable
controller, its native precision consequence, the single-seed unit-peel
nonstationary realization, the full Parry–Haar retained-prefix version, and
their exact finite-prefix and declared-port acquisition boundaries. The
ordinary proofs do not claim global originality or new kernel verification.
Classical entropy, induced transformations and atomless probability-space
isomorphism are intermediate suppliers, not newly proposed general results.

| Supplier | Exact use and boundary |
| --- | --- |
| [FIB source §§2–5,8–9][FIB] | Literal product completion, finite peel fibres, branch inverses, actual finite-script ports, all-invariant-law identity (1.5), Parry–Haar invariance. The arithmetic coordinate is not an uncompensated infinite symbolic sum. The invariant occupation law in (2.3) must first be constructed. |
| [III145.1–145.2,183–185][III] | Entire native carrier, fixed Hamiltonians, square minimal-current rates, uninterrupted integer-call seams, reports/failures, actual-history scope, three iid composite cycle marks per ten calls and the exact quantile entropy. III185's fixed-$r$ exclusion is extended only through Theorem 2.2's additional joint stationarity and integrability contracts. No new native reader or feedback is supplied. |
| [Native certification §§63,67][Native] | Existing static atomless/conull recovery correspondence and its Borel representative discipline. Those cutwise results do not themselves supply the cross-cut fixed joint-state formulas (5.1) and (6.2). |
| [Sarig, *Lecture Notes on Ergodic Theory*, §4.5, Theorem 4.6, printed pp.116–118][Sarig] | Literature-attested Abramov formula for a spanning measurable section of a probability-preserving transformation on a Lebesgue space. The statement does not require ergodicity; the proof treats the invertible case and passes to the natural extension for the noninvertible case. The tower section in (2.5)–(2.6) is explicitly spanning. |
| [Sarig §§2.2–2.3.1, Theorems 2.2 and 2.3, printed pp.37–40][Sarig] | Literature-attested integrable pointwise ergodic limit and its identification as conditional expectation on the invariant sigma-field. Convention 8.1 uses this standard result inside the source-clock comparison; it does not assume that conditional expectation is constant. |
| [Zweimüller, *Invariant measures for general(ized) induced transformations*, Theorem 5.1][Zwei] | Literature-attested related generalized Abramov formula, with conservative ergodic measure-preserving hypotheses and its invariant-measure occupation identity. Those ergodic hypotheses are retained in that statement; it is not used as a nonergodic replacement for Sarig's spanning-section result. |
| [Fremlin, *Measure Theory*, Chapter 34, 344I proof (b), 344K(a), PDF pp.37–38][Fremlin] | Literature-attested isomorphism of the applicable atomless, perfect, complete, countably separated probability spaces. Definition 4.1 chooses actual Borel versions and conull inverse domains. Fremlin's arbitrary null-set bijection in proof (c) is not used as a Borel code. |
| [V57 §§2,7.4,8.1–8.2,10][V57] | Internal counter/record accounting, within-history predictive sufficiency and inverse actual-work completion clocks. These distinguish containment, readable record and predictive sufficiency; they do not identify source peel cost with arbitrary decoder work or nonergodic path means with an ensemble mean. |
| [FiniteFiberEntropy][LeanFinite], `finite_fiber_entropy` | The source declaration concerns compact uniform spaces, a continuous surjective semiconjugacy with uniformly bounded finite fibres, and equality of topological cover entropy. It is not the measurable countable-fibre probability argument (2.10)–(2.15). |
| [AutonomousPredictionEntropy][LeanAutonomous], `autonomous_prediction_entropy` | The source declaration assumes a nonempty compact metric source, continuous autonomous dynamics and continuous metric observation. It relates finite-horizon predictor-state minima to response-cover growth and ordered observation/topological entropy. It does not prove measurable entropy transfer for Borel controllers or finite acquisition of $\bar B$. |
| [ConullImageProbabilityIsomorphism][LeanConull], `conull_measurable_injection_probability_isomorphism` | The source declaration assumes a measurable injection between standard Borel spaces and an image of full target probability; it concludes a pulled-back probability and a measure-preserving equivalence with that image. It corresponds to the structure after (4.2), and does not assert existence of the coding injection or the native path laws. |

**Definition 9.2 (unprovided extensions).** Theorems 5.1 and 6.1 concern a
fixed original address-one running program, with all of its finite native
configuration-path laws on the same seed. They do not construct the full
counterfactual-program noise coupling, independent extra fine archives,
arbitrary control acquisition, a stable finite-resolution code or a finite
physical implementation. Full source recovery from current joint state,
arithmetic recovery from infinite output, finite-prefix reconstruction and
actual finite-interface acquisition have the distinct conditions proved
above. An entropy inequality alone supplies none of the missing operations.

The stationary obstruction and the nonstationary realization therefore give
an exact conditional distinction between event clock, retained memory and
source-marginal law on this original completion. They do not establish an
unconditional mutual reconstruction of space, time, boundary and memory,
or remove the declared resource and common-source contracts.

[FIB]: FIB_SOURCE_COMPLETION_DYNAMICS.md
[III]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md
[Native]: RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md
[V57]: AURIC_FIXED_ONTIC_STATE_GROWING_OBSERVER_STABLE_SELF_INTERNAL_PREDICTION_AND_RELATIVE_CLOCKS_V57.md
[Sarig]: https://www.weizmann.ac.il/math/sarigo/sites/math.sarigo/files/uploads/ergodicnotes.pdf
[Zwei]: https://www.mat.univie.ac.at/~zweimueller/MyPub/z7.pdf
[Fremlin]: https://www1.essex.ac.uk/maths/people/fremlin/chap34.pdf
[LeanFinite]: ../../../D5/S1/Dynamics/FiniteFiberEntropy.lean
[LeanAutonomous]: ../../../D5/S3/Observer/MetricGeometry/AutonomousPredictionEntropy.lean
[LeanConull]: ../../../D5/S3/Observer/ProbabilisticClosure/ConullImageProbabilityIsomorphism.lean

## 追加锚（本行以下为增补区）
