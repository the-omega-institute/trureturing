# Fibonacci harmonic-edge load: ergodic full-support stationary attainment

## 1. The visible domain and the supplied law

**Definition 1.1 (Words, cylinders and exterior fields).** Let

$$
X=\{x\in\{0,1\}^{\mathbb Z}:x_jx_{j+1}=0\text{ for all }j\in\mathbb Z\},
\qquad (Tx)_j=x_{j+1},
$$

with its Borel sigma-field. Write $X_j(x)=x_j$ and

$$
\mathcal E_i=\sigma(X_j:j\ne i),\qquad
F_i=\{X_{i-1}=X_{i+1}=0\}.
$$

For $n\ge1$, put

$$
B_n=\{w\in\{0,1\}^n:w_jw_{j+1}=0\ (1\le j<n)\},
\qquad k(w)=\sum_{j=1}^n w_j.
$$

The cylinder $[w]_a$ specifies $X_{a+j-1}=w_j$ for $1\le j\le n$;
$[w]=[w]_1$. For a stationary probability law $P$ on $X$, $P_n$ is its
actual marginal on coordinates $1,\ldots,n$. Every cylinder probability and
conditional probability below belongs to this one law, rather than to a
separately specified collection of rows.

**Definition 1.2 (The original harmonic objective).** The graph $\Gamma_n$
has vertex set $B_n$ and every legal Hamming-one edge. There is no wraparound
constraint. Define on the entire simplex $\mathcal P(B_n)$

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}
\qquad
\Phi_n(\mu)=\sum_{\{b,c\}\in E(\Gamma_n)}h(\mu_b,\mu_c),
\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu).
$$

The constant $c_\star$ is the supplied limit $\lim_n\kappa_n/n$. When it
exists, write $d(P)=\lim_n\Phi_n(P_n)/n$.

**Hypothesis 1.3 (Published stationary-attainment input).** Let $Q_\star$
be the normalized two-sided stationary law supplied by [Stationary,
Theorem 3.1][Stationary]. No ergodicity hypothesis is imposed on $Q_\star$.
The same source, equations (1.1), (2.5), (2.6), (3.4) and (4.2), supplies

$$
\kappa_n\le(n+1)c_\star\quad(n\ge1),\qquad
d(P)=\mathbb E_P[(X_0-\mathbb E_P[X_0\mid\mathcal E_0])^2]
\le c_\star
\tag{1.1}
$$

for every stationary probability law $P$ on $X$, with no support or memory
assumption on $P$, and $d(Q_\star)=c_\star$. Choose an
$\mathcal E_0$-measurable Borel version
$q_0=\mathbb E_{Q_\star}[X_0\mid\mathcal E_0]$ taking values in $[0,1]$.
Its supplied bounds are

$$
q_0=0\text{ on }F_0^c,\qquad
\frac14\le q_0\le\frac12\text{ on }F_0,
\quad Q_\star\text{-almost surely}.
\tag{1.2}
$$

For every $i\in\mathbb Z$ put $q_i=q_0\circ T^i$. Stationarity makes this
a version of $\mathbb E_{Q_\star}[X_i\mid\mathcal E_i]$, and (1.2) holds
at coordinate $i$. These inputs are reused without reconstructing the
finite optimizers or the stationary law. The other project input is
[Finite Memory, Theorem 1.5][Finite Memory]: every normalized two-sided
stationary law on $X$ with positive legal cylinders and finite visible
Markov order has density strictly below $c_\star$.

## 2. One common set of optimal full-support ergodic components

**Theorem 2.1 (Component attainment with the inherited constants).** There
is a standard Borel space $\Lambda$ of actual normalized stationary ergodic
probability laws $R_\lambda$ on $X$, a measurable component map
$\psi:X\to\Lambda$, and its probability distribution
$W=(\psi)_*Q_\star$, such that $Q_\star$ disintegrates over these laws.
There is one measurable $\Lambda_\star\subseteq\Lambda$ with
$W(\Lambda_\star)=1$ on which all of the following assertions hold
simultaneously.

For every $\lambda\in\Lambda_\star$, every $i\in\mathbb Z$, and every
$A\in\mathcal E_i$,

$$
q_i=\mathbb E_{R_\lambda}[X_i\mid\mathcal E_i]
\quad R_\lambda\text{-almost surely},
\qquad
R_\lambda(A,X_i=0)\ge\frac12R_\lambda(A),
\tag{2.1}
$$

and, whenever $A\subseteq F_i$,

$$
\frac13R_\lambda(A,X_i=0)
\le R_\lambda(A,X_i=1)
\le R_\lambda(A,X_i=0).
\tag{2.2}
$$

For every such $\lambda$, every $m,n\ge1$, every $a\in\mathbb Z$, and
every $w\in B_n$,

$$
R_\lambda([0^m]_a)\ge2^{-m},\qquad
R_\lambda([w]_a)\ge2^{-(n+2)}3^{-k(w)}>0,
\tag{2.3}
$$

and

$$
d(R_\lambda)=c_\star,\qquad
n c_\star\le\Phi_n((R_\lambda)_n)
\le\kappa_n\le(n+1)c_\star\quad(n\ge1).
\tag{2.4}
$$

Every legal finite next-extension $wv$ of a legal nonempty word $w$ has
$R_\lambda([wv]) / R_\lambda([w])>0$. If the final bit of $w$ is $1$,
the next bit is $0$ with conditional probability one. Each $R_\lambda$
in this common set has no finite visible Markov order. In particular at
least one single stationary ergodic law has all these properties.

**Proof.** We first specify the actual joint law, then transfer the
infinite-exterior posterior, and only then deduce optimality and support.

### 2.1. The measurable decomposition and the exterior component label

The space $X$ is a closed subset of the compact metrizable binary product,
so it is Polish with its Borel sigma-field standard. The shift $T$ is
invertible and Borel. Thus [Gray, Theorem 8.5.1][Gray] applies to the
stationary dynamical system $(X,Q_\star,T)$. In the realization used in
that theorem's proof, $\Lambda$ is the Borel set of stationary ergodic
probability measures on $X$ and $R_\lambda=\lambda$. In particular each
component is a normalized law on the original visible space. The evaluation
maps $\lambda\mapsto R_\lambda(C)$ are measurable for Borel $C\subseteq X$.
The theorem gives an invariant measurable $\psi$, and asserts that
$R_{\psi(x)}(C)$ is a version of $Q_\star(C\mid\psi)$.

The process is two-sided, stationary, and has the finite, hence standard,
alphabet $\{0,1\}$. [Gray, Lemma 8.6.2][Gray] therefore permits the same
component map to be chosen measurable with respect to
$\sigma(X_j:j<0)$. This lemma does not assume finite visible Markov order.
For every integer $i$, $\psi\circ T^i$ is measurable with respect to
$\sigma(X_j:j<i)\subseteq\mathcal E_i$. Invariance identifies it with
$\psi$. It is enough if this identification holds $Q_\star$-almost surely;
the countably many coordinate identifications can be imposed together.
Consequently, for every $H$ in the Borel sigma-field $\mathcal L$ of
$\Lambda$, $\mathbf1_{\{\psi\in H\}}$ has an
$\mathcal E_i$-measurable version for every $i$.

To make the joint-law claim explicit, define the probability measure

$$
J=(\psi,\operatorname{id}_X)_*Q_\star
\quad\text{on }\Lambda\times X.
$$

The conditional-probability assertion of Theorem 8.5.1 says that, for
$H\in\mathcal L$ and Borel $C\subseteq X$,

$$
J(H\times C)=Q_\star(\{\psi\in H\}\cap C)
=\int_H R_\lambda(C)\,dW(\lambda).
\tag{2.5}
$$

Measurability of the probability kernel extends (2.5), first by simple
functions and then by monotone convergence on the product sigma-field, to

$$
\int f(\psi(x),x)\,dQ_\star(x)
=\int_\Lambda\int_X f(\lambda,x)\,dR_\lambda(x)\,dW(\lambda)
\tag{2.6}
$$

for every bounded Borel $f$ on $\Lambda\times X$. This is the joint law
used throughout the proof; its $X$-marginal is $Q_\star$, its
$\Lambda$-marginal is $W$, and it is concentrated on $\psi(x)=\lambda$.
The latter graph is Borel because $\Lambda$ is standard Borel. Applying
(2.6) to its indicator shows that

$$
\Lambda_0=\{\lambda:R_\lambda(\{x:\psi(x)=\lambda\})=1\}
$$

is measurable and conull. This also specifies the component fiber under
each law in the common set constructed below.

### 2.2. A simultaneous posterior transfer

Fix $i$ and an exterior cylinder $A$ specifying finitely many coordinates
other than $i$. For every $H\in\mathcal L$, the exterior measurability of
the component label and the defining identity for $q_i$ give

$$
\int \mathbf1_A\mathbf1_{\{\psi\in H\}}(X_i-q_i)\,dQ_\star=0.
$$

Applying (2.6) yields

$$
\int_H g_{i,A}(\lambda)\,dW(\lambda)=0,
\qquad
g_{i,A}(\lambda)=\int\mathbf1_A(X_i-q_i)\,dR_\lambda.
\tag{2.7}
$$

The function $g_{i,A}$ is measurable and bounded. Since (2.7) holds for
every $H$, taking its positive and negative level sets gives
$g_{i,A}=0$ $W$-almost surely. There are countably many $i$ and countably
many exterior cylinders at each $i$, including $X$ and the empty event.
Intersect their measurable conull sets with $\Lambda_0$ to obtain
$\Lambda_1$.

For a fixed $\lambda\in\Lambda_1$ and $i$, the finite signed measure
$A\mapsto\int_A(X_i-q_i)\,dR_\lambda$ vanishes on this cylinder
pi-system. It vanishes on all of $\mathcal E_i$: the class of zero sets
contains $X$, is closed under complements and disjoint countable unions,
and hence contains the generated sigma-field by the pi-lambda argument.
The function $q_i$ is $\mathcal E_i$-measurable and bounded, so the
defining conditional-expectation identities prove

$$
q_i=\mathbb E_{R_\lambda}[X_i\mid\mathcal E_i]
\quad R_\lambda\text{-almost surely}
\quad(\lambda\in\Lambda_1,\ i\in\mathbb Z).
\tag{2.8}
$$

This reduction to a countable generating class precedes the extension to
all exterior events. No intersection over an uncountable family of
event-dependent exceptional sets is taken.

Let $E$ be the Borel event on which, simultaneously for all $i$,
$q_i=0$ on $F_i^c$ and $1/4\le q_i\le1/2$ on $F_i$. By (1.2) and
stationarity, $Q_\star(E)=1$. Equation (2.6) gives
$\int R_\lambda(E)\,dW=1$, so

$$
\Lambda_2=\Lambda_1\cap\{\lambda:R_\lambda(E)=1\}
$$

is measurable and conull. Both the common posterior and all of its
coordinate bounds now hold under each component in $\Lambda_2$.

### 2.3. The exact density identity and component optimality

For $\lambda\in\Lambda_2$, apply the stationary risk identity (1.1) to
$R_\lambda$ and use (2.8) at $i=0$:

$$
d(R_\lambda)=\int(X_0-q_0)^2\,dR_\lambda\le c_\star.
\tag{2.9}
$$

The density is a measurable function of $\lambda$: it is the limit of
the measurable finite-cylinder functions
$\Phi_n((R_\lambda)_n)/n$, and the limit exists for every stationary
component by (1.1). Equations (2.6), (2.9) and $d(Q_\star)=c_\star$ give

$$
c_\star=\int(X_0-q_0)^2\,dQ_\star
=\int_\Lambda d(R_\lambda)\,dW(\lambda).
\tag{2.10}
$$

In the last equality it suffices to use the conull set $\Lambda_2$;
all integrands are bounded. The nonnegative function
$c_\star-d(R_\lambda)$ therefore has integral zero. Hence

$$
\Lambda_\star=\Lambda_2\cap\{\lambda:d(R_\lambda)=c_\star\}
\tag{2.11}
$$

is one measurable conull set of exact attainers. Identity (2.10) concerns
the infinite-exterior risk. No equality between a finite-window risk of
the mixture and the average of the components' finite-window risks is
used or asserted.

### 2.4. Component insertion inequalities and all cylinder bounds

We apply the support implications of [Stationary, §4][Stationary] to
the component posterior just proved, retaining their constants. Fix
$\lambda\in\Lambda_\star$ and write $R=R_\lambda$. For
$A\in\mathcal E_i$, (2.8) gives

$$
R(A,X_i=1)=\int_A q_i\,dR,\qquad
R(A,X_i=0)=\int_A(1-q_i)\,dR.
\tag{2.12}
$$

On $F_i$ the bounds on $q_i$ imply
$(1-q_i)/3\le q_i\le1-q_i$, yielding (2.2) by integration when
$A\subseteq F_i$. On $F_i^c$ legality forces $X_i=0$ and $q_i=0$ almost
surely. Thus $1-q_i\ge1/2$ everywhere almost surely, proving (2.1).
These inequalities apply even when an exterior event has zero mass;
they require no division by that mass.

For any $a\in\mathbb Z$ apply (2.1) successively at the $m$ coordinates
$a,\ldots,a+m-1$. At each step the zeros already imposed form an
exterior event for the next coordinate. Starting with $R(X)=1$ gives

$$
R([0^m]_a)\ge2^{-m}.
\tag{2.13}
$$

Given $w\in B_n$, consider its padded cylinder $[0w0]_{a-1}$. Start from
$[0^{n+2}]_{a-1}$ and insert each of the $k(w)$ ones into its middle
$n$ coordinates. All intermediate words are legal because no two of
these insertion sites are adjacent. For each insertion the cylinder
specifying every other coordinate of the padded word belongs to
$\mathcal E_i$ and is contained in $F_i$. This includes an insertion at
either endpoint of $w$, since the extra padding bit is zero. Inequality
(2.2) therefore gives, one insertion at a time,

$$
R([w]_a)\ge R([0w0]_{a-1})
\ge3^{-k(w)}R([0^{n+2}]_{a-1})
\ge2^{-(n+2)}3^{-k(w)}.
\tag{2.14}
$$

This proves (2.3) in every component in the already fixed set
$\Lambda_\star$. No support assertion has been inferred from positive
mixture masses. A cylinder on any other finite set of coordinates that
admits a legal completion contains a legal interval cylinder, and is
positive as well: fill unspecified positions in its spanning interval
with zero.

If $wv\in B_{n+\ell}$ is a legal extension with $\ell\ge1$, both
$R([wv])$ and $R([w])$ are positive by (2.14), proving the stated finite
conditional positivity. When $w$ ends in $1$, $[w1]$ is empty in $X$
and $[w0]=[w]$ as events on $X$, so the sole legal next bit has
conditional probability one. This uses finite-history conditionals;
it introduces no finite-memory hypothesis.

### 2.5. Every finite-length objective certificate

Fix any $n\ge1$ and $1\le i\le n$. Put
$\mathcal G_{n,i}=\sigma(X_j:1\le j\le n,\ j\ne i)$ and
$u_{n,i}=\mathbb E_R[X_i\mid\mathcal G_{n,i}]$. Since
$\mathcal G_{n,i}\subseteq\mathcal E_i$, the conditional-expectation
identity gives

$$
\begin{aligned}
\mathbb E_R[(X_i-u_{n,i})^2]
&=\mathbb E_R[(X_i-q_i)^2]
  +\mathbb E_R[(q_i-u_{n,i})^2]\\
&\ge d(R)=c_\star.
\end{aligned}
\tag{2.15}
$$

Indeed the cross term has expectation zero by conditioning on
$\mathcal E_i$, and stationarity with $q_i=q_0\circ T^i$ identifies
the first term with (2.9).

The supplied coordinate-fiber identity [Stationary, §2][Stationary], also
stated as [Finite Memory, Lemma 2.1][Finite Memory], identifies the left
side of (2.15) with the contribution of coordinate $i$ to
$\Phi_n(R_n)$. Its hypotheses are exactly a probability vector on the
complete $B_n$. On a two-word fiber of masses $s,t$ the weighted squared
risk is $h(s,t)$; a forced-zero singleton has risk zero, and a fiber with
$s=t=0$ has both weighted risk and $h(0,0)$ zero. Thus this identity keeps
the all-zero word, legal endpoint ones, and all original edges. It
requires no boundary matching, seam independence or positive-mass
division. Summing (2.15) over all $n$ coordinates, and applying the
definition of $\kappa_n$ and the supplied ceiling (1.1), proves (2.4).
The argument also covers $n=1$ with its trivial conditioning field.

### 2.6. Existence of one law and the visible-memory consequence

All conclusions so far hold for every $\lambda$ in the single set
$\Lambda_\star$. The only exceptional sets removed were the
component-fiber condition, those indexed by countably many coordinates
and exterior cylinders, the one event $E$, and the one density equality.
After (2.8), all exterior-event, word,
length, translation and finite-extension conclusions followed for each
fixed component without further exceptional-set choices.

Since $W$ is a probability measure and $W(\Lambda_\star)=1$,
$\Lambda_\star$ is nonempty. Choose any one member and take its actual
law $R_\lambda$; every marginal and certificate above then belongs to
that single normalized two-sided stationary ergodic process.

If this law had finite visible order $m\ge1$, it would satisfy every
hypothesis of [Finite Memory, Definition 1.4 and Theorem 1.5][Finite Memory]:
normalization, two-sided stationarity, positive legal cylinders, actual
finite-history transition rows, positive legal next-extensions and
forced zero after one. The supplier would give $d(R_\lambda)<c_\star$,
contradicting (2.4). Order zero is excluded too: a stationary order-zero
law is iid, and positive one-bit probability for $1$ would give positive
probability for the forbidden cylinder $11$. Thus no finite visible
order is possible. $\square$

## 3. Mathematical source ownership

**Convention 3.1 (Premises and attribution).** The project premises of
Theorem 2.1 are exactly Hypothesis 1.3 and the cited coordinate-fiber
identity from the two published suppliers. Their ordinary mathematical
proofs are the assumed source inputs. The stationary law, the all-law
risk identity and ceiling, and the posterior interval $[1/4,1/2]$ belong
to [Stationary]; the pointwise finite-visible-order contradiction belongs
to [Finite Memory]. The component posterior transfer (2.7)–(2.8), the
exact component-density consequence (2.9)–(2.11), and their simultaneous
use with the insertion and finite-length certificates constitute the
`repo-derived` conclusion here.

The needed `literature-attested` probability facts are those of Robert
M. Gray, *Probability, Random Processes, and Ergodic Properties*, the
author-hosted text bearing the version date January 2, 2010:
Theorem 8.5.1, printed pp. 185–186, supplies the measurable invariant
ergodic decomposition and its conditional-probability interpretation;
Lemma 8.6.2, printed p. 187, supplies past measurability for a two-sided
stationary process with standard alphabet. Its Markov-process setting
does not add a Markov hypothesis to that lemma. The standard-space
criterion used above is Gray, Theorem 3.3.2; the defining conditional
expectation identities are Gray, §5.9, equations (5.27)–(5.28).
The new transfer to the entire punctured exterior is proved in §2.2
rather than imported as a learning or finite-memory conclusion.

The theorem establishes existence and the specified quantitative
certificates. It does not identify a unique component, assert mixing,
specify a Gibbs interaction or an effective construction, exclude finite
hidden-state producers, determine a numerical value of $c_\star$, or
give a gap uniform over laws of a fixed visible order. Those assertions
are not consequences claimed here. The attribution is to the checked
facts and to this deduction from them, with no worldwide priority claim
or assertion of a learning or physical benefit.

[Stationary]: https://github.com/the-omega-institute/trureturing/blob/db23810980530aea4b6fc2a056615460c8cbecb9/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[Finite Memory]: https://github.com/the-omega-institute/trureturing/blob/db23810980530aea4b6fc2a056615460c8cbecb9/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_NONATTAINMENT.md
[Gray]: https://www-ee.stanford.edu/~gray/arp.pdf

## 追加锚（本行以下为增补区）
