# CDSO uniform dilution limit

## 1. The original law and prescribed graph domains

**Definition 1.1 (Common laws and strictly oriented graphs).** Integers
$a\ge4$, $h\ge1$ have $s=a+1+h$. Retain exactly the law domain
$\mathcal X(a,h)$ of [Growing, Definition 1.1](CDSO_GROWING_SURPLUS_HUBS.md):

$$
x_T\ge0,\qquad \sum_{\varnothing\ne T\subseteq[s]}x_T=1,
\qquad \mathbb E_x|T|=a,\qquad
y_i=\mathbb P_x(i\in T)>0.
\tag{1.1}
$$

All expectations and marginals come from this one law. Every nonempty
cardinality is allowed, type masses can vanish, positive marginals have no
imposed lower bound, and the incidence support can be disconnected. Write

$$
K=|T|,\qquad
H(x)=\mathbb E_x\left[K^2\sum_{i\in T}y_i^{-2}\right],\qquad
M(a,h)=\inf_{x\in\mathcal X(a,h)}H(x),\qquad B_0(a)=a(a+1)^2.
\tag{1.2}
$$

Retain exactly $\mathfrak G_N(a,h)$ of Growing, Definition 9.1. Its
members are finite simple connected bipartite graphs with independent
parts consisting of $N$ sources and $s$ sinks, exactly $aN$ edges, and
source degree $k_u$ and sink degree $d_i$ satisfying

$$
k_u<d_i\qquad(ui\in E).
\tag{1.3}
$$

For such a graph put

$$
\begin{aligned}
W(G)&=2N\sum_{ui\in E}\left(\sqrt{1+(k_u/d_i)^2}-1\right),\\
Q(G)&=N\sum_{ui\in E}(k_u/d_i)^2,\\
V_N(a,h)&=\min_{G\in\mathfrak G_N(a,h)}W(G)
\end{aligned}
\tag{1.4}
$$

when the class is nonempty. This is a minimum because the class of
labelled simple graphs with these part sizes is finite. The actual law
obtained by choosing a source uniformly has $y_i=d_i/N$ and
$Q(G)=H(x)$, by Growing, Lemma 9.2. The CDSO convention is the
maximum-endpoint-degree denominator, with no factor $1/\sqrt2$ [1, §1].

**Theorem 1.2 (Uniform transfer at dilution scale $a^{3/2}$).** For every
$0<L\le R<\infty$ there are positive finite constants $A,D_0,C$,
depending only on $L,R$, such that all integers

$$
a\ge A,\qquad L\le h/\sqrt a\le R,\qquad
N\ge\lceil D_0a^{3/2}\rceil
\tag{1.5}
$$

have $\mathfrak G_N(a,h)\ne\varnothing$. Every graph in this full class
satisfies

$$
W(G)\ge M(a,h)-C\left(a^{3/2}+\frac{a^5}{N^2}\right),
\tag{1.6}
$$

and at least one member satisfies

$$
W(G)\le M(a,h)+C\frac{a^{7/2}}N.
\tag{1.7}
$$

Consequently

$$
-C\left(a^{-1/2}+\left(\frac{a^{3/2}}N\right)^2\right)
\le\frac{V_N(a,h)-M(a,h)}{a^2}
\le C\frac{a^{3/2}}N.
\tag{1.8}
$$

The constants are simultaneous over the entire fixed positive window,
including its phase boundaries. Sections 2--4 prove (1.6)--(1.7), and
Section 5 gives the resulting quantified and sequential conclusions.

## 2. Nonlinear control without a marginal floor

**Lemma 2.1 (A nonlinear sublevel controls the common-law sublevel).**
For every $G\in\mathfrak G_N(a,h)$ and its actual law,

$$
W(G)\ge a^3+\frac{H(x)-a^3}{\sqrt2}-\frac{s^5}{4N^2}.
\tag{2.1}
$$

In particular, if $s\le2a$, $N\ge a^{3/2}$ and
$W(G)\le a^3+C_0a^2$, then

$$
H(x)\le a^3+\sqrt2(C_0+8)a^2.
\tag{2.2}
$$

**Proof.** Define

$$
g(t)=2(\sqrt{1+t^2}-1),\qquad
F_k(z)=N^2g(k\sqrt z/N).
$$

For an incidence of a source of degree $k$, the entire interval
$1\le z\le y_i^{-2}$ has $k\sqrt z/N<1$, by (1.3). Therefore

$$
F_k'(z)=\frac{k^2}{\sqrt{1+k^2z/N^2}}\ge\frac{k^2}{\sqrt2},
\qquad
F_k(1)\ge k^2-\frac{k^4}{4N^2}.
\tag{2.3}
$$

The second inequality is the Taylor bound in Growing, Lemma 9.2.
Integration of the first inequality gives, for this incidence,

$$
F_k(y_i^{-2})\ge k^2-\frac{k^4}{4N^2}
                  +\frac{k^2}{\sqrt2}(y_i^{-2}-1).
$$

Sum within each actual neighborhood and take the actual source-law
expectation. Since $W=N^2\mathbb E\sum_{i\in T}g(K/(Ny_i))$,

$$
W\ge \mathbb E K^3-\frac{\mathbb E K^5}{4N^2}
                  +\frac{H-\mathbb E K^3}{\sqrt2}.
\tag{2.4}
$$

Jensen gives $\mathbb E K^3\ge a^3$, while $K\le s$ gives
$\mathbb E K^5\le s^5$. These imply (2.1). If $s\le2a$ and
$N\ge a^{3/2}$, then $s^5/(4N^2)\le8a^2$, proving (2.2).
In particular, the factor $1/\sqrt2$ applies to the excess above $a^3$;
it does not replace the leading value by a constant multiple of $a^3$.
No lower bound on an actual marginal was assumed. ∎

**Lemma 2.2 (A nonlinear common-event certificate).** Let $G$ have its
actual law as above, and let $D\subseteq[s]$ be any nonempty sink set of
size $n$. Set

$$
A_D=\{T\cap D\ne\varnothing\},\qquad
p=\mathbb P(A_D),\qquad
U_D(T)=\sum_{i\in T\cap D}y_i^{-1},
$$

and let $W_D$ be the part of $W$ on edges incident to $D$. Then $p>0$ and

$$
\begin{aligned}
W_D&\ge pN^2g\left(\frac{n}{Np}\right)\\
&\ge\frac{n^2}p-\frac{n^4}{4N^2p^3}.
\end{aligned}
\tag{2.5}
$$

These inequalities do not require a positive lower bound on the
marginals or any bound on the individual tail ratios other than the
graph's own hypotheses.

**Proof.** The actual marginal identity is

$$
\mathbb E U_D=\sum_{i\in D}\frac{\mathbb P(i\in T)}{y_i}=n.
\tag{2.6}
$$

On $A_D$ put $b=|T\cap D|\ge1$. The function $g$ is increasing on
$[0,\infty)$ and convex there, since
$g''(t)=2(1+t^2)^{-3/2}>0$. Finite Jensen and $K\ge b$ imply

$$
\begin{aligned}
\sum_{i\in T\cap D}g\left(\frac{K}{Ny_i}\right)
&\ge b\,g\left(\frac{KU_D}{Nb}\right)\\
&\ge g(U_D/N).
\end{aligned}
\tag{2.7}
$$

On $A_D^c$ both sides vanish. Conditional Jensen on the same event,
together with (2.6), yields

$$
W_D\ge N^2\mathbb E[g(U_D/N);A_D]
       \ge pN^2g(n/(Np)).
$$

Finally $g(t)\ge t^2-t^4/4$ for every $t\ge0$. To check the unrestricted
range, set $z=t^2$ and differentiate
$2(\sqrt{1+z}-1)-z+z^2/4$ twice: its second derivative is
$[1-(1+z)^{-3/2}]/2\ge0$, and its value and first derivative vanish
at zero. This proves (2.5). Every expectation in this calculation
uses the original joint law. ∎

## 3. A uniform lower bound over the entire graph class

**Proposition 3.1 (Full-class nonlinear lower transfer).** For every
$0<L\le R<\infty$ there are finite $A,C$, depending only on $L,R$,
such that every graph in $\mathfrak G_N(a,h)$ with
$a\ge A$, $L\le h/\sqrt a\le R$ and $N\ge a^{3/2}$ satisfies (1.6).

**Proof.** Throughout this proof all constants depend only on $L,R$.
Increase $A$ so that $s\le2a$. Put $k=h/\sqrt a$ and
$C_0=R^2+10$. Growing, Theorem 7.2, and its comparison
$U(k)\le k^2+2$ give, after another uniform increase of $A$,

$$
M(a,h)\le a^3+(R^2+6)a^2.
\tag{3.1}
$$

A graph with $W>a^3+C_0a^2$ already has $W>M$. It suffices to treat
the complementary sublevel. Lemma 2.1 places its actual law in

$$
H\le a^3+C_1a^2,\qquad C_1=\sqrt2(C_0+8).
\tag{3.2}
$$

Apply Growing, Lemma 7.1, to this one law with $C=C_1$. Its threshold
partition and the estimates established in (7.7), (7.10), (7.13)--(7.15)
and (7.19) of that proof give sets $C\dot\cup D=[s]$ and constants
$c,v_*,J,E>0$ depending only on $L,R$, such that

$$
\begin{gathered}
m=|C|=a+j,\qquad n=|D|=h+1-j>0,\qquad 1\le j\le J,\\
y_i\ge c\quad(i\in C),\qquad
p=\mathbb P(T\cap D\ne\varnothing)=v/a,\\
v_*\le v\le j+Ea^{-1/2},\qquad n\le(R+1)\sqrt a,
\end{gathered}
\tag{3.3}
$$

and the core part of the quadratic energy obeys

$$
H_C:=\mathbb E\left[K^2\sum_{i\in T\cap C}y_i^{-2}\right]
\ge a^3+(2j+2v)a^2-Ea^{3/2}.
\tag{3.4}
$$

In particular, (3.4) is the core estimate (7.19), before the quadratic
tail energy is added; it retains the original, unconditioned denominators.
These are existing common-law estimates, not assumptions about an
optimizing graph, symmetry, or its allowed source types.

On every core incidence $K/(Ny_i)\le s/(cN)$. The edge Taylor estimate
therefore gives

$$
\begin{aligned}
W_C&\ge H_C-\frac N4\sum_{ui:\ i\in C}(k_u/d_i)^4\\
&\ge H_C-\frac{s^2}{4c^2N^2}H_C
\ge H_C-C_2\frac{a^5}{N^2}.
\end{aligned}
\tag{3.5}
$$

For the last inequality use $H_C\le H\le2a^3$, after increasing $A$.
The lower bound on core marginals was deduced from (3.2); none was
imposed on the original domain.

Apply Lemma 2.2 to the actual complementary sink set $D$. Equations
(3.3) and (2.5) give

$$
W_D\ge\frac{n^2}p-C_3\frac{a^5}{N^2},\qquad
C_3=\frac{(R+1)^4}{4v_*^3}.
\tag{3.6}
$$

This estimate permits arbitrarily small individual tail marginals and
all the graph's original source cardinalities. It bounds their combined
nonlinear cost through their common event, rather than replacing each
individual cost by its quadratic approximation.

Adding (3.4)--(3.6), subtracting $B_0=a^3+2a^2+a$, and using $p=v/a$,

$$
\frac{W-B_0}{a^2}
\ge \frac{n^2}{av}+2v+2j-2
       -C_4\left(a^{-1/2}+\frac{a^3}{N^2}\right).
\tag{3.7}
$$

Since $n=h+1-j$, the first term differs from $k^2/v$ by
$O_{L,R}(a^{-1/2})$. If $v>j$, replace $v$ by $j$ in
$k^2/v+2v$. The change is again $O_{L,R}(a^{-1/2})$:
$v-j\le Ea^{-1/2}$, and the derivative $-k^2/v^2+2$ is uniformly
bounded between those two arguments. Growing, (7.23) and (7.28), now give

$$
\frac{n^2}{av}+2v+2j-2\ge U(k)-C_5a^{-1/2}.
\tag{3.8}
$$

Thus $W\ge B_0+a^2U(k)-C_6(a^{3/2}+a^5/N^2)$. Growing,
Theorem 7.2, also gives $M\le B_0+a^2U(k)+C_7a^{3/2}$, proving (1.6).
The initial high-energy case and this sublevel case exhaust the entire
original graph class. ∎

## 4. Every integer budget with bounded-degree connectors

**Lemma 4.1 (A uniformly rounded connected comparison law).** Fix
$0<L\le R<\infty$, an integer $J\ge1$, and $0<v_0\le1$.
There exist positive finite $A,D_0,C$, depending only on these fixed
parameters, with the following property. Suppose

$$
\begin{gathered}
a\ge A,\qquad L\le h/\sqrt a\le R,\qquad
1\le j\le\min(J,h),\qquad v_0\le v\le j,\\
m=a+j,\qquad n=h+1-j,\qquad
p=\frac{v}{a+v-1},\qquad N\ge\lceil D_0a^{3/2}\rceil.
\end{gathered}
\tag{4.1}
$$

Let $f$ be the linear interpolation of the integer cubes on $[a,m]$.
The actual comparison law of Growing, Proposition 3.2, has energy

$$
H_{j,v}=H_C^*+H_D^*,\qquad
H_C^*=\frac{(1-p)f(a+v)}{((a-p)/m)^2},\qquad H_D^*=\frac{n^2}p.
\tag{4.2}
$$

There is a graph in $\mathfrak G_N(a,h)$ with

$$
W(G)\le Q(G)\le H_{j,v}+C\frac{a^{7/2}}N.
\tag{4.3}
$$

This holds for every such integer $N$, including integer $v$ and $v=j$.

**Proof.** Enlarge $A$ using only the displayed fixed parameters so that

$$
\begin{gathered}
a>J,\qquad m,s\le2a,\qquad n/m\le1,\qquad
y_C^*:=(a-p)/m\ge1/2,\\
\frac{v_0}{2a}\le p\le\frac Ja\le\frac14,\qquad
n\le(R+1)\sqrt a.
\end{gathered}
\tag{4.4}
$$

For example, take $D_0\ge\max\{8,16(R+1)/v_0\}$. Define integer counts

$$
Z=\lfloor pN\rfloor,\qquad T_1=Z-n,\qquad Q_0=N-Z.
\tag{4.5}
$$

Then $pN\ge8n$, hence $Z\ge7n$, $T_1\ge0$, $Q_0\ge3N/4$ and
$Z\ge pN/2$. Allocate $T_1$ singleton sources to the $n$ tail sinks
as evenly as possible. For each tail sink add one distinct connector
source, adjacent to that sink and to a fixed core sink $i_0$.
These are $n$ sources of degree two. Together the singleton and
connector sources have $Z$ vertices and $Z+n$ edges.

The remaining $Q_0$ sources must supply exactly

$$
B=aN-Z-n
\tag{4.6}
$$

core incidences. Their required excess mean degree is

$$
w=\frac{B}{Q_0}-a
  =\frac{(a-1)Z-n}{N-Z}.
\tag{4.7}
$$

Here $0\le w\le v\le j$. Indeed $Z\ge7n$ makes the numerator
nonnegative, while $Z\le pN$ and $N-Z\ge N(1-p)$ give
$w\le(a-1)p/(1-p)=v$. With $b=\lfloor w\rfloor$, set

$$
q_1=B-(a+b)Q_0,\qquad q_0=Q_0-q_1.
\tag{4.8}
$$

These are integers with $0\le q_1<Q_0$. Give $q_0$ core sources
degree $a+b$ and $q_1$ degree $a+b+1$, omitting a zero-count degree.
All requested degrees lie in $[a,m]$. In particular, if $b=j$,
then $w=j$ and $q_1=0$, so no source of degree $m+1$ is requested.

Assign their neighborhoods by reading consecutive blocks of the requested
lengths in the cyclic word of the $m$ core labels, continuing at the end
of the previous block. Every block has distinct labels because its length
is at most $m$. Every core label occurs in this prefix either
$\lfloor B/m\rfloor$ or $\lceil B/m\rceil$ times. Write
$D_i^C$ for these degrees and $\mu=B/m$. If
$\mu^*=Ny_C^*=N(a-p)/m$, then

$$
\mu\ge\mu^*-n/m\ge\mu^*-1,\qquad
d_i\ge D_i^C\ge\mu^*-2\ge N/4\quad(i\in C).
\tag{4.9}
$$

The final core sink $i_0$ also receives the $n$ connector incidences;
every other core sink keeps its assigned degree. The singleton counts
$t_d$ at tail sinks differ by at most one and sum to $Z-n$. Hence
their final degrees obey

$$
d_d=t_d+1\in\{\lfloor Z/n\rfloor,\lceil Z/n\rceil\},\qquad
d_d\ge Z/n-1\ge6>2.
\tag{4.10}
$$

There are exactly $Q_0+T_1+n=N$ sources, $m+n=s$ sinks, and
$B+T_1+2n=aN$ edges. Every source uses distinct sinks, so the graph
is simple and bipartite. Two core-source neighborhoods intersect
because both have size at least $a$ and $2a>m$. Every core sink
has positive $D_i^C$, by (4.9). Thus the entire core incidence graph
is connected. Each tail sink joins it through its designated connector,
and all singleton sources attach to these sinks, proving connectedness.

By enlarging $A$ if necessary, (4.9) and $N\ge8a^{3/2}$ give
$d_i\ge N/2-2>m$ at every core sink. Its incident sources have
degree at most $m$. At each tail sink the incident source degrees
are one or two and (4.10) is strict. This proves (1.3) for every
actual edge, and thus membership in the required graph class.

It remains to bound the quadratic energy with these final degrees.
The sum of the cubed regular core-source degrees is

$$
S=q_0(a+b)^3+q_1(a+b+1)^3=Q_0f(a+w).
$$

Since $f$ is increasing, $w\le v$, and
$Q_0\le N(1-p)+1$,

$$
S\le S^*+8a^3,\qquad S^*=N(1-p)f(a+v).
\tag{4.11}
$$

The regular core sources contribute at most $NS/(\mu^*-2)^2$.
Using $\mu^*\ge N/2$, $H_C^*\le32a^3$ and, for
$0\le x\le1/2$, $(1-x)^{-2}\le1+8x$, gives

$$
\frac{NS}{(\mu^*-2)^2}
\le (1+32/N)H_C^*+128a^3/N
\le H_C^*+2048a^3/N.
\tag{4.12}
$$

For the tail incidences, the $t_d$ singleton sources have squared
degree one and the connector has squared degree four. Their total
contribution is

$$
N\sum_{d\in D}\frac{t_d+4}{(t_d+1)^2}
=N\sum_{d\in D}\left(\frac1{d_d}+\frac3{d_d^2}\right).
\tag{4.13}
$$

Since $Z\ge7n$, (4.10) implies

$$
\sum_d\frac1{d_d}\le\frac{n^2}{Z-n}
\le\frac{n^2}Z+\frac{2n^3}{Z^2},\qquad
\sum_d\frac1{d_d^2}\le\frac{4n^3}{Z^2}.
$$

Also $Z\ge pN-1$ and $Z\ge pN/2$, so

$$
\begin{aligned}
N\sum_d\left(\frac1{d_d}+\frac3{d_d^2}\right)
&\le\frac{Nn^2}Z+\frac{14Nn^3}{Z^2}\\
&\le\frac{n^2}p+\frac{58n^3}{p^2N}\\
&\le H_D^*+\frac{232(R+1)^3}{v_0^2}\frac{a^{7/2}}N.
\end{aligned}
\tag{4.14}
$$

The remaining connector incidences, at $i_0$, contribute at most
$4Nn/(\mu^*-2)^2\le64n/N$. Adding (4.12)--(4.14) proves (4.3),
for example with

$$
C=2048+64(R+1)+232(R+1)^3/v_0^2.
\tag{4.15}
$$

Finally $W\le Q$ is Growing, Lemma 9.2. Every count and denominator
used above belongs to this one graph. No congruence condition on $N$
has been used. ∎

**Lemma 4.2 (Uniform parameters for every exact minimizing law).**
Fix $0<L\le R<\infty$. For all sufficiently large $a$, uniformly over
$L\le h/\sqrt a\le R$, every minimizing law of (1.2), after a label
permutation, has the comparison energy (4.2) with

$$
1\le j\le J_R,\qquad v_0\le v\le j,
\qquad v_0>0,
\tag{4.16}
$$

where $J_R$ and $v_0$ depend only on $L,R$. In particular at least one
such law exists and $H_{j,v}=M(a,h)$.

**Proof.** Use the exact attainment and full classification of Growing,
Theorem 15.5. Its active indices obey

$$
j\le J_R=\left\lceil4((\max\{R,4\})^2+10)\right\rceil.
$$

The minimizing law is $x^{j,p}$ in Growing, (15.2), with
$p\in I_j$ in (15.1). Its positive tail types are singletons of total
mass $p$, and its core cardinalities are $m-1,m$, with
$m=a+j$, $n=h+1-j$. Put

$$
v=\frac{(a-1)p}{1-p},\qquad p=\frac{v}{a+v-1}.
\tag{4.17}
$$

The interval $I_j$ maps to $j-1\le v\le j$ for $j\ge2$ and to
$0<v\le1$ for $j=1$. The conditional core mean is $a+v$, so its
third moment is precisely the interpolation $f(a+v)$ in (4.2).
The actual core marginal is $(a-p)/m$, and the actual tail
marginals equal $p/n$. Thus its energy is the cited $H_{j,v}$.

Only a positive lower bound on $v$ remains. Put $C_*=R^2+10$.
Growing, Theorem 7.2, bounds $M\le a^3+C_*a^2$ uniformly after
increasing the threshold. In each classified law, the core marginals
are at least $1/2$, whereas

$$
0<p/n\le \frac{J_R}{an}
\le\frac{2J_R}{L a^{3/2}}
\tag{4.18}
$$

for sufficiently large $a$; here $n=h+1-j\ge L\sqrt a/2$.
Consequently the threshold partition in Growing, Lemma 7.1, with
$C=C_*$, is exactly this law's core and singleton tail: its threshold
is $4C_*/a$. The event probability in that lemma is therefore this
same $p$. Equation (7.15) there gives

$$
ap\ge\frac{L^2}{8C_*},\qquad
v\ge(a-1)p\ge\frac{L^2}{16C_*}.
\tag{4.19}
$$

One may take $v_0=L^2/(16C_*)<1$. This uses the exact classification
as an existing result and supplies its uniform positive-parameter
interface; it does not repeat its optimization proof. ∎

**Corollary 4.3 (Exact-law upper transfer in every phase).** For fixed
$0<L\le R<\infty$ and all sufficiently large $a$ in that window,
Lemma 4.1 applies to any attaining branch of Growing, Theorem 15.5,
with constants depending only on $L,R$. It proves nonemptiness and
(1.7) for every integer $N\ge\lceil D_0a^{3/2}\rceil$.

**Proof.** Apply Lemma 4.2, then Lemma 4.1 with the fixed $J_R,v_0$
there. Since $H_{j,v}=M$, (4.3) is (1.7). The construction permits
$v$ at either adjacent-integer endpoint, at an interior constrained
minimum, or at $v=j$. At $v=j$ its rounded regular core sources
still have degree at most $m$, by (4.8). If exact adjacent branches
tie, either one supplies the same bound, using the same constants.
Thus no positive-window phase or boundary is omitted. ∎

## 5. Quantifiers and the normalized surplus

**Proof of Theorem 1.2.** Choose $A$ larger than the thresholds in
Proposition 3.1 and Corollary 4.3, and take $D_0\ge1$ from the latter.
Increase $C$ to cover both conclusions. Proposition 3.1 proves
(1.6) for every graph; Corollary 4.3 supplies a legal connected graph
at every budget in (1.5) and proves (1.7). Minimizing and dividing
by $a^2$ gives (1.8). All constants were chosen using only $L,R$;
no limit with fixed $a,h$ has entered their selection. ∎

**Corollary 5.1 (The uniform $\epsilon$ statement).** For every
$0<L\le R<\infty$ and $\epsilon>0$, there are positive finite
$A_\epsilon,D_\epsilon$, depending only on $L,R,\epsilon$, such that
all integers

$$
a\ge A_\epsilon,\qquad L\le h/\sqrt a\le R,\qquad
N\ge\lceil D_\epsilon a^{3/2}\rceil
\tag{5.1}
$$

have a nonempty graph class. Every graph in that class has
$W\ge M-\epsilon a^2$, and at least one has
$W\le M+\epsilon a^2$.

**Proof.** With the constants in Theorem 1.2, take

$$
A_\epsilon\ge\max\{A,(2C/\epsilon)^2\},\qquad
D_\epsilon\ge\max\{D_0,2C/\epsilon,\sqrt{2C/\epsilon}\}.
\tag{5.2}
$$

Then $C(a^{-1/2}+a^3/N^2)\le\epsilon$ and
$Ca^{3/2}/N\le\epsilon/2$ throughout (5.1). Apply (1.6)--(1.7).
The ceiling and the construction's floor counts impose no divisibility
subsequence. ∎

**Corollary 5.2 (Every jointly growing diluted sequence).** For every
integer sequence with

$$
a\longrightarrow\infty,\qquad
h/\sqrt a\longrightarrow\kappa\in(0,\infty),\qquad
N/a^{3/2}\longrightarrow\infty,
\tag{5.3}
$$

the graph class is eventually nonempty and

$$
\frac{V_N-M(a,h)}{a^2}\longrightarrow0,\qquad
\frac{V_N-B_0(a)}{a^2}\longrightarrow U(\kappa).
\tag{5.4}
$$

Here $U$ is exactly Growing, Theorem 7.2. Its formulas are

$$
\begin{aligned}
U(\kappa)&=2\sqrt2\,\kappa&& (0<\kappa\le\sqrt2),\\
F_j(\kappa)&=\kappa^2/j+4j-2,\\
U(\kappa)&=F_1(\kappa)&& (\sqrt2\le\kappa\le2\sqrt2),\\
U(\kappa)&=F_j(\kappa)&&
\left(2\sqrt{j(j-1)}\le\kappa\le2\sqrt{j(j+1)},\ j\ge2\right).
\end{aligned}
\tag{5.5}
$$

The formulas agree at $\sqrt2$ and at every adjacent cap crossing
$2\sqrt{j(j+1)}$.

**Proof.** Choose fixed $0<L<\kappa<R<\infty$. Eventually the
sequence satisfies (1.5), and both errors in (1.8) tend to zero.
Growing, Theorem 7.2, gives
$(M-B_0)/a^2\to U(\kappa)$, with the displayed phases and continuity.
Adding the two convergences proves (5.4), including each phase
boundary. ∎

## 6. Sources and remaining mathematical boundaries

**Attribution 6.1 (Inputs and scope).** The definitions and exact-law
results used here are those of Growing, Definitions 1.1 and 9.1,
Lemma 7.1 with its core estimate (7.19), Theorem 7.2, Proposition 3.2,
Lemma 9.2, Theorem 15.5, and Proposition 15.6. These repository results concern
mathematical prose in their declared domains. The nonlinear sublevel
estimate, nonlinear common-event certificate, uniform full-graph lower
transfer, bounded-degree integer-budget construction and their uniform
combination in this volume are repo-derived deductions. Finite Jensen
is used only for the explicitly convex scalar functions in Section 2;
no convexity of $H$ as a function of the joint law is a premise.

Growing, Theorem 9.4, supplies a uniform graph result under the
stronger sufficient budget $N\ge Da^5$. Growing, Section 11, concerns
the different scale $h/a^{3/2}$ in a fixed positive interval. Neither
result yields (1.5)--(1.8) by substituting a varying parameter into a
fixed-parameter constant. [Periodic, Theorem
1.3](CDSO_PERIODIC_CONNECTION_COST.md) supplies its sharper periodic
first correction and eventual source types for fixed high-ratio
integers $a,h$, with constants depending on that pair. Theorem 1.2
asserts uniform value transfer as all three integers grow and does
not replace those fixed-pair conclusions.

The law and graph domains in the capacity-crossovers,
incidence-moments, higher-capacity, sink-incidence and universal-vertex
volumes retain their stated capacity, density and fixed-parameter
conditions. Their fixed-capacity realization and graph comparison
results are not extrapolated to the present growing window.

**Citation 6.2 (Original normalization and the historical graph
question).** [1] A. M. Albalahi, S. Das, A. Ali, J. Barman and
A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*,
Discrete Mathematics Letters 16 (2025), 108--115,
DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176),
[arXiv:2510.24809v1](https://arxiv.org/html/2510.24809v1), §1,
defines the CDSO sum with the maximum endpoint degree and explicitly
drops the factor $1/\sqrt2$. This literature-attested definition
identifies (1.4) with twice the source count times the CDSO excess
above the edge count. No extremal theorem from [1] is a premise of
the bounds in this volume.

[2] A. M. Albalahi, *On Two Conjectures Concerning the Hyperbolic
Sombor Index and Its Counterpart*,
DOI [10.47443/dml.2026.217](https://doi.org/10.47443/dml.2026.217),
Proposition 2.1, states that no CDSO minimizer among connected graphs
of order $5\ell+7$ and cyclomatic number $\ell\ge1$ has maximum
degree $5\ell+6$. Thus the CDSO universal-vertex assertion of [1]
is a historical motivation with known counterexamples, rather than
an unresolved premise of the present transfer theorem. Theorem 2.2
of [2] concerns maxima. These finite-graph results do not supply
the uniform common-law-to-graph estimate (1.8).

**Open problem 6.3 (Unasserted finite and moving-window refinements).**
Determine the optimal sufficient dilution threshold and the behavior
when $N/a^{3/2}$ tends to a finite positive constant, including
possible nonemptiness obstructions. Determine a uniform finite-budget
correction, eventual optimal source types, or exact $V_N$ across all
low, interior and cap phases. Theorem 1.2 proves none of these
refinements. The estimates do not assert moving-window uniformity
when $h/\sqrt a\to0$ or $\infty$, or graph conclusions at transition
and other surplus scales. They concern precisely the bipartite,
connected, simple, strictly degree-oriented class (1.3); no lower
bound for all connected graphs at the same order and edge count
follows from this class restriction.

The possible full-text overlap with K. Zhao and X. Zhao,
*Extremal values with respect to vertex-degree-based topological
indices in unicyclic and bicyclic graphs*,
DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
remains unassessed. That paper is not an input theorem here, and
no worldwide priority assertion is attached to these deductions.

## 追加锚（本行以下为增补区）

## 7. Rooted incidence patterns at finite positive budgets

**Definition 7.1 (Tail patterns with core ports).** Write
$g(t)=2(\sqrt{1+t^2}-1)$. A rooted tail pattern consists of a finite
simple bipartite incidence graph with $n\ge1$ tail vertices and $q$
source vertices, together with a nonnegative integer $\ell_u$ at each
source. Every source has at least one tail neighbor. Put

$$
b_u=|N(u)|,\qquad k_u=b_u+\ell_u,\qquad
d_i=|N(i)|.
\tag{7.1}
$$

Require $k_u<d_i$ on every tail incidence, and require each connected
component of the incidence graph to contain a source with
$\ell_u>0$. The $\ell_u$ core ports represent distinct future core
neighbors of that source; they are not additional tail incidences.
Equivalently, joining all ports to one auxiliary root gives a connected
multigraph. No degree condition is imposed at this auxiliary root.
Define the two normalized quantities

$$
r=\frac qn,\qquad
c=\frac1n\sum_{ui}g(k_u/d_i).
\tag{7.2}
$$

Disjoint unions of patterns share the auxiliary root and are allowed.
Thus their pairs $(r,c)$ are combined with weights proportional to
their tail counts. These patterns are auxiliary objects; actual
simple graphs with the original prescribed budgets are constructed
in Theorem 11.1 below.

**Definition 7.2 (Finite incidence linear programs).** For an integer
$M\ge3$ use nonnegative variables $t_d$ for $2\le d\le M$,
$q_k$ for $1\le k<M$, and $z_{kd},w_{kd}$ for $1\le k<d\le M$.
Variables with other indices are zero. Put

$$
E_k=\sum_{d>k}(z_{kd}+w_{kd}),\qquad
Z_k=\sum_{d>k}z_{kd}.
$$

The constraints are

$$
\begin{gathered}
\sum_{d=2}^M t_d=1,\qquad
\sum_{k<d}z_{kd}=t_d,\qquad
\sum_{k<d}w_{kd}=(d-1)t_d,\\
q_k\le E_k\le kq_k,\qquad
Z_k\le(k-1)q_k.
\end{gathered}
\tag{7.3}
$$

For a feasible array set

$$
r=\sum_kq_k,\qquad
c=\sum_{k<d}(z_{kd}+w_{kd})g(k/d).
\tag{7.4}
$$

For $\alpha,\beta>0$ and $R>1$ let
$\mathcal L_M(\alpha,\beta;R)$ be the minimum of
$\alpha r+\beta c$ subject to (7.3) and $r\le R$, with value
$+\infty$ if infeasible. Define

$$
\mathcal L(\alpha,\beta;R)
=\inf_{M\ge3}\mathcal L_M(\alpha,\beta;R).
\tag{7.5}
$$

For $R\le1$ its value is defined as $+\infty$. The marked incidences
$z$ will be parent-to-child incidences of a rooted spanning tree.
In particular, the last inequality of (7.3) retains a joint
connectivity condition in addition to degree and incidence counts.

## 8. From connected patterns to arrays and back

**Theorem 8.1 (Exact incidence constraints and asymptotic realization).**
Every rooted pattern gives a feasible array (7.3) for some finite $M$,
with its actual pair (7.2). Conversely, every finite feasible array
is a limit of pairs of rooted patterns. For rational arrays the latter
patterns can have uniformly bounded source degrees, tail degrees and
core ports. The bounds may depend on the array. Consequently, for
$R>1$,

$$
\mathcal L(\alpha,\beta;R)
=\inf\{\alpha r+\beta c:
    (r,c)\text{ comes from a rooted pattern},\ r<R\}.
\tag{8.1}
$$

The same infimum results from replacing $r<R$ by $r\le R$.

**Proof.** Adjoin the root to a pattern and take a spanning tree,
oriented away from the root. Mark the parent incidence of each tail
vertex. A source of total degree $k$ has its own parent edge and
therefore at most $k-1$ marked tail incidences. It has $b$ tail
incidences with $1\le b\le k$. Counting, and dividing by $n$, gives
exactly (7.3), including one marked incidence at each tail vertex.
All degrees and all costs are those of the same pattern.

First consider a rational feasible array. If $q_k>0$, the pair

$$
(E_k/q_k,Z_k/q_k)
\tag{8.2}
$$

lies in the polygon
$1\le b\le k$, $0\le z\le b$, $z\le k-1$.
For $k=1$ this polygon is the point $(1,0)$. For $k\ge2$ its
vertices are integral: they occur among
$(1,0),(k,0),(k,k-1),(k-1,k-1),(1,1)$.
Triangulating the polygon expresses any rational point as a rational
convex combination of integral pairs $(b,z)$ in it. Thus sources of
degree $k$ can be assigned integer tail counts $b$ and marked counts
$z$, with $k-b$ core ports, in exactly the proportions (8.2).

Clear denominators. Make the prescribed numbers of sources and tail
vertices, give a degree-$d$ tail vertex one marked stub and $d-1$
unmarked stubs, and pair stubs according to $z_{kd},w_{kd}$.
This produces a bipartite multigraph with the prescribed degrees,
marks and port counts. Each source has at least one tail edge, and
every tail edge has $k<d$. The marked count at a source is at most
$k-1$.

Parallel edges can be removed without changing any normalized count.
Replace each vertex by $L$ copies indexed modulo $L$. For each
parallel class assign distinct shifts to its edges, and replace an
edge of shift $a$ by all edges from source copy $i$ to tail copy
$i+a$. Taking $L$ at least the largest parallel multiplicity gives
a simple incidence graph. Every copy has the original degree,
marked count and ports. In particular its cost is exactly replicated.

A component without a port contains a cycle. Indeed if it has $n_0$
tails, $q_0$ sources and $e_0$ edges, then all its sources have $b=k$.
Counting marked incidences gives

$$
n_0\le\sum_u(k_u-1)=e_0-q_0,
\tag{8.3}
$$

so it cannot be a tree. In each such component choose a nonbridge
edge. In $L'$ disjoint copies delete this edge in every copy, and
cyclically join its source endpoint in copy $i$ to its tail endpoint
in copy $i+1$. The component with the chosen edge deleted is
connected. The resulting cyclic join is therefore connected and
simple, preserves all degrees and marks, and contains all $L'$
copies. Add one new source with one core port and one incidence to
any tail vertex of this joined component. Its degree is two and
the chosen tail degree increases from $d$ to $d+1$. Every original
orientation inequality remains strict; the new inequality is
$2<d+1$. Here $d\ge3$: a degree-two tail could only meet
degree-one sources, which have no marked capacity in (7.3).

Components already containing ports need no alteration. There are
only finitely many component types before replication. Hence this
construction adds $O(1)$ sources and changes $O(1)$ tail costs as
$L'\to\infty$, while the number of tails grows linearly. It gives
rooted patterns whose pairs tend to (7.4). All their degrees and
ports are bounded by constants depending on the rational array.

General real feasible arrays are approximated by rational feasible
arrays. This follows, for example, by decomposing the finite rational
polyhedron (7.3) into rational faces and approximating the convex
coefficients within each face; the normalization is rational.
Thus their pairs are also limits of rooted-pattern pairs.

It remains to preserve a strict cap on $r$. There are rooted
patterns with $r$ arbitrarily close to one from above. For each
integer $t\ge2$, take $t$ tails and $t+1$ sources of degree $t$,
with all possible incidences between them. Add a degree-two source
with one core port and one incidence to a chosen tail. This is a
rooted pattern, all inequalities are strict, and

$$
r_t=1+2/t,\qquad
c_t=\frac{(t-1)(t+1)g(t/(t+1))
              +(t+1)g(t/(t+2))+g(2/(t+2))}{t}.
\tag{8.4}
$$

Given $R>1$, fix such a pattern with $r_t<R$. Mixing any finite
array with an arbitrarily small positive amount of this pattern
moves a pair with $r=R$ strictly below $R$, changing its cost by
arbitrarily little. A pair already below $R$ requires no change.
Rational approximation and the preceding realization then preserve
the strict inequality. The forward direction bounds every rooted
pattern from below by (7.5), and the converse gives the reverse
inequality in (8.1). The same mixing argument proves the last
assertion. ∎

## 9. Coercivity and a certified finite degree cutoff

**Lemma 9.1 (Tail moment and source-count bounds).** Put
$\gamma=2/(1+\sqrt2)$. Every finite feasible array in (7.3), and
every rooted pattern, satisfies $r>1$ and

$$
c\ge\frac{\gamma}{r(r-1)},\qquad
\sum_d t_d d^{1/3}\le(c r^2/\gamma)^{1/3}.
\tag{9.1}
$$

**Proof.** Write $e_{kd}=z_{kd}+w_{kd}$. For $t_d>0$ set

$$
u_d=\frac1{t_d}\sum_{k<d}\frac{e_{kd}}k,
\qquad c_d=\frac1{t_d}\sum_{k<d}e_{kd}g(k/d).
$$

There are $d$ incidences per tail of degree $d$. Since $k\le d-1$,

$$
u_d\ge\frac d{d-1}>1,\qquad
\sum_d t_d u_d=\sum_k E_k/k\le r.
\tag{9.2}
$$

On $0\le t\le1$, $g(t)\ge\gamma t^2$. Jensen applied to the
convex function $x\mapsto x^{-2}$, with incidence weights
$e_{kd}/(dt_d)$ and arguments $1/k$, gives

$$
c_d\ge\frac{\gamma d}{u_d^2}
\ge\frac{\gamma}{u_d(u_d-1)}.
\tag{9.3}
$$

The last step uses $d\ge u_d/(u_d-1)$ from (9.2).
The function $u\mapsto1/[u(u-1)]$ is decreasing and convex on
$u>1$. Jensen and (9.2) prove the first inequality in (9.1).
Also $d^{1/3}\le(c_d/\gamma)^{1/3}u_d^{2/3}$; summing and
applying Hölder proves the second one. In particular $r>1$.
Theorem 8.1 supplies the array of every rooted pattern, so the
same conclusions apply to its actual counts. ∎

**Theorem 9.2 (Finite linear programs with explicit error).** Fix
$\alpha,\beta>0$ and $R>1$. Choose $t\ge2$ with $r_t<R$ in
(8.4), and put

$$
\begin{gathered}
L_0=\alpha r_t+\beta c_t,\qquad C=(L_0+1)/\beta,\\
\delta_M=(C R^2/(\gamma M))^{1/3},\qquad
\varepsilon_M=
\frac{L_0\delta_M}{1-\delta_M}
\left(1+\frac R{R-r_t}\right).
\end{gathered}
\tag{9.4}
$$

For every integer $M\ge t+2$ with $\delta_M<1$,

$$
0\le\mathcal L_M(\alpha,\beta;R)
          -\mathcal L(\alpha,\beta;R)
\le\varepsilon_M.
\tag{9.5}
$$

In particular (7.5) is finite, and (9.5) evaluates it by finite
linear programs with an explicit error tending to zero.

**Proof.** The pattern (8.4) is feasible at cutoff $t+2$, so
$0\le\mathcal L\le L_0$. Take any finite feasible array with
$r\le R$ and objective at most $\mathcal L+\eta$, where
$0<\eta\le1$. Its cost $c$ is at most $C$. Delete every tail
degree $d>M$ and let $\delta$ be its total deleted mass.
Lemma 9.1 gives $\delta\le\delta_M$.

Retain the other edge variables. With their new row sums $E'_k,Z'_k$
set

$$
q'_1=E'_1,\qquad
q'_k=\max\{E'_k/k,Z'_k/(k-1)\}\quad(k\ge2).
\tag{9.6}
$$

These obey $q'_k\le q_k$, $q'_k\le E'_k$ and all the source
constraints. For $k\ge M$ their values vanish. Dividing all
retained variables by $1-\delta$ therefore gives a feasible
cutoff-$M$ array with

$$
r'\le\frac R{1-\delta},\qquad
\alpha r'+\beta c'\le
\frac{\mathcal L+\eta}{1-\delta}.
\tag{9.7}
$$

If $r'>R$, mix this array with (8.4), using the weight
$\theta=(r'-R)/(r'-r_t)$ on (8.4). Otherwise put $\theta=0$.
In either case the mixed array has $r\le R$ and

$$
0\le\theta\le
\frac{R\delta}{(1-\delta)(R-r_t)}.
$$

Its objective is at most
$(\mathcal L+\eta)/(1-\delta)+\theta L_0$.
Subtract $\mathcal L$, use $\mathcal L\le L_0$ and
$\delta\le\delta_M$, and let $\eta\downarrow0$.
This proves the upper inequality in (9.5). The lower inequality
is the definition (7.5). All cutoff problems with $r\le R$ are
compact when feasible: $q_k\le R$, $E_k\le kR$, and the remaining
variables are bounded by these row sums. Thus their minima exist. ∎

## 追加锚（本行以下为增补区）

## 10. The finite-budget value function

**Definition 10.1 (A finite set of core sizes and a universal value).**
For $\kappa,D>0$ put

$$
\alpha=2\kappa/D,\qquad \beta=D\kappa,\qquad
R_j=Dj/\kappa.
\tag{10.1}
$$

The one-tail rooted pattern with two degree-one sources and one
degree-two source having a core port has

$$
r_*=3,\qquad c_*=2g(1/3)+g(2/3).
$$

Define

$$
\begin{gathered}
j_0=\lfloor3\kappa/D\rfloor+1,\qquad
T_0=2j_0+3\alpha+\beta c_*,\qquad
J_0=\lceil T_0/2\rceil,\\
F(\kappa,D)=-2-\frac1{4D^2}
 +\min_{\substack{1\le j\le J_0\\R_j>1}}
       \{2j+\mathcal L(\alpha,\beta;R_j)\}.
\end{gathered}
\tag{10.2}
$$

This is a nonempty finite minimum of finite numbers: the index $j_0$
has $R_{j_0}>3$, and Theorem 9.2 applies to every $R_j>1$.
Equivalently the minimum can be taken over all positive integers,
since any $j>J_0$ has $2j>T_0$ and cannot improve the comparison
at $j_0$.

For each index in (10.2), choose $t_j$ and $M$ as in Theorem 9.2.
Replacing $\mathcal L$ by $\mathcal L_M$ gives an upper bound for
$F$; replacing it by $\mathcal L_M-\varepsilon_{M,j}$ gives a
lower bound. Their difference is at most
$\max_j\varepsilon_{M,j}\to0$. Thus (10.2) is specified by finite
linear programs and explicit error bounds, without a limit of the
original graph optima as part of its definition. The coefficients
$g(k/d)$ of those programs are explicit real algebraic numbers.

## 11. Exact integer graph budgets from every rooted pattern

**Theorem 11.1 (Original-graph realization of a finite pattern).**
Fix a rooted pattern with pair $(r,c)$ and an integer $j\ge1$.
Suppose $\kappa,D>0$ and $\kappa r/D<j$. On every integer sequence

$$
a\to\infty,\qquad h/\sqrt a\to\kappa,\qquad
N/a^{3/2}\to D,
\tag{11.1}
$$

there is, for every sufficiently large term, a graph in the full
class $\mathfrak G_N(a,h)$ of Definition 1.1 with

$$
\frac{W(G)-B_0(a)}{a^2}
\longrightarrow
2j-2+\frac{2\kappa r}{D}+D\kappa c-\frac1{4D^2}.
\tag{11.2}
$$

In particular this uses exactly $N$ sources and $aN$ edges at each
term, without a congruence restriction on $N$.

**Proof.** Set $m=a+j$ and $n=h+1-j$. For all sufficiently large
terms these are positive and sum to $s$. Make $\lfloor n/t\rfloor$
copies of the fixed pattern, where $t$ is its tail count. Supply the
remaining fewer than $t$ tails with copies of the one-tail pattern
in Definition 10.1. If $q$ is the resulting number of tail-touching
sources, $\tau$ the sum of their full degrees, and $\rho$ the sum
of their core ports, then

$$
\begin{gathered}
q=rn+O(1),\qquad \tau=O(n),\qquad \rho=O(n),\\
\sum_{ui:\ i\text{ tail}}g(k_u/d_i)=cn+O(1).
\end{gathered}
\tag{11.3}
$$

The constants depend only on the fixed pattern. Its source and
tail degrees remain bounded. Allocate its $\rho$ ports to distinct
core labels, even across different sources. This is possible since
$\rho=O(\sqrt a)<m$ eventually. Every source then has distinct
neighbors, and every core label receives at most one port.

There remain $Q=N-q$ sources and exactly $B=aN-\tau$ core incidences
to allocate to them. Put

$$
v=aq/N,\qquad w=B/Q-a=\frac{aq-\tau}{N-q}.
\tag{11.4}
$$

Here $v\to\kappa r/D$, $w=v+O(a^{-1})$, and eventually
$0<w<j$. Give these $Q$ sources degrees
$a+\lfloor w\rfloor$ and $a+\lfloor w\rfloor+1$, with exactly
$B-(a+\lfloor w\rfloor)Q$ of the latter degree. Both degrees
are at most $m$, and their sum is exactly $B$.

Assign these neighborhoods as consecutive blocks in the cyclic word
of the $m$ core labels, continuing each block where the previous one
ended. All labels in a block are distinct, and each core label has
regular degree $B/m+O(1)$. Adding ports preserves this estimate.
All regular neighborhoods have size at least $a$, so any two meet
when $2a>m$. Every core label occurs since $B/m\sim N$.
Thus the core incidence graph is connected. Each component of the
tail pattern has a port and hence joins it. This proves connectedness
of the entire graph.

The source and edge counts are $Q+q=N$ and $B+\tau=aN$.
The graph is simple and bipartite. At every core sink,
$d_i\sim N\gg a+j$; the bounded-degree pattern sources also
obey the strict core inequality. At tail sinks the original pattern
inequalities are unchanged. Thus this is a member of the exact
original graph class, not merely a law or a degree prescription.

For its core marginals, uniformly in the core label,

$$
y_i=\frac{B}{mN}+O(N^{-1})
    =1-j/a+o(a^{-1}).
\tag{11.5}
$$

The regular source degrees are adjacent integers with mean $a+w$;
their averaged cube differs from $(a+w)^3$ by $O(a)$. Since
$Q/N=1-v/a$, their contribution to the actual quadratic core
energy is therefore

$$
\begin{aligned}
H_C^{\rm reg}
&=(1+2j/a+o(a^{-1}))(1-v/a)
                      \{(a+w)^3+O(a)\}\\
&=a^3+(2j+2v)a^2+o(a^2).
\end{aligned}
\tag{11.6}
$$

The bounded-degree port incidences add $O(q/N)=o(1)$ to $H_C$.
Taylor expansion of $g(t)=t^2-t^4/4+O(t^6)$ on the core gives

$$
W_C=H_C-\frac1{4N^2}
     \mathbb E\left[K^4\sum_{i\in T\cap C}y_i^{-4}\right]
     +O(a^7/N^4)
=H_C-\frac{a^2}{4D^2}+o(a^2).
\tag{11.7}
$$

The quartic expectation is $(1+o(1))a^5$: regular sources have
$K=a+O(1)$, almost all their $a+O(1)$ neighbors are core labels,
their total mass tends to one, and (11.5) is uniform.
The tail contribution is exactly $N(cn+O(1))$ by (11.3).
Since $Nn/a^2\to D\kappa$, (11.6)--(11.7), followed by subtracting
$B_0=a^3+2a^2+a$, give (11.2). ∎

## 12. The full-class lower bound and the universal core correction

**Lemma 12.1 (Core expansion on every nonlinear sublevel).** Fix
$\kappa,D>0$ and a finite constant $C_0$. On any sequence (11.1),
every sequence of actual graphs satisfying
$W\le a^3+C_0a^2$ has the core and tail partition of Growing,
Lemma 7.1, with

$$
\begin{gathered}
m=a+j,\quad n=h+1-j,\quad 1\le j\le J,\quad
p=q/N=v/a,\quad 0<v\le j+O(a^{-1/2}),\\
\min_{i\in C}y_i\ge c_0>0,\qquad
\sum_{i\in C}(1-y_i)=O(1),\\
H_C\ge a^3+(2j+2v)a^2-O(a^{3/2}),\\
W_C=H_C-\frac{a^2}{4D^2}+o(a^2).
\end{gathered}
\tag{12.1}
$$

Here $q$ is the number of actual sources touching the tail, and
$J,c_0$ and the estimates are uniform over the indicated sublevel.
Its tail incidences and actual core-neighbor counts form a rooted
pattern. Its pair

$$
r=q/n,\qquad c=W_D/(Nn)
\tag{12.2}
$$

has both coordinates bounded, and $r$ is bounded away from one.

**Proof.** Lemma 2.1, which holds for every original graph, gives

$$
H\le a^3+\sqrt2\left(W-a^3+\frac{s^5}{4N^2}\right)
\le a^3+C_1a^2
\tag{12.3}
$$

for a fixed $C_1\ge1$, since $s/a\to1$ and $N/a^{3/2}\to D>0$.
The latter implication does not require $D\ge1$. Apply Growing,
Lemma 7.1, in a fixed positive window containing $\kappa$.
Its (7.7), (7.10), (7.13)--(7.14) and (7.19) give all the
core and event estimates in (12.1) except the nonlinear expansion.
In particular the denominators in $H_C$ are the original actual
marginals, rather than conditional marginals.

Every core edge has ratio $K/(Ny_i)=O(a/N)=O(a^{-1/2})$.
The same Taylor formula as in (11.7) applies uniformly, with
remainder $O(a^7/N^4)=O(a)$. Write $L=|T\cap C|$ and
$B=|T\cap\mathcal D|$. Bounded core deficit and the derived
positive core marginal floor give

$$
\sum_{i\in C}(y_i^{-4}-1)=O(1),\qquad
\mathbb E\left[K^4\sum_{i\in T\cap C}y_i^{-4}\right]
=\mathbb E K^5-\mathbb E[K^4B]+O(a^4).
\tag{12.4}
$$

Jensen and $K\le s=a+O(\sqrt a)$ imply
$a^5\le\mathbb E K^5\le s^4\mathbb E K
=a^5+O(a^{9/2})$. Also $B\le n=O(\sqrt a)$, so the second
term in (12.4) is $O(a^{9/2})$. Thus (12.4) is
$a^5+O(a^{9/2})$. Its quartic correction is
$a^2/(4D^2)+o(a^2)$, proving the last line of (12.1).

To obtain a rooted pattern, retain all sources touching the tail,
with their actual tail incidences and their actual numbers of core
neighbors as ports. Every such incidence preserves the strict
degree inequality, including the source's full degree. Every
tail component reaches the nonempty core because the original
graph is connected. Hence Definition 7.1 applies, even if the
core induced incidence graph itself has several components.

The bound on $v$ gives bounded $r=q/n$ since
$q=vN/a$ and $n\sim\kappa\sqrt a$. The lower estimate for $W_C$
and the upper estimate for $W$ imply $0\le W_D=O(a^2)$, so $c$
is bounded as well. Lemma 9.1 now gives a uniform positive lower
bound on $r-1$. This argument imposed no degree bound, marginal
floor, source type or connected-law hypothesis on the original
domain. ∎

**Proposition 12.2 (Lower limit over the full prescribed graph class).**
On every sequence (11.1), every sequence of graphs with
$W\le a^3+C_0a^2$ satisfies

$$
\liminf\frac{W-B_0(a)}{a^2}\ge F(\kappa,D).
\tag{12.5}
$$

**Proof.** Lemma 12.1 gives the lower estimate

$$
\frac{W-B_0}{a^2}
\ge2j-2+\frac{2an}{N}r+\frac{Nn}{a^2}c
                    -\frac1{4D^2}+o(1).
\tag{12.6}
$$

All $j,r,c$ on its right are bounded. Along a subsequence attaining
the lower limit, pass to a further subsequence with a fixed $j$
and convergent $r,c$. The inequality $v\le j+o(1)$ gives
$r\le R_j+o(1)$. Since $r$ is bounded away from one, necessarily
$R_j>1$.

If a term has $r>R_j$, mix its actual feasible array from
Theorem 8.1 with a fixed pattern (8.4) of ratio $r_t<R_j$ until
the ratio is $R_j$. The mixing weight tends to zero. Boundedness
of $r,c$ shows that this changes $\alpha r+\beta c$ by $o(1)$.
If $r\le R_j$ no repair is required. Consequently

$$
\alpha r+\beta c\ge\mathcal L(\alpha,\beta;R_j)-o(1).
\tag{12.7}
$$

The coefficients of $r,c$ in (12.6) tend to $\alpha,\beta$.
If $j\le J_0$, (12.7) and (10.2) prove (12.5). If $j>J_0$,
nonnegativity of $r,c$ gives a limiting right side at least
$2j-2-1/(4D^2)>T_0-2-1/(4D^2)\ge F$. This treats the full
sublevel, including source degrees or tail degrees tending to
infinity and arbitrarily small actual tail marginals. ∎

## 13. The universal finite positive budget limit

**Theorem 13.1 (All positive parameters and all integer sequences).**
Let $\kappa,D$ be arbitrary elements of $(0,\infty)$. For every
integer sequence (11.1), with $a\ge4$, $h\ge1$, $N\ge1$ and
$s=a+1+h$, the original class $\mathfrak G_N(a,h)$ is eventually
nonempty, and

$$
\frac{V_N(a,h)-a(a+1)^2}{a^2}\longrightarrow F(\kappa,D),
\tag{13.1}
$$

where the finite real number $F$ is exactly (10.2), with the
finite-linear-program bounds of Theorem 9.2. The class retains
all finite simple connected bipartite graphs with exactly the
prescribed part sizes and edge count, and strict source-to-sink
degree inequalities. No further source-cardinality restriction
or marginal lower bound is imposed. Formula (13.1) includes every
parameter boundary; no uniqueness of a minimizing index or pattern
is assumed.

**Proof.** Use the one-tail pattern of Definition 10.1 and $j=j_0$.
It has $\kappa r_*/D<j_0$. Theorem 11.1 therefore proves
nonemptiness at every sufficiently large term and provides an
upper bound $V_N\le a^3+C_0a^2$ with a fixed finite $C_0$.
At each such term the graph minimum is attained by finiteness.
Proposition 12.2 applies to any sequence of those actual minimizers
and gives the lower limit at least $F$.

Conversely, choose an index attaining the finite minimum in (10.2).
For any $\epsilon>0$, Theorem 8.1 gives a fixed rooted pattern
with $r<R_j$ and

$$
\alpha r+\beta c
\le\mathcal L(\alpha,\beta;R_j)+\epsilon.
$$

Theorem 11.1 realizes this fixed pattern at every sufficiently
large exact integer budget of the given sequence. Its limit
(11.2) is at most $F+\epsilon$. Hence the upper limit of the
graph minima is at most $F+\epsilon$. Letting $\epsilon\downarrow0$
proves (13.1). The argument takes limits only after fixing the
pattern, so it uses no fixed-parameter remainder with parameters
silently varying. ∎

**Corollary 13.2 (The finite-budget gap from the original law).**
On the same sequences,

$$
\frac{V_N(a,h)-M(a,h)}{a^2}
\longrightarrow F(\kappa,D)-U(\kappa),
\tag{13.2}
$$

with exactly the existing $U$ of Growing, Theorem 7.2, or (5.5).
Neither (13.1) nor (13.2) presupposes that this difference is
nonzero or has a specified sign.

**Proof.** Subtract Growing (7.20) from (13.1). Continuity of the
displayed existing $U$ gives the asserted law limit, including
its phase boundaries. ∎

## 14. Mathematical dependencies and remaining distinctions

**Attribution 14.1 (Scope of the finite-budget deductions).**
The graph and common-law domains in Definition 1.1 are unchanged.
Growing, Lemma 7.1, supplies the actual-law core partition and
quadratic core lower estimate used in Lemma 12.1; its proof gives
the needed bounded deficit and positive core marginal floor.
Lemma 2.1 supplies the full-graph nonlinear-to-quadratic sublevel
implication. Growing, Theorem 7.2, supplies only the law value
$U$ in Corollary 13.2. No exact-law classification or cap comparison
is rederived in Sections 7--13.

The rooted incidence constraints, their converse by common actual
patterns, the explicit degree cutoff, the nonlinear core coefficient
at finite positive $D$, and their matching exact-budget upper and
full-class lower limits are repo-derived deductions. Their proofs
use finite spanning trees, stub pairing and cyclic joins, finite
linear programming, Jensen, Hölder and the displayed Taylor
expansions. The limit function is determined by (7.3), (9.4)--(9.5)
and (10.2), independently of an extremal theorem from the external
literature. The original CDSO convention is the maximum-degree
denominator without $1/\sqrt2$ in [1, §1, p.109], as in (1.4).

Theorem 13.1 settles the finite-positive-ratio limit and eventual
nonemptiness portion of Open problem 6.3. It does not classify exact
finite-budget minimizers or give a smaller-order remainder, eventual
source types, a moving-$\kappa$ limit, or an extremum over all
connected graphs outside the prescribed bipartite domain. The
fixed-pair periodic correction of Periodic, Theorem 1.3, has different
quantifiers. The universal-vertex counterexamples in [2,
Proposition 2.1] concern a different original-graph question and
are not a premise of the finite-budget limit. The Zhao--Zhao
full-text overlap identified in Section 6 remains unassessed;
no global priority statement is attached to these deductions.

## 追加锚（本行以下为增补区）

## 15. Finite support, countable attainment and the all-degree dual

**Definition 15.1 (Finite attainment).** Retain exactly the marked
incidence constraints (7.3). A finite attainer for
$\mathcal L(\alpha,\beta;R)$ is an array at some finite cutoff, with
$r\le R$, whose objective equals (7.5). For integers $M\ge3$ define

$$
F_M(\kappa,D)=-2-\frac1{4D^2}
 +\min_{\substack{1\le j\le J_0(\kappa,D)\\R_j>1}}
       \{2j+\mathcal L_M(\alpha,\beta;R_j)\}.
\tag{15.1}
$$

All parameters and $J_0$ are exactly those of Definition 10.1;
infeasible branches have value $+\infty$. Finite attainment of the
envelope means $F_M=F$ for some finite $M$. Since the index set is
finite, this is equivalent to finite attainment of at least one
winning branch. The original law and graph domains are unchanged.

**Lemma 15.2 (Saturation at every finite optimum).** If a finite array
attains $L=\mathcal L(\alpha,\beta;R)$, with $\alpha,\beta>0$ and
$R>1$, then $E_k=kq_k$ for every $k$. Every active source row
therefore has unmarked mass at least $q_k>0$.

**Proof.** Lemma 9.1 gives $r>1$, hence $L>0$. Suppose a row $l$
has slack $s_l=lq_l-E_l>0$. Choose an integer $k\ge3$, exceeding
every source index of the array, with $\alpha/(k-1)<L/2$.
Choose an integer $d>k,l$, exceeding all its tail degrees, with

$$
\frac\alpha{k-1}
 +\beta\{g(k/d)+(d-1)g(l/d)\}<L.
\tag{15.2}
$$

This is possible since $g(x)\le x^2$. Before normalization, add
$t_d=\delta$, $z_{kd}=\delta$, $w_{ld}=(d-1)\delta$, and
$q_k=\delta/(k-1)$, taking $0<\delta<s_l/(d-1)$. The old row $l$
remains feasible. The new row has $E_k=Z_k=\delta$ and satisfies
$q_k\le E_k\le kq_k$ and $Z_k\le(k-1)q_k$. Every new incidence
has its source index strictly smaller than $d$. Dividing all
variables by $1+\delta$ gives a normalized feasible array with

$$
r'=\frac{r+\delta/(k-1)}{1+\delta}<r\le R.
$$

Its objective is strictly less than $L$ by (15.2), a contradiction.
Finally $E_k-Z_k\ge kq_k-(k-1)q_k=q_k$. ∎

**Theorem 15.3 (All-degree dual attainment).** For every
$\alpha,\beta>0$ and $R>1$, put $L=\mathcal L(\alpha,\beta;R)$.
There exist $\lambda\ge0$, a real $\ell$, $u_1=A=\alpha+\lambda$,
$v_1=0$, and nonnegative $u_k,v_k$ for all $k\ge2$, such that

$$
ku_k+(k-1)v_k=A\quad(k\ge2),\qquad \ell=L+\lambda R.
\tag{15.3}
$$

For every integer $d\ge3$ define

$$
\begin{aligned}
b_d&=\min_{1\le k<d}\{u_k+\beta g(k/d)\},\\
m_d&=\min_{2\le k<d}\{u_k+v_k+\beta g(k/d)\}.
\end{aligned}
$$

Then $\ell\le m_d+(d-1)b_d$ for every $d\ge3$. For any fixed
finite feasible comparison array $(r_b,c_b)$ with $r_b<R$, the
dual can be chosen with

$$
\lambda\le\frac{\alpha r_b+\beta c_b}{R-r_b}.
\tag{15.4}
$$

Every finite attainer has $\lambda(R-r)=0$. At every active tail
degree there is equality in the column inequality, and every
positive marked or unmarked entry attains its corresponding
minimum. Also

$$
\frac A k\le u_k+v_k\le\frac A{k-1}\quad(k\ge2).
\tag{15.5}
$$

**Proof.** The source-one constraint forces $Z_1=0$, hence $t_2=0$.
For $k\ge2$ the smallest admissible source variable is
$\max\{E_k/k,Z_k/(k-1)\}$, which is at most $E_k$; for $k=1$
it is $E_1$. Thus deleting the inequality $q_k\le E_k$ does not
change a finite LP value. If that inequality fails, reducing $q_k$
to this minimum restores it, decreases $r$, and decreases the
positive objective.

For each sufficiently large finite cutoff, ordinary finite LP
strong duality gives an optimum with objective
$\ell_M-\lambda_M R=\mathcal L_M$. The cap price is $\lambda_M\ge0$.
Pricing $E_k\le kq_k$ by $u_k\ge0$ and
$Z_k\le(k-1)q_k$ by $v_k\ge0$ gives
$ku_k+(k-1)v_k\le\alpha+\lambda_M$. Source one has price
$u_1=\alpha+\lambda_M$. Eliminating the two column prices gives
exactly the displayed minima and column inequalities for $d\le M$.
Increasing a row price preserves those inequalities, so its row
price inequality can be made an equality. The finite primal is
feasible with finite value by the comparison array and Theorem
9.2. Finite LP dual attainment therefore applies, without strict
incidence inequalities or a strict cap at the optimum.

Testing this dual against the comparison array gives

$$
\mathcal L_M+\lambda_M R=\ell_M
 \le\alpha r_b+\beta c_b+\lambda_M r_b.
$$

Since $\mathcal L_M\ge0$, this bounds $\lambda_M$ by (15.4).
The row price equalities then bound each coordinate $u_k,v_k$.
Take a convergent subsequence for $\lambda_M$, followed by a
diagonal subsequence for all row prices. As
$\mathcal L_M\downarrow L$, the limit has $\ell=L+\lambda R$.
Each fixed column inequality involves finitely many coordinates
and passes to the limit. This proves existence of the stated dual.

For every finite feasible array, its inequalities imply

$$
\ell\le
 \sum_{k,d}\{u_k(z_{kd}+w_{kd})+v_kz_{kd}\}+\beta c
 \le A r+\beta c.
\tag{15.6}
$$

The first inequality weights column inequalities by $t_d$; the
second uses the source inequalities. For an attainer the last
quantity is $L+\lambda r\le L+\lambda R=\ell$. Every inequality
is equality. All discarded terms are nonnegative, proving the
individual contact and cap statements. Finally (15.5) follows
from the nonnegative row prices and their equality in (15.3). ∎

The finite LP duality step is the standard affine case of
Boyd--Vandenberghe, *Convex Optimization*, §5.2.3, (5.26)--(5.27),
and §5.2.4, printed pp.226--227
([author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)).
Its affine refinement reduces the constraint qualification to
feasibility, and the finite objective here excludes $-\infty$.
Only this intermediate finite-dimensional fact is literature-attested.
The countable diagonal extension and saturation perturbation are
deductions for (7.3); no infinite-dimensional strong-duality theorem
is assumed.

**Corollary 15.4 (No fixed rooted pattern attains a branch infimum).**
For every rooted pattern with $r\le R$, where $R>1$ and
$\alpha,\beta>0$, one has
$\alpha r+\beta c>\mathcal L(\alpha,\beta;R)$.

**Proof.** The pattern has a positive total number $\rho$ of core
ports by Definition 7.1. Its actual array from Theorem 8.1 has
$\sum_k(kq_k-E_k)=\rho/n>0$. Some row has positive slack, so
Lemma 15.2 excludes equality. The array is feasible, which gives
the non-strict comparison and therefore the asserted strict one.
There is no assertion of a uniform positive gap over patterns. ∎

**Definition 15.5 (Countable incidence arrays).** Allow every index
$2\le d<\infty$ and $1\le k<d$, and impose exactly (7.3), with
the sums interpreted as nonnegative series. Require
$r=\sum_kq_k\le R$ and
$c=\sum_{k<d}(z_{kd}+w_{kd})g(k/d)<\infty$. In particular
$E_k\le kq_k<\infty$ for each fixed $k$. No extra incidence,
source-type or connected-pattern condition is imposed. These arrays
are an auxiliary completion of the finite programs; they do not
enlarge either original domain in Definition 1.1.

**Theorem 15.6 (Attainment in the countable completion).** For every
$\alpha,\beta>0$ and $R>1$,

$$
\min_{\text{countable feasible arrays}}
       \{\alpha r+\beta c\}
=\mathcal L(\alpha,\beta;R).
\tag{15.7}
$$

Every countable feasible array has finite feasible approximations
whose objectives converge to its objective, with the same cap $r\le R$.
The minimum in (15.7) exists. Neither assertion requires finite
support of a minimizer.

**Proof.** First fix a countable feasible array, and a finite
comparison array $(r_b,c_b)$ with $r_b<R$, supplied by (8.4).
For sufficiently large $M$ retain only columns $d\le M$, and put
$\delta_M=\sum_{d>M}t_d$. Then $\delta_M\to0$. Define $E'_k,Z'_k$
from the retained incidences and replace the retained source counts by

$$
q'_k=\min\{q_k,E'_k\}\quad(k\ge1).
\tag{15.8}
$$

Both terms in this minimum are at least $E'_k/k$, and, for
$k\ge2$, at least $Z'_k/(k-1)$. For $k=1$, $Z'_1=0$ and
$q'_1=E'_1$. Thus the counts satisfy all row constraints and
vanish for $k\ge M$. They increase to $q_k$ as $M\to\infty$,
because $E'_k\uparrow E_k\ge q_k$. Divide every
retained variable by $1-\delta_M$. The resulting finite array has
source ratio $r'_M\le R/(1-\delta_M)$ and objective at most
$(\alpha r+\beta c)/(1-\delta_M)$. If $r'_M>R$, mix it with the
comparison array with weight

$$
\theta_M=\frac{r'_M-R}{r'_M-r_b}
\le\frac{R\delta_M}{(1-\delta_M)(R-r_b)}.
\tag{15.9}
$$

Otherwise use $\theta_M=0$. Take the cutoff large enough to include
the comparison array. The mixture has $r\le R$ and objective at
most

$$
\frac{\alpha r+\beta c}{1-\delta_M}
 +\theta_M(\alpha r_b+\beta c_b).
\tag{15.10}
$$

The retained source and cost sums increase to $r,c$, respectively.
Normalization and mixing, whose weight tends to zero, therefore
give finite feasible objectives converging to $\alpha r+\beta c$.
Their upper excess is bounded by (15.10) minus that objective.
Consequently $\mathcal L\le\alpha r+\beta c$. Finite arrays are
themselves countable feasible arrays, so the two infima agree.

For existence, take finite feasible arrays with objectives tending
to $L=\mathcal L$, all at most $L+1$. Lemma 9.1 gives the uniform
tail estimate

$$
\sum_{d>M}t_d
\le M^{-1/3}
 \left(\frac{(L+1)R^2}{\beta\gamma}\right)^{1/3}.
\tag{15.11}
$$

Each source coordinate is at most $R$, and for each fixed $d$ the
incidence coordinates are bounded by $d$. Successive subsequences
and a diagonal choice therefore give coordinatewise limits of
$t,z,w$ and provisional source counts $\widetilde q_k$.
Equation (15.11) implies $\sum_dt_d=1$: a fixed finite initial
sum passes to the limit, and its omitted mass is uniformly bounded
by the right side of (15.11). Each column has finitely many source
indices, so its two equalities in (7.3) also pass to the limit.

For each fixed row, nonnegative partial sums give
$E_k\le k\widetilde q_k$ and
$Z_k\le(k-1)\widetilde q_k$. The lower constraint
$\widetilde q_k\le E_k$ need not pass to a coordinatewise limit.
Instead define
$q_1=E_1$ and $q_k=\max\{E_k/k,Z_k/(k-1)\}$ for $k\ge2$.
Then $q_k\le\widetilde q_k$, $q_k\le E_k$, and all row
constraints hold. For $k=1$, the limiting bound is
$E_1\le\widetilde q_1$ and $Z_1=0$, so the same conclusion holds.
Fatou's inequality, applied to the joint nonnegative objective
series, gives the following bounds. Explicitly, take any finite
set of source and incidence coordinates, pass its weighted sum to
the limit along the minimizing sequence, and then take the
supremum over these finite sets. Since $q_k\le\widetilde q_k$,
the result is

$$
\sum_kq_k\le R,\qquad
\alpha\sum_kq_k+
 \beta\sum_{k<d}(z_{kd}+w_{kd})g(k/d)\le L.
\tag{15.12}
$$

This is a countable feasible array. The first part of the proof
bounds its objective below by $L$, establishing (15.7) and
attainment. All limiting arguments concern explicit nonnegative
series; no countable-dimensional duality or compactness theorem
for an unspecified topology is used. ∎

**Corollary 15.7 (Saturation and contacts in every countable optimum).**
Every minimizer in (15.7) has $E_k=kq_k$ and
$E_k-Z_k\ge q_k$ for every $k$. It satisfies the cap and incidence
contact conclusions of Theorem 15.3 for every dual there.

**Proof.** For any countable feasible array, put
$\xi_d=t_d^{-1}\sum_{k<d}(z_{kd}+w_{kd})/k$ at positive columns.
Then $\xi_d\ge d/(d-1)>1$, and summing gives
$\sum_dt_d\xi_d=\sum_kE_k/k\le r$. Thus $r>1$.

Suppose an optimal array has row slack $s_l=lq_l-E_l>0$.
Use the perturbation of Lemma 15.2, taking any $k\ge3$ distinct
from $l$ with $\alpha/(k-1)<L/2$ and then $d>k,l$ satisfying
(15.2). Neither index need be absent from the countable array.
The increments in row $k$, namely
$(\Delta q_k,\Delta E_k,\Delta Z_k)
=(\delta/(k-1),\delta,\delta)$, themselves satisfy its homogeneous
row inequalities. Row $l$ uses less than its slack. The column
equalities are preserved before normalization, and all series stay
finite where required. Normalizing strictly decreases both $r$
and the objective, contradicting (15.7). Therefore all rows are
saturated, and subtracting the marked bound gives $E_k-Z_k\ge q_k$.

For the contact statements, (15.6) extends to a countable array by
summing nonnegative series. Indeed the total row-price sum is at
most $Ar<\infty$, and the cost sum is $\beta c<\infty$. For an
optimal array the complete chain is

$$
\ell\le
\sum_{k,d}\{u_k(z_{kd}+w_{kd})+v_kz_{kd}\}+\beta c
\le Ar+\beta c=L+\lambda r\le L+\lambda R=\ell.
\tag{15.13}
$$

Each inequality is equality. The omitted summands are nonnegative,
so every positive incidence realizes its corresponding column
minimum, every positive column has equality, and
$\lambda(R-r)=0$. ∎

## 16. Explicit support bounds for finite attainers

**Lemma 16.1 (Largest source degree).** For a finite attainer and any
dual from Theorem 15.3, let $K$ be its largest active source index.
With $\gamma=2/(1+\sqrt2)$,

$$
2\le K\le\max\left\{2,\frac{4\ell}{\beta\gamma},
                         \frac{48\ell^2}{A\beta\gamma^2}\right\}.
\tag{16.1}
$$

**Proof.** Marked mass is one and cannot use source one, so $K\ge2$.
Lemma 15.2 gives a positive unmarked entry $(K,d)$. Its contact
and $g(x)\ge\gamma x^2$ give

$$
\ell\ge(d-1)\beta g(K/d)
 \ge\frac{\beta\gamma K^2}{2d},\qquad
 d\ge\frac{\beta\gamma K^2}{2\ell}.
\tag{16.2}
$$

Every actual marked entry at this tail uses an index at most $K$,
and by (15.5) its marked price is at least $A/K$. If $K$ strictly
exceeded both nonconstant bounds in (16.1), then $d>2K$. The
admissible marked competitor $2K$ would have price at most

$$
\begin{aligned}
\frac A{2K-1}+\beta g(2K/d)
&\le\frac{2A}{3K}+\frac{4\beta K^2}{d^2}\\
&\le\frac{2A}{3K}+\frac{16\ell^2}{\beta\gamma^2K^2}
 <\frac A K.
\end{aligned}
$$

This contradicts marked contact. The estimates use $K\ge2$,
$d-1\ge d/2$, and $g(x)\le x^2$. Strictly exceeding both bounds
is impossible, proving (16.1) including its boundary cases. ∎

**Lemma 16.2 (Tail support).** Suppose a finite attainer and its dual
satisfy

$$
0<a_*\le A\le A^*,\quad 0<\beta\le B^*,\quad
 a_*\le\ell\le H^*,\quad K\le K^*,
$$

where $K^*\ge2$ is an integer. Define

$$
\begin{gathered}
p_* =\lceil4A^*/a_*\rceil+1,\\
d_* =\left\lceil\max\left\{
3,K^*+1,p_*+1,2p_*\sqrt{B^*/a_*},4B^*(K^*)^2/a_*
\right\}\right\rceil,\qquad
u_* =\frac{a_*}{4(d_*-1)}.
\end{gathered}
\tag{16.3}
$$

Then $u_k\ge u_*$ for $1\le k\le K^*$, and every active tail
has degree at most $1+H^*/u_*$.

**Proof.** In the all-degree column inequality at $d_*$, use $p_*$
as a marked competitor and any $k\le K^*$ as an unmarked competitor.
Both are admissible, and (15.5) gives

$$
\begin{aligned}
\ell
&\le u_{p_*}+v_{p_*}+\beta g(p_*/d_*)
 +(d_*-1)\{u_k+\beta g(k/d_*)\}\\
&\le\frac{a_*}{4}+\frac{a_*}{4}
       +\frac{a_*}{4}+(d_*-1)u_k.
\end{aligned}
$$

Here the last cost term is at most $B^*(K^*)^2/d_*\le a_*/4$.
Since $\ell\ge a_*$, this proves $u_k\ge u_*$. Every active tail
has equality in its column inequality and unmarked indices at
most $K^*$, so $\ell\ge(d-1)u_*$. This proves the tail bound,
without uniqueness of any contact or incidence minimizer. ∎

**Theorem 16.3 (Bounded source support and the infinite alternative).**
For any fixed $\alpha,\beta>0$, $R>1$, finite attainment of
$\mathcal L$ is equivalent to the existence of a countable optimum
with bounded source indices. For any dual from Theorem 15.3 put

$$
K_{\rm grow}=\max\left\{2,\frac{4\ell}{\beta\gamma},
                      \frac{192\ell^2}{A\beta\gamma^2}\right\}.
\tag{16.4}
$$

If a countable optimum has an active row $k>K_{\rm grow}$, it
has active rows $k_0=k,k_1,k_2,\ldots$ and positive tail columns
$d_0,d_1,d_2,\ldots$ with

$$
w_{k_nd_n}>0,\qquad z_{k_{n+1}d_n}>0,\qquad
k_{n+1}>\frac43k_n,\qquad
d_n\ge\frac{\beta\gamma k_n^2}{2\ell}.
\tag{16.5}
$$

Thus an unbounded optimal support has an unbounded incidence chain
of this specified kind. Existence of that alternative is not
asserted.

**Proof.** Finite attainment supplies a countable optimum with
bounded source indices. Conversely suppose a countable optimum
has largest active source index $K$. Corollary 15.7 supplies the
unmarked mass and contacts used in Lemma 16.1. Its proof does not
require a bound on the tail indices, only a largest source index:
choose a positive unmarked entry in row $K$ and compare its
marked minimum with source $2K$ at the same tail. It therefore
gives (16.1) here as well. Apply the proof of Lemma 16.2 with
$a_*=\alpha$, $A^*=A$, $B^*=\beta$, $H^*=\ell$ and this finite
$K^*=K$. Its column test bounds the finitely many $u_k$ below by
a common positive number. At every active tail, countable contact
then gives $\ell\ge(d-1)u_*$. Hence the tail indices are bounded
too, and the countable optimum is a finite attainer.

Now take an active $k>K_{\rm grow}$. Corollary 15.7 provides a
positive $w_{kd}$. Contact, (15.5), and $g(x)\ge\gamma x^2$ imply

$$
\ell\ge(d-1)\beta g(k/d)
\ge\frac{\beta\gamma k^2}{2d}.
\tag{16.6}
$$

Thus $d\ge\beta\gamma k^2/(2\ell)>2k$, so $2k$ is an admissible
marked competitor. Its marked price is at most

$$
\begin{aligned}
u_{2k}+v_{2k}+\beta g(2k/d)
&\le\frac{2A}{3k}+\frac{16\ell^2}{\beta\gamma^2k^2}\\
&<\frac{3A}{4k}.
\end{aligned}
\tag{16.7}
$$

Every actual marked index $j$ at that tail attains the minimum,
and its marked price is at least $A/j$. Therefore $j>4k/3$.
There is such an index since the column has positive mass and
one unit of marked incidence per tail. Its row is active, so the
same argument iterates. This proves (16.5).

The series $\sum_kq_k$ is finite, but this by itself does not
exclude an increasing chain whose positive row masses tend to
zero. Accordingly (16.5) supplies neither finite attainment nor
a counterexample to it. ∎

## 17. Uniformity reduces to pointwise finite attainment

**Theorem 17.1 (Explicit conditional endpoint bound).** Let

$$
\mathcal K=[\kappa_-,\kappa_+]\times[D_-,D_+],\qquad
0<\kappa_-\le\kappa_+<\infty,\quad0<D_-\le D_+<\infty.
$$

Use $c_*$ from Definition 10.1 and define

$$
\begin{gathered}
\alpha_-=2\kappa_-/D_+,\quad \alpha_+=2\kappa_+/D_-,\quad
\beta_-=D_-\kappa_-,\quad \beta_+=D_+\kappa_+,\\
j_b=\lfloor3\kappa_+/D_-\rfloor+1,\quad
T_b=2j_b+3\alpha_++\beta_+c_*,\quad J_b=\lceil T_b/2\rceil,\\
R_b=D_+J_b/\kappa_-,\quad
\eta=\frac{\beta_-\gamma}{T_bR_b},\quad
 t_b=\max\{2,\lceil4/\eta\rceil\},\quad r_b=1+2/t_b.
\end{gathered}
\tag{17.1}
$$

Let $c_b=c_{t_b}$ be exactly (8.4), and put

$$
\begin{gathered}
C_b=\alpha_+r_b+\beta_+c_b,\quad
\Lambda_b=2C_b/\eta,\quad A_b=\alpha_++\Lambda_b,\\
H_b=T_b+\Lambda_bR_b,\quad
K_b=\left\lceil2+\frac{4H_b}{\beta_-\gamma}
 +\frac{48H_b^2}{\alpha_-\beta_-\gamma^2}\right\rceil.
\end{gathered}
\tag{17.2}
$$

Apply (16.3) with $a_*=\alpha_-$, $A^*=A_b$, $B^*=\beta_+$,
$H^*=H_b$, $K^*=K_b$, and denote the resulting constants by
$d_b,u_b$. Define

$$
\widehat M_{\mathcal K}
=\max\{3,\lceil1+H_b/u_b\rceil\}.
\tag{17.3}
$$

For every $(\kappa,D)\in\mathcal K$,

$$
[\exists M\ge3:\ F_M(\kappa,D)=F(\kappa,D)]
\quad\Longrightarrow\quad
F_{\widehat M_{\mathcal K}}(\kappa,D)=F(\kappa,D).
\tag{17.4}
$$

More precisely, every finite attainer of any winning branch at this
point has tail degrees at most $\widehat M_{\mathcal K}$ and source
indices at most $K_b$. No stabilization of losing branches is assumed.

**Proof.** At any point, $T_0\le T_b$ and $J_0\le J_b$. For any
winning $j$, write $R=R_j$ and $L=\mathcal L(\alpha,\beta;R)$.
Then $L\le T_b$ and $R\le R_b$. Lemma 9.1, applied to every
finite feasible array before taking its objective infimum, gives

$$
T_b\ge L\ge\frac{\beta_-\gamma}{R(R-1)},
\qquad R-1\ge\frac{\beta_-\gamma}{T_bR_b}=\eta.
\tag{17.5}
$$

The comparison pattern (8.4) with $t=t_b$ has
$r_b\le1+\eta/2<R$ and objective at most $C_b$. Theorem 15.3
gives a dual with

$$
\lambda\le\Lambda_b,\quad
\alpha_-\le A\le A_b,\quad
\alpha_-\le\ell=L+\lambda R\le H_b.
\tag{17.6}
$$

For the lower bound, every feasible finite array has $r>1$, so
$L\ge\alpha\ge\alpha_-$ even when the infimum is not attained.
If this branch has a finite attainer, Lemma 16.1 bounds its largest
source index by $K_b$, and Lemma 16.2 bounds all its tail degrees
by $1+H_b/u_b$.

If $F_M=F$ at some finite cutoff, a branch attaining the finite
minimum in (15.1) is a winning branch of (10.2), and its finite
array attains $L$. The support bound just proved makes this array
feasible at $\widehat M_{\mathcal K}$. Hence
$F_{\widehat M_{\mathcal K}}\le F$, with the reverse inequality
following from $\mathcal L_M\ge\mathcal L$. This proves (17.4).
The choice of winning branch was arbitrary. No strict separation
of competing caps or contacts was used, so all ties, incidence
transitions and equal-endpoint rectangles are included. ∎

**Corollary 17.2 (A fixed-point obstruction suffices).** On $\mathcal K$,
one common finite cutoff gives exact equality everywhere if and only
if every point has finite envelope attainment. In that case (17.3)
is an explicit sufficient cutoff. If some point satisfies
$F_{\widehat M_{\mathcal K}}(\kappa,D)>F(\kappa,D)$, then at that
same fixed positive pair $F_M(\kappa,D)>F(\kappa,D)$ for every
finite $M\ge3$.

**Proof.** The forward direction is immediate and the reverse is
(17.4) with its common endpoint bound. At a point of strict
inequality, equality for any finite $M$ would contradict (17.4).
Neither existence nor nonexistence of such a point is asserted. ∎

## 18. Original-graph recovery and the remaining existence question

**Theorem 18.1 (Bounded tail recovery at a finitely attained point).**
With the rectangle and constants of Theorem 17.1, put

$$
P_{\mathcal K}=\max\{\widehat M_{\mathcal K},t_b+2\},\qquad
B_{\mathcal K}=P_{\mathcal K}+1.
\tag{18.1}
$$

Fix a point of $\mathcal K$ with finite envelope attainment. On
every original integer sequence with $a_n\ge4$, $h_n\ge1$, $N_n\ge1$, and

$$
a_n\to\infty,\quad h_n/\sqrt{a_n}\to\kappa,\quad
 N_n/a_n^{3/2}\to D,
\tag{18.2}
$$

there are graphs $G_n\in\mathfrak G_{N_n}(a_n,h_n)$ at all
sufficiently large terms such that

$$
\frac{W(G_n)-a_n(a_n+1)^2}{a_n^2}
\longrightarrow F(\kappa,D)=F_{\widehat M_{\mathcal K}}(\kappa,D).
\tag{18.3}
$$

For one fixed winning index $j$, these graphs can have an
$(a_n+j)$-sink core and $h_n+1-j$ tail sinks. Every tail degree
and full degree of a source touching the tail is at most
$B_{\mathcal K}$. The other source degrees lie between $a_n$ and
$a_n+j$. This bounds a recovery sequence, not every minimizer or
the large core sink degrees. Independently of finite attainment,
Theorem 13.1 already gives eventual nonemptiness and the full
original-graph minimum limit on every sequence (18.2).

**Proof.** Fix a finite attainer on a winning branch, whose cutoff
is at most $\widehat M_{\mathcal K}$ by Theorem 17.1. Mix it with
an arbitrarily small positive proportion of the comparison pattern
(8.4) at $t=t_b$. Its ratio becomes strictly smaller than $R_j$,
even when the attainer was on the cap. Its objective changes by
arbitrarily little, and the cutoff is at most $P_{\mathcal K}$.

Rational approximation in the finite rational polyhedron (7.3),
within its faces as in Theorem 8.1, preserves this strict cap and
approximates the objective. That theorem gives a fixed rooted
pattern with $r<R_j$ and objective at most $L+\epsilon$.
In its proof, stub pairing and simple covers preserve degrees;
attaching a port to a portless component adds a degree-two source
and increases one tail degree by one. Thus every resulting pattern
can have full source and tail degrees at most
$P_{\mathcal K}+1$, independently of its size or denominator.
Ports are bounded by the source full degree. This uses the actual
marked constraints, rather than only marginal degree counts.

Apply Theorem 11.1 with this pattern and $j$. Its strict assumption
is exactly $r<R_j=Dj/\kappa$. At every sufficiently large term it
constructs a finite simple connected bipartite graph with exactly
$N_n$ sources, $a_n+1+h_n$ sinks and $a_nN_n$ edges. The pattern
preserves $k_u<d_i$ on tail edges, and the actual large core degrees
give it on core edges. The leftover tails use the one-tail pattern
of Definition 10.1, with source degrees at most two and tail degree
three, within the same bound. Regular source degrees lie between
$a_n$ and $a_n+j$. Its limiting normalized value is at most
$F+\epsilon$.

Choose a fixed such pattern for each error $1/m$. On the given
integer sequence, choose increasing thresholds beyond which its
construction is valid and its normalized value is at most
$F+2/m$. Use pattern $m$ between successive thresholds. The degree
bound is independent of $m$, so it survives this diagonal choice,
while the thresholds may depend on the pair, sequence and patterns.
The upper limit is at most $F$, and Theorem 13.1 (or Proposition
12.2) gives the reverse lower limit over the full graph class.
This proves (18.3) with all exact budgets. No fixed rooted pattern
is asserted to attain the limit; Corollary 15.4 excludes exact
attainment of its branch infimum by such a pattern. ∎

**Open problem 18.2 (Exact finite sufficiency on every compact
rectangle).** Determine whether every
$\mathcal K=[\kappa_-,\kappa_+]\times[D_-,D_+]$ with positive
finite endpoints admits an integer $M_{\mathcal K}\ge3$, with an
explicit upper bound depending only on its four endpoints, such that

$$
F_{M_{\mathcal K}}(\kappa,D)=F(\kappa,D)
\qquad\text{for every }(\kappa,D)\in\mathcal K.
\tag{18.4}
$$

The function $F_M$ is exactly (15.1), with the same $J_0$ and
$R_j>1$ admissibility as (10.2), and with infeasible branches
assigned $+\infty$. The question includes all winning-cap ties,
incidence transitions and equal-endpoint rectangles.

By Theorems 16.3 and 17.1, (18.4) is equivalent to the following
pointwise assertion: at every $\kappa,D>0$, some winning branch
has a countable optimum with bounded source support. Every branch
already has a countable optimum by Theorem 15.6. An affirmative
answer to the bounded-support assertion makes (17.3) an explicit
endpoint-only choice in (18.4), and Theorem 18.1 then gives bounded
tail recovery on every original integer sequence (18.2).

A refutation requires a fixed positive compact rectangle
$\mathcal K$ such that for every integer $M\ge3$ some point of
$\mathcal K$ satisfies $F_M>F$. Corollary 17.2 makes this equivalent
to the existence of a fixed positive pair at which every countable
optimum of every winning branch has unbounded source support;
at that pair $F_M>F$ for all finite $M$. A losing branch with no
finite attainer, failure of one proof method, or approximate cutoff
stability does not meet this criterion.

Theorem 15.3 gives an attained all-degree dual, and Theorem 15.6
gives an attained countable primal. Corollary 15.7 gives exact
saturation and contacts. The increasing chains of Theorem 16.3
do not exclude summable positive source masses. None of these
statements proves bounded source support or produces a pair where
all winning branches lack it. Thus (18.4) and its quantified
negation both remain unresolved.

The saturation perturbation, countable primal attainment,
source-degree comparison, support-chain alternative, conditional
endpoint bound and bounded tail recovery are repo-derived from
(7.3) and the cited theorems of this volume. Finite LP duality is
attributed only in its intermediate role following Theorem 15.3.
The original-object bridge reuses Theorems 8.1, 11.1, 13.1 and
Proposition 12.2 with their full integer-sequence quantifiers.
There is no claim about all original minimizers, smaller-order
finite-budget errors, or connected graphs outside Definition 1.1.
The Zhao--Zhao full-text overlap in Section 6 remains unassessed;
no worldwide priority assertion is made.

## 追加锚（本行以下为增补区）

## 19. Finite total incidence on the countable optimal face

**Theorem 19.1 (High-row marked saturation and finite incidence).**
Fix $\alpha,\beta>0$, $R>1$, an attained dual from Theorem 15.3,
and any countable optimum from Theorem 15.6. Retain $A,\ell,u,v$
from (15.3), and put

$$
H_0=\left\lceil\max\left\{2,
             \frac{4\ell^2}{A\beta\gamma}\right\}\right\rceil,
\qquad W_k=\sum_{d>k}w_{kd}=E_k-Z_k.
\tag{19.1}
$$

Every active row satisfies

$$
u_k\le\frac{4\ell^2}{\beta\gamma k^2}.
\tag{19.2}
$$

Consequently, for $k>H_0$,

$$
v_k>0\quad\hbox{if }q_k>0,\qquad
Z_k=(k-1)q_k,\qquad W_k=q_k.
\tag{19.3}
$$

In particular the total incidence, rather than merely the tail
mass, is finite:

$$
\sum_d d t_d=\sum_k kq_k\le H_0R+2,
\qquad \sum_k W_k=\sum_d(d-1)t_d\le H_0R+1.
\tag{19.4}
$$

For a positive compact rectangle $\mathcal K$ from Theorem 17.1,
define, using exactly (17.1)--(17.2),

$$
H_{\mathcal K}
=\left\lceil\max\left\{2,
 \frac{4H_b^2}{\alpha_-\beta_-\gamma}\right\}\right\rceil.
\tag{19.5}
$$

Every countable optimum of every winning branch at every point of
$\mathcal K$ satisfies $\sum_d d t_d\le H_{\mathcal K}R_b+2$.
This conclusion does not assume finite attainment of that branch.

**Proof.** Saturation and Corollary 15.7 give $W_k\ge q_k>0$ in
an active row. Choose $d$ with $w_{kd}>0$. Its unmarked contact,
the nonnegativity of all marked prices, and $g(x)\ge\gamma x^2$
give

$$
\ell\ge(d-1)\{u_k+\beta g(k/d)\},\qquad
 d\ge\frac{\beta\gamma k^2}{2\ell}.
\tag{19.6}
$$

Here $d\ge3$ and $d-1\ge d/2$. Therefore
$u_k\le\ell/(d-1)\le2\ell/d$, proving (19.2).
For active $k>H_0$ this is strictly less than $A/k$.
The row equality $ku_k+(k-1)v_k=A$ implies $v_k>0$.
The equality of the nonnegative sums in (15.13) gives

$$
v_k\{(k-1)q_k-Z_k\}=0.
\tag{19.7}
$$

Thus the marked constraint is saturated at these rows; subtracting
it from $E_k=kq_k$ proves (19.3). Inactive rows have $q_k=Z_k=W_k=0$.
Since $\sum_kZ_k=1$, nonnegative summation now gives

$$
\begin{aligned}
\sum_k kq_k
&\le H_0\sum_{k\le H_0}q_k
   +\sum_{k>H_0}\frac{k}{k-1}Z_k\\
&\le H_0R+2.
\end{aligned}
$$

Tonelli's identity and saturation identify this sum with
$\sum_d d t_d$. Subtracting $\sum_dt_d=1$ gives the second
bound in (19.4). For the uniform assertion choose the dual with
(17.6) on the winning branch. Then $H_0\le H_{\mathcal K}$ and
$r\le R\le R_b$, proving the stated bound. No unique branch,
contact or strict inequality between competing caps is needed. ∎

## 20. An exact flow and dual-gap identity for the marked constraints

**Definition 20.1 (Incidence flow).** Let

$$
\mathcal A=\{(k,j,d):d\ge3,\ 1\le k<d,\ 2\le j<d\}.
$$

The index $k$ is unmarked and $j$ is marked; both refer to the
same tail degree $d$. For nonnegative $y=(y_{kjd})_{\mathcal A}$
with $\sum_{\mathcal A}y_{kjd}<\infty$, put

$$
\begin{gathered}
W_k=\sum_{j,d}y_{kjd},\qquad
I_1=0,\qquad
I_j=\sum_{k,d}\frac{y_{kjd}}{(j-1)(d-1)}\quad(j\ge2),\\
b_k=W_k-I_k,\qquad
\mathcal N(y)=\sum_{\mathcal A}\frac{y_{kjd}}{d-1},\\
\mathcal R(y)=\sum_k\left(I_k+\frac{b_k}{k}\right),\qquad
\mathcal C(y)=\sum_{\mathcal A}y_{kjd}
 \left\{g(k/d)+\frac{g(j/d)}{d-1}\right\}.
\end{gathered}
\tag{20.1}
$$

Only flows with $b_k\ge0$ are considered. The vector $b$ is the
injection. It is not an additional source type or an extra
constraint on either original domain.

**Proposition 20.2 (Exact saturated-array correspondence and gap).**
Saturated countable arrays satisfying (7.3), $E_k=kq_k$ and
$\sum_ddt_d<\infty$ are exactly the images of the flows in
Definition 20.1 with $\mathcal N(y)=1$. The correspondence preserves
$r=\mathcal R(y)$ and $c=\mathcal C(y)$. In particular, imposing
$\mathcal R(y)\le R$ preserves exactly the original cap on these
arrays, including equality.

For an attained dual from Theorem 15.3 define

$$
\begin{aligned}
p_{jd}&=\frac1{(j-1)(d-1)},\\
\Delta_{kjd}
&=u_k-p_{jd}u_j+A p_{jd}
 +\beta\left\{g(k/d)+\frac{g(j/d)}{d-1}\right\}
 -\frac\ell{d-1}.
\end{aligned}
\tag{20.2}
$$

Every $\Delta_{kjd}$ is nonnegative. For every normalized flow
with $\mathcal R(y)\le R$, the exact objective gap is

$$
\begin{aligned}
\alpha\mathcal R(y)+\beta\mathcal C(y)-L
={}&\sum_{\mathcal A}y_{kjd}\Delta_{kjd}
 +\sum_k b_k(A/k-u_k)\\
 &+\lambda\{R-\mathcal R(y)\}.
\end{aligned}
\tag{20.3}
$$

Hence such a flow gives an optimum if and only if all three
nonnegative terms on the right vanish. Equivalently, its positive
actions satisfy $\Delta_{kjd}=0$, its positive injection rows satisfy
$u_k=A/k$, and $\lambda\{R-\mathcal R(y)\}=0$.
Every countable optimum has a representing flow of this kind, with
$b_k=0$ for $k>H_0$.

**Proof.** Given a saturated array of finite total incidence, set

$$
y_{kjd}=\frac{w_{kd}z_{jd}}{t_d}\quad(t_d>0),
\qquad y_{kjd}=0\quad(t_d=0).
\tag{20.4}
$$

The column identities in (7.3) show

$$
\sum_jy_{kjd}=w_{kd},\qquad
\sum_ky_{kjd}=(d-1)z_{jd}.
\tag{20.5}
$$

Thus $\sum y=\sum W_k=\sum(d-1)t_d<\infty$ and
$\mathcal N(y)=1$. For $k\ge2$, $I_k=Z_k/(k-1)$.
The marked constraint and saturation imply $I_k\le W_k$, since
$Z_k\le(k-1)(W_k+Z_k)/k$ is exactly this inequality.
For source one, $Z_1=0$ and $q_1=W_1$. For every $k$,

$$
q_k=I_k+b_k/k.
\tag{20.6}
$$

This proves nonnegative injection and preservation of $r$.
Equation (20.5) proves preservation of $c$ as well. The product
in (20.4) is a way to pair the two types of incidence at one
column; it asserts no independence of original graph or law data.

Conversely, given a flow as stated, define

$$
\begin{gathered}
t_d=\frac1{d-1}\sum_{k,j}y_{kjd},\qquad
w_{kd}=\sum_jy_{kjd},\qquad
z_{jd}=\frac1{d-1}\sum_ky_{kjd},\\
z_{1d}=0,\qquad q_k=I_k+b_k/k.
\end{gathered}
\tag{20.7}
$$

The two column identities hold and $\sum_dt_d=1$.
For $k\ge2$, $Z_k=(k-1)I_k$ and
$E_k=W_k+(k-1)I_k=kq_k$; for $k=1$, $E_1=q_1=W_1$.
The assumption $b_k\ge0$ gives
$Z_k\le(k-1)q_k$, and $q_k\le E_k$ follows from saturation.
All incidence indices obey the actual strict inequality $k<d$.
Also $\sum_ddt_d=1+\sum y<\infty$. This proves the exact image
statement; different pairings $y$ can represent the same array.

For the dual identity use
$u_j+v_j=(A-u_j)/(j-1)$. The all-degree column inequality gives

$$
\ell\le u_j+v_j+\beta g(j/d)
 +(d-1)\{u_k+\beta g(k/d)\},
$$

which is $\Delta_{kjd}\ge0$. Moreover $0\le u_k\le A/k$.
Every series needed below is absolutely convergent: $\sum y<\infty$,
$0\le I_k,b_k\le W_k$, $u_k\le A$, $p_{jd}\le1/2$, and $g$
is bounded on $[0,1]$. Summing (20.2) therefore gives

$$
\sum y_{kjd}\Delta_{kjd}
=\sum_k u_kb_k+A\sum_k I_k
 +\beta\mathcal C(y)-\ell\mathcal N(y).
\tag{20.8}
$$

Add $\sum_kb_k(A/k-u_k)$, use (20.6) and $\mathcal N(y)=1$,
and finally use $A=\alpha+\lambda$, $\ell=L+\lambda R$.
This proves (20.3) and its equality criterion.
Theorem 19.1 permits (20.4) for every optimum. Equation (19.3)
gives $W_k=I_k=q_k$ for $k>H_0$, hence $b_k=0$ there. ∎

**Lemma 20.3 (Finite contact actions at a fixed source row).**
For any attained dual, $u_k>0$ for every fixed $k\ge1$.
If $\Delta_{kjd}=0$, then

$$
d\le1+\ell/u_k.
\tag{20.9}
$$

Consequently the set of contact actions $(j,d)$ at each fixed
unmarked row $k$ is finite, without any finite-attainment assumption.

**Proof.** Source one has $u_1=A>0$. For fixed $k\ge2$ choose
$m\ge2$ with $A/(m-1)<\ell/4$, and then choose an integer
$d>\max\{k,m,2\}$ so large that
$\beta m^2/d^2<\ell/4$ and $\beta k^2/d<\ell/4$.
Testing the column inequality with marked row $m$ and unmarked
row $k$, using $g(x)\le x^2$, gives
$\ell<3\ell/4+(d-1)u_k$. Thus $u_k>0$.
At a contact action the right side of the column test equals
$\ell$ and all its terms are nonnegative. In particular
$(d-1)u_k\le\ell$, which is (20.9). Both $j$ and $d$ are then
in finite sets. ∎

## 21. Two injection rows and the exact remaining support selection

**Theorem 21.1 (Two-injection reduction on every optimal face).**
Fix $\alpha,\beta>0$, $R>1$ and an attained dual.
There is a countable optimum whose representing flow has injection
on at most two rows, all at indices at most $H_0$ and satisfying
$u_k=A/k$. If $\lambda=0$, one injection row suffices.
The optimum can use only contact actions of any one prescribed
countable optimum. This reduction preserves the cap and the exact
objective; the initial optimum need not have finite support.

More precisely, for its set $S$ of active unmarked rows there are
probabilities $\pi_k(j,d)$ on the finite contact actions at $k\in S$,
with all their positive targets $j$ in $S$. Define on $\ell^1(S)$

$$
(P_\pi f)_j
=\sum_{k,d}p_{jd}\pi_k(j,d)f_k.
\tag{21.1}
$$

The flow has the representation

$$
W=\sum_{n=0}^{\infty}P_\pi^n b,\qquad
 y_{kjd}=W_k\pi_k(j,d),\qquad
\|P_\pi\|_{1\to1}\le\frac12.
\tag{21.2}
$$

**Proof.** Start with the flow (20.4) of the prescribed optimum.
Let $S=\{k:W_k>0\}$ and set $\pi_k(j,d)=y_{kjd}/W_k$.
Proposition 20.2 and Lemma 20.3 give the stated contact support
and its local finiteness. If $y_{kjd}>0$, then $I_j>0$ and
$W_j\ge I_j$, so $j\in S$. Each coefficient $p_{jd}$ is positive
and at most $1/2$, proving the norm bound by nonnegative summation.
The definitions give $I=P_\pi W$ and $W=b+P_\pi W$.
Iteration has a remainder of norm at most $2^{-n}\|W\|_1$,
proving (21.2). In particular there is no additional positive
summable solution with zero injection. The injection is nonzero,
as $W\ne0$ and $\|P_\pi\|<1$, and its support $B$ is a finite
subset of $\{1,\ldots,H_0\}$ with $u_h=A/h$.

For each $h\in B$, let $e_h$ be the unit vector at $h$, and put

$$
W^{h}=\sum_{n\ge0}P_\pi^ne_h,\qquad
 y^{h}_{kjd}=W^{h}_k\pi_k(j,d),\qquad
 n_h=\mathcal N(y^{h}).
\tag{21.3}
$$

These are nonnegative summable flows with injection $e_h$.
Here $0<n_h<\infty$: the term $W^{h}_h\ge1$ and the probability
row $\pi_h$ give positive normalized tail mass, while
$\|W^{h}\|_1\le2$ gives finiteness. Their normalized versions
$\bar y^{h}=y^{h}/n_h$ satisfy all incidence constraints, but their
ratios $\rho_h=\mathcal R(\bar y^{h})$ need not individually obey
the cap. All their actions and injections are contacts, so (20.8)
gives, without imposing a cap on each component,

$$
A\rho_h+\beta\mathcal C(\bar y^{h})=\ell.
\tag{21.4}
$$

The original flow decomposes exactly as

$$
y=\sum_{h\in B}\theta_h\bar y^{h},\qquad
\theta_h=b_h n_h>0,\qquad \sum_{h\in B}\theta_h=1.
\tag{21.5}
$$

Indeed (21.2) is linear in $b$, and $\mathcal N(y)=1$ gives the
last identity. In particular $r=\sum_h\theta_h\rho_h$.
If $\lambda=0$, choose a component with $\rho_h\le r\le R$.
Its objective is $\ell=L$ by (21.4), so it is a one-injection
optimum. If $\lambda>0$, the original $r=R$ by (20.3).
If some $\rho_h=R$, use that component. Otherwise choose one
$\rho_h<R$ and one $\rho_{h'}>R$, and mix their normalized flows
with the unique weights giving ratio $R$. Both normalization and
(21.4) are preserved, so the mixture has objective
$\ell-\lambda R=L$ and obeys the cap exactly. It has at most two
injection rows. Its positive actions were already positive in the
original flow. Individual components exceeding the cap have only
been used inside this feasible mixture. ∎

**Corollary 21.2 (Finite attainment as finite reachability with two
injection rows).** For a fixed branch and any fixed attained dual,
finite attainment of $\mathcal L(\alpha,\beta;R)$ is equivalent to
the following selection statement. There exist a set $S$ of source
indices, contact probabilities $\pi_k(j,d)$ as in Theorem 21.1,
and nonzero $b\ge0$ supported on at most two rows in
$\{1,\ldots,H_0\}$ with $u_k=A/k$, such that the flow (21.2)
satisfies

$$
\mathcal N(y)=1,\qquad \mathcal R(y)\le R,\qquad
\lambda\{R-\mathcal R(y)\}=0,
\tag{21.6}
$$

and the set reachable from $\operatorname{supp}b$ through positive
actions $k\longrightarrow j$ is finite. One injection row suffices
in this equivalence when $\lambda=0$.

**Proof.** For a finite attainer, choose its representing flow in
Theorem 21.1. Its source set and action set are finite, and the
reduction retains a subset of them. Conversely, for a selection as
stated, positivity of $p_{jd}$ and the nonnegative series (21.2)
show that $W_k>0$ exactly on the reachable set. If that set is
finite, Lemma 20.3 bounds all its positive action degrees $d$ by
a common finite integer. Thus $y$ has finite support. Proposition
20.2 reconstructs an actual finite array satisfying every constraint
in (7.3), and its gap (20.3) is zero. This is a finite attainer. ∎

## 22. Scope of the optimal-face reduction

Theorems 19.1 and 21.1 and Proposition 20.2 are repo-derived
consequences of the marked incidence constraints, the attained
primal and dual, and their nonnegative complementary-slackness sums.
The geometric-series solution in (21.2) and the two-point interpolation
in (21.5) are elementary occupation-flow tools. Their CDSO-specific
coefficients, incidence reconstruction and cap identity are given
explicitly above; no general finite-state approximation or
finite-moment support theorem is applied. The finite LP duality
input remains exactly the affine result attributed after Theorem
15.3. No additional literature theorem is a premise of the support
reduction, and no priority assertion is made. The Zhao--Zhao
full-text overlap in Section 6 remains unassessed.

For every $\kappa,D>0$, apply these statements with exactly
$\alpha=2\kappa/D$, $\beta=D\kappa$, $R=R_j=Dj/\kappa$ and the
admissible winning indices of (10.2). A countable optimal flow with
at most two injection rows exists on every such branch. What is
not established is the existence, on at least one winning branch,
of a selection in Corollary 21.2 with finite reachable set.
The norm bound $\|P_\pi\|\le1/2$, finitely supported injection,
finite total incidence and finitely many actions at each fixed row
do not in their proofs bound the union of rows reachable along
arbitrarily long positive paths. A feasible mixture of components
must still retain both normalization and (21.6); separately feasible
or separately optimal resource choices cannot replace that mixture.

Thus Open problem 18.2, including every positive compact rectangle,
all winning-cap ties and equal-endpoint rectangles, remains open,
as does its quantified negation. Corollary 21.2 gives an equivalent
support-selection obligation, not a stronger sufficient condition
substituted for the question. If that obligation holds on a winner
at every positive pair, Theorem 17.1 supplies exactly the explicit
endpoint-only cutoff (17.3), and Theorem 18.1 supplies the bounded
tail recovery. Neither conclusion is asserted unconditionally here.
A negative result still requires a fixed positive pair for which
all winning branches fail finite attainment, or the equivalent
fixed-compact/all-cutoff criterion of Open problem 18.2.

The original graph and actual common-law domains remain Definition
1.1. Independently of the unresolved finite-support selection,
Theorems 8.1, 11.1, 13.1 and Proposition 12.2 still give eventual
nonemptiness and the full original-graph limit on every integer
sequence $a_n\to\infty$, $h_n/\sqrt{a_n}\to\kappa>0$,
$N_n/a_n^{3/2}\to D>0$, with the prescribed exact counts and strict
edge inequalities. This reduction supplies no new bound on all
original minimizers and no single exactly attaining connected rooted
pattern. It changes neither $\mathcal X(a,h)$ nor $M(a,h)$ and
does not infer a sign for the gap in Corollary 13.2.

## 追加锚（本行以下为增补区）

## 23. Contact descent and exact two-row resource values

**Lemma 23.1 (Marked-price descent and the singleton entrance).**
Fix an attained dual from Theorem 15.3 and a representing flow of
any countable optimum. Write $s_k=u_k+v_k$ for $k\ge2$.
On every positive action $(k,j,d)$ with $k\ge2$,

$$
v_j\le v_k.
\tag{23.1}
$$

Consequently every unit-injection component of Theorem 21.1 rooted
at a row $h\ge2$ has finite support. Every positive action with
unmarked row one has marked row two, and its degree satisfies

$$
j=2,\qquad d^2<6\beta/A.
\tag{23.2}
$$

These conclusions apply to the prescribed optimum and its positive
actions; no cap feasibility of a normalized component is assumed.

**Proof.** Unmarked and marked contact at the same tail give

$$
u_k+\beta g(k/d)\le u_j+\beta g(j/d),\qquad
s_j+\beta g(j/d)\le s_k+\beta g(k/d).
$$

Subtracting yields (23.1). If $h\ge2$ is an injection row,
$u_h=A/h$ by (20.3), so the row equality gives $v_h=0$.
Descent and nonnegativity then force $v_k=0$ at every row reachable
from $h$. All these rows are active in the prescribed optimum.
Theorem 19.1 places them at indices at most $H_0$, since its active
rows above $H_0$ have strictly positive $v_k$. Lemma 20.3 bounds
all their action degrees. The unit-injection component therefore
has finite support. This conclusion concerns support; its normalized
resource value need not lie below $R$.

For an action from row one, unmarked contact permits the competitor
two and gives

$$
s_2=A-u_2\le\beta\{g(2/d)-g(1/d)\}.
\tag{23.3}
$$

Here $s_2\ge A/2$. If $d\ge4$, strict convexity of $g$ gives
$2g(2/d)-g(1/d)<g(3/d)$. Thus

$$
s_2+\beta g(2/d)
\le\beta\{2g(2/d)-g(1/d)\}
<\beta g(3/d)\le s_j+\beta g(j/d)\quad(j\ge3).
$$

Only row two can be marked. At $d=3$ it is the only admissible
marked row as well. Finally $g'(x)=2x/\sqrt{1+x^2}<2x$ for $x>0$,
so $g(2/d)-g(1/d)<3/d^2$. Together with (23.3) this proves
(23.2). All comparisons use the exact nonlinear cost. ∎

**Proposition 23.2 (An exact pair of tail degrees).** For integers
$d,e\ge3$ there is a normalized finite flow using just the actions
$(1,2,d)$ and $(2,2,e)$, with injection only at row one. Its
resource and cost are

$$
\begin{aligned}
r_{de}&=1+\frac{(d-1)(e-2)}{e-1}
       =d-\frac{d-1}{e-1},\\
c_{de}&=\frac{(d-1)(e-2)g(1/d)
                 +(e-2)g(2/d)+e g(2/e)}{e-1}.
\end{aligned}
\tag{23.4}
$$

It satisfies every original incidence constraint (7.3), including
when $d=e$. More generally, every normalized finite flow supported
on actions $(1,2,d)$ and $(2,2,e)$, with injection only at one,
is a convex combination of these normalized pair flows. The
combination preserves the actual $r$ and $c$ simultaneously.

**Proof.** Set

$$
y_{12d}=\frac{(d-1)(e-2)}{e-1},\qquad y_{22e}=1,
\tag{23.5}
$$

and all other actions to zero. Then $W_2=I_2=1$,
$b_1=W_1=y_{12d}$, $b_k=0$ for $k\ge2$, and
$\mathcal N(y)=(e-2)/(e-1)+1/(e-1)=1$.
Proposition 20.2 proves feasibility and gives (23.4). In its
reconstructed array $q_1=y_{12d}$, $q_2=1$ and $Z_2=1$;
in particular the marked constraint in row two is an equality.
Both actions have the strict actual incidence inequality.
When $d=e$, the two actions have different unmarked rows and their
column contributions add, with no change to these identities.

For the general flow, write $a_d=y_{12d}$ and $b_e=y_{22e}$.
Since $b_2$ as an injection coordinate is zero, its row balance and
normalization give

$$
\sum_e b_e=W_2=I_2=\mathcal N(y)=1,\qquad
\sum_d\frac{a_d}{d-1}=1-B,\quad
B=\sum_e\frac{b_e}{e-1}\le\frac12.
\tag{23.6}
$$

Define probabilities $\eta_d=a_d/\{(d-1)(1-B)\}$.
The weights $\theta_{de}=\eta_d b_e$ sum to one.
The mixture of (23.5) with these weights has row-two action mass
$b_e$ and row-one action mass

$$
\sum_e\theta_{de}\frac{(d-1)(e-2)}{e-1}
=\eta_d(d-1)(1-B)=a_d.
$$

It is the original flow itself. Linearity of the three functionals
in (20.1) proves simultaneous preservation of normalization,
resource and cost. A component can exceed a specified cap; only
a feasible final mixture can be used under that cap. ∎

## 24. Exact finite continuation in an inactive-cap region

Throughout this section put $t=\sqrt{\beta/\alpha}$ and
$L=\mathcal L(\alpha,\beta;R)$. The hypotheses here restrict a
region of the original parameter space; they do not replace the
all-positive quantifiers of Open problem 18.2.

**Proposition 24.1 (A comparison interval with a slack actual cap).**
If $t\ge128$ and $R>2t+6$, then

$$
\alpha(2t-1/12)\le L\le\alpha(2t+6).
\tag{24.1}
$$

Every countable optimum has $r<R$. Every attained dual has
$\lambda=0$, $A=\alpha$ and $\ell=L$.

**Proof.** The exact identity $g(x)+g(x)^2/4=x^2$, together with
$g(x)\le x^2$, gives

$$
g(x)\ge\frac{x^2}{1+x^2/4}.
\tag{24.2}
$$

Consider the all-degree dual candidate
$u_k=\alpha/k^2$ for $k\ge1$ and $v_k=\alpha/k$ for $k\ge2$,
with $v_1=0$ and $\lambda=0$. Its row equalities hold.
For any $k<d$ put $z=k^2/(d^2+k^2/4)>0$. Then

$$
\begin{aligned}
u_k+\beta g(k/d)
&\ge\frac\alpha{k^2}+\beta z\\
&=\frac\alpha{d^2z}+\beta z-\frac\alpha{4d^2}
 \ge\frac{2\sqrt{\alpha\beta}}d-\frac\alpha{4d^2}.
\end{aligned}
$$

Since $m_d\ge b_d$, the column expression is at least
$d b_d\ge2\sqrt{\alpha\beta}-\alpha/(4d)$.
For $d\ge3$ this is at least $\alpha(2t-1/12)$.
The candidate with that value of $\ell$ is dual feasible.
The weak-duality calculation (15.6) proves the lower bound in
(24.1); dual attainment for this particular candidate is not used.

For the upper bound choose $d=\lceil t\rceil$ and $e=4d$ in
Proposition 23.2. Its resource is $r_{de}<d\le t+1<R$.
Using $g(x)\le x^2$ in its exact cost gives

$$
c_{d,4d}\le\frac1d+\frac4{d^2}+\frac6{(4d)^2}
<\frac1d+\frac5{d^2}.
$$

Here $e/(e-1)\le3/2$. Consequently its objective is at most
$\alpha d+\beta/d+5\beta/d^2\le\alpha(2t+6)$.
This is one actual normalized feasible array, not independently
chosen resource and cost estimates. Every optimum now has
$r\le L/\alpha\le2t+6<R$. Corollary 15.7 gives
$\lambda(R-r)=0$ for every attained dual, so $\lambda=0$.
The other identities follow from (15.3). ∎

**Lemma 24.2 (Quantitative prices and row-two continuation degrees).**
Under the hypotheses of Proposition 24.1, fix any attained dual
and any countable optimum. For every $k\ge2$,

$$
\frac{1-4/(3t)}{k^2}\le\frac{u_k}{\alpha},
\qquad
\frac{u_k}{\alpha}\le\frac{(1+12/t)^2}{k^2}
\quad\text{if row }k\text{ is active}.
\tag{24.3}
$$

Every representing optimal flow has injection only at row one.
If a positive action has unmarked row two and tail degree $d$,
then, with $x=d/(4t)$,

$$
\frac t2<d<9t,\qquad |x-1|<\frac8{\sqrt t}.
\tag{24.4}
$$

**Proof.** To bound $u_k$ below, test the all-degree column
inequality at $D_k=\lceil tk^2\rceil$, using marked row two and
unmarked row $k$. Both are admissible. Since
$s_2=\alpha-u_2\le\alpha$ and $g(z)\le z^2$,

$$
\frac\ell\alpha
\le1+\frac{4t^2}{D_k^2}
 +(D_k-1)\frac{u_k}{\alpha}
 +\frac{t^2k^2}{D_k}.
$$

The lower bound (24.1) therefore gives

$$
(D_k-1)u_k/\alpha
\ge t-13/12-4/k^4\ge t-4/3.
$$

Because $D_k-1<tk^2$ and the right side is positive, this proves
the first bound in (24.3), with a weak inequality as stated.

For an active $k\ge2$, choose a positive unmarked incidence at
some $d$. Contact, $g(z)\ge\gamma z^2$, $d-1\ge d/2$ and
$\ell/\alpha\le2t+6\le3t$ give

$$
d\ge\frac{\beta\gamma k^2}{2\ell}
\ge\frac{\gamma tk^2}{6}>\frac{tk^2}{8}.
\tag{24.5}
$$

The last step uses $\gamma>3/4$. Put $q=u_k/\alpha$;
the dual row equality gives $q\le1/k$. The exact Taylor lower
bound $g(z)\ge z^2-z^4/4$ on $[0,1]$ gives

$$
\begin{aligned}
\frac\ell\alpha
&\ge(d-1)\{q+t^2g(k/d)\}\\
&\ge dq+\frac{t^2k^2}d-q
       -\frac{t^2k^2}{d^2}-\frac{t^2k^4}{4d^3}\\
&\ge2tk\sqrt q-\frac1k-\frac{64}{k^2}
                         -\frac{128}{tk^2}
\ge2tk\sqrt q-17.
\end{aligned}
\tag{24.6}
$$

Indeed $k\ge2$ and $t\ge128$ bound the discarded terms by
$1/2+16+1/4<17$. It follows that
$2tk\sqrt q\le2t+23$, proving the upper bound in (24.3).

For a positive injection at $k\ge2$, (20.3) requires
$u_k=\alpha/k$. Equation (24.3) would give
$k\le(1+12/t)^2<2$, a contradiction. The nonzero injection is
therefore supported only at one. This uses the actual optimal-flow
identity, without substituting a separately normalized component.

For an action from row two, (24.5) gives $d>t/2$.
Write $a_0=1-4/(3t)$. From $u_2/\alpha\ge a_0/4$ and
$(d-1)u_2\le\ell$,

$$
d\le1+\frac{4(2t+6)}{a_0}<9t,
$$

where the last inequality holds for $t\ge128$.
The same Taylor lower bound, now just for row two, gives

$$
\begin{aligned}
\frac\ell\alpha
&\ge\frac{a_0(d-1)}4
       +t^2(d-1)\left(\frac4{d^2}-\frac4{d^4}\right)\\
&\ge t\left(a_0x+\frac1x\right)
       -\frac{a_0}4-\frac{4t^2}{d^2}-\frac{4t^2}{d^3}\\
&\ge t\left(a_0x+\frac1x\right)-17.
\end{aligned}
$$

The discarded terms are at most $1/4+16+32/t<17$.
Hence $a_0x+1/x\le2+23/t$. As $x<9/4$, it follows that
$x+1/x<2+26/t$, and thus

$$
(x-1)^2=x(x+1/x-2)<\frac{(9/4)26}{t}<\frac{64}{t}.
$$

This proves (24.4). The inequalities remain valid when tail or
source contacts tie. ∎

**Theorem 24.3 (Exact finite continuation and an attained resource
formula).** Suppose

$$
\alpha,\beta>0,\qquad t=\sqrt{\beta/\alpha}\ge10^{12},
\qquad R>2t+6,
\qquad M_t=\lceil9t\rceil.
\tag{24.7}
$$

Every countable optimum has source support exactly $\{1,2\}$
and tail support at degrees at most $M_t$. In particular

$$
\begin{aligned}
\mathcal L_{M_t}(\alpha,\beta;R)
&=\mathcal L(\alpha,\beta;R)\\
&=\min_{3\le d,e\le M_t}
       \{\alpha r_{de}+\beta c_{de}\}.
\end{aligned}
\tag{24.8}
$$

The $r_{de},c_{de}$ are exactly (23.4), without replacing $g$ by
a quadratic cost. Every minimizing pair in (24.8) has $r_{de}<R$.
There exists an optimum equal to one of these normalized pair
arrays. This is finite-array attainment, not exact attainment by
one connected rooted pattern.

**Proof.** Fix a countable optimum, an attained dual and its
representing flow. Lemma 24.2 leaves only injection at one, and
Lemma 23.1 makes every positive action from one target two.
It remains to prove that every positive action from two also
targets two. Consider such an action $(2,j,d)$ and put $x=d/(4t)$.
The target row $j$ is active because it has positive marked
incidence. Equations (24.3)--(24.4) imply

$$
\begin{gathered}
999/1000<x<1001/1000,\qquad
1-4/(3t)\ge1-1/10000,\qquad
(1+12/t)^2\le1+1/10000,\\
\frac{s_2+\beta g(2/d)}\alpha
\le\frac34+\frac1{40000}
       +\frac14\left(\frac{1000}{999}\right)^2
<\frac{1001}{1000}.
\end{gathered}
\tag{24.9}
$$

For an active marked competitor $j\ge2$, (24.3) gives

$$
\frac{s_j}{\alpha}
=\frac{1-u_j/\alpha}{j-1}
\ge\frac{j+1}{j^2}-\frac1{10000j^2(j-1)}.
\tag{24.10}
$$

For $j=3,4$, Taylor's lower bound gives

$$
\frac{\beta g(j/d)}\alpha
\ge\frac{j^2}{16x^2}-\frac{j^4}{1024t^2x^4}
>\frac{j^2}{16}\left(\frac{1000}{1001}\right)^2
   -\frac1{1000000}.
\tag{24.11}
$$

The error bound uses $t\ge10^{12}$ and $x>999/1000$.
Thus the marked cost at three is strictly larger than

$$
\frac49-\frac1{180000}
 +\frac9{16}\left(\frac{1000}{1001}\right)^2
 -\frac1{1000000}>\frac{201}{200},
$$

and at four it is strictly larger than

$$
\frac5{16}-\frac1{480000}
 +\left(\frac{1000}{1001}\right)^2
 -\frac1{1000000}>\frac{13}{10}.
$$

All these costs are divided by $\alpha$.
For $j\ge5$, use $s_j\ge0$, $\gamma>4/5$, and $g(z)\ge\gamma z^2$:

$$
\frac{s_j+\beta g(j/d)}\alpha
\ge\frac{\gamma j^2}{16x^2}
>\frac45\frac{25}{16}
       \left(\frac{1000}{1001}\right)^2>\frac65.
$$

Each lower bound exceeds the upper bound for marked row two in
(24.9). A positive marked contact cannot have $j\ge3$.
This proves the exact $2\longrightarrow2$ continuation.

By the resolvent (21.2), the active rows are precisely those
reachable from the injection. The only reachable rows are one
and two, and both are active. Every action from two has $d<9t$
by Lemma 24.2. Every action from one satisfies
$(d-1)\alpha\le\ell\le\alpha(2t+6)$, hence
$d\le2t+7<9t$. There are therefore only finitely many positive
actions. Proposition 20.2 reconstructs a finite optimal array at
cutoff $M_t$, proving the first equality in (24.8).

Proposition 23.2 decomposes this normalized optimal flow into
normalized pair flows with $3\le d,e\le M_t$. Since $\lambda=0$,
the weak-duality inequality (15.6) gives
$L\le\alpha r_{de}+\beta c_{de}$ for every pair flow, even before
imposing its cap. The mixture has objective $L$, so every pair
with positive mixture weight has objective exactly $L$.
At least one such pair exists. Conversely every pair in the
finite displayed minimum has objective at least $L$, proving
the second equality. A minimizing pair obeys
$r_{de}\le L/\alpha\le2t+6<R$, since its cost is nonnegative.
It is itself a cap-feasible optimum with the exact resource value
(23.4). No passage to a closure of resource values is involved.

The proof does not assume unique minimizing degrees. All ties
between degrees $d,e$ are retained by the finite minimum, and all
positive optimal contacts obey the same strict exclusion of marked
indices at least three. ∎

## 25. A region of the winning envelope and its original-graph consumer

**Corollary 25.1 (Exact finite sufficiency at small $\kappa$ and large
finite $D$).** If

$$
0<\kappa\le1/10,\qquad D\ge2\cdot10^{12},
\tag{25.1}
$$

then the unique winning core index in (10.2) is $j=1$.
With $t=D/\sqrt2$ and $M_t=\lceil9D/\sqrt2\rceil$,

$$
\begin{aligned}
F(\kappa,D)=F_{M_t}(\kappa,D)
=-\frac1{4D^2}
+\min_{3\le d,e\le M_t}
 \left\{\frac{2\kappa}D r_{de}+D\kappa c_{de}\right\}.
\end{aligned}
\tag{25.2}
$$

For any positive compact rectangle $\mathcal K$ contained in
(25.1), the explicit endpoint-only cutoff
$\widehat M_{\mathcal K}$ of (17.1)--(17.3) satisfies
$F_{\widehat M_{\mathcal K}}=F$ throughout $\mathcal K$.
The endpoint inequalities in (25.1), equal-endpoint rectangles and
all minimizing-degree ties are included.

On every original integer sequence (18.2) tending to a point of
this rectangle, the full class of Definition 1.1 is eventually
nonempty and its minimum has limit

$$
\frac{V_{N_n}(a_n,h_n)-a_n(a_n+1)^2}{a_n^2}
\longrightarrow F(\kappa,D)
=F_{\widehat M_{\mathcal K}}(\kappa,D).
\tag{25.3}
$$

There is a recovery sequence with one $(a_n+1)$-sink core and
$h_n$ tail sinks, whose tail degrees and full degrees of sources
touching the tail are at most the existing $B_{\mathcal K}$ of
(18.1). It retains exactly $N_n$ sources, $a_n+1+h_n$ sinks and
$a_nN_n$ edges, simple connected bipartiteness and $k_u<d_i$ on
every edge. The remaining source degrees lie between $a_n$ and
$a_n+1$.

**Proof.** Use exactly $\alpha=2\kappa/D$, $\beta=D\kappa$ and
$R_j=Dj/\kappa$. Then $t=D/\sqrt2\ge10^{12}$ and
$R_1\ge10D>2t+6$. Theorem 24.3 applies to branch one.
Proposition 24.1 gives

$$
L_1\le\frac{2\kappa}D(2t+6)
=\kappa(2\sqrt2+12/D)<4\kappa\le2/5.
$$

Branch one is admissible and its envelope term is
$2+L_1<12/5<4$. Every admissible $j\ge2$ has
$2j+\mathcal L(\alpha,\beta;R_j)\ge4$.
This is a comparison with every competing branch, not a statement
about a selected losing branch. Thus one is the unique winner,
and (24.8) proves (25.2).

Pointwise finite winning attainment on $\mathcal K$ is now proved.
Theorem 17.1 supplies its existing endpoint-only bound without any
new graph construction. Theorem 18.1, with the winning index one,
gives precisely the recovery and degree bounds stated here.
Its use of Theorems 8.1 and 11.1 preserves marked incidence and
all exact integer budgets, and its lower bound is Proposition
12.2 or Theorem 13.1 over the full original graph class.
The latter theorem independently gives the full-minimum limit in
(25.3). No fixed connected rooted pattern is claimed to attain
the branch infimum, and no degree bound for all original minimizers
follows. The actual law domain $\mathcal X(a,h)$ and $M(a,h)$
remain unchanged. ∎

## 26. Sources and the unchanged all-positive question

The contact descent, singleton entrance, normalized pair resources,
quantitative dual-price bounds and strict row-two continuation are
repo-derived from the exact $g$, (7.3), the attained primal and
dual of Section 15, and the flow, gap and resolvent of Sections
19--21. The parameter $10^{12}$ in (24.7) is a sufficient explicit
threshold for the displayed rational inequalities; no optimal
threshold is asserted. The arithmetic-geometric mean inequality
and the scalar bounds for $g$ are proved or applied explicitly.
No external finite-state, monotone-policy or finite-support theorem
is a premise. The external CDSO convention remains that of
Albalahi--Das--Ali--Barman--Hamza, arXiv:2510.24809v1, Section 1,
and Citation 6.2: the denominator is the maximum endpoint degree,
with no $1/\sqrt2$ factor. The exact original cost is used in
(23.4), (24.8) and (25.2); Taylor bounds only certify inequalities.
The finite-duality input and its conditions remain those attributed
after Theorem 15.3. The Zhao--Zhao full-text overlap identified in
Section 6 remains unassessed; no global priority claim is made.

Theorem 24.3 rules out unavoidable infinite contact continuation
through row two in the region (24.7), and Corollary 25.1 rules out
a fixed-point refutation anywhere in (25.1). These are exact
finite-attainment results, including actual normalized resource
values, rather than approximation bounds or a chosen infinite
policy. They address a restricted region. In particular the
small-$\kappa$, large-$D$ family alone is not a counterexample to
Open problem 18.2; beyond the explicit threshold its only winning
branch has the finite attainers (23.5).

For the remaining positive parameters, Lemma 23.1 does not force
finite continuation from row two. When $\lambda>0$, the price
ratio relevant to the inequalities is $\sqrt{\beta/(\alpha+\lambda)}$,
and Proposition 24.1 has not supplied the needed inactive-cap
hypothesis. Finite non-singleton injection components can also
have normalized resources exceeding $R$; replacing a required
mixture by one component need not preserve its exact cap and
complementarity. The present results give no general finite
selection at a binding cap, and no exclusion of every finite
selection there.

Accordingly Open problem 18.2 remains unresolved on arbitrary
positive compact rectangles, including its full cap-boundary and
winning-tie requirements. Its genuine quantified negation also
remains unresolved: no fixed positive pair is supplied at which
every winner fails every finite cutoff. The conditions and
completion criterion of that problem are unchanged. Theorem 17.1
and Theorem 18.1 remain the endpoint-bound and original-graph
consumers if finite winning attainment is established in the
remaining range. The independent full-graph limit and eventual
nonemptiness of Theorem 13.1 continue to hold on every original
integer sequence, without the extra assumptions (24.7) or (25.1).

## 追加锚（本行以下为增补区）

## 27. The uncapped auxiliary problem and uniform bounds for its finite attainers

**Definition 27.1 (Uncapped scalarization).** Let $\mathscr A_M$ be
exactly the normalized nonnegative arrays in Definition 7.2 satisfying
(7.3), with indices $1\le k<d\le M$, without a resource cap. Retain
exactly $r,c$ in (7.4) and $g(t)=2(\sqrt{1+t^2}-1)$. Set

$$
\mathscr A_{\rm fin}=\bigcup_{M\ge3}\mathscr A_M,\qquad
\Psi_M(x)=\min_{Q\in\mathscr A_M}\{x r(Q)+c(Q)\},\qquad
\Psi(x)=\inf_{M\ge3}\Psi_M(x)\quad(x>0).
\tag{27.1}
$$

The notation $Q$ denotes a whole array, not a pair chosen independently
from its incidences. Let $\mathscr A_\infty$ consist of the countable
arrays satisfying exactly the nonnegative-series version of (7.3),
with $r,c<\infty$, without a cap. Write

$$
\mathscr O_x=\{Q\in\mathscr A_\infty:xr(Q)+c(Q)=\Psi(x)\},\qquad
S=\{x>0:\exists Q\in\mathscr A_{\rm fin},\ xr(Q)+c(Q)=\Psi(x)\}.
\tag{27.2}
$$

These are auxiliary array domains. No cap is removed from
$\mathcal L$, $F$, $F_M$, the original graph class, or the common-law
domain. In particular, (7.3) still includes the marked inequalities
$Z_k\le(k-1)q_k$ and every strict incidence index $k<d$.

**Lemma 27.2 (Countable attainment and a harmless large cap).** Put
$H_x=3x+c_*$, using exactly the comparison cost in Definition 10.1.
For every $x>0$ and every $R>H_x/x$,

$$
\Psi(x)=\mathcal L(x,1;R)
       =\min_{Q\in\mathscr A_\infty}\{xr(Q)+c(Q)\},\qquad
\mathscr O_x\ne\varnothing.
\tag{27.3}
$$

Every $Q\in\mathscr O_x$ has $1<r(Q)\le H_x/x<R$. Each finite
program in (27.1) has a minimum. The function $\Psi$ is concave and,
for $0<a\le x\le y\le b<\infty$ and $H=3b+c_*$, satisfies

$$
x\le\Psi(x)\le H_x,\qquad
0\le\Psi(y)-\Psi(x)\le(H/a)(y-x).
\tag{27.4}
$$

**Proof.** The comparison array with $(r,c)=(3,c_*)$ belongs to
$\mathscr A_3$, so $\Psi_M(x)\le H_x$ for every $M\ge3$. The finite
polyhedron $\mathscr A_M$ is closed and bounded: its column
normalization bounds $t,z,w$, while $q_k\le E_k$ gives
$\sum_kq_k\le\sum_ddt_d\le M$. It is nonempty by the same comparison
array. Thus its minimum exists.

Since $c\ge0$, any finite minimizing sequence with objective tending
to $\Psi(x)\le H_x<xR$ eventually has $r<R$. Consequently
$\mathcal L(x,1;R)=\Psi(x)$. Theorem 15.6 supplies a countable
minimizer with that cap. Conversely, for any $Q\in\mathscr A_\infty$,
choose $R'>\max\{1,r(Q),H_x/x\}$. Its finite approximations in
Theorem 15.6 imply $\Psi(x)\le xr(Q)+c(Q)$. This proves (27.3).
For any countable feasible array, the nonnegative summation argument
in Corollary 15.7 gives $r>1$; it uses only finite $r$, not optimality.
Thus $\Psi(x)\ge x$, and a minimizer has
$r\le\Psi(x)/x\le H_x/x$.

Concavity follows by taking the infimum of affine functions of $x$.
Monotonicity follows from $r\ge0$. For the quantitative upper bound,
take finite arrays with objective at $x$ at most $\Psi(x)+\epsilon$.
Their resources are at most $(H+\epsilon)/a$. Evaluating the same
arrays at $y$ gives

$$
\Psi(y)\le\Psi(x)+\epsilon
          +(y-x)(H+\epsilon)/a.
$$

Let $\epsilon\downarrow0$. This proves (27.4), including continuity
on $(0,\infty)$. ∎

**Lemma 27.3 (A common cutoff for every existing finite scalarized
attainer in a coefficient interval).** Fix $0<a\le b<\infty$, and put

$$
H=3b+c_*,\qquad
K_{a,b}=\left\lceil
2+\frac{4H}{\gamma}+\frac{48H^2}{a\gamma^2}
\right\rceil,\qquad \gamma=\frac2{1+\sqrt2}.
\tag{27.5}
$$

Apply (16.3) with

$$
a_*=a,\qquad A^*=b,\qquad B^*=1,\qquad
H^*=H,\qquad K^*=K_{a,b},
$$

and denote its resulting constants by $d_{a,b},u_{a,b}$. Define

$$
M_{a,b}=\max\{3,\lceil1+H/u_{a,b}\rceil\}.
\tag{27.6}
$$

Every finite scalarized attainer at every $x\in[a,b]\cap S$ belongs
to $\mathscr A_{M_{a,b}}$, and its source indices are at most
$K_{a,b}$. No existence of a finite attainer is assumed outside $S$.
Moreover, $S$ is closed relative to $(0,\infty)$.

**Proof.** Choose $R^*=H/a+1$. A finite scalarized attainer at
$x\in[a,b]$ has $r\le H/a<R^*$, and Lemma 27.2 makes it an attainer
of $\mathcal L(x,1;R^*)$. For an attained dual of this capped
problem, complementarity in Theorem 15.3 and the strict inequality
$r<R^*$ imply $\lambda=0$. Hence

$$
A=x\in[a,b],\qquad \ell=\Psi(x)\in[a,H],\qquad \beta=1.
\tag{27.7}
$$

Lemma 16.1 bounds its largest source index by $K_{a,b}$. Lemma 16.2
then bounds every tail degree by $1+H/u_{a,b}$. These are exactly
the existing support-bound hypotheses, now with a common cap used
only to obtain the dual. This proves (27.6).

If $x_n\in S$ and $x_n\to x>0$, discard finitely many terms so that
$x_n\in[a,b]\subset(0,\infty)$. Their finite attainers lie in one
compact $\mathscr A_{M_{a,b}}$. A convergent subsequence has a limit
there, and continuity in Lemma 27.2 makes its objective at $x$ equal
to $\Psi(x)$. Thus $x\in S$, proving relative closedness. This
argument bounds the support of finite attainers; it makes no claim
that every countable optimum is finite. ∎

## 28. Exact resource-face selection and the capped optimal face

**Theorem 28.1 (Finite replacement of the complete scalarized resource
face).** Fix $x>0$. Suppose there exist sequences

$$
x_n^-\in S,\qquad x_n^+\in S,\qquad
x_n^-<x<x_n^+,\qquad x_n^-\to x,\quad x_n^+\to x.
\tag{28.1}
$$

Then there are finite arrays $Q_{\min},Q_{\max}\in\mathscr O_x$
such that, with $r_{\min}=r(Q_{\min})$ and
$r_{\max}=r(Q_{\max})$,

$$
\{(r(Q),c(Q)):Q\in\mathscr O_x\}
 =\{(r,\Psi(x)-xr):r_{\min}\le r\le r_{\max}\}.
\tag{28.2}
$$

Every pair on the right is attained by a convex combination of these
two finite arrays. They and their mixtures can all be chosen at the
single cutoff $M_{x/2,2x}$ in (27.6). The case
$r_{\min}=r_{\max}$ is included. In particular, the assertion holds
at every $x>0$ if $S=(0,\infty)$.

**Proof.** Eventually both coefficient sequences lie in
$[x/2,2x]$. Choose finite attainers $Q_n^\pm$ there. Lemma 27.3
places all of them in one compact finite polyhedron. Passing to a
subsequence separately on each side gives limits $Q^+,Q^-$ at
that cutoff. Since

$$
x_n^\pm r(Q_n^\pm)+c(Q_n^\pm)=\Psi(x_n^\pm),
$$

continuity implies $Q^+,Q^-\in\mathscr O_x$.

For any $Q\in\mathscr O_x$, optimality at the nearby coefficient
and Lemma 27.2 give

$$
\Psi(x)+(x_n^\pm-x)r(Q_n^\pm)
 \le\Psi(x_n^\pm)
 \le\Psi(x)+(x_n^\pm-x)r(Q).
\tag{28.3}
$$

The first inequality uses the feasible array $Q_n^\pm$ at $x$;
the second uses the same whole array $Q$ at $x_n^\pm$. Division
by the positive or negative coefficient difference, respectively,
shows

$$
r(Q_n^+)\le r(Q)\le r(Q_n^-).
$$

The limits therefore satisfy $r(Q^+)\le r(Q)\le r(Q^-)$ for every
$Q\in\mathscr O_x$. Take $Q_{\min}=Q^+$ and $Q_{\max}=Q^-$.
They are themselves in that face, so they attain its exact resource
extrema. Any intermediate resource is attained by their convex
mixture, and its cost is $\Psi(x)-xr$ by linearity. Conversely every
point of the face has this cost and lies between the two extrema.
This proves (28.2). If the extrema coincide, either array supplies
the required pair. Every mixture satisfies each individual balance
and marked inequality in (7.3), since its two constituent arrays do.
No selection of raw incidence atoms is made. ∎

**Proposition 28.2 (The exact scalar coefficient of a capped face).**
Fix $\alpha,\beta>0$, $R>1$, let
$L=\mathcal L(\alpha,\beta;R)$, and choose any attained dual from
Theorem 15.3. Put

$$
x=\frac{\alpha+\lambda}{\beta}=\frac A\beta>0.
\tag{28.4}
$$

Then

$$
\beta\Psi(x)=\ell=L+\lambda R.
\tag{28.5}
$$

Every countable capped optimum belongs to $\mathscr O_x$. For any
$Q\in\mathscr O_x$ with $r(Q)\le R$,

$$
\alpha r(Q)+\beta c(Q)-L=\lambda\{R-r(Q)\}.
\tag{28.6}
$$

Consequently, for this prescribed dual, finite capped attainment is
equivalent to the existence of a finite $Q\in\mathscr O_x$ such that

$$
r(Q)\le R,\qquad \lambda\{R-r(Q)\}=0.
\tag{28.7}
$$

**Proof.** The nonnegative weak-duality summation (15.6) applies to
every uncapped array with finite $r,c$: its row-price sum is bounded
by $Ar$ and its cost sum by $\beta c$. The cap is not used in that
summation. Thus $\ell\le Ar+\beta c$ on $\mathscr A_\infty$.
For a countable capped optimum $Q_*$, Theorem 15.6 and Corollary
15.7 give

$$
Ar(Q_*)+\beta c(Q_*)=L+\lambda r(Q_*)
                   =L+\lambda R=\ell.
$$

Lemma 27.2 identifies the uncapped infimum with the countable
minimum, proving (28.5) and $Q_*\in\mathscr O_x$. Subtracting
$L=\beta\Psi(x)-\lambda R$ gives (28.6). If a finite array is a
capped optimum, the same complementarity gives (28.7). Conversely,
(28.6) makes every finite selection in (28.7) a capped optimum. ∎

**Corollary 28.3 (Universal scalarized attainment supplies every exact
cap).** If $S=(0,\infty)$, then every
$\mathcal L(\alpha,\beta;R)$ with $\alpha,\beta>0$, $R>1$ has a
finite attainer. More precisely, for every countable capped optimum
$Q_*$ and every prescribed attained dual, there is a finite capped
optimum with exactly the same resource and cost as $Q_*$. A mixture
of at most two finite scalarized attainers at the coefficient
(28.4) suffices.

**Proof.** Proposition 28.2 puts $Q_*$ in $\mathscr O_x$.
Theorem 28.1 supplies a finite mixture with
$r=r(Q_*)$ and $c=c(Q_*)$. It therefore preserves (28.7).
If $\lambda>0$, complementarity gives $r(Q_*)=R$, and the mixture
hits that cap exactly. If $\lambda=0$, its unchanged resource may
be strictly below $R$ or equal to $R$; both give the same objective.
This also covers an endpoint resource, coincident face endpoints,
and ties between scalarized minimizers. Neither endpoint constituent
is required individually to satisfy the cap when an interior
mixture is used. ∎

## 29. Equivalence with the complete winning-envelope question

**Proposition 29.1 (Every positive coefficient occurs on an actual
unique winner).** For any $x>0$ define the following positive numbers,
using $c_*$ from Definition 10.1:

$$
\begin{gathered}
D_x=\sqrt{2/x},\qquad H_x=3x+c_*,\qquad Q_x=H_x/x,\\
\kappa_x=\min\left\{
 \frac{D_x}{2(Q_x+1)},\frac1{2D_xH_x}\right\},\qquad
\beta_x=D_x\kappa_x.
\end{gathered}
\tag{29.1}
$$

At the original parameter pair $(\kappa_x,D_x)$, the exact original
$j_0$ is one and the exact original $J_0$ is two. Branch $j=1$ is
the unique winner both for $F$ and for every $F_M$, $M\ge3$. One has

$$
\begin{aligned}
F(\kappa_x,D_x)&=-\frac1{4D_x^2}+\beta_x\Psi(x),\\
F_M(\kappa_x,D_x)&=-\frac1{4D_x^2}+\beta_x\Psi_M(x),\\
F_M(\kappa_x,D_x)-F(\kappa_x,D_x)
 &=\beta_x\{\Psi_M(x)-\Psi(x)\}.
\end{aligned}
\tag{29.2}
$$

All scalarized minimizers used in these identities have resource
strictly below the original $R_1=D_x/\kappa_x$.

**Proof.** Since $c_*>0$, one has $Q_x>3$. The choices in (29.1) give

$$
R_1\ge2(Q_x+1)>Q_x>3,\qquad
\beta_xH_x\le\tfrac12,\qquad
\frac{2\kappa_x}{D_x}=\beta_x x.
\tag{29.3}
$$

For every $M\ge3$, the comparison array at cutoff three shows
$\Psi_M(x)\le H_x$. Each minimum defining $\Psi_M(x)$ therefore
has $r\le Q_x<R_1$, by nonnegative cost. It follows that

$$
\mathcal L_M(\beta_x x,\beta_x;R_1)=\beta_x\Psi_M(x),\qquad
\mathcal L(\beta_x x,\beta_x;R_1)=\beta_x\Psi(x).
\tag{29.4}
$$

The second identity also follows from Lemma 27.2; it includes every
countable scalarized minimizer. Thus the cap has not been discarded
from either original branch: it is strictly satisfied at the
uncapped minima.

Moreover $3\kappa_x/D_x\le3/\{2(Q_x+1)\}<1$, so the formula in
Definition 10.1 gives $j_0=1$. Its comparison value is exactly
$T_0=2+\beta_xH_x\in(2,5/2]$, and hence $J_0=2$. Both indices
are admissible since $R_1>3$. Branch one has envelope term at most
$5/2$, whereas branch two has term at least four, at every finite
cutoff and in the unrestricted value. This proves unique actual
winning without a hypothesis on any losing optimizer. Substitution
in the unchanged (10.2) and (15.1) proves (29.2). ∎

**Theorem 29.2 (The all-positive scalarized finite-attainment
equivalence).** The following two assertions are equivalent:

1. For every $x>0$, the uncapped auxiliary problem (27.1) has a finite
   attainer, that is, $S=(0,\infty)$.
2. The complete assertion of Open problem 18.2 holds, with exactly
   the original $F_M$, $F$, $J_0$, $R_j>1$ admissibility and
   infeasible-branch convention, on every positive compact rectangle.

If they hold, the explicit endpoint-only cutoff is precisely
$\widehat M_{\mathcal K}$ of (17.1)--(17.3). All winning-cap ties,
incidence transitions and equal-endpoint rectangles are included.
The first assertion also implies finite attainment of every capped
branch with $\alpha,\beta>0$, $R>1$; this is a consequence, rather
than an added requirement on losing branches in the second assertion.

**Proof.** Assume the first assertion. At any positive pair
$(\kappa,D)$, choose any actual winning index in the nonempty finite
minimum (10.2). Its parameters are exactly

$$
\alpha=2\kappa/D,\qquad \beta=D\kappa,\qquad R=R_j=Dj/\kappa>1.
$$

Corollary 28.3 gives a finite attainer on that branch, even at a
binding cap. Hence $F_M=F$ for some finite $M$ at this point.
Theorem 17.1 now gives the same $\widehat M_{\mathcal K}$ throughout
any prescribed rectangle $\mathcal K$. Its hypotheses require only
finite attainment on a winner at each point, and its proof includes
all ties and degenerate rectangles. No alteration of $J_0$ or of an
inadmissible or infeasible branch is made. This proves the second
assertion with its requested explicit bound.

Conversely, fix any $x>0$ and use the original pair in (29.1).
Apply the second assertion to its equal-endpoint rectangle
$\{\kappa_x\}\times\{D_x\}$. Equality at its finite cutoff and
(29.2) give $\Psi_M(x)=\Psi(x)$. The minimum in (27.1) exists,
so $x\in S$. Since $x$ was arbitrary, the first assertion follows.
The additional capped-branch conclusion is Corollary 28.3. ∎

**Corollary 29.3 (Exact negative transfer).** If some $x>0$ does not
belong to $S$, then the fixed positive pair (29.1) satisfies

$$
F_M(\kappa_x,D_x)>F(\kappa_x,D_x)\qquad(M\ge3).
\tag{29.5}
$$

It is a genuine refutation of Open problem 18.2, on the corresponding
equal-endpoint rectangle or on any positive compact rectangle
containing that pair. Conversely, if a fixed positive pair has
$F_M>F$ for every finite $M$, choose any of its actual winning
branches and any attained dual on that branch, and put
$x=(\alpha+\lambda)/\beta$. Then for some $0<\delta<x$, at least
one of the intervals

$$
(x-\delta,x),\qquad(x,x+\delta)
\tag{29.6}
$$

is disjoint from $S$. Thus an original winning-envelope obstruction
also forces actual uncapped scalarized nonattainment at positive
coefficients. The fixed-compact/all-cutoff refutation criterion in
Open problem 18.2 has the same consequence by Corollary 17.2.

**Proof.** If $x\notin S$, each attained finite value $\Psi_M(x)$
is strictly greater than $\Psi(x)$. Equation (29.2), with
$\beta_x>0$, proves (29.5) on an actual unique winner.

For the converse, no winning branch at the stated pair has a finite
attainer, by Definition 15.1. Proposition 28.2 supplies a countable
capped optimum in $\mathscr O_x$ satisfying (28.7). If $S$ accumulated
at $x$ from both sides, Theorem 28.1 would replace that optimum by
a finite array with the same resource and cost. It would be a finite
attainer on the chosen winning branch, a contradiction. Failure of
two-sided accumulation means that one interval in (29.6) avoids
$S$, after decreasing $\delta$ to be less than $x$. Any coefficient
in that interval is an auxiliary nonattainment coefficient, and
(29.1)--(29.5) transfer it back to an original unique winner.
Finally, Corollary 17.2 converts a compact obstruction to a fixed-pair
obstruction. No existence of either obstruction is assumed here. ∎

**Corollary 29.4 (The original-graph consumer of the equivalence).**
Under either equivalent assertion of Theorem 29.2, let
$\mathcal K$ be any positive compact rectangle, including an
equal-endpoint rectangle. For every $(\kappa,D)\in\mathcal K$ and
every original integer sequence with $a_n\ge4$, $h_n\ge1$,
$N_n\ge1$ and

$$
a_n\to\infty,\qquad h_n/\sqrt{a_n}\to\kappa,\qquad
N_n/a_n^{3/2}\to D,
\tag{29.7}
$$

the full original graph class is eventually nonempty and

$$
\frac{V_{N_n}(a_n,h_n)-a_n(a_n+1)^2}{a_n^2}
 \longrightarrow F(\kappa,D)
 =F_{\widehat M_{\mathcal K}}(\kappa,D).
\tag{29.8}
$$

There is a recovery sequence with one fixed winning index $j$,
$a_n+j$ core sinks and $h_n+1-j$ tail sinks, for which every tail
degree and every full degree of a source touching the tail is at
most $B_{\mathcal K}$ from (18.1). The remaining source degrees lie
between $a_n$ and $a_n+j$. Each graph has exactly $N_n$ sources,
$a_n+1+h_n$ sinks and $a_nN_n$ edges, is simple, connected and
bipartite, and has $k_u<d_i$ on every edge. Core sink degrees are
not bounded by this conclusion.

**Proof.** Theorem 29.2 supplies pointwise finite winning attainment,
so the hypotheses of Theorem 18.1 hold with exactly the endpoint
constants of Theorem 17.1. That theorem supplies the asserted
recovery sequence and bounds. In particular, its use of Theorem
8.1 approximates the finite marked arrays by actual rooted patterns,
after strict-cap mixing when necessary. Theorem 11.1 is applied
only with its strict condition $\kappa r/D<j$; it provides each
sufficiently large exact integer budget, without restricting a
congruence class. Proposition 12.2 supplies the lower limit over
the whole prescribed graph class. Theorem 13.1 independently gives
the full-minimum limit and eventual nonemptiness on every sequence
(29.7), even without either assertion of Theorem 29.2.

Under a nonattainment hypothesis in Corollary 29.3 the same independent
Theorem 13.1 still applies, including at the pair (29.1). Thus the
strict finite-cutoff gap concerns its actual original-graph limit,
not the value of a substitute graph domain. Finite-array attainment
does not assert attainment by one connected rooted pattern or a
degree bound for every original minimizer. Neither $\mathcal X(a,h)$
nor $M(a,h)$ has been changed. ∎

## 30. Sources and the remaining scalarized existence question

The scalarization and supporting-hyperplane interpretation are
classical: S. Boyd and L. Vandenberghe, *Convex Optimization*,
[author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf),
Section 4.7.4, printed pp.178--180. The finite affine strong-duality
and dual-attainment input is exactly Section 5.2.3, (5.26)--(5.27),
and Section 5.2.4, printed pp.226--227, already used in Theorem 15.3.
Sections 5.6.1--5.6.3, printed pp.249--252, give the standard
perturbation and sensitivity viewpoint. No differentiability of
$\Psi$ or uniqueness of a dual or primal minimizer is assumed here;
(28.3) is the direct comparison of the two affine objectives.
These mature scalarization and sensitivity facts are not asserted
as new mathematics.

The additional correspondence uses the actual CDSO support bounds
in Lemmas 16.1--16.2 to put all existing nearby finite attainers in
one finite polyhedron. Compactness inside that common cutoff, rather
than compactness of an unspecified infinite-dimensional feasible
set, permits the exact resource endpoints in Theorem 28.1. The
coefficient (28.4), exact cap identity (28.6), all-cutoff original
winning identity (29.2) and the endpoint and graph consumers are
deductions for the specific normalized marked constraints and exact
nonlinear cost of this volume. They do not replace those constraints
by independent moments, a quadratic cost, or relaxed graph budgets.

C. Bayer and J. Teichmann, *The proof of Tchakaloff's theorem*,
[arXiv:math/0502473v2](https://arxiv.org/abs/math/0502473v2),
Theorem 1 and Corollaries 1--2, pp.2--4, give finite positive
representations for finitely many integrable functions; their
Theorem 2 gives the polynomial cubature formulation. That result is
not a premise of Theorems 28.1 or 29.2. Applied just to normalization,
resource and cost of raw incidence actions, it would not preserve
the countably many row balances in (7.3). Nor does a finite mixture
of countable components imply finitely many reachable source rows.
Here the two endpoint arrays already have finite support and satisfy
all row constraints before they are mixed. Theorem 21.1 and Lemma
23.1 retain their separate scopes, including the possibility that a
normalized component exceeds an original cap.

The original CDSO normalization remains Albalahi--Das--Ali--Barman--Hamza,
*On the hyperbolic Sombor index and its counterpart*,
[arXiv:2510.24809v1](https://arxiv.org/html/2510.24809v1), Section 1,
and DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176):
the maximum endpoint degree is the denominator and the factor
$1/\sqrt2$ is dropped. No extremal theorem from that paper is used
in the equivalence. The Zhao--Zhao full-text overlap identified in
Section 6 remains unassessed, and no global priority assertion is
made.

**Open boundary 30.1 (Universal scalarized attainment remains the
existence obligation).** Theorems 28.1 and 29.2 do not prove
$S=(0,\infty)$ and do not exhibit $x\notin S$. In particular,
finite attainment at one coefficient alone has not supplied both
resource endpoints there: (28.1) is a sufficient two-sided
finite-attainment hypothesis, established everywhere only under the
universal assertion. The large-cap construction in Lemma 27.2
proves countable attainment and does not by itself make an optimum
finite. The local cutoff in Lemma 27.3 bounds finite attainers when
they exist and does not turn an arbitrary countable optimum into a
finite one.

It follows that the complete proof or genuine refutation of Open
problem 18.2 remains unresolved. Its original full parameter,
winning-envelope and integer-sequence quantifiers are unchanged.
A proof of universal uncapped attainment would complete the original
finite-sufficiency assertion through Theorem 29.2, with its existing
explicit endpoint bound and exact-budget graph recovery. A proved
positive coefficient outside $S$ would instead give the fixed-pair
strict inequalities (29.5), and hence the original genuine quantified
refutation. A losing-branch obstruction, a failure of finite cubature
to preserve balances, or the equivalence alone supplies neither
outcome.

## 追加锚（本行以下为增补区）

## 31. The rigid entrance price and an exact integer return test

**Definition 31.1 (The row-one two-row comparison).** For $x>0$ put

$$
\begin{gathered}
C_d=(d-1)g(1/d)+g(2/d),\qquad
B_d(x)=dx+C_d,\qquad
\mathfrak B(x)=\min_{d\ge3}B_d(x),\\
a_x=\mathfrak B(x)-x,\qquad
f_e(x)=\frac{a_x-e g(2/e)}{e-1},\qquad
\vartheta_x=\sup_{e\ge3}f_e(x),\\
\mathsf T_2(x)=\inf_{d,e\ge3}\{x r_{de}+c_{de}\}.
\end{gathered}
\tag{31.1}
$$

All degree indices in this section are integers unless a real argument
is explicitly specified. The pairs $(r_{de},c_{de})$ are the actual
normalized pair flows of Proposition 23.2. Thus $\mathsf T_2$ compares
only flows with source rows one and two and injection only at one.
It does not include two-row flows with injection at two, and it is
not a replacement for $\Psi$.

**Proposition 31.2 (Finite exact comparison and all minimizing pairs).**
For every $x>0$, define

$$
D_x^{\rm ent}=\left\lfloor\frac{3x+C_3}{x}\right\rfloor,\qquad
n_x=\max\{3,\lceil8/a_x\rceil\},\qquad E_x=2n_x-1.
\tag{31.2}
$$

The minimum defining $\mathfrak B(x)$ exists, $a_x>0$, and

$$
\begin{gathered}
\mathfrak B(x)=\min_{3\le d\le D_x^{\rm ent}}B_d(x),\\
0<\frac{a_x}{2(n_x-1)}
 \le\vartheta_x=\max_{3\le e\le E_x}f_e(x),\\
\mathsf T_2(x)=\mathfrak B(x)-\vartheta_x.
\end{gathered}
\tag{31.3}
$$

In particular the infimum defining $\mathsf T_2$ is attained.
Its minimizing pairs are exactly all pairs for which
$B_d(x)=\mathfrak B(x)$ and $f_e(x)=\vartheta_x$.
The same value is the minimum over all normalized finite flows
supported on source rows one and two with injection only at one.

**Proof.** Since $B_d(x)\ge dx$ and $x>0$, its minimum exists.
A minimizing $d$ satisfies $dx\le B_3(x)=3x+C_3$, proving its
cutoff. Every $B_d(x)>3x$, so $\mathfrak B(x)>3x>x$.
The exact pair formula (23.4) gives

$$
x r_{de}+c_{de}
 =\frac{(e-2)B_d(x)+x+e g(2/e)}{e-1}.
\tag{31.4}
$$

For each fixed $e$, the positive factor $(e-2)/(e-1)$ makes
its minimizing $d$ exactly a minimizer of $B_d(x)$.
After that minimization, (31.4) is $\mathfrak B(x)-f_e(x)$.

The inequality $g(z)\le z^2$ gives
$n_xg(2/n_x)\le4/n_x\le a_x/2$. Hence
$f_{n_x}(x)\ge a_x/\{2(n_x-1)\}>0$.
Also $f_e(x)\to0$ as $e\to\infty$, so its positive supremum is
attained. If $f_e(x)=\vartheta_x$, then

$$
(e-1)\vartheta_x=a_x-e g(2/e)<a_x,
\qquad
e<1+\frac{a_x}{\vartheta_x}\le2n_x-1.
$$

The stated, slightly larger closed integer cutoff follows.
This proves (31.3) and the characterization of all minimizing
pairs. Every pair is feasible by Proposition 23.2, and that
proposition expresses every other finite flow in the stated
class as a convex combination of these pair flows. Such a
combination cannot have smaller objective. ∎

**Theorem 31.3 (Entrance rigidity across all attained duals).**
Fix $x>0$ and any harmless cap $R>H_x/x$ from Lemma 27.2.
Suppose there exists an actual normalized optimal flow $y$ for
$\Psi(x)$ whose injection satisfies $b_k=0$ for every $k\ge2$.
For every attained dual of $\mathcal L(x,1;R)$, write
$\ell=\Psi(x)$ and $p=u_2$. Then

$$
\ell+p=\mathfrak B(x),\qquad
0<\vartheta_x\le p\le x/2<1/3,\qquad
v_2=x-2p.
\tag{31.5}
$$

Thus $u_2$, $v_2$ and the row-two return gap are independent of
the choice of attained dual. Every positive row-one action in
any such optimal flow has degree in
$\operatorname{argmin}_{d\ge3}B_d(x)$.

For $0<z<1/3$ define

$$
\tau(z)=\frac{2(2-z)}{\sqrt{z(4-z)}},\qquad
\mathcal E(z)=\{\lfloor\tau(z)\rfloor,\lceil\tau(z)\rceil\}.
\tag{31.6}
$$

The exact all-degree return gap is

$$
\begin{aligned}
G_2
 &=\min_{e\ge3}\{(e-2)p+x+e g(2/e)-\ell\}\\
 &=\min_{e\in\mathcal E(p)}
       \{(e-1)p+x+e g(2/e)-\mathfrak B(x)\}.
\end{aligned}
\tag{31.7}
$$

Both integers in $\mathcal E(p)$ are at least three.
If the two values tie, both are retained.

**Proof.** Lemma 27.2 puts every scalarized optimum strictly inside
the prescribed cap. Thus every attained dual has
$A=x$, $\beta=1$, $\lambda=0$ and $\ell=\Psi(x)$.
Proposition 20.2 and Theorem 21.1 give a nonzero injection.
Since only row one is allowed, $b_1>0$ and $W_1=b_1>0$.
Lemma 23.1 makes each positive row-one action $(1,2,d)$.
For every integer $d\ge3$, the all-degree dual test with
unmarked row one and marked row two is

$$
\ell\le (d-1)\{x+g(1/d)\}+x-p+g(2/d)=B_d(x)-p.
\tag{31.8}
$$

Every positive row-one action has equality by the exact gap
identity. At least one exists. Consequently
$\ell+p=\min_dB_d(x)$, with the asserted minimizing degrees.
The same actual optimum has zero gap against every attained
dual, so this reasoning fixes $p$ for all of them.

Lemma 20.3 gives $p>0$, and the row equality gives
$p\le x/2$ and $v_2=x-2p$.
A positive row-one action satisfies $d^2<6/x$ by Lemma 23.1.
Since $d\ge3$, one has $x<2/3$, and hence $p<1/3$.
The self-return column inequalities and (31.8) give, for every $e$,

$$
0\le(e-1)p+x+e g(2/e)-\mathfrak B(x)
  =(e-1)\{p-f_e(x)\}.
\tag{31.9}
$$

Taking the maximum of $f_e$ proves $\vartheta_x\le p$.

For the integer minimization use the exact identity
$e g(2/e)=2\sqrt{e^2+4}-2e$, rather than a quadratic approximation.
The real function

$$
h_z(t)=(t-2)z+x+2\sqrt{t^2+4}-2t\quad(t\ge3)
$$

has derivatives

$$
h_z'(t)=z-2+\frac{2t}{\sqrt{t^2+4}},\qquad
h_z''(t)=\frac8{(t^2+4)^{3/2}}>0.
$$

Its unique unrestricted positive critical point is $\tau(z)$.
For $0<z<1/3$ it lies above three: indeed
$h_z'(3)<1/3-2+6/\sqrt{13}<0$, where the last
inequality is equivalent to $324<325$.
Strict decrease up to $\tau(z)$ and strict increase afterwards
put every integer minimizer among its two adjacent integers.
Applying this with $z=p$ proves (31.7). ∎

**Corollary 31.4 (Quantitative gap from the whole two-row comparison).**
Under the hypotheses of Theorem 31.3 put

$$
\varepsilon_x=\mathsf T_2(x)-\Psi(x)=p-\vartheta_x,\qquad
E_x^\circ=\lceil\tau(\vartheta_x)\rceil.
\tag{31.10}
$$

Then

$$
2\varepsilon_x\le G_2\le(E_x^\circ-1)\varepsilon_x.
\tag{31.11}
$$

In particular, $G_2=0$ if and only if an actual pair flow of
Proposition 23.2 is scalarized optimal. If one such pair is
optimal, every attained dual has $G_2=0$.

**Proof.** Every pair is a feasible uncapped array, so
$\Psi(x)\le\mathsf T_2(x)$ by Lemma 27.2. Equations (31.3)
and (31.5) give (31.10). For each $e$ the return slack is exactly

$$
(e-1)\{p-f_e(x)\}
 =(e-1)\varepsilon_x
   +(e-1)\{\vartheta_x-f_e(x)\}.
\tag{31.12}
$$

The second term is nonnegative, and $e-1\ge2$, giving the lower
bound in (31.11). Choose any maximizing degree $e_0$ for $f_e$.
At $p=\vartheta_x$ the corresponding slack is zero and all
others are nonnegative. The real minimization in the proof of
Theorem 31.3, now at $z=\vartheta_x\le p<1/3$, therefore gives
$e_0\in\mathcal E(\vartheta_x)$. At the actual $p$, its slack is
$(e_0-1)\varepsilon_x\le(E_x^\circ-1)\varepsilon_x$.
The minimum over all $e$ gives the upper bound.
Proposition 31.2 supplies an actual minimizing pair, so equality
of its value with $\Psi$ is attainment, rather than a limiting
resource or a relaxed column comparison. ∎

## 32. A positive return gap forces strict departure and higher rows

**Proposition 32.1 (A quantitative departure barrier on the same
optimal flow).** Retain the hypotheses of Theorem 31.3 and fix
any one of its attained duals and any actual normalized optimal
flow with injection only at row one. Suppose $G_2>0$.
Every positive action $(2,j,d)$ has $j\ge3$ and

$$
v_j\le v_2-G_2.
\tag{32.1}
$$

Every active row $k\ge3$ satisfies the same bound. No positive
action from any of these rows targets row two, so all marked
incidence in row two comes directly from row one. Moreover

$$
0<G_2\le v_2=x-2p,\qquad
0<\varepsilon_x\le\frac{x-2\vartheta_x}{4}.
\tag{32.2}
$$

These statements refer to this actual optimal flow and its
all-degree dual; existence of a flow with $G_2>0$ is not asserted.

Write $W_+=\sum_{k\ge3}W_k$ and define

$$
D_2=\left\lfloor1+\frac{\ell}{p}\right\rfloor,\qquad
P_*=(D_2-2)(D_2-1).
\tag{32.3}
$$

Then $D_2\ge4$, all quantities below are finite, and

$$
\begin{gathered}
\frac{W_2}{P_*}\le W_+\le\frac{W_2}{5},\\
\frac57\le W_2\le\frac{P_*}{P_*+2}<1,\qquad
1-W_2=\sum_{k\ge3}(k-1)W_k.
\end{gathered}
\tag{32.4}
$$

Thus a positive gap would force positive higher-row mass in the
actual optimum, with a bound depending on its actual $\ell,p$.

**Proof.** There is positive row-one action mass, all targeting
two, so $I_2>0$ and $W_2>0$. For a positive action $(2,j,d)$,
unmarked contact permits row $j$ as a competitor and gives

$$
a_{jd}=u_j+g(j/d)-u_2-g(2/d)\ge0.
$$

Its column contact and marked comparison give

$$
\begin{aligned}
b_{jd}
 &=u_2+v_2+g(2/d)-u_j-v_j-g(j/d)\\
 &=(d-2)p+x+d g(2/d)-\ell\ge G_2.
\end{aligned}
$$

Adding gives $a_{jd}+b_{jd}=v_2-v_j$.
This proves (32.1), excludes $j=2$, and gives $G_2\le v_2$.
The resolvent (21.2) puts every active row on a finite positive
path from the injection. The first step is $1\longrightarrow2$.
After the first departure from two, Lemma 23.1 makes the marked
price nonincreasing along the remainder of the path.
Consequently every reached row at least three has price at most
$v_2-G_2$ and cannot return to two. This proves the asserted
barrier on the entire active support. Combining
$2\varepsilon_x\le G_2\le x-2p$ with
$p=\vartheta_x+\varepsilon_x$ proves (32.2).

For $k\ge2$ the zero-injection condition gives $W_k=I_k$.
There is no marked incidence into two except from one, so

$$
W_2=I_2=\sum_d\frac{y_{12d}}{d-1}.
\tag{32.5}
$$

Every other positive action has target $j\ge3$ and $d\ge4$.
Its propagation coefficient is
$p_{jd}=1/\{(j-1)(d-1)\}\le1/6$.
The nonnegative balance sums therefore give

$$
W_+=\sum_{j\ge3}I_j
 \le\frac16(W_2+W_+),\qquad W_+\le W_2/5.
\tag{32.6}
$$

These sums are finite by Theorem 19.1 and Proposition 20.2.
For all non-row-one actions, $1/(d-1)\le1/3$.
Their normalization mass is $1-W_2$ by (32.5), whence

$$
1-W_2
 \le\frac13(W_2+W_+)\le\frac25W_2.
$$

This proves $W_2\ge5/7$. Also nonnegative summation in
Definition 20.1 gives the exact normalization identity

$$
1=\sum_{j\ge2}(j-1)I_j
  =W_2+\sum_{j\ge3}(j-1)W_j.
\tag{32.7}
$$

Each positive action out of two satisfies $d\le D_2$ by
Lemma 20.3. Since it targets $j\ge3$, $D_2\ge4$ and
$p_{jd}\ge1/P_*$. Summing just these contributions to the
higher-row incoming mass gives $W_+\ge W_2/P_*>0$.
Finally (32.7) gives
$1\ge W_2+2W_+\ge W_2(1+2/P_*)$.
This proves the remaining bounds in (32.4), including $W_2<1$.
Every sum uses the same flow, not separate extremizers of its
resource and cost. ∎

## 33. Sources and the unresolved return relation

The exact scalar cost remains
$g(z)=2(\sqrt{1+z^2}-1)$ from Definition 27.1.
The original normalization is that of Albalahi--Das--Ali--Barman--Hamza,
*On the hyperbolic Sombor index and its counterpart*,
[arXiv:2510.24809v1](https://arxiv.org/html/2510.24809v1),
Section 1, equation (1) and the following definition: the CDSO
denominator is the maximum endpoint degree and the factor
$1/\sqrt2$ is dropped. No extremal assertion from that paper is
used in Sections 31--32.

The finite affine duality input to the reused Theorem 15.3 is
Boyd--Vandenberghe, *Convex Optimization*,
[author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf),
Sections 5.2.3--5.2.4, printed pp.226--227,
especially (5.26)--(5.27) and dual attainment under the affine
refinement. The integer minimization in (31.7) uses elementary
real differentiation inside a CDSO-specific proof.
Entrance rigidity, the exact comparison gap, the strict departure
barrier and the mass bounds are deductions for the particular
marked balances and nonlinear cost of this volume. They are not
applications of a finite-moment representation theorem to discard
the countably many row constraints. The Zhao--Zhao full-text
overlap specified in Section 6 remains unassessed; no global
priority or exhaustive-literature assertion is made.

**Open boundary 33.1 (The return implication remains unproved).**
For every $x>0$ admitting an actual scalarized optimal flow with
injection only at row one, the remaining proposed implication is

$$
G_2=0.
\tag{33.1}
$$

Theorem 31.3 makes this a dual-independent assertion about that
coefficient, and Corollary 31.4 identifies its precise missing
inequality as $\Psi(x)\ge\mathsf T_2(x)$ under the stated
row-one-optimality hypothesis. The reverse inequality is already
true because the pair flows are feasible. Neither the two adjacent
integer test nor the departure barrier establishes the missing
inequality. In particular, (32.1)--(32.4) are necessary consequences
of a positive gap, not an existence certificate or a contradiction.

A strict counterexample to (33.1) still requires an actual $x>0$,
an all-degree attained dual with $\ell=\Psi(x)$, and an actual
normalized row-one-only optimal flow satisfying the full countable
balances, with the strictly positive return value in (31.7).
No such coefficient and certificate is supplied here. Computing
the two integer values with an uncertified proposed $\ell$ or $p$
would not supply those obligations.

Even a certified positive gap would refute only (33.1).
The optimum could still be a finite array using more than two
source rows. It would not imply $x\notin S$, or any strict gap
between the original winning envelopes $F_M$ and $F$.
The complete all-positive compact-rectangle assertion of Open
problem 18.2, its exact finite endpoint bound, all winning ties
and its genuine quantified refutation criterion remain unchanged
and unresolved. The original-graph transfer remains exactly
Theorem 29.2 and Corollary 29.4, through Theorem 8.1,
Theorem 11.1, Proposition 12.2 and Theorem 13.1, with the same
strict incidence conditions and exact integer budgets.
Nothing in Sections 31--32 supplies universal scalarized finite
attainment or a coefficient outside $S$.

## 追加锚（本行以下为增补区）

## 34. Finite certification with a critical reciprocal-square price tail

**Definition 34.1 (A finite price prefix and its prescribed tail).**
Fix $x,\ell>0$, an integer $K\ge1$, and real numbers

$$
u_1=x,\qquad 0<u_k\le x/k\quad(2\le k\le K),\qquad
0<a\le x(K+1).
\tag{34.1}
$$

Extend these finitely many prices by

$$
u_k=a/k^2\quad(k>K),\qquad v_1=0,\qquad
v_k=\frac{x-ku_k}{k-1}\quad(k\ge2).
\tag{34.2}
$$

Thus $u_k,v_k\ge0$ and $ku_k+(k-1)v_k=x$ for every $k\ge2$.
For integers $d\ge3$ use the actual nonlinear cost and set

$$
\begin{gathered}
g(t)=2(\sqrt{1+t^2}-1),\qquad
b_d=\min_{1\le k<d}\{u_k+g(k/d)\},\\
m_d=\min_{2\le j<d}\left\{\frac{x-u_j}{j-1}+g(j/d)\right\},
\qquad \Phi_d=(d-1)b_d+m_d,\\
\eta=\min_{1\le k\le K}u_k>0,\qquad Q=2\sqrt a,\qquad
\gamma=\frac2{1+\sqrt2},\qquad
\mu=3\left(\frac{\gamma x^2}{4}\right)^{1/3},\qquad
C=Q+a/4.
\end{gathered}
\tag{34.3}
$$

The prescribed tail is a family of dual candidates, not an assumption
about the form of every attained dual. Its finite data are
$x,\ell,K,u_1,\ldots,u_K,a$.

**Theorem 34.2 (Sharp tail threshold and an effective finite test).**
For the prices in Definition 34.1,

$$
\lim_{d\to\infty}\Phi_d=Q.
\tag{34.4}
$$

In particular, if $\ell>Q$, these prices cannot satisfy all-degree
dual feasibility. If $0<\ell\le Q$, define the integer

$$
D=\max\left\{3,K+2,
 1+\left\lceil\frac\ell\eta\right\rceil,
 1+\left\lceil\left(\frac C\mu\right)^3\right\rceil\right\}.
\tag{34.5}
$$

Then $\Phi_d>\ell$ for every integer $d\ge D$. Consequently

$$
\bigl[\ell\le\Phi_d\text{ for every integer }d\ge3\bigr]
\quad\Longleftrightarrow\quad
\bigl[\ell\le\Phi_d\text{ for }3\le d<D\bigr].
\tag{34.6}
$$

Every quantity on the right is a finite minimum of explicitly given
real numbers. The assertion includes the critical case $\ell=2\sqrt a$;
no strict gap between the limiting tail value and $\ell$ is required.
If $Q>\ell$, the alternative cutoff

$$
D_+=\max\left\{3,K+2,
 1+\left\lceil\frac\ell\eta\right\rceil,
 1+\left\lceil\frac{a}{4(Q-\ell)}\right\rceil\right\}
\tag{34.7}
$$

also has $\Phi_d>\ell$ for every $d\ge D_+$ and may replace $D$
in (34.6).

**Proof.** For every marked row $j\ge2$, the row price bounds give

$$
\frac{x-u_j}{j-1}\ge\frac xj.
\tag{34.8}
$$

For $j>K$ this uses $a\le x(K+1)\le xj$; thus the inequality
holds on the entire prescribed tail as well as the prefix.
Since $g(t)\ge\gamma t^2$ on $[0,1]$, minimize the following
real function over $s>0$:

$$
\frac xs+\frac{\gamma s^2}{d^2}.
$$

Its derivative vanishes at $s=(xd^2/(2\gamma))^{1/3}$;
it decreases before this point and increases afterwards. Its minimum
is $\mu d^{-2/3}$. The admissible marked rows are a subset of these
positive real arguments, so

$$
m_d\ge\mu d^{-2/3}>0.
\tag{34.9}
$$

For a tail row $k>K$, reuse the scalar inequality (24.2), with
$z=k^2/(d^2+k^2/4)>0$. It gives

$$
\begin{aligned}
u_k+g(k/d)
&\ge\frac a{k^2}+z
 =\frac a{d^2z}+z-\frac a{4d^2}\\
&\ge\frac{2\sqrt a}{d}-\frac a{4d^2}.
\end{aligned}
\tag{34.10}
$$

The final step is the arithmetic-geometric mean inequality. Every
prefix row has unmarked price at least $\eta$. Therefore

$$
b_d\ge\min\left\{\eta,\frac Qd-\frac a{4d^2}\right\}.
\tag{34.11}
$$

For $d\ge D$, the prefix alternative satisfies
$(d-1)\eta\ge\ell$. With (34.9) its column contribution is
strictly larger than $\ell$. In the tail alternative, (34.9) gives

$$
\begin{aligned}
(d-1)\left(\frac Qd-\frac a{4d^2}\right)+m_d
&\ge Q-\frac Cd+\frac a{4d^2}+\mu d^{-2/3}\\
&>Q\ge\ell.
\end{aligned}
\tag{34.12}
$$

Indeed (34.5) makes $d>(C/\mu)^3$. Both alternatives in (34.11)
thus give strict column slack. This proves (34.6), including equality
at the tail threshold. The marked term in (34.9) is essential here:
its order $d^{-2/3}$ dominates the negative correction of order $d^{-1}$.

For (34.7), nonnegative $v_j$ imply $m_d\ge b_d$. Hence

$$
\Phi_d\ge d b_d
 \ge\min\left\{d\eta,Q-\frac a{4d}\right\}>\ell
 \qquad(d\ge D_+).
\tag{34.13}
$$

It remains to prove the exact threshold (34.4). Equation (34.11)
gives $\liminf_d(d-1)b_d\ge Q$. For sufficiently large $d$, the
integer $k_d=\lfloor a^{1/4}\sqrt d\rfloor$ exceeds $K$ and lies
strictly below $d$. It obeys $k_d^2/d\to\sqrt a$. Since
$g(t)/t^2\to1$ as $t\downarrow0$,

$$
(d-1)\{a/k_d^2+g(k_d/d)\}\longrightarrow2\sqrt a=Q.
\tag{34.14}
$$

Testing the unmarked minimum at $k_d$ proves
$(d-1)b_d\to Q$. Similarly, for sufficiently large $d$, let
$j_d=\lfloor d^{2/3}\rfloor$. This is an admissible marked row and

$$
0\le m_d\le\frac{x}{j_d-1}+g(j_d/d)\longrightarrow0.
\tag{34.15}
$$

The bound uses $u_{j_d}\ge0$. Thus $\Phi_d\to Q$, and $\ell>Q$
is incompatible with all-degree feasibility. Every tested pair of
indices above has the original strict inequality $k,j<d$. ∎

**Corollary 34.3 (Finite evidence for an actual row-one certificate).**
Fix data in Definition 34.1 with $K\ge2$ and $\ell\le Q$.
Suppose the finite inequalities on the right of (34.6) hold.
Let $y$ be an actual finite flow in Definition 20.1, with

$$
\mathcal N(y)=1,\qquad b_k(y)\ge0\ (k\ge1),\qquad
b_k(y)=0\ (k\ge2),\qquad
x\mathcal R(y)+\mathcal C(y)=\ell.
\tag{34.16}
$$

Here $b_k(y)=W_k-I_k$ is the flow injection, distinct from the
column minimum $b_d$ in (34.3). Then $\Psi(x)=\ell$,
$y$ is scalarized optimal, and (34.2) is an attained all-degree
dual with $\lambda=0$ at every harmless cap in Lemma 27.2.
In particular, with $\mathsf T_2$ from Definition 31.1,

$$
\ell\le\mathsf T_2(x),\qquad
G_2=0\ \Longleftrightarrow\ \ell=\mathsf T_2(x).
\tag{34.17}
$$

If the same finite evidence has $\ell<\mathsf T_2(x)$, it is a
strict counterexample to (33.1), with
$G_2\ge2\{\mathsf T_2(x)-\ell\}>0$.
No existence of such strict evidence is asserted.

More generally, whenever a feasible dual of Definition 34.1 has
$\ell=\Psi(x)$, every countable optimum has $t_d=0$ for $d\ge D$.
It therefore has finite incidence support. This last assertion does
not require the injection to be at row one.

**Proof.** Theorem 34.2 supplies every omitted column inequality.
The row equalities and nonnegative prices are those of Theorem 15.3
with $A=x$, $\beta=1$, $\lambda=0$. Its weak-duality summation
(15.6) gives $\ell\le xr+c$ on every countable feasible array with
finite $r,c$; the row-price sum is bounded by $xr$ and the cost sum
by $c$. By Proposition 20.2, the single flow in (34.16) reconstructs
an array satisfying every balance in (7.3), with exactly its stated
normalization, resource and cost. Thus $\Psi(x)\le\ell$, proving
equality and actual attainment. Lemma 27.2 places this optimum
strictly inside every stated harmless cap. The candidate dual is
therefore attained there. Theorem 31.3 and Corollary 31.4 now give
(34.17) and the positive-gap bound.

For the last assertion, choose any countable optimum and a harmless
cap. Equality in the weak-duality sum forces
$t_d(\Phi_d-\ell)=0$ for each $d$. Theorem 34.2 gives strict
slack at every $d\ge D$, so all those $t_d$ vanish. Every remaining
incidence index has $k<d<D$, and $q_k\le E_k$ excludes unused
source rows. Thus the support is finite. This uses full row balances,
not finite moments of an uncoupled tail. ∎

## 35. Uniform finite tests and a critical certificate with explicit contacts

**Corollary 35.1 (One omitted-degree cutoff for bounded price data).**
Let $\xi$ range over an arbitrary set. For each $\xi$ suppose
Definition 34.1 holds with a common $K$ and with

$$
\begin{gathered}
x(\xi)\ge x_->0,\qquad 0<\ell(\xi)\le L<\infty,\\
\min_{k\le K}u_k(\xi)\ge\eta_->0,\qquad
0<a(\xi)\le a_+<\infty,\qquad
\ell(\xi)\le2\sqrt{a(\xi)}.
\end{gathered}
\tag{35.1}
$$

Put $\mu_-=3(\gamma x_-^2/4)^{1/3}$ and
$C_+=2\sqrt{a_+}+a_+/4$. Then

$$
D_* =\max\left\{3,K+2,
1+\left\lceil L/\eta_-\right\rceil,
1+\left\lceil(C_+/\mu_-)^3\right\rceil\right\}
\tag{35.2}
$$

has $\Phi_d(\xi)>\ell(\xi)$ simultaneously for every $\xi$ and
$d\ge D_*$. Thus feasibility of this entire family reduces exactly
to its column inequalities $3\le d<D_*$. All equalities and ties
in those finite tests are allowed; the parameter set need not be
an interval and no continuity of the price data is assumed.

**Proof.** In (34.9)--(34.12), use $\eta_-,\mu_-$ as lower bounds
and $L,C_+$ as upper bounds. The two alternatives are strictly
larger than $\ell(\xi)$ at (35.2), by the same inequalities.
The finitely many remaining columns are necessary and sufficient
for each $\xi$. ∎

**Proposition 35.2 (An exact critical certificate at $x=1/4$).**
Write

$$
\begin{gathered}
A_0=g(1/3),\qquad B_0=g(2/3),\\
p=\frac{1/2-4A_0+B_0}{5},\qquad
\ell=\frac{13}{20}+\frac{14}{5}A_0+\frac45B_0,\qquad
a=\ell^2/4.
\end{gathered}
\tag{35.3}
$$

At $x=1/4$, take $K=2$, $u_1=x$, $u_2=p$, and the tail (34.2).
These prices are all-degree feasible at $\ell$, with critical
value $Q=\ell$. The normalized pair flow $(d,e)=(3,6)$ is
scalarized optimal, so $\Psi(1/4)=\ell=\mathsf T_2(1/4)$ and
$G_2=0$. This is a specialization of the certification theorem;
it does not impose a parameter restriction on Open boundary 33.1.

**Proof.** The exact radicals $A_0=2\sqrt{10}/3-2$ and
$B_0=2\sqrt{13}/3-2$ give

$$
\frac{9419}{10^5}<p<\frac{9420}{10^5},\qquad
\frac{127587}{10^5}<\ell<\frac{127589}{10^5}.
\tag{35.4}
$$

In particular $0<p<x/2$, $\eta=p$, $13<\ell/p<14$,
and $0<a<3x$. Also $\gamma>41/50$ gives $\mu>7/10$,
while $C=\ell+\ell^2/16<7/5$. Thus $(C/\mu)^3<8$ and
(34.5) has exactly $D=15$.

Here are all the remaining column minima. The entries $k_d,j_d$
are respectively their unique unmarked and marked minimizing rows;
the last column is a rational lower bound for $\Phi_d-\ell$.

| $d$ | $k_d$ | $j_d$ | Column slack |
| --- | --- | --- | --- |
| 3 | 1 | 2 | $0$ |
| 4 | 1 | 2 | $>50/1000$ |
| 5 | 2 | 2 | $>27/1000$ |
| 6 | 2 | 2 | $0$ |
| 7 | 2 | 2 | $>5/1000$ |
| 8 | 2 | 2 | $>31/1000$ |
| 9 | 2 | 2 | $>72/1000$ |
| 10 | 3 | 3 | $>114/1000$ |
| 11 | 3 | 3 | $>82/1000$ |
| 12 | 3 | 3 | $>62/1000$ |
| 13 | 3 | 3 | $>52/1000$ |
| 14 | 3 | 3 | $>49/1000$ |

For completeness these finite radical comparisons have the following
rational verification. Let $H=10^9$ and, for every $1\le k<d\le14$,
put

$$
\begin{gathered}
n_{kd}=\left\lfloor
\sqrt{\left\lfloor H^2(d^2+k^2)/d^2\right\rfloor}\right\rfloor,\\
G^-_{kd}=2n_{kd}/H-2,\qquad G^+_{kd}=G^-_{kd}+2/H.
\end{gathered}
\tag{35.5}
$$

The defining integer inequalities
$n_{kd}^2d^2\le H^2(d^2+k^2)<(n_{kd}+1)^2d^2$ imply
$G^-_{kd}\le g(k/d)<G^+_{kd}$. Substituting the bounds for
$(k,d)=(1,3),(2,3)$ in (35.3) gives the enclosing intervals

$$
\begin{gathered}
p_- =\frac{235480209}{2500000000},\qquad
p_+ =\frac{117740107}{1250000000},\\
L_- =\frac{1594848721}{1250000000},\qquad
L_+ =\frac{159484873}{125000000},\qquad
p_-\le p\le p_+,\quad L_-\le\ell\le L_+.
\end{gathered}
\tag{35.6}
$$

Define $U^-_1=U^+_1=1/4$, $U^-_2=p_-$, $U^+_2=p_+$, and
$U^-_k=L_-^2/(4k^2)$, $U^+_k=L_+^2/(4k^2)$ for $k\ge3$.
For each column set

$$
\begin{aligned}
B^-_{kd}&=U^-_k+G^-_{kd},&
B^+_{kd}&=U^+_k+G^+_{kd},\\
M^-_{jd}&=\frac{1/4-U^+_j}{j-1}+G^-_{jd},&
M^+_{jd}&=\frac{1/4-U^-_j}{j-1}+G^+_{jd}.
\end{aligned}
\tag{35.7}
$$

The finite rational inequalities, with $k_d,j_d$ from the table, are

$$
\begin{gathered}
B^-_{kd}-B^+_{k_d,d}>1/2000
 \quad(3\le d\le14,\ 1\le k<d,\ k\ne k_d),\\
M^-_{jd}-M^+_{j_d,d}>1/250
 \quad(3\le d\le14,\ 2\le j<d,\ j\ne j_d),\\
(d-1)B^-_{k_d,d}+M^-_{j_d,d}-L_+>s_d/1000
 \quad(d\in\{4,5,7,8,9,10,11,12,13,14\}),\\
(s_4,s_5,s_7,s_8,s_9,s_{10},s_{11},s_{12},s_{13},s_{14})
 =(50,27,5,31,72,114,82,62,52,49).
\end{gathered}
\tag{35.8}
$$

All their inputs are the displayed integers and rational operations;
(35.5) specifies each integer by its two square inequalities.
Thus (35.8) verifies both the stated minimizers and the strictly
positive slack entries. The two zero entries instead follow exactly
from (35.3):

$$
\Phi_3=3x+2A_0+B_0-p=\ell,\qquad
\Phi_6=4p+x+6A_0=\ell.
\tag{35.9}
$$

Theorem 34.2 now supplies every column $d\ge15$.

Finally use the actual pair flow of Proposition 23.2:
$y_{123}=8/5$, $y_{226}=1$, all other entries zero. Its
normalization is $(8/5)/2+1/5=1$; $W_2=I_2=1$ and its only
injection is $b_1=8/5$. The full correspondence of Proposition
20.2 gives (7.3), resource $r=13/5$ and cost
$c=14A_0/5+4B_0/5$. Thus $xr+c=\ell$, proving actual
optimality by Corollary 34.3. As this is a pair flow,
$\Psi(x)\le\mathsf T_2(x)\le xr+c=\Psi(x)$, proving the
remaining equalities. ∎

## 36. Mathematical scope of the finite certification theorem

The reciprocal-square scalar lower estimate (34.10) reuses the
calculation inside Proposition 24.1. The new conclusion is an exact
finite test for arbitrary positive finite price prefixes and arbitrary
$x>0$, with a free prescribed tail amplitude. Equations
(34.9)--(34.12) close the critical threshold using the marked price,
and (34.14)--(34.15) prove that the limiting threshold is necessary
for this entire family. No such arbitrary-prefix, critical-tail
certification is assumed in Sections 15--33. The uniform cutoff and
the exact specialization in Section 35 are consequences for these
same dual candidates. The minimization of $x/s+\gamma s^2/d^2$
and the arithmetic-geometric mean inequality are elementary
intermediate tools, not new general optimization principles.

The CDSO convention remains that of Albalahi--Das--Ali--Barman--Hamza,
[arXiv:2510.24809v1](https://arxiv.org/html/2510.24809v1),
Section 1, equation (1) and the following definition, DOI
[10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176):
the denominator is the maximum endpoint degree and the factor
$1/\sqrt2$ is dropped. The only reused finite affine LP duality
input remains Boyd--Vandenberghe,
[author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf),
Sections 5.2.3--5.2.4, printed pp.226--227. The new tail estimates
are repo-derived for the explicit nonlinear cost and marked balances;
they invoke no countable strong-duality or finite-moment cubature
theorem. Technical full-text overlap with Zhao--Zhao, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
remains unassessed. No worldwide-priority assertion is made.

**Open boundary 36.1 (Return and support questions after finite
certification).** Open boundary 33.1 remains unresolved: no proof
has been supplied that every coefficient admitting an actual
row-one-only optimum has $\Psi(x)\ge\mathsf T_2(x)$, and no
strict instance of Corollary 34.3 with $\ell<\mathsf T_2(x)$
has been supplied. The theorem makes a proposed all-degree
certificate finitely verifiable once its stated price family is
specified. It does not show that every attained dual has that form,
or produce a feasible prefix at $\ell=\mathsf T_2(x)$ for every
coefficient in the original hypothesis. Those are additional
mathematical obligations, not consequences of (34.6).

In particular, the obstruction $\ell>2\sqrt a$ refutes only a
prescribed price tail. Failure of its finite tests would likewise
refute that candidate, not (33.1). Conversely, a certified strict
return gap would still allow finite optimal flows on three or more
rows. It would not establish $x\notin S$.

Universal scalarized finite attainment in Open boundary 30.1 and
the complete assertion or genuine refutation of Open problem 18.2
remain unresolved. Their connection is exactly Theorem 29.2,
using the exact resource-face replacement of Theorem 28.1 and the
capped-face identity of Proposition 28.2. The one-injection
reduction in Theorem 21.1, finite non-singleton components in
Lemma 23.1 and harmless-cap lemma 27.2 retain their original
hypotheses. Theorem 29.4 retains every positive compact rectangle,
equal endpoints, winning-cap ties, strict incidence inequalities
and the exact original integer sequences (29.7). No conclusion
about all original minimizers, an exactly attaining connected
rooted pattern, or universal original-graph finite sufficiency
follows from the certificate at a single coefficient.

## 追加锚（本行以下为增补区）

## 37. An active-price ceiling and the comparison parameters

**Definition 37.1 (Return comparison coordinates).** Retain exactly (7.3), (20.1), (27.1) and (31.1), with the nonlinear cost $g(t)=2(\sqrt{1+t^2}-1)$. Write

$$
\begin{gathered}
p(x)=\vartheta_x,\quad L_2(x)=\mathsf T_2(x)=\mathfrak B(x)-p(x),\quad
h_e=e g(2/e),\quad H(p)=\min_{e\ge3}\{ep+h_e\},\quad J(p)=H(p)-p\quad(p>0),\\
x_0=1/5000,\qquad x_*=2\{g(2/3)-g(1/3)\},\qquad
V_j(L)=2-\sqrt{4-(L/j)^2}\quad(0<L<2j),\\
\mathcal D_{jd}(x)=(d-1)\{p(x)+g(2/d)\}
 +\frac{x-V_j(L_2(x))}{j-1}+g(j/d)-L_2(x)\quad(3\le j<d,\ L_2(x)<2j).
\end{gathered}
\tag{37.1}
$$

**Lemma 37.2 (Exact comparison coordinates and the possible entrance range).** For every $x>0$,

$$
J(p(x))=\mathfrak B(x)-x,\qquad
L_2(x)=x-2p(x)+H(p(x)),\qquad p(x)>x/4.
\tag{37.2}
$$

The functions $J$ and $p(x)$ are continuous and strictly increasing. If an actual normalized scalarized optimum has injection only at row one, then $x\le x_*$ and $p(x)\le x/2$.

**Proof.** Proposition 31.2 makes the maximum defining $p(x)$ attained. The inequalities $(e-1)p(x)+h_e\ge\mathfrak B(x)-x$, with equality for a maximizing $e$, give the first identity; the second follows by subtraction. Each affine function defining $J$ has slope at least two. Its locally finite minimum is continuous and strictly increasing, with limits zero and infinity at the two ends of $(0,\infty)$. The same properties of $\mathfrak B(x)-x$, whose affine slopes are $d-1\ge2$, prove the assertion about $p$ by inversion.

For a minimizing entrance degree $d$, choose $e=4d-3$. Taylor's lower bound for $g$ and its quadratic upper bound give

$$
C_d\ge\frac{d+3}{d^2}-\frac{d+15}{4d^4}>\frac4{4d-3}\ge h_{4d-3}.
\tag{37.3}
$$

The strict inequality is equivalent to $36d^3-40d^2-57d+45>0$, valid for $d\ge3$. Therefore $f_{4d-3}(x)>x/4$, proving (37.2). Theorem 31.3 gives $p(x)\le u_2\le x/2$ under the actual-optimum hypothesis. The elementary square bounds $59/100<x_*<3/5$, $C_3<63/100$ and $C_4>1/10$ imply that $B_3(x)<B_d(x)$ for $d\ge4$ whenever $x\ge x_*$: for $d=4$ compare $x+C_4-C_3$, and for $d\ge5$ compare $(d-3)x-C_3$. Hence at such an $x$, $p(x)\ge f_3(x)=x-x_*/2$. Together with $p(x)\le x/2$, this forces $x\le x_*$. ∎

**Lemma 37.3 (Exact nonlinear ceiling on every active row).** Fix any scalarized countable optimum and any attained all-degree dual at a harmless cap. If row $k$ is active and $\ell<2k$, then

$$
u_k\le V_k(\ell).
\tag{37.4}
$$

If the optimum has injection only at row one, a positive action $(2,j,d)$ with $j\ge3$ necessarily satisfies $\mathcal D_{jd}(x)\le0$.

**Proof.** Saturation gives positive unmarked mass in every active row. At one of its unmarked contacts, $b_d=u_k+g(k/d)$. Since $m_d\ge b_d$ and that column is active, $\ell=(d-1)b_d+m_d\ge db_d$. Thus $u_k\le\ell/d-g(k/d)$. For $0<a<2$, differentiation gives

$$
\sup_{z\ge0}\{az-g(z)\}=2-\sqrt{4-a^2}.
\tag{37.5}
$$

Apply this with $a=\ell/k$ and $z=k/d$. This proves (37.4) using the exact cost, and strengthens the active-row estimate (19.2).

For a row-one optimum, put $p_*=u_2$ and $\ell=\Psi(x)$. Theorem 31.3 and feasible pair comparison give $p_*\ge p(x)$ and $\ell\le L_2(x)$. Lemma 37.2 gives $x\le x_*$. Also $L_2(x)<B_3(x)<243/100<6$, so (37.4) applies to every active $j\ge3$. At a positive action, Proposition 20.2 gives

$$
0=(d-1)\{p_*+g(2/d)\}
 +\frac{x-u_j}{j-1}+g(j/d)-\ell\ge\mathcal D_{jd}(x).
\tag{37.6}
$$

Here $V_j$ is increasing, so $u_j\le V_j(\ell)\le V_j(L_2(x))$. All prices, contacts and incidences in this argument belong to the same actual optimum and its all-degree dual. ∎

## 38. Analytic exclusion at small comparison prices

**Lemma 38.1 (A uniform small-price departure inequality).** Suppose $0<p\le10^{-4}$ and $2p\le x\le4p$. Set $L=x-2p+H(p)$ and, for $3\le j<d$, set

$$
D_{jd}=(d-1)\{p+g(2/d)\}+\frac{x-V_j(L)}{j-1}+g(j/d)-L.
\tag{38.1}
$$

Then $D_{jd}>0$ for every such integer pair. Consequently, under the row-one-optimum hypothesis, no positive action $2\longrightarrow j\ge3$ exists when $0<x\le x_0$.

**Proof.** Put $s=\sqrt p\le1/100$. Rounding $2/s$ to a nearest integer $e$ and using $g(t)\le t^2$ gives

$$
H(p)\le ep+4/e\le4s+\frac{s^3}{8-2s}\le4s+s^3/7,
\qquad L\le4s+2s^2+s^3/7.
\tag{38.2}
$$

The last upper bound yields, for every $j\ge3$,

$$
V_j(L)\le\frac{4p}{j^2}(1+21s/20)<\frac{2p}{j}\le\frac xj.
\tag{38.3}
$$

To verify the first inequality, write $a=1+s/2+s^2/28$ and $z=(2sa/j)^2$. Then $a^2\le1+s+s^2/3<9/8$, so $z\le s^2/2$. Rationalizing $V_j$ and using $2/(1+\sqrt{1-z})\le1+z$ gives
$V_j(L)/(4p/j^2)\le a^2(1+z)\le1+s+s^2\le1+21s/20$.

Write $h(t)=tp+2\sqrt{t^2+4}-2t$ and $R_d=h(d)-H(p)\ge0$. Subtraction in (38.1) gives exactly

$$
D_{jd}=R_d+p-\frac{j-2}{j-1}x-\frac{V_j(L)}{j-1}
                  +g(j/d)-g(2/d)\ge R_d-3p.
\tag{38.4}
$$

The critical point of $h$ lies strictly between $3/(2s)$ and $5/(2s)$; this follows directly from $s\tau(s^2)=2(2-s^2)/\sqrt{4-s^2}$. Its derivative is negative before that point and positive after it. Taylor's lower bound $g(t)\ge t^2-t^4/4$, evaluated at these two endpoints, therefore gives

$$
\begin{aligned}
d\le3/(2s)&\ \Longrightarrow\ R_d\ge s/6-(32/27+1/7)s^3>3p,\\
d\ge5/(2s)&\ \Longrightarrow\ R_d\ge s/10-(32/125+1/7)s^3>3p.
\end{aligned}
\tag{38.5}
$$

This proves the assertion outside $3/2\le w=ds\le5/2$. Inside this interval,

$$
R_d\ge\frac{s(w-2)^2}{w}-(32/27+1/7)s^3.
\tag{38.6}
$$

For $j=3$, (38.3), the same Taylor bounds, and the tangent inequality $5/w^2\ge5/4-(5/4)(w-2)$ imply

$$
\begin{aligned}
D_{3d}&\ge\frac25s(w-2)^2-\frac54s^2(w-2)+\frac{s^2}{36}
 -(32/27+1/7+7/30)s^3-4s^4\\
&\ge\frac{s^2}{36}-(32/27+1/7+7/30+125/128+4s)s^3\\
&>s^2\{1/36-(8/3)s\}\ge p/900>0.
\end{aligned}
\tag{38.7}
$$

The second line completes the square. The coefficient in parentheses is less than $8/3$ for $s\le1/100$. For $j=4$, use $V_4(L)\le21p/80$ and $R_d\ge0$; for $j\ge5$, use (38.4) before discarding its last difference and the monotonicity of $g$. These give respectively

$$
\begin{aligned}
D_{4d}&\ge p(1-8/3-7/80+48/25)-(1024/81)p^2>p/10,\\
D_{jd}&\ge(84/25-3)p-(2500/81)p^2>p/3\quad(j\ge5).
\end{aligned}
\tag{38.8}
$$

Here $g(4/d)-g(2/d)\ge12/d^2-64/d^4$ and $g(5/d)-g(2/d)\ge21/d^2-625/(4d^4)$, with $3/(2s)\le d\le5/(2s)$. This proves the full integer assertion. Finally, for an actual row-one optimum with $x\le x_0$, Lemma 37.2 gives $x/4<p(x)\le x/2\le10^{-4}$. Apply the assertion with $p=p(x)$, $L=L_2(x)$, and contradict (37.6). ∎

## 39. Exact endpoint exclusion on the remaining coefficient interval

**Proposition 39.1 (A finite algebraic inequality for the whole interval).** For every $x\in[x_0,x_*]$ and integers $3\le j<d\le580$,

$$
\mathcal D_{jd}(x)>x/50.
\tag{39.1}
$$

**Proof.** All entrance minimizers on this interval have degree at most 144. Indeed $C_{72}\le75/72^2$ and
$\mathfrak B(x)/x\le72+5000C_{72}<145$. Also $p(x)>x/4\ge1/20000$. The derivative of $ep+h_e$ in its real argument is greater than $p-4/e^2$, so every return minimizer has degree at most 580. Thus both minima in (37.2) may be taken over these finite ranges.

For the continuous extension $C(t)=(t-1)g(1/t)+g(2/t)$, direct differentiation gives

$$
C''(t)=\frac{2(t^3-3t^2-2)}{t^3(t^2+1)^{3/2}}
       +\frac{8(3t^2+8)}{t^3(t^2+4)^{3/2}}>0\quad(t\ge3).
\tag{39.2}
$$

For the sign, use $((t^2+4)/(t^2+1))^{3/2}<3/2$. The resulting numerator is greater than $2t^3+10t^2+116/3$. Since $C(t)>0$ tends to zero, it is decreasing. The extension $h(t)=2\sqrt{t^2+4}-2t$ is also decreasing and strictly convex. Hence entrance changes occur only at $t_d=C_d-C_{d+1}$, and return changes only at $r_e=h_e-h_{e+1}$. At a return change, (37.2) gives the coefficient

$$
X_e=\max_{3\le a\le144}\frac{(e-1)r_e+h_e-C_a}{a-1}.
\tag{39.3}
$$

This is the inverse of $\min_a\{(a-1)x+C_a\}$ at $(e-1)r_e+h_e$. Therefore all phase endpoints in $[x_0,x_*]$ are exactly the members there of

$$
\mathcal Q=\{x_0,x_*\}\cup\{t_d:3\le d\le143\}
                       \cup\{X_e:3\le e\le579\}.
\tag{39.4}
$$

Between successive endpoints both $p(x)$ and $L_2(x)$ are affine. The function $V_j$ is convex on $(0,2j)$, so $\mathcal D_{jd}(x)-x/50$ is concave on each such phase. Its positivity at every endpoint suffices. Throughout the interval $0<L_2(x)<B_3(x)<243/100<2j$.

Here is a complete rational specification of the endpoint comparisons. All intervals below are integer intervals representing the enclosed real number multiplied by $A=10^{18}$. For $1\le k<d\le580$, define

$$
\begin{gathered}
n_{kd}=\left\lfloor\sqrt{\left\lfloor A^2(d^2+k^2)/d^2\right\rfloor}\right\rfloor,\\
G_{kd}^-=2n_{kd}-2A,\qquad G_{kd}^+=G_{kd}^-+2,\\
C_d^-=(d-1)G_{1d}^-+G_{2d}^-,\quad C_d^+=(d-1)G_{1d}^++G_{2d}^+,\qquad
h_e^-=eG_{2e}^-,\quad h_e^+=eG_{2e}^+.
\end{gathered}
\tag{39.5}
$$

The square inequalities $n_{kd}^2d^2\le A^2(d^2+k^2)<(n_{kd}+1)^2d^2$ enclose the exact $g(k/d)$. Construct an interval $[q_-,q_+]$ for each candidate in (39.4) by ordinary outward interval arithmetic: addition and subtraction use the corresponding endpoint sums and differences; multiplication or division by a positive integer rounds the lower endpoint down and the upper endpoint up; minima and maxima act separately on the two endpoints. In particular use $r_e\in[h_e^--h_{e+1}^+,h_e^+-h_{e+1}^-]$ in (39.3). The endpoints $x_0$ and $x_*$ have intervals $[A/5000,A/5000]$ and $[2(G_{23}^--G_{13}^+),2(G_{23}^+-G_{13}^-)]$.

The intervals decide membership strictly for every other candidate: 71 entrance points and 276 return points lie strictly between the endpoints; the other 70 and 301 candidates lie outside. All 349 retained intervals are pairwise disjoint. For each retained interval put

$$
\begin{gathered}
B_- =\min_{3\le a\le144}(a q_-+C_a^-),\quad
B_+ =\min_{3\le a\le144}(a q_++C_a^+),\\
p_- =\max_{3\le e\le580}\left\lfloor\frac{B_--q_+-h_e^+}{e-1}\right\rfloor,\quad
p_+ =\max_{3\le e\le580}\left\lceil\frac{B_+-q_--h_e^-}{e-1}\right\rceil,\qquad L_+=B_+-p_-,\\
z_j=\left\lfloor\sqrt{\left\lfloor(4A^2j^2-L_+^2)/j^2\right\rfloor}\right\rfloor,\qquad V_j^+=2A-z_j,\\
K_{qjd}=(d-1)(p_-+G_{2d}^-)
 +\left\lfloor\frac{q_--V_j^+}{j-1}\right\rfloor+G_{jd}^--L_+.
\end{gathered}
\tag{39.6}
$$

These integers satisfy $A\mathcal D_{jd}(q)\ge K_{qjd}$. In particular $L_+/A$ encloses $L_2(q)$ from above, and $z_j/A$ encloses its required square root from below. The complete finite comparisons are the following; each minimum includes every retained $q$ in the indicated row and every $4\le d\le580$, $3\le j<d$.

| Endpoint window | Points | Comparisons | $\min\lfloor10^{12}K_{qjd}/q_+\rfloor$ | Strict bound $K_{qjd}/q_+$ |
| --- | --- | --- | --- | --- |
| $[1/5000,1/1000)$ | 197 | 32850341 | 20422291405 | $>1/50$ |
| $[1/1000,1/100)$ | 108 | 18009324 | 35287873393 | $>7/200$ |
| $[1/100,1/10)$ | 33 | 5502849 | 80874749690 | $>2/25$ |
| $[1/10,x_*]$ | 11 | 1834283 | 162915745818 | $>4/25$ |

There are $577\cdot578/2=166753$ comparisons per endpoint and 58196797 in total. Every entry is determined by the integer square inequalities and directed quotients in (39.5)--(39.6); no approximate optimizer or presumed contact is an input. Since each strict bound exceeds or equals $1/50$, this proves positivity at all phase endpoints. Phasewise concavity proves (39.1), including both ends and all degree ties. ∎

## 40. Full return, scalarized attainment and the original graph consumer

**Theorem 40.1 (The full row-one return assertion).** For every $x>0$, every actual normalized scalarized optimal flow with injection only at row one has source support exactly $\{1,2\}$ and finite incidence support. In particular

$$
\Psi(x)=\mathsf T_2(x),\qquad G_2=0
\tag{40.1}
$$

for every attained all-degree dual at a harmless cap. Thus the implication in Open boundary 33.1 holds with all its original hypotheses.

**Proof.** Use the actual all-degree dual supplied by Theorem 15.3 and Lemma 27.2. Entrance rigidity and Lemma 37.2 put $0<x\le x_*$ and make every row-one action target two. Lemma 38.1 excludes every action $2\longrightarrow j\ge3$ when $x\le x_0$. For $x\ge x_0$, a positive row-two action has, by Lemma 20.3,

$$
d\le1+\ell/u_2\le1+L_2(x)/p(x)
 <1+4\{72+5000C_{72}\}<581.
\tag{40.2}
$$

Here $C_{72}\le75/72^2$, and $\ell\le L_2(x)\le\mathfrak B(x)$. Its integer degree is therefore at most 580. Proposition 39.1 now contradicts the necessary inequality (37.6) for every $j\ge3$. All actions out of row two must return to two.

The exact resolvent (21.2) makes the active rows precisely those reachable from the nonzero injection. Its only reachable rows are one and two, both active. Lemma 20.3 gives finitely many actions at each of these fixed rows, and Proposition 20.2 reconstructs the same finite normalized array satisfying every constraint in (7.3). Proposition 23.2 expresses this flow as a convex combination of actual normalized pair flows, preserving both resource and cost. Its objective is at least $\mathsf T_2(x)$, while pair feasibility gives the reverse inequality for $\Psi$. This proves the first equality in (40.1); Corollary 31.4 proves $G_2=0$ for every attained dual, including tied minimizing degrees. ∎

**Corollary 40.2 (Universal scalarized and exact capped finite attainment).** One has $S=(0,\infty)$. Every capped problem $\mathcal L(\alpha,\beta;R)$ with $\alpha,\beta>0$ and $R>1$ has a finite attainer. For every countable capped optimum there is a finite capped optimum with exactly its resource and cost.

**Proof.** Fix $x>0$ and a harmless cap. Theorem 21.1 supplies a normalized one-injection scalarized optimum, since $\lambda=0$. If its injection is at $h\ge2$, Lemma 23.1 makes its reachable support finite. If its injection is at one, Theorem 40.1 makes it finite. Proposition 20.2 gives a finite feasible array in either case. Hence $x\in S$, answering the existence obligation of Open boundary 30.1.

For a capped problem choose any attained dual, put $x=(\alpha+\lambda)/\beta$, and take any countable capped optimum $Q_*$. Proposition 28.2 puts $Q_*$ in $\mathscr O_x$. Universal $S$ supplies the two-sided sequences $x(1\pm1/(n+2))\in S$, so Theorem 28.1 supplies finite arrays at both exact resource endpoints of this scalarized face. Their appropriate convex mixture has exactly $r(Q_*),c(Q_*)$ and retains every countable balance. If $\lambda>0$, complementarity gives $r(Q_*)=R$ and the mixture hits that cap exactly. If $\lambda=0$, its preserved resource is at most $R$, with equality allowed. Equation (28.6) gives capped optimality in both cases. Coincident resource endpoints and scalarized ties are included. ∎

**Corollary 40.3 (Every positive compact rectangle and every original integer sequence).** Open problem 18.2 has the affirmative answer with exactly $M_{\mathcal K}=\widehat M_{\mathcal K}$ in (17.1)--(17.3), for every positive finite-endpoint rectangle, including equal endpoints. Thus $F_{\widehat M_{\mathcal K}}=F$ everywhere on that rectangle, with the original $J_0$, admissibility $R_j>1$, infeasible-branch convention and all winning ties. On every integer sequence (29.7), the exact original-graph limit and bounded-tail recovery in (29.8) hold with exactly $B_{\mathcal K}$ in (18.1).

**Proof.** At any positive pair, choose any winning branch of the unchanged finite minimum (10.2). Its parameters are $\alpha=2\kappa/D$, $\beta=D\kappa$, $R=R_j=Dj/\kappa>1$. Corollary 40.2 supplies finite attainment even if its cap binds. Theorem 17.1 gives the common endpoint-only cutoff without separating tied winners, hence the stated uniform equality. Theorem 18.1 then applies to every sequence $a_n\ge4$, $h_n,N_n\ge1$ with $a_n\to\infty$, $h_n/\sqrt{a_n}\to\kappa>0$, $N_n/a_n^{3/2}\to D>0$. Its strict-cap mixing, Theorem 8.1 and Theorem 11.1 preserve all marked balances, strict incidence inequalities and exact counts $N_n$, $a_n+1+h_n$, $a_nN_n$, at every sufficiently large term, with no congruence restriction. Proposition 12.2 supplies the full-class lower limit. This is precisely the transfer in Corollary 29.4, now with its finite-attainment premise supplied. ∎

**Attribution 40.4 (Mathematical inputs and remaining scope).** The active-price ceiling, full-coefficient departure exclusion and their attainment consequences are deductions for this volume's exact marked arrays. The finite rational table is a proof of explicit algebraic inequalities over whole coefficient phases, rather than a finite-cutoff LP estimate. Differentiation, convexity, completing the square and integer square brackets are intermediate elementary tools; no countable moment representation or unproved dual-completion ansatz is used. The primal and all-degree dual existence inputs remain exactly Theorems 15.3, 15.6 and Lemma 27.2.

The original normalization is Albalahi--Das--Ali--Barman--Hamza, [arXiv:2510.24809v1](https://arxiv.org/html/2510.24809v1), Section 1, equation (1) and its following definition, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176): maximum endpoint degree in the denominator, with $1/\sqrt2$ dropped. The finite affine duality used in Theorem 15.3 is Boyd--Vandenberghe, [*Convex Optimization*](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf), Sections 5.2.3--5.2.4, printed pp.226--227, including feasibility under the affine refinement and attained dual value when finite. No extremal theorem from the first source is a premise here. Technical full-text overlap with Zhao--Zhao, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), remains unassessed; no worldwide-priority assertion is made.

The conclusions answer 33.1, 30.1 and 18.2 through the separate proofs above. They bound a recovery sequence, not every original graph minimizer or the core sink degrees. They assert no exact attaining connected rooted pattern, no smaller-order error, no moving-rectangle extension to zero or infinity, and no extension beyond the original common-law and graph domains. Corollary 15.4 continues to exclude exact branch attainment by a single fixed rooted pattern.

## 追加锚（本行以下为增补区）
