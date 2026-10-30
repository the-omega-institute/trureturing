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
