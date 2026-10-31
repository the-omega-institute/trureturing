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
