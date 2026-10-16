# FIB two paid reads: selective risk and seed availability

For the original biased XOR source, this volume determines every
two-read supporting objective for joint endpoint correctness and
budgeted return mass. A finite family of paid policies gives the exact
attained envelope when the independent auxiliary probability law may be
chosen. A particular exposed face has an explicit equation, and equality
on that face under any specified unchanged auxiliary law is equivalent
to a four-part measurable partition of its seed space.

These are ordinary mathematical results relative to the supplied texts.
The original law, finite-record interface, selective count coefficients,
zero-record bounds and one-read results retain their attribution to
[Original][Original] and [Risk][Risk]. The almost-sure-return two-read
slice belongs to [`FIB_TWO_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md`][Endpoint], *FIB two paid reads:
exact almost-sure-return endpoint risk*, §§5–6; it appears here only as an endpoint consequence of the
support formula. The complete frontier for each specified atomic
auxiliary law remains a separate question.

## 1. The source and the full acquisition contract

**Definition 1.1 (Original law and endpoint).** Fix $0<p<1$,
$p\ne1/2$, and a single $j\in\{0,1\}$. The four symbols in
$\mathcal A=\{a_0,a_1,b_0,b_1\}$ are distinct. Let $\varphi$ be
uniform on $\{0,1\}$, independently of iid Bernoulli$(p)$ spins
$(S_\ell)_{\ell\in\mathbb Z}$. On the original integer clock put

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=Y_\ell:=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

Write $J_p$ for this one joint law. Its active transition takes $a_s$
to $b_t$ with probability $\pi_t$, where $\pi_0=1-p$, $\pi_1=p$,
and emits $s\oplus t$. The next transition takes $b_t$ to $a_t$ and
emits zero. The stationary masses are
$(1-p,p,1-p,p)/2$: incoming mass at $b_t$ is
$\sum_s(\pi_s/2)\pi_t=\pi_t/2$, and copying supplies the same mass
at $a_t$. Thus this is the stationary emitted-bit clock of Original,
Proposition 2.1 and (2.2), including the separator positions. In
particular $X_tX_{t+1}=0$ at every integer $t$.

The target is the actual $H_j$ in (1.1). Define

$$
\begin{array}{c|cc}
 &j=0&j=1\\ \hline
h_0(s)&a_s&b_s\\
h_1(s)&b_s&a_s
\end{array}
\qquad v_0=j,\quad v_1=0.
\qquad H_j=h_\varphi(S_{v_\varphi}).
\tag{1.2}
$$

This is Original, (9.4). The two state pairs indexed by the phases are
disjoint. On a phase-ambiguous observation, one correct state cannot
collect correct masses from both pairs. The representation provides no
operation that observes an unacquired spin or the phase.

**Definition 1.2 (Paid arbitrary-address protocol).** Choose any
probability space $(\mathsf U,\mathcal U,\nu)$ independent of the
entire $J_p$ source and keep its law unchanged. Fixed public data can
be included as constants. All random public data and internal
randomness are included in this same auxiliary variable $u$. A finite
acquired record is an ordered list

$$
r=((t_1,x_1),\ldots,(t_n,x_n))
\in(\mathbb Z\times\{0,1\})^n,
\qquad n\in\mathbb N_0.
\tag{1.3}
$$

A measurable next-event rule, based only on these public data, $u$ and
$r$, either requests an integer address, returns a state
$A\in\mathcal A$, or continues internally forever without another
read or return. Finite events may follow internal waiting. The
occurrence, kind, address or output, and finite waiting time of such
an event are measurable functions of exactly these available data.
Waiting supplies no extra observation.

Every requested address $t$ returns the actual $X_t$ of (1.1), and
every actual call costs one read. This includes repeats, separator
zeros, negative and positive addresses, disconnected sets and
arbitrarily distant addresses. Ignoring a reply does not refund its
call. An address may depend on all previously acquired replies.

Let $\tau$ be return time, with $\tau=\infty$ on every nonreturn,
and let $N\in\mathbb N_0\cup\{\infty\}$ count all actual calls.
Internal nonreturn after finitely many calls, including zero, and
infinite-read paths are allowed. A return has finite $N$, and its
output and return time depend measurably only on the available data
and terminal acquired record. A zero-read return and a wrong-phase
output are permitted. Null records and versions completed by null
sets are included through the usual measurable completion.

There is no hidden-state, half-line or tail read, source-dependent
seed or timing, reset, law switch, moving endpoint, or replacement of
an erased coordinate. This is the full contract of Original,
Definition 9.1, also stated in Risk, Definition 1.2. Put
$\mathbb P_p=J_p\otimes\nu$.

**Definition 1.3 (Budgeted masses and parameters).** Throughout put

$$
\begin{gathered}
E_2=\{\tau<\infty,\ N\le2\},\qquad
q=\mathbb P_p(E_2),\\
L=\mathbb P_p(A\ne H_j,E_2),\qquad
C=\mathbb P_p(A=H_j,E_2)=q-L,\\
a=\max(p,1-p),\quad b=\min(p,1-p),\quad
\eta=ab,\quad c=a^2+b^2=1-2\eta,\quad \delta=a-b,\\
\sigma=\begin{cases}1&p>1/2,\\0&p<1/2,\end{cases}
\qquad x_+=\max(x,0).
\end{gathered}
\tag{1.4}
$$

In particular $a+b=1$, $0<b<1/2<a<1$, $0<\eta<1/4$,
$1/2<c<1$, and $\delta>0$. The majority spin $\sigma$ has mass $a$.
The risk $L$ is a joint four-state classification error on $E_2$;
for $q>0$ its conditional version is $L/q$. No conditional error is
defined here at $q=0$. This loss is distinct from Brier loss for an
erased visible bit.

No restriction is imposed on paths outside $E_2$. In particular they
may return after more calls, continue internally forever after any
finite count, or have infinitely many calls. The total return mass
need not be $q$.

## 2. Finite sections and elementary spin products

**Lemma 2.1 (Source sections and two-call representation).** At a fixed
seed, a consistent finite acquired record $r$ has exactly the source
section

$$
\mathcal C(r)=\{X_{t_i}=x_i:1\le i\le n\}.
\tag{2.1}
$$

An inconsistent record has empty section. For computing $(q,C)$, a
fixed-seed protocol can be represented by one of the following:
immediate return, complete rejection, or a depth-two binary tree with
root address $t$, second address $t_x$ after first reply $x$, and a
return/reject decision with a fixed output on each leaf. All calls in
this representation are actual paid calls. The original protocol is
not required to have two calls on paths outside $E_2$.

Proof. At a fixed seed and acquired prefix the next-event rule and its
internal delay are fixed. If the next action requests $t$, adjoining
reply $x$ intersects the preceding section with $\{X_t=x\}$.
A finite return adds no source restriction. Internal continuation
forever is also identical on that whole section. Induction proves
(2.1) for arbitrary adaptive choices, including repeated addresses;
contradictory repeated replies give empty sections. This is the
finite-section interface of Original, Theorems 9.2–10.1.

Any branch which will not return within two actual calls contributes
zero to both $q$ and $C$. In the representation mark it rejected,
irrespective of its later behavior. A branch returning after one call
can instead make a second actual call at the same address, ignore
the deterministic repeated reply, and retain its original output.
This paid padding preserves its source section, $q$ and $C$. A
short rejected branch may likewise be padded with actual repeats
and rejected. Once a root address is requested, the two possible
first replies have independently specified continuations, so these
operations give the stated tree. If there is no first read, the
first finite action is a zero-read return or there is internal
nonreturn; these are the other two cases.

This representation changes neither the values being bounded nor
the original class over which the bound is asserted. It makes no
claim about preserving expected cost or later behavior. $\square$

For a leaf section $D$, write

$$
W=J_p(D),\qquad M=\max_{h\in\mathcal A}J_p(D,H_j=h).
\tag{2.2}
$$

A deterministic output has correct mass at most $M$. For a fixed real
$\lambda$, this leaf's best contribution to $C-\lambda q$ is
$(M-\lambda W)_+$: return a maximizing state or reject. Null leaves
contribute zero. A zero-read return has $q=1$ and $C\le a/2$;
complete rejection has $q=C=0$.

**Lemma 2.2 (One edge and complementary triples).** In a specified
phase an active address $2\ell+\phi$ reads the spin-line edge
$\{\ell,\ell+1\}$; an opposite-parity address is a separator.
Conditional on that phase, one active edge has the following masses:

| Target position | Zero reply: two target-spin masses | One reply: two target-spin masses |
| --- | --- | --- |
| In the edge | $a^2,b^2$ | $\eta,\eta$ |
| Outside the edge | $ac,bc$ | $2a\eta,2b\eta$ |

The edge-zero probability is $c$ and edge-one probability is
$2\eta$. For two adjacent distinct active edges, zero-zero has
conditional mass $a^3+b^3=1-3\eta$. Each of the other three label
pairs has mass $\eta$, with complementary triple products
$a\eta,b\eta$. On such a nonzero pair the maximal full-law
endpoint-state mass, for every target position, is $a\eta/2$.

Proof. Equal spins have products $a^2,b^2$; unequal spins have
products $ab,ab$. If the target is outside the edge, independence
multiplies its prior into the constraint probability. This proves
the one-edge table.

Write adjacent spins in their line order as $(s_0,s_1,s_2)$.
The two XOR labels leave exactly a triple and its complement. For
label pairs $01,10,11$, respectively, their larger-product triples
are

$$
(\sigma,\sigma,1-\sigma),\qquad
(1-\sigma,\sigma,\sigma),\qquad
(\sigma,1-\sigma,\sigma).
\tag{2.3}
$$

Their products are $a^2b=a\eta$; the complements have product
$ab^2=b\eta$. Their sum is $\eta$. If the target lies in the
triple, the two completions have opposite target spins, so the larger
state mass, including phase prior, is $a\eta/2$. If the target
is outside, its independent majority factor $a$ gives the same
mass. Reversing the acquisition order only permutes the labels and
does not change these conclusions. For $00$ all three spins agree,
giving $a^3+b^3=(a+b)^3-3ab(a+b)=1-3\eta$.
$\square$

**Lemma 2.3 (Exhaustive geometry).** Two same-parity calls repeat an
active edge, use adjacent distinct active edges, or use edges with
disjoint vertex sets. In the last case the target lies in the first
edge, in the second, or in neither. With opposite address parities,
exactly one call is active in each phase, and the other is a
separator. These alternatives exhaust all integer addresses.

Proof. Edges of the integer spin line are precisely the pairs
$\{\ell,\ell+1\}$. Distinct pairs either share their single
intermediate endpoint or have no common vertex. For opposite
parities, activity is determined by the phase in (1.1). Negative
indices, arbitrary distances and acquisition order introduce no
further incidence. Constraints on disjoint spin sets multiply within
each phase of this one realization; the two phase alternatives are
then added as disjoint events. $\square$

## 3. All-real supporting objectives

**Definition 3.1 (Finite support formula).** For $\lambda\in\mathbb R$
put

$$
z=1-\eta=\frac{1+c}{2},\qquad
u=1-\frac{3\eta}{2},\qquad v=\frac{1+c^2}{2},
\tag{3.1}
$$

and define the following functions, all evaluated at $\lambda$:

$$
\begin{aligned}
T&=\eta(a-\lambda)_+,\\
H&=\eta(a^2-\lambda c)_+
       +2\eta^2(1/2-\lambda)_+,\\
U_I&=T,\qquad U_D=\max(T,H),\\
Z_R&=(a/2-\lambda z)_+,\\
Z_A&=(a/2-\lambda u)_++\frac\eta2(a-\lambda)_+,\\
Z_I&=(a/2-\lambda v)_++\eta(a^2-\lambda c)_+,\\
Z_D&=(a/2-\lambda v)_++\eta c(a-\lambda)_+,\\
O_I&=(a^2/2-\lambda c)_++\eta(a-\lambda)_+,\\
O_{DD}&=(ac/2-\lambda c)_++\eta(a-\lambda)_+,\\
O_{DI}&=(a^2/2-\lambda c)_++\eta(1/2-\lambda)_+,\\
V_I&=\max(Z_R,Z_A,Z_I,O_I),\\
V_D&=\max(Z_R,Z_A,Z_D,O_{DD},O_{DI}),\\
B(\lambda)&=\max\{0,a/2-\lambda,U_I+V_I,U_D+V_D\}.
\end{aligned}
\tag{3.2}
$$

The subscripts $I,D$ indicate whether the root's active edge is
incident to, or disjoint from, its phase's actual target vertex.
The letter $H$ here denotes a scalar function, distinct from the
hidden coordinates $H_j$.

**Theorem 3.2 (Exact support under every auxiliary law).** Every
protocol of Definition 1.2 satisfies, for every real $\lambda$,

$$
C-\lambda q\le B(\lambda),\qquad
L\ge(1-\lambda)q-B(\lambda).
\tag{3.3}
$$

For every $\lambda$ and either original endpoint there is a
deterministic admissible policy attaining $B(\lambda)$ under every
specified unchanged auxiliary law. Its returning paths use at most
two actual paid calls. Its calls, rejection and outputs use only
acquired replies and the public $p,j$.

The proof is divided into Lemmas 3.3–3.6 below. In particular the two
subtree maxima in (3.2) are simultaneously attainable by one policy.

**Lemma 3.3 (First-one subtrees).** Let $\alpha$ be the parity of the
root address $t$, and let $e$ be its active edge in phase $\alpha$.
The optimal supporting contribution on the first-one branch is
$U_I$ for a type-$I$ root and $U_D$ for a type-$D$ root.

Proof. A first one certifies phase $\alpha$ and has full-law mass
$\eta$. For a type-$I$ root the target is in $e$, and its spin is
fair on this branch. A repeat or separator adds no information. A
vertex-disjoint second active edge is independent of that target
and its first constraint. Its leaves still have confidence $1/2$,
so selecting their positive contributions gives
$\eta(1/2-\lambda)_+$. A distinct adjacent edge instead gives two
leaves, each with

$$
(W,M)=(\eta/2,a\eta/2),
\tag{3.4}
$$

by Lemma 2.2, for either possible endpoint of $e$. Their total
support is $T$. Since $a>1/2$,
$(1/2-\lambda)_+\le(a-\lambda)_+$ for every real $\lambda$;
hence adjacency dominates all the other choices and $U_I=T$.

For a type-$D$ root a repeat or separator leaves the untouched target
at its prior, giving $T$. An adjacent edge again has the two pairs
(3.4). Indeed the target is outside the triple or is the newly
added vertex, and the corresponding independent-prior or triple
calculation applies. A disjoint active edge avoiding the target
also leaves confidence $a$ on both leaves, with total $T$.

The remaining possibility is a second active edge $f$ disjoint from
$e$ and touching the target. The first constraint uses spins
disjoint from $f$. Multiplying its probability $2\eta$ by the
one-edge table and phase factor $1/2$ gives

$$
\begin{array}{c|cc}
\text{second reply}&W&M\\ \hline
0&\eta c&a^2\eta\\
1&2\eta^2&\eta^2
\end{array}
\tag{3.5}
$$

Its support is precisely $H$. At least one of the target's two
incident edges is vertex-disjoint from an edge avoiding the target:
such an edge can meet at most one of those two incident edges.
Thus (3.5) is available. The preceding alternatives exhaust the
second address by Lemma 2.3, proving $U_D=\max(T,H)$.
$\square$

**Lemma 3.4 (First zero, same-parity second call).** The retained
first-zero supports are $Z_R,Z_A,Z_I$ for a type-$I$ root and
$Z_R,Z_A,Z_D$ for a type-$D$ root. Every other same-parity
configuration is impossible or dominated for all real $\lambda$.

Proof. Write $f$ for the second edge in phase $\alpha$, and
$\beta=1-\alpha$. In phase $\beta$ both calls are separators,
so all that phase lies on $00$. In particular $h_\beta(\sigma)$
has joint mass $a/2$ there. No individual endpoint state has prior
larger than $a/2$. Consequently $M_{00}=a/2$ exactly in every
same-parity configuration.

If $f=e$, the zero constraint in phase $\alpha$ has probability
$c$, so $W_{00}=(1+c)/2=z$ and $01$ is impossible. This gives
$Z_R$; the repeated call is still charged.

If $e,f$ are adjacent, their zero-zero probability is $1-3\eta$,
so $W_{00}=[1+(1-3\eta)]/2=u$. The other leaf has
$(W_{01},M_{01})=(\eta/2,a\eta/2)$ by Lemma 2.2, irrespective
of the target position or orientation. This gives $Z_A$.

For vertex-disjoint edges, $W_{00}=(1+c^2)/2=v$ and
$W_{01}=\tfrac12 c(2\eta)=\eta c$. On $01$ the target incidences
give the following exact maxima:

$$
\begin{array}{c|c}
\text{target position}&M_{01}\\ \hline
\text{in }e&a^2\eta\\
\text{in }f&\eta c/2\\
\text{in neither}&a\eta c
\end{array}
\tag{3.6}
$$

The first row multiplies a touching zero-edge majority mass $a^2$
by the disjoint one probability and phase prior. The second uses
the fair target on a one edge, and the third uses the independent
majority target factor. For type $I$ only the first row is possible,
giving $Z_I$. For type $D$ the second or third row is possible.
Choosing $f$ away from both $e$ and the target realizes the third.
It dominates the second because $a>1/2$, while all leaf masses
$W$ and the $00$ maximum remain unchanged. This is pointwise
domination of $M-\lambda W$ for every real $\lambda$, including
after taking positive parts. Thus $Z_D$ suffices for type $D$.
$\square$

**Lemma 3.5 (First zero, opposite-parity second call).** The retained
supports are $O_I$ for a type-$I$ root and $O_{DD},O_{DI}$ for a
type-$D$ root. Together with Lemma 3.4 they give $V_I,V_D$ in
(3.2).

Proof. In phase $\alpha$ the root is active and the second call is
a separator; in phase $\beta$ the root is a separator and the
second call reads an active edge $f$. Thus $00$ has one
zero-edge constraint in each phase, with total mass $W_{00}=c$.
The leaf $01$ certifies $\beta$ and has mass $W_{01}=\eta$.

In a phase whose zero edge touches its actual target, the largest
state mass on $00$ is $a^2/2$; in a phase whose edge avoids its
target it is $ac/2$. The phase pairs are disjoint state sets, so
the full-law maximum is the larger of the two phase maxima, not
their sum. The comparison is strict because

$$
a-c=b\delta>0.
\tag{3.7}
$$

On $01$ the state maximum is $a\eta$ if $f$ avoids the
phase-$\beta$ target, and $\eta/2$ if it touches that target.
For root type $I$, choosing an avoiding $f$ maximizes this leaf
without changing $M_{00}=a^2/2$; a touching choice is dominated
at the same leaf masses for all $\lambda$. This yields $O_I$.

For type $D$ an avoiding $f$ gives
$(M_{00},M_{01})=(ac/2,a\eta)$, yielding $O_{DD}$. A touching
$f$ gives $(a^2/2,\eta/2)$, yielding $O_{DI}$. Both choices
are retained: improving the zero leaf can worsen the one leaf.
This proves precisely the claimed first-zero maxima. $\square$

**Lemma 3.6 (Paid joint representatives and integration).** All retained
subtree choices can be made jointly, and they prove Theorem 3.2.

Proof. For a type-$I$ root the two reply branches have total support
at most $U_I+V_I$ by Lemmas 3.3–3.5. For type $D$ the bound is
$U_D+V_D$. The second address on first zero and the second address
on first one are separate choices in an adaptive policy. They need
not coincide. The zero-read return and initial rejection give the
other two entries of $B$.

Here are explicit representatives, all with even root address. The
target in phase zero is $S_j$; the target in phase one is $S_0$,
for both endpoint choices.

| Root type | Root address | First-one second-address choices | First-zero second-address choices |
| --- | --- | --- | --- |
| $I$ | $2j$ | $2(j+1)$ for $T$ | $2j$, $2(j+1)$, $2(j+2)$, $2(j+8)+1$ for $Z_R,Z_A,Z_I,O_I$ |
| $D$ | $2(j+4)$ | root repeat for $T$, or $2j$ for $H$ | root repeat, $2(j+5)$, $2(j+8)$, $2(j+8)+1$, $1$ for $Z_R,Z_A,Z_D,O_{DD},O_{DI}$ |

The adjacent choices share one spin vertex; the stated distant
even choices have disjoint spin supports. Odd address $1$ touches
the phase-one target $S_0$, whereas $2(j+8)+1$ avoids it.
Thus every retained table entry is realized at the same root as
all the other entries of its type.

For completeness, maximizing outputs for these concrete choices
can be fixed entirely in advance as follows. At an $I$ root the
adjacent first-one leaves $10,11$ output $h_0(1-\sigma)$ and
$h_0(\sigma)$ respectively. On a same-parity first-zero branch,
output $h_1(\sigma)$ on $00$ and $h_0(\sigma)$ on any possible
$01$. On its opposite-parity first-zero branch, output
$h_0(\sigma)$ on $00$ and $h_1(\sigma)$ on $01$.

At a $D$ root, use $h_0(\sigma)$ on every possible first-one
leaf for either retained second-address choice; a fair leaf has
a tie and this fixes one maximizer. On a same-parity first-zero
branch use $h_1(\sigma)$ on $00$ and $h_0(\sigma)$ on $01$.
For $O_{DD}$ use $h_0(\sigma)$ on $00$ and $h_1(\sigma)$ on
$01$; the $00$ phase maxima tie. For $O_{DI}$ use
$h_1(\sigma)$ on both leaves. Impossible leaves can have any
fixed output. Lemma 2.2 and tables (3.5)–(3.6) verify every such
maximizer.

For the chosen $\lambda$, choose a maximizing entry on each
branch, make both actual calls on every path, and accept a leaf
exactly when $M-\lambda W>0$, allowing either decision at a
zero. On rejection continue internally forever with no more calls.
This is a measurable finite rule; even a repeated or rejected call
is paid. Choose the best whole tree, immediate majority-state
return, or initial internal nonreturn according to (3.2). The
result ignores the seed and attains $B(\lambda)$ under every
unchanged $\nu$. No phase or spin was observed beyond the actual
replies.

Conversely apply the fixed-seed bound to an arbitrary original
protocol. There are countably many finite integer-address/reply
records. Consistency and finite return on each record are
measurable seed conditions, and its output takes only four values.
Its source-section mass and correct mass therefore give measurable
functions $q(u),C(u)$. Finite section sums, or their countable
nonnegative sums before the two-call reduction, give

$$
q=\int q(u)\,d\nu(u),\qquad
C=\int C(u)\,d\nu(u).
\tag{3.8}
$$

Integrating $C(u)-\lambda q(u)\le B(\lambda)$ proves (3.3).
For completed product versions use measurable representatives;
their differences lie in a product-null set, whose sections are
source-null for almost every seed. They change no integral.
No conditioning on a singleton seed, regular conditional law on
an arbitrary auxiliary space, or added randomness is required.
$\square$

## 4. The attained all-auxiliary-law envelope

**Definition 4.1 (Explicit finite canonical family).** For each of the
four first-zero choices at the type-$I$ root in Lemma 3.6, pair it
with that root's adjacent first-one choice. For the type-$D$ root,
pair each of its two first-one choices with each of its five
first-zero choices. These are fourteen concrete address trees.
On each tree include every subset of its four binary reply leaves
as the acceptance set, with the fixed maximizing outputs specified
in Lemma 3.6. Make two actual calls on all paths, return on the
chosen leaves, and continue internally forever on the other leaves.
Also include immediate return of $h_0(\sigma)$ and immediate
internal nonreturn. Denote this finite policy family by
$\mathcal K$. Duplicated or impossible leaf choices cause no
difficulty; this description uses at most $14\cdot16+2$ policies.

For $k\in\mathcal K$ let $(q_k,C_k)$ be its actual same-source
pair. This is a finite construction from the displayed addresses,
outputs and leaf subsets, independent of $\lambda$ and of the
auxiliary law. In particular it is not an optimization over an
unspecified class of all protocols.

**Theorem 4.2 (Universal risk curve).** Let $L_{\mathrm{univ}}(q)$
be the infimum risk at mass $q$ over protocols and all allowed
independent auxiliary probability spaces. For every $0\le q\le1$,

$$
L_{\mathrm{univ}}(q)
=\sup_{\lambda\in\mathbb R}
   \bigl[(1-\lambda)q-B(\lambda)\bigr].
\tag{4.1}
$$

This is a finite piecewise affine curve and its infimum is attained
at every $q$. One may choose a uniform independent seed law at the
outset and, for each $q$, select between at most two policies of
$\mathcal K$ by a measurable interval of that seed. The inequality
in (4.1) applies to every specified unchanged auxiliary law; the
attainment statement does not append randomness to such a law.

Proof. Theorem 3.2 and the explicit independent branch choices give

$$
\max_{k\in\mathcal K}(C_k-\lambda q_k)=B(\lambda)
\quad(\lambda\in\mathbb R).
\tag{4.2}
$$

Indeed choosing an accepting subset realizes independently each
positive part, and the fourteen trees realize all choices of the
retained subtree maxima. Immediate return and rejection supply
the remaining entries. Thus (4.2) is a support formula for the
finite polygon

$$
P=\operatorname{conv}\{(q_k,C_k):k\in\mathcal K\},\qquad
g(q)=\max\{C:(q,C)\in P\}.
\tag{4.3}
$$

The convex hull is compact: it is the continuous image of the
finite-dimensional compact simplex of convex weights. It has
points at masses zero and one, so its vertical section is
nonempty and compact at every $q\in[0,1]$. Hence $g$ is defined
there. All its points obey $0\le C\le q$.

We give the support argument including the endpoints. Every extreme
point of this finite convex hull is one of its defining points:
otherwise a convex representation with at least two distinct
positive-weight points expresses it nontrivially as a convex
combination of one point and the combination of the others.

To see directly why the upper graph has finitely many affine
pieces, maximize height among convex weights with a fixed
horizontal coordinate, and choose a maximizer with the fewest
positive weights. If it has at least three, there is a nonzero
perturbation of those weights preserving both their sum and
their weighted horizontal coordinate: these are only two
homogeneous linear equations in at least three unknowns.
Both signs of a sufficiently small perturbation preserve
nonnegativity. A nonzero change in height would contradict
maximality by choosing its increasing sign. A zero change
allows the perturbation to be extended until one weight
vanishes, contradicting the minimal support. Thus at most
two weights are needed at each upper point. There are
finitely many pairs, each providing an affine segment on
its horizontal interval, so their upper envelope has finitely
many affine pieces. At either endpoint the best point there
can be joined to a point at the opposite endpoint; this
also ensures that the graph meets its endpoint value
continuously. Its maximal affine pieces join upper vertices,
which are extreme points of $P$ unless they are redundant
collinear points, so their endpoints are defining points.

Convexity of $P$ implies concavity of $g$: the convex combination of two
upper points lies in $P$, so its height is at most $g$ at its
combined coordinate. In particular successive upper-segment
slopes are nonincreasing.

At a point in an upper segment choose its slope $\lambda$.
At an interior upper vertex choose any slope between the
outgoing and incoming upper slopes. Monotonicity of slopes,
summing the horizontal increments to either side, proves
that the resulting line through the point lies above the
entire upper graph, and hence above $P$. At $q=0$ choose a
finite slope at least the first upper-segment slope; at $q=1$
choose one at most the last upper-segment slope. The same
argument proves support there. If the upper graph is a single
segment, use that segment's slope throughout. No vertical
support or infinite slope is necessary.

A linear functional has maximum on $P$ equal to its maximum
on the finite defining points, since its value at any convex
combination is the corresponding combination of values.
Consequently the line just constructed has intercept
$B(\lambda)$ by (4.2), and

$$
g(q)=\inf_{\lambda\in\mathbb R}
     \bigl[\lambda q+B(\lambda)\bigr]
\quad(0\le q\le1).
\tag{4.4}
$$

The reverse inequality for every slope also follows directly
from (4.2). In particular (4.4) includes both endpoints as
an attained finite-slope support identity.

Theorem 3.2 bounds every original protocol's correct mass by
the right side of (4.4), so $C\le g(q)$ under every seed law.
Conversely an upper-boundary point is an upper vertex or lies
between the endpoints of one upper segment. Those vertices
are pairs from $\mathcal K$. Write such a point as

$$
(q,g(q))=(1-\theta)(q_k,C_k)+\theta(q_\ell,C_\ell),
\qquad 0\le\theta\le1.
\tag{4.5}
$$

Choose the allowed auxiliary space to be $[0,1]$ with uniform
law, independently of $J_p$, before specifying the protocol.
Run policy $\ell$ on the event $u<\theta$ and policy $k$
otherwise. Each complete policy uses the same original $J_p$
and same fixed endpoint. Independence integrates their actual
joint masses to exactly (4.5). No branch borrows a phase or
spin from a different realization, and every selected call
remains paid. If the two policies agree or $\theta$ is an
endpoint, no random choice is needed.

Therefore the universal maximal correct mass equals $g(q)$
and is attained. Subtracting it from $q$ proves (4.1).
The finite upper polygon makes the risk finite and piecewise
affine. A specified seed law supplies (4.5) only if its
needed selection is available, or some other policy realizes
the same pair; (4.4) alone does not establish that availability.
$\square$

## 5. A selective support and four paid equality policies

**Lemma 5.1 (The only leaf with confidence above $a$).** In a two-call
tree every positive leaf has maximal confidence $M/W\le a$ except
possibly a leaf consisting, in one certified phase, of a zero edge
touching the target and a vertex-disjoint one edge. Such a leaf has

$$
W=\eta c,\qquad M=a^2\eta,\qquad
M-aW=\delta\eta^2=:D>0.
\tag{5.1}
$$

There is at most one such exceptional leaf in a tree. Every $00$
leaf and every zero-read return has confidence strictly below $a$.

Proof. The tables in Lemmas 3.3–3.5 exhaust the geometries before
dominated cases are omitted. For same-parity $00$ leaves,
$M=a/2$ and $W=z,u,v>1/2$, so $M/W<a$. For opposite-parity
$00$, $M\le a^2/2$ and $W=c$, and
$a^2/(2c)<a$ because $2c>1>a$. The zero-read maximum is $a/2<a$.

The one-containing leaves have confidence $1/2$ or $a$ except
the pair $(\eta c,a^2\eta)$ in (3.5) or the first row of (3.6).
These two descriptions are exactly the stated zero-edge/one-edge
event in its two acquisition orders. Its excess is

$$
\eta(a^2-ac)=a\eta(a-c)
=ab\eta\delta=\delta\eta^2>0,
\tag{5.2}
$$

using (3.7). At a type-$I$ root it can occur only on first zero,
then a disjoint one edge. At a type-$D$ root it can occur only
on first one, then a disjoint touching zero edge. The other
first-reply branch cannot have an exception of its own for
that root type. Opposite parity cannot supply two active edges
in a single phase. Thus there is at most one. $\square$

**Theorem 5.2 (Selective support).** Every protocol satisfies

$$
B(a)=D=\delta\eta^2,\qquad
C\le aq+D,\qquad L\ge bq-D.
\tag{5.3}
$$

Proof. By Lemma 5.1 all accepted nonexceptional leaves have
nonpositive contribution to $C-aq$, while the sole possible
exception contributes at most $D$. The zero-read and initial
rejection cases also obey the bound. Integration proves it
for the full class. Equivalently (3.2) gives
$U_I(a)=0$, $V_I(a)=D$, $U_D(a)=D$, $V_D(a)=0$.
The paid policies below attain $D$, proving the claimed
support value. $\square$

**Definition 5.3 (Four deterministic equality rules).** Put

$$
q_H=\eta c,\qquad Q=\eta(1+c).
\tag{5.4}
$$

Each rule below ignores the auxiliary variable, makes two actual
calls on every path, and returns only on its explicitly accepted
leaves. On every other leaf it continues internally forever
without another call. Delays may be chosen zero.

The rule $K_0$ first reads $2(j+4)$. After a first one it reads
$2j$ and accepts just a second zero, outputting $h_0(\sigma)$.
After a first zero it makes a paid repeat and rejects.

The rule $K_h$ first reads $2j$. After a first zero it reads
$2(j+2)$, accepts just a second one, and outputs $h_0(\sigma)$.
After a first one it reads $2(j+1)$, accepts just a second one,
and outputs $h_0(\sigma)$.

The rule $K_c$ first reads $2(j+4)$. Its first-one branch is
that of $K_0$. After a first zero it reads $2(j+8)$, accepts
just a second one, and outputs $h_0(\sigma)$.

The rule $K_1$ first reads $2(j+4)$. Its first-one branch is
again that of $K_0$. After a first zero it reads $2(j+8)+1$,
accepts just a second one, and outputs $h_1(\sigma)$.

All unlisted outputs on rejected or impossible leaves can be
assigned a fixed state, giving total measurable rules. A phase
label in these descriptions specifies an output state via (1.2);
it is not a preliminary phase observation.

**Proposition 5.4 (Exact masses and the universal face).** The four
rules have the following joint masses:

| Rule | $q$ | $C$ |
| --- | --- | --- |
| $K_0$ | $q_H$ | $a^2\eta$ |
| $K_h$ | $q_H+\eta/2$ | $a^2\eta+a\eta/2$ |
| $K_c$ | $2\eta c$ | $a^2\eta+a\eta c$ |
| $K_1$ | $Q$ | $a^2\eta+a\eta$ |

Each obeys $C=aq+D$. Moreover

$$
0<q_H<q_H+\eta/2<2\eta c<Q<1,
\tag{5.5}
$$

and

$$
L_{\mathrm{univ}}(q)=bq-D
\quad\text{for }q_H\le q\le Q.
\tag{5.6}
$$

Proof. For $K_0$ the accepted event certifies phase zero and
requires a distant one edge and the target's zero edge. In
phase zero these constraints use disjoint spin pairs, so its
return mass is $\tfrac12(2\eta)c=\eta c$ and its correct
mass is $\tfrac12(2\eta)a^2=a^2\eta$. Its risk is
$\eta b^2$. This is the inherited $n=2$ selective anchor of
Original, Theorem 10.1 and (10.4), also restated in Risk, §2;
reading its disjoint constraints in the reverse order leaves
the same products. The anchor is not a new result here.

The first-zero accepted event of $K_h$ is the same exceptional
geometry, with the same masses. Its additional accepted $11$
leaf uses $Y_j=Y_{j+1}=1$. The larger triple is
$(S_j,S_{j+1},S_{j+2})=(\sigma,1-\sigma,\sigma)$, of mass
$a^2b=a\eta$ before the phase factor. Including its complement,
that leaf has $W=\eta/2$ and the specified correct mass
$M=a\eta/2$. Thus the displayed $K_h$ pair follows.

For $K_c$ its additional accepted $01$ leaf has two disjoint
edges avoiding the target, with first constraint zero and
second one. Its return mass is $\tfrac12 c(2\eta)=\eta c$.
The untouched target's majority factor gives correct mass
$a\eta c$. These are within the same phase-zero realization;
the disjoint constraints were not discarded.

For $K_1$ the additional $01$ leaf certifies phase one.
The first even address is then a separator. The second odd
address reads $Y_{j+8}$, whose spin pair avoids the actual
phase-one target $S_0$. Consequently this leaf has mass
$\eta$ and correct mass $a\eta$ for output $h_1(\sigma)$.
Its first-one accepted event remains the phase-zero exception.
The two events are disjoint events of the one source, so
their displayed masses add.

Equation (5.1) gives $a^2\eta=aq_H+D$; each added pair has
correct-mass slope $a$. This proves equality for all four
rules. Their strict ordering follows from $1/2<c<1$.
Also $Q=\eta(1+c)<(1/4)2<1$.

For any $q\in[q_H,Q]$, an already available independent
seed event of measure

$$
\theta=\frac{q-q_H}{\eta}
\tag{5.7}
$$

can select $K_1$ on that event and $K_0$ otherwise. Here
$Q-q_H=\eta$, so $0\le\theta\le1$. Integrating the same-source
pairs gives $q$ and $C=aq+D$. A uniform auxiliary space chosen
at the outset supplies all such events. Together with Theorem
5.2 this proves (5.6). The four deterministic points themselves
need no seed event. $\square$

## 6. Exact equality availability under a specified seed law

**Theorem 6.1 (Four-part partition criterion).** Fix any specified
unchanged independent auxiliary space $(\mathsf U,\mathcal U,\nu)$.
For a given $q\in[0,1]$, an admissible protocol with this mass
attains $L=bq-D$ if and only if there is a measurable partition
$(G_0,G_h,G_c,G_1)$ of $\mathsf U$, up to null sets, such that

$$
q=q_H+\frac\eta2\nu(G_h)+\eta c\nu(G_c)+\eta\nu(G_1).
\tag{6.1}
$$

Empty parts are allowed. In particular equality forces
$q_H\le q\le Q$. This interval is exactly the universal
exposed face for slope $a$. With a constant seed the equality
masses are exactly the four in Proposition 5.4.

Proof of necessity. Let $q(u),C(u)$ be the measurable source-section
masses of the original protocol. Theorem 5.2 applies at every
eligible fixed seed, so its nonnegative deficit satisfies

$$
D-[C(u)-a q(u)]\ge0,\qquad
\int\bigl(D-[C(u)-a q(u)]\bigr)\,d\nu(u)=0.
\tag{6.2}
$$

A nonnegative measurable function of zero integral is zero
almost everywhere: for each positive integer $m$ the set where
it is at least $1/m$ must have measure zero, and the positive
set is their countable union. Thus almost every seed itself
attains $C(u)-a q(u)=D$.

At such a seed Lemma 5.1 forces the unique exceptional leaf
to exist, to be accepted, and to have its maximizing output.
Without it the objective is at most zero; losing any part of
its excess cannot be compensated by another leaf. Every other
accepted positive leaf must have confidence exactly $a$ and
use a maximizing output, because a smaller confidence or output
would cause a strict deficit. The exception itself has a
strictly larger majority-spin mass, since $a^2>b^2$.

We check early returns in the original rule as well as its
two-call representation. A zero-call return has confidence
$a/2<a$. A first-zero return has mass $z>1/2$ and maximum state
mass $a/2$, so its confidence is below $a$. A first-one return
at a type-$I$ root has confidence $1/2<a$. At a type-$D$ root
it has confidence $a$, but it consumes the first-one branch
on which the required exceptional descendant must occur.
None can occur at an equality seed. Thus paid padding has
not supplied an unobserved selection within an early-return
section. Rejecting short branches still supplies no positive
contribution.

For a type-$I$ root the exception uses the first-zero branch
with a disjoint second one. The other leaf there is $00$,
of confidence strictly below $a$. On the first-one branch
a repeat, separator or disjoint edge leaves the target fair;
only an adjacent active edge gives confidence-$a$ leaves.
Its two leaves each have mass $\eta/2$. The accepted addition
is therefore $0$, $\eta/2$ or $\eta$.

For a type-$D$ root the exception uses first one and a disjoint
target-touching second zero. Its other leaf has confidence
$1/2<a$. On the first-zero branch all $00$ leaves have strict
confidence below $a$. A repeat gives no other positive leaf.
Adjacency supplies one confidence-$a$ leaf of mass $\eta/2$.
A disjoint same-parity edge avoiding the target supplies one
of mass $\eta c$; if it touches the target instead, its
one-containing leaf has confidence $1/2<a$. An opposite-parity
edge avoiding that phase's target supplies one of mass $\eta$;
if it touches the target, that leaf again has confidence
$1/2<a$. Lemma 2.3 exhausts all alternatives.

It follows that almost everywhere

$$
q(u)=q_H+d(u),\qquad
d(u)\in\{0,\eta/2,\eta c,\eta\}.
\tag{6.3}
$$

The four numbers are distinct by $1/2<c<1$. Since $q(u)$ is
measurable by (3.8), its four level sets in (6.3) define
measurable $G_0,G_h,G_c,G_1$ on the full-measure equality set.
Assign its null complement to $G_0$, using completed versions
or measurable representatives as appropriate. Their measures
are unaffected. Integrating (6.3) proves (6.1). This proof
uses source sections and integration, without disintegration
of an arbitrary auxiliary space.

Proof of sufficiency. Given the partition, run $K_0,K_h,K_c,K_1$
on its corresponding parts. Selection depends only on the
original seed; it does not change its law or observe the
source. The rules of Definition 5.3 are measurable and make
their actual two paid calls. Their masses in Proposition 5.4
integrate to (6.1), and their common excess is $C-aq=D$.
Thus $L=bq-D$, proving sufficiency.

The partition formula is a convex combination of the four
deterministic masses, whose smallest and largest values are
$q_H,Q$. With a uniform law all intermediate masses are
available by (5.7), so the face has exactly this extent.
For a constant seed each measurable part has probability
zero or one, and one part has probability one; hence exactly
the four listed masses occur. At $q=q_H$ the partition has
only $G_0$ of positive measure; at $q=Q$ only $G_1$ can have
positive measure, by the strict ordering (5.5). $\square$

The event condition (5.7) is a sufficient special case of
Theorem 6.1, obtained by taking $G_h=G_c=\varnothing$.
Necessity requires the whole partition condition, rather
than that particular gate. All strict classifications above
use $0<\eta$, $\delta>0$ and $1/2<c<1$. The fair and endpoint
parameters are excluded; their extra ties or zero masses
cannot be treated by this necessity argument.

**Proposition 6.2 (A nonvacuous constant-seed obstruction).** With
a constant auxiliary variable, mass $q=\eta$ is attainable
within two reads, but no protocol attains the universal face
value $b\eta-D$ there. The exact optimal excess over this
value is not determined by this nonattainment statement.

Proof. Make one actual read at $2(j+2)$ and return
$h_0(\sigma)$ only on reply one, otherwise continue internally
forever. In phase zero its active spin pair
$\{j+2,j+3\}$ avoids target $j$; in phase one the reply is
zero. Thus its return mass is $\eta$ and its correct mass
$a\eta$, with risk $b\eta$. This is the inherited one-read
selective witness in Original, Theorem 10.1, and Risk,
Theorem 4.1. Its one call is paid on all paths and it belongs
to the present budget-two class.

Since $c<1$ and $c>1/2$,

$$
q_H=\eta c<\eta<\eta(c+1/2)=q_H+\eta/2.
\tag{6.4}
$$

So $\eta$ lies in the universal face but is none of its four
constant-seed equality masses. Theorem 6.1 excludes equality
under that specified law. Nonattainment alone does not rule
out a sequence approaching the universal value; no strictly
positive infimum gap is inferred here. $\square$

## 7. Endpoint consequences and attribution

**Corollary 7.1 (The inherited almost-sure slice as a support check).**
The support formula gives

$$
B(0)=\frac a2+a\eta+a^2\eta,\qquad
L_{\mathrm{univ}}(0)=0,\qquad
L_{\mathrm{univ}}(1)=1-\frac a2-a^2b(1+a).
\tag{7.1}
$$

The last value is the attained almost-sure-return two-read result
of [`FIB_TWO_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md`][Endpoint], *FIB two paid reads: exact almost-sure-return endpoint risk*,
Theorem 6.1 and its §§5–6 paid construction. It is not a new
independent endpoint result here and is not a premise for
Theorem 3.2.

Proof. At $\lambda=0$ the first-one functions satisfy
$T=H=a\eta$. On first zero the type-$I$ maximum is
$Z_I=a/2+a^2\eta$: its differences from $Z_R,Z_A,O_I$ are,
respectively,

$$
a^2\eta,\qquad a\eta(a-1/2),\qquad
\eta(1/2-\eta),
\tag{7.2}
$$

all strictly positive. For type $D$ the maximum is
$Z_D=a/2+a\eta c$; it exceeds $Z_A$ since $c>1/2$,
exceeds $Z_R$, and $O_{DD}=O_{DI}=a/2$. Finally
$Z_I-Z_D=a\eta(a-c)=D>0$. Thus (3.2) gives the displayed
$B(0)$, also exceeding the immediate-return value $a/2$.

The canonical type-$I$ tree with first-one adjacent second
address $2(j+1)$ and first-zero disjoint second address
$2(j+2)$, accepting all leaves, has mass one and correct
mass $B(0)$ by Lemma 3.6. It is exactly the paid tree in
the cited slice's Definition 5.1 and Proposition 5.2.
Thus the support upper bound at zero is attained at mass
one under every auxiliary law. Its risk is
$1-B(0)=1-a/2-a^2b(1+a)$ because $\eta=ab$.
At mass zero the joint risk is zero by definition, and
internal nonreturn attains it. $\square$

**Attribution 7.2 (Precise inherited and additional content).** The
source-specific attribution is as follows.

| Source | Inherited result and use |
| --- | --- |
| `FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md`, Proposition 2.1, (2.2), (9.4) | One stationary $J_p$, four distinct states, original separator clock and phase-specific target indices. |
| Original, Lemma 3.1, §8 and Theorem 9.2 | Complementary-spin products, complete-half-line endpoint description, finite source-section interface and positive-error boundary. Complete-half-line recovery supplies no free call. |
| Original, Theorem 10.1 and (10.4) | Sharp count-only selective coefficients and paid witnesses, including $(q,L)=(\eta c,\eta b^2)$ at two reads and $(\eta,b\eta)$ at one. |
| Original, Theorems 11.1–11.4 | Sharp all-zero record envelope and witnesses, integrated zero/one-record bound, forced zero-record mass under a budget and exact guaranteed-return one-read optimum. |
| `FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md`, §§1–3 | Same contract and finite-record estimates, and the general-budget return-mass correction without a general sharpness claim. |
| Risk, Theorem 4.1 | Complete universal one-read envelope, exact seed-event equality gate and the one-read almost-sure optimum, overlapping Original, Theorem 11.4. |
| Risk, Theorem 5.1 and §6 | Finite paid-probe/local-block family with exact risk and cost formulas, and the distinction between fixed-law and all-law frontiers. |
| [`FIB_TWO_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md`][Endpoint], *FIB two paid reads: exact almost-sure-return endpoint risk*, Definition 5.1, Proposition 5.2, Theorem 6.1 and §7 | The $q_2=1$ optimum and its same-source deterministic attainer; only its consequence and agreement with (3.2) are used here. |

Its endpoint theorem is credited
as ordinary mathematics and supplies no premise for the support
derivation in §3.

The additional content relative to these texts is the entire
all-real support family (3.2), including selective acceptance
on both compatible adaptive subtrees; its attained finite
all-auxiliary-law envelope; the explicit support face (5.6);
and its necessary-and-sufficient four-part fixed-law equality
criterion. The anchor $K_0$ is inherited. The additional
deterministic equality masses and their joint classification
do not follow merely by restating that anchor or the
almost-sure slice.

The probability products, maximum-state decision rule,
positive-part leaf selection and convex hull arguments have
their elementary mathematical meanings. These conclusions
are repo-derived relative to the supplied texts, with no
worldwide priority or exhaustive literature-absence claim.
They are ordinary proofs, with no formal-verification claim.

## 8. Unresolved frontiers and resource boundaries

**Definition 8.1 (Specified-law optimization).** For a fixed unchanged
auxiliary law $\nu$, define, at an attainable mass $q$,

$$
\mathcal L_{2,\nu}(q)
=\inf\{L:\text{a protocol of Definition 1.2 has mass }q\}.
\tag{8.1}
$$

Theorem 3.2 supplies its supporting inequalities; Theorem 6.1
settles exactly when equality with the explicit face is
attainable. The complete attainable mass set and the value
of (8.1) above the universal envelope on each specified
atomic space are not classified here. In particular the
exact excess in Proposition 6.2 remains unsettled by this
volume. Enlarging that space with a fresh uniform variable
would change this question.

Formula (3.2) and the explicit finite family determine the
all-law curve exactly, but a simplified list of its
bias-dependent breakpoints is not printed. The full
$k>2$ return-mass frontier, minimum expected paid cost and
optimal stopping questions remain outside these conclusions.
Expected cost counts all actual calls on returning and
nonreturning paths, including repeats and separators; it
cannot be replaced by a mean restricted to returns.

The original arbitrary-finite attainment and separation
question for the whole-domain harmonic/Brier objective,
Original, Open Problem 6.4, remains unresolved here. The
endpoint classification results do not supply a bridge to
that objective. Actual read count, internal computation,
address size, return time, persistent state and physical
storage are distinct resources. No bounds on the latter
resources, native machine-learning realization, neural
training, generalization or empirical learning conclusion
follow from the paid-read curve. The fair and endpoint
parameters are not covered. These results settle precisely
the stated two-read support and equality questions.

[Original]: FIB_LEGAL_EDGE_LOAD_FIXED_STATE_TAIL_NONUNIFORMITY_AND_ERASURE_RISK_JUMP.md
[Risk]: FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md
[Endpoint]: FIB_TWO_PAID_READ_ALMOST_SURE_ENDPOINT_RISK.md

## 追加锚（本行以下为增补区）
