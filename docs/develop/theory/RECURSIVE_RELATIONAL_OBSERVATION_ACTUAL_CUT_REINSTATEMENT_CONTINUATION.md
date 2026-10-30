# Recursive Relational Observation: Actual Cut Reinstatement Continuation

This continuation fixes the information earned by paid presence replies in the
actual autonomous birth source of [GPO][GPO] and the actual-cut service of
[ACR][ACR].  The source remains the single root with persistent physical ports
$a<b$, the alpha origin, chronological beta births, an unknown all-index law,
and a mature cut.  A reply is a paid current-source literal reply.  It is not
a supplied law bit, a clock, a private label, or an equivalence oracle.

The statements below concern exact finite certificates and their information
fibres.  They do not change the original $\rho_d$, $K_d$, output convention,
resource bills, or the unrestricted polynomial-TOTAL question.

## 33. Authenticated chronology after a root certificate

**Definition 33.1 (chronological indices and the normalized clock).**
Let $F_0=0$, $F_1=1$, $F_{i+2}=F_{i+1}+F_i$, and

$$
B_t=F_{t+1}-1,\qquad v_t=B_{t-1}=F_t-1\quad(t\ge2).
$$

The $j$th birth belongs to the unique update

$$
\tau(j)=\min\{t\ge2:j\le B_t\},\qquad
R(j)=j-B_{\tau(j)-1}.
$$

The normalized birth sample at update index $i\ge0$ is

$$
b_i=z_{B_{i+1}}.
$$

This convention begins at the slot $B_1$ and is not the assertion
$A_2=3$ for every source.  When the raw physical stream is one-based, its
first consumed bit remains $z_1$ at $B_2$; the $b$-index is a normalized address
and does not shift the raw update time.  Whenever a suffix is evaluated at a
proposed cut $\tau$, its normalized clock argument is $\tau-1$; this is
distinct from the raw update index $\tau$.

For $\nu\ge2$, a root rank certificate supplies $x,y$ with
$|x|=\nu-1$ and tests

$$
\begin{array}{c|c}
\nu=2k+1&\operatorname{Read}(ya)=0\\
\nu=2k&\operatorname{Read}(yaa)=\operatorname{Read}(yba)=0,
\end{array}
$$

in addition to $\operatorname{Read}(x)=1$.  All words are submitted to the
same physical root.  A proposed prefix $A=(a_1,\ldots,a_{2d})$ determines
$p_j(A)$ by the old tree at cut $\tau(j)-1$; the proposed orientation is
$c_j=a$ when $a_j=1$ and $c_j=b$ when $a_j=0$.  Put
$t_j=\nu-\tau(j)$ for a mature birth $1\le j\le v_n$; maturity gives
$t_j\ge1$.

**Theorem 33.2 (the cut alternatives and exact root conjunction).**
For every actual cut $n\ge2$ and every $\nu\ge2$:

1. $\operatorname{Read}(x)=1$ for a word of length $\nu-1$ implies
   $n\ge\nu$.  Its converse is false for an arbitrary $x$.
2. $\operatorname{Read}(x)=0$ has the necessary alternatives
   $n<\nu$, or $n\ge\nu$ and $x$ reaches a terminal node before its end.
   Thus a general negative reply is not a cut certificate.
3. The whole conjunction consisting of the positive $x$ test and the odd or
   even two-child absence tests passes if and only if $\nu=n$.

Proof. A present word of length $\nu-1$ requires a root rank at least $\nu$,
which proves the first assertion. If $x$ is absent, either the cut is too
young or a terminal node blocks the extension; both alternatives occur in the
Fibonacci rank trees. For the conjunction, a positive $x$ forces rank at
least $\nu$. At $\nu=2k+1$, rank at least $2k+2$ makes every length-$k+1$
suffix present, contradicting the odd test. At $\nu=2k$, rank at least
$2k+1$ leaves a length-$k-1$ prefix with a child of rank at least two, so
one of $yaa,yba$ is present. Hence a passing test has rank at most $\nu$.
At rank $\nu$, a longest path supplies $x$ and a shortest rank descent
supplies $y$ and the displayed absences. This includes $\nu=2$, where $y$
is empty. The root is the actual rank-$n$ cone, so the conjunction is
equivalent to $\nu=n$. No presentation minimality or invertibility is used.
$\square$

**Theorem 33.3 (maximal-witness conjunction and earned indexed samples).**
Assume the root conjunction has passed and the proposed bits before $j$ have
already passed their own positive witness tests. Then $p_j(A)$ is the actual
birth parent and

$$
\begin{aligned}
z_j=a_j
&\Longleftrightarrow
\exists v\in\{a,b\}^{t_j}
   \;\operatorname{Read}\bigl(p_j(A)c_jv\bigr)=1,\\
z_j\ne a_j
&\Longleftrightarrow
\forall v\in\{a,b\}^{t_j}
   \;\operatorname{Read}\bigl(p_j(A)c_jv\bigr)=0.
\end{aligned}
\tag{ACRC.1}
$$

Consequently a paid native support-refutation service may enumerate the
$2^{t_j}$ suffixes, return a present maximal witness, or return the complete
zero certificate $\bot$.  Its answer is nonempty exactly for the authentic
orientation.  A positive returned witness is an authenticated sample at the
actual index $j$; it is not merely a prediction from $A$.

Proof. The authenticated prefix reconstructs the actual old tree at
$\tau(j)-1$, by the chronological parent rule. At the actual cut, the child
selected by $z_j$ has rank $t_j+1$ and the opposite child has rank $t_j$.
The former has a suffix of length $t_j$, while the latter has maximum suffix
depth $t_j-1$. This proves both implications in (ACRC.1). The service is a
finite conjunction of actual literal replies, so its zero output is a paid
refutation of that proposed orientation. $\square$

For an arbitrary single birth reply, the exact weaker statement is

$$
\operatorname{Read}(p_jc_jv)=0
\Longrightarrow
\bigl(a_j\ne z_j\bigr)
\vee
\bigl(a_j=z_j\ \wedge\ v\text{ is not a present maximal witness}\bigr).
\tag{ACRC.2}
$$

The second disjunct is real: a correct child can have absent suffixes of the
tested length.  Therefore a negative reply to one unqualified literal neither
names an erroneous bit nor refutes the candidate source.  The complete
maximal-witness conjunction is the extra information that removes this
alternative.

After the root certificate, the first $m\le v_n$ earned bits therefore use at most

$$
3+\sum_{j=1}^{m}2^{t_j}
$$

paid Reads and at most

$$
O\!\left((n+1)+\sum_{j=1}^{m}t_j2^{t_j}\right)
$$

literal traffic, including the root certificate and the complete zero
certificates.  These are exact finite support-service bounds; they are not a
polynomial acquisition claim.  The data identify the authenticated prefix
and its chronological indices.  They do not identify a private recurrence,
its seed presentation, or any source bit outside the tested prefix.

## 34. Feedback algebra and the two-to-five all-index bridge

**Lemma 34.1 (all-index feedback composition, including singular laws).**
Let $p(E)s=0$ for every index $i\ge0$, and let a feedback service produce $y$
from the same initial origin by

$$
q(E)y=s,
$$

where $p,q$ are monic binary polynomials and either polynomial may have zero
intermediate or final taps.  Then

$$
(pq)(E)y=0\quad\text{for every }i\ge0,
$$

and the least order of $y$ is at most $\deg p+\deg q$ and may be smaller
after cancellation.

Proof. Both equations hold at every nonnegative index, so commuting forward
shifts gives $p(E)q(E)y=p(E)s=0$ at every such index. The argument never
divides by a constant tap, extends a recurrence backwards, or discards a
finite transient. $\square$

**Theorem 34.2 (an exact order-$2$ source feeding an exact order-$5$ law).**
Let

$$
p(E)=E^2+E+1,\qquad q(E)=E^3+E+1.
$$

Take the order-$2$ source $s_0=0,s_1=1$ and
$s_{i+2}=s_i+s_{i+1}$, and initialize $y_0=y_1=y_2=0$.  The paid feedback
equation is

$$
y_{i+3}=y_i+y_{i+1}+s_i\quad(i\ge0).
\tag{ACRC.3}
$$

Then $y$ satisfies the all-index order-$5$ recurrence

$$
y_{i+5}=y_{i+4}+y_i,
\tag{ACRC.4}
$$

and its least all-index order is exactly five.  Its initial segment is

$$
000011111010100110001\cdots.
$$

Proof. Multiplication over $\mathbb F_2$ gives

$$
(E^2+E+1)(E^3+E+1)=E^5+E^4+1,
$$

so (ACRC.4) follows from Lemma 34.1.  The first five consecutive Hankel
rows are

$$
\begin{pmatrix}
0&0&0&0&1\\
0&0&0&1&1\\
0&0&1&1&1\\
0&1&1&1&1\\
1&1&1&1&1
\end{pmatrix}.
$$

This is anti-triangular with diagonal one over $\mathbb F_2$, hence has rank
five.  No recurrence of order below five can generate the displayed
all-index stream.  The example consumes the feedback output in (ACRC.1):
the resulting stream is a legal source law for indexed witness extraction,
while the extraction still requires paid current-root support replies.
The proof remains valid for singular endpoint laws; for example
$p(E)=E^2$ and $q(E)=E^3+1$ give the same product argument for a finite
impulse source, without an inverse transition. $\square$

**Proposition 34.3 (extremal-spine formula and its precise domain).**
In the fixed global-port substitution supplier of GPO, let $d_L,d_R$ be the
original left and right extreme heights and let $\eta_L,\eta_R$ indicate
whether the corresponding terminal is beta.  For $x=\rho^{2k+1}u$,

$$
h_L(x)=d_L+2k+\eta_L,\qquad
h_R(x)=d_R+k+\eta_R.
\tag{ACRC.5}
$$

If the physical port $a$ is the global left port, $(h_a,h_b)=(h_L,h_R)$;
if it is the global right port, the pair is reversed.  The two formulas are
the exact extremal feedback values used to construct the corresponding
longest and shortest rank witnesses in a fixed-port root certificate.

They are not a law-independent identity for the autonomous orientation bits
$z_j$.  In that source, the paid chronology and (ACRC.1), rather than a
semantic extremal formula, authenticate each physical orientation.

Proof. The left extreme gains two levels per homogeneous $\rho$ pair and the
terminal beta gains one extra level; the right extreme gains one level per
pair and the same terminal correction. Induction on $k$ gives (ACRC.5).
The port exchange is a renaming. The distinction between the fixed-port
supplier and the autonomous-bit source follows because a changed early $z_j$
can move a physical $a$-spine while preserving every semantic rank. $\square$

## 35. A period-eleven extremal-observation fibre

**Definition 35.1 (two period-eleven source laws).**
Let $s^{A}$ and $s^{B}$ be the period-eleven words

$$
s^{A}[0{:}11]=10000000000,\qquad
s^{B}[0{:}11]=01000000000,\qquad z_j=s[j-1].
$$

Both satisfy the all-index law $s_{i+11}=s_i$ and have exact period eleven.
Start at the alpha root and run the actual chronological updates to cut
$n=4$, so $B_4=4$.  The two consumed birth prefixes are $1000$ and $0100$.

**Theorem 35.2 (same extremal observations, complete legal separator).**
For the two sources of Definition 35.1,

$$
(h_a,h_b)=(2,2)\quad\text{at cut }4
$$

for both sources, but their supports are respectively

$$
\begin{aligned}
S_A&=\{\varepsilon,a,aa,ab,b,ba,bb,aba,abb\},\\
S_B&=\{\varepsilon,a,aa,ab,b,ba,bb,baa,bab\}.
\end{aligned}
$$

The full legal distinguishing words are

$$
S_A\setminus S_B=\{aba,abb\},\qquad
S_B\setminus S_A=\{baa,bab\}.
\tag{ACRC.6}
$$

Proof. At cut two, the first bit $1$ places beta at $a$ and the first bit
$0$ places beta at $b$.  At cut three, the second bit splits that beta leaf;
at cut four, the two later bits split the lexicographically ordered beta
leaves.  Applying the four prefixes gives exactly the displayed sets.
Both sets contain $a^2$ and $b^2$ and neither contains a cube in one port,
so both extremal heights are two.  The four words in (ACRC.6) are precisely
the symmetric difference, hence every legal support separator is listed. $\square$

**Proposition 35.3 (two distinct same-transcript ambiguities).**
At cut four every birth prefix with the same first two bits has the same
complete support, although its third and fourth indexed bits can differ.
In particular, the period-eleven laws with prefixes $0100$ and $0101$ have
identical replies on every legal word at cut four; their unresolved bits are
$z_3$ and $z_4$.  This is tested-bit uncertainty, not a failure to choose a
convenient separator.

There is also a stronger inability-to-name-one-disagreement witness.  The
four period-eleven prefixes

$$
0000,\quad0100,\quad1000,\quad1100
$$

have identical replies on

$$
W_2=\{\varepsilon,a,aa,ab,b,ba,bb\}.
$$

Relative to the $0000$ source, the additional depth-three supports for the
other three candidates are respectively

$$
\{baa,bab\},\quad\{aba,abb\},\quad\{aaa,aab\},
$$

which are pairwise disjoint.  Thus a transcript restricted to $W_2$ does not
name any one word that must be a disagreement for the unknown alternative.
The conclusion is about this finite fibre and includes newest, not mature,
births; it does not claim that no later paid word can separate a chosen pair.

Proof. Chronological replacement shows that the support through depth two
uses only the first two births; the third and fourth births attach only
depth-three children.  Direct replacement gives the three displayed pairs.
Each nonzero listed cycle is exact period eleven; the $0000$ cycle is the
zero all-index law and is also eleven-periodic.  Thus all four are legal
all-index sources. $\square$

## 36. What the earned data do and do not recover

**Corollary 36.1 (native support-refutation is exact but paid).**
Under the authenticated-prefix hypotheses of Theorem 33.3, the complete
finite service over $\{a,b\}^{t_j}$ is a proper native support-refutation
service. It returns the authentic $z_j$ after at most $2^{t_j}$ literal
presence replies, and it returns no source law, no arbitrary-DFA equivalence
answer, and no chronological bit outside the authenticated index.

The period-eleven fibre proves that extremal heights alone cannot replace
those support replies. The same-transcript families prove separately that a
tested bit may remain unknown and that, with several surviving candidates,
no single unqueried word need be a certified disagreement. A source recovery
claim therefore requires the full source promise, the root certificate, the
authenticated-prefix induction, and the paid witness or zero certificate at
each requested index.

The suppliers have the following exact correspondence. GPO §§27--29 supply
the alpha origin, chronological beta order, $B_t$, all-index recurrence
class, and finite-separation convention. ACR §§22, 25 and 31--32 supply the
paid root certificate, authentic-prefix boundary, and typed local normalizer
whose original $\rho_d$ remains unchanged. Massey, [*Shift-Register Synthesis
and BCH Decoding*][MAS], supplies shortest finite-prefix register
synthesis; it supplies no physical chronology or paid support witness.
Rueppel, [*Linear Complexity and Random Sequences*][RUEPPEL], supplies the
classical count and recurrence correspondence for binary semi-infinite
linear-complexity streams; it supplies no native-root acquisition result.
These correspondences are restricted to the stated domains and make no
global novelty, original-$\rho_d$ hardness, polynomial automaton-size, or
full-goal claim.

[ACR]: RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT.md
[GPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md
[MAS]: https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI411.pdf
[RUEPPEL]: https://link.springer.com/content/pdf/10.1007/3-540-39805-8_21.pdf

## 追加锚（本行以下为增补区）
