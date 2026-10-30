# Recursive Relational Observation: Actual Cut Reinstatement Continuation

This continuation concerns information earned by paid presence replies in the
actual autonomous birth source of [GPO][GPO] and the actual-cut service of
[ACR][ACR]. The source has one root, persistent physical ports $a<b$, the
alpha origin, chronological beta births and an unknown all-index law. Unless
an earlier cut is explicitly specified, retain ACR Definition 9.1's mature
cut, public bound $d$, stationary binding, grants and complete charges. A
reply is a paid current-source literal reply, with no generator, archive or
chronological-bit channel. Section 35 states its early-cut domain separately.

The results concern exact certificates and their information fibres. The
original $\rho_d$, $K_d$, output convention and TOTAL bills are retained.
The unrestricted deterministic polynomial-TOTAL and exact-original-normalizer
questions remain unresolved.

## 33. Authenticated chronology after a root certificate

**Definition 33.1 (chronological indices and well-formed witnesses).**
Let $F_0=0$, $F_1=1$, $F_{i+2}=F_{i+1}+F_i$, and

$$
B_t=F_{t+1}-1\quad(t\ge1),\qquad v_n=B_{n-1}\quad(n\ge2).
$$

For the one-based raw stream $z_j=s_{j-1}$, birth $j\ge1$ belongs to

$$
\tau(j)=\min\{t\ge2:j\le B_t\},\qquad
R(j)=j-B_{\tau(j)-1}.
$$

A normalized update index is $i=t-1\ge1$ for an update containing births.
Its last-birth sample is

$$
b_i=z_{B_{i+1}}=s_{B_{i+1}-1}\quad(i\ge1).
$$

There is no $b_0$: $B_1=0$, whereas $z_0$ is undefined. In particular,
$b_1=z_1=s_0$. These batch-end samples need not satisfy the original
recurrence in their $i$ index. Their consumer below uses the actual birth
$j=B_{i+1}$, update $\tau(j)=i+1$ and suffix length $n-i-1$.

For a proposed cut $\nu\ge2$, a root rank certificate consists of supplied
physical words $x,y$ with $|x|=\nu-1$ and

$$
\begin{array}{c|c|c}
\nu&|y|&\text{required replies}\\
2k+1&k&\operatorname{Read}(ya)=0\\
2k&k-1&\operatorname{Read}(yaa)=\operatorname{Read}(yba)=0,
\end{array}
$$

in addition to $\operatorname{Read}(x)=1$. Malformed lengths are rejected.
Every Read is at the same stationary physical root; no separate presence
premise for $y$ is assumed. Write $C_n(\nu;x,y)$ for acceptance on the
actual support $S_n$.

After acceptance, a proposed prefix $A=(a_1,\ldots,a_m)$ is checked in
increasing birth order, with $m\le B_{\nu-1}$. Reconstruct the old tree
at cut $\tau(j)-1$ from the first $B_{\tau(j)-1}<j$ proposed bits and
let $p_j(A)$ be its $R(j)$th beta leaf in physical lexicographic order.
Set $c_j=a$ for $a_j=1$, $c_j=b$ for $a_j=0$, and
$t_j=\nu-\tau(j)\ge1$. In ACR's full-law application $m=2d$ and
$\nu\ge n_0$, where $n_0$ is exactly ACR (ACR.23).

**Theorem 33.2 (universal soundness and existential completeness).**
For every actual source, actual cut $n\ge2$, proposed $\nu\ge2$ and
supplied well-formed $x,y$:

1. A present word $x$ of length $\nu-1$ implies $n\ge\nu$.
   An arbitrary word of that length need not be present when $n\ge\nu$.
2. For $|x|=\nu-1$, a negative reply has the alternatives $n<\nu$, or
   $n\ge\nu$ and $x$ attempts to continue beyond a terminal node.
3. $C_n(\nu;x,y)$ implies $\nu=n$, and

$$
\bigl(\exists x,y\;C_n(\nu;x,y)\bigr)\quad\Longleftrightarrow\quad\nu=n.
$$

The reverse direction quantifies existentially over witnesses. It does not
say that every well-formed supplied pair passes at the correct cut.

Proof. Use the rank-cone facts of ACR Theorem 22.2. A rank-$q\ge1$
cone has maximum present suffix depth $q-1$, while rank zero is terminal.
Every word of length $\ell$ is present for $q\ge2\ell$. The root at
cut $n$ has rank $n$. These facts prove the first two assertions.

A passing positive test forces $n\ge\nu$. If $\nu=2k+1$ and
$n\ge\nu+1$, every length-$(k+1)$ word is present. The required
length $|y|=k$ makes $ya$ such a word, contradicting its absence. If
$\nu=2k$ and $n\ge\nu+1$, every supplied length-$(k-1)$ word $y$
is present with residual rank at least three. One of its children has
rank at least two, so at least one of $yaa,yba$ is present. Thus acceptance
forces $n=\nu$, for every supplied well-formed pair.

Conversely, at $n=\nu$ choose a longest path for $x$. Repeatedly choosing
a rank-two decrement gives a length-$k$ path ending at rank one in the odd
case, or a length-$(k-1)$ path ending at rank two in the even case. These
supply the required $y$ and absences. At $\nu=2$ this means $y$ is empty,
$x$ is either child, and $aa,ba$ are absent. Ranks zero and one cannot pass
any proposed $\nu\ge2$ certificate. For a failure with correct proposed
cut, the zero source at $n=3$ has $aa$ absent, so the well-formed supplied
pair $x=aa,y=a$ fails. $\square$

**Proposition 33.2a (the length constraint is necessary).**
If the parity-dependent $y$ length is omitted, the root conjunction and its
indexed consequence are false even in ACR's mature domain. On the zero
all-index source with public $d=1$, actual $n=6$, proposed $\nu=4$,
$x=aaa$ (also $bbb$) and $y=aaaaaa$ pass the literal positive and two
negative tests. Yet $n\ne\nu$. Moreover $j=1$ has actual $z_1=0$ and
$\tau(1)=2$, but proposed $a_1=1$ gives $t_1=2$ and a present suffix
$aa$ below the proposed child $a$.

Proof. At cut six both constant-port spines have height at least three:
in the zero source their heights are three at $a$ and five at $b$.
Thus both choices of $x$ are present. The negative words have length eight,
exceeding the maximum depth five. The erroneous birth test is $aaa$, which
is present. The supplier requires $|y|=1$ at $\nu=4$, so this tuple is
not a well-formed certificate of Definition 33.1. The actual maturity
threshold for $d=1$ is $n_0=4$. $\square$

**Theorem 33.3 (maximal witnesses and earned indexed samples).**
Suppose a well-formed root certificate has passed. For $1\le j\le m$,
assume all proposed bits before $j$ have already been authenticated, either
by positive maximal witnesses or by complete negative certificates as below.
Then $p_j(A)$ is the actual birth parent, $t_j=n-\tau(j)$, and

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

A supplied suffix of length $t_j$ with positive reply universally certifies
that proposed bit under these hypotheses. An accepting supplied suffix
exists for the correct bit; an arbitrary supplied suffix need not pass.
Consequently an accepting supplied root-and-birth certificate for $(\nu,A)$
exists exactly when $\nu=n$ and $A=z_1\cdots z_m$, for $m\le v_n$.

Proof. Theorem 33.2 authenticates the cut. The authenticated earlier bits
reconstruct the actual old tree at $\tau(j)-1$, so GPO Proposition 39.2
identifies the actual parent independently of later bits. At cut $n$ the
child selected by $z_j$ has rank $t_j+1$, and the opposite child has rank
$t_j$. The former has a suffix of length $t_j$; the latter has maximum
suffix depth $t_j-1$. This proves both equivalences and the supplied-witness
soundness. Choose a longest suffix in each correct child to obtain
existential completeness, inductively in $j$. $\square$

For a single reply under the same actual-parent and maturity hypotheses,

$$
\operatorname{Read}(p_jc_jv)=0
\Longrightarrow
\bigl(a_j\ne z_j\bigr)
\vee
\bigl(a_j=z_j\ \wedge\ v\text{ is not a present maximal witness}\bigr)
\quad(|v|=t_j).
\tag{ACRC.2}
$$

The second alternative occurs: on the zero source at cut four, $j=1$,
the correct child is $b$ and $t_1=2$, but $baa$ is absent whereas $bba$
is present. Thus this negative reply alone does not imply $a_j\ne z_j$.
A single negative literal does refute a full candidate when that candidate
has a separately established prediction that the literal is present;
(ACRC.2) alone supplies no such prediction.

**Proposition 33.4 (paid complete native construction and its bills).**
After checking a supplied accepting root certificate, choose a trial bit at
each next index and enumerate all $2^{t_j}$ suffixes under its proposed
child. Stop with a positive witness if one appears; otherwise retain the
complete zero certificate $\bot$ and authenticate the complementary bit.
Reconstruct later parents using the bits thereby authenticated. For the
first $m\le v_n$ bits this uses at most

$$
3+\sum_{j=1}^{m}2^{t_j}
$$

Reads, counting the supplied root certificate's verification. If
$L_{\rm root}$ is its actual literal traffic, the total literal traffic is
at most

$$
L_{\rm root}+\sum_{j=1}^{m}(|p_j|+1+t_j)2^{t_j}
\le 3(n+1)+(n-1)\sum_{j=1}^{m}2^{t_j}.
$$

A supplied positive witness per authentic bit instead needs at most $m+3$
verification Reads. Its construction costs are separate. Both bounds
include the full parent addresses; $t_j$ alone is not the literal length.
Every enumerated reply, zero certificate, local computation, scratch write,
retained output and handoff remains paid in the original TOTAL model.

Proof. Apply (ACRC.1) at each step. A positive reply authenticates the trial
bit; exhausting all suffixes authenticates its complement. There is no
free disagreement or bit query. The old tree has at most $2j-1$ nodes and
$|p_j|\le\tau(j)-2$, hence each birth literal has length at most $n-1$.
Root words have length at most $n$, including the $n=2$ endpoint. These
give the stated bills. Sequential suffix enumeration and finite old-tree
reconstruction use finite backing and work; no polynomial TOTAL bound is
inferred from these exponential enumerations.

For completeness without supplied root witnesses, one may try
$\nu=2,3,\ldots$, search all $2^{\nu-1}$ possible positive $x$ words,
then all parity-length $y$ words for the required absences. At a proposal
with no positive $x$, skip the $y$ search. Soundness excludes an early
acceptance and completeness guarantees termination at $\nu=n$. Discovery
uses at most

$$
\sum_{\nu=2}^{n}\left(2^{\nu-1}+2^{\lfloor\nu/2\rfloor}\right)
$$

Reads: the odd $y$ search has one test per word, the even search at most
two. Its traffic is at most $n$ times this bound and is additional to any
subsequent verification bill. For a known public $d$ one may start at
$n_0$ instead. At $d=0$ the empty prefix requires no birth tests and the
zero descriptor is fixed; root recovery still has its own bill.

Finally, for $i\ge1$, $i+2\le n$ and $B_{i+1}\le m$, the same procedure
at $j=B_{i+1}$ authenticates the declared $b_i$, using suffix length
$n-i-1$. It does not obtain that sample without the preceding authenticated
prefix or the native witnesses. $\square$

## 34. Feedback algebra and the two-to-five all-index bridge

**Lemma 34.1 (all-index feedback composition, including singular laws).**
Let $p(E)s=0$ for every index $i\ge0$, and define $y$ at the same initial
origin by $q(E)y=s$, where $p,q$ are monic binary polynomials. All
nonleading taps, including the constant taps, may vanish. Then

$$
(pq)(E)y=0\quad(i\ge0),
$$

so the least all-index order of $y$ is at most $\deg p+\deg q$ and may
be smaller. These equations describe an autonomous generator construction,
not an added physical feedback, law-bit or chronological query service.

Proof. Commuting forward shifts gives $p(E)q(E)y=p(E)s=0$ at every
nonnegative index. Given the two finite seeds, monicity computes $s$ and
then $y$ forward; their joint state defines an autonomous generator fixed
before the first birth. No inverse transition or removal of a transient is
used. Degree-zero $p=1$ means $s=0$, and degree-zero $q=1$ means $y=s$.
The classical annihilator calculation is the ingredient already used in
GPO Lemma 29.2; the physical indexed application below still requires
Theorem 33.3's native replies. $\square$

**Theorem 34.2 (an exact order-$2$ source feeding an exact order-$5$ law).**
Let

$$
p(E)=E^2+E+1,\qquad q(E)=E^3+E+1.
$$

Take $s_0=0,s_1=1$, $s_{i+2}=s_i+s_{i+1}$, and initialize
$y_0=y_1=y_2=0$. Define the feedback output by

$$
y_{i+3}=y_i+y_{i+1}+s_i\quad(i\ge0).
\tag{ACRC.3}
$$

Then $s$ has least all-index order two, while $y$ has least all-index order
five and satisfies

$$
y_{i+5}=y_{i+4}+y_i,\qquad
 y[0{:}21]=000011111010100110001.
\tag{ACRC.4}
$$

Proof. The $2$ by $2$ Hankel matrix of $s$ beginning at zero is
$\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$, of rank two.
Multiplication over $\mathbb F_2$ gives

$$
(E^2+E+1)(E^3+E+1)=E^5+E^4+1,
$$

so Lemma 34.1 gives (ACRC.4). Direct forward substitution gives the stated
prefix and its first five Hankel rows:

$$
\begin{pmatrix}
0&0&0&0&1\\
0&0&0&1&1\\
0&0&1&1&1\\
0&1&1&1&1\\
1&1&1&1&1
\end{pmatrix}.
$$

This matrix is anti-triangular with anti-diagonal one and has rank five.
An order-$r<5$ all-index recurrence would express every column after the
first $r$ as a combination of its preceding columns, contradicting that
rank. Thus an order-two driver does not impose order two on its feedback
output. Installed as $z_j=y_{j-1}$, this is a legal autonomous source with
public bound $d=5$. Its first ten bits are mature for $n\ge7$ and can be
consumed by Theorem 33.3 with paid root and birth witnesses. This supplies
no free installation or acquisition. Singular examples such as $p(E)=E^2$
with seed $10$, a finite impulse, and $q(E)=E^3+1$ use the same forward
product argument. $\square$

**Proposition 34.3 (extremal-spine formula and its precise domain).**
In GPO's fixed global-port supplier, take an arbitrary nonempty ordered
alpha/beta tree $u$, one persistent bijection of physical ports with semantic
$L,R$ at every branch, $k\ge1$, and $x=\rho^{2k+1}u$. If $d_L,d_R$
are the original extreme-path lengths and $\eta_L,\eta_R$ indicate beta
terminal leaves, then

$$
h_L(x)=d_L+2k+\eta_L,\qquad
h_R(x)=d_R+k+\eta_R.
\tag{ACRC.5}
$$

For physical $a=L$ the pair $(h_a,h_b)$ is $(h_L,h_R)$; for $a=R$ it
is reversed. These are exactly GPO (GPO.25)'s fixed-port values. They
support its orientation probe, not a law-independent identity for arbitrary
autonomous orientations $z_j$.

Proof. Substitution preserves original branches. The terminal replacement
is $T_{2k+1}$ for alpha and $T_{2k+2}$ for beta, where $T_m=\rho^m\alpha$.
Its left height is $m-1$ for $m\ge1$ and its right height is
$\lfloor m/2\rfloor$. Adding the original path lengths gives (ACRC.5),
including both terminal labels and both global port bijections.

For $u=\alpha$ these two spines supply longest and shortest root-rank
paths. For arbitrary $u$ they need not do so: take
$u=\langle\alpha,\langle\alpha,\beta\rangle\rangle$ and $k=1$.
The two heights are $3,4$, but the maximum root-to-leaf depth is five and
the minimum is two, by adding the original leaf depths $1,2,2$ to those
of their $T_3,T_3,T_4$ replacements. Thus the claim that these spines
always supply globally longest and shortest rank witnesses is false in
the stated arbitrary-$u$ supplier domain. Autonomous birth-bit sources
instead use the actual-parent rank witnesses of Theorem 33.3. $\square$

## 35. A period-eleven extremal-observation fibre

**Definition 35.1 (source laws and observation domains).**
Let $s^A,s^B$ be the repeating words

$$
s^A[0{:}11]=10000000000,\qquad
s^B[0{:}11]=01000000000,\qquad z_j=s[j-1].
$$

Both satisfy $s_{i+11}=s_i$ at every $i\ge0$ and have exact period
eleven. Use the actual alpha origin and chronological updates. The
following cut-four supports have $B_4=4$ consumed births and $v_4=2$
mature bits. They are early-cut statements: for the public recurrence
bound $d=11$, ACR's full-law maturity threshold is $n_0=9$, since
$F_8-1=20<22\le F_9-1=33$. They do not satisfy that full-law maturity
premise at cut four.

**Theorem 35.2 (exact extremal ambiguity and complete legal separators).**
At cut four, the sources of Definition 35.1 both have $(h_a,h_b)=(2,2)$,
but their complete supports are

$$
\begin{aligned}
S_A&=\{\varepsilon,a,aa,ab,b,ba,bb,aba,abb\},\\
S_B&=\{\varepsilon,a,aa,ab,b,ba,bb,baa,bab\}.
\end{aligned}
$$

Every finite word on which their replies differ belongs to

$$
S_A\setminus S_B=\{aba,abb\},\qquad
S_B\setminus S_A=\{baa,bab\}.
\tag{ACRC.6}
$$

At the first full-law mature cut for public $d=11$, namely $n=9$, these
same sources instead have

$$
(h_a,h_b)_A=(5,6),\qquad (h_a,h_b)_B=(4,7).
$$

Thus this pair's equal extremal heights at cut four do not extend to that
mature cut.

Proof. Write $c(1)=a,c(0)=b$, and let $\bar c$ be the other port.
At update two the root splits: its beta child is $c(z_1)$ and its alpha
child is $\bar c(z_1)$. At update three the former splits using $z_2$,
creating both its depth-two children; the latter only changes alpha to
beta. At update four that latter depth-one beta splits, completing all
words through depth two. The depth-two beta at
$u=c(z_1)c(z_2)$ also splits, creating exactly $ua,ub$ at depth three.
The old leaves are processed once, so no deeper node is created then.
For prefixes $1000$ and $0100$, $u$ is respectively $ab$ and $ba$.
This gives both full supports. Each contains $aa,bb$ and neither contains
$aaa,bbb$, giving heights two. Set subtraction gives all separators.
The new bits consumed at update four determine the labels of its newborn
children, not which of those children are present.

For the mature-cut calculation, a beta leaf on the all-$a$ spine is first
in physical order, so its birth index at split update $t$ is $F_t$.
One on the all-$b$ spine is last, so its birth index is $B_t$.
At a split, both children are created; the selected child's next split is
one update later for a beta child and two for an alpha child. Apply these
rules and the stated eleven-cycles. The successive first-presence times
of the constant-port words, starting with depth one and continuing through
the first absent word at cut nine, are

$$
\begin{array}{c|c|l}
\text{law}&\text{port}&\text{first-presence times}\\
A&a&2,3,5,7,9,10\\
A&b&2,4,5,6,8,9,10\\
B&a&2,4,6,8,10\\
B&b&2,3,5,6,7,8,9,10.
\end{array}
$$

For example the successive splitting indices on the $A$ all-$a$ spine
are $2,5,13,34,55$; the bit at $34$ is one and the bits at the other
displayed indices are zero. On its all-$b$ spine they are $4,7,12,33,54,88$, with the
bit at $12$ one and the others zero. For $B$ they are respectively
$3,8,21,55$, all zero, and $2,7,12,20,33,54,88$, with only the bit at
$2$ one. Together with the root bit these determine every entry of the
table. Counting entries at most nine gives the asserted mature heights.
$\square$

**Proposition 35.3 (invisible newest bits and a common disagreement).**
Let $W_2=\{\varepsilon,a,aa,ab,b,ba,bb\}$ and, for a consumed
four-bit prefix $r$, write $S_r$ for its cut-four support. Then for every
choice of the four bits,

$$
S_r=W_2\cup\{c(r_1)c(r_2)a,\ c(r_1)c(r_2)b\}.
$$

Thus all four sources with a fixed first two bits have identical complete
support, independently of $z_3,z_4$. For example, the eleven-cycles whose
first four bits are $01uv$, $u,v\in\{0,1\}$, and whose other seven bits
are zero all have exact period eleven and identical complete cut-four
replies. Both newest bits can independently vary in this fibre. The
mature bits at this cut are exactly $z_1,z_2$.

For the comparison with reference $0000$, however, there is a common
word distinguishing it from each of $0100,1000,1100$. The full differences
are, in the order of those three alternatives,

$$
\begin{aligned}
S_{0000}\triangle S_{0100}&=\{bba,bbb,baa,bab\},\\
S_{0000}\triangle S_{1000}&=\{bba,bbb,aba,abb\},\\
S_{0000}\triangle S_{1100}&=\{bba,bbb,aaa,aab\}.
\end{aligned}
$$

In particular,

$$
\bigcap_{r\in\{0100,1000,1100\}}
   (S_{0000}\triangle S_r)=\{bba,bbb\}.
$$

The assertion that this fibre has no single reference-versus-every-alternative
disagreement is false. Either displayed common word is present in the
reference and absent in all three alternatives. Pairwise disjoint additions
alone do not settle that assertion: the removals are common.

Proof. The chronology in Theorem 35.2 gives the formula for every prefix.
If $z_1=0$, the update-four beta parents are $a$ first and $bc(z_2)$
second; if $z_1=1$, they are $ac(z_2)$ first and $b$ second. Thus $z_3$
and $z_4$ select labels at these actual ordered births. Their newborn
beta children can first split at update five, so neither orientation has
a support effect at cut four. This proves the full-support fibre and its
visibility boundary.

For first two bits $00,01,10,11$, the depth-three pairs are respectively
$\{bba,bbb\},\{baa,bab\},\{aba,abb\},\{aaa,aab\}$. They are mutually
disjoint, so every full symmetric difference between two of the four
representatives is the union of the corresponding two pairs. This proves
the three displayed differences, all other pair differences, and their
intersection. Each nonzero eleven-cycle used here is nonconstant; since
eleven is prime, its least period is eleven. The all-zero reference is
an eleven-periodic zero all-index law with least period one. All are legal
members of $\mathscr R_{11}$.

At any common mature cut $n\ge9$, all these sources still have the same
transcript restricted to $W_2$, since every word of length at most two is
present at every cut $n\ge4$. This statement does not assert equal mature
extremal heights, equal full mature supports, or a mature full-law ambiguity.
The common-disagreement calculation above concerns the original cut-four
reference comparison, not those later supports. $\square$

## 36. What the earned data do and do not recover

**Corollary 36.1 (native support-refutation is exact but paid).**
Under Theorem 33.3's authenticated cut, prefix and maturity hypotheses,
the complete finite service over $\{a,b\}^{t_j}$ authenticates the actual
$z_j$ with at most $2^{t_j}$ literal presence replies. A positive reply
certifies the trial orientation; a complete zero certificate certifies its
complement. Neither a single arbitrary negative reply nor a predicted
witness has that force.

Proof. Apply (ACRC.1), with the parent computed from the authenticated
prefix, and Proposition 33.4's actual enumeration. For $m=2d$, ACR's
maturity promise supplies every requested index, including the empty
prefix at $d=0$. The authentic prefix determines the full behavior by
GPO Lemma 29.2, but selecting and installing the exact $K_d(P)$ still uses
its original fixed enumeration and its paid work. $\square$

The cut-four period-eleven pair separates extremal observations from full
support at that early cut. The same-first-two-bit fibre concerns newest
bits, while Proposition 35.3 refutes the proposed no-common-disagreement
strengthening in its reference comparison. None of these finite observations
is an impossibility theorem for mature polynomial acquisition. Equally,
the finite witness constructions do not prove that acquisition polynomial.

The supplier correspondence is as follows. GPO §§27--29 supply the alpha
origin, actual beta order, $B_t$, the all-index class and its finite-separation
convention, including singular laws and zero order. GPO §39 supplies the
actual chronological-parent relation. ACR Definition 22.1 and Theorem 22.2
supply exactly the parity lengths, rank tests, universal certificate
soundness and existential completeness used here. ACR §§25 and 31--32
retain the original local normalizer and $\rho_d$. GPO Lemma 7.2 supplies
the fixed-global-port extremal formulas in their separate source domain.

Massey's [*Shift-Register Synthesis and BCH Decoding*][MAS] supplies classical
finite-prefix synthesis, and Rueppel's [*Linear Complexity and Random
Sequences*][RUEPPEL] supplies the classical linear-complexity setting. Neither
supplies physical chronology, a paid native witness or the exact original
normalizer's bill. The shift algebra is a reused ingredient; the source
applications, support fibres and comparison refutations above are derived
within the stated repository models. No literature-priority claim is made.

The unresolved target remains deterministic polynomial TOTAL acquisition
for the unrestricted unknown all-index source and unknown mature cut,
with the exact original $(P,K_d(P),n,B_n)$ output and original $\rho_d$.
Exponential native enumeration, a different recurrence presentation or a
changed normalizer does not settle it. Source binding, grants, stationary
visibility, actual backing, retained writes and handoff remain separate
paid prerequisites throughout.

[ACR]: RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT.md
[GPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md
[MAS]: https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI411.pdf
[RUEPPEL]: https://link.springer.com/content/pdf/10.1007/3-540-39805-8_21.pdf

## 追加锚（本行以下为增补区）
