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

## 37. A small original chronological answer and its exact information

**Definition 37.1 (the source-blind query entrance).** Fix the public integer
$d\ge0$ and precisely the original all-index class $\mathscr R_d$ of
[GPO, Definition 29.1][GPO]. Write $z_j=s_{j-1}$. The source is the actual
alpha-origin process with persistent physical ports $a<b$, simultaneous
old-leaf replacement and actual lexicographic beta-parent birth order.
Keep [ACR, Definition 9.1][ACR] and [PSA, Definition 1.1][ACRC-PSA] in their
entirety. In particular the unknown actual cut is any fixed finite integer

$$
 n\ge n_0(d),\qquad
 n_0(d)=
 \begin{cases}
 \min\{u\ge3:F_u-1\ge2d\},&d>0,\\
 2,&d=0.
 \end{cases}
\tag{ACRC.7}
$$

Only $d$ is numerical source information at entry. Law, seed, phase, cut,
source shape, labels, boundary, chronology, receipts and histories are
inaccessible. Common source-blind code and working resources contain no
source or cut advice. The genuine root binding is usable for calls but its
identity is not a source-information channel. A completed paid call accepts
a fully materialized finite word at this root and returns precisely
$\operatorname{Read}^s_n(w)=\mathbf1_{w\in S^s_n}$.

The actual cut stays fixed through every calculation, call, allocation,
intermediate or retained write and completed handoff; the controller makes
zero source updates. Genuine binding, valid grants, sufficient owned growing
readable backing, reliable call completion and finite local progress remain
premises with their original charges. Neither source allocator information,
allocation outcomes, capacity, duration, waiting, private generator state nor
source storage can supply another reply. There is no reset, recut, clone,
alias, ordinal port, supplied law, supplied cut or source-bearing certificate.

Let $U_s(j)$ be the physical parent of birth $j$ in the whole original
forward orbit, calibrated exactly as [PCR, Definitions 27.1 and 27.3][ACRC-PCR].
This is a mathematical answer, not a new physical operation. Put
$f(s)=U_s(2)$. A controller returning at least $f$ has one fixed output
projection $\pi$ with $\pi(o)=f(s)$ on every admitted $(s,n)$; it may return
other fields as well. Total correctness here requires a finite completed
return, including finite local computation and actual output retention, on
every source and every mature finite cut, with the stated service premises.

**Theorem 37.2 (the one-letter answer and the complete tuple image).**
For every original all-index source,

$$
 f(s)=c(s_0),\qquad c(1)=a,\quad c(0)=b.
\tag{ACRC.8}
$$

Consequently an authentic retained $s_0$ suffices to answer this query
without retaining the full law. If all source-dependent accessible
information must be carried by the retained record and no later source
access is allowed, at least two record values are necessary at $d\ge1$.
There is only one answer at $d=0$.

The complete ordinal-two query output, in PCR Definition 27.1's field order,
is the literal $c(s_0)$ together with

$$
 (j;b_v,\sigma_v,\tau_v,e_v,A_v,B_v,s_{j-1})
       =(2;2,\beta,3,2,2,4-s_0,s_1).
\tag{ACRC.9}
$$

Its whole-origin-orbit image has exactly one, three and four elements for
$d=0$, $d=1$ and $d\ge2$, respectively. Thus the pair $(s_0,s_1)$ is a
sufficient record for that complete tuple, and its distinct realizable pair
values require distinct records under the same no-further-access condition.
For $d\ge1$, every mature cut already contains this branching event. At
$d=0,n=2$ it has not yet occurred; the already-occurred query therefore
requires PCR's actual-cut guard, rather than the whole-orbit constant answer.

Proof. The root branches at update two using $s_0$. Its initial-beta child
is $c(s_0)$ and is the unique beta parent branching at update three. This
parent consumes $s_1$, has creation $(2,\beta)$, beta origin two and first
birth index two. Apply PCR (PCR.39) to the actual root coordinates
$(e,A,B)=(1,1,2)$. Its initial-beta child's second clock is three if $s_0=1$
and four if $s_0=0$. This proves every field of (ACRC.9), including the
exterior offset in $B_v$; replacing that clock by a local ordinal would give
the wrong tuple when $s_0=0$.

The zero and constant-one laws are in $\mathscr R_1$, and their answers in
(ACRC.8) differ. Identical retained records with identical future-free
instructions would give identical answers, proving the two-value necessity.
Equation (ACRC.8) supplies the matching sufficient record. The complete tuple
recovers $s_0$ from its literal and $s_1$ from its event bit, and conversely
(ACRC.9) reconstructs it from that pair.

At $d=0$ the sole pair is $00$. At $d=1$ the complete class is
$0^\infty,10^\infty,1^\infty$, with pairs $00,10,11$, as in GPO
Proposition 37.3. At $d\ge2$ every pair is realized by taking it as the
seed of $s_{i+2}=0$ for every $i\ge0$. These are original all-index laws,
not arbitrary finite prefixes followed by an unbounded recurrence onset.
The tuple image counts follow. Finally $n_0(d)\ge4$ for $d\ge1$, whereas
the event occurs at three. PCR's occurrence guard is exactly $\tau_v\le n$,
so the stated mature and zero-order cases follow. $\square$

**Proposition 37.3 (equal small answers and unequal later original queries).**
The retained answer in (ACRC.8) does not in general suffice for a larger
chronological menu. For every fixed public $d\ge1$, the original sources
$x=10^\infty$ and $y=1^\infty$ satisfy

$$
 U_x(2)=U_y(2)=a,\qquad U_x(3)=ab,\quad U_y(3)=aa.
\tag{ACRC.10}
$$

For every fixed public $d\ge2$, even the complete ordinal-two output agrees
for $x=10^\infty$ and $t=(10)^\infty$, but

$$
 U_x(6)=abb,\qquad U_t(6)=aba.
\tag{ACRC.11}
$$

At the particular common public bound $d=2$ and common actual cut $n=5$,
the latter pair also has

$$
 \operatorname{Read}^{x}_5(abaa)=0,\qquad
 \operatorname{Read}^{t}_5(abaa)=1.
\tag{ACRC.12}
$$

Thus the shared retained tuple does not determine the reply to that legal
same-root presence-and-stop request before the call is made. The cut five
specifies the two realizations; it is not supplied to the controller.

The ordinal comparisons use the same actual alpha origin, the same physical
ports and any common fixed $n\ge n_0(d)$. All their displayed queried events
have occurred at those cuts. The literal comparison keeps its stated
cut-five domain. They are neither comparisons of shifted cores
nor examples obtained by changing the cut during acquisition.

Proof. On semi-infinite sequences, $Ex=0$, $(E+1)y=0$ and
$(E^2+1)t=(E+1)^2t=0$ at every nonnegative index. Thus the impulse retains
its singular transient, and the alternating source retains the permitted
repeated factor. They belong to the claimed classes without altering the
source promise or bounding periods for the rest of the class.

For $s_0=1$, the root's beta child is $a$. At update three it splits using
$s_1$; its beta child is $ab$ when $s_1=0$ and $aa$ when $s_1=1$.
That child is the first beta parent at update four, giving (ACRC.10).
For $x$ and $t$, both first two bits are $10$, so their complete outputs
in (ACRC.9) agree, with literal $a$ and tuple
$(2;2,\beta,3,2,2,3,0)$. At update four the ordered beta parents are
$ab,b$, consuming bits $s_2,s_3$. At update five the first beta parent
is $aa$, of index five. The second is the beta child of $ab$, of index
six: it is $abb$ for $x$ and $aba$ for $t$. This proves (ACRC.11).
At update four $aba$ is initially alpha for $x$ and initially beta for
$t$. At update five it respectively only changes label or creates both
children, proving (ACRC.12). Here $n_0(2)=5$, so both are authentic mature
realizations and $abaa$ is a legal total-presence operand in either one.
Birth three occurs at four and birth six at five; $n_0(d)\ge5$ when
$d\ge2$. Hence the comparisons also satisfy PCR's actual occurrence guard.
A record consisting only of the shared earlier answer cannot select the
unequal later answers without additional source information. $\square$

## 38. Pointwise acquisition prices without returning the age

**Definition 38.1 (literal prices and a uniform envelope).** Fix $d\ge1$
and a deterministic total correct controller of Definition 37.1 returning
at least $f$. On an actual input $(s,n)$ write its submitted words in order
as $w_1,\ldots,w_Q$, and define

$$
 \begin{aligned}
 Q(s,n)&=\text{number of completed presence calls},\\
 M(s,n)&=\max\bigl(\{0\}\cup\{|w_i|:1\le i\le Q(s,n)\}\bigr),\\
 W(s,n)&=\sum_{i=1}^{Q(s,n)}|w_i|.
 \end{aligned}
\tag{ACRC.13}
$$

Traffic $W$ counts every submitted full root literal, including repeated
prefixes, repeated calls and calls with either reply. It is not the length
of a union of operands, a suffix-only bill or a local bit-write count.
PSA denotes this same traffic coordinate by $J$ and uses $W$ instead for
cumulative local writes. Local work, scratch and retained writes, backing,
source storage, service and installation keep their separate charges here.

A uniform linear literal envelope means that fixed real constants
$\kappa\ge1$ and $\lambda\ge0$ satisfy

$$
 \forall s\in\mathscr R_d\;\forall n\in\mathbb Z_{\ge n_0(d)},
 \qquad M(s,n)\le\kappa n+\lambda.
\tag{ACRC.14}
$$

The constants may depend on this fixed public controller and $d$, but not
on its actual source, cut or transcript. This is a hypothesis about the
whole controller, not an inferred price guarantee for a physical service.

**Theorem 38.2 (finite positive prefixes are actual, and cannot be terminal).**
Under Definition 38.1, the formal path obtained by answering every call one
has a next fully materialized call after every finite prefix, reached by
finite local work. If its first $i$ words are $w_1^+,\ldots,w_i^+$ and

$$
 L_i=\max\bigl(\{0\}\cup\{|w_j^+|:1\le j\le i\}\bigr),\qquad
 L_0=0,\qquad N_i=\max(n_0(d),2L_i),
\tag{ACRC.15}
$$

then every source at the single fixed cut $N_i$ realizes that entire
positive prefix. The sequence $L_i$ is unbounded. Every actual terminating
run has at least one negative reply, and on every actual $(s,n)$,

$$
 M(s,n)>\frac n2,\qquad W(s,n)>\frac n2.
\tag{ACRC.16}
$$

These conclusions require no envelope (ACRC.14).

Proof. ACR Proposition 2.2 gives, uniformly over the original law,
$b_w\le2|w|$ for every nonempty word, and the empty word is always present.
Thus every finite family of words of length at most $L$ is present at every
cut at least $2L$. This is precisely ACR Proposition 12.2's saturation.

The compared data are in the original entrance image. For a seeded
all-index law and any finite $N$, its original forward history starts from
alpha, uses that autonomous stream fixed before initialization, and makes
exactly $N$ original updates with the prescribed physical beta order.
Every update has finitely many old leaves. Erasing the observer data while
retaining the stipulated genuine binding and service gives the admitted
$(s,N)$ entrance. This is a model realization under the original service
premises, not a construction of physical authority from a word; its generated
source, history and storage retain their original costs.

Construct the positive path inductively. The empty prefix is realizable at
$n_0(d)$. For any already constructed finite prefix, all its words are
present on every source at cut $N_i$. Determinism and source blindness
therefore give the same control, operands and local actions through that
prefix in each such actual realization. A halt after further source-free
work would give the same output on the zero and constant-one sources at
that same cut, contradicting their different $f$ values. Infinite local
work without another call is impossible because this prefix is reached on
an actual input on which total correctness requires finite return. Hence a
next call is reached in finite local work and has a finite literal. This
completes the induction without assuming an oracle that decides whether an
unrealizable computation will terminate.

If all $L_i$ were bounded by an integer $L$, one fixed cut
$N=\max(n_0(d),2L)$ on, for example, the zero source would realize every
one of these calls with reply one. That actual run would be infinite,
contradicting total correctness. So the formal positive path is unbounded.
An actual finite run with only positive replies would terminate on a finite
prefix just proved nonterminal. It must therefore have a first negative
reply, at a nonempty word $w$. Saturation implies $n<2|w|$. Its actual
operand contributes to both the maximum and the sum in (ACRC.13), proving
(ACRC.16). This argument forces one such long operand on each run; it does
not give that length to every Read. $\square$

**Theorem 38.3 (unknown-scale lower bound for a one-letter answer).**
For every deterministic source-blind total correct controller returning at
least $f$, assume exactly the uniform envelope (ACRC.14). Set

$$
 r=2\kappa,\qquad K=\kappa n_0(d)+\lambda>0.
\tag{ACRC.17}
$$

Then for every actual $s\in\mathscr R_d$ and every actual fixed integer
$n\ge n_0(d)$, on that same execution,

$$
 \begin{aligned}
 M(s,n)&>n/2,\\
 W(s,n)&>n/2,\\
 Q(s,n)&>\log_r\left(1+\frac{(r-1)n}{2K}\right).
 \end{aligned}
\tag{ACRC.18}
$$

In particular the conclusion is pointwise on the source and cut, including
the lower endpoint $n=n_0(d)$. The output need not contain $n$, a complete
law or any field other than the one-letter answer.

Proof. Apply Theorem 38.2 to this same controller. After its first $i-1$
positive replies, every source at cut $N_{i-1}$ reaches the next call
$w_i^+$ by finite work. Apply the envelope to a complete actual run from
that independent admissible input. The next word, whether its reply there
is zero or one, is among that run's submitted operands. Therefore

$$
 \begin{aligned}
 |w_i^+|&\le\kappa N_{i-1}+\lambda\\
 &\le 2\kappa L_{i-1}+\kappa n_0(d)+\lambda
       =rL_{i-1}+K,\\
 L_i&\le rL_{i-1}+K.
 \end{aligned}
\tag{ACRC.19}
$$

The last line also uses $r\ge2$, $K>0$ and $L_{i-1}\ge0$ to bound the
previous maximum. Induction starting with $L_0=0$ yields

$$
 L_i\le K\sum_{j=0}^{i-1}r^j
       =K\frac{r^i-1}{r-1}.
\tag{ACRC.20}
$$

Now fix the actual $(s,n)$ once and for all. Let $q$ be its first negative
call index, whose existence and finiteness are Theorem 38.2. Until this
call its control path is the positive path, so its negative operand is
$w_q^+$. Saturation at this negative operand and (ACRC.20) give

$$
 \frac n2<|w_q^+|\le L_q
       \le K\frac{r^q-1}{r-1}.
\tag{ACRC.21}
$$

Since $r>1$, taking logarithms proves the claimed strict bound on
$q\le Q(s,n)$. The peak and traffic bounds are already (ACRC.16).

The cuts $N_i$ in the proof label separate possible original-source
realizations. No run is physically moved from one of these cuts to another;
the actual input in (ACRC.21) stays stationary at its fixed $n$. Uniformity
of the envelope across these independently realizable cuts is essential to
(ACRC.19). A bound only at the chosen actual cut would not justify that
step. No returned age is counted in the distinguishability argument: the
zero and constant-one sources require different output projections even
when the output omits age. $\square$

## 39. Matching Read order, retained obligations and supplier scope

**Theorem 39.1 (fixed-bound Read order and the acquisition/retention split).**
At each fixed $d\ge1$, the original erased stationary entrance admits a
deterministic controller for $f$, and also for the complete ordinal-two
query, with

$$
 Q(s,n)=O_d(1+\log(n+2)),\qquad
 M(s,n)\le2n-1,\qquad
 W(s,n)=O_d(n(1+\log(n+2))).
\tag{ACRC.22}
$$

These are existing acquisition and supplied-query bounds composed on the
same original source. In conjunction with Theorem 38.3, their logarithmic
Read order in the unknown cut is attained under a uniform linear literal
envelope, even though the retained answer needs only the small record of
Theorem 37.2. The constants and conclusions assert neither a sharp dependence
on $d$ nor an $\Omega(n\log n)$ traffic lower bound nor a total-memory optimum.

The same necessary lower bounds (ACRC.18) apply to a controller delivering
the original $(P,n)$ or $(P,K_d(P),n,B_n)$, whenever it satisfies (ACRC.14)
and the original complete service and installation premises. Those larger
outputs, original $K_d/\rho_d$ firstness, full-future readiness and completed
installation remain separate obligations; they are not replaced by $f$ or
by a small query record.

Proof. Reuse PSA Theorem 8.4 on precisely Definition 37.1's entrance. It
actually acquires and retains the transient-inclusive $(P,n)$, including
singular sources and repeated factors, with no supplied period or core.
Its earned spine height $h$ gives $H=2h+1$ with $h+1\le n\le H$.
Thus $H\le2n-1$, its full-root maximum literal is at most $H$, and its
Read bound is $O_d(1+\log(n+2))$. Its literal traffic is $J\le HQ$.
These are exactly the three coordinates in (ACRC.22), with $J=W$ in
(ACRC.13)'s notation.

For $f$, extract the first bit of this authentic $P$ and use (ACRC.8).
For the complete tuple, either use (ACRC.9) on its first two bits or apply
PCR Theorems 27.4 and 27.6 to the acquired $(d,P)$ and query $j=2$.
Those are supplied-data computations with represented operands and charged
writes and output; they add no physical Read. At $d\ge1$ the mature-cut
promise passes the actual occurrence guard. The retained small record may
then omit the other acquired bits only if no larger menu or original output
is owed. Erasing that extra working information refunds none of the paid
acquisition, backing or write costs. The resulting controller has the
uniform envelope $\kappa=2,\lambda=0$. Theorem 38.3 supplies the lower
Read order for every fixed controller with a uniform linear envelope; it
does not require these particular envelope constants.

For the original output, its authentic $P$ contains $s_0$, so a fixed output
projection gives $f$. Theorem 38.3 therefore applies without weakening that
output. PSA's acquisition does not select the original first row, and PCR's
least-annihilator synthesis is not that first-row selection either. ACR
Theorems 21.4, 26.1 and 29.2 and §§31--32 retain that normalization and
completed-writeback task with the exact original enumeration. GPO §§34 and
39 retain source binding, synchronized continuation and actual-call charges.
All source storage, grants, stationarity, backing, retained writes and
installation costs remain paid; no hypothetical computation acquires a
physical ordinal port or a new read service.

The source-specific lower deduction uses ACR Proposition 2.2's uniform
physical first-presence bound and extends Proposition 12.2's fixed-menu
saturation to the actually reached positive path with (ACRC.19). ACR
Proposition 12.1 concerns full-output finite-window capacity and separate
worst-case coordinates; it does not supply this pointwise bound for a
nonconstant output omitting age. ACR Proposition 10.2 supplies the existing
inverse existence, ACR §§21--22 and 27--32 supply normalization, certificates
and acquisition, and PCR §§22--27 supply represented full-source query
computations. None is used as free source advice. The source-bearing supplied
certificates in §33 have a different entrance from Definition 37.1.
GPO §§37--38 concern full-future preparation with actual updates from the
origin, rather than this stationary unknown-cut one-letter task.

The classical doubling and bisection used inside the upper supplier are
already identified in ACR Theorem 3.2 and Proposition 9.2 with
[Bentley--Yao, *An Almost Optimal Algorithm for Unbounded Searching*,
SLAC-PUB-1679, pp. 2--5][ACRC-BY]. That task returns an unknown monotone
threshold. The lower proof here derives its scale obstruction from a
nonconstant original-source statistic and never requires returning the
threshold. No finite-hypothesis splitting assumption from generalized binary
search is invoked; the neighborliness and coherence restrictions documented
in ACR Proposition 12.3 remain separate. The native
`NativeSerialMachine.reached_prefix_replay` supplies the reached-prefix
reasoning pattern, with source-free local control and finite actual runs;
its four-valued semantic source and `NativeRankedNavigationCompiler`'s fixed
semantic ports are not a compiled specialization to this binary locally
wired source. These are repository-derived mathematical deductions using
the stated suppliers, without a new kernel-verification or literature-priority
claim.

At $d=0$, (ACRC.8) is the constant $b$ and its whole-orbit tuple is fixed;
no source call is needed for either of those outputs alone. The original
unknown $(P,n)$, an actual occurrence guard and a completed physical handoff
still have their own requirements. At $d\ge1$, Theorem 38.3 concerns only
deterministic total correct zero-update controllers and uniform peak
literal envelopes. It makes no randomized or expected-cost assertion,
physical-duration bound, universal acquisition optimum or claim that a
single small answer supplies full legal continuation. The complete original
all-index class, singular transients, repeated factors and unrestricted
periods are unchanged throughout. $\square$

[ACRC-PSA]: RECURSIVE_RELATIONAL_OBSERVATION_POLYNOMIAL_SOURCE_ACQUISITION.md
[ACRC-PCR]: RECURSIVE_RELATIONAL_OBSERVATION_PERIODIC_CLOCK_RIGIDITY.md
[ACRC-BY]: https://www.slac.stanford.edu/pubs/slacpubs/1500/slac-pub-1679.pdf

## 追加锚（本行以下为增补区）
