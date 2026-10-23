# Coupled rank escape and complete signed support

> This generic-v1 volume is mathematical reference input. Its proofs are ordinary
> mathematics, with no assertion of Lean-kernel verification. Integrated content
> is extended at the append anchor.

## 1. Native sources and the complete acquired question

**Definition 1.1 (native algebra and inclusive observation).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle s,t\rangle&=\langle\rho s,\rho t\rangle,\\
T_j&=\rho^j\alpha\qquad(j\in\mathbb N).
\end{aligned}
\tag{CRE.1}
$$

Sources are nonempty finite free ordered trees. There is no common size, depth
or rank bound. The operation $\rho$ is interpreted by (CRE.1), not a free unary
constructor. An address is a word over $\{L,R\}$, with root $\varepsilon$.
The reply $r_u(p)$ is $\alpha,\beta,\mathsf{branch}$ or $\mathsf{absent}$;
strict descendants of a leaf are absent. Write

$$
p_h(u)=(r_u(p))_{|p|\le h},\qquad
u\equiv_h v\Longleftrightarrow p_h(u)=p_h(v).
\tag{CRE.2}
$$

Every occurrence of a named argument has the same value. Sharing a value does
not quotient the ordered source tree or discard any occurrence.

**Definition 1.2 (entire acquired fiber and complete rows).** Use
[ARH, Definitions 1.1–1.2][ARH]. For a finite prefix-free original cut $A$,
$R_A(u)$ retains the entire concrete numbered-hole exterior, the ordered
reached set $A\cap\operatorname{Pos}(u)$, and the equality partition of the
entire reached subtrees. Absent cut addresses contribute no holes. An attained
input $I=(P,R,H_0,H_{\rm rel},Q,N)$ has entire fiber

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{CRE.3}
$$

A literal $(e,p,c)$ imposes $r_{\rho^e u}(p)=c$. A signed record
$(e,p,f,q,\bowtie)$, $\bowtie\in\{=,\ne\}$, imposes

$$
p\in\operatorname{Pos}(\rho^e u),\quad
q\in\operatorname{Pos}(\rho^f u),\quad
(\rho^e u)|_p\ \bowtie\ (\rho^f u)|_q.
\tag{CRE.4}
$$

Both guards are required for either sign. Absence is not a negative
certificate. Lists retain repetitions; every record in one realization
concerns its same original source. Every old class, cross-class inequality
and off-task condition belongs to (CRE.3).

For distinct attained complete labels $r_0,r_1$ put

$$
D_i=\{u\in D:R_Q(u)=r_i\},\qquad
J(h)\Longleftrightarrow
\exists u_0\in D_0\ \exists u_1\in D_1\quad u_0\equiv_h u_1.
\tag{CRE.5}
$$

The two witnesses are alternative originals producing one common retained
input. Each satisfies one whole source contract and its own complete row;
they are not incompatible labels assigned to one realization. Other rows
remain in $D$.

**Assumption 1.3 (paid producer and authentic continuation).** Impose exactly
[ARH, Assumption 1.3 and Proposition 2.1][ARH]. A public source-total paid
producer acquires the old row and the finite whole-subtree endpoint descriptions
at their actual epochs, computes signs from those descriptions, advances the
same register and original root to certified $N$, and makes the stipulated
complete access cut. Its entire accessible state is a common recoverable
encoding of $I$ and common parameters, with original-source fiber exactly $D$.
Every source in $D$ gives that state, and every source giving it lies in $D$.

Every accessible source-dependent cache, count, length, address, control
position, timing field, permission, archive and handle is included in this
premise. It is an access assumption, not a physical-erasure conclusion.
Subsequent actions are paid four-valued $\mathsf{Read}(p)$ and real serial
forward $\mathsf{ApplyRho}$ on that same register. A correct service is
deterministic, effective and terminating on every source in $D$. There is no
mathematical chart, rank, equality, selected-source, reset, reroot, clone,
old-version or clock port. Acquisition, new reads, literal words, updates,
local computation, preparation, installation, memory, retention and entry
remain separate charges.

## 2. A recognizable whole acquired family

**Definition 2.1 (coupled native expressions).** Define

$$
\begin{aligned}
W(a,x,v,y,z,w)
 &=\langle a,\langle x,\langle v,\langle y,\langle z,w\rangle\rangle\rangle\rangle\rangle,\\
F_a(y)&=\langle\alpha,\langle a,\rho y\rangle\rangle,\\
G_a(y)&=\langle\alpha,\langle\rho a,\rho y\rangle\rangle,\\
U(a,x,v,y)&=W(a,x,v,y,F_a(y),G_a(y)).
\end{aligned}
\tag{CRE.6}
$$

The six original cut addresses, in lexicographic order, are

$$
(q_a,q_x,q_v,q_y,q_z,q_w)=(L,RL,RRL,RRRL,RRRRL,RRRRR),\qquad
Q=\{q_a,q_x,q_v,q_y,q_z,q_w\}.
\tag{CRE.7}
$$

They are prefix-free. Take $P=\{\varepsilon\}$ and its reached one-hole
old row, exterior $\square_1$ and singleton partition. Thus the old row
itself imposes no extra restriction on a nonempty finite original.

**Definition 2.2 (base records and optional ceiling).** At epoch zero retain
branch literals at

$$
\varepsilon,R,R^2,R^3,R^4,q_a,q_z,q_zR,q_w,q_wR,
\tag{CRE.8}
$$

and $\alpha$ literals at $q_zL,q_wL$. Retain the following whole signed
records, with both endpoint guards:

$$
\begin{gathered}
(0,q_a,1,q_aL,=),\\
(0,q_zRL,0,q_a,=),\qquad (0,q_zRR,1,q_y,=),\\
(0,q_wRL,1,q_a,=),\qquad (0,q_wRR,1,q_y,=),\\
(0,q_y,0,q_a,\ne).
\end{gathered}
\tag{CRE.9}
$$

One may also retain $(0,q_aL^m,\mathsf{absent})$ for one supplied integer
$m\ge2$. Write $m=\infty$ when this literal is absent; $\infty$ is notation
for an omitted ceiling, not a finite rank. Put

$$
A_m=\{j\in\mathbb N:j\ge2,\ j\le m\text{ if }m<\infty\}.
\tag{CRE.10}
$$

Apart from repetitions, the only further records admitted by this definition
are the structural negatives of Definition 2.3. The final authentic $N$ is
at least one and at least every additional recorded epoch. No acquisition
description survives as an undeclared extra field.

**Definition 2.3 (structural negative recognition).** An additional negative
list $\mathcal H$ is recognized as follows. For an endpoint $(e,p)$,
distribute its supplied finite power $\rho^e$ through
$U(T_j,x,v,y)$. Evaluate powers of finite grounds; replace atomic occurrences
by $T_{j+c}$ and residual occurrences by $\rho^c x,\rho^c v,\rho^c y$,
with fixed nonnegative $c$. Navigate $p$ through explicit pairs and evaluated
finite grounds only. An endpoint may stop at any node or token. It may not
descend into an unspecified atomic or residual token. A descent meeting a
ground leaf before its endpoint fails recognition.

Successful navigation produces an entire reached endpoint expression
$E_{e,p}(j,x,v,y)$, in the mixed native grammar of NIC. For each supplied
record $(e,p,f,q,\ne)$ retain its actual whole comparison
$E_{e,p}\ne E_{f,q}$, with repeated occurrences unchanged. Their entire
conjunction is $\Delta(j,x,v,y)$; an empty list gives true.

Recognition is a finite syntactic algorithm on the supplied acquired input:
check the stated $P,R,Q$, the common integer $N$ against every record epoch,
all specified base literals and records, the permitted optional literal,
and every additional endpoint by the above navigation. It needs no productive description,
completion point or unknown source coordinate. It recognizes this presented
family, not all equivalent acquired presentations. An extra positive record,
extra unallowed literal or failed structural navigation is outside the class,
not a NO answer to (CRE.5).

**Theorem 2.4 (exact structural guards).** For every successfully recognized
endpoint and every $j\in A_m$, $x,v,y\in\mathcal T$,

$$
p\in\operatorname{Pos}(\rho^e U(T_j,x,v,y)),\qquad
(\rho^e U(T_j,x,v,y))|_p=E_{e,p}(j,x,v,y).
\tag{CRE.11}
$$

Consequently every additional signed predicate is equivalent to its retained
whole-tree negative, in both directions, on this entire parameter domain.

**Proof.** Distribution is the actual pairing law in (CRE.1), not a change
of signature. Atomic powers add to $j$; powers on residuals compose by adding
fixed exponents. Induct through the finite address navigation. An explicit
pair has both children reached for every assignment. Navigation in an
evaluated ground tree has its exact finite subtree and guard. A stopped
token is nonempty for every assignment. These cases prove (CRE.11) and
termination: neither navigation nor power evaluation enters an unknown
parameter. Applying (CRE.11) to both endpoints of each record proves the
two signed directions. No missing endpoint is replaced by a disequality.
$\square$

## 3. Entire sources and both designated full strata

**Theorem 3.1 (the whole acquired fiber).** For every input recognized in
§2 its entire fiber, conditional on Assumption 1.3 for the actual producer,
is exactly

$$
D=\{U(T_j,x,v,y):j\in A_m,\ x,v,y\in\mathcal T,
                 \ y\ne T_j,\ \Delta(j,x,v,y)\}.
\tag{CRE.12}
$$

Both inclusions reconstruct the same finite original source. Before the
displayed negatives its domain is precisely $A_m\times\mathcal T^3$.
Every source has all six $Q$-holes reached and the full exterior
$W(\square_1,\square_2,\square_3,\square_4,\square_5,\square_6)$.

**Proof.** The original branch literals force the five-pair outer spine
$W(a,x,v,y,z,w)$, with $a$ a branch, and force
$z=\langle\alpha,\langle b,c\rangle\rangle$,
$w=\langle\alpha,\langle d,e\rangle\rangle$.
Original branches persist at later epochs. Thus the first record of
(CRE.9) is exactly

$$
L\in\operatorname{Pos}(\rho a),\qquad a=(\rho a)|_L.
\tag{CRE.13}
$$

Apply the existing finite classification [ARH, Theorem 4.2][ARH] to this
same subtree with $(n,m,p)=(0,1,L)$. Its entire guarded fiber is
$\{T_k:k\ge1\}$. The original branch literal excludes $T_1=\beta$,
so $a=T_j$ with $j\ge2$. This is a consequence of the acquired record;
atomic membership is not a new source promise. The rank is unique by the
native clock $\kappa(T_j)=j$ from ARH Definition 4.1. This reuses the
feedback classification, also used in ARH Application 26.1, rather than
reproving a finite native centralizer theorem.

The next four positives in (CRE.9) give, in order,
$b=a$, $c=\rho y$, $d=\rho a$, $e=\rho y$. Their guards hold because
the stipulated original parents are branches and persist. These reconstruct
$z=F_a(y),w=G_a(y)$, including both occurrences of the same $a,y$.
The last record retains precisely $y\ne a$. Along the left spine of
$T_j$, the subtree at $L^d$ is $T_{j-d}$ for $0\le d\le j-1$;
the last one is $\beta$, and $L^j$ and its descendants are absent.
The recurrence $T_{j+2}=\langle T_{j+1},T_j\rangle$ therefore gives

$$
r_{T_j}(L^m)=\mathsf{absent}\quad\Longleftrightarrow\quad j\le m.
\tag{CRE.14}
$$

Thus the optional literal is exactly the rank ceiling. Theorem 2.4 retains
every additional negative and both guards. This derives (CRE.12) from the
whole acquired predicate and recovers that original itself.

Conversely, each source in (CRE.12) has every literal and the old root row.
The atomic recurrence gives
$\rho T_j=T_{j+1}=\langle T_j,T_{j-1}\rangle$, proving the first
guarded equality. Substitution in (CRE.6) proves the other four positives
with their reached endpoints. The displayed $y\ne T_j$ proves the base
negative; (CRE.14) proves the optional absent reply. Theorem 2.4 proves
every additional negative at its recorded epochs. This establishes the
reverse inclusion, including all records and repetitions.

For the actual producer use ARH Proposition 2.1 with these public coordinates.
It computes the old row, acquires the paid endpoint descriptions at epochs
zero and one and at the additional epochs, compares descriptions while
they are accessible, continues the same register to $N$, and performs the
stipulated complete cut. Every source satisfying these records produces
the same successful retained input; conversely that successful input
entails precisely the records just analyzed. Earlier descriptions are
pre-cut paid evidence, not old-version runtime reads. This is exactly the
producer correspondence required in Assumption 1.3. $\square$

**Definition 3.2 (complete designated labels).** With the full exterior and
reached set in Theorem 3.1, let $r_0,r_1$ have complete partitions

$$
\pi_0=\{\{1\},\{2,3,4\},\{5\},\{6\}\},\qquad
\pi_1=\{\{1\},\{2,5\},\{3,6\},\{4\}\}.
\tag{CRE.15}
$$

Define

$$
\begin{aligned}
\Theta_0(j,y)&=U(T_j,y,y,y),\\
\Theta_1(j,y)&=U(T_j,F_{T_j}(y),G_{T_j}(y),y),\\
\Delta_0(j,y)&=\Delta(j,y,y,y),\\
\Delta_1(j,y)&=\Delta(j,F_{T_j}(y),G_{T_j}(y),y),\\
C_i(j,y)&\Longleftrightarrow y\ne T_j\ \land\ \Delta_i(j,y).
\end{aligned}
\tag{CRE.16}
$$

Every substitution in (CRE.16) is simultaneous throughout the entire list.
In particular its copies of $y$ and of $j$ are shared.

**Theorem 3.3 (both whole-stratum correspondences).** For $i=0,1$,

$$
D_i=\{\Theta_i(j,y):j\in A_m,\ y\in\mathcal T,\ C_i(j,y)\}.
\tag{CRE.17}
$$

All cross-class inequalities of both full partitions hold exactly; none is
replaced by selected equality bits. Before negatives each chart has the full
product $A_m\times\mathcal T$.

**Proof.** For finite $y$, the height of $\rho y$ is at least the height of
$y$, since original branches persist. Both $F_a(y)$ and $G_a(y)$ have
height strictly greater than that of $y$. Hence they both differ from $y$.
For $a=T_j$, $j\ge2$, their left children are $\alpha$ whereas the left
child of $a$ is $T_{j-1}\ne\alpha$, so they both differ from $a$.
They differ from one another by their inner left children
$T_j\ne T_{j+1}$. Together with the retained $y\ne a$, the four
values $a,y,F_a(y),G_a(y)$ are pairwise distinct.

In $\Theta_0$ the six holes are
$(a,y,y,y,F_a(y),G_a(y))$; in $\Theta_1$ they are
$(a,F_a(y),G_a(y),y,F_a(y),G_a(y))$.
The pairwise distinctions prove every different-class inequality, and the
displayed repetitions prove every within-class equality, in (CRE.15).
The entire exterior and reached set follow from Theorem 3.1. The
substituted negative conjunction preserves all additional signed records.
Thus each displayed chart point lies in its stated complete stratum.

Conversely, in a source from (CRE.12), $r_0$ forces $x=v=y$, and $r_1$
forces $x=F_a(y),v=G_a(y)$. These reconstruct that same source as its
respective $\Theta_i$. Its original negative list becomes precisely
$C_i(j,y)$. This proves the other inclusion without dropping any row
field. It also establishes the Cartesian domains directly, independently
of a choice of feasibility witness. $\square$

## 4. Automatic entire support, with no residual section replacement

**Definition 4.1 (full feasible supports).** Define

$$
\begin{aligned}
S_D&=\{j\in A_m:\exists x,v,y\in\mathcal T\quad
                     y\ne T_j\ \land\ \Delta(j,x,v,y)\},\\
S_i&=\{j\in A_m:\exists y\in\mathcal T\quad C_i(j,y)\}
\quad(i=0,1).
\end{aligned}
\tag{CRE.18}
$$

These are the entire rank projections of $D,D_i$, respectively. A subset
$S\subseteq\mathbb N$ is unbounded when
$\forall b\in\mathbb N\ \exists j\in S\ (j>b)$.

**Theorem 4.2 (terminating exact support construction).** From every
recognized finite input one can compute Presburger formulas for all three
supports in (CRE.18), decide designated-row attainment and unboundedness,
extract arbitrarily large feasible ranks when unbounded, and extract a
finite upper bound when bounded. No rank truncation is an input hypothesis.

**Proof.** Put $n=j-2\in\mathbb N$. Every atomic occurrence is
$T_{n+c}$ with $c\ge2$; further fixed transforms only increase $c$.
For finite $m$, the rank condition is $n\le m-2$; otherwise it is true.
The substitution defining $\Delta_i$ distributes fixed powers through
pairs and finite grounds. Each $C_i$ is therefore a finite conjunction of
whole native negatives in URR Definition 1.2's grammar, with one shared
natural coordinate and one shared residual. The predicate for $S_D$ has
the same grammar with three residual names. Theorems 3.1 and 3.3 prove
their full Cartesian domains before negatives. There are no remaining
positive residual equations or hidden image, shape or reach restrictions.

Apply [URR, Theorem 3.1 and Corollary 3.2][URR] to each entire list.
Their simultaneous separator and atomic equality analysis produce exact
Presburger support, conjoined with the displayed rank condition. In
particular all additional negatives are included, even if they make a
support empty or bounded. The admitted support is not guessed from the
base example. Presburger decision tests emptiness and
$\forall b\ \exists j\ (j>b\land j\in S_i)$.
For an unbounded support, the query $j\in S_i\land j\ge b$ returns a
rank for every supplied $b$. For a bounded support, the true existential
formula $\exists M\ \forall j\in S_i\ (j\le M)$ returns a bound.
Under the attained-row premise both supports are nonempty, so a bound
can be taken at least two. Empty support instead detects a failed
designated-row attainment premise.

This use of NIC's normalization has its actual scope. [NIC, Theorems
3.2–3.3 and Proposition 3.5][NIC] prove that their own produced positive
pieces have full Cartesian residuals, reconstruct the same entire
declared tuple, and retain negatives after native expansion. Their
minimum-potential residual-block reconstruction and omission of ambient
normality restrictions supply that product in both directions; ambient
code inequality is not a native sign. The explicit correspondence here
is a direct such mixed description. SLP's restriction on arbitrary
secondary representations does not remove NIC's producer guarantee.

URR's separator is a section of the entire rank projection, not equality
of that section with the whole source image. We use it here only to
compute (CRE.18) and establish finite feasibility at fixed ranks. The
full source and stratum domains remain (CRE.12) and (CRE.17). $\square$

## 5. Completed equations synthesized from the acquired relations

**Definition 5.1 (native completion).** Let $\widehat{\mathcal T}$ be all
valid finite or infinite ordered trees over the same native signature.
Every branch has two children and leaves have none. Extend $\rho$ by its
actual leaf replacements and pairing law. For $X\subseteq\mathcal T$,
$\xi\in\overline X$ means every finite inclusive prefix of $\xi$ is
realized by a member of $X$. This makes no negative or finite-partition
assertion at a limit. Let $\Omega$ be the all-branch tree.

Use the prefix locality from [SPC, §4][SPC] and
[NativeDepthPatterns, `original_prefix_locality`][DEPTH]: $\rho$ is
nonexpanding in prefix distance. Write $\delta(s,t)$ for the least depth
of a reply discrepancy, or $\infty$ if there is none. Thus
$s\equiv_h t$ means $\delta(s,t)>h$. Pairing adds one level to a child
discrepancy. These facts also hold in the completion, since original
branches persist and each reply depends only on a finite original prefix.

**Theorem 5.2 (both completed directions and the unique synthesized point).**
Every common point of $\overline{D_0}\cap\overline{D_1}$ is

$$
\Lambda=W(\Omega,K,K,K,K,K),\qquad
K=\langle\alpha,\langle\Omega,\rho K\rangle\rangle.
\tag{CRE.19}
$$

The unsigned completed equations inherited from the acquired positives and
both complete-row equality patterns reduce, in both directions, to

$$
a=\rho a,\qquad y=\langle\alpha,\langle a,\rho y\rangle\rangle.
\tag{CRE.20}
$$

They have exactly the one solution $(a,y)=(\Omega,K)$, and every requested
finite prefix of this solution is computable. No finite tree is a solution
of (CRE.20). This conclusion alone does not assert that $\Lambda$ is a
signed contact for a bounded or infeasible support.
When $m<\infty$, $\Lambda$ replies branch at $q_aL^m$, so the retained
absent literal itself excludes that point; its exact finite-source rank
barrier remains (CRE.14).

**Proof.** A common closure point keeps the five-pair outer spine. Name its
six subtrees $a,x,v,y,z,w$. Whole equality is closed: a discrepancy occurs
at a finite address and prevents all sufficiently close equal approximants.
The graphs of $F,G$ are closed by prefix continuity. Thus (CRE.9),
Theorem 3.3 and both row patterns give

$$
z=F_a(y),\quad w=G_a(y),\quad x=v=y,\quad x=z,\quad v=w.
\tag{CRE.21}
$$

Consequently $y=F_a(y)=G_a(y)$. Cancel the ordered pairs of the last
equality, including the common $\alpha$ child: its inner left comparison
is $a=\rho a$. The equality $y=F_a(y)$ supplies the second equation
of (CRE.20). Conversely (CRE.20) implies $F_a(y)=G_a(y)=y$;
putting $x=v=z=w=y$ proves every equation in (CRE.21), and reconstructs
the whole completed source. It also satisfies the completed positive
feedback record (CRE.13): an all-branch $a$ has left subtree itself.
Thus no completed source comparison has been silently projected away.

To classify $a=\rho a$, suppose $a$ has a leaf and let $d$ be its
minimum leaf depth. Under $\rho^2$, either leaf label is replaced by a
tree with minimum leaf depth one, while every original branch persists.
Hence the new minimum leaf depth is at least $d+1$. But
$a=\rho a$ implies $a=\rho^2a$, a contradiction. A tree with no finite
leaf address is exactly $\Omega$, and $\rho\Omega=\Omega$.
This excludes finite fixed points without using the finite clock on an
infinite tree or treating $\rho$ itself as a strict contraction.

With $a=\Omega$ define
$\Phi(t)=\langle\alpha,\langle\Omega,\rho t\rangle\rangle$.
The recursive occurrence is below two actual pair nodes. Prefix locality gives

$$
\delta(\Phi(s),\Phi(t))\ge\delta(s,t)+2.
\tag{CRE.22}
$$

Use the guarded prefix argument already employed in SPC Theorem 4.2 and
FJC Theorem 3.1. Here its two-level estimate is explicit: consecutive
iterates $\Phi^r(\alpha),\Phi^{r+1}(\alpha)$ differ no earlier than
depth $2r$. Every finite reply therefore stabilizes, yielding a valid
native completion $K$. Validity of the stabilized replies follows from
the finite conditions that both children of a branch are present and
descendants of a leaf are absent. Continuity gives $\Phi(K)=K$.
If $K,K'$ are fixed points, iterating (CRE.22) gives
$\delta(K,K')\ge2r$ for every $r$, so they coincide.
In particular

$$
p_h(K)=p_h(\Phi^{h+1}(\alpha)).
\tag{CRE.23}
$$

The right side has a terminating finite-prefix evaluation: its recursion
is iterated finitely many times, $\Omega$ answers branch at every word,
and each fixed native transform uses only the requested original prefix.
Thus (CRE.19) is synthesized from the acquired equations, not supplied
as a productive certificate. Its $K$ is infinite since $K|_{RR}=\rho K$
and the repeated $RR$ path never ends. The reduction gives no finite
solution. The pair guards, not bare $\rho$, supply the contraction.
$\square$

## 6. Forced rank escape and the complete signed alternative

**Theorem 6.1 (every deep joint witness escapes both rank bounds).** For
every $M\ge2$ and any legal $\Theta_0(j_0,y_0)\in D_0$,
$\Theta_1(j_1,y_1)\in D_1$,

$$
\Theta_0(j_0,y_0)\equiv_{M+4}\Theta_1(j_1,y_1)
\quad\Longrightarrow\quad j_0>M\ \land\ j_1>M.
\tag{CRE.24}
$$

This holds with completely unrestricted finite residual choices before
their negatives. It concerns every witness, not a chosen witness sequence.

**Proof.** Write $H=M+4$. The addresses $q_x,q_v$ have lengths two and
three. Agreement through $H$ gives

$$
y_0\equiv_{H-2}F_{T_{j_1}}(y_1),\qquad
y_0\equiv_{H-3}G_{T_{j_1}}(y_1).
\tag{CRE.25}
$$

Restriction and transitivity give $F_{T_{j_1}}(y_1)\equiv_{H-3}
G_{T_{j_1}}(y_1)$. Their inner left address is $RL$, of length two;
its two whole values are $T_{j_1},T_{j_1+1}$. Hence

$$
T_{j_1}\equiv_{H-5}T_{j_1+1}.
\tag{CRE.26}
$$

At $L^{j_1-1}$ these atoms reply $\beta$ and branch respectively.
If $j_1\le M$, that word has length at most
$M-1=H-5$, contradicting (CRE.26). Thus $j_1>M$.

If instead $j_0\le M$, the length-one address $q_a$ gives
$T_{j_0}\equiv_{H-1}T_{j_1}$. The height of $T_j$ is $j-1$ for
$j\ge1$, by the atomic recurrence. A finite tree is determined by an
inclusive prefix containing all its leaves: the observed leaf labels
forbid further branches, including all absent descendants. Since
$H-1=M+3>j_0-1$, this agreement forces $T_{j_1}=T_{j_0}$.
Rank injectivity gives $j_1=j_0\le M$, the contradiction already obtained.
All comparisons use only the actual original addresses and shared
coordinates. Neither a residual bound nor any sign at a limit is used.
$\square$

**Theorem 6.2 (automatic complete contact/support alternative).** On every
recognized input with both designated full rows attained,

$$
\boxed{\quad\forall h\in\mathbb N\ J(h)
       \quad\Longleftrightarrow\quad S_0,S_1\text{ are both unbounded}.\quad}
\tag{CRE.27}
$$

The choice terminates from the acquired input. If either support is bounded
by $M\ge2$, it returns the finite exclusion depth $H=M+4$.
If both are unbounded, for every requested $h$ it constructs actual finite
sources in both entire strata sharing $p_h(\Lambda)$. Moreover

$$
\overline{D_0}\cap\overline{D_1}=
\begin{cases}
\{\Lambda\},&S_0,S_1\text{ both unbounded},\\
\varnothing,&\text{otherwise}.
\end{cases}
\tag{CRE.28}
$$

**Proof.** Theorem 4.2 computes both complete supports and decides their
unboundedness. If one is bounded by $M$, all sources in that stratum
have rank at most $M$, by both directions of (CRE.17) and (CRE.18).
Theorem 6.1 excludes every depth-$M+4$ joint witness. This proves
necessity in (CRE.27) and the quantitative NO branch. A common closure
point at that depth would supply one approximant from each stratum
with its same prefix, contradicting exclusion. An empty designated
support is detected as failure of the attainment premise; without that
premise it also gives $\neg J(0)$.

Suppose both supports are unbounded. For supplied $h$, compute $p_h(K)$
using (CRE.23). Independently extract

$$
j_i\in S_i,\qquad j_i\ge2h+4\quad(i=0,1).
\tag{CRE.29}
$$

Fix each chosen $j_i$ before constructing its residual. Its support
membership means the entire conjunction $C_i(j_i,y)$ has a finite witness.
Apply [SLP, Lemma 2.1][SLP] at this same fixed rank, with its one unfixed
residual prescribed to have the inclusive prefix $p_h(K)$. The lemma
applies because $K$ is infinite and Theorem 3.3 proves the full product
before the finite negative list. It supplies one finite $y_i$ satisfying
all of $C_i(j_i,y_i)$ together, with $y_i\equiv_h K$. At fixed rank
all atomic terms are finite grounds. Every repeated $y$ uses that same
prefix context and frontier filling, so all signs and shared occurrences
survive simultaneously. This uses local signed lifting after contact
synthesis, not a claim that SLP synthesizes an unknown contact.

[NLC, Lemma 3.1][NLC] gives the exact native minimum leaf depth
$\mu(T_j)=\lfloor j/2\rfloor$. Therefore (CRE.29) makes
$T_{j_i},T_{j_i+1}$ agree through $h$ with $\Omega$.
Continuity with the explicit prefix-locality bound gives

$$
F_{T_{j_i}}(y_i)\equiv_h F_\Omega(K)=K,\qquad
G_{T_{j_i}}(y_i)\equiv_h G_\Omega(K)=K.
\tag{CRE.30}
$$

Filling the finite outer spine shows
$\Theta_i(j_i,y_i)\equiv_h\Lambda$. Theorem 3.3 puts these finite
sources in the exact $D_i$, and Theorem 3.1 makes them satisfy the
entire acquired input with all guards at their recorded epochs.
This is one common original prefix, rather than independently selected
hole marginals. Each candidate internally uses its own single rank
$j_i$ and its own single $y_i$. The two alternative originals need
not have equal ranks or residuals.

Every construction terminates for its supplied finite $h$: Presburger
witness extraction, the computed contact prefix, and SLP's finite
simultaneous separator construction. No upper bound on expanded source
size is claimed. These constructions prove sufficiency in (CRE.27)
and place $\Lambda$ in both closures. Theorem 5.2 proves that it is
their only possible common point. Together with the bounded case this
gives (CRE.28). A limit need not satisfy $y\ne T_j$ or an additional
negative, and no finite partition is assigned to $\Lambda$. $\square$

## 7. Substantive coupling, native non-rationality and actual recovery

**Theorem 7.1 (non-rational contact and bounded-rank method obstruction).**
When both supports are unbounded, $K$ and $\Lambda$ are non-rational in
the expanded native signature: they have infinitely many distinct whole
subtrees. No method limited to rational native common closure points can
witness this pair. Replacing either whole designated stratum by sources
with a fixed rank bound loses all-depth contact even if every finite
residual tree at those ranks remains available.

**Proof.** Distribution through the two pairs in (CRE.19) gives for
every $q\ge0$

$$
K|_{(RR)^q}=\rho^q K,\qquad
K|_{(RR)^qL}=\rho^q\alpha=T_q.
\tag{CRE.31}
$$

All these addresses are reached, as follows inductively from the
preserved pairs. The finite atomic subtrees are pairwise distinct by
the supplied clock $\kappa(T_q)=q$. Thus $K$ has infinitely many
different subtrees, and so does any source containing it, including
$\Lambda$. This is the subtree discrimination used in SPC Theorem
4.2, here applied to the contact whose side coordinate is forced to
$\Omega$. The finite guarded interpreted description (CRE.19) is
compatible with this native non-rationality; it is not a rational-tree
description in the expanded signature.

By (CRE.28) a common closure point would have to be this non-rational
$\Lambda$, proving the stated restriction on rational-contact methods.
For any bounded-rank replacement, choose its bound $M\ge2$.
Theorem 6.1 excludes contact at $M+4$ independently of every residual
choice. This supplies the precise failed quantifier exchange: arbitrary
residual freedom at finitely selected ranks cannot replace
$\forall h\ \exists(j_0,j_1,y_0,y_1)$ over the whole feasible supports.
The same $a$ occurs inside both feedback expressions, and their overlap
forces $a=\rho a$. Rank escape is therefore coupled to the residual
equation rather than appended beside an unrelated residual. $\square$

**Theorem 7.2 (attained YES and NO families, with unrestricted residual size).**
With no additional negatives and no ceiling, both rows are attained at
every $j\ge2$, both supports equal $\{j:j\ge2\}$, and the pair has
all-depth contact. With no additional negatives and any finite $m\ge2$,
both rows remain attained and their pair is excluded at $m+4$.
For every recognized input and every fixed feasible rank in either
designated stratum, its legal residuals and whole sources have unbounded
native constructor mass.

**Proof.** In the unextended cases, $y=\alpha$ satisfies $y\ne T_j$
for every $j\ge2$. Theorem 3.3 proves both exact full labels, so the
support descriptions follow, including the finite ceiling case. Theorem
6.2 supplies YES and NO respectively.

For an explicit finite joint sequence in the unbounded base family, put

$$
a_h=T_{2h+4},\qquad c=\langle\alpha,\alpha\rangle,\qquad
y_h=F_{a_h}^{\,h+1}(c),\qquad
u_i(h)=\Theta_i(2h+4,y_h).
\tag{CRE.32}
$$

The outer left child of $y_h$ is $\alpha$, so $y_h\ne a_h$.
The two-pair guard gives
$\delta(F_a(s),F_a(t))\ge\delta(s,t)+2$ for fixed $a$.
Hence $y_h\equiv_h F_{a_h}(y_h)$ by iterating this estimate from
the pair $c,F_{a_h}(c)$. The exact minimum leaf depths of
$a_h,\rho a_h$ exceed $h$, so they agree through $h$; therefore
$F_{a_h}(y_h)\equiv_h G_{a_h}(y_h)$. The sources in (CRE.32)
differ only at the $x,v$ holes and agree through $h$. Theorem 3.3
proves every finite partition bit. This sequence illustrates the
unextended case; Theorem 6.2 covers the entire extended family rather
than reducing it to this section.

For the final assertion fix $j\in S_i$ and use the constructor mass
$\gamma$ supplied by [URR, Definition 2.1][URR], via ABC's normal
atomic code. It satisfies $\gamma(T_j)=0$,
$\gamma(\rho t)=\gamma(t)$, and a pair with a positive-mass child
has mass $1$ plus its children's masses. Prescribe longer and longer
prefixes of the infinite comb $Z=\langle\alpha,Z\rangle$ for the
one residual at this same fixed rank. SLP Lemma 2.1 supplies a finite
legal residual for every such prefix, satisfying the entire $C_i$.
A prefix through depth $d$ retains $d$ pairs of the form
$\langle\alpha,t\rangle$ along its right spine. None is an atomic
collapse: its left primitive rank is zero, whereas collapse requires
the left rank to exceed the right rank by one. Each contributes one
to $\gamma$, so the residual masses are unbounded.

For $\gamma(y)=b\ge1$, the positive-child formula, with all occurrences
counted, gives

$$
\begin{aligned}
\gamma(F_{T_j}(y))&=\gamma(G_{T_j}(y))=b+2,\\
\gamma(\Theta_0(j,y))&=5b+9,\qquad
\gamma(\Theta_1(j,y))=5b+13.
\end{aligned}
\tag{CRE.33}
$$

Thus neither whole stratum has bounded mass. This does not justify
erasing its constrained interior atomic rank: Theorem 6.1 still applies
to every witness. We make no additional assertion that an arbitrary
alternative finite rank-free cover cannot exist; FJC Theorem 7.1
retains ownership of its atomic-tail cover obstruction. $\square$

**Theorem 7.3 (lawful consumer and the all-pair boundary).** Under
Assumption 1.3, a YES answer in Theorem 6.2 excludes a uniform finite
new-read static or lawful serial forward service for the entire $R_Q$
on the entire $D$. A NO answer excludes only this designated pair.
The full row image of this family is finite. If every distinct pair in
that entire attained image has a finite exclusion depth, their maximum
$H$ yields a correct static current-epoch service with

$$
q\le2(2^{H+1}-1),\qquad a=0,\qquad
\ell\le2(2^{H+1}-1)(H+\lceil N/2\rceil),
\tag{CRE.34}
$$

where $q$ counts new reads, $a$ new updates and $\ell$ total submitted
literal-word length. Independently, every actual source permits
sourcewise finite recovery by paid traversal of the finite current
tree followed by local inverse reconstruction.

**Proof.** Use the unchanged actual service/prefix existence bridge
[ARH, (ARH.2.3)][ARH], also used by FJC §5. A controller with a uniform
finite number of four-valued reads has a finite reply tree after its
deterministic intervening computation/update segments are compressed.
The submitted physical addresses have a finite maximum original
dependency depth, by native prefix locality at every actual epoch,
including born and absent cases. Two sources from different complete
rows sharing that original prefix defeat the service. Theorem 6.2
supplies them for every depth. Real forward updates add no new port
and do not avoid this obstruction.

Every source in (CRE.12) has the same exterior and reached six-hole
set. Only its finite equality partition can vary, so its full row
image is finite. Its exact distinct attained list and original
realizers can be obtained by [NPL, Theorem 5.3][NPL], or by NSF
Theorem 5.2's full-row feasibility query for every partition of those
six holes. Other attained labels must be included. If each distinct
pair has an exclusion depth, take their finite maximum $H$ (and take
$H=0$ for a singleton image). Different rows on a common $H$-prefix
would contradict their pair exclusion. Thus this prefix determines
the entire row. An exclusion of $\{r_0,r_1\}$ alone supplies no such
conclusion about other pairs.

Apply the actual epoch-$N$ decoder of [ARH, §2][ARH] and
[DelayedOriginalReadout, `original_decoder_correct` and
`original_decoder_service`][DECODER] at every original word of length
at most $H$. It uses at most two paid current-register reads per word,
with length at most $H+\lceil N/2\rceil$, including original absence.
There are $2^{H+1}-1$ words, proving (CRE.34). A compatible finite
source can then be found by NSF or local finite enumeration. The
actual source ensures compatibility; prefix determination makes the
output row correct without identifying that witness with the actual
source. No post-entry update is required.

For sourcewise recovery, traverse the actual finite $\rho^N u$ using
paid branch-guided reads. Its complete acquired description has the
unique finite image inverse supplied by ARH Lemma 19.2 and ABC
Theorem 2.3. Apply that inverse $N$ times as local computation on
the description to recover $u$ and hence $R_Q(u)$. This is not inverse
execution on the register. The traversal uses
$|\operatorname{Pos}(\rho^N u)|$ new calls and their actual total
word length, with storage and inverse work charged separately. There
is no uniform bound on these quantities here.

Pre-cut acquisition remains the paid sourcewise procedure of Theorem
3.1. For a nonsharing acquisition its raw charge is the ARH bound

$$
|\operatorname{Pos}(u)|+|H_0|
 +\sum_{(e,p)\in E}|\operatorname{Pos}((\rho^e u)|_p)|,
\tag{CRE.35}
$$

with endpoint occurrences $E$ retaining repetitions and their root
reads included. Literal-word lengths, actual updates to $N$, finite
comparison work, descriptions, certification and the complete cut
have separate costs. The offline support computation, synthesized
completion and signed finite realizers are common mathematical
preparation, not runtime evidence about the actual source. Local
computation, table installation, memory, retention and entry are not
bounded or refunded by (CRE.34)–(CRE.35). $\square$

## 8. Mathematical ownership, literature and the remaining relation

**Definition 8.1 (attribution and transfer boundaries).** The new
repository-derived content is the whole acquired family (CRE.12), its
complete designated strata, the forced escape of both ranks at $M+4$,
and the terminating exact signed support/contact alternative (CRE.27).
The non-rational point is derived from that acquired coupling, with
actual signed finite realizers. It is not a new general density,
centralizer, guarded-recursion, rank-support or service theorem.

The following sources specify the reused mathematical interfaces.

| Source | Exact content used and boundary |
| --- | --- |
| [ARH, §§1–4, Theorem 4.2, Lemma 19.2 and Application 26.1][ARH] | `repo-derived`: full signed fiber, both reached guards, paid actual producer, finite inverse/clock, localized finite feedback classification and actual static/serial bridge. They do not supply arbitrary all-depth contact synthesis. |
| [ABC, Theorems 2.2–2.3][ABC]; [NLC, Lemma 3.1][NLC] | `repo-derived`: normal atomic coding, native rank translation and finite image inverse; exact minimum leaf depth $\lfloor j/2\rfloor$. Native pairing and reached leaves remain distinct from code nodes. |
| [NIC, Theorems 3.2–3.3, Proposition 3.5 and Theorem 4.3][NIC] | `repo-derived`: exact whole-tuple/source correspondence, Cartesian positive domains from the actual normalizer, and native signed pullback. A rank section is not a whole-image replacement. |
| [URR, Theorem 3.1 and Corollary 3.2][URR] | `repo-derived`: simultaneous finite residual separation and exact entire Presburger support on full Cartesian mixed domains. No prescribed-prefix or unknown-contact synthesis is inferred from its section. |
| [SLP, Lemma 2.1][SLP] | `repo-derived`: simultaneous finite signed lifting of prescribed infinite-coordinate prefixes at a fixed feasible rank, with shared occurrences. It is invoked only after rank choice and contact synthesis. |
| [SPC, Theorem 4.2][SPC]; [FJC, Theorems 3.1, 5.1, 7.1 and §6][FJC] | `repo-derived`: guarded prefix solution method, native non-rational subtree argument, source-faithful coupled outputs and the existing rank-free cover boundary. Neither supplied productive certificates nor a supplied functional presentation is an arbitrary-input synthesis theorem. |
| [NSF, Theorem 5.2][NSF]; [NPL, Theorem 5.3][NPL] | `repo-derived`: finite signed source queries and exact full row image with original witnesses. They preserve the whole domain and do not decide every all-depth pair. |
| [SJM, Theorems 2.2, 3.2 and Open problem 6.2][SJM] | `repo-derived`: all-set closure multiplicity and complete-field memory distinction. A persistent pair is a lower obstruction; deciding this pair does not determine every row-set multiplicity or the minimum complete field. |
| [NativeCutFibers][CUT], `rowFiberEquiv`, `legal_values_row`; private `recover_fill`, `fill_injective` | Exact finite old-row correspondence with shared class values and all class inequalities. A source-coordinate inverse is not an observer port. |
| [NativeHistoryCells][CELLS], `historyCellEquiv`, `cell_feasibility_exact`; private `sourceCell_right`, `cellSource_injective` | Entire finite literal-history cells and reconstruction of the same source. These statements are not an unrestricted signed all-depth solver. |
| [NativeDepthPatterns][DEPTH], `original_prefix_locality`, `depthEquiv`; private `fill_decompose`, `decompose_fill` | Finite prefix locality and full frontier/source correspondence. Reading a textual declaration does not supply new compiled evidence. |
| [NativeGroundSeparation][NGS], `simultaneous_ground_separation`; private `count_length`, `evaluated_length`, `compound_mass_ne` | Existing finite free-magma separator method with fixed term bounds, reused by URR. Native rank-uniform separation has its own stated mass/clock hypotheses. |
| [DelayedOriginalReadout][DECODER], `original_decoder_correct`, `original_decoder_service`; private `original_query_bounds` | Actual same-root epoch-$N$ decoder, absent guards and its two-read/word-length bound. No old-version read or source equality port. |
| [SourceTransportCentralizer, `source_transport_centralizer`][CENTRALIZER] | The finite ordered-source stability classification, injectivity and image-only inverse underlying ARH. It does not classify arbitrary infinite interpreted equations. |

**Definition 8.2 (primary mathematical reference frame).** The guarded
prefix construction uses mature fixed-point reasoning. [Milius–Moss,
*The Category Theoretic Solution of Recursive Program Schemes*,
arXiv:0904.2385v2, Theorem 7.5 and §7.3 Theorem 7.15][MM] is
`literature-attested` background: a guarded recursive program scheme
has an interpreted solution in an Elgot algebra, unique in a completely
iterative algebra; its contracting-functor/nonempty complete-metric
setting identifies that solution with the unique fixed point of its
specified operator. Here (CRE.22) proves the required prefix gain
directly. Those theorems do not convert arbitrary overlapping native
equations into lawful guarded presentations, preserve finite signs at
a completion, or make finite native trees a complete metric space.

[Comon–Lescanne, *Equational Problems and Disunification*, Journal of
Symbolic Computation 7 (1989), 371–425, §3.2 Lemma 1, Appendix B.3
and §6.2][CL] is `literature-attested` free-term background. Its
nontrivial syntactic disequation argument uses infinite sort carriers
and the finite/at-most-one one-variable exclusion property in its free
or rational-tree setting. Section 6.2 explicitly excludes general
nontrivial equational theories from those completeness results.
Interpreted $\rho$ with its native leaf laws is not a free unary
constructor. Neither that result nor a rational-native-contact-only
method supplies the required native synthesis here; Theorem 7.1
gives the latter method's exact obstruction. No faithful transfer of
rigid E-unification, tree-transducer or regular-substitution decision
results to this full acquired relation is assumed. Unchecked or
inaccessible unused leads yield no novelty or undecidability conclusion.

The statements of this volume are `repo-derived` ordinary consequences
of the specified native contracts. No external priority or literature-wide
originality is asserted.

**开放问题 8.3 (general mixed contact synthesis).** For arbitrary complete
acquired inputs and finite sets of distinct attained complete rows,
terminate with either a finite joint exclusion depth or actual finite
signed sources at every depth. Preserve every positive condition,
both signed guards, shared rank and residual incidences, the old row
and every complete target label in both source directions. In
particular, general correlated multiple-rank and nonfunctional overlaps,
unknown finite residual barriers and image restrictions are not treated
by the recognizer of §2. Recognition failure leaves that instance
unresolved, not NO and not a proof of undecidability.

The criterion (CRE.27) closes the designated pair on the entire
recognized family. Its sufficiency depends on the specifically derived
unique infinite contact and its necessity on the coupled rank escape;
scalar supports alone are not a general substitute for the full joint
source maps. For whole-row recovery every actual distinct row pair
must be covered as in Theorem 7.3. For optimal complete retained fields,
the all-set obligation of SJM remains. These are finite-family
recovery conditions within the native relation model, not a theorem
recovering physical space, time, boundary or memory in general.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md
[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[FJC]: RECURSIVE_RELATIONAL_OBSERVATION_FUNCTIONAL_JOINT_CONTACT.md
[SJM]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_JOINT_MEMORY.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[CUT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[CELLS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[NGS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.lean
[DECODER]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[CENTRALIZER]: ../../../D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[MM]: https://arxiv.org/pdf/0904.2385v2
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf

## 追加锚（本行以下为增补区）
