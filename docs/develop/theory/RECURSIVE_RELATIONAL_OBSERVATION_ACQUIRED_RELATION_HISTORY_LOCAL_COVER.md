# Acquired local atomic covers and complete-row recovery

**Definition 33.0 (source and cross-volume conventions).** The source trees, substitution, acquired input, entire source fiber and complete original-row target are those of [Acquired Relation History](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md), Definitions 1.1–1.2 and Assumption 1.3. References to its items 1–26 and equations with prefix ARH retain that meaning; items 33–37 and equations with prefix LAC are local to this continuation. The normal-code, atomic-orbit and term-power suppliers are the references specified in Definition 37.1.
## 33. An acquired local atomic cover

**Definition 33.1 (local certificates on the complete old row).** Keep
Definitions 1.1–1.2 and Assumption 1.3, with arbitrary finite prefix-free
$P,Q$. In particular $U$ is the entire fiber (ARH.1.4), the target is the
entire original $R_Q$, and the only source actions after the authentic
entry epoch $N$ are original-root $\mathsf{Read}$, forward
$\mathsf{ApplyRho}$ and absorbing $\mathsf{Halt}$. Every literal, both
guards of every signed record, the concrete old exterior, repeated old
classes and all different-class inequalities remain imposed.

Write $I_P$ for the reached old addresses specified by $R=(C,\pi)$, and
$\mathcal B$ for its equality classes. A *local atomic cover* consists,
for each $b\in\mathcal B$, of an occurrence $a_b\in I_P$ of that class
and a positive record actually present in $H_{\rm rel}$ of the form

$$
e_b=(n_b,a_b,m_b,a_bs_b,=),\qquad s_b\ne\varepsilon,
\tag{LAC.33.1}
$$

allowing its two endpoints to be exchanged. Finding such a cover is a
finite syntactic test on the retained records and old occurrence list.
The rest of the history is unrestricted. Failure to find a cover means
*outside this recognizer*, never a negative recovery answer on the
unrestricted fiber. For $\mathcal B=\varnothing$ the cover is empty and
the original source, if consistent with the records, is the concrete $C$.

For logical consistency questions allow $U=\varnothing$ while retaining
a well-formed complete old row. Such an input has no actual acquired
entry satisfying Assumption 1.3; it will be reported separately from a
nonempty fiber with no uniform recovery service.

**Proposition 33.2 (atomicity is forced at each original occurrence).**
If a covered input has a source, every designated record satisfies

$$
m_b=n_b+w(s_b),\qquad
(u|_{a_b})=T_{k_b},\qquad k_b\ge\epsilon_b,
\quad
\epsilon_b=
\begin{cases}
1,&n_b=0\text{ and }s_b\text{ ends in }L,\\
0,&\text{otherwise}.
\end{cases}
\tag{LAC.33.2}
$$

The index $k_b$ is unique and is shared by every occurrence of class $b$.
Different old classes have different indices. If $\mathcal B$ is nonempty,
every authentic entry has $N\ge1$. An incompatible epoch equation in
(LAC.33.2) implies an empty fiber, not an additional source promise.

Proof. Put $z=u|_{a_b}$. This original subtree exists by the complete
old row. Original-address transport gives
$(\rho^n u)|_{a_b}=\rho^n z$ for every $n\ge0$. In particular $a_b$
persists at both recorded epochs, and the descendant endpoint exists
exactly when $s_b$ exists in $\rho^{m_b}z$. The whole guarded predicate
of (LAC.33.1) is therefore

$$
s_b\in\operatorname{Pos}(\rho^{m_b}z)\quad\land\quad
\rho^{n_b}z=(\rho^{m_b}z)|_{s_b}.
\tag{LAC.33.3}
$$

Apply Theorem 4.2 to this actual finite subtree. Its full classification,
including its last-edge reach condition, is exactly (LAC.33.2).
The old partition identifies the whole original subtrees at repeated
occurrences; injectivity of $k\mapsto T_k$ transfers that identity to
indices. The old different-class disequalities give $k_b\ne k_c$ for
$b\ne c$, including classes absent from the task. Finally
$m_b=n_b+w(s_b)\ge1$, and the authentic $N$ dominates $m_b$.
This is a mathematical application at an original subtree, not a physical
reroot or an acquisition of its index. $\square$

## 34. One joint arithmetic domain and the complete target

**Theorem 34.1 (whole-source and whole-row interpretation).** On a covered
input one can construct Presburger predicates $\mathsf{Adm}(k)$ and
$\mathsf{Same}_Q(k,l)$, for $k,l\in\mathbb N^{\mathcal B}$, such that

$$
\begin{gathered}
U_k=C[(T_{k_{[i]}})_i],\qquad
S=\{k\in\mathbb N^{\mathcal B}:\mathsf{Adm}(k)\},\\
k\longmapsto U_k\text{ is a bijection }S\longrightarrow U,\\
\mathsf{Same}_Q(k,l)\quad\Longleftrightarrow\quad
R_Q(U_k)=R_Q(U_l).
\tag{LAC.34.1}
\end{gathered}
$$

The last equivalence holds for all nonnegative tuples, hence in particular
for all admitted tuples. The target equality compares the entire concrete
exterior, the reached original addresses and every whole-subtree equality
in their partition. The construction does not require a bound on ranks,
expanded source size or concrete target exterior. It imposes all retained
constraints on one tuple; it makes no replacement by independent margins.

Proof. Use the native normal codes, join $J$, translation $\tau_n$,
guarded navigation $\nu_p$ and literal map $\lambda$ of
[ABC, Definitions 2.1 and 3.1, Theorems 2.2–3.2][LAC-ABC]. The following
finite symbolic construction checks their precise arithmetic interface
for the fixed acquired context.

A guarded symbolic code is a finite ordered $F$-shape with primitives
$[f(k)]$, where $f$ is an integer-affine expression and its Presburger
guard entails $f(k)\ge0$ and native normality of the code. Integer-affine
notation is only shorthand for arithmetic over $\mathbb N$: move negative
coefficients and constants across each equality or inequality. A family
of such guarded codes has finitely many branches. Its branches are
mathematical cases in a formula, not accessible chart labels.

Start with $[k_b]$ at each hole of class $b$, $[0]$ at each concrete
$\alpha$ and $[1]$ at each concrete $\beta$. Recursively combine the two
already normal child families at every pairing node of $C$. On a branch
where both children are primitive, $[f]$ and $[g]$, split on $f=g+1$:
the true branch returns $[g+2]$ and the false branch returns
$F([f],[g])$. If either child has an $F$ head, retain their $F$ pair.
These are precisely the cases of native $J$. The two guards partition
the existing branch; false guards may be kept or discarded. Structural
induction on the finite $C$ proves that the resulting guarded family
$X(k)$ evaluates to the canonical code $B(U_k)$ for every tuple.

Every internal join is processed after its children, so a collapse can
propagate through arbitrarily many levels of this fixed context.
It may join blocks from distinct old classes. Such a join does not erase
the physical old occurrence: expansion still has the same native pair
and the same reached original address. In particular the pair expression
$F([1],[0])$ must normalize to $[2]$ before native equality is tested;
their expansions are the same $T_2$.

For a fixed epoch $n$, translation replaces each $[f]$ by $[f+n]$ and
preserves $F$, by ABC Theorem 2.3. For one child step, an $F$ node returns
the designated child; at $[f]$ split into $f=0$, $f=1$ and $f\ge2$.
The first two cases return absence, while the third returns $[f-1]$ for
$L$ or $[f-2]$ for $R$. Absence is absorbing. Iterate for the finitely
many letters of the specified word. At the resulting code the literal
cases are $[0]$, $[1]$, a primitive of rank at least two, an $F$ head,
or absence. These cases give respectively $\alpha$, $\beta$,
$\mathsf{branch}$, $\mathsf{branch}$ and $\mathsf{absent}$.

Thus, for every fixed endpoint $(n,p)$, both its existence and its exact
whole-subtree normal code have finite guarded arithmetic descriptions.
The construction checks every intermediate child, not merely the final
rank's nonnegativity. For example, $T_2|_{LL}$ is absent although
$2-w(LL)=0$. A known original exterior leaf may expand before an endpoint
is requested; translation and these same native child rules include its
born addresses without interpreting them as original ones.

To compare two present endpoint codes, refine their finite branch families
together. On each pair of branches, different normal $F$/primitive shapes
give false; equal shapes give the conjunction of the corresponding
primitive-rank equalities. Theorem 2.2 of ABC makes this exactly whole
native-tree equality. Write $G_{n,p}(k)$ for endpoint existence,
$E_{n,p;m,q}(k)$ for this guarded equality test, and
$L_{n,p,c}(k)$ for the exact literal predicate. A signed record contributes

$$
G_{n,p}(k)\land G_{m,q}(k)\land
\begin{cases}
E_{n,p;m,q}(k),&\bowtie\text{ is }=,\\
\neg E_{n,p;m,q}(k),&\bowtie\text{ is }\ne.
\end{cases}
\tag{LAC.34.2}
$$

The guards stay outside the negation. In particular neither missing
endpoint can make a disequality true. Equality of a paired expression
is conjunction of its child equalities; its disequality negates the
whole conjunction, rather than demanding both child disequalities.

Define $\mathsf{Adm}$ as the conjunction of every $k_b\ne k_c$ for
different old classes, every literal predicate $L_{n,p,c}$ in the retained
list, and (LAC.34.2) for every retained signed record. One may also conjoin
the designated compatibility equations and lower bounds (LAC.33.2):
Proposition 33.2 proves them consequences of the predicates already
included. An incompatible designated equation gives the constant false
predicate. Repeated literals and records remain conjuncts.

The complete old row is enforced by the construction of $U_k$, not by
forgetting it. The concrete context $C$ and its reached-hole list are
unchanged, and every repeated class uses the same rank variable. Because
$P$ is prefix-free, an old absent cut cannot lie below a reached old hole.
It is blocked by a concrete strict-prefix leaf in $C$, which filling does
not alter. Thus every filling has exactly the old reached set and exterior.
Index injectivity makes all the stated $k_b\ne k_c$ exactly the remaining
requirements for its complete old partition.

Now take $u\in U$. Proposition 33.2 supplies its unique atomic old-class
values. The original old-row reconstruction (ARH.1.2) gives $u=U_k$.
Its old inequalities and every actual guarded record give
$\mathsf{Adm}(k)$ by the exact endpoint and literal computations.
Conversely take any $k$ satisfying $\mathsf{Adm}$. Its filling is a
nonempty finite native tree, has the complete old row just proved, and
satisfies every literal and both guarded endpoints and sign of every
relation. It therefore lies in the original $U$. Finally, equality
$U_k=U_l$ recovers $T_{k_b}=T_{l_b}$ at $a_b$ for every class and hence
$k=l$. This proves both source inclusions and injectivity without assuming
that old holes are maximal atomic blocks.

For the target, construct the symbolic reached set
$I_Q(k)=\{q\in Q:\nu_q(X(k))\ne\bot\}$. All of its finitely many membership
predicates are already available. Use the native mask of
[ABC, Definition 4.1 and Theorem 4.2][LAC-ABC]: $M_Q(X)$ is the code of
the tree obtained by filling each reached original $Q$ hole with $\alpha$.
For an empty cut trie retain the whole current code. For a root cut
return $[0]$. With only proper cuts, a native leaf remains that leaf;
at a native branch recurse down the two appropriate subtries and rejoin
with $J$. This is a finite recursion on the fixed cut trie. Each child
step uses the guarded rules above and each rejoin the same finite
normalization. Hence $M_Q(X(k))$ also has a finite guarded code family,
even when an uncut part of its expansion has unbounded size.

Use a second tuple $l$ and define

$$
\begin{aligned}
\mathsf{Same}_Q(k,l)\ \Longleftrightarrow\quad& I_Q(k)=I_Q(l),\\
&M_Q(X(k))=M_Q(X(l)),\\
&\bigwedge_{q,r\in I_Q(k)}
 \left(\nu_q(X(k))=\nu_r(X(k))\ \Longleftrightarrow\
       \nu_q(X(l))=\nu_r(X(l))\right).
\end{aligned}
\tag{LAC.34.3}
$$

Every displayed code equality is implemented by the finite normal-shape
comparison, not ambient equality of unnormalized terms. The last line
is a finite conjunction over $Q\times Q$ guarded by membership of both
addresses; the first line then supplies the same guards on the other
tuple. Consequently (LAC.34.3) is a Presburger formula.

For a fixed reached set $I$, filling all numbered holes with $\alpha$
is injective on contexts with holes at precisely $I$: replace the
subtrees at $I$ by their numbered holes to invert it. Prefix-freeness
ensures this replacement cannot conceal another cut. Therefore equal
native masks and equal reached sets mean equal complete concrete
exteriors, even when normalization of a mask collapsed a surrounding
atomic block. The last line compares every pair of whole removed
subtrees, so it is exactly equality of the complete partitions,
including repeated target holes. This is precisely ABC's whole-row
correspondence and proves (LAC.34.1).

All recursions have finite inputs: the known $C$, the finitely many
specified words and epochs, the $Q$ trie, and finite products of their
branch families. Their tests are affine arithmetic and Boolean operations.
No step unfolds an unbounded unknown $T_k$ or enumerates unknown shapes.
No general formula for normality on arbitrary ambient shapes is assumed.
$\square$

## 35. A cofinal cutoff and a terminating recovery decision

**Definition 35.1 (joint clipped-rank agreement).** For $K\in\mathbb N$ put
$\operatorname{clip}_K(k)_b=\min(k_b,K)$, and abbreviate its equality by

$$
\mathsf{Clip}_K(k,l):=
\bigwedge_{b\in\mathcal B}
\bigl[(k_b=l_b\land k_b<K)\ \lor\ (k_b\ge K\land l_b\ge K)\bigr].
\tag{LAC.35.1}
$$

Let $A=\max(\{0\}\cup\{|a_b|:b\in\mathcal B\})$. Use the inclusive
original-prefix convention of Definition 2.2. Both empty tuples agree
under every cutoff. The clipped tuples describe observation classes;
they do not replace the unbounded jointly constrained set $S$.

**Proposition 35.2 (two sufficient cofinal prefix bounds).** For all
nonnegative rank tuples, all $h,K\ge0$, and the same fixed context,

$$
\begin{aligned}
\mathsf{Clip}_{2h+2}(k,l)
&\Longrightarrow
 \forall |p|\le h,\quad r_{U_k}(p)=r_{U_l}(p),\\
\left[\forall |p|\le A+K,\quad r_{U_k}(p)=r_{U_l}(p)\right]
&\Longrightarrow\mathsf{Clip}_K(k,l).
\end{aligned}
\tag{LAC.35.2}
$$

These are sufficient bounds in opposite directions, not assertions of
optimal or exactly matching prefix depths.

Proof. If $j\ge2h+2$, every atomic reply at $|s|\le h$ is branch.
At the root $j\ge2$. For a nonempty $s$, the guard
$j\ge w(s^-)+2$ follows from $w(s^-)+2\le2|s|\le2h$;
the reached rank $j-w(s)$ is at least two. Use (ARH.4.3).
Consequently equal clipped coordinates at $2h+2$ either give identical
whole atomic trees or two trees having the same replies through depth
$h$. A physical word of length at most $h$ in a filling either remains
in the fixed $C$, is blocked there, or enters one of its holes and uses
a suffix of length at most $h$. The replies agree in each case, including
every repeated occurrence. This proves the first line.

For the second line there is nothing to prove at a coordinate whose
two ranks are at least $K$. Otherwise choose the smaller rank $j<K$
at that coordinate. The recurrence gives
$\operatorname{ht}(T_0)=0$ and
$\operatorname{ht}(T_j)=\max(0,j-1)$ for $j\ge1$, so every leaf of
this $T_j$ is at relative depth at most $K$. At the fixed reached $a_b$,
the assumed original-prefix agreement includes all these relative
addresses. Matching all branch and leaf replies of a finite complete
tree forces exactly that tree: recurse through its pairs, and at each
leaf a matching leaf reply forbids any further child. Thus the other
subtree is also $T_j$. Index injectivity gives equality of the ranks.
For $K=0$ there are no small ranks and (LAC.35.1) is vacuous; for no
old classes both conclusions are immediate. $\square$

**Theorem 35.3 (uniform bounded recovery, decided in both directions).**
For a covered input, emptiness of its entire original fiber is decidable.
On a nonempty input satisfying Assumption 1.3, the following are equivalent:

1. A source-total permitted serial service has a uniform finite new-read
   budget for the entire original $R_Q$.
2. Such a static service exists at the authentic $N$.
3. Some finite original prefix determines the entire row on $U$.
4. The following single Presburger sentence is true:

$$
\exists K\in\mathbb N\ \forall k,l\in\mathbb N^{\mathcal B},\quad
\bigl[\mathsf{Adm}(k)\land\mathsf{Adm}(l)\land
       \mathsf{Clip}_K(k,l)\bigr]
\Longrightarrow\mathsf{Same}_Q(k,l).
\tag{LAC.35.3}
$$

There is a terminating yes/no decision of these conditions. A positive
answer supplies $K$, the sufficient original depth $A+K$, and an actual
static service with at most $|\mathcal B|K$ new reads. A negative answer
supplies, for every requested original depth $h$, two finite members of
the original $U$ agreeing through that depth and having unequal complete
$R_Q$ rows.

Proof. Theorem 34.1 makes $\exists k\,\mathsf{Adm}(k)$ a sentence of
Presburger arithmetic over nonnegative integers. Its truth is decidable
by the classical result stated in Ginsburg–Spanier,
[*Semigroups, Presburger Formulas, and Languages*, Theorem 1.2,
printed p. 287][LAC-GS]. The same decision applies to (LAC.35.3), including
its existential cutoff and both universal tuples. Their Theorem 1.3,
printed p. 288, also gives effective semilinear descriptions of these
definable sets; no independent semilinearity assumption on the acquired
input is used. These arithmetic results are suppliers, not new decision
theorems about arithmetic.

Conditions 1–3 are the existing operational correspondence (ARH.2.3).
Its domain hypotheses are exactly the common complete state, finite
literal alphabet, source-total deterministic control and original-address
locality in Assumption 1.3. A uniform read bound gives finitely many
reachable reply prefixes; every intervening computation/update segment
at a reachable prefix is fixed and finite. Thus its finitely many read
addresses have a finite maximum length. Equal original prefixes through
that length force the same replies at every actual later epoch, then
the same updates and output. No rank, hidden timing information or
uniform local-computation hypothesis enters this implication. The
supplier's reverse direction uses paid historical decoding on the same
entry register. It applies to the entire $U$ because membership of a
given concrete finite candidate is decidable with every retained guard.

If condition 3 holds at $h$, the first line of (LAC.35.2) and exact
target correspondence give condition 4 with $K=2h+2$. Conversely a
witness $K$ to condition 4 and the second line of (LAC.35.2) give condition
3 at depth $A+K$. This proves the four-way equivalence.

After deciding (LAC.35.3) positively, test successive concrete $K$ using
the same arithmetic decision until one passes. The initial positive
decision proves that this extraction terminates. This is not an
algorithm that searches depths forever on negative inputs: those inputs
have already received the terminating negative decision of the quantified
sentence. Finite natural-tuple witnesses of a satisfiable arithmetic
predicate can likewise be found by enumeration in increasing total sum,
testing each tuple. A prior positive satisfiability decision proves
termination of that extraction.

Here is a direct service for the extracted cutoff. For each class $b$
and each $r<K$ to be tested, put

$$
t_r=\left\lfloor\frac{N+r}{2}\right\rfloor,
\qquad p_{b,r}=a_bR^{t_r}.
\tag{LAC.35.4}
$$

At the actual epoch $N$, original-address transport gives the subtree
$T_{N+k_b}$ at $a_b$. The supplied right-spine rule (ARH.6.1), also used
in [AOF, §§2–3][LAC-AOF], says that the actual reply at $p_{b,r}$ is
$\alpha$ exactly when $N+k_b=2t_r$, and $\beta$ exactly when
$N+k_b=2t_r+1$. Accept only $\alpha$ when $N+r$ is even and only
$\beta$ when it is odd. Thus the test accepts exactly $k_b=r$.
When $t_r=0$ it is a read at the existing $a_b$ itself, with the same
leaf-reply rule; in particular the boundary $N=1,r=0$ uses $\beta$.
Neither absence nor branch is accepted. Every request is an actual
original-root address, with its full prefix $a_b$.

For each $b$, stop its tests after the first acceptance. If all $r<K$
fail, record only $k_b\ge K$. These at most $|\mathcal B|K$ actual
queries determine the joint clipped tuple $c$. They reveal no exact
rank in its tail case and use no new update. For each possible
$c\in\{0,\ldots,K\}^{\mathcal B}$ consider the entire conditioned set

$$
S_c=\{k:\mathsf{Adm}(k)\land\operatorname{clip}_K(k)=c\}.
\tag{LAC.35.5}
$$

Decide its emptiness. For every nonempty $S_c$, extract a member $v_c$,
construct the finite native $U_{v_c}$, and compute its complete original
$R_Q$. Condition 4 proves that this one row is correct for every source
in $S_c$. There are finitely many $c$, so this finite table can be
computed from common input before any new observation. At runtime the
actual clipped tuple selects its row and the service halts. An actual
branch has the real source's tuple in $S_c$ and therefore is never an
empty table entry. Impossible reply branches may halt with any fixed
output; they are not claimed to be admitted runs.

This use of a finite table follows the proved whole-row constancy on
each full $S_c$. It does not decide the problem on a finite rank grid,
assume independent coordinate feasibility, or replace actual reads by
witness access. The witness is only a locally computed finite tree whose
row has been proved common; it need not be the actual source. New raw
receipts are precisely the actual epoch-$N$ address/reply events in
(LAC.35.4), not the inferred rank inequalities or synthetic past events.

If (LAC.35.3) is false, for every $K$ its negation gives a satisfiable
predicate

$$
\mathsf{Adm}(k)\land\mathsf{Adm}(l)\land\mathsf{Clip}_K(k,l)
       \land\neg\mathsf{Same}_Q(k,l).
\tag{LAC.35.6}
$$

For a requested $h$ use $K=2h+2$, extract such a pair and expand its
two finite fillings. Theorem 34.1 places both in the entire original
$U$ with all old inequalities and both endpoints of every signed record
intact. Proposition 35.2 gives equal original replies through $h$;
(LAC.34.3) gives different complete rows. These are admitted original
finite sources, never ambient nonnormal descriptions or infinite limits.
They exclude every uniformly bounded permitted serial service by
(ARH.2.3). The witnesses may depend on $h$.

All finite symbolic constructions, arithmetic decisions, conditional
witness extractions and finite-tree output computations terminate on
their stated domains. The service has zero new updates and a finite
actual address list; its submitted lengths are exactly
$|a_b|+\lfloor(N+r)/2\rfloor$ for the tests it makes. These are sufficient
bounds, not minimum prices. Acquisition, comparisons before the complete
cut, authentic entry, installation, local computation, address formation,
storage, retained receipts, output and physical time remain separately
charged. Output and absorbing halt do not themselves erase accessible
records or create a new free entry. $\square$

**Proposition 35.4 (empty, no-hole and extreme-cut meanings).** The
interpretation and decision have the following boundary values.

1. If $S=\varnothing$, (LAC.35.3) is vacuously true, but the reported
   result is logical emptiness. There is no admitted input run and no
   negative witness or acquired positive example.
2. If $\mathcal B=\varnothing$, the tuple space is the singleton
   $\{()\}$. Its admission predicate is the concrete check of all records
   on $C$. If it passes, $U=\{C\}$ and the complete target is computed
   and returned with zero new reads, even when $P$ or $Q$ is empty.
3. If $Q=\{\varepsilon\}$, the complete target is the constant one-hole
   row, so $K=0$ suffices on every nonempty covered input.
4. If $Q=\varnothing$, the target is the whole concrete original source.
   Bounded recovery holds exactly when $S$ is finite. If all target cuts
   happen to be absent on a branch, its row likewise contains the entire
   source; absence never denotes an empty output.

Proof. The first two assertions follow from the quantified predicates
over an empty set or zero coordinates and the exact source bijection.
In the third, the root always exists, its exterior is one numbered hole
and its partition is one class. For the fourth, Theorem 34.1 identifies
target equality with $k=l$. If a cutoff works, each of the finitely many
clipped tuples contains at most one admitted tuple, hence $S$ is finite.
Conversely a finite $S$ admits a cutoff strictly above all its coordinates
(with $K=0$ sufficient when there are none), so equal clips imply equal
tuples. The mask retains everything when no cut is reached, proving the
last statement. $\square$

## 36. A joint acquired consumer and deletion obstruction

**Proposition 36.1 (one actual read consumes two locally certified classes).**
Take the full original input

$$
\begin{gathered}
P=\{L,R\},\quad C=\langle\square_1,\square_2\rangle,
\quad\pi=\{\{1\},\{2\}\},\\
H_0=((0,L,\mathsf{branch}),(0,R,\mathsf{branch})),\\
e_L=(0,L,1,LL,=),\quad e_R=(0,R,1,RL,=),\\
d_1=(0,L,1,R,\ne),\quad d_2=(0,L,2,R,\ne),\\
H_{\rm rel}=(e_L,e_R,d_1,d_2),\quad N=2,\\
Q=\{LLL,LLR,LR,RL,RR\}.
\end{gathered}
\tag{LAC.36.1}
$$

Its entire original fiber is

$$
U=\{\langle T_i,T_j\rangle:i,j\ge2,\ i-j\notin\{0,1,2\}\}.
\tag{LAC.36.2}
$$

It has exactly the following two complete target rows. Number holes by
the displayed reached addresses in order.

$$
\begin{array}{c|c|c|c}
\text{case}&\text{reached cuts}&\text{concrete exterior}&\text{partition}\\\hline
i=2&LR,RL,RR&
 \langle\langle\beta,\square_1\rangle,
              \langle\square_2,\square_3\rangle\rangle&
 \{\{1\},\{2\},\{3\}\}\\
i\ge3&LLL,LLR,LR,RL,RR&
 \langle\langle\langle\square_1,\square_2\rangle,\square_3\rangle,
              \langle\square_4,\square_5\rangle\rangle&
 \{\{1,3\},\{2\},\{4\},\{5\}\}.
\end{array}
\tag{LAC.36.3}
$$

At actual entry epoch two, $\mathsf{Read}(LRR)$ selects the first row
on reply $\alpha$ and the second on $\beta$ or branch. The service then
outputs that whole row and halts, using one new read, zero new updates
and one submitted address of length three.

Proof. Both local certificates have suffix $L$, $n=0$ and $m=1$.
Proposition 33.2 forces each original child to be atomic of index at
least one. The two retained literals strengthen both bounds to two.
The old partition imposes $i\ne j$. At the same source the two additional
records compare $T_i$ with $T_{j+1}$ and $T_{j+2}$ respectively, giving
exactly the remaining excluded differences.

Conversely every displayed pair has the old branch exterior and distinct
children. Its epoch-zero literals are branch. At epoch one the reached
subtrees at $LL$ and $RL$ are $T_i$ and $T_j$, since $i+1,j+1\ge3$;
the two local positive predicates therefore hold with both endpoints
present. The $R$ endpoint of each negative record is an originally
reached child and persists at epochs one and two. The stipulated
inequalities make both negative signs true. Thus every tree in
(LAC.36.2), and no other finite source, satisfies the entire input.
No tree in this fiber is globally atomic: an atomic native pair with
children $T_i,T_j$ would require $i=j+1$, which $d_1$ excludes.

When $i=2$, the original $LL$ subtree is $\beta$, so $LLL$ and $LLR$
are absent; that concrete $\beta$ remains outside. The three reached
hole values are $T_0,T_{j-1},T_{j-2}$. Here $j\ge3$ by the old
disequality, making all three different. This gives the first whole row.
When $i\ge3$ all five cuts are reached, with ordered values

$$
T_{i-2},\quad T_{i-3},\quad T_{i-2},\quad T_{j-1},\quad T_{j-2}.
\tag{LAC.36.4}
$$

The first and third always agree. They differ from the second; the
fourth differs from the fifth. A cross-equality between the left and
right groups requires, respectively, $i-j=1$, $0$, $2$ or $1$.
All are excluded in (LAC.36.2), so the second complete partition in
(LAC.36.3) exhausts every pair comparison. The exterior is the fixed
displayed trie. Both rows occur, for example at $(i,j)=(2,4)$ and
$(3,4)$.

At epoch two the actual source is $\langle T_{i+2},T_{j+2}\rangle$.
The physical address $LRR$ enters the original left child and follows
two right edges. Its guard is $i+2\ge4$, and its whole subtree is
$T_{i-2}$. Its actual root reply is therefore $\alpha$ for $i=2$,
$\beta$ for $i=3$, and branch for $i\ge4$. This proves the service on
every source in the fiber. In the arithmetic decision one may also use
$K=3$: equal clipped pairs agree on whether $i=2$, which by the derived
whole rows is the only remaining target distinction. This explicitly
consumes the joint domain and complete-target interpretation.

For acquisition, use Proposition 2.1 with precisely the public coordinate
schedule in (LAC.36.1). At epoch zero acquire the old row, the stipulated
literals and the required original endpoint descriptions. After one
actual update acquire the whole subtrees at $LL$, $RL$ and $R$ needed
there; after the next update acquire the $R$ endpoint for $d_2$.
Compute the signs from these paid descriptions and impose the complete
cut at $N=2$. The proposition gives both source directions for that
retained outcome. No description, rank or forgotten traversal field is
available to the post-cut one-read service. Its acquisition and cut
hypotheses are precisely Assumption 1.3. $\square$

**Proposition 36.2 (deleting one acquired negative constraint destroys
uniform bounded recovery).** Delete only $d_1$ from (LAC.36.1), retaining
$P,R,H_0,e_L,e_R,d_2,N$ and the same entire target $Q$. The exact fiber is

$$
U^-=\{\langle T_i,T_j\rangle:i,j\ge2,\ i-j\notin\{0,2\}\}.
\tag{LAC.36.5}
$$

It still has a local atomic cover. No source-total permitted serial or
static service has a uniform finite new-read bound for its complete
target, although a pointwise terminating actual static service exists.

Proof. The two original-source directions in Proposition 36.1 apply with
only the comparison to $T_{j+1}$ omitted. In particular the old
$i\ne j$, both branch literals and both guards of $d_2$ remain. No new
source promise or changed cut is involved.

For any cutoff $K$, choose $M\ge\max(K,3)$ and the two admitted tuples

$$
(i,j)=(M+1,M),\qquad (i',j')=(M+3,M).
\tag{LAC.36.6}
$$

Their clipped tuples at $K$ both equal $(K,K)$. All five target cuts
are reached in both sources, and their concrete exteriors coincide with
the second exterior in (LAC.36.3). Formula (LAC.36.4) gives the first
source's partition as
$\{\{1,3,4\},\{2,5\}\}$, since its rank difference is one. The second
source has only the repeated class $\{1,3\}$, since its difference is
three. These are distinct complete native rows. Both sources are finite
and satisfy every remaining original predicate. The first is itself the
native atomic tree $T_{M+2}$; its alternative paired expression is not
counted as a different source.

Thus (LAC.35.3) is false for this full input. For an explicit negative
witness at any inclusive original depth $h$, take
$M=\max(2h+2,3)$ in (LAC.36.6) and apply Proposition 35.2. The resulting
admitted finite sources agree at every address of length at most $h$
and disagree on the whole target. Theorem 35.3 excludes all permitted
uniformly bounded comparators, including adaptive serial updates.

For completeness, on any one source recover each finite atomic index
by actual epoch-two reads at $LR^t$ and $RR^t$, respectively, for
$t=0,1,\ldots$, stopping each sequence at its first leaf reply.
For a child index $k$, the current index is $x=k+2$. All preceding
right-spine replies are branch, and at $t=\lfloor x/2\rfloor$ the
reply is $\alpha$ when $x=2t$ and $\beta$ when $x=2t+1$.
Thus the two sequences terminate, yield the two indices from actual
reads, and permit local computation of the complete original row.
Their lengths have no common finite bound on $U^-$.

The full target image here consists of three rows: the two in
(LAC.36.3) and the same five-hole exterior with partition
$\{\{1,3,4\},\{2,5\}\}$. Indeed, for $i\ge3$ the only newly permitted
cross-equality condition in (LAC.36.4) is $i-j=1$; for $i=2$ the old
first row remains unchanged. The obstruction therefore comes from a
source-sensitive constraint deletion in the joint interpretation, even
when the complete target image is finite. $\square$

## 37. Scope of the local-cover interpretation

**Definition 37.1 (supplier and unresolved boundaries).** The domain of
Theorems 34.1 and 35.3 is the complete acquired input with the syntactically
retained cover (LAC.33.1), including its logical empty and no-hole cases.
The source-relative addition is the finite guarded arithmetic
interpretation of the full jointly constrained old-class tuple, the
complete-row predicate, and the cofinal cutoff deciding bounded recovery
on that domain. Proposition 36.1 consumes all of these in an actual
original-root protocol; Proposition 36.2 supplies native finite witnesses
after deleting just one retained constraint.

Theorem 4.2 supplies certificate-to-atomic classification, Proposition
2.1 supplies acquisition correspondence, and (ARH.2.3) supplies the
original static/serial existence equivalence. ABC supplies canonical
native equality, guarded navigation and complete mask/partition
correspondence. AOF's atomic reply formulas are used only on certified
local atomic subtrees; its single-global-orbit finite representative and
exact-price theorems are not transferred to a joint rank domain.
Ginsburg–Spanier's decidability and effective semilinear correspondence
are literature-attested suppliers with the natural-number first-order
arithmetic hypotheses stated in Theorem 35.3. The additional native
source and service correspondences are repository-derived ordinary
mathematics; no global originality or complexity claim is part of them.

The finite guarded case families in Theorem 34.1 are generated from the
retained finite context and finitely many fixed words and epochs. Their
construction requires no arbitrary-shape normal-domain formula. ABC
Assumption 7.3 postulates such a formula; [TPO, Corollary 4.2][TPO] excludes
it in exactly the four-sort covariant $\{F\}$-term-power language, even with
fixed finite parameters. This language-specific exclusion leaves the
finite-context arithmetic construction above intact and implies neither
undecidability nor impossibility of unrestricted native recovery.

Missing local certificates give no decision
on arbitrary unknown subtrees or unrestricted coupled interpreted
histories. The theorem decides the existence of a finite completion
budget under Assumption 1.3; it does not decide all specified raw or
address budgets or supply exact general Pareto or weighted prices.
Those require their separate arbitrary-address and same-run resource
correspondences. No such price conclusion follows from the clipped
output table alone.

The original simultaneous complete-law, supported-depth, $j_c$, stochastic
attainment and physical realization questions retain their original
hypotheses and remain outside this deterministic interpretation. Neither
arithmetic coordinates nor locally computed witness trees install an
observation port or discharge acquisition, access-cut or physical-cost
obligations.

[LAC-ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[LAC-AOF]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[LAC-GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md

## 追加锚（本行以下为增补区）
