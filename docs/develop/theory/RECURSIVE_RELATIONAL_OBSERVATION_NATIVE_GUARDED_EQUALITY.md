# FIB relation-fiber theory: exact equality for pair-guarded native recursion

> This generic-v1 volume gives ordinary mathematical definitions and proofs,
> not Lean-kernel verification. Its native recursion and signed chart suppliers
> retain their own scope. Integrated text is retained; additions and corrections
> follow the terminal append anchor.

## 1. The supplied description class and original observations

**Definition 1.1 (native trees and four replies).** Retain the finite native
algebra and its prefix completion from [NCC, Definitions 1.1 and 2.1][NCC]:

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&
\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle s,t\rangle&=\langle\rho s,\rho t\rangle,\\
T_n&=\rho^n\alpha\qquad(n\in\mathbb N).
\end{aligned}
\tag{NGE.1}
$$

The completion $\overline{\mathcal T}$ consists of finite or infinite ordered
full binary trees whose leaves are labelled $\alpha$ or $\beta$. Actual $\rho$
extends by these same leaf replacements and pair law, as supplied by
[NLC, Theorem 11.3][NLC]. The tree $\Omega$ has a branch at every address;
$\rho\Omega=\Omega$.

Put $\Sigma=\{L,R\}$ and
$\mathcal R=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.
For every $Z\in\overline{\mathcal T}$ and every original-root address
$p\in\Sigma^{*}$, let $r_Z(p)\in\mathcal R$ be its exact reply. The empty
address $\varepsilon$ observes the root. A leaf has absent replies at all
proper descendants. Write $Z\sim_h W$ when all replies at $|p|\le h$ agree;
this depth is inclusive. Define the four address languages by

$$
\mathcal L_\tau(Z)=\{p\in\Sigma^{*}:r_Z(p)=\tau\}
\qquad(\tau\in\mathcal R).
\tag{NGE.2}
$$

Neither normal-code depth nor an unlabelled reached-address trace replaces
these observations. Infinite trees are auxiliary completion points, whereas
original sources belong to $\mathcal T$.

**Assumption 1.2 (finite nullary pair-guarded data).** Supply finitely many
state names $X_1,\ldots,X_s$ and equations

$$
X_i=E_i(X_1,\ldots,X_s)\qquad(1\le i\le s).
\tag{NGE.3}
$$

Each $E_i$ is a finite expression in the two native leaves, ordered pairing,
the states and fixed powers $\rho^a$, $a\in\mathbb N$. After distributing
these powers through explicit pairs, every state occurrence in each $E_i$
is below at least one explicit pair. States are nullary: no state receives
a tree, integer or changing exponent as a parameter.

An output $O$ is any finite expression in those same operations and states,
also allowing exact finite constants $g\in\mathcal T$, fixed $T_q$ and
$\Omega$. An output need not itself have a pair above every state. There
are no negative, variable or parameterized powers. The case $s=0$ is allowed.

Use the unique completed solution, effective prefixes and finite/infinite
tag facts already supplied by [NCC, Corollary 6.1][NCC]. Write
$\llbracket E\rrbracket$ for evaluation in that solution. The output tree
is $Z_O=\llbracket O\rrbracket$. These existing semantic and tag results
are premises of the address construction, not new fixed-point theorems here.
For outputs containing $\Omega$, its infinite tag is immediate; the same
nondeletion property used by NCC handles its finite expression contexts.

## 2. A finite presentation and the atomic head relation

**Definition 2.1 (finite distributed syntax).** In each equation and output,
expand exact ground constants into their finite native syntax. Distribute
fixed powers through explicit pairs, combine successive powers on a state,
evaluate powers on ground leaves, and replace any power on $\Omega$ by
$\Omega$. The resulting finite syntax has the form

$$
e::=\alpha\mid\beta\mid\Omega\mid\langle e,e\rangle
       \mid\rho^a X_i,
\qquad a\in\mathbb N.
\tag{NGE.4}
$$

Here a bare state is written $\rho^0X_i$. Only outputs require the
$\Omega$ alternative. These are finite expansions:
every expanded ground power has one fixed finite exponent, and no equation
is unfolded during this normalization. The actual laws (NGE.1) justify the
normalization inside its subsequent semantic use. It need not be a compact
representation of a large supplied constant.

The same pair guard remains true. In particular the normalized right-hand
side $E_i$ never has a root of the form $\rho^a X_j$: its root is a pair or
a ground leaf. Normalization distributes through pairs and does not remove
a pair above a state occurrence. Give each explicit pair occurrence in the
finite normalized equations and chosen output a syntax control. The children
of that occurrence retain their own syntax references. Repeated occurrences
of $X_i$ always refer to the same equation, rather than to new independent
states or coordinates.

**Definition 2.2 (counter meaning).** At an ordinary syntax control $q_e$,
the nonnegative counter $c$ represents the tree

$$
\rho^c\llbracket e\rrbracket.
\tag{NGE.5}
$$

The accumulated exponent acts on the entire currently followed subtree.
At an explicit pair it passes unchanged to the selected child. It is not
the remaining address length. Native atomic heads instead obey the identities

$$
T_0=\alpha,\qquad T_1=\beta,\qquad
T_{n+2}=\langle T_{n+1},T_n\rangle\quad(n\ge0).
\tag{NGE.6}
$$

Indeed apply $\rho^n$ to $T_2=\langle\beta,\alpha\rangle$ and use the
pair law in (NGE.1). These elementary native identities are used as
intermediate steps in Theorem 4.1. Thus $\rho^c\beta=T_{c+1}$, and an
atomic branch of rank $n\ge2$ has left rank $n-1$ and right rank $n-2$.
Those atomic child rules do not apply to an explicit syntax pair.

## 3. The lawful deterministic one-counter presentation

**Definition 3.1 (finite controls and transition relation).** A counter
configuration is $(q,c)$ with $c\in\mathbb N$. A transition inspects only
whether $c=0$ or $c>0$, reads one of $L,R$ or $\varepsilon$, and changes the
counter by $-1$, $0$ or $+1$. An update $-1$ is permitted only at $c>0$.

Use the following finite control set. For a pair occurrence $e$, its syntax
control is $P_e$. The syntax controls for $\alpha,\beta,\Omega$ are
$q_\alpha,q_\beta,O_\Omega$, respectively. For a decorated occurrence
$\rho^aX_i$, its syntax control is $J_{a,i}$. Include $J_{d,i}$ for all
$0\le d\le a$ needed by any such occurrence. Sharing these controls for
the same $d,i$ is harmless. Also include controls

$$
A,\ V,\ B,\ H_\alpha,\ H_\beta,\ N.
\tag{NGE.7}
$$

The controls $A,V,B$ will represent atomic ranks $c,c+1,c+2$,
respectively. The controls $H_\alpha,H_\beta$ are stable leaf heads and
$N$ is the stable absent head. Let $q_{E_i}$ and $q_O$ be the syntax
controls of the normalized equation root and output root.

The entire transition relation is given below. In the test column, “both”
means one rule for zero and one for positive, with the displayed same
destination and update. A row with “$L,R$” means one rule for each letter.
There are no additional rules.

| Control | Counter test | Read | Destination | Update |
| --- | --- | --- | --- | --- |
| $P_{\langle e_L,e_R\rangle}$ | both | $L$ | $q_{e_L}$ | $0$ |
| $P_{\langle e_L,e_R\rangle}$ | both | $R$ | $q_{e_R}$ | $0$ |
| $O_\Omega$ | both | $L,R$ | $O_\Omega$ | $0$ |
| $q_\alpha$ | both | $\varepsilon$ | $A$ | $0$ |
| $q_\beta$ | both | $\varepsilon$ | $A$ | $+1$ |
| $J_{d,i}$, $d>0$ | both | $\varepsilon$ | $J_{d-1,i}$ | $+1$ |
| $J_{0,i}$ | both | $\varepsilon$ | $q_{E_i}$ | $0$ |
| $A$ | zero | $\varepsilon$ | $H_\alpha$ | $0$ |
| $A$ | positive | $\varepsilon$ | $V$ | $-1$ |
| $V$ | zero | $\varepsilon$ | $H_\beta$ | $0$ |
| $V$ | positive | $\varepsilon$ | $B$ | $-1$ |
| $B$ | both | $L$ | $A$ | $+1$ |
| $B$ | both | $R$ | $A$ | $0$ |
| $H_\alpha,H_\beta$ | both | $L,R$ | $N$ | $0$ |
| $N$ | both | $L,R$ | $N$ | $0$ |

The initial configuration is $(q_O,0)$. Stable controls are the pair
controls, $O_\Omega,B,H_\alpha,H_\beta,N$. Their reply labels and four
accepting sets are

$$
\begin{aligned}
F_\alpha&=\{H_\alpha\},&F_\beta&=\{H_\beta\},\\
F_{\mathsf{branch}}&=\{P_e:e\text{ is a pair occurrence}\}
                         \cup\{O_\Omega,B\},&
F_{\mathsf{absent}}&=\{N\}.
\end{aligned}
\tag{NGE.8}
$$

Unused controls can be omitted. All administrative controls are
nonaccepting in all four machines. For each $\tau$, let $M_{O,\tau}$
have this same transition relation and initial configuration, with
accepting set $F_\tau$. Acceptance is finite-word final-state acceptance
at any nonnegative counter: a word is accepted when a finite run consuming
that whole word ends in an accepting control. Epsilon transitions consume
no original address letter.

**Theorem 3.2 (unit rules, exclusivity and finite administration).** The
presentation of Definition 3.1 is a finite deterministic one-counter
automaton in the classical epsilon convention. For each control, input
letter and counter test there is at most one transition. For each control
and counter test, an epsilon transition excludes all input transitions.
Every reachable counter is nonnegative. From the initial configuration
and after each consumed address letter, administrative processing ends
after finitely many epsilon transitions at exactly one stable head. Every
stable head can consume either next address letter. In particular every
finite original address has exactly one terminal stable reply label.

Proof. Finiteness follows from the finite normalized syntax and the finite
sets of fixed remainders $d$. Each row is already a standard unit-update
rule, not an unimplemented multiple increment or threshold test. The two
decrements have explicit positive guards. All remaining updates are $0$
or $+1$, so induction along any run gives nonnegativity.

Pair and stable-head controls have only input transitions. Every other
control has exactly one epsilon rule at each counter test and no input
rule. The table therefore gives both determinism conditions directly.
Duplicated syntax references to the same $J_{d,i}$ use the same rule,
not competing transitions.

At $J_{d,i}$, exactly $d$ increment steps reach $J_{0,i}$, then one
zero-update step reaches $q_{E_i}$. Pair guardedness ensures this equation
root is a pair or ground leaf; it is never another decorated-state root.
Thus state unfolding cannot form an epsilon cycle. A ground leaf enters
$A$ in one step, and $A$ reaches a stable head in at most two more steps.
At $A$, zero goes directly to $H_\alpha$; positive makes one lawful
decrement to $V$. At $V$, zero goes to $H_\beta$; positive makes one more
lawful decrement to $B$. No restoration, negative counter or test for
an arbitrary threshold is hidden in these steps.

A pair or $O_\Omega$ is already stable. An input transition from $B$
enters $A$, and a leaf enters $N$; the other input transitions enter
a child syntax control. These cases prove finite administration after
each input as well as at the start. For instance, a decorated-state
entry with exponent $a$ needs at most $a+4$ administrative steps before
the next stable head, regardless of the entering counter. This is a
finite-chain termination fact, not a cost bound for compact native data.
There are no epsilon transitions from a stable head, and all its input
rules are total on $\{L,R\}$. Determinism then proves uniqueness.
$\square$

## 4. Exact native denotation at every original address

**Theorem 4.1 (four-language correspondence).** For every supplied system
and output satisfying Assumption 1.2, the four machines of Definition 3.1
recognize exactly the four original-address reply languages:

$$
L(M_{O,\tau})=\mathcal L_\tau(Z_O)
\qquad(\tau\in\mathcal R).
\tag{NGE.9}
$$

The equality includes the empty address, born branches inside native leaf
images, and all absent descendants. The four languages partition
$\Sigma^{*}$.

Proof. Interpret an ordinary syntax configuration by (NGE.5). For the
remaining administrative and atomic controls use

$$
\begin{aligned}
(J_{d,i},c)&\longmapsto\rho^{c+d}\llbracket X_i\rrbracket,\\
(A,c)&\longmapsto T_c,&
(V,c)&\longmapsto T_{c+1},&
(B,c)&\longmapsto T_{c+2},\\
(H_\alpha,c)&\longmapsto\alpha,&
(H_\beta,c)&\longmapsto\beta,&
(O_\Omega,c)&\longmapsto\Omega.
\end{aligned}
\tag{NGE.10}
$$

The control $N$ represents an absent position and every subsequent
descendant. This is a reply convention, not a new native source. Reachable
$H_\alpha,H_\beta$ configurations have counter zero; their displayed
meaning can also ignore the counter at unreachable configurations.

Every epsilon transition preserves this interpretation. At $q_\alpha$,
the value is $\rho^c\alpha=T_c$. At $q_\beta$, one increment makes the
value $\rho^c\beta=T_{c+1}$. An increment at $J_{d,i}$ decreases $d$
and increases $c$, preserving $c+d$. At $J_{0,i}$ the defining equation
identifies $\llbracket X_i\rrbracket$ with $\llbracket E_i\rrbracket$.
This includes repeated state occurrences with their shared solution.

The atomic classification preserves the same value while changing its
counter convention. At zero, $(A,0)$ represents $T_0=\alpha$. At positive
$c$, its decrement to $(V,c-1)$ represents $T_{(c-1)+1}=T_c$. At zero,
$(V,0)$ represents $T_1=\beta$. At positive $c$, its decrement to
$(B,c-1)$ represents $T_{(c-1)+2}=T_{c+1}$. Thus $B$ stores the atomic
rank minus two. It does not store the original rank unchanged.

At every stable head, its label in (NGE.8) is precisely its represented
root reply. An explicit pair is a branch because

$$
\rho^c\langle\llbracket e_L\rrbracket,\llbracket e_R\rrbracket\rangle
 =\langle\rho^c\llbracket e_L\rrbracket,
            \rho^c\llbracket e_R\rrbracket\rangle.
\tag{NGE.11}
$$

Consuming $L$ or $R$ at that pair therefore selects the correct child
without changing $c$. At $(B,c)$, (NGE.6) gives left subtree $T_{c+1}$
and right subtree $T_c$. Its $L$ transition to $(A,c+1)$ and $R$
transition to $(A,c)$ give exactly these values. The two initial
classification decrements together with these input updates yield net
rank changes $-1$ and $-2$, respectively. At $O_\Omega$ both children
are $\Omega$. At a stable leaf either child is absent, and $N$ stays
absent on any further suffix. These statements treat every input rule.

Initially the represented value is $Z_O$. By Theorem 3.2 its initial
administration terminates with that same root value and correct label.
Induct on the number of consumed letters. The stable-head input rule
selects the actual addressed subtree, or the absent convention after
an early leaf; the following finite administration preserves that
value and classifies its root correctly. Consequently the stable
label after exactly $p$ is $r_{Z_O}(p)$ for every $p$, including
$p=\varepsilon$.

Administrative controls never accept. Stable controls have no epsilon
successors. Hence any accepting run consuming a whole word ends at
its unique stable head; stopping early in administrative processing
cannot add an accepted word. Conversely that stable head is reached
by a finite run, and accepts in precisely the machine with its label.
This proves (NGE.9) and the partition assertion. No endmarker or
additional original observation has been used. $\square$

## 5. Equality decided through the classical automata supplier

**Theorem 5.1 (exact equality for supplied native descriptions).** Given
two outputs of systems satisfying Assumption 1.2, equality of their
completed native trees is decidable. More precisely,

$$
\begin{aligned}
Z_O=Z_{O'}
&\ \Longleftrightarrow\
\bigwedge_{\tau\in\mathcal R}
\mathcal L_\tau(Z_O)=\mathcal L_\tau(Z_{O'})\\
&\ \Longleftrightarrow\
\bigwedge_{\tau\in\mathcal R}
L(M_{O,\tau})=L(M_{O',\tau}).
\end{aligned}
\tag{NGE.12}
$$

The equality decision concerns the actual interpreted $\rho$ outputs;
it requires no supplied ordinary equational derivation of their equality.

Proof. An ordered labelled constructor tree is determined by its reply
at every finite address. Indeed its present addresses, the branch/leaf
status at each present address and each terminating leaf label are
then fixed. Thus equality implies the first language conjunction;
that conjunction implies agreement of all replies and hence equality.
Theorem 4.1 gives the second conjunction. Separate systems can have
their state names renamed disjointly; no identification of their
solutions is assumed.

For the decision step use the established classical deterministic
one-counter language-equivalence result in Böhm–Göller–Jančar,
*Equivalence of Deterministic One-Counter Automata is NL-complete*,
[arXiv:1301.2181v1, Appendix, PDF pp. 23–24][BGJ],
DOI [10.1145/2488608.2488626][BGJDOI]. That Appendix
defines transitions in

$$
Q\times(\Sigma\cup\{\varepsilon\})\times\{0,1\}
 \times Q\times\{-1,0,1\},
\tag{NGE.13}
$$

where $0,1$ indicate zero and positive tests, forbids a decrement on
zero, requires uniqueness for each control/letter/test, and excludes
input rules wherever an epsilon rule has the same control/test.
Its initial counter is zero. It accepts a finite word upon reaching
an accepting control at any nonnegative counter. It reduces this
classical language-equivalence problem to the paper's normalized
equivalence problem and explicitly states the corresponding analogue
of its Theorem 3. This cited decidability is an intermediate in the
native proof, rather than a new general automata theorem here.

Theorem 3.2 matches each transition requirement, and Definition 3.1
matches initial and final-state conventions. Theorem 4.1 matches the
accepted words to original addresses before invoking equivalence.
Apply the supplier to each of the four finite pairs of machines.
Their four Boolean answers decide (NGE.12).

The machines have epsilon transitions; they are not being called
strict real-time automata. No reset-form trace convention is silently
substituted for final-state acceptance. The Appendix may introduce a
fresh acceptance letter inside its reduction, but that letter is
automata acceptance plumbing, not an additional original address or
reply. No bound on native-description equality complexity is inferred
from the supplier's complexity classification. $\square$

## 6. Semantic boundaries of the construction

**Theorem 6.1 (leaf growth, atomic ranks and necessity of labels).** The
following native observations and presentation boundaries hold.

1. At original address $L$, $\rho^2\langle\alpha,\alpha\rangle$ replies
   branch, rather than $\beta$.
2. $\rho^c\beta$ has effective atomic rank $c+1$, not $c$.
3. $T_2$ replies $\alpha$ at $R$ and absent at $RL$.
4. Forgetting all reply labels cannot distinguish the trees $\alpha$
   and $\beta$ by their total machine traces.
5. Removing the pair guard allows an infinite administrative run in
   this construction, so Theorem 3.2 has no such unguarded extension.

Proof. The pair law gives
$\rho^2\langle\alpha,\alpha\rangle=\langle T_2,T_2\rangle$.
Its $L$ subtree is $T_2=\langle\beta,\alpha\rangle$, a branch.
Decrementing the accumulated exponent merely upon passing an explicit
pair would instead turn that child into $T_1=\beta$ and give the wrong
reply. This proves the first assertion and explains the zero-update
pair rules.

The identity $\beta=\rho\alpha$ proves the second assertion. The
displayed exact $T_2$ proves the third, including the absent suffix
below its right leaf. In particular the actual operation changes
leaf shape: $\rho\beta$ is a pair. A claim that $\rho$ never changes
shape would contradict these finite values.

For the fourth assertion, after administration either leaf machine
has a defined run on every $p\in\Sigma^{*}$, entering $N$ after any
nonempty address. Both unlabelled total trace languages are therefore
$\Sigma^{*}$. Even their present-address sets both equal
$\{\varepsilon\}$. Their $\alpha$ and $\beta$ languages differ at
$\varepsilon$, which (NGE.12) retains.

For the fifth assertion consider the unguarded equation $X=\rho X$.
Its normalized equation root is $J_{1,X}$. Administrative processing
cycles from $J_{1,X}$ to $J_{0,X}$ and back to $J_{1,X}$, increasing
the counter each time and consuming no address letter. It never
reaches a stable head. This is a failure of the unguarded presentation
and its termination argument; it makes no claim about undecidability
or all possible semantics for unguarded equations. $\square$

## 7. Consumption in complete signed prescribed-row charts

**Assumption 7.1 (the exact original fiber and labelled chart pair).**
Retain the entire acquired native source predicate of
[PDC, Assumption 1.2][PDC] and [NCC, Assumptions 1.2–1.3][NCC]:

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{NGE.14}
$$

Here $R$ is the complete old row, $H_0$ is the entire finite literal
list and $H_{\rm rel}$ is the entire signed mixed-epoch list. Every
signed record retains both reached endpoints and compares the actual
whole subtrees at those endpoints, whether its sign is equality or
disequality. All records concern the same original source. Repeated
names/classes, old cross-class inequalities, off-task negatives and
the entire old exterior are retained.

Fix a finite prefix-free original $Q$. Its full target row records
the reached positions in their order, its complete numbered-hole
exterior and its whole-subtree equality partition. Neither a partition
alone nor a label for a sample replaces $R_Q$.

Supply two charts from the exact full-row-labelled cover of
[NCC, (NCC.5)][NCC], with distinct prescribed complete labels
$r_i\ne r_j$. For $\nu=i,j$ their domains and source maps are

$$
\begin{aligned}
\mathcal C_\nu
 &=\{(\mathbf n,\mathbf z)\in\mathbb N^{k_\nu}\times
             \mathcal T^{m_\nu}:K_\nu(\mathbf n)
                        \land\Gamma_\nu(\mathbf n,\mathbf z)\},\\
\Gamma_\nu&=\bigwedge_\ell A_{\nu\ell}\ne B_{\nu\ell},\\
A&::=g\mid T_{n_a+c}\mid\rho^b z_t\mid\langle A,A\rangle,
\qquad g\in\mathcal T,\quad b,c\in\mathbb N,\\
\Theta_\nu[\mathcal C_\nu]
 &\subseteq\{u\in D:R_Q(u)=r_\nu\}.
\end{aligned}
\tag{NGE.15}
$$

The residual carrier is the full Cartesian $\mathcal T^{m_\nu}$,
subject only to this entire list of whole negatives; $K_\nu$ is an
effective scalar Presburger formula. Every shared name has one value.
No remaining positive residual, image, navigation or root-sort
predicate is allowed outside the displayed conjunction. Necessary
nonprimitive-sort restrictions are retained as whole negatives.

[PDC, Theorem 5.2 and §§6–8][PDC] supplies these charts, discharges the
positives, literals and guards in both original-source directions,
and preserves the exterior and all row comparisons. The complete
finite family covers the entire original domain. One selected branch
need not alone cover its whole row stratum. In the finite full-row-image
case, [PDC, Corollary 8.3, (23)][PDC] fixes a distinct-label chart pair
before the requested prefix depth varies. These are supplier premises,
not a new all-source chart construction in this volume.

**Definition 7.2 (concrete supplied descriptions, finite freezing and joint
cofinality).** For each selected chart, let $\mathsf{Desc}_\nu$ be the
class of finite records $d_\nu$ consisting of exactly the following data:

1. For each scalar coordinate, a label $\overline n_a=q_a\in\mathbb N$
   with its exact supplied integer, or the label $\overline n_a=\infty$.
   Let $J_\nu$ be the infinite-scalar index set. These labels denote
   $t_a=T_{q_a}$ and $t_a=\Omega$, respectively.
2. A partition of the residual indices into $F_\nu$ and $I_\nu$, and an
   exact finite native tree $f_t\in\mathcal T$ for every $t\in F_\nu$.
3. A supplied finite nullary equation system $\mathscr E_\nu$ and one
   supplied finite output expression $O_{\nu,t}$ for every $t\in I_\nu$.
   This system and every output satisfy Assumption 1.2: all powers are
   fixed nonnegative integers, and every state occurrence in an equation
   lies below an explicit pair after fixed-power normalization. Outputs
   may use the exact finite constants and $\Omega$ allowed there.

In the dependency graph of $\mathscr E_\nu$, put an edge $X_r\to X_s$
when $X_s$ occurs in $E_r$. Each $O_{\nu,t}$ with $t\in I_\nu$ must
contain either $\Omega$ or a state reaching a directed cycle. By
[NCC, Corollary 6.1][NCC] and the nondeletion rule for $\Omega$ in
Assumption 1.2, this finite graph condition is exactly the assertion
that its completed output is genuinely infinite. Thus the residual
tags are correct for these concrete data; no arbitrary program's
infinitude or independently chosen semantic coordinate is an input
oracle. When $I_\nu$ is empty, the system and output family may be empty.

Several outputs may share one equation system and its states. Systems
supplied independently may be bundled after disjoint renaming; a shared
system is included once. Renaming preserves every shared state reference,
and every repeated chart-coordinate name uses the same output expression
and value. This sharing does not identify the private finite completion
holes of different residual coordinates.

The record determines its coordinate point, rather than taking such a
point as additional input:

$$
\xi_\nu:=\operatorname{pt}(d_\nu)
       =(\mathbf t_\nu,\mathbf Z_\nu)
 \in\overline{\mathcal A}^{k_\nu}\times
                \overline{\mathcal T}^{m_\nu},
\qquad
\overline{\mathcal A}=\{T_q:q\in\mathbb N\}\cup\{\Omega\}.
\tag{NGE.16}
$$

Here $Z_{\nu,t}=f_t$ for $t\in F_\nu$ and
$Z_{\nu,t}=\llbracket O_{\nu,t}\rrbracket_{\mathscr E_\nu}$ for
$t\in I_\nu$, evaluated in the unique solution of the supplied system.
The atomic coordinates are exactly the trees $t_a$ determined by the
scalar labels, as in [NCC, Definition 2.2][NCC]. Every infinite residual
carries an actual finite system/output witness, not merely an assertion
that one exists. The map $\operatorname{pt}$ is not asserted to cover arbitrary
completion points or every prescribed-pair contact witness.

These same data supply a total effective prefix interface
$\operatorname{Pref}_{d_\nu}(t,h)$, defined for every residual index
$1\le t\le m_\nu$ and $h\in\mathbb N$, returning the exact finite table
$(r_{Z_{\nu,t}}(p))_{|p|\le h}$, including root and absent replies.
For $t\in F_\nu$ use its supplied finite syntax. For $t\in I_\nu$ use
the guarded iteration of [NCC, Corollary 6.1][NCC]: starting all states
at $\alpha$, $h+1$ iterations stabilize their replies through $h$.
Evaluate the supplied finite output with actual native locality and the
known prefixes of $\Omega$. Fixed powers and pairing preserve agreement
through $h$, so this yields the required output table. Scalar prefixes
are computed from the exact $T_{q_a}$ or $\Omega$ in the same way. This
interface is derived from the supplied descriptions, not assumed for
arbitrary points in the space displayed in (NGE.16).

Use exactly the following formulas, with chart subscripts suppressed:

$$
\begin{aligned}
S_f(\mathbf n)
 &\ \Longleftrightarrow\ K(\mathbf n)\land
   \exists\mathbf w_I\in\mathcal T^I\quad
        \Gamma(\mathbf n,(f_t)_{t\in F},\mathbf w_I),\\
\operatorname{Cof}(d)
 &\ \Longleftrightarrow\
 \forall b\in\mathbb N\ \exists\mathbf n\in\mathbb N^k\quad
 S_f(\mathbf n)\land
 \bigwedge_{a\notin J}n_a=q_a\land
 \bigwedge_{a\in J}n_a\ge b.
\end{aligned}
\tag{NGE.17}
$$

The notation $\operatorname{Cof}(d)$ is precisely the semantic condition
of [NCC, Definition 2.2][NCC] applied to $\operatorname{pt}(d)$.
One finite residual tuple $\mathbf w_I$ must satisfy the whole
$\Gamma$ at the same entire scalar vector. Every finite residual
is frozen at $f_t$, and every finite scalar is frozen at $q_a$.
For empty index sets the conjunctions and products have their usual
literal empty meanings. In particular no infinite scalars makes
$\operatorname{Cof}$ exact fixed-rank feasibility, not a growth test.

The completed output
$Y_\nu(d_\nu)=\overline\Theta_\nu(\operatorname{pt}(d_\nu))$ replaces
each atomic term $T_{n_a+c}$ by $\rho^c(t_a)$, with
$t_a=T_{q_a}$ or $\Omega$ according to its supplied scalar tag,
and each residual name by $f_t$ or its actual supplied expression
$O_{\nu,t}$. Thus the finite expressions for $Y_i(d_i),Y_j(d_j)$ are
outputs of Assumption 1.2: combine their supplied systems, renaming only
independent systems disjointly and preserving all shared references.
The exponents $b,c$ in the source templates are fixed; no unbounded rank
variable is silently turned into a recursive exponent in this output description.

**Theorem 7.3 (decidable supplied signed prescribed-pair certificate).**
Under Assumption 7.1, for every pair of concrete records
$d_i\in\mathsf{Desc}_i$, $d_j\in\mathsf{Desc}_j$ of Definition 7.2,
the exact condition

$$
\mathsf{Accept}(d_i,d_j)
\ \Longleftrightarrow\
\operatorname{Cof}_i(d_i)\land
\operatorname{Cof}_j(d_j)\land Y_i(d_i)=Y_j(d_j)
\tag{NGE.18}
$$

is decidable as a predicate of these supplied finite records. It is
equivalent to their induced points $\operatorname{pt}(d_i)$ and
$\operatorname{pt}(d_j)$ lying in their own finite chart-coordinate
closures and their completed source outputs being equal. On acceptance
of these records, for every requested inclusive original depth
$h\in\mathbb N$, it constructs
actual finite sources $u_h,v_h$ satisfying

$$
\begin{aligned}
u_h,v_h&\in D,&
R_Q(u_h)&=r_i,&R_Q(v_h)&=r_j,&u_h&\sim_h v_h.
\end{aligned}
\tag{NGE.19}
$$

They are distinct because their complete rows differ. Sources and
finite coordinate tuples may vary with $h$ and are chosen separately
for the two charts. Failure rejects precisely this supplied candidate
point pair; it does not exclude another certificate for these labels or another
distinct-label pair.

Proof. First substitute every finite $f_t$ exactly into all its shared
occurrences in $\Gamma$. Evaluating its fixed native powers leaves
the same mixed-template grammar on the remaining full Cartesian
residual tuple. [URR, Corollary 3.2][URR], as used in
[NCC, Definition 2.2][NCC], supplies an exact effective Presburger
formula for $S_f(\mathbf n)$. It retains all negatives jointly,
including those expressing cross-class and residual root-sort
conditions. Therefore each sentence in (NGE.17) is a Presburger
sentence and is decidable with its displayed quantifier order.
This reuse is scalar projection on the whole residual carrier;
URR's selected completion tuple is not being substituted for the
whole original domain or for the depth-dependent realizations.

Next apply Theorem 5.1 to the two concrete output expressions
$Y_i(d_i),Y_j(d_j)$ constructed in Definition 7.2 from their supplied
systems, output witnesses, exact finite values and scalar labels.
It decides their actual completed-tree equality by the four exact
original-address languages. Together these decisions decide every
conjunct of (NGE.18).

Only now invoke the signed correspondence. [NCC, Theorem 4.1][NCC]
gives, with precisely the finite freezing and joint support of
(NGE.17),

$$
\operatorname{Cof}_\nu(d_\nu)
\ \Longleftrightarrow\
\operatorname{pt}(d_\nu)\in
\overline{\operatorname{coord}[\mathcal C_\nu]}.
\tag{NGE.20}
$$

This proves both directions of the supplied-coordinate assertion in
the theorem. With $Y_i(d_i)=Y_j(d_j)$ established, [NCC, Theorem 5.2][NCC]
then applies to this very chart pair and its same prescribed complete
labels. Its forward finite-realization direction gives admitted
tuples $a_h\in\mathcal C_i$, $b_h\in\mathcal C_j$ independently
approximating their own points through $h$. Its native source locality
gives

$$
\Theta_i(a_h)\sim_h Y_i(d_i)=Y_j(d_j)\sim_h\Theta_j(b_h).
\tag{NGE.21}
$$

Take $u_h=\Theta_i(a_h)$ and $v_h=\Theta_j(b_h)$. The exact original
chart reconstruction in (NGE.15) supplies membership in the entire
$D$ and the exact full rows, proving (NGE.19). It preserves all the
old row, acquired literals, signed mixed-epoch records, both endpoint
guards, repeated names/classes, off-task negatives, cross-class
inequalities, numbered exterior and partition. None is checked only
on the limiting trees. In particular finite inequalities may vanish
at the common limit and still hold in every admitted finite source.

The supplied recursive coordinates have the effective prefix interface
of Definition 7.2, derived from [NCC, Corollary 6.1][NCC].
[NCC, Theorem 4.1][NCC] combines these prefixes with a Presburger rank
witness and one joint residual completion for the whole substituted
negative list.
These already supplied finite constructions make (NGE.19) productive
for every requested $h$, without a fixed source-size, depth or rank
cutoff. Raw recursive unfoldings alone need not satisfy the signs;
their role is to provide the prefixes before exact joint completion.

For the other original-source direction, [NCC, Theorem 5.2][NCC] says
that contact at every $h$ for the images of this fixed chart pair implies
the existence of some semantic cofinal coordinate points with equal completed outputs.
If those witnesses are denotations of records in $\mathsf{Desc}_i$ and
$\mathsf{Desc}_j$, (NGE.20) and Theorem 5.1 force acceptance of those
records. The supplier does not say those semantic witnesses admit such
records, and supplies no effective prefixes for arbitrary points.
No converse description-completeness assertion is used.

If a cofinality sentence is false, [NCC, Theorem 4.1][NCC] supplies a
finite coordinate neighborhood of that supplied point disjoint from its
own chart.
If equality is false, (NGE.12) gives a finite original address at
which the two supplied completed outputs differ. Such an address
can also be found by enumerating finite words and computing the
supplied effective replies, since inequality ensures termination
of this witness search. Either failure invalidates (NGE.18), while
leaving alternative points and chart pairs untested. $\square$

**Theorem 7.4 (the exact premise removed from [NCC, Corollary 6.1][NCC]).**
For the concrete supplied-description records of Definition 7.2, whose
equation and output data satisfy Assumption 1.2, the supplied ordinary
equality derivation premise in [NCC, Corollary 6.1][NCC] may be replaced
by the affirmative equality decision of Theorem 5.1. Its signed
prescribed-pair conclusion remains sound as in Theorem 7.3 with both
exact cofinality sentences.

Proof. [NCC, Corollary 6.1][NCC] uses its derivation premise to establish
the truth of the equality of the two completed source outputs.
Theorems 4.1 and 5.1 establish precisely that equality when their answer is affirmative,
with the same interpreted leaf laws, states and output trees. The
remaining hypotheses are unchanged, and Theorem 7.3 invokes the
same signed finite-source correspondence at those hypotheses.
This substitution concerns a proof of equality's truth. It does not
assert that the automata decision produces a finite native equational
derivation, or that every true equality is derivable in that particular
equational proof language. $\square$

## 8. Exact supplier correspondence and unresolved general target

**Convention 8.1 (mathematical ownership and literature scope).** The
finite-control/counter correspondence, its complete reply semantics
and their equality-driven signed consumption in Theorems 3.2–5.1
and 7.3 are repo-derived ordinary deductions. The signed decision and
productive finite-source conclusion of Theorem 7.3 quantify only over
the concrete record classes $\mathsf{Desc}_i,\mathsf{Desc}_j$; their
semantic points are denotations of those data. Theorem 7.4 records
their exact change to the supplied-certificate premise. No literature
novelty or priority claim is made. The following references are used
only at the indicated mathematical interfaces.

| Supplier | Exact use in this volume | Boundary retained |
| --- | --- | --- |
| [NCC, Corollary 6.1][NCC] | Unique semantics, graph-based finite/infinite tags and the effective prefix interface for the actual system/output witnesses in Definition 7.2 | No effective representation of arbitrary semantic points, description completeness or equality-proof-language completeness |
| [NCC, Definition 2.2 and Theorem 4.1][NCC] | Exact finite freezing, joint scalar support and coordinate closure iff Cof | Separate rank unboundedness and a freely varying finite residual do not suffice |
| [NCC, Theorem 5.2][NCC] | Both original-source contact directions for the same complete labelled chart pair | Its semantic closure points are not asserted to be denotations of records in Definition 7.2 |
| [PDC, Theorem 5.2 and §§6–8][PDC] | Whole original domain, complete positive/guard elimination, full Cartesian negative charts, exterior and all row fields | No representative, completion section or convenient subdomain replaces the source domain |
| [URR, Corollary 3.2][URR] | Effective exact Presburger support after finite-residual substitution | One tuple satisfies all negatives; it is not the whole chart or one common witness for every changing prefix |
| [NLC, Theorem 11.3 and Proposition 12.2][NLC] | Actual completed native operation and scope evidence for finite interpreted nonregular descriptions | Its native K and parameterized H constructions are already owned results; the general parameterized class is not translated here |
| [Böhm–Göller–Jančar, arXiv:1301.2181v1, Appendix, PDF pp. 23–24][BGJ] | Literature-attested decidability of classical deterministic one-counter language equivalence, with epsilon/input exclusivity, unit updates, zero/positive tests, counter-zero initialization and arbitrary nonnegative final counter | Its normalized trace theorem is reached through the Appendix's classical reduction; no native compact-input complexity transfer |

The construction treats interpreted $\rho$, not a free ranked unary
constructor. It therefore does not appeal to a generic regular-tree
equality theorem or an uninterpreted recursive-scheme solution theorem
in place of Theorem 4.1. Ordinary constructor regularity is not a
restriction here: the already supplied interpreted K of NLC12.2 is
within the nullary pair-guarded input class although NLC11.3 proves
its nonregularity. This is scope evidence, not another proof of that
tree or its prescribed-pair contact.

**Convention 8.2 (binding finite-source counterexamples).**
[NCC, Theorem 8.1][NCC] remains a counterexample to accepting only
productive common positive descriptions and source-valid approximants:
those approximants can have a third full row and miss both prescribed
labels. The present test preserves its decisive failed cofinality
condition after exact finite freezing. [NCC, Theorem 8.2][NCC] also
retains the necessity of independent private finite completion holes
and exact finite residual values. Output equality alone establishes
none of those finite realization conditions.

**Open problem 8.3 (description completeness, synthesis and outer
stopping).** For arbitrary nonempty acquired signed source fibers
(NGE.14) and arbitrary finite prefix-free original $Q$, the general
goal remains to decide

$$
\exists H\in\mathbb N\quad
\forall u,v\in D\quad
u\sim_H v\ \Longrightarrow\ R_Q(u)=R_Q(v),
\tag{NGE.22}
$$

with both a positive finite determining depth and its authorized paid
actual consumer, or a terminating negative decision or exactly justified
finite-source countercertificate productive at every requested depth.
All original records, complete state and operations remain part of that
goal. The following obligations are not discharged by supplied-data
equality or Theorem 7.3:

1. Every true prescribed-pair contact has cofinal points with equal
   outputs by [NCC, Theorem 5.2][NCC], but no theorem here supplies records
   of Definition 7.2 denoting those points. The existence of semantic
   witnesses does not furnish their finite descriptions or effective prefixes.
2. There is no synthesis method or exhaustive terminating search over
   all descriptions, all chart points, all finite residual values or
   all finite scalar ranks. Enumerating successful candidates need
   not give a negative stop.
3. Equality of arbitrary completed native trees or of broader interpreted
   parameter-recursive descriptions is outside Theorem 5.1.
4. The finite full-row-image case still requires the unrestricted
   distinct-label contact/exclusion decision of PDC(23). Testing one
   supplied pair or a finite candidate list does not settle it.
5. Fixed-depth decisions, finite chart families, finite row image and
   successive depth searches do not by themselves decide (NGE.22).

The general signed goal has not been replaced by the supplied description
class. A coordinate point or automaton is an offline mathematical object,
not an original source register or physical observer operation. No
observer equality port, reset, inverse update, source/chart selector,
hidden control access or paid receipt follows from these theorems.
Nor is a general complexity, undecidability or programme-completion
claim part of their conclusion.

[NCC]: https://github.com/the-omega-institute/trureturing/blob/0487ddfee131db56e40b654fad5a69689948e3c7/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CHART_CLOSURE.md
[PDC]: https://github.com/the-omega-institute/trureturing/blob/5f6e4c682e3e92206e00b81be891b30e35a25f1b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_POSITIVE_DOMAIN_CORRESPONDENCE.md
[NLC]: https://github.com/the-omega-institute/trureturing/blob/a5680221ab72e9a913651087bc74d21de1109933/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[URR]: https://github.com/the-omega-institute/trureturing/blob/cdf8955c35033409ca3e51aa485794bf57a78723/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[BGJ]: https://arxiv.org/pdf/1301.2181v1
[BGJDOI]: https://doi.org/10.1145/2488608.2488626

## 追加锚（本行以下为增补区）
