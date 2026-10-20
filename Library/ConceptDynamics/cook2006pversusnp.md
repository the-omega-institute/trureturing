---
bibkey: cook2006pversusnp
authors: Stephen Cook
year: 2006
title: 'The P versus NP Problem'
doi: null
url: https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf
claim: Polynomial checking relations define NP through bounded existential witnesses, and P equals NP would give polynomial algorithms for their associated search problems.
strata_touched: []
license: citation-only
triage: anchor
---

# Bounded certificate completion, search and a fixed oracle

**Definition 1 (Source scope and model).** The primary exposition at https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, PDF pp. 1–2, gives polynomial-time machines, checking relations and the existential certificate definition of NP; p. 5 explains decision-to-search and the consequence of $P=NP$ for every NP search relation. The following is a complete elementary reformulation of those mechanisms, with an explicit fixed oracle and prefix address. It is supporting literature exposition, not a solution of ordinary $P=NP$. The diagonal and space-oracle propositions below are proved from their definitions; their particular formulations are not attributed to this source.

Fix one oracle language $O\subseteq\{0,1\}^*$. All deterministic deciders, nondeterministic machines, verifiers and function programs use this same $O$. Queries cost their ordinary writing and reading work and one oracle-answer step. $\mathrm P^O$, $\mathrm{NP}^O$ and $\mathrm{FP}^O$ use ordinary uniform machines with polynomial runtime in total input length; function programs are total. Encodings of tuples and machines are fixed, efficiently parsed and of polynomial length. Malformed encodings are rejected or assigned the explicitly stated default. No completion table is included in $O$ unless explicitly named.

## 1. Prefix completion and exact growth

**Definition 2 (Fixed-length certificates).** Let $R(x,w)\in\{0,1\}$ be a total verification relation, and $m:\mathbb N\to\mathbb N$ a length function. For $|u|\le m(|x|)$ put

$$
\mathcal F_R(x,u)=\{v\in\{0,1\}^{m(|x|)-|u|}:R(x,uv)=1\},
\qquad H_R(x,u)=\mathbf1_{\mathcal F_R(x,u)\ne\varnothing}.
\tag{1}
$$

For overlong prefixes both the set and $H_R$ are empty or zero respectively. A semantic table (1) exists as a set function even when it has no efficient implementation. State addresses are $(x,u)$ with update $U((x,u),b)=(x,ub)$.

**Proposition 1 (Finite Bellman table, total selector and both answers).** At full length $H_R(x,w)=R(x,w)$. For $|u|<m(|x|)$,

$$
\mathcal F_R(x,ub)=b^{-1}\mathcal F_R(x,u),\qquad
H_R(x,u)=H_R(x,u0)\lor H_R(x,u1).
\tag{2}
$$

The boundary values and (2) uniquely determine the table. Define the total bit-valued selector by

$$
\pi_R(x,u)=\begin{cases}
0,& |u|<m(|x|),\ H_R(x,u0)=1,\\
1,& |u|<m(|x|),\ H_R(x,u0)=0,\\
0,& |u|\ge m(|x|).
\end{cases}
$$

Let $G_R$ append this bit at nonterminal prefixes and fix all terminal or overlong ones. Then

$$
H_R=H_R\circ G_R.
\tag{3}
$$

Starting at $(x,\varepsilon)$, after exactly $m(|x|)$ appends the resulting $w_*$ satisfies

$$
H_R(x,\varepsilon)=R(x,w_*).
\tag{4}
$$

Proof. Every nonempty residual certificate starts with exactly one of zero and one, giving (2) and its left-residual identity. Backwards induction on $m(|x|)-|u|$ proves uniqueness. If the zero child has value one, the parent does too and zero preserves it. Otherwise the parent's value equals the one child's value, so one preserves it. Fixed states give (3) globally. Every append lowers the nonnegative remaining-length rank by one, so (3) telescopes to the full-length boundary (4). If no witness exists, every selected residual has value zero and the final verifier rejects. If $m(|x|)=0$, (4) is already the root boundary with no append. This is a total decision construction, not only positive-instance witness production. $\square$

## 2. Four equivalent closure statements

**Proposition 2 (Projection, next-bit selection and bounded universal acceptance).** For this same fixed $O$, the following four assertions are equivalent.

A. $\mathrm P^O=\mathrm{NP}^O$.

B. For every fixed $V\in\mathrm P^O$ and every polynomial integer bound $p$, the language

$$
L_{V,p}=\{x:\exists y,\ |y|\le p(|x|),\ V(x,y)=1\}
\tag{5}
$$

belongs to $\mathrm P^O$.

C. For every fixed total Boolean $R\in\mathrm P^O$ and every polynomially bounded, polynomial-time computable $m$, there is a total bit function $\pi_{R,m}\in\mathrm{FP}^O$ such that

$$
H_R(x,u)=H_R(x,u\pi_{R,m}(x,u))
\quad\text{for all }|u|<m(|x|).
\tag{6}
$$

D. The one bounded universal acceptance language

$$
B_O=\{\langle e,x,1^t\rangle:
M_e^O(x)\text{ has an accepting execution of at most }t\text{ steps}\}
\tag{7}
$$

belongs to $\mathrm P^O$. Here $M_e$ is a nondeterministic oracle machine in a fixed explicit model; invalid codes are rejected and the horizon is unary.

Proof. A implies B because guessing the polynomial-length witness and running $V$ is an $\mathrm{NP}^O$ procedure.

For B implies C, encode $z=\langle x,u\rangle$ and verify the relation $S(z,v)$ which checks parsing, $|u|\le m(|x|)$, $|v|=m(|x|)-|u|$, and $R(x,uv)=1$. It is in $\mathrm P^O$, and the allowed $v$ length is bounded by a polynomial in $|z|$. Applying B gives the language $H_R(x,u)=1$ in $\mathrm P^O$. Boundary tests and one call on $(x,u0)$ implement Proposition 1's selector, with default zero on invalid or terminal input. Thus (6) holds and the selector is total in $\mathrm{FP}^O$.

For C implies A, take $L\in\mathrm{NP}^O$. Its verifier definition gives a fixed $V\in\mathrm P^O$ and polynomial $p$ with (5) defining $L$. Convert variable-length witnesses into length $m(|x|)=p(|x|)+1$ strings by

$$
\operatorname{pad}_{p,x}(y)=y1\,0^{p(|x|)-|y|}.
\tag{8}
$$

Decode the final one as the separator, keeping the preceding prefix as $y$; all-zero and wrong-length words reject. Every $|y|\le p(|x|)$ has exactly this valid encoding, and every valid fixed-length encoding decodes to a witness within the bound. Running $V$ after decoding gives a total $R\in\mathrm P^O$. Its root completion bit is $\mathbf1_L(x)$.

Apply C at each successive prefix for $m(|x|)$ iterations. Each selector input has length $O(|x|+m(|x|))$ and there are polynomially many calls. The fixed selector program therefore computes $w_*$ in polynomial time with the same oracle. The final $R(x,w_*)$ equals the root bit by repeated (6), on both yes and no instances. Thus $L\in\mathrm P^O$; the opposite containment is obtained by a nondeterministic machine with one choice.

For A implies D, a nondeterministic universal machine guesses at most $t$ transition choices and simulates the coded machine for $t$ steps, answering its actual queries using the same $O$. A branch index uses at most polynomially many bits in $|e|$. Universal configuration updates, table decoding and query copying take polynomial time in $|e|+|x|+t$, including immediate acceptance at $t=0$. The unary horizon makes this polynomial in input length, so $B_O\in\mathrm{NP}^O$ and A gives D.

For D implies A, any $L\in\mathrm{NP}^O$ has a fixed machine code $e$ and polynomial clock $p$. The mapping $x\mapsto\langle e,x,1^{p(|x|)}\rangle$ is polynomial-time computable and preserves membership in $L$ and $B_O$. A deterministic $\mathrm P^O$ decider for the latter decides $L$. This proves all equivalences. $\square$

**Proposition 3 (Quantifier order and operational interpretation).** With $O=\varnothing$, Proposition 2 gives precisely

$$
P=NP\quad\Longleftrightarrow\quad
P\text{ is closed under polynomially bounded existential projection},
\tag{9}
$$

and equivalently the next-step condition C with quantifiers

$$
\forall R\ \forall m\ \exists\pi_{R,m}\ \forall x,u.
\tag{10}
$$

This is uniformity across all inputs for each fixed verifier and length, not a single efficient compiler with an unclocked arbitrary verifier as an input. Semantic existence of $H_R$ or a small encoding of one of its values does not establish C.

Proof. Substitution of the empty oracle gives (9), while the fixed parameters and machine in C give exactly (10). Definition 2 and Proposition 1 construct the semantic selector as a function from arbitrary completion bits. Membership in $\mathrm{FP}^O$ is the additional assertion that one fixed finite program computes it with polynomial resource bounds for all $x,u$. Proposition 2 proves that assertion equivalent to A; no step proves A without such an assumption. Statement D is a genuinely universal coded language, but has a supplied unary runtime horizon; its efficient evaluation is itself equivalent to A. $\square$

## 3. Unbounded evaluation and a consistent stronger interface

**Proposition 4 (No same-class unbounded universal evaluator).** There is no total Boolean $U\in\mathrm P^O$ such that, for every code $e$ of a total Boolean $\mathrm P^O$ program and all $x$,

$$
U(e,x)=M_e^O(x).
\tag{11}
$$

Proof. If such $U$ exists, the total program $D(x)=1-U(x,x)$ is in $\mathrm P^O$ because the pair encoding has polynomial length. Let $d$ be its code. Then (11) gives $U(d,d)=D(d)=1-U(d,d)$, impossible for a Boolean value. No behavior is required of $U(e,x)$ as a simulator of partial or nonpolynomial codes, so those exclusions do not remove this contradiction. In contrast, $B_O$ asks for bounded nondeterministic acceptance with a horizon, not (11). $\square$

**Definition 3 (Space-bounded ordinary-machine oracle).** For explicitly coded ordinary deterministic machines with a read-only finite input and one work tape, put

$$
O_{\rm sp}=\{\langle M,x,1^s\rangle:
M(x)\text{ accepts without exceeding }s\text{ work cells}\}.
\tag{12}
$$

A run that exceeds the budget, loops forever within it or halts rejecting is outside the language. Invalid encodings reject. This is a different, explicitly stronger basic interface.

**Proposition 5 (Space oracle completeness and relative equality).** Under polynomial-time many-one reductions, $O_{\rm sp}$ is PSPACE-complete, and

$$
\mathrm P^{O_{\rm sp}}=\mathrm{NP}^{O_{\rm sp}}=\mathrm{PSPACE}.
\tag{13}
$$

Proof. Let $N$ be the encoded input length in (12). A bounded configuration has a state, bounded input head, work head and at most $s$ work symbols from the explicitly encoded alphabet. Its encoding has polynomial length in $N$, and the number of configurations is at most $2^{q(N)}$ for one polynomial $q$. Simulate deterministically with that many steps, using a binary counter of $q(N)+1$ bits and the current configuration. Reject immediately upon an illegal budget violation. If no accept has occurred after the configuration bound, a bounded configuration repeats and the deterministic continuation can never first accept. This gives a polynomial-space decider, without a time-bound promise for the simulated $M$.

For any $L\in\mathrm{PSPACE}$ choose its fixed deterministic decider $M_L$ and polynomial space bound $p$. Then $x\mapsto\langle M_L,x,1^{p(|x|)}\rangle$ is a polynomial-time reduction to (12). This proves completeness and $\mathrm{PSPACE}\subseteq\mathrm P^{O_{\rm sp}}$.

Conversely a nondeterministic polynomial-time $O_{\rm sp}$ machine has polynomially long branches and queries. Deterministically enumerate all its finite choice strings using a polynomial-length counter. Simulate each branch in polynomial space and answer each query with the decider just constructed. A polynomial-size query needs polynomial space in the original input length, and this scratch is reused between calls and branches. Accept if any branch accepts, otherwise reject after the finite enumeration. Thus $\mathrm{NP}^{O_{\rm sp}}\subseteq\mathrm{PSPACE}$. The ordinary containment of deterministic in nondeterministic polynomial time completes (13).

The result exhibits a model in which the same permitted interface is closed under the bounded projections of Proposition 2. It supplies no efficient ordinary implementation of $O_{\rm sp}$ and hence no ordinary $P=NP$ conclusion. If an interface is enlarged, verifiers also gain its operations, so closure must be checked for that enlarged whole class; adding answers to old tasks alone does not prove it. $\square$

## 追加锚（本行以下为增补区）

## 4. Polynomial observer presentations of bounded completion tables

Throughout this section set $O=\varnothing$. Every verifier and every $\operatorname{Init}_R$, $\operatorname{Upd}_R$ and $\operatorname{Val}_R$ procedure is an ordinary uniform deterministic machine without oracle access; $P$ and $NP$ denote the ordinary unrelativized classes.

**Definition 4 (Polynomial observer presentation).** Let $R(x,w)\in\{0,1\}$ be a fixed deterministic polynomial-time verification relation and let $m$ be a polynomially bounded, polynomial-time computable certificate-length function. For every $|u|\le m(|x|)$ put

$$
H_R(x,u)=
\mathbf 1\left\{\exists z,\ |uz|=m(|x|),\ R(x,uz)=1\right\}.
\tag{14}
$$

An observer presentation for $(R,m)$ consists of fixed ordinary uniform deterministic procedures

$$
\operatorname{Init}_R,\qquad
\operatorname{Upd}_R,\qquad
\operatorname{Val}_R
$$

and addresses $a_u$ satisfying

$$
a_\varnothing=\operatorname{Init}_R(x),
\qquad
a_{ub}=\operatorname{Upd}_R(x,a_u,b),
\qquad
\operatorname{Val}_R(x,a_u)=H_R(x,u)
\tag{15}
$$

for every legal prefix $u$ and $b\in\{0,1\}$ with $|ub|\le m(|x|)$. The address length, initialization, one-bit update, one evaluation, and all input-dependent preparation or compilation material are bounded by a polynomial in $|x|+|u|$. Terminal prefixes $|u|=m(|x|)$ are included, so $\operatorname{Val}_R(x,a_u)=R(x,u)$. The empty prefix is included; if $m(|x|)=0$, the initialized address is already terminal. No precomputed table is supplied for free.

**Theorem 5 (Observer presentation equivalence).** The following are equivalent:

$$
\boxed{
P=NP
\iff
\text{every polynomial-time bounded verification relation }(R,m)
\text{ has a polynomial observer presentation.}
}
\tag{16}
$$

The quantifier is per fixed relation and length function:

$$
\forall R\ \forall m\ \exists
(\operatorname{Init}_R,\operatorname{Upd}_R,\operatorname{Val}_R)
\ \forall x,u.
\tag{17}
$$

It does not assert one compiler that receives an unclocked arbitrary program as input, and it does not assert that the semantic table is small without the stated address and preparation bounds.

Proof. Assume observer presentations exist. For an $NP$ language represented by $R$ and $m$, compute the initialized address $a_\varnothing$ and return

$$
\operatorname{Val}_R(x,a_\varnothing)=H_R(x,\varnothing)
=\mathbf 1\{\exists w,\ |w|=m(|x|),\ R(x,w)=1\}.
$$

Initialization and evaluation, including their input-dependent preparation, are polynomial-time by Definition 4. Hence the language is in $P$, so $NP\subseteq P$; the reverse containment is standard. This direction uses only the root address and value, so an update procedure is redundant for the implication but remains part of the observer-presentation contract.

Conversely assume $P=NP$. For fixed $R,m$, define

$$
L_R^{\mathrm{pref}}
=
\{(x,u):|u|\le m(|x|),\
\exists z,\ |uz|=m(|x|),\ R(x,uz)=1\}.
\tag{18}
$$

This is in $NP$: a witness is the completion $z$, whose length is polynomial in the input length, and verification parses $(x,u,z)$ and runs $R$. Hence $L_R^{\mathrm{pref}}\in P$ under the assumption. Let $D_R(x,u)$ be a polynomial-time decider for it. Use the address $a_u=u$, initialize with the empty word, and update by concatenation,

$$
\operatorname{Init}_R(x)=\varepsilon,
\qquad
\operatorname{Upd}_R(x,u,b)=ub.
\tag{19}
$$

For legal nonterminal prefixes set

$$
\operatorname{Val}_R(x,u)=D_R(x,u),
$$

and for terminal prefixes use the same decider, which equals $R(x,u)$ because the completion $z$ is empty. Return zero on overlong or malformed addresses. Since $|u|\le m(|x|)$ is polynomially bounded, all three procedures have a uniform polynomial bound in $|x|+|u|$, including the address construction and validation. Equations (14)–(15) follow, including empty and terminal prefixes. Thus an observer presentation exists for every fixed $(R,m)$. $\square$

**Corollary 6 (Scope of the equivalence).** The equivalence in (16) identifies a precise uniform completion-table condition with the ordinary class equality. It gives no construction of the presentations without the assumption $P=NP$, no claim that a supplied finite table is cheaply obtainable, and no resolution of ordinary $P$ versus $NP$.

Proof. The forward implication of Theorem 5 uses the assumed decider for the prefix language, while the reverse implication uses an already supplied presentation. Removing either assumption would change the quantifier or resource contract in Definition 4. $\square$

## 追加锚（本行以下为增补区）

## 5. Explicit NOR circuits and boundary tasks

**Definition 5.1 (Classical circuit specialization and encoding).** In §§5–9 all machines are ordinary uniform deterministic or nondeterministic machines, with no oracle. The source premises are Cook's checking-relation definition on PDF pp. 1–2, polynomial reductions and NP-completeness on pp. 4–5, SAT and 3-SAT completeness on p. 5, and the decision-to-search construction on p. 5 of the [Clay exposition](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf). The NOR identities, circuit translations, clause-compatibility reduction and order normal form below are classical Boolean and decision/search mechanisms written out for this circuit language. Their notation is an elementary reformulation, not an additional result attributed verbatim to Cook, and not a proof of $P=NP$.

A well-formed circuit $\mathcal C$ explicitly lists all $m$ distinct primary input names in the order $w_1,\ldots,w_m$, constant nodes labelled zero or one, a finite list of two-input NOR gates, and one designated output signal. Every gate has two ordered input references and one fresh output name. Each internal signal has exactly one producer. References may point to primary inputs, constants or preceding gates in a supplied topological order. Equivalently, a supplied order of an explicit DAG is checked against all its edges before use. All references must be valid; names cannot be silently identified. A signal may have arbitrary fan-out or occupy both input ports of a gate. These are permissions of this explicit circuit model.

The binary encoding includes the entire input-name list, all nodes, references and output; write its length as $N$. Choose an encoding with $m\le N$, even for unused inputs, so a binary declaration of a large input count without its names is invalid. Parsing, checking uniqueness and checking the supplied order are polynomial-time operations on this explicit encoding. Malformed circuits reject in every language below. The total verifier $R_{\mathcal C}(w)$ returns zero on malformed circuits or words not in $\{0,1\}^m$; otherwise it evaluates the gates and returns the output bit. Constant-only circuits are allowed and have $m=0$. An input pin is an additional explicit equality to a bit, checked on the same assignment; conflicting pins reject, and the verifier returns zero on every assignment violating a supplied pin. Output forcing is a boundary requirement on the designated signal, not a new deterministic gate operation.

**Proposition 5.2 (NOR expressions and the meaning of a binary basis).** Put $x\downarrow y=\neg(x\lor y)$. Then

$$
\neg x=x\downarrow x,\qquad
x\lor y=(x\downarrow y)\downarrow(x\downarrow y),\qquad
x\land y=(x\downarrow x)\downarrow(y\downarrow y).
\tag{20}
$$

Consequently every finite AND/OR/NOT circuit can be translated to this NOR model with constant-factor gate overhead and the same input/output function. If only unary gates, constants and wires are allowed, every output depends on at most one primary input; hence such a basis cannot express binary AND. NOR attains the necessary maximum arity two in this restricted comparison.

Proof. The first equality negates $x\lor x=x$. Applying the same equality to $x\downarrow y$ gives the second. De Morgan's law gives the third. Direct evaluation on the four pairs $(x,y)$ proves all three without a historical-priority premise. Replace each original gate by its displayed finite gadget, in original topological order. Connecting a gadget's output to every original use preserves fan-out and keeps all occurrences of an input equal. Induction on this order proves equality of all original signals and designated outputs. The construction is acyclic and polynomial in the original encoding length, including references and the output order.

For the arity statement, an input wire depends on its one named variable and a constant on none. A unary function of a signal depends only on that signal's dependency set, which has size at most one by induction. Fan-out does not join two dependency sets. Binary AND depends on both variables: changing either can change the output with the other fixed to one. Thus unary gates cannot express it. This is a statement about allowed circuit gates, not about physical primitives or native FIB wiring. $\square$

## 6. Completion and cardinality with classical reductions

**Theorem 6.1 (Evaluation and output-one completion).** Let

$$
\mathrm{NOR\text{-}COMP}
=\{\mathcal C:\mathcal C\text{ is well formed and }
\exists w\in\{0,1\}^m, R_{\mathcal C}(w)=1\}.
\tag{21}
$$

Fully specified input evaluation is deterministic polynomial time, with one Boolean operation per gate after parsing. Language (21) is NP-complete under polynomial-time many-one reductions, even when the topological order is part of the input. A total polynomial verifier can check a proposed full completion, including pins and all internal signals if these are supplied as an additional certificate.

Proof. Every gate has fixed operands by the time it is visited. Computing each gate once gives the unique internal assignment. The Boolean work is linear in gate count; scanning or indexing explicitly encoded references on a standard Turing machine still costs a polynomial in $N+|w|$. The witness in (21) has length $m\le N$ and is checked by this total procedure, so (21) is in NP. Supplying the internal values as well merely adds polynomially many bits and checks: each equality is evaluated on the same global assignment and compared to its unique producer.

Use Cook's p. 5 NP-completeness of 3-SAT as the hardness premise. Parse a formula, retain one named input for each of its distinct variables, and build the literal NOT gates, disjunctions for clauses, and a conjunction of their outputs. Names are renumbered by syntactic occurrence, not by their numeric magnitude. Repeated literals reference the same input. Binary trees of AND and OR gates suffice; size is linear in literal occurrences before encoding references. Translate by (20), retaining a topological order. For every assignment $w$,

$$
R_{\mathcal C_\varphi}(w)=\varphi(w),\qquad
\varphi\text{ satisfiable}\iff\mathcal C_\varphi\in\mathrm{NOR\text{-}COMP}.
\tag{22}
$$

Empty conjunctions give a constant-one output and empty clauses give constant zero, if these additional CNF cases are admitted. A malformed formula maps to a fixed valid constant-zero circuit, making the reduction total on binary strings. Circuit construction, including its order, has polynomial encoding length and runtime. Thus hardness remains when the evaluation order is already supplied. Pins do not weaken hardness because the construction needs none. Constant-only circuits are evaluated on the unique empty word, so the proof includes $m=0$. $\square$

**Definition 6.2 (Original five-state edge network).** Let

$$
\Sigma=\{(x,y,z)\in\{0,1\}^3:xz=yz=0\}.
\tag{23}
$$

An explicit edge-network instance supplies a finite simple graph $G=(V,E)$, one named Boolean variable $u_v$ per vertex, and a signed binary integer $K$. A fixed canonical orientation of each edge $\{v,w\}$ supplies the unit $(x,y,z)=(u_v,0,u_w)$. Every occurrence of $u_v$ refers to this one vertex variable. Zero pins are an explicit extra permission. The goal is legality of every unit together with

$$
\sum_{v\in V}u_v\ge K,
\tag{24}
$$

counting each vertex once. A malformed graph, duplicate vertex name, loop, bad reference or malformed integer encoding rejects. Empty graphs are valid. Signed thresholds avoid an implicit positive-threshold promise: $K\le0$ always admits the all-zero assignment, and $K>|V|$ never admits one.

**Theorem 6.3 (Threshold completion and its classical clause graph).** The language in Definition 6.2 is NP-complete. The result uses arbitrary shared-variable edge networks and the global cardinality goal; the relation (23) by itself, with only pins, has polynomial-time satisfiability.

Proof. Each edge unit imposes precisely $u_vu_w=0$, since its other product is zero. Thus the support $S=\{v:u_v=1\}$ is an independent set, and (24) says $|S|\ge K$. Guessing the explicit vertex bit list, checking every edge and comparing the binary count with $K$ is polynomial in the complete input length, so the language is in NP. The count needs only $O(\log(|V|+1))$ bits; no iteration up to the numerical value of $K$ occurs. For $V=\varnothing$ its value is zero.

For hardness, the standard clause-compatibility graph construction can be verified directly from Cook's 3-SAT premise. For a formula with $r$ clauses, create a separate vertex for each literal occurrence. Make every clause's vertices a clique, and join every pair of occurrences that are complementary literals of the same variable. Retain only one edge per pair and set $K=r$. There are polynomially many vertices and at most quadratically many edges.

A satisfying assignment supplies one true occurrence from each clause. Chosen occurrences are in different clause cliques and none are complementary, so they form an independent set of size $r$. Conversely any independent set contains at most one vertex per clause. Size at least $r$ therefore means exactly one per clause. No two selected literals are complementary, so there is a consistent assignment making every selected literal true; freely extend it to the other variables. Every clause is satisfied. Repeated literals and tautological clauses do not change either argument. An empty clause, when allowed, has no vertex, so no size-$r$ set is possible; the empty conjunction has $r=0$ and the empty set works. Malformed formulas map to the valid empty graph with $K=1$, a fixed NO instance. This is a total polynomial reduction. Composing with the edge units proves NP-hardness of the exact network language. The independent-set correspondence and compatibility-graph proof are classical reduction exposition, not a new complexity classification claimed for the literature.

Finally, an arbitrary collection of original units (23) gives only pairwise exclusions between their actual $x,z$ and $y,z$ variables. Check conflicting pins and whether any exclusion has both variables pinned to one. If none does, leave the one pins and set every unpinned variable to zero. This satisfies all exclusions. A repeated port that yields $u^2=0$ is handled by the same check. Thus pins and the original local relation have a simple satisfiability algorithm; adding (24) changes the task. $\square$

**Proposition 6.4 (Verification graph and constraint graph).** A verification DAG for Theorem 6.3 may be acyclic even when the variable constraint graph has cycles and many overlapping scopes. A known topological evaluation order does not remove the existential quantifier in (21) or (24).

Proof. A verifier first reads the proposed assignment, computes the edge-product tests and the count, and combines their results. These operations can be arranged in successive layers with no back edge for every finite graph $G$. The edges of $G$ instead connect variables that appear in the same exclusion; they need not follow the verifier's operation layers. The reduction in Theorem 6.1 explicitly supplies an evaluation order while preserving SAT. This proves the distinction without a claim that membership in P would exclude NP-hardness. The fixed-DAG work invariant and the difference from variable elimination are detailed in [Bryant §1](bryant1986boolean.md#1-three-orders-and-the-cost-of-a-fixed-pure-dag). $\square$

## 7. Whole-prefix fibres, prediction and terminal growth

**Definition 7.1 (Completion fibres of the explicit circuit language).** For a well-formed circuit with the full input list of Definition 5.1 and a legal prefix $b\in\{0,1\}^{\le m}$, define a set of complete words, rather than only a summary of the last observed bit:

$$
\Omega_{\mathcal C}(b)
=\{w\in\{0,1\}^m:b\preceq w,\ R_{\mathcal C}(w)=1\},
\qquad
E(\mathcal C,b)=\mathbf1[\Omega_{\mathcal C}(b)\ne\varnothing].
\tag{25}
$$

For malformed circuits, nonbinary or overlong prefixes set $\Omega=\varnothing$ and $E=0$. At a nonterminal prefix $|b|<m$, put

$$
\Lambda_{\mathcal C}(b)=\{a\in\{0,1\}:E(\mathcal C,ba)=1\},\qquad
\operatorname{Predict}(\mathcal C,b)=(E(\mathcal C,b0),E(\mathcal C,b1)).
\tag{26}
$$

The address of each semantic query is the complete pair $(\mathcal C,ba)$. Growth chooses $b0$ if its bit is one, otherwise $b1$ if its bit is one, otherwise returns failure $\bot$. At a full-length prefix it makes no successor query: it halts with that word exactly if $R_{\mathcal C}(b)=1$, and otherwise rejects. Invalid inputs reject immediately. Prediction at terminal or invalid states can have a fixed distinguished terminal or invalid tag; it is not interpreted as permission to append a bit.

**Proposition 7.2 (Exact prediction/growth and both boundary answers).** For every nonterminal legal prefix,

$$
\Omega_{\mathcal C}(b)
=\Omega_{\mathcal C}(b0)\mathbin{\dot\cup}\Omega_{\mathcal C}(b1),
\qquad
E(\mathcal C,b)=E(\mathcal C,b0)\lor E(\mathcal C,b1).
\tag{27}
$$

If the starting fibre is nonempty, exact growth never fails and yields an accepted complete word in at most $m-|b|$ appends. With a root query, the procedure is total on both YES and NO instances: reject a zero root, and otherwise grow and finally verify. On a constant-only circuit it performs the root/terminal verification on the empty word and no growth. This is the circuit instance of Proposition 1 and Cook's decision-to-search procedure.

Proof. Every complete word extending a nonterminal $b$ has a unique next bit, so (27) is an equality of disjoint sets of whole completions. A nonempty parent therefore has a nonempty child, and the prescribed rule selects such a child. Inductively the invariant is the nonemptiness of the entire current fibre, with all earlier bits retained. The remaining length drops by one per append. At full length the fibre is either the singleton consisting of that word or empty, and its indicator equals $R_{\mathcal C}(b)$. A zero root contains no accepted word; the initial rejection is therefore correct. Malformed inputs were already assigned rejecting behavior. When $m=0$ the root is terminal, so the same boundary equality handles constants. The statement charges at most $1+2m$ exact table queries and one final verification; it does not provide an ordinary efficient realization of each query. $\square$

**Proposition 7.3 (One next-step bit can encode the whole decision).** From any valid $\mathcal C(w)$ construct a circuit with a fresh first input $b$ and function

$$
\mathcal D(b,w)=b\land\mathcal C(w).
\tag{28}
$$

Then $E(\mathcal D,1)=1$ exactly when $\mathcal C\in\mathrm{NOR\text{-}COMP}$. This one-bit next-step permission query is NP-complete as a language of such circuit/prefix pairs.

Proof. Build the AND gadget of (20) after $\mathcal C$, with the same variables $w$ and fresh input $b$ first. Its size overhead is constant apart from the explicit reference encoding. Under $b=1$, (28) equals $\mathcal C(w)$ on every assignment, giving the equivalence. A malformed source maps to a valid constant-zero example. Membership follows by guessing the remaining $w$ and verifying. Thus Theorem 6.1 supplies hardness even for this particular one-bit prefix family. A bit's output length and its location before the remaining construction give no bound on the uniform cost of obtaining it. Likewise a short description of an auxiliary result need not provide a cheap method to acquire or confirm that result. $\square$

## 8. Uniform good-order compilation and the XOR normal form

**Definition 8.1 (A total efficient order compiler).** A description $d$ for a valid circuit with $m$ inputs determines a permutation

$$
\pi_{\mathcal C,d}:\{0,\ldots,2^m-1\}\longrightarrow\{0,1\}^m.
\tag{29}
$$

There must be fixed total deterministic algorithms $D,U$, fixed polynomials $p_D,p_U$, and a fixed positive integer-valued polynomial $q$, independent of $\mathcal C$. Algorithm $D(\mathcal C)$ produces $d$ in time at most $p_D(N)$, including every instance-dependent preparation step, and $|d|\le p_D(N)$. Algorithm $U(\mathcal C,d,k)$ on a binary index $k$ un-ranks (29) in time at most $p_U(N+|d|+|k|)$ for compiled descriptions. Indices outside $0\le k<2^m$ return a distinguished error; total polynomial behavior is required also on other input strings, with an arbitrary error or default there. This is algorithmic unranking, not random access to an exponentially materialized permutation. Every well-formed NO circuit also receives its description in polynomial time. A malformed circuit gives a rejecting tagged description, and the executor rejects it before enumeration.

For every YES circuit the hit guarantee is

$$
\exists k<\min\{q(N),2^m\},\qquad
R_{\mathcal C}(\pi_{\mathcal C,D(\mathcal C)}(k))=1.
\tag{30}
$$

The executor computes $D$, un-ranks and verifies these candidates, and rejects if all fail. Its total runtime on all inputs must be polynomial in $N$, with the costs of construction, description, address decoding, verification, index arithmetic and termination included. No witness or instance-dependent advice is a free input. For $m=0$, (29) has exactly one element, the empty word at index zero, and (30) requires that candidate when the constant output is one.

**Theorem 8.2 (Uniform order–completion equivalence).** The following ordinary unrelativized assertions are equivalent:

A. $P=NP$.

B. The total bit $E(\mathcal C,b)$ of (25) is computable by one deterministic polynomial-time algorithm on all pairs.

C. A compiler and executor satisfying Definition 8.1 exist.

Whenever they hold, C has the normal form $q(N)=1$, with an $m$-bit order parameter and XOR unranking. This is a decision/search consequence of Cook's p. 5 mechanism specialized to the explicit circuit verifier, not an unconditional construction of B or C.

Proof. For A implies B, parse the circuit and prefix and reject the invalid cases. Guess exactly $m-|b|$ further bits and verify $R_{\mathcal C}$ on their concatenation with $b$. Since $m\le N$, this is an NP language on the pair encoding. Under A it has a polynomial-time decider. All invalid, empty and full-length cases are included in the language definition, so extending its decider by the stated parsing convention gives a total B algorithm.

For B implies A, use the empty prefix. Its bit is precisely the NP-complete language (21). Thus $\mathrm{NOR\text{-}COMP}\in P$, and Cook's reduction principle on pp. 4–5 gives $P=NP$.

For B implies C, first reject malformed circuits by a tagged default. On valid circuits compute the root bit. If zero, take $w=0^m$; this is only a permutation parameter and is not claimed to be a witness. If one, Proposition 7.2 constructs an accepted $w$ using at most $2m$ further B calls and final verification. Every such query has encoding length polynomial in $N$, so the whole construction is polynomial on YES and NO inputs. In the zero-input case set $w=\varepsilon$.

Store the parameter $w$ (and its length), and for valid indices define

$$
\pi_w(k)=w\oplus\operatorname{bin}_m(k).
\tag{31}
$$

The fixed-width binary encoding includes leading zeroes. XOR with $w$ is its own inverse, so (31) is a permutation and $\pi_w(0)=w$. Binary range tests, padding and XOR take polynomial time, including scanning an overlong index to return an error. A fixed decoder can reject malformed descriptions and otherwise use (31), so its totality does not depend on solving an additional validity problem. On YES circuits candidate zero verifies, establishing $q=1$. On NO circuits it fails and the executor rejects. For $m=0$, $\operatorname{bin}_0(0)=\varepsilon$ and the one candidate is verified normally.

For C implies A, run the specified executor. An accepted candidate proves YES by verification. If none of the first $\min\{q(N),2^m\}$ candidates passes, (30) rules out YES, so rejection is correct on every well-formed NO circuit as well. The cutoff is computable by binary arithmetic without constructing the full permutation: loop at most $q(N)$ times and stop earlier on reaching $2^m$. Valid indices have at most $m+1\le N+1$ bits. For fixed polynomials, the cost is bounded by

$$
p_D(N)+q(N)\bigl(p_U(N+p_D(N)+N+1)+p_V(N)\bigr)
+\operatorname{poly}(N),
\tag{32}
$$

where $p_V$ includes total verification and input/output work; the final term covers the counters and syntax checks. This is polynomial even if $q(N)>2^m$, because the loop then stops at the smaller number. Malformed encodings reject in polynomial time. Thus (21) is in P, which implies A. This proves the equivalence and the normal form. $\square$

**Proposition 8.3 (Existence versus uniform acquisition).** Unconditionally, every satisfiable $\mathcal C$ has an $m$-bit description of a permutation whose first word is accepted:

$$
\forall\mathcal C\in\mathrm{NOR\text{-}COMP}\ \exists w\in\{0,1\}^m:
R_{\mathcal C}(\pi_w(0))=1.
\tag{33}
$$

This has different quantifiers from

$$
\exists D,U\text{ with the fixed polynomial bounds of Definition 8.1}\
\forall\mathcal C\text{ satisfying its hit and total-execution contract}.
\tag{34}
$$

The latter is equivalent to $P=NP$ by Theorem 8.2; (33) supplies no algorithm $D$.

Proof. For each YES circuit choose any accepted word $w$ and use (31). It is a short, efficiently decoded description once $w$ is supplied. This selection does not bound the cost of finding $w$ from $\mathcal C$. Statement (34) moves that choice into one fixed efficient procedure on every encoded instance and includes NO behavior, so it is exactly the additional uniformity requirement of C. At $m=0$ the unique word already gives the same distinction between constant verification and a general family. $\square$

## 9. Succinct observer compilation and the remaining open condition

**Definition 9.1 (Circuit observer compiler with a paid horizon).** An exact observer compiler receives a circuit encoding and produces a finite program/description and initial state. Every reached state represents a full chosen input prefix $b$, either literally or through a polynomial-time decoding; the circuit and all earlier chosen bits remain available. It provides the exact values (25)–(26), append updates at nonterminal states, and terminal verification/rejection. The compiled description, reached state encodings, initialization, preparation, next-query addressing, bit computation, updates, witness decoding and termination have fixed polynomial bounds in $N$. All runs, on YES, NO and malformed inputs, terminate within one fixed polynomial bound. An implementation using one-bit appends has at most $m$ growth steps; a different presentation must supply its own polynomial total-step bound. Complete tables are not free primitives. Succinct programs are allowed; there is no bound here on the number of semantic residual classes over all prefixes.

**Corollary 9.2 (The global completion-compiler question is exactly open P versus NP).** Existence of a compiler satisfying Definition 9.1 for every circuit is equivalent to $P=NP$, and hence to Theorem 8.2. This is the explicit-circuit specialization of Theorem 5's observer-presentation equivalence. It is not a new independent conjecture about a different class.

Proof. Such a compiler can initialize and evaluate the exact root bit in polynomial time, deciding the NP-complete language (21); alternatively its total successful/rejecting run decides the same language. Conversely B of Theorem 8.2 gives a presentation retaining $b$ itself, a fixed program for B, and ordinary concatenation updates. State size is at most $m\le N$ apart from the retained circuit and fixed code. Proposition 7.2 bounds the run and supplies terminal verification, while invalid encodings reject before initialization. All required costs are polynomial, so the presentation satisfies Definition 9.1.

Unlike a generic certificate convention in which $m$ must depend only on $|x|$, here $m$ is read from the explicitly supplied circuit input-name list. The proof above verifies that length directly and uses its bound $m\le N$; it does not substitute an instance-dependent $m$ into a length-only convention. For arbitrary fixed verification relations, the padding/decoding bridge (8) in Proposition 2 instead converts every length-at-most-$p(|x|)$ witness into the exact length $p(|x|)+1$, rejects the all-zero word, and preserves existence in both directions. These are two valid routes to the decision/search statement with their length assumptions explicit.

A small state/program for the current prefix does not assert a small exact-residual quotient for all prefixes. The grouped equality example already proved in [Dechter Proposition 4](dechter1996bucket.md#3-order-sensitivity-and-program-cost) has exponentially many distinct middle-cut residuals and nevertheless a polynomial-time next-bit selector. Explicit separator width and exact tables provide useful sufficient constructions under the hypotheses of that note, not necessary conditions for this general compiler contract. $\square$

**Definition 9.3 (AURIC specialization and task correspondence).** The port map, added nonempty rule, full input list, fan-out, repeated input, constant pins and output forcing are specified in [Selection Calculus §§15–16](../../docs/develop/theory/AURIC_FIB_ATOM_SELECTION_CALCULUS.md#十五附加非空规则的逻辑端口与全局补全). They transport (21), (25) and (29) pointwise to the extended pyramid circuits. Their original five-state threshold extension transports Definition 6.2 and its same-variable cardinality objective. Neither map is a native-chain universality statement.

The canonical FIB tree-sharing theorem of that source's §14 and its two-state locally restricted native chain of §16 supply separate sufficient mechanisms: equal pure subtrees share computations, and equal legality futures share seam states. The latter retains its endpoint and factorized-weight assumptions. Auxiliary structure can be assessed by the actual reduction in repeated pure work, joint separator information or task-future distinctions, together with its construction and use costs; a predecessor location and short description alone supply none of those cost bounds, as Proposition 7.3 shows.

[Finite-table classification §§6–7](../../docs/develop/theory/FIB_NATIVE_FINITE_TABLE_COMPLEXITY_CLASSIFICATION.md#6-actual-origin-boolean-banks-and-a-four-reply-cnf-compiler) uses a different native four-reply language: a stationary actual origin fixes each Boolean variable on repeated reads, all assignments have finite actual witnesses, and a CNF with $M$ occurrences compiles to an acyclic occurrence-evaluation fragment with all four reply edges supplied and at most $M$ paid Reads before reaching its supplied continuations. Its NP-complete BOTH-PREPARER slice can already use universally terminating acyclic preparers. These correspondences compare fixed-source evaluation with existential source attainment, without identifying its full language with (21). Its [Theorem 11.1](../../docs/develop/theory/FIB_NATIVE_FINITE_TABLE_COMPLEXITY_CLASSIFICATION.md#11-literally-fixed-acquired-tables-and-finite-cap-saturation) fixes the entire table and original entries and varies only a binary cap. That fixed-object P result provides no uniform preprocessing algorithm for varying tables, and therefore does not establish B, C or Definition 9.1 for the full circuit family.

## 追加锚（本行以下为增补区）

## 10. Zero-knowledge views and the causal information contract

The circuit language in §§5–9 supplies the public statement and the finite witness relation. A proof protocol adds a message interface and a probability space; it does not change the completion fibre.

**Definition 10.1 (Protocol view).** A prover receives $(x,w)$ and private randomness, while a verifier receives $x$, an explicitly declared auxiliary input and a random tape. The complete verifier view contains that tape, every message, public output, failure and termination flag, and any length or timing quantity visible through the interface. A protocol is complete and sound when its acceptance probabilities satisfy the stated bounds on YES and NO inputs. A zero-knowledge assertion is a distributional assertion about this complete view.

For a security parameter $1^n$, computational zero knowledge with auxiliary input means that for every probabilistic polynomial-time verifier $V^*$ there is one uniform expected-polynomial-time simulator $S_{V^*}$ such that, for every legal $(x,w)$, every allowed auxiliary input $\eta$, and every polynomial-time distinguisher $D$,

$$
\left|
\Pr[D(\operatorname{View}_{V^*}^{P(x,w)}(x,\eta))=1]
-
\Pr[D(S_{V^*}(x,\eta))=1]
\right|
$$

is negligible in $n$. Perfect and statistical variants replace computational indistinguishability by equality or negligible statistical distance. The simulator is not required to decide whether $x$ is in the language; the assertion is normally quantified over legal witnesses on YES inputs.

This map has output type

$$
 x\longmapsto \text{a verifier view},
\tag{35}
$$

whereas witness search has output type $x\longmapsto w\in W_x$. A simulator therefore supplies a completion algorithm only when an additional efficient postprocessor reads a simulated view and produces a valid witness with a stated probability. The definition itself supplies no such postprocessor.

## 11. The graph-isomorphism order test

For graphs $G_0,G_1$ of the same size, a witness is an isomorphism $\phi:G_0\to G_1$. The three-message protocol is:

1. choose a uniform vertex permutation $\pi$ and send $H=\pi(G_0)$;
2. receive a fresh uniform bit $b$;
3. send $\tau=\pi$ when $b=0$, and $\tau=\pi\phi^{-1}$ when $b=1$.

The verifier accepts exactly when $H=\tau(G_b)$. Permutations are sampled and represented in time polynomial in the graph encoding; a malformed graph is rejected before the protocol starts.

**Theorem 11.1 (Completeness, soundness, extraction and honest-verifier simulation).** The graph-isomorphism protocol has perfect completeness. If $G_0\not\cong G_1$, every causal prover whose first message is fixed before the challenge is accepted with probability at most $1/2$. If the same first message $H$ has accepting replies $\tau_0$ and $\tau_1$ to challenges zero and one, then

$$
\phi=\tau_1^{-1}\tau_0
\tag{36}
$$

is an isomorphism from $G_0$ to $G_1$. Against the honest verifier, a perfect simulator chooses $b$ and a uniform $\tau$, sets $H=\tau(G_b)$, and outputs $(H,b,\tau)$.

**Proof.** Honest substitution gives acceptance one. If a fixed $H$ answered both challenges, then $H=\tau_0(G_0)=\tau_1(G_1)$, so $G_1=\tau_1^{-1}\tau_0(G_0)$. Nonisomorphic graphs therefore permit at most one of the two answers for each fixed first message, giving soundness at most one half. The same equality proves (36). For honest verification, conditioned on either challenge the reply is uniform over the relevant permutation set; when the graphs are isomorphic, the simulator's distribution is exactly the honest one. This is honest-verifier perfect simulation; malicious-verifier zero knowledge requires an additional simulator argument and is not inferred from this paragraph. $\square$

The order is the quantifier difference

$$
\exists H\;\forall b\;\exists\tau_b: H=\tau_b(G_b),
\tag{37}
$$

versus separately choosing $H_b$ after seeing $b$. The first is equivalent to isomorphism, while the second is true for arbitrary graphs by taking $H_b=G_b$. A record generator that is told the challenge in advance therefore does not implement the causal protocol.

**Proposition 11.2 (Same-state fork requirement).** Suppose a saved prover state after the same first message $H$ can be challenged twice, with fresh independent verifier challenges, without changing the saved state before the second fork. If the prover succeeds on challenge $b$ with probability $p_b$ over its fixed private randomness, and its one-shot success is $\varepsilon=(p_0+p_1)/2>1/2$, then

$$
\Pr[A_0\cap A_1]\ge p_0+p_1-1=2\varepsilon-1.
\tag{38}
$$

On the intersection, (36) extracts an isomorphism. If $2\varepsilon-1$ is inverse polynomial and each fork costs polynomial time, independent repetitions give expected polynomial extraction time. When a repetition must recreate the saved state from the public instance, it must independently rerun the prover's initialization and first-message procedure, restore the same forkable state, and count that initialization and restoration cost in the repetition bound; the fork hypothesis alone does not make state preparation free. Two transcripts with different first messages, or two independently simulated records, do not meet the premise: their events are not defined on one saved state and (36) need not be valid.

This is the exact causal resource needed by a knowledge extractor. It is stronger than a single-view simulator and also stronger than having the same marginal distribution for two separately generated records.

## 12. A single simulated view can imply randomized witness search

**Definition 12.1 (Single-view postprocessor contract).** Let $R(x,w)$ be a polynomial-time relation with witness length bounded by a polynomial. A postprocessor receives $x$ and one view sampled from a simulator, but has no prover code, trapdoor, reset access, hidden verifier tape, or second correlated view. It runs in polynomial time after a strict polynomial cutoff for the simulator. Public auxiliary input may be included only when it is generated and counted by the same algorithm.

**Theorem 12.2 (View-to-witness postprocessing).** Assume a uniform expected-polynomial-time simulator $S$, with a uniform strict polynomial cutoff on every input, and a postprocessor $E$ such that for every YES instance $x$,

$$
\Pr[E(x,S(x))\in W_x]\ge\frac1{q(|x|)}
\tag{39}
$$

for a fixed positive polynomial $q$. Suppose the relation verifier is polynomial and $E$'s output is finally checked. Then the language is in $RP$. On NO inputs the algorithm never accepts, regardless of the simulator's output.

**Proof.** Let $p(n)$ be a uniform bound on the simulator's expected running time on every input, and choose the strict cutoff $T(n)=2p(n)q(n)$ (rounded up). Markov's inequality makes the timeout probability at most $1/(2q(n))$, so the inverse-polynomial success in (39) loses at most half its margin. Run the truncated simulator, apply $E$, and verify its output. Repeat $O(q(n)\log q(n))$ times, or any fixed polynomial amplification schedule, to raise the YES probability above $1/2$. A NO instance has no valid output in $W_x$, so final verification makes its acceptance probability zero. All simulator, postprocessor, repetition and verification costs are included in the uniform bound. $\square$

The theorem is a statement about one simulated view. It cannot use the same-state fork of Proposition 11.2, because a single view contains only one challenge branch. Conversely, same-state extraction can be useful even when no one-view postprocessor exists.

## 13. Online substitution and the BPP/RP distinction

An **online substitute** is a uniform probabilistic machine that receives only the public instance (and explicitly public auxiliary input), follows the real message schedule, uses its own fresh random coins, and emits legal messages without a witness or a simulator-only reset. Its initialization, every message, all state updates and termination have one fixed polynomial total-time bound on YES, NO and malformed inputs; the verifier's parsing, challenge, response checking and final decision have the same kind of uniform bound. If on every YES instance the resulting verifier accepts with probability at least $2/3$, while soundness on NO instances remains at most $1/3$, then the language is in $BPP$: run the substitute and the verifier once, then amplify. This is an actual online proving algorithm, not merely a distributional simulator.

For the explicit NOR completion language, a stronger prefix interface gives an RP consequence. Suppose a BPP procedure answers every prefix query $\operatorname{Ext}(\mathcal C,b)$ with error at most $1/(12m+12)$, uniformly for all legal prefixes, and terminates in polynomial time on malformed and NO inputs. Assume also that the gate evaluator and final verifier parse, check and terminate in a uniform polynomial time on YES, NO and malformed circuit/word encodings. Use the prefix procedure to select one child at each prefix, amplify or repeat the queries, and finally verify the resulting word. The union bound over at most $m$ queries gives an inverse-constant probability of an entirely correct path; final verification removes false positives. Thus the NP-complete completion language is in $RP$, yielding $NP=RP$. A single average-case query guarantee or a per-instance simulator whose public input already contains the selected prefix does not satisfy this prefix contract.

## 14. The plain-model one-message consequence

The following restricted theorem is the relevant single-message boundary. There is no CRS, programmable random oracle, setup trapdoor or verifier randomness chosen before the proof string.

**Theorem 14.1 (Single-message plain-model ZK implies BPP under strict soundness).** Let a protocol send one proof string $\pi$ before the verifier samples its independent random tape $r$. Assume, for security parameter $1^n$:

1. the verifier parses and terminates in a uniform polynomial time on YES, NO and malformed inputs;
2. for every YES input and legal witness, honest completeness is at least $2/3$;
3. for every NO input and every proof string $\pi$, $\Pr_r[V(x,\pi;r)=1]\le1/3$;
4. a uniform expected-polynomial-time simulator produces a first-message marginal computationally indistinguishable from the honest proof-string marginal on every YES input, with an all-input strict polynomial truncation and public auxiliary inputs included in the input length.

Then the language is in $BPP$.

**Source anchors for the protocol claims.** The auxiliary-input and black-box distinctions, including the one-message triviality boundary used here, are attributed to Goldreich and Oren, *Definitions and Properties of Zero-Knowledge Proof Systems*, Journal of Cryptology 7 (1994), 1–32, [author copy](https://www.wisdom.weizmann.ac.il/~oded/PSX/oren.pdf). The graph-isomorphism protocol, the NP zero-knowledge construction under cryptographic assumptions, and the distinction between simulation and witness revelation are attributed to Goldreich, Micali and Wigderson, *Proofs that Yield Nothing But Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems*, Journal of the ACM 38 (1991), 691–729, [paper](https://people.csail.mit.edu/silvio/Selected%20Scientific%20Papers/Zero%20Knowledge/Proofs_That_Yield_Nothing_But_Their_Validity_or_All_Languages_in_NP_Have_Zero-Knowledge_Proof_Systems.pdf). The sparse arithmetic-circuit and R1CS translation interface cited in the AURIC adapter is from Justin Thaler, *Proofs, Arguments, and Zero-Knowledge*, §8.4, [survey](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf). These references supply the standard protocol interfaces; the finite-field correspondence and resource qualifications in this note remain subject to the definitions stated here.
