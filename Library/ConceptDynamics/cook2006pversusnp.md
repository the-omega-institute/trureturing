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
