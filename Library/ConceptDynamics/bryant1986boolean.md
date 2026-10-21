---
bibkey: bryant1986boolean
authors: Randal E. Bryant
year: 1986
title: 'Graph-Based Algorithms for Boolean Function Manipulation'
doi: 10.1109/TC.1986.1676819
url: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
claim: Reduced ordered function graphs give canonical representations of Boolean functions for a fixed variable order; representation size can depend strongly on that order.
strata_touched:
  - D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts
license: citation-only
triage: anchor
---

# Ordered Boolean function graphs

Published in IEEE Transactions on Computers C-35(8), 677–691 (1986).
The author-hosted PDF reconstructs the original electronic submission and
includes footnotes explicitly marked “Update”; its pagination differs from
the journal pagination.

## Verified scope

Section 1.1 defines restrictions/cofactors after assigning an input and fixes
one common order of variables. Section 2 defines ordered function graphs,
their isomorphisms and reduction. Theorem 1 states existence and uniqueness up
to isomorphism of a reduced graph for each Boolean function, together with
the corresponding graph-size minimality. The introduction and examples
explain the dependence on variable order and the possible exponential size.

## Repository use and limits

Section 79 of the boundary-dynamics theory volume uses remaining responses
as finite messages after each prescribed set of coordinates has been read.
This is related to merging identical residual Boolean functions, but it
counts reachable message labels at every externally specified position.
It does not equate those layer counts with the total number of nodes in a
reduced graph, which may skip irrelevant variables.

The explicit violation of submodularity, the bottleneck layout recurrences,
and the joint task/overlap-port quotient in that section are proved there.
They are not attributed to Bryant's Theorem 1. No complexity classification
of variable-order optimization is imported from this source, and no new
Lean result is asserted by this citation.

## Source

- [Author-hosted updated manuscript](https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf).
- [Journal DOI](https://doi.org/10.1109/TC.1986.1676819).

This note is an original citation-only summary. No article text or PDF is
copied into the repository.

## 1. Three orders and the cost of a fixed pure DAG

**Definition 1.1 (Scheduling, elimination and completion order).** Bryant's §1.1 fixes an order of input variables and defines the restrictions of a Boolean function; §2 and Theorem 1 give a canonical reduced ordered function graph for that fixed order. This note uses those exact representation conditions. The following elementary distinctions state how they relate to the classical circuit and search mechanisms of [Cook §§5–9](cook2006pversusnp.md#5-explicit-nor-circuits-and-boundary-tasks); they are not additional theorems attributed to Bryant.

A scheduling order is a topological order of a fixed finite dependency DAG with fixed input ports, fixed initial data and deterministic pure node functions. An elimination order chooses which variables to remove while forming intermediate factors or residual functions. A completion order chooses candidate inputs, or nonempty completion fibres of successive prefixes, in search of an accepted witness. Input-variable order in a reduced ordered Boolean graph belongs to the second kind of representation choice; it is not merely a schedule of the same fixed nodes. Completion order has its own resource contract in Cook Definition 8.1.

**Proposition 1.2 (Fixed-DAG scheduling invariant).** Fix such a pure DAG and all initial inputs. If every noninput node executes exactly once after its predecessors, then all topological schedules give the same value at every node. If its cost $c_v$ depends only on that node and its determined operands, their total node work is

$$
W=\sum_v c_v.
\tag{B.1}
$$

The conclusion does not bound peak live storage, cache misses, communication or schedule-construction cost; nor does it cover an algorithm that prunes, short-circuits, changes sharing or skips nodes.

Proof. Induct on dependency depth, the length of a longest path ending at the node. Initial values are fixed. Every operand of a node of positive depth is a fixed port reference to a value already uniquely determined at smaller depth. Applying the same deterministic pure function therefore gives the same output in every schedule. This induction does not require a particular choice among available unrelated nodes. Every node is then executed once with the same operands, so summing its fixed cost gives (B.1). Changes in residence intervals or physical data movement are not part of that sum unless they were included in a cost model satisfying its fixed-operand hypothesis. A function with side effects or dependence on time, execution history or occurrence identity would violate the purity premise. $\square$

**Definition 1.3 (Two different sharing tests).** For rooted ordered labelled trees, merging identical subtrees preserves their entire ordered syntactic unfolding. The standard minimal-DAG statement counts one node per distinct rooted fringe subtree; see Seelbach Benkner–Wagner, *Distinct Fringe Subtrees in Random Trees*, [§1, p. 3687](https://doi.org/10.1007/s00453-022-01013-y). Its random-tree estimates are not used here. The deterministic source-specific application, including the one-root exceptions and operand/output costs, is [Selection Calculus Theorem 14.2](../../docs/develop/theory/AURIC_FIB_ATOM_SELECTION_CALCULUS.md#十四规范来源的展开共享与纯解释成本).

For an ordered Boolean function graph, merging equal remaining functions uses semantic equality under a fixed variable order, and reduction may also remove a test whose two successors agree. Bryant's Theorem 1 concerns these reduced ordered graphs. It is not the assertion that a canonical graph for an arbitrary circuit is always small, and it does not identify the number of labels at each prescribed layer with total reduced nodes when variables can be skipped.

**Proposition 1.4 (Representation order can change the task while schedule does not).** The invariant in Proposition 1.2 is compatible with both variable-order sensitivity of Boolean function graphs and NP-completeness of circuit completion with a supplied topology. Neither an exponential exact residual representation nor an efficiently described successful candidate order alone gives an ordinary computational lower or upper bound for all succinct completion programs.

Proof. Bryant's §3 compares ordered representations after changing the sequence of variables; the remaining functions, and hence the graph being constructed, change with that sequence. Proposition 1.2 instead fixes the graph and computes all its node values. The hypotheses differ at the representation itself, so the fixed sum (B.1) makes no assertion about the size or construction cost of the new ordered representation.

For elimination over constraints, the complete boundary assignment, not just its separate unary projections, must be retained until the unfinished constraints have been tested. [Dechter Propositions 1–3](dechter1996bucket.md#1-records-addresses-and-compilation-cost) give the explicit frontier construction, its failure record, its $\operatorname{poly}(n)2^{O(w)}$ cost and complete-overlap gluing premises. The graph can change with the chosen order because scopes of intermediate relations change. A supplied suitable order has its own cost if an algorithm must first find it.

The grouped-versus-alternating equality example and its explicit next-bit selector are already proved in [Dechter Proposition 4](dechter1996bucket.md#3-order-sensitivity-and-program-cost). Its grouped cut has exponentially many exact residuals but a polynomial description of the current one and a polynomial-time selector. Thus a bound for an explicit exact-residual table does not bound all programs computing the required entries. Conversely, [Cook Proposition 8.3](cook2006pversusnp.md#8-uniform-good-order-compilation-and-the-xor-normal-form) puts any already supplied accepted witness first in a short XOR permutation, but uniform acquisition of such a parameter has the additional bounds of Definition 8.1.

Finally, Cook Theorem 6.1 constructs the full topological order as part of a SAT reduction. Evaluating one fixed input then uses Proposition 1.2, whereas completion quantifies over the input assignments. A known schedule and a total verifier do not eliminate that quantifier. The exact uniform success-order equivalence, including NO instances, is Cook Theorem 8.2. These comparisons separate the tasks without assuming either $P=NP$ or $P\ne NP$. $\square$

## 追加锚（本行以下为增补区）

## 2. Exact residual distinctions and quantum memory

Fix a Boolean formula $\varphi$ and variable order $x_1,\ldots,x_m$. At cut $i$, define $F_u(z)=\varphi(uz)$ for prefixes $u\in\{0,1\}^i$, and let $r_i$ be the number of distinct functions $F_u$. These are residual functions at prescribed layers, not a count of all nodes in a reduced graph that can skip tests.

**Proposition 2.1 (Exact future answers require distinct states).** A deterministic machine reading this order and correctly evaluating every full assignment requires at least $r_i$ reachable states at cut $i$. Suppose instead that all prefix-dependent information available to future operations passes through a joint memory of finite Hilbert-space dimension $d_i$. If for every suffix $z$ a continuation fixed independently of the hidden prefix returns $F_u(z)$ with zero error, then $d_i\ge r_i$. A memory of $q$ qubits therefore requires $q\ge\lceil\log_2r_i\rceil$.

Proof. Identical deterministic states followed by the same suffix give the same answer, so their residual functions must coincide. For the quantum statement, choose a density state $\rho_u$ for each distinct residual. Two distinct residuals have some separating suffix $z$; reverse their names if necessary so $F_u(z)=1$ and $F_v(z)=0$. Pull the entire continuation and its final binary measurement back to an effect $0\le E_z\le I$ on the current joint memory. Exactness gives

$$
\operatorname{tr}(E_z\rho_u)=1,
\qquad\operatorname{tr}(E_z\rho_v)=0.
\tag{B.2}
$$

Positivity places the support of $\rho_u$ in the one-eigenspace of $E_z$ and that of $\rho_v$ in its zero-eigenspace. Indeed the nonnegative traces against $I-E_z$ and $E_z$, respectively, vanish, so their positive square roots annihilate the corresponding support. The supports are orthogonal. This argument applies to every pair even though different pairs may use different suffixes. Selecting a nonzero vector from each support gives $r_i$ orthogonal vectors, proving $d_i\ge r_i$. This is the standard perfect-discrimination obstruction discussed in [Barnett–Croke §§2, 3.2.b](../Quantum/barnett2009discrimination.md), applied here to suffix-selected tests; it requires no common measurement supplied in advance for all residuals. $\square$

Any accessible classical transcript, retained input prefix, reference, control register or environment that can return must be included in this joint memory. Fixed prefix-independent ancillary states may be part of the continuation, but an omitted prefix-dependent register would invalidate (B.2) as a common effect on the stated memory. The result concerns exact zero error and all specified suffixes; it does not give the same dimension bound for bounded error or a smaller test menu. It is a capacity bound, not a runtime bound: $r_i=2^i$ requires only $q\ge i$ by this argument.

## 3. A small effective layered representation

**Definition 3.1 (Uniform layered codes).** For a formula/order encoding of length $N$ with $m\le N$ listed variables, fix programs for an initial code, an update $T(\varphi,i,q,b)$ and a terminal bit $A(\varphi,q)$. Code lengths and initialization, transition and readout costs are bounded by fixed polynomials in $N$. For every assignment $w$, starting at the initial code and applying its bits yields $q_m$ with $A(\varphi,q_m)=\varphi(w)$. Let the total number of reachable layered codes $(i,q)$ be bounded by a fixed polynomial $B(N)$. Codes have exact bit-string equality; they need not identify all semantically equal residuals.

**Proposition 3.2 (Uniform construction, decision and witness).** Under Definition 3.1, satisfiability is decidable in deterministic polynomial time, and a satisfying assignment can be output in polynomial time when one exists.

Proof. From the initial code, generate both successors of every reached code in each layer and merge exact duplicate strings. At most $B(N)$ layered codes and $2B(N)$ edges occur. Their lengths and update costs are polynomial, so even direct comparisons and sequential scans take polynomial total time. Save one parent and selected bit per newly reached code. Every saved parent chain is a genuine prefix and every assignment's state appears by induction. An accepting terminal code therefore has a parent chain producing a witness, while absence of such a code rules out all assignments. Initialization, enumeration, deduplication, parent reconstruction and final readout are charged. The construction supplies a sufficient algorithmic condition, not an assumption that semantic equivalence testing or a small representation is automatically available. $\square$

The clause-specific masks in [Dechter Propositions 5.2–5.3](dechter1996bucket.md#5-cnf-crossing-clause-satisfaction-masks) give such codes when their crossing-clause bound is logarithmic. The grouped equality example in that note still has an inexpensive selector despite an exponential full residual table, so small explicit layered representations are not a necessary condition for efficient witness search. These statements are elementary automaton and dynamic-programming exposition, not additional results attributed to Bryant's Theorem 1.

## 追加锚（本行以下为增补区）
