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
