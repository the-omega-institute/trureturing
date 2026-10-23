# Native projection finiteness and concrete-exterior limitedness

Finite existential feasibility and finiteness of the entire output image
are different questions. This volume decides the latter for the actual
finite Fibonacci tree algebra. A finite answer supplies every output
and an original realizing assignment; an infinite answer supplies an
effective sequence of original solutions with pairwise distinct outputs.
The argument extends the witness construction of NSF by proving which
output coordinates are fixed on **all** solutions and which can be pumped.
It does not identify NSF's replacement witnesses with the solution set.

For arbitrary acquired signed fibers this gives exact whole-row image
classification and a complete bounded-recovery criterion for the reached
set and concrete exterior. For an empty target cut it decides bounded
whole-source recovery. When the entire source fiber is finite, it gives
the complete paid adaptive Pareto frontier and rational same-source
weighted optimum, including zero weights. On infinite source fibers,
finite row image does not settle partition observability or arbitrary
physical-word optimization.

The proofs are ordinary mathematics. They are not new Lean kernel
verification, a solver implementation, a complexity claim or evidence
that a particular physical acquisition has occurred. This companion is
reference input; published text is immutable and additions use the final
append anchor.

## 1. Original sources, existential projections and paid services

**Definition 1.1 (native expressions and their output images).** Put

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&
\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle x,y\rangle&=\langle\rho x,\rho y\rangle.
\end{aligned}
\tag{NPL.1}
$$

All trees are nonempty, finite, free and ordered. Native expressions use
variables, the two constants, pairing and fixed numeral powers of $\rho$.
Let $\Phi(\mathbf x)$ be a finite Boolean combination of equalities of
such expressions, and let $\mathbf t=(t_1,\ldots,t_s)$ be a finite tuple
of native expressions in the same finite variable list. Define

$$
\operatorname{Sol}(\Phi)=\{\mathbf x\in\mathcal T^n:\Phi(\mathbf x)\},
\qquad
\operatorname{Im}_{\Phi}(\mathbf t)
 =\{\mathbf t(\mathbf x):\mathbf x\in\operatorname{Sol}(\Phi)\}.
\tag{NPL.2}
$$

Variables not occurring in the output are still jointly existentially
quantified; none is deleted from $\Phi$. Fixed finite tree parameters
are native constructor expressions. Zero variables, empty output tuples
and empty solution sets are allowed. There is no quantified epoch,
physical word, arbitrary pointwise rank predicate or universal tree
quantifier in this syntax.

**Assumption 1.2 (the entire acquired fiber).** Service applications use
exactly [ARH, Assumption 1.3][ARH] and [NSF, Assumption 1.2][NSF]. For
finite prefix-free original cuts $P,Q$, an acquired complete old row $R$,
finite literal history $H_0$ and finite signed relation history
$H_{\rm rel}$, the common retained input has the entire nonempty fiber

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{NPL.3}
$$

A record $(a,p,b,q,\bowtie)$ requires both endpoints to exist and
compares the **whole** subtrees $(\rho^a u)|_p$ and $(\rho^b u)|_q$,
with $\bowtie$ equal to $=$ or $\ne$. Absence invalidates either sign.
Every record refers to the same original $u$. All old repetitions,
cross-class and off-task disequalities, concrete exterior and guards
remain imposed. There is no size, depth or template promise on $D$.

Entry is the actual same-root register $\rho^N u$, with authentic $N$
at least every acquired epoch. The complete accessible state is a fixed
function of the retained input and common parameters. Every accessible
source-bearing cache, address, count, length, control position, timing
field, reference, permission and archive is included in that input.
ARH Proposition 2.1 supplies a paid source-total acquisition procedure
conditional on this complete-state contract; its cost can be unbounded
across sources. No such cost is refunded here.

The full target $R_Q(u)$ includes the reached original cut addresses,
numbered-hole concrete exterior and complete equality partition of the
reached whole subtrees. Empty $Q$ asks for the original source itself;
$Q=\{\varepsilon\}$ has a single fixed hole row.

**Definition 1.3 (actual actions and costs).** A comparator is any common
deterministic effective controller that terminates correctly on every
$u\in D$, using actual original-root $\mathsf{Read}(p)$, forward
same-register $\mathsf{ApplyRho}$ and absorbing $\mathsf{Halt}$.
Reply-dependent control and every finite physical word are allowed,
including absent addresses. There is no reset, reroot, clone, equality,
source-identity, chart-membership or unknown-tree port. Computation and
updates reveal no unlisted source-dependent side information.

For a service $A$ use

$$
\begin{aligned}
c_A(u)&=(q_A(u),a_A(u),\ell_A(u)),
&\ell_A(u)&=\sum_{\text{actual reads at }p}|p|,\\
b(A)&=(\sup_Dq_A,\sup_Da_A,\sup_D\ell_A),
&W_\lambda(A)&=\sup_{u\in D}\lambda\cdot c_A(u),
\quad\lambda\in\mathbb Q_{\ge0}^3.
\end{aligned}
\tag{NPL.4}
$$

Here $q$ counts every actual raw Read call, including repeated calls and
absent replies; $a$ counts post-entry actual updates. Root reads have
length zero but cost one call. Same-source sums precede their supremum;
$W_\lambda(A)$ need not equal $\lambda\cdot b(A)$. Installation, local
computation, address generation, memory, retention, authentication,
output work and physical time are separate resources. A computed
hypothetical source or simulated action produces no physical receipt.

**Convention 1.4 (falsifiers of the correspondences).** An original
solution whose output is omitted refutes finite-image completeness.
A generated assignment violating any retained guard, normality condition
or signed constraint refutes soundness. Equal proposed observations
with different claimed outputs refute behavioral sufficiency. A hidden
selector, backwards epoch or fictitious receipt refutes a physical
consumer. An increased coordinate on one same source refutes sourcewise
dominance. An excluded legal adaptive comparator refutes an exact
optimum. A search lacking a finite rejection or stopping argument
refutes a decision claim. The proofs below address these obligations
universally; finite examples do not replace them.

## 2. The finite branch data that are reused

**Definition 2.1 (normal codes, shapes and decorations).** Reuse the
bijection $B:\mathcal T\to\mathcal N$ with inverse $E$ from [ABC,
Theorems 2.2–2.3][ABC]. Its normal codes are finite terms over $F$ and
primitive ranks $[r]$, $r\in\mathbb N$, subject to

$$
F(X,Y)\in\mathcal N
\quad\Longleftrightarrow\quad
X,Y\in\mathcal N\ \land\
\neg\exists r\ge0\ (X=[r+1]\land Y=[r]).
\tag{NPL.5}
$$

Every primitive is normal. Expansion sends $[r]$ to $T_r=\rho^r\alpha$.
Native pairing is the smart constructor $J$, which replaces exactly
$F([r+1],[r])$ by $[r+2]$ and otherwise keeps $F$. A native iterate
$\rho^k$ is translation $\tau_k$ of every primitive rank by $k$.
Its image consists exactly of normal codes with all ranks at least $k$.
Normal codes, rather than arbitrary ambient terms, are essential for
injectivity of expansion.

Apply the finite reduction of NSF §§2–3 to $\Phi$, including all output
expressions as named subexpressions with positive defining equations.
An output name is not constrained to any preselected value. The
reduction distributes Boolean branches, chooses collapse/noncollapse
cases for every $J$, and solves positive **shape** equations by ordinary
finite-tree unification with the occurs check. Primitive shape is $c$;
the binary shape constructor is $f$. On a successful branch each name
$Z$ has a shape term $S_Z$ over $c,f,w_1,\ldots,w_m$.

Each explicit $c$ occurrence has a scalar rank variable. Each residual
$w_j$ occurrence has its own block variable, denoting a rank function on
the same nonempty finite shape assigned to $w_j$. Repeated uses of a
name reuse its decorated template. Different occurrences of a residual
shape can have different rank functions.

**Definition 2.2 (scalar graph and branch conditions).** NSF Lemma 3.2
leaves scalar equations and whole-block equations of the forms

$$
r=r'+d,\qquad r=d,\qquad U=V+d,
\quad d\in\mathbb Z.
\tag{NPL.6}
$$

Whole-block addition is pointwise, and both blocks in an equation have
the same residual shape sort. There is no scalar/block equation and no
block equation between different sorts. All ranks are natural.

At every explicit primitive cherry impose the noncollapse inequality
$r_L\ne r_R+1$. An original code disequality with syntactically different
shape terms remains a disequality of those decorated terms. If the shape
terms are identical, choose one unequal corresponding scalar or block
in its finite disjunction. This yields finitely many negative branches,
with scalar and whole-block offset disequations in addition to (NPL.6).
Actual solutions with accidentally equal ground shapes of syntactically
different terms are **not** discarded; their code disequality is still
retained. Distinct ground shapes will only be used to construct witnesses.
For all-solution statements a branch still requires normality of every
entire code. The later marker restrictions give an equisatisfiable witness
family, not the definition of its original solution set.

Add a scalar vertex $o$ fixed to zero and encode $r=d$ as $r=o+d$.
The scalar equality graph has one edge with its signed offset for every
scalar equation. Reject inconsistent offset cycles. In each remaining
connected component $C$ compute potentials $\delta_r$ such that

$$
r=b_C+\delta_r.
\tag{NPL.7}
$$

The component containing $o$ is **anchored**; its base is fixed by
$o=0$. Every other component is **free**. Nonnegativity imposes only
lower bounds on a free base. Scalar disequations, including explicit
normality, exclude differences of bases; they add no upper bound.
Block equation components have the analogous potentials of NSF
Lemma 4.2, separately for each residual sort.

**Lemma 2.3 (what feasibility does and does not say).** The branch list
is effective and finite. Its feasibility is decidable by NSF Theorem 4.3.
Every original solution chooses at least one feasible branch, factors
through its shape unifier, and satisfies its scalar equations at all
explicit leaves. Conversely NSF's marker construction for any feasible
branch gives an original solution, including values of every input
variable and the named outputs.

These conclusions do not say that every original solution is a marker
solution or that the branch has finitely many original solutions.

Proof. Adding a subexpression name with its defining equality is an
existential definitional extension: evaluation extends every original
assignment, and the definitions uniquely recover that evaluation.
NSF Lemma 2.3 proves the native-to-normal branch correspondence;
NSF Definition 3.1 supplies factorization of every actual shape assignment.
NSF Lemma 3.2 retains exactly the positive equations after decoration.
Every identical-shape code disequality has a scalar or block mismatch
in an actual solution, so a negative disjunct can be chosen. A
syntactically different-shape disequality stays satisfied by that actual
solution whether or not its ground shapes coincide.

NSF Theorem 4.3 decides the resulting arithmetic witness conditions.
Its completeness keeps the actual explicit scalar ranks while replacing
residual blocks; its soundness checks all normality boundaries and
reassembles every defining equation and disequality. These are the
stated directions. The replacement step is existential, which is why
neither of the stronger assertions follows. $\square$

## 3. Two infinite families and one rigidity alternative

**Lemma 3.1 (arbitrarily large separating shape markers).** Fix the finite
list of shape terms in a branch. There is an effective integer $M_0$
such that for every $M\ge M_0$ there are pairwise distinct nonleaf
shapes $G_1(M),\ldots,G_m(M)$, each with $M$ leaves, whose substitution
for the $w_j$ preserves every syntactic inequality in that list.

Proof. Take $M_0\ge3$ larger than each listed term's leaf count, counting
variable occurrences as leaves, and with $M_0-1\ge m$. For every
$M\ge M_0$ there are at least $M-1$ different full ordered binary
shapes with $M$ leaves: choose the root's left and right combs to have
$i$ and $M-i$ leaves, for $1\le i<M$. Choose $m$ of them by a fixed
finite enumeration. They are nonleaf and distinct.

Cancel common constructors in two different terms to the first
disagreement, as in NSF Lemma 4.1. Different variables have distinct
markers. A variable's marker has $M$ leaves; a constant has one; a
variable-free compound from the given terms has fewer than $M$; and a
compound containing a variable has more than $M$. The last assertion
follows because it has at least one additional leaf occurrence besides
that variable, whether that occurrence is constant or another variable.
A constant/constructor disagreement also persists. These cases are
exhaustive. The argument holds for **every** such $M$, which is the
extra parameter needed for an infinite output family. $\square$

**Lemma 3.2 (marker models with retained scalar choices).** In a feasible
branch, fix any solution of its scalar equations, disequations,
nonnegativity and explicit-cherry conditions. There are constant-rank
values for all block variables that, together with this scalar solution
and the markers of Lemma 3.1, give an original solution for every
$M\ge M_0$. The block constants can be chosen independently of $M$.

Proof. NSF Lemma 4.2 computes potentials on each block equation
component. Feasibility rules out a nonzero offset cycle and a
same-component disequation with identical offsets. Every other
same-component disequation is automatic. For different components,
choose natural base constants successively above all nonnegativity
bounds and outside the finitely many forbidden differences. This is a
finite construction independent of the number of leaves. All blocks of
one sort use that sort's marker; a block's assigned constant is placed
at every leaf, with its required offset.

Equal ranks at a marker cherry cannot have left rank one more than right
rank, so each inserted block is normal. Its root is nonleaf, hence no
primitive cherry can cross the boundary between the explicit template
and an inserted marker. Every remaining primitive cherry is explicit
and is normal by the retained scalar condition. Thus every entire named
code is normal.

Block and scalar constraints are separate by (NPL.6). Their equations
reassemble all positive definitions. Selected scalar or block mismatches
satisfy the identical-shape negative atoms; Lemma 3.1 satisfies all
syntactically different-shape negative atoms by genuine shape difference.
Expansion by $E$ therefore gives an original assignment of the full
formula. The construction changes no conjunct or sign. $\square$

**Lemma 3.3 (free scalar pumping).** In a feasible branch, fix one free
scalar component $C$. There is an effectively constructed sequence of
scalar solutions for which $b_C=b_*+k$, $k\in\mathbb N$, while every
other scalar component has one fixed base. The solutions satisfy every
scalar condition of the branch.

Proof. Begin with any scalar solution supplied by feasibility and freeze
all components except $C$. Equations internal to $C$ retain their
potentials. Internal disequations depend only on those potentials and
remain true. Nonnegativity is $b_C\ge\max_{r\in C}(-\delta_r)$.
Every disequation between $C$ and a fixed other component excludes at
most one integer value of $b_C$. There are finitely many such values.
Choose $b_*$ above all excluded values and at least the nonnegativity
bound. Every $b_*+k$ then satisfies all constraints. The component is
free, so no equation ties this change to $o$ or to another component.
All quantities and the chosen bound are computable. $\square$

**Definition 3.4 (output rigidity in a branch).** A feasible branch is
output-rigid when both of the following hold:

1. Every output shape term $S_{t_i}$ contains no residual shape variable.
2. Every explicit scalar leaf in those output templates lies in the
   anchored scalar component.

Both conditions are finite inspections of the branch. They concern
only the designated output tuple; residual shapes or free scalar
components elsewhere are permitted.

**Theorem 3.5 (singleton-or-infinite branch dichotomy).** On a feasible
branch, the original output image is a singleton if the branch is
output-rigid. Otherwise it is infinite, with an effective sequence of
original satisfying assignments having pairwise distinct output tuples.
The singleton assertion concerns all original solutions of that branch,
including those not produced by the marker construction.

Proof. In the rigid case the output shapes are ground finite terms over
$c,f$. Every output leaf rank is fixed by its equation path to $o$.
Consequently the decorated output codes are fixed on every actual
solution factoring through the unifier, by Lemma 2.3. Their expansions
are fixed native values. Feasibility supplies an actual solution, so the
image has exactly one tuple rather than being empty. A witness computes
that tuple and supplies its original realizing assignment.

If some output shape contains a residual variable, use any scalar
solution and Lemma 3.2 for $M=M_0+k$. For that output, let $e$ be its
number of explicit $c$ leaves and $v>0$ its number of residual-variable
occurrences. Its ground code shape then has exactly

$$
e+v(M_0+k)
\tag{NPL.8}
$$

leaves. This number strictly increases with $k$. The normal output codes
are therefore pairwise different. Since $E$ is injective on normal
codes, the native outputs are pairwise different too. This counts code
leaves, not native source leaves; no equality of those counts is needed.

It remains to consider ground output shapes with some output scalar in
a free component $C$. Fix any one set of nonleaf markers. Apply
Lemma 3.3 and keep the block constants of Lemma 3.2 fixed. That lemma
applies to every resulting scalar solution. At the designated fixed
output leaf, the rank increases by one with each $k$. The normal output
codes are pairwise distinct and again expand to distinct native outputs.

In both cases decoding the named input codes gives every original
variable value. Each generated assignment satisfies the **whole**
original formula by Lemma 3.2, not merely the output definitions.
All constructions are finite for each $k$. These cases exhaust failures
of output rigidity. $\square$

The theorem does not assert an exact normal-form parametrization of all
solutions. Universal rigidity and an infinite subfamily are enough for
its two alternatives. In particular replacing originally primitive
residual blocks by nonleaf markers is used only in the infinite-family
construction, never to describe all original values.

## 4. A terminating decision for native projection finiteness

**Theorem 4.1 (exact finite image or effective infinite image).** Given
$\Phi$ and $\mathbf t$ of Definition 1.1, a terminating algorithm returns
exactly one of the following:

- FINITE: the complete finite set $\operatorname{Im}_{\Phi}(\mathbf t)$,
  with an original assignment $\mathbf x$ satisfying $\Phi$ for every
  listed output and evaluating to that output;
- INFINITE: an effective map $k\mapsto\mathbf x_k$, $k\in\mathbb N$,
  with $\Phi(\mathbf x_k)$ and pairwise distinct $\mathbf t(\mathbf x_k)$.

In the finite case the list is empty exactly when $\Phi$ is unsatisfiable.
The original variable domain remains all finite native trees.

Proof. Compute the finite branch list and decide feasibility of each by
Lemma 2.3. Discard only infeasible branches. If any remaining branch is
not output-rigid, Theorem 3.5 supplies the INFINITE answer within original
solutions, so it is sound for their union.

Otherwise every feasible branch has its single fixed output. Obtain a
witness from each and evaluate its output tuple. Remove duplicate tuples
by finite native syntactic equality, retaining a realizing assignment
for each. Every listed tuple is realized. Every original satisfying
assignment chooses a feasible branch and has that branch's rigid tuple;
hence no output is omitted. If there are no feasible branches, the
solution set and image are empty.

There are finitely many Boolean choices, pairing-collapse choices,
finite unification steps and negative-witness choices. Feasibility has
a terminating NO decision; rigidity is a finite graph and syntax test.
Witness extraction and comparison of finite native trees terminate.
An infinite answer returns a finite description of the generator proved
in Theorem 3.5, not an attempted enumeration to establish infinitude.
Thus both answers terminate without testing successive source-size or
prefix bounds. $\square$

**Corollary 4.2 (actual finite source sets and hidden witnesses).** Finiteness
of any native existentially defined set

$$
X=\{\mathbf x:\exists\mathbf z\ \Psi(\mathbf x,\mathbf z)\}
\tag{NPL.9}
$$

is decidable. A finite answer enumerates all $\mathbf x$ with a realizing
$\mathbf z$ for each; an infinite answer produces pairwise distinct
$\mathbf x_k$ with their witnesses. Taking the output to be the entire
variable tuple decides finiteness of $\operatorname{Sol}(\Phi)$ itself.

Proof. Designate $\mathbf x$ as the output and retain all variables
$(\mathbf x,\mathbf z)$ and all of $\Psi$ in Theorem 4.1. The original
assignments it returns contain the required hidden witnesses. $\square$

**Proposition 4.3 (fixed navigation and finite tags).** Theorem 4.1 extends
effectively to the finite-observation syntax of NSF Lemma 5.1 whenever
the designated output on each of its finitely many original prefix
cases is a tuple of native expressions, optionally paired with a fixed
finite tag. All fixed guards, signed tests and Boolean complements
remain in the domain.

Proof. NSF's compiler decomposes the source tuple into actual original
prefix patterns beyond all finitely supplied navigation positions.
Repeated occurrences use the same frontier variables. On each case,
reached subtrees and the output expressions are native expressions in
those variables; guards and literal replies are computed exactly. Apply
Theorem 4.1 to that case's full formula and designated expressions.
Fill its returned frontier assignments into its original patterns.

Every produced tuple reconstructs an original source tuple satisfying
all case conditions. Conversely every original tuple determines its
actual prefix case and frontier assignment, so its output is covered.
A finite union of finite images is finite, and a single infinite case
supplies an infinite image because its native outputs are already
distinct at one fixed tag. Deduplicate the finite tagged outputs and
retain their original witnesses. All case lists are finite. No variable
physical word or variable navigation depth has been introduced. $\square$

The singleton-or-infinite test is the additional uniform inference here.
NSF's one-witness bound alone would not justify it: even $x=x$ has a
small witness and an infinite full output image. The proof explicitly
uses which coordinates remain fixed on every actual solution and the
two original-solution pumping constructions.

## 5. Exact images of complete original rows

**Definition 5.1 (mask and exterior output).** For the original source
$u$ let $I_Q(u)=Q\cap\operatorname{Pos}(u)$ and let $m_Q(u)$ be the
native tree obtained by replacing the subtree at each $q\in I_Q(u)$
by $\alpha$. Define

$$
\operatorname{Ext}_Q(u)=(I_Q(u),C_Q(u)),
\tag{NPL.10}
$$

where $C_Q(u)$ is the numbered-hole context before those fillings.
The partition is deliberately a separate field of the **full** target,
not discarded from that target. ABC Theorem 4.2 supplies the exact
bijection between $(I_Q,m_Q)$ and this exterior output on their images:
replace the subtrees at the known reached positions by numbered holes.
This holds even when coding the mask collapses an atomic block.

**Lemma 5.2 (entire signed fibers with native mask outputs).** From the
finite retained input and $Q$ one can compute finitely many formulas
$\Phi_i(\mathbf x)$, native source terms $W_i(\mathbf x)$, fixed reached
sets $I_i$, native mask terms $m_i(\mathbf x)$ and whole-hole terms
$h_{i,q}(\mathbf x)$ for $q\in I_i$, such that

$$
\begin{aligned}
D&=\bigcup_i\{W_i(\mathbf x):\Phi_i(\mathbf x)\},\\
I_Q(W_i(\mathbf x))&=I_i,\qquad
m_Q(W_i(\mathbf x))=m_i(\mathbf x),\qquad
W_i(\mathbf x)|_q=h_{i,q}(\mathbf x)
\end{aligned}
\tag{NPL.11}
$$

on every satisfying assignment. Each original $u\in D$ has its actual
prefix case and frontier values giving these identities. Every
satisfying filling gives an original member of $D$ with every old and
additional constraint intact.

Proof. Use ARH Proposition 3.2's full-domain guarded cells, or equivalently
NSF Lemma 5.1's fixed-navigation compiler, including the full predicate
(NPL.3). Split original prefix patterns strictly beyond all fixed
endpoints and cut positions. Reached target sets are then fixed;
navigation yields the entire native subtree expressions, not only root
labels. Mask those reached expressions by $\alpha$, retaining every
uncut residual term in the exterior. Old class occurrences share their
original variables and all class disequalities remain in $\Phi_i$.
The actual frontier decomposition gives the inverse source direction;
filling it gives the forward direction. These are reused correspondences,
not a claim that the cell domains are finite. $\square$

**Theorem 5.3 (whole-row image decision with actual original witnesses).**
For every fiber (NPL.3), including an empty fiber when testing consistency,
there is a terminating decision whether $R_Q(D)$ is finite. In the finite
case it returns its exact row list and an original source in $D$ realizing
each row. In the infinite case it returns an effective sequence
$u_k\in D$ with pairwise distinct complete original rows and pairwise
distinct masks within one fixed reached-set case.

Moreover the following are equivalent:

$$
|R_Q(D)|<\infty
\quad\Longleftrightarrow\quad
|\operatorname{Ext}_Q(D)|<\infty
\quad\Longleftrightarrow\quad
|m_Q(D)|<\infty.
\tag{NPL.12}
$$

Proof. The reached sets range over the finite powerset of $Q$. For a
fixed reached set the possible equality partitions form a finite set.
Together with the mask these fields determine the complete row, by
ABC Theorem 4.2. Conversely each row determines its mask and exterior.
These observations prove (NPL.12); no recovery service is used in them.

Apply Theorem 4.1 to $(\Phi_i,m_i)$ in each cell of Lemma 5.2. An infinite
case supplies assignments with distinct native masks. Filling them by
$W_i$ gives sources in the original $D$; their different masks force
different full rows. This proves the infinite answer with its original
witness family.

If all cases have finite mask image, retain the exact lists. For each
case, each listed mask $m$, and each equivalence partition $\pi$ of
$I_i$, decide

$$
\exists\mathbf x\quad
\Phi_i(\mathbf x)\ \land\ m_i(\mathbf x)=m\ \land\
\bigwedge_{q,r\in I_i}
\begin{cases}
h_{i,q}(\mathbf x)=h_{i,r}(\mathbf x),&q\sim_\pi r,\\
h_{i,q}(\mathbf x)\ne h_{i,r}(\mathbf x),&q\not\sim_\pi r.
\end{cases}
\tag{NPL.13}
$$

This is NSF's finite existential syntax. Every positive decision gives
an original source $W_i(\mathbf x)$ realizing the full row described by
$I_i,m,\pi$. Every original source occurs in its own case with its
actual mask and complete partition, so its row passes one such query.
Remove duplicate rows and retain a realizing source for each. Every
list and every query is finite and each decision terminates.

A realizing source certifies a possible output offline. It is not the
actual source and gives no runtime test of which row holds. $\square$

## 6. A complete bounded-recovery criterion for the exterior

**Lemma 6.1 (bounded raw reads give finitely many outputs).** On any
nonempty domain with the common-state and action contract of
Assumption 1.2, a source-total service with a uniform bound $K$ on raw
reads has at most $4^K$ different outputs. This applies to the full row,
the exterior output or the whole original source.

Proof. At a reachable reply history the computation until the next read
or halt, including its update schedule and submitted word, is fixed by
that history and the common input. It is finite because at least one
source reaches it and the service terminates on that source. Updates
have no source-dependent reply. Unroll the reachable histories into a
four-child tree of read depth at most $K$, making unreachable children
halts. A halt has a fixed output. A four-ary tree of depth at most $K$
has at most $4^K$ leaves, also when some branches halt early. This is
the operational part of ARH (2.3); it uses no literal-only feasibility
or uniform computation-time assumption. $\square$

**Theorem 6.2 (native exterior limitedness with a paid consumer).** For a
nonempty arbitrary admitted signed fiber $D$, the following are
equivalent and decidable:

1. $m_Q(D)$ is finite.
2. The reached set and entire concrete exterior have uniformly bounded
   height after holes are treated as leaves.
3. A legal static service at the supplied epoch $N$ recovers
   $\operatorname{Ext}_Q(u)$ with uniform finite $q,a,\ell$ bounds.
4. A legal serial service recovers that exterior with a uniform finite
   raw-read bound.
5. The full semantic row image $R_Q(D)$ is finite.

A positive answer supplies an effective actual consumer for the exterior.
It does not assert a full-row consumer unless the partition is separately
recovered. A negative answer excludes uniformly bounded full-row recovery.

Proof. A mask has exactly the shape of its exterior when numbered holes
are treated as leaves, so finiteness of masks gives a height bound.
Conversely there are only finitely many ordered binary trees of bounded
height with leaf labels in $\{\alpha,\beta\}$. Thus 1 and 2 are equivalent.
The finite reached set introduces no unbounded field. Equivalence of
1 and 5 is (NPL.12), and Theorem 5.3 decides them.

For 1 implying 3, compute the exact nonempty finite mask image and let
$h$ be its largest native tree height, with root depth zero. Traverse the
original source mathematically from its root. At a reached position
$p\in Q$, put its numbered hole in the output and do not inspect that
subtree. At any other reached position recover its original root reply.
An original leaf is placed in the concrete output and ends that branch;
an original branch causes visits to its two children. Only original
positions outside target holes are visited. The mask-height bound makes
every such position have depth at most $h$.

Each visited position is known originally reached: the root is reached,
and a decoded original branch certifies both original children. Use the
known-reached case of SLH Theorem 2.2: one actual epoch-$N$ read at the
full physical word

$$
pR^{\lceil N/2\rceil}
\tag{NPL.14}
$$

recovers the original root reply through its parity decoder. For even
$N$ the label is unchanged on these known-reached cases; for odd $N$,
current absent, alpha, and beta/branch decode to original alpha, beta,
and branch respectively. This is an actual read at the original root,
not a reroot operation. Its current reply can be absent without the
original position being absent. At $N=0$ it is simply the read at $p$.

No updates are performed. The traversal therefore constructs exactly
the reached holes and all concrete nodes, orders the holes and halts.
It reads at most $B_h=2^{h+1}-1$ visited non-hole positions, giving

$$
q\le B_h,\qquad a=0,\qquad
\ell\le B_h\bigl(h+\lceil N/2\rceil\bigr).
\tag{NPL.15}
$$

These are sufficient bounds, not asserted optima. The finite source
witnesses used to compute masks supply no hidden runtime selector.
The traversal uses only actual decoded replies, and covers every $u\in D$.

Static inclusion gives 3 implying 4. Lemma 6.1 gives a finite exterior
image from 4, and (NPL.12) gives 1. This proves all equivalences. A
negative answer has infinitely many rows by 5, so Lemma 6.1 excludes a
uniform raw bound for the full target as well. $\square$

**Corollary 6.3 (infinite image excludes a finite length budget too).** If
Theorem 5.3 returns INFINITE, every correct source-total full-row service
has unbounded worst raw-read cost and unbounded worst literal-address
sum. The analogous conclusion holds for the exterior task when its
image is infinite. A uniform bound on updates alone is not excluded.

Proof. Raw unboundedness is Lemma 6.1. JRF Lemma 3.2, restricted to the
same entire signed domain as justified by NSF Proposition 7.4, removes
repeated same-epoch reads and universally constant late root reads
without increasing any same-source coordinate. Its resulting service
satisfies $q(u)\le\ell(u)+\max(0,2-N)$. A finite length bound would thus
imply a finite raw bound, a contradiction. The transformation preserves
whatever output the original service computes; it makes no assumption
on the source predicate. Nothing in this proof lower-bounds updates.
$\square$

Finite row image is now a decidable necessary condition for bounded
full-row recovery on arbitrary signed fibers, and an exact condition for
bounded recovery of their exterior field. The missing full-row condition
is the uniform observation of the remaining partition, not a missing
concrete output or an unenumerated row image.

## 7. Empty-cut recovery and the actual finite-source alternative

**Theorem 7.1 (whole-source bounded recovery without a size promise).**
For arbitrary nonempty (NPL.3), finiteness of the entire original source
fiber $D$ is decidable. A finite answer enumerates exactly all sources;
an infinite answer supplies pairwise distinct sources in $D$.
For $Q=\varnothing$, the following are equivalent:

$$
|D|<\infty
\quad\Longleftrightarrow\quad
\text{uniform-finite-read whole-source serial recovery}
\quad\Longleftrightarrow\quad
\text{uniformly bounded static }(q,a,\ell)\text{ recovery}.
\tag{NPL.16}
$$

Proof. Apply Proposition 4.3 to the whole retained predicate with output
$u$ itself, or Theorem 5.3 with the empty cut. Its mask and full row are
exactly $u$. Thus its returned finite list is the entire source set,
not one representative for a row class. The infinite family also lies
in the entire original fiber. For $Q=\varnothing$ the exterior is the
source, so Theorem 6.2 gives the two operational directions. Necessity
also follows directly from Lemma 6.1. $\square$

The classification computes a source-size bound only **after proving and
enumerating** finiteness from the original input. No extra bound is asked
of the producer or assumed while deciding finiteness. Infinite fibers
still admit sourcewise finite full traversal of the current tree and
computational recovery of the original through the image inverse of
$\rho^N$; this does not give a uniform read bound. The inverse is applied
to a paid, fully acquired finite description, never to the unknown register
through an extra source port.

**Lemma 7.2 (finite-domain physical menus).** Suppose the classification
has returned the exact nonempty set $D=\{u_1,\ldots,u_d\}$, with duplicates
removed. Put

$$
M=\max(N,5),\qquad U=M-N,\qquad
\mathcal P_n=\bigcup_{i=1}^d\operatorname{Pos}(\rho^n u_i)
\quad(N\le n\le M),
\qquad
H=\max_{N\le n\le M,\ p\in\mathcal P_n}|p|.
\tag{NPL.17}
$$

These are effectively computable finite data. At epoch $n$, every word
outside $\mathcal P_n$ gives absent on every source. The table
$r_{\rho^n u_i}(p)$ for $p\in\mathcal P_n$ describes each retained physical
read on every original source, including absence on some sources.

At epoch $N$ this finite menu separates all different sources. Therefore
for any target cut $Q$ a static finite service can recover the full row
with at most $d-1$ reads.

Proof. Compute the finitely many finite iterates; list their positions
and literal replies. The root belongs to every position set, so the
maximum defining $H$ exists. A word not in the union is absent on every
listed tree and these are all sources.

Injectivity of $\rho^N$ makes its images of different $u_i$ different.
Two different finite free trees have a different literal reply somewhere
in the union of their positions, by comparison from the first differing
node. Start with the possible-source set $S=D$. If all its full rows
agree, halt with that row. Otherwise two candidates have different rows,
hence different current trees, so some menu word gives different replies
on $S$. Read that word physically and keep just the candidates with the
actual reply. Every nonempty reply subset is a proper subset of $S$.
After at most $d-1$ strict decreases a constant-row set is reached.
This gives a common effective controller using actual reads, with no
update and no assumed identity of the source. The candidates are all
computed from retained input; only actual replies select among them.
$\square$

## 8. All adaptive comparators on an enumerated finite fiber

**Theorem 8.1 (a finite sourcewise dominating service family).** Under
Lemma 7.2's exact finite-domain hypothesis, one can effectively construct
a finite nonempty family $\mathcal A_D$ of lawful full-$R_Q$ services
such that for every legal adaptive comparator $A$ there is
$B\in\mathcal A_D$ with

$$
\operatorname{out}_B(u)=R_Q(u),\qquad
c_B(u)\le c_A(u)\quad\text{coordinatewise for every }u\in D.
\tag{NPL.18}
$$

Every member of the family has monotone epochs in $[N,M]$, at most
$d-1$ reads per path, and physical words in $\mathcal P_n$ at epoch $n$.
In particular it lies in the computable box

$$
(q,a,\ell)\le(d-1,U,(d-1)H)
\quad\text{on each source}.
\tag{NPL.19}
$$

Proof. First construct the finite candidate family. Enumerate all finite
four-reply tree shapes of read depth at most $d-1$, allowing early halts.
Label every read vertex by a monotone epoch $n\in[N,M]$ and a word in
$\mathcal P_n$. For each leaf compute its exact candidate subset by
following the tabulated replies of every $u_i$. Accept the tree precisely
when $R_Q$ is constant on each nonempty subset. Install that constant
full row; give empty leaves arbitrary default outputs. Before each read,
perform the nonnegative epoch difference from the previous actual epoch;
a halt adds no actions. This realizes exactly the tabulated reply paths
on the actual source. The finite tree terminates and is correct on all
of $D$. The enumeration is finite, and Lemma 7.2 supplies at least one
accepted tree. Every accepted tree has (NPL.19).

For the other comparator direction, take any source-total $A$. Apply
JRF Theorem 3.1's all-source cap, valid on this signed domain by NSF
Proposition 7.4. It produces the same output on each same source with

$$
q^c(u)=q_A(u),\qquad a^c(u)=\min(a_A(u),U),\qquad
\ell^c(u)\le\ell_A(u).
\tag{NPL.20}
$$

All actual reads are now in $[N,M]$. Early epochs, including zero and
one when available, are retained. Late simulated actions supply neither
extra source access nor actual receipts.

There are finitely many sources and the capped program terminates on
each. Its finitely many finite actual executions can therefore be
unrolled into a finite reachable reply tree, compressing deterministic
local computations and update segments. No uniform local running-time
premise is needed. At each node let $S$ be the nonempty subset of $D$
that reaches it. If its next read has the same reply for all of $S$,
supply that known reply locally and delete the actual call, following
its unique reachable child. This is sound on each same source in $S$.
In particular a read outside $\mathcal P_n$ is removed as universally
absent. Keep any actual updates before subsequent informative reads;
the simulated control retains the skipped replies without inventing
receipts. Delete updates after the last retained read, retaining the
computed output, since they supply no further information.

Each retained read has at least two nonempty reply subsets of $S$.
Every source proceeding past it therefore belongs to a strictly smaller
candidate subset. There are at most $d-1$ retained reads on a path.
Every retained word belongs to the finite menu at its actual epoch.
The monotone update segments telescope to the final read epoch minus
$N$; replacing segments between retained reads by that difference does
not increase actual updates. All removed reads and terminal updates
only decrease sourcewise costs. Correctness implies the remaining halt
subsets have constant full rows.

The resulting tree is one of the enumerated accepted services, with
(NPL.18). This comparison proves existence for every allowed $A$; the
finite synthesis procedure need not decide termination or analyze code
of an arbitrary comparator. Conversely every enumerated service is an
actual allowed comparator, already proved above. These are both paid
comparison directions on the same original sources. $\square$

**Theorem 8.2 (complete Pareto and same-source weighted optima).** For an
exact finite nonempty fiber produced by Theorem 7.1 and any $Q$, the set

$$
\mathcal F_D=
\{b\in\mathbb N^3:\exists A\ \forall u\in D,\ c_A(u)\le b\}
\tag{NPL.21}
$$

has an effectively computable finite minimal basis, with an attaining
actual service for each basis vector. Its upward closure is exactly
$\mathcal F_D$. Every rational nonnegative weight tuple has a computable
attained minimum of $W_\lambda$ over **all** legal adaptive comparators,
including every zero-weight case. Bounded $(q,a)$ feasibility with
unbounded word lengths, and arbitrary $(q,a,\ell)$ feasibility, are
therefore decidable on this entire finite fiber.

Proof. Compute $c_B(u_i)$ for every $B\in\mathcal A_D$ and every source.
For a reached terminal path with $k$ reads, last read epoch $n$ and words
$p_1,\ldots,p_k$, its exact vector is

$$
(k,n-N,\textstyle\sum_{j=1}^k|p_j|),
\tag{NPL.22}
$$

taking $(0,0,0)$ for a root halt. Actual epoch differences telescope and
there are no terminal updates. A source is followed through its own
reply path; absent replies and repeated class values are included in the
table. Compute the exact coordinate maxima to obtain $b(B)$, and retain
the coordinatewise minimal vectors among this finite list. Each has its
actual realizing service. Their upward closure is feasible because each
service meets every larger upper bound.

Conversely any feasible comparator is sourcewise dominated by a listed
service by Theorem 8.1, hence is dominated in worst-coordinate budgets.
This proves the other inclusion in (NPL.21) and exactness of the minimal
basis. For a requested $(K,A)$ bound, test whether any listed service
has its first two maxima at most those bounds; Theorem 8.1 covers the
arbitrarily long words of all other comparators. The third bound can be
included in the same finite comparison when supplied.

For weights compute instead

$$
\min_{B\in\mathcal A_D}\ \max_{1\le i\le d}\lambda\cdot c_B(u_i).
\tag{NPL.23}
$$

The dominating inequality (NPL.18) holds on every same source, so it
preserves the inequality after nonnegative weighting and then taking
the maximum. Conversely each candidate is an allowed service. These
two inequalities prove equality with the unrestricted infimum and give
an attaining candidate. No division by a weight is used; zero coordinates
and the all-zero tuple require no exception. Store a source attaining
each reported maximum if desired. Different coordinate maxima may have
different witnesses, and (NPL.23) is not replaced by a weighted sum of
those separate maxima.

Termination follows from the explicit finite menus, finite depth and
finite epoch interval in Theorem 8.1, followed by finite exact arithmetic.
It does not follow merely from Dickson finiteness or from finding one
successful budget. $\square$

The finite reply table is computed only after $D$ itself has been proved
finite and enumerated exactly. A finite list of possible **rows**, a
finite collection of feasibility witnesses or a finite cover by infinite
cells does not meet this hypothesis. Substituting any such list for $D$
would invalidate the removal of constant replies and the cardinality
decrease used in Theorem 8.1.

## 9. Examples that distinguish the alternatives

**Example 9.1 (finite projection, infinite original solutions).** Let
$g=\langle\alpha,\alpha\rangle$ and impose

$$
x=g,\qquad y\ne x.
\tag{NPL.24}
$$

The output $x$ has exactly the one value $g$, while the whole solution
set is infinite. For example $y=T_{k+2}$ never equals $g$: the latter's
normal code is $F([0],[0])$, whereas every $T_j$ has a primitive code.
The rigid output test ignores freedom in $y$ for the image question,
but retains the disequality when producing its witnesses. Applying the
finite-domain resource theorem to the whole solution set on the strength
of this singleton projection would be invalid.

**Example 9.2 (two distinct pumping mechanisms).** With
$x=\langle y,y\rangle$ and $y\ne\alpha$, choose $y$ to expand a
nonleaf normal code with constant rank zero on a shape with $M$ leaves.
Then $y\ne\alpha$, and the normal output code of $x$ has $2M$ leaves.
Varying $M$ gives shape pumping with fixed ranks and preserves the
repeated occurrence of $y$ exactly.

For a rank-only illustration, reuse the classification in
[SourceTransportCentralizer][D5-CENTRAL] and ABC:

$$
\rho^2x=\langle\rho x,x\rangle
\quad\Longleftrightarrow\quad
x=T_j\text{ for some }j\ge0.
\tag{NPL.25}
$$

Its possible output codes all have shape $c$ but unbounded rank $j$.
This is an already supplied atomic classification, used only to
illustrate why a shape-only finiteness test is insufficient. Neither
this example nor Example 9.1 is a replacement for Theorem 3.5's general
original-solution argument.

**Example 9.3 (a whole coupled signed fiber with exact finite resources).**
Let $P=\{L,R\}$ and let the acquired old row be the pair context with
two different classes. Retain the literal record $(0,LL,\mathsf{absent})$
and the signed record $(1,L,0,R,=)$; take authentic entry $N=1$.
The entire fiber is exactly

$$
D=\{u_0,u_1\},\qquad
u_0=\langle\alpha,\beta\rangle,\qquad
u_1=\langle\beta,\langle\beta,\alpha\rangle\rangle.
\tag{NPL.26}
$$

Indeed the old row writes the original source as $\langle x,y\rangle$
with $x\ne y$. Both relation endpoints are reached, and the record says
$y=\rho x$. The literal absence at $LL$ says that $x$ is a leaf, hence
$x=\alpha$ or $x=\beta$. These yield exactly the two displayed sources,
and in both cases the old disequality holds. Conversely each displayed
source satisfies the literal, both guards and the entire old row.
Thus this is a full fiber equality, not a selected pair from a larger
source domain. Its signed record is eligible for the paid producer of
ARH Proposition 2.1.

For $Q=\varnothing$ the target is the entire original source. One actual
read at $L$ at epoch one gives $\beta$ on $u_0$ and branch on $u_1$.
Output the corresponding original source and halt. Both runs have exact
cost $(1,0,1)$.

Every source remains a pair under every update, so every root read is
branch on both sources at every available epoch. Before the first
nonroot read, all replies and common control are identical. A correct
service cannot halt with different sources as outputs there. Thus on
each of the two sources it must make at least one nonroot actual read,
giving $q\ge1$ and $\ell\ge1$; always $a\ge0$. Consequently the entire
Pareto basis is $\{(1,0,1)\}$ and the same-source weighted optimum is
$\lambda_q+\lambda_\ell$ for every nonnegative rational weight tuple.
The lower bound covers adaptive updates, early halts and absent reads;
zero weights do not require a different proof.

**Example 9.4 (finite full-row image with no bounded full-row selector).**
Reuse NSF Proposition 11.4. The root old row and the literal original
root reply branch give the entire domain of original pairs. At
$Q=\{L,R\}$ the reached set and exterior are constant, and the full row
has exactly two possible partitions, equal and unequal children.
Theorem 5.3 returns precisely these two rows; Theorem 6.2 permits a
zero-read exterior consumer.

For every original prefix depth $h$, choose $m\ge2(h+1)$ and compare

$$
\langle T_m,T_m\rangle,\qquad
\langle T_m,T_{m+1}\rangle.
\tag{NPL.27}
$$

Both are in the same entire fiber, agree through depth $h$, and have
different full partitions. The common-prefix fact follows from the
all-source branch saturation in NSF Lemma 9.2; $T_m\ne T_{m+1}$ follows
from the normal-code bijection. The ARH serial/static/prefix equivalence
therefore excludes a uniformly bounded full-row service. Deciding the
finite image neither adds an equality read nor installs a semantic
partition selector. CAR Proposition 9.1 supplies a further acquired,
coupled example of this same boundary at its own stated atomic scope.

**Example 9.5 (edge cases).** On any nonempty admitted fiber,
$Q=\{\varepsilon\}$ has a single full row and a zero-action consumer,
even if the source fiber is infinite. For $Q=\varnothing$ on the all-tree
fiber, the source projection is infinite and bounded recovery is
impossible by Theorem 7.1. On a singleton fiber every $Q$ has a known
constant row; $d-1=0$ in Theorem 8.1 and the Pareto basis is
$\{(0,0,0)\}$. An inconsistent signed history, including either sign
with a forced absent endpoint, has empty image rather than a fabricated
witness. The mathematical classifier accepts this empty case, while
all service assertions retain the nonempty-entry promise.

## 10. The remaining full-row and physical-word obligations

**Open problem 10.1 (uniform separation after finite-image classification).**
On an arbitrary infinite admitted signed fiber whose complete row image
has been classified as finite, decide whether

$$
\exists h\ge0\ \forall u,v\in D,\quad
\left[\forall |p|\le h, r_u(p)=r_v(p)\right]
\Longrightarrow R_Q(u)=R_Q(v).
\tag{NPL.28}
$$

Theorem 6.2 gives a bounded physical consumer for the reached set and
concrete exterior. Each remaining row predicate has decidable native
existential feasibility by NSF. Nevertheless the complete relation
between arbitrarily deep common prefixes and different partition bits
is not decided by these facts. Example 9.4 refutes the proposed inference
from a finite image alone. NSF Theorem 6.1 decides each supplied $h$,
but enumerating those decisions still lacks a general negative stopping
rule. The new projection theorem does not assert one.

**Open problem 10.2 (infinite-domain physical-word optimization).** On
an arbitrary infinite admitted signed fiber, decide feasibility of a
uniform $(q,a)$ budget when the physical read words have no supplied
length bound, and give the applicable complete Pareto and rational
same-source weighted interfaces. The all-source cap already bounds
useful actual epochs, but there is no finite union $\mathcal P_n$ of
known entire current sources to support Lemma 7.2. Theorem 8.1's finite
candidate-cardinality descent is likewise unavailable.

An INFINITE row-image result settles bounded raw recovery negatively;
a finite source-fiber result settles all the interfaces in §8 positively
and effectively. Between them, an infinite source fiber with finite row
image can have bounded or unbounded full-row recovery. Existing CAR,
SRF, CRF and GRS decisions continue to apply where their entire source
and action hypotheses hold. The new theorem neither weakens those
hypotheses nor repeats their recognized-family algorithms.

The two open obligations retain all signed constraints, original whole
outputs, actual same-register operations and separately charged resources.
No source-size parameter, finite representative domain or free producer
has been added. No undecidability or general native impossibility result
is inferred from these unresolved obligations.

## 11. Exact suppliers and evidence boundaries

**References 11.1 (repository deductions and supplied interfaces).**
Repository sources are read at the immutable [baseline][BASE]. The
following table separates reused statements from the new deductions.

| Source | Exact use and scope |
| --- | --- |
| [NSF §§2–4][NSF] | Finite native flattening, complete shape factorization, explicit scalar/block offset constraints and terminating existential feasibility. Its witnesses are not a parametrization of original solutions. |
| [NSF §§5–7][NSF] | Full guarded fixed-navigation compiler, entire signed-fiber feasibility and all-source operational restriction. Finite boxes and supplied-prefix decisions remain reused results. |
| [ABC Theorems 2.2–2.3 and 4.2][ABC] | Normal native codes, injective expansion, forward translation with its actual image condition, and exact reached-set/mask/partition reconstruction. |
| [ARH Assumption 1.3, Proposition 2.1, (2.3), Proposition 3.2][ARH] | Entire actually acquired fiber, source-total paid producer conditional on the complete cut, serial/static/prefix existence correspondence and both guarded source-cell directions. |
| [SLH Theorem 2.2][SLH] | Current physical decoding of original replies, including the one-read known-reached form used in (NPL.14). Historical decoded values are not past receipts. |
| [JRF Lemma 2.2, Theorem 3.1, Lemma 3.2][JRF] | All-source nonexpansive late probes, epoch-five cap retaining early actions, and constant/cached-reply cleanup. Its literal-only logical compiler is not applied to arbitrary signed histories. |
| [NSF Proposition 11.4][NSF]; [CAR Propositions 5.3 and 9.1][CAR] | Finite row image does not imply uniform physical observability. Their counterexamples retain their force. |
| §§3–4 of this volume | repo-derived: arbitrarily large original-solution marker families, free-rank pumping, universal output rigidity, the branch dichotomy and exact native projection-image decision. |
| §§5–8 of this volume | repo-derived: whole-row image classification from that decision, exterior limitedness with an actual consumer, whole-source classification, and complete finite-domain paid comparator/resource synthesis. |

**References 11.2 (formal-source inspection).** The native correspondence
is $\alpha=\mathtt{FreeMagma.of\ true}$,
$\beta=\mathtt{FreeMagma.of\ false}$, pairing $\mathtt{FreeMagma.mul}$,
and $\rho=\mathtt{substitution}$. Public declarations and the relevant
private/local proofs in the following source families provide existing
interfaces. Reading them is not a fresh compile of this volume.

| Source family | Exact interface and limit |
| --- | --- |
| [SourceTransportCentralizer][D5-CENTRAL] | `source_transport_centralizer`, with its local injectivity, classification and orbit arguments, supplies native injectivity and atomic stability. It states no arbitrary projection-image decision. |
| [NativeDepthPatterns][D5-DEPTH] | `depthEquiv`, private `fill_decompose`/`decompose_fill`, and `original_prefix_locality` give all-source original prefix decomposition and physical locality. `History` is `List (Nat × Address × Reply)`. |
| [NativeGroundSeparation][D5-GROUND] | `simultaneous_ground_separation` and private `compound_mass_ne`/`bounded_eval_injective` use equal-mass native markers. Lemma 3.1 uses NSF's one-constant shape variant with arbitrarily growing mass, not an unproved erasure of Boolean marker labels. |
| [NativeCutFibers][D5-CUT] | `rowFiberEquiv`, private `recover_fill` and `fill_injective` retain the entire old row and all class inequalities. |
| [NativeHistoryCells][D5-HISTORY] | `cell_feasibility_exact`, `historyCellEquiv` and private `syntax_iff_ground` cover literal histories and all old-class constraints, not arbitrary acquired signed subtree comparisons. |
| [NativeSymbolicRecutting][D5-RECUT] | `symbolic_recut_exact`, private `termAt_fill` and `exterior_commute` preserve reached order, concrete exterior and full equality partition beyond the supplied original cut depth. |
| [DelayedOriginalReadout][D5-READ] | `original_decoder_correct`, `original_decoder_service` and private `present_label_decode` identify the actual chronological read list and known-reached decoder. |
| [DelayedTemplateCertificate][D5-TEMPLATE] | `delayed_template_certificate`, `delayed_template_resources` and `delayed_template_service` give paid equality certificates for a supplied finite template. They do not by themselves classify all sources in an arbitrary signed fiber. |
| [Pinned mathlib Algebra/Free.lean][FREE] | FreeMagma's free constructors, decidable equality, lift and homomorphism extensionality. Shape unification is used only after native smart-pairing branches have been separated. |

**References 11.3 (primary-literature scope).** Kuncak and Rinard,
[*On the Theory of Structural Subtyping*][KR], arXiv:cs/0408015v1,
§6 and PDF Theorem 90/Corollary 91, supplies quantifier elimination and
sentence decision for its specified term-power language and a decidable
base structure. This is literature-attested at that exact interpreted
language. [TPO Definition 1.2 and Corollary 4.2][TPO] explain
why the native normal-domain predicate cannot simply be inserted as if
it were already a formula of that language. No such interpretation is
assumed here; the projection proof instead uses NSF's finite branch
reduction and the explicit arguments of §3.

Finite free-term unification, difference-equation graphs, finite
forbidden-value avoidance and finite decision trees are standard methods.
The present mathematical increment is their stated native projection
inference and its source-faithful consumers, classified as repo-derived.
This bounded comparison does not establish literature-wide novelty,
priority, absence of another decision method or undecidability of either
open problem. No external theorem is used to bridge unspecified physical
addresses to a logical address sort.

**Status 11.4 (what the evidence establishes).** The support for the new
claims consists of the ordinary universal proofs and exact examples
above, with the named suppliers at their stated hypotheses. No new Lean
build, experiment, implemented solver or physical run is asserted.
Structural document checks do not verify the mathematics. Exact paid
claims retain the acquisition, common-state and action assumptions of
§1; their finite-domain restriction is proved from the full input before
resource synthesis. These results do not complete the unrestricted
continuing recovery programme.

[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[CAR]: RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[BASE]: https://github.com/the-omega-institute/trureturing/tree/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c
[D5-CENTRAL]: https://github.com/the-omega-institute/trureturing/blob/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[D5-DEPTH]: https://github.com/the-omega-institute/trureturing/blob/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5-GROUND]: https://github.com/the-omega-institute/trureturing/blob/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c/D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.lean
[D5-CUT]: https://github.com/the-omega-institute/trureturing/blob/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[D5-HISTORY]: https://github.com/the-omega-institute/trureturing/blob/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c/D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[D5-RECUT]: https://github.com/the-omega-institute/trureturing/blob/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c/D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean
[D5-READ]: https://github.com/the-omega-institute/trureturing/blob/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c/D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[D5-TEMPLATE]: https://github.com/the-omega-institute/trureturing/blob/0457c83095ce46852f746bfa2d8b2d0bf04d1b8c/D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.lean
[FREE]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Free.lean
[KR]: https://arxiv.org/pdf/cs/0408015v1

## 追加锚（本行以下为增补区）
