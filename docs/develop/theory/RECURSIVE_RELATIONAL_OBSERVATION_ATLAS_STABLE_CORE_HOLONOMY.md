# Recursive relational observation: atlas-compatible stable cores and holonomy

**Convention (mathematical scope).** The carrier in this volume is one actual
jointly generated source, with a declared task and partial operation language.
The claims and proofs are ordinary mathematics. The mathematical ingredients
from [Typed Residual Resource Boundary](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_RESOURCE_BOUNDARY.md),
[Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md),
[Context Geometry](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) and
[Transport--Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)
retain their stated hypotheses. Source-code citations below identify reused
statements; they do not identify the present adaptations with Lean proofs.

## 1. Executable probes and relabelings

**Definition 1.1 (actual typed contract).** Let

$$
X=\bigsqcup_{i\in I}X_i
$$

be the actual image of a declared common source, closed under the operations
under consideration. An executable name $a:i\to j$ has a domain
$D_a\subseteq X_i$, a successor $T_a:D_a\to X_j$ and a complete response
$\ell_a$. The response distinguishes illegal access, legal success and legal
executed failure. An illegal action has no successor; a legal failure has its
declared successor, which may be a stopped state. Responses include every
task-visible event, record, selector decision, namespace, clock, inherited
meter and resource update. If an illegal request has a task-visible rejection
label, that label is also retained. External controls and initial records are
matched when two states are compared. Every selector or record update required
by the task is included among the compared readouts, at every reachable state.

The language is typed and contains every prefix of each declared finite
experiment. Every allowed continuation after a legal failure is included.
For chronological words $uv$, $T_{uv}=T_v\circ T_u$ on

$$
D_{uv}=\{x\in D_u:T_ux\in D_v\}.
\tag{1.1}
$$

The complete trace retains ordered labels and all declared terminal readouts.
It does not replace an archive by its task summary.

**Definition 1.2 (two transport contracts).** An executable probe
$e\in E_{\mathrm{probe}}$ has the same partial response contract as an
action, with successor $H_e:U_e\to X_k$. A pure relabeling
$e\in E_{\mathrm{rel}}$ is a partial bijection
$H_e:U_e\to V_e$ between actual subsets of two charts, with a declared inverse.
Its dictionaries identify the task fields in the two representations.
Relabelings impose representation compatibility; they supply no additional
experiment, readout, free recut or execution permission.

For a typed equivalence $R$, a relabeling descends precisely when $U_e$ and
$V_e$ are saturated for the respective restrictions of $R$, and both $H_e$
and its inverse preserve related pairs. In formulas,

$$
xRy\Longrightarrow (x\in U_e\Longleftrightarrow y\in U_e),\qquad
xRy, x,y\in U_e\Longrightarrow H_ex\,R\,H_ey,
\tag{1.2}
$$

with the corresponding conditions for $H_e^{-1}$ on $V_e$. Task-field
dictionaries must also be independent of the representative. These conditions
give a partial bijection between quotient charts: a class is in its domain
exactly when every representative is. Forward preservation alone gives neither
this domain property nor a descended inverse.

**Definition 1.3 (strict route equality).** A labeled partial route has its
actual domain, its full label word and its successor. Equality of two such
routes, after a declared comparison of label types, means equality of all
three. Agreement on their common domain is a weaker assertion. A coordinate
route can have no executable label, but a probe's event or resource word
cannot be erased by treating its state map as a relabeling. Pure relabeling
units and inverses concern partial coordinate maps; an immediate inverse
cancellation is an identity on its actual domain, which need not be the
whole chart.

The strict path-relation descent criterion is reused from Process Geometry,
Theorem 1.4: equality of domains, full labels and successors on generating
relations is equivalent to descent through their compositional congruence.
The total-domain tree normalization in Transport--Memory Completion §1.7
has whole-fiber bijections as a hypothesis.

## 2. The response-preserving stable core

**Definition 2.1 (typed refinement).** Let $K_0$ be a typed equivalence:
related points have the same type and the same declared initial observation.
It may impose additional restrictions on identification. For a typed equivalence
$R$, let $\operatorname{Ref}_{A,E_{\mathrm{probe}}}(R)$ consist of its pairs
$xRy$ such that, for every executable action or probe,

1. the pair has identical legality and complete response, including legal
   failures and any task-visible illegal rejection;
2. if legal, the two successors are $R$-related;
3. every task-required selector, namespace and record-update readout agrees
   for the pair, for each matched external input.

These are pairwise conditions on actual states. In particular they do not
assume that a selector factors through an equivalence merely because the
selector's name has been declared. Set

$$
R_0=K_0,\qquad R_{n+1}=\operatorname{Ref}_{A,E_{\mathrm{probe}}}(R_n),
\qquad R_\infty=\bigcap_{n\ge0}R_n.
\tag{2.1}
$$

**Theorem 2.1 (relative greatest stable core).** Under Definition 1.1,
every $R_n$ and $R_\infty$ is a typed equivalence. The latter is the largest
response-preserving invariant equivalence contained in $K_0$. All executable
domains, complete responses, successors and declared selector/update readouts
descend to $Q_i=X_i/(R_\infty|_{X_i})$. It is the coarsest such boundary
subject to $K_0$. It is an absolutely coarsest exact boundary for the declared
task if $K_0$ is exactly equality of type and initial task observations and
the compared fields and language are precisely that task's contract.

**Proof.** For each executable name, simultaneous legality and response
equality are reflexive, symmetric and transitive. On a legal pair, these
properties also hold for the requirement that successors be $R$-related.
The same is true of the selector/update equalities. Intersecting these
conditions with $R$ preserves equivalence and type. Refinement is monotone
and preserves nonempty intersections, since all of its tests are universal
pairwise tests. Thus

$$
\operatorname{Ref}(R_\infty)
=\bigcap_{n\ge0}\operatorname{Ref}(R_n)
=\bigcap_{n\ge0}R_{n+1}=R_\infty.
$$

If $S\subseteq K_0$ satisfies the same response and invariance conditions,
$S\subseteq R_n$ implies $S\subseteq\operatorname{Ref}(R_n)=R_{n+1}$.
Induction gives $S\subseteq R_\infty$. The fixed-point conditions give
saturated executable domains and representative-independent labels and
successors, which define the quotient operations. If $K_0$ has extra
constraints, maximality is only within those constraints. If it is exactly
the initial task-observation kernel, every exact task representation has a
kernel contained in $K_0$ and satisfying these pairwise conditions; hence its
actual image maps uniquely onto $Q$. This proves the final assertion.
$\square$

**Mathematical citation 2.2 (reused mechanisms).** The greatest-invariant
subkernel construction is already present in
[MaximalForwardInvariantSubkernel](../../../D5/S1/FixedPoints/MaximalForwardInvariantSubkernel.lean),
`maximal_forward_invariant_subkernel`, for a total self-map.
[TypedFiniteViewKernel](../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean),
`typed_finite_view_kernel`, relates typed finite-path views, refinement and
complete behavior. [DynamicsDescent](../../../D5/S0/Rewriting/Quotients/DynamicsDescent.lean),
`dynamics_descends_iff`, supplies the fiber-preserving total-map criterion.
[StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean),
`contextual_equivalence_is_greatest` and `signature_extension_refines`,
supply strong partial-operation congruence and signature enlargement.
Theorem 2.1 uses these established mechanisms with explicit complete-response
and selector conditions; these mechanisms are intermediate ingredients, not
a claim of new fixed-point or factorization theory.

**Proposition 2.3 (an executable recut can refine memory).** Let
$X=\{x,y,u,v\}$, with constant initial observation and no informative ordinary
actions. Add an executable probe $e$ taking $x$ to $u$ and $y$ to $v$, with
equal labels, and a read probe $b$ returning zero at $u$ and one at $v$.
The action-only stable core merges $x,y$, whereas the enlarged core separates
them.

**Proof.** Ordinary continuations produce equal observations from $x,y$.
The allowed word $eb$ produces different labels. Any response-preserving
invariant equivalence merging $x,y$ would have to merge $u,v$ after $e$ and
then preserve the unequal $b$ labels, a contradiction. $\square$

A pure relabeling is excluded from (2.1). If it does not satisfy (1.2) for
$R_\infty$, that quotient does not support the proposed atlas. Refining the
relation for representation compatibility is an additional constraint, not
evidence that a new physical experiment distinguishes the original pair.

## 3. Residual routes, complete squares and presentation relations

**Definition 3.1 (declared residual route lift).** For a coordinate route
$e:i\rightsquigarrow k$ and an action $a:i\to j$, declare a matched name
$a^e:k\to\ell$, an output route $e/a:j\rightsquigarrow\ell$ and an invertible
complete-response dictionary $\Lambda_{e,a}$. The output route need not be
$e$. Let $C_{e,a}\subseteq U_e$ be the task-required crossing domain.
On this domain the complete square contract is

$$
\begin{aligned}
x\in D_a&\Longleftrightarrow H_ex\in D_{a^e},\\
T_ax&\in U_{e/a}\quad (x\in C_{e,a}\cap D_a),\\
H_{e/a}T_ax&=T_{a^e}H_ex,\\
\ell_{a^e}(H_ex)&=\Lambda_{e,a}(\ell_a(x)).
\end{aligned}
\tag{3.1}
$$

The last equation includes illegality, failures, resources, records and
selectors, wherever that response is declared. The two composed legal
routes have exactly the common domain $C_{e,a}\cap D_a$ after restriction
to $C_{e,a}$. Initial and terminal task observations have their declared
coordinate dictionaries as well. All crossing domains are saturated for the
relation through which the square is to descend. Relabeling dictionaries,
matched actions and residual routes must be representative independent.
No statement about points outside $C_{e,a}$ is part of this square.

**Theorem 3.1 (complete square descent).** Suppose executable data descend
through $R_\infty$, the two coordinate routes satisfy (1.2), and the full
contract (3.1) holds. Its induced square on the actual quotient crossing
domain has equal legal domains, transported complete responses and equal
successors. Conversely, a square on a quotient need not give equality of
hidden original successors; it gives only equality of their quotient classes.

**Proof.** Saturation allows a quotient class to enter the crossing or legal
domain without choosing a privileged representative. All responses and maps
are independent of that choice. For a legal representative $x$, the two
successors agree by (3.1), hence have the same class. The response equation
and simultaneous illegality descend by the same representative argument.
Pulling a quotient square back only yields related successors, so the
converse has exactly the stated weaker conclusion. This is the strict
fiberwise descent argument of Process Geometry Theorem 3.2, applied to the
declared complete square. $\square$

**Theorem 3.2 (finite continuation and route-presentation compatibility).**
Assume every required initial crossing and every reachable legal prefix has
its declared lift, and the family of routes is closed under the resulting
residual routes. Then the one-step contract (3.1) is equivalent to its
finite-continuation contract: for each required word $u$, its matched word
$u^e$ is simultaneously legal, has the stepwise transported complete trace,
and, if legal, satisfies

$$
T_{u^e}H_ex=H_{e/u}T_ux.
\tag{3.2}
$$

Illegal prefixes agree as rejected requests; executed failures follow their
declared successors. The assertion includes the terminal observation
transport, and applies only on the recursively declared actual crossing
domain.

For independence of a presentation of the route, additionally require that
the lift respect units, composition and a generating family of *strict*
route relations. On a composite route $ed$, the one-step composition laws are

$$
a^{ed}=(a^e)^d,\qquad
(ed)/a=(e/a)(d/a^e),
\tag{3.3}
$$

with composite dictionaries and exact restricted domains. For each generating
relation $e\equiv e'$, matched names and dictionaries agree and
$e/a\equiv e'/a$ on the same crossing domain. These conditions imply that
all finite lifted continuations respect the compositional route congruence,
including their exact domains and complete labels.

**Proof.** Define $\epsilon^e=\epsilon$ and $e/\epsilon=e$. If $u$ has been
lifted, append the name $a^{e/u}$ and set $e/(ua)=(e/u)/a$. The prefix
hypothesis puts the related successors in the next crossing domain. Equation
(3.1) there gives simultaneous legality, the next label dictionary and the
new successor square; composing it with the induction hypothesis proves
(3.2). At the first illegal request neither side has a successor and their
rejection responses match. A legal failure remains an ordinary legal step
in this induction. The empty word gives the initial observation equation;
the length-one words recover (3.1), proving equivalence.

For presentation independence, a replacement $e\equiv e'$ has equal actual
route domains and, by hypothesis, equal crossing domains and one-step data.
After the first legal action its residual routes are still related. Induction
on word length gives the same lifted names, dictionaries and terminal
coordinate map for every required finite word. Replacing the route inside
prefix and suffix route contexts preserves these equalities by (3.3) and
exact domain composition. A finite chain of such replacements preserves
strict equality by transitivity. Process Geometry Theorem 1.4 supplies the
underlying strict path congruence argument; the additional induction here
ensures the residual lift respects that same presentation. $\square$

**Proposition 3.3 (a fixed-route normalizer is not necessary).** There is a
faithful partial-chart task satisfying the residual square whose fixed input
route cannot remain the output route.

**Proof.** In each of two charts take states $0,1$ and the action $T:0\mapsto1$.
Let $r_0$ transport $0$ to its copy in the other chart, and let $r_1$ transport
$1$ to its copy. All responses are identical under the copy dictionaries.
On the required domain $\{0\}$,

$$
Tr_0=r_1T,
$$

including legality and complete labels. But $r_0T$ is undefined there,
because $T0=1$ is outside $r_0$'s domain. Each chart retains the states
faithfully. The output residual route is $r_1$, not $r_0$. $\square$

**Proposition 3.4 (state squares do not determine resource squares).**
Singleton states and trivial holonomy can satisfy the successor square while
violating (3.1).

**Proof.** Take singleton source and target charts, identity coordinate
transport, and matched total identity actions $a,b$. Both emit zero, but
$a$ costs one and $b$ costs two in the same fixed resource unit. The successor
maps and all coordinate loops are identities. The declared identity response
dictionary cannot identify the unequal costs. Thus their full square fails.
$\square$

## 4. The partial atlas and the corrected frame criterion

**Definition 4.1 (actual transport quotient).** Suppose all coordinate routes
have descended to partial bijections between the charts $Q_i$ of §2. Retain
every edge identity, every actual domain and a true partial inverse for each
edge. Let $Z=\bigsqcup_i Q_i$ and let $\sim$ be the equivalence relation
generated by $q\sim H_eq$ for $q$ in an edge domain. Write

$$
Y=Z/{\sim},\qquad \iota_i:Q_i\to Y.
\tag{4.1}
$$

A transport word $p:i\rightsquigarrow j$ is executable as a coordinate
comparison at $q$ precisely when every successive partial map is defined.
This mathematical comparison does not grant a physical operation.
An actual closed path at $i$ acts by a partial bijection $H_p:D_p\to Q_i$;
it is not in general a total endomap of $Q_i$.

**Theorem 4.1 (minimal partial-atlas recovery criterion).** The following
conditions are equivalent:

1. every $\iota_i$ is injective;
2. for every chart $i$, every actual closed transport word $p:i\rightsquigarrow i$
   and every $q\in D_p$, $H_pq=q$;
3. there is a carrier $W$ and injections $f_i:Q_i\hookrightarrow W$ such
   that $f_j(H_eq)=f_i(q)$ on every actual edge domain.

When they hold, each chart is bijective with its own image $\iota_i(Q_i)$
in $Y$. No chart is thereby required to cover all of $Y$. The quotient $Y$
is the universal carrier for maps obeying just these edge identifications.

**Proof.** Each finite equivalence chain is an actual word: a forward
identification is an edge and a backward identification is its partial
inverse. Its successive values witness that the entire word is defined.
If two points of the same chart have the same image in $Y$, such a chain
is a closed path between them. Condition 2 therefore implies they are equal,
giving 1. Conversely, a closed path identifies its input and output in $Y$;
1 makes them equal, giving 2. Condition 1 gives 3 with $W=Y$. Under 3, every
identification chain has constant $f$ value; a closed chain in one chart
then has equal endpoints by injectivity, giving 2. A compatible family of
maps from the charts is constant along chains, hence has a unique factor
through $Y$. This also proves universality and the image bijections.
$\square$

This theorem is about state coordinates on each route's domain. It does
not say that all parallel partial paths have the same domains or labels.

**Corollary 4.2 (actual coverage for a full root frame).** Fix a root chart
$Q_o$. Under Theorem 4.1, every chart has injective root coordinates if every
actual point can be transported to some point of $Q_o$. These coordinates
are bijections $Q_i\cong Q_o$ for every $i$ if and only if every transport
orbit meets every chart. Equivalently, every $q\in Q_i$ has an actual route
to the root and every root point has an actual route to each chart.

**Proof.** Root coverage says $\iota_o(Q_o)=Y$; injectivity then gives a
unique root representative of every orbit. Composing $\iota_i$ with this
inverse defines injective coordinates. They are onto $Q_o$ exactly when
every root orbit also meets $Q_i$. A chain witnessing an orbit intersection
is an actual transport path by the proof of Theorem 4.1. Thus the two route
coverage clauses are both necessary and sufficient. The coordinates commute
with partial transports on their domains. Conversely, compatible bijective
coordinates *realized by actual root transport* imply these coverage clauses
and make all closed paths identity. Arbitrary set bijections with no actual
root realization do not imply coverage. $\square$

**Proposition 4.3 (complete comparisons, domains and labels).** In Theorem
4.1 condition 2 can be tested on a selected loop family $\Gamma$ if a
domain-aware generation proof is supplied: every closed actual word must,
at each point of its domain, be a legal finite composite of conjugates of
loops in $\Gamma$ and their inverses, and partial identity restrictions.
Each conjugation and each intermediate value must be in its actual domain.
Then identity of all selected loops on their domains implies condition 2.
An arbitrary selected family has no such implication.

For strict endpoint-only equality of full routes an additional comparison
requirement is necessary: every compared parallel pair must have equal
actual domains, equal complete transported labels and equal successors.
It suffices to check a family generating all those pairs by strict
compositional relations. Flat partial holonomy alone proves only equality
of successors where both routes are defined.

**Proof.** A conjugate of a partial identity is identity wherever the
conjugation is defined; a legal finite composite of such maps is identity
on its domain. The assumed generation gives the first implication. For
parallel paths $p,q$ both defined at $x$, the actual closed word $p q^{-1}$
starting at $x$ is not always defined: $H_px$ might not be in the image of
$q$. Instead, the reverse of $p$ followed by $q$ is defined at $H_px$ and
returns to the target chart with output $H_qx$. Flatness there yields
$H_px=H_qx$. This establishes equality on the common domain without an
unsupported domain inclusion. Equal domains and full labels still require
the additional strict comparison data. Sufficiency of a complete generating
comparison family is Process Geometry Theorem 1.4. $\square$

**Proposition 4.4 (parallel-edge obstruction to an incomplete loop test).**
Let $Q_0=Q_1=\{0,1\}$. Give two named, total transports $e,d:0\to1$,
with $H_e$ identity and $H_d$ swap, and their true inverses. Let $\Gamma$
contain only immediate inverse cancellations. Every selected loop acts
identically, but there is no faithful endpoint-only frame and no embedding
atlas as in Theorem 4.1.

**Proof.** An edge followed by its own inverse is identity. However
$ed^{-1}$ swaps the two points in $Q_0$. The two routes $e,d$ assign different
endpoint coordinates to the same input. If both charts injected into $W$
compatibly, identity transport would give $f_0(0)=f_1(0)$ while swap transport
would give $f_0(0)=f_1(1)$, contradicting injectivity of $f_1$. Thus the
selected cancellations do not generate the required comparisons. $\square$

**Proposition 4.5 (connected base without fiber coverage).** Let
$Q_0=\{a\}$, $Q_1=\{b,c\}$, and let the only nontrivial transport send
$a$ to $b$, with its inverse. Every actual closed word is identity, and the
base graph is connected. Nevertheless no full root frame exists. The
partial atlas is

$$
Y=\{[a,b],[c]\}.
$$

**Proof.** Every nonempty legal closed path alternates the edge and its
inverse, so returns to its input. At $c$ only the empty path is legal. The
orbit classes are exactly the two displayed classes, and both chart maps
are injective. The orbit $[c]$ has no root representative; furthermore the
fiber cardinalities differ. Connectedness of chart names therefore does
not yield whole-fiber transport. $\square$

**Proposition 4.6 (flatness does not equalize route domains).** In one chart
$Q=\{0,1\}$ take a coordinate self-edge that is identity only on $\{0\}$,
with the same partial inverse. All actual loops are identity on their
domains and $Q\hookrightarrow Y$ is injective. This edge is not strictly
equal to the empty route, whose domain is all of $Q$.

**Proof.** Every nonempty composable word in the partial edge is identity
on $\{0\}$, whereas the empty word is identity on both points. There are
no identifications between distinct points, but the displayed domains are
unequal. $\square$

**Proposition 4.7 (orbit gauge criterion).** Let each $Q_i$ have a declared
task gauge equivalence $\approx_i$, such as the orbits of a specified group
of automorphisms preserving the complete task contract. Suppose each edge
domain and image is orbit saturated, and each partial transport and inverse
preserves orbit equivalence; all response dictionaries and task operations
also descend to these orbit quotients. The orbit charts embed into their
transport quotient if and only if every actual closed path sends each input
to its own orbit. Full orbit frames require the coverage of Corollary 4.2
on the orbit charts. Membership of some selected loop maps in a gauge group,
without these domain, descent and comparison conditions, is insufficient.

**Proof.** Saturation and orbit preservation give true partial bijections
$Q_i/\!\approx_i\dashrightarrow Q_j/\!\approx_j$. Saturation permits an
actual representative to lift every successive quotient-domain step, so a
closed quotient word has an actual closed lift. Identity of that word on
the orbit chart is exactly $H_pq\approx_i q$. Apply Theorem 4.1 and
Corollary 4.2 to these quotient charts. Descended response and operation
data retain precisely the stated gauge-invariant task. $\square$

**Corollary 4.8 (gluing dynamics through residual routes).** Under Theorem
4.1, choose an action $a_i:i\to j(i)$ in every chart. In this statement
all domains and squares are the induced data on the quotient charts $Q_i$.
Let $L_i(q)$ be its complete response decoded into common task fields,
defined for every $q\in Q_i$: it includes legality and every task-visible
illegal rejection as well as legal success and failure. Suppose the
following hold for every named edge $e:i\rightsquigarrow k$ used to
generate $\sim$ in Definition 4.1 and its declared inverse:

1. the matched action is exactly $a_i^e=a_k$, and the crossing domain is
   the entire actual edge domain, $C_{e,a_i}=U_e$;
2. the full square (3.1) holds at every $q\in U_e$, including its legality
   and response equations at illegal inputs, and its response dictionary
   agrees with the common decoding, so $L_k(H_eq)=L_i(q)$;
3. the residual output route $e/a_i$ is an actual atlas word, defined at
   every $T_{a_i}q$ with $q\in U_e\cap D_{a_i}$, and
   $H_{e/a_i}T_{a_i}q=T_{a_k}H_eq$;
4. the decoded initial observations agree at every such edge
   identification, on all of $U_e$.

Then the chosen action has a saturated legal domain and well-defined
successors, complete decoded responses and initial observations on the
entire union carrier $Y$. Explicitly, writing $[q]=\iota_i(q)$,

$$
\begin{aligned}
\overline D&=\{[q]:q\in D_{a_i},\ i\in I\},\\
\overline T([q])&=[T_{a_i}q]\quad([q]\in\overline D),\\
\overline L([q])&=L_i(q)\quad([q]\in Y).
\end{aligned}
\tag{4.2}
$$

Its iterates descend as well. More generally, require these whole-edge
hypotheses for every action choice in a declared continuation menu to glue
that menu and all its finite continuations. If the residual lifts also
satisfy the route-presentation hypotheses of Theorem 3.2, those
continuations descend with that presentation.

**Proof.** For every generating identification $q\sim H_eq$, hypothesis
1 puts the point in the full square's crossing domain. Hypothesis 2 gives
identical legality and complete decoded responses even when the request is
illegal. If legal, hypothesis 3 joins the two successors by an actual
residual atlas word, so they have the same class in $Y$. Hypothesis 4 gives
the initial-observation equality. Each comparison also holds in the reverse
orientation.

Any two representatives of a point of $Y$ are joined by a finite chain of
these actual edge identifications and their inverses. Propagating legality
along that chain makes the disjoint union of the $D_{a_i}$ saturated: either
every representative is legal or every representative is illegal. In the
legal case, each link gives equal successor classes, and transitivity gives
the same class at both ends. In either case, each link gives equal complete
decoded responses, including any rejection, and equal decoded initial
observations. This proves every representative-independence assertion in
(4.2); at an illegal class there is no successor. The universal property of
$Y$ gives the descended responses and observations, and the saturated
domain gives the partial operation. Induction on the word length proves
the continuation assertion, retaining the full response at each legal or
first illegal prefix and following actual successors after legal failures.
The presentation assertion is then Theorem 3.2 under its stated hypotheses.
$\square$

The whole-edge requirement concerns every identification used to form
$Y$. A task-local square on $C_{e,a_i}\subsetneq U_e$ leaves the links at
$U_e\setminus C_{e,a_i}$ unconstrained. Flatness and orbit coverage control
state identifications, but do not supply legality or response comparisons
at those links. Gluing on a smaller transport-saturated carrier is a
separate restricted assertion.

**Proposition 4.9 (task-local squares need not glue the full carrier).**
There is a flat atlas whose every orbit meets every chart, with compatible
initial observations, equality stable chart cores and complete residual
squares on all declared task-local crossing domains, but whose chosen
chart actions do not have a well-defined legal domain on $Y$.

**Proof.** Let $Q_0=\{x_0,z_0\}$ and $Q_1=\{x_1,z_1\}$, with the total
copy transport $e$ and its inverse. Both charts are actual copies of the
same two-point source. Include also the copy transport $r$
restricted to $\{x_0\}$ and its inverse as residual atlas routes. Initial
observations distinguish $x_i$ from $z_i$ and agree between copies, so the
stable core in each chart is equality. Choose $a_0$ to be total identity
and $a_1$ to be identity only on $\{x_1\}$, illegal at $z_1$. Use the same
complete-response type and identity dictionaries in both charts: legal
inputs report success, illegal inputs report rejection, and all other
task fields are constant.

For $e$ declare $C_{e,a_0}=\{x_0\}$ and residual $e/a_0=r$; for its
inverse use $\{x_1\}$ and $r^{-1}$. For $r,r^{-1}$ use their entire
singleton domains and the same residual routes. On every declared crossing
the actions are legal identities, their complete responses agree, and the
residual route joins their successors. Repeated actions stay at $x_i$, so
the same squares hold for all finite task-local continuations. Every actual
transport preserves the letter $x$ or $z$, and a closed word returns to its
input. Thus the atlas is flat, its chart maps are injective, and its two
orbits $[x_0,x_1]$ and $[z_0,z_1]$ each meet both charts. Nevertheless
$[z_0]=[z_1]$ is legal when represented by $z_0$ and illegal when
represented by $z_1$. Its decoded responses also disagree. The missing
comparison is precisely the point $z_0\in U_e\setminus C_{e,a_0}$.
$\square$

## 5. When action closure commutes with transport compatibility

**Definition 5.1 (two relation closures).** In this section all operations
$T_a:X\to X$ are total on one carrier, and $H$ is a group of bijections of
$X$. Empty words act identically. For an equivalence $K$ define

$$
\begin{aligned}
\operatorname{Core}_A(K)
 &=\{(x,y):\ \forall u\in A^{\ast},\ (T_ux,T_uy)\in K\},\\
\operatorname{Sat}_H(K)
 &=\{(x,y):\ \forall h\in H,\ (hx,hy)\in K\}.
\end{aligned}
\tag{5.1}
$$

Here $\operatorname{Sat}_H$ means an intersection of transported relations,
so it is a *refinement* of $K$, not the union of its gauge orbits. It enforces
representation compatibility. Group bijections in this definition are not
necessarily executable probes. If they are executable, their full response
contract must additionally be retained.

**Theorem 5.1 (normalizer bridge).** Suppose for every $h\in H$ there is a
permutation $a\mapsto h.a$ of the full declared action menu, satisfying

$$
hT_ah^{-1}=T_{h.a}.
\tag{5.2}
$$

Then for every equivalence $K$,

$$
\operatorname{Core}_A(\operatorname{Sat}_H(K))
=\operatorname{Sat}_H(\operatorname{Core}_A(K))
=\operatorname{Core}_{A\cup H}(K).
\tag{5.3}
$$

Consequently the representation-compatible refinement of the action core
is still action stable, and it is the largest $A$- and $H$-invariant
equivalence inside $K$. If $K$ is already $H$-invariant, then
$\operatorname{Core}_A(K)$ admits transport descent without further
refinement. For $K$ encoding complete process observations, the corresponding
semantic assertion requires complete response covariance under the same
menu and invertible dictionaries.

**Proof.** The first relation in (5.3) tests $K(hT_ux,hT_uy)$ for every
$u,h$. The second tests $K(T_uhx,T_uhy)$. Extend the menu permutation
letterwise to words. Equation (5.2) gives $hT_u=T_{h.u}h$ and
$T_uh=hT_{h^{-1}.u}$. Since these substitutions biject the full word menu,
the two universal tests are identical. Moving each group letter to the
left by this identity rewrites every finite mixed transformation as
$hT_u$; every such transformation is itself a mixed word. Thus the same
tests are exactly the third relation in (5.3).

The word-intersection construction is the reused greatest-invariant
subkernel mechanism: a stable relation inside $K$ remains inside $K$
after every word, hence is contained in that intersection. It follows that
the common relation is invariant under the enlarged transformation menu.
If $K$ is $H$-invariant, $\operatorname{Sat}_H(K)=K$, so (5.3) says its
action core is also $H$-invariant. For complete process observations, moving
an action past a transport must move its complete label by the declared
dictionary as well as its state successor. Otherwise the state-relation
identity remains true but does not assert a complete semantic square.
$\square$

**Corollary 5.2 (precise partial-operation version).** Theorem 5.1 applies
to partial self-operations on $X$ if the transports are total bijections
and the conjugacy is exact:

$$
h(D_a)=D_{h.a},\qquad
h(T_ax)=T_{h.a}(hx)\quad(x\in D_a).
\tag{5.4}
$$

Totalize each operation on $\widehat X=X\sqcup\{\bot\}$ by sending an
illegal input to the new absorbing $\bot$; let every transport fix $\bot$.
Use an observation equivalence $\widehat K$ that isolates $\bot$ and records
the actual complete response of every name, including legal failures and
task-visible illegal rejections. If these observations have the required
invertible response covariance, (5.3) on $\widehat X$, restricted to $X$,
gives the greatest complete-response-preserving equivalence compatible with
both partial actions and those transports **among equivalences contained
in $\widehat K|_{X\times X}$**. Thus its boundary is coarsest subject to
that ambient restriction. An exact task-observation kernel is an additional
hypothesis for deriving absolute task minimality by this argument; an
arbitrarily finer $\widehat K$ does not supply it.

**Proof.** Exact domain conjugacy makes the totalized maps satisfy (5.2)
on both legal and illegal inputs, and on $\bot$. Apply Theorem 5.1. The
isolated sink makes legality visible in the word tests; the other observation
fields retain the complete response at each actual prefix. A legal failure
has its actual successor in $X$, possibly a stopped state, and is never
identified with $\bot$. Restricting the greatest stable relation to actual
states gives the asserted pairwise semantics and retains containment in
$\widehat K|_{X\times X}$, since the empty word is one of the tests.
Conversely, any complete-response-preserving equivalence $S$ on $X$ inside
that restriction, invariant under legal successors and transports, extends
to $\widehat S=S\cup\{(\bot,\bot)\}$. Identical legality makes it invariant
under the totalized actions, and the transports fix its isolated sink.
It is contained in $\widehat K$, so Theorem 5.1 puts it inside the joint
core. This proves exactly the relative maximality claimed.

The restriction cannot be discarded: take two actual points with the same
initial observation, one total identity action with identical complete
responses, and only the identity transport. If $\widehat K$ is equality
on $X\sqcup\{\bot\}$, the joint core restricted to $X$ is equality.
Yet the universal equivalence on the two actual points preserves this
entire task and its transports. Thus a finer ambient observation can force
distinctions beyond the task. The auxiliary sink is an interpretation of
illegality, not a newly executable state. $\square$

This corollary concerns global transports and exact conjugacy. General
partial-chart tasks use the residual routes of §3; Proposition 3.3 proves
that fixed-route normalization is a sufficient special case rather than a
necessary condition for those tasks.

**Proposition 5.3 (finite obstruction to commuting the closures).** Take
$X=\{0,1,2,3,4\}$, the observation and action tables

$$
q=(0,0,0,0,1),\qquad f=(0,0,1,4,4),
\tag{5.5}
$$

and let $g$ swap $0,3$, fixing the other points. For $K=\ker q$, the relation
$\operatorname{Sat}_{\langle g\rangle}(\operatorname{Core}_f(K))$ is not
$f$-invariant. In particular it differs from the joint mixed-word core.

**Proof.** Under repeated $f$, the points $0,1,2$ always read zero; $3$
reads zero once and then one forever; $4$ reads one forever. Hence
$\operatorname{Core}_f(K)$ has blocks $\{0,1,2\},\{3\},\{4\}$.
Intersecting this relation with its pullback by $g$ gives the blocks
$\{0\},\{1,2\},\{3\},\{4\}$. Thus $1,2$ remain related, but their
$f$ images $0,1$ do not. The chronological mixed word $f,g,f$ takes
$1\mapsto0\mapsto3\mapsto4$ and
$2\mapsto1\mapsto1\mapsto0$, whose final $q$ values are one and zero.
The joint core must therefore separate the pair. There is no complete
normalizer law for this menu: $gfg^{-1}(0)=4$ whereas $f(0)=0$.
$\square$

If $g$ is a pure relabeling, this obstruction says the once-refined relation
fails action descent; the mixed words test representation compatibility.
If $g$ is a permitted executable probe with its own complete contract,
$f,g,f$ is an enlarged experiment. Those are different interpretations of
the same finite relation calculation.

## 6. Refinement completion and individual four-view recovery

**Mathematical ingredient 6.1 (inverse-limit realization).** Let
$Q_n=X/R_n$ and $\rho_n([x]_{R_{n+1}})=[x]_{R_n}$. The canonical map

$$
\Theta:X\to\varprojlim_nQ_n,\qquad
\Theta(x)=([x]_{R_n})_{n\ge0}
\tag{6.1}
$$

has kernel $R_\infty$. Its factor from $X/R_\infty$ is injective and is
surjective precisely under ThreadComplete: every coherent thread has one
actual representative in $X$. These are the inverse-limit and actual-image
ingredients of
[InverseLimitCompletion](../../../D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean),
`stateThread_injective_iff_separates` and
`stateThread_bijective_iff_complete_and_separates`, applied after quotienting
by all-stage agreement. If the chain stabilizes at a finite stage, its
threads are actual stable classes, so ThreadComplete holds. In particular
this holds for finite $X$.

The kernel assertion follows because two points have the same thread
exactly when they are $R_n$-related for every $n$. Surjectivity is precisely
the stated actual-representative condition. In a stabilized chain the later
bonding maps are bijections and a stable class supplies every thread.
These are reused completion ingredients rather than new atlas sufficiency
conditions. A transport must additionally descend at each compared stage
and commute with its bonding maps; descent only at the limiting core does
not establish finite-stage descent.

**Proposition 6.2 (a compatible but nonactual thread).** On $X=\mathbb N$,
let $R_n$ be equality modulo $2^n$. There is a coherent thread with no actual
natural representative.

**Proof.** Choose residues $r_n=2^n-1$ modulo $2^n$, including the unique
residue at $n=0$. Each reduces to the previous one. If $m\in\mathbb N$
represented them all, then for $2^n>m+1$ its residue would be $m$, which is
strictly smaller than $2^n-1$, a contradiction. $\square$

**Theorem 6.3 (four views on one actual stable image).** Let
$q_{\mathrm{sp}},q_{\mathrm{tm}},q_{\mathrm{bd}},q_{\mathrm{mem}}$ be maps on
this same $X$. Suppose each individually has kernel $R_\infty$ and supports
all descended executable responses, selectors and updates. Suppose its
coordinate transports satisfy (1.2), its complete squares and route
presentation satisfy §3, and its atlas satisfies the appropriate partial
or full criterion of §4. Then each actual view image is uniquely bijective
with $Q=X/R_\infty$; these bijections intertwine the specified operations
and transports. Chartwise recovery gives the corresponding bijections with
$\iota_i(Q_i)$, and covers all of $Y$ only under the appropriate actual
coverage condition. If only the joint map of the four views has kernel
$R_\infty$, no individual sufficiency follows.

These chartwise assertions retain the task-local crossing domains of §3.
For dynamics and complete responses on the entire glued carrier $Y$,
additionally require the whole-edge hypotheses of Corollary 4.8 for every
action being glued.

**Proof.** For each view, send $q_v(x)$ to $[x]$. Kernel equality is exactly
well-definedness and injectivity, and restriction to the actual image gives
surjectivity and uniqueness. The descended responses and successors
intertwine because their values agree on every representative. Apply the
same factorization chartwise and then Theorem 4.1 or Corollary 4.2. A joint
kernel is the intersection of the component kernels, which does not force
any one of them to equal that intersection. For example on $\{0,1\}^2$,
the two coordinate projections, repeated as four views, jointly separate
points, while each projection merges a pair. With the additional whole-edge
hypotheses, Corollary 4.8 supplies the operations and complete responses
throughout $Y$. $\square$

**Convention 6.4 (interpretation boundary).** A spatial view may encode
coordinate overlap and adjacency; a temporal view may encode ordered
continuations and declared clock labels; a boundary view encodes the stable
quotient; a memory view is its task-accessible realization. Theorem 6.3
requires each chosen view to retain the same task distinctions. Merely
naming a graph spatial or a sequence temporal does not satisfy its kernel
or operation hypotheses. Set-theoretic inverse maps imply neither algorithms,
resource bounds, acquired access to an unknown source nor a physical
spacetime construction. The actual image, ThreadComplete and the specified
operation permissions remain separate conditions.

## 追加锚（本行以下为增补区）

## 7. A finite linear source: forward memory versus permitted recuts

**Definition 7.1 (linear prefix contract).** Let $\mathbb F_q$ be a finite
field, let $H:\mathbb F_q^n\to\mathbb F_q^m$ be linear, and let
$C=\ker H$. At cut $k$, partition its columns as

$$
H=[H_P\ H_F],\qquad
r_P=\operatorname{rank}H_P,\quad
r_F=\operatorname{rank}H_F,\quad r=\operatorname{rank}H.
\tag{7.1}
$$

The actual states at every cut $j$ are the extendable prefixes of codewords
in this one family. Thus at the chosen cut,

$$
U_k=\{p\in\mathbb F_q^k:\ \exists f\in\mathbb F_q^{n-k},
                       \ H_Pp+H_Ff=0\}.
\tag{7.2}
$$

The forward contract has a name $\operatorname{append}_a$ for each field
symbol $a$, legal exactly when the longer prefix $pa$ is extendable. Its
successor is $pa$, and its complete label is the requested symbol and its
status; all other task fields are constant or functions of these and the
known cuts. The root observation is just the cut. No task-visible query
returns the entire existing prefix. There is no pre-existing full prefix
archive in this contract. The declaration supplies all finite append
continuations, including rejected requests, and stops appending at cut $n$.

The enlarged contract also permits every name $\operatorname{delete}_a$,
legal precisely when the current nonempty prefix ends in $a$. Its successor
removes that symbol. The label records its name and legality. A deleted
prefix is still extendable. Both kinds of operation act only on the actual
prefix family. They are partial deterministic construction/comparison
permissions of this model, not an assertion of physically free access to
an unknown prepared source or to the unseen tail of a fixed codeword.
If an archive, source identifier, varying resource meter or independently
accessible prefix is included, its response kernel must instead be included
and the forward count below need not be the task's minimal count.

**Theorem 7.2 (recut permission separates a hidden prefix factor).** For
Definition 7.1 at the known cut $k$, the forward exact boundary has

$$
N_{\mathrm{forward}}(k)=q^{r_P+r_F-r}
\tag{7.3}
$$

states, represented by the syndrome $H_Pp$ in
$\operatorname{im}H_P\cap\operatorname{im}H_F$. With all labeled append and
delete probes, the exact boundary is the actual prefix itself and has

$$
N_{\mathrm{recut}}(k)=q^{k+r_F-r}
=q^{k-r_P}N_{\mathrm{forward}}(k)
\tag{7.4}
$$

states. Each forward state has exactly $q^{k-r_P}$ enlarged states above it.
When $k-r_P>0$, some delete domain at a reachable cut is not saturated under
forward behavioral equivalence, so the enlarged recuts cannot all descend as pure
relabelings of that boundary.

**Proof.** The future completion set of $p$ is

$$
F(p)=\{f:H_Ff=-H_Pp\}.
\tag{7.5}
$$

It is nonempty by actual extendability. Two prefixes have the same set
$F(p)$ exactly when they have the same syndrome: equality follows from
the same defining equation, and a shared completion forces the two right
sides to be equal. Equality of completion sets also determines legality
of each shorter suffix word, since such a word is legal exactly when it
extends to an element of $F(p)$. Conversely, different completion sets
are distinguished by a complete suffix word in one set and not the other.
At its first rejected append, the full finite response differs. Thus
syndrome equality is exactly forward behavior equality, not merely a
sufficient summary. After a legal append the syndrome at the next cut is
the old syndrome plus that symbol times the relevant column of $H$; legality
is determined by membership of its negative in the remaining column image.
This verifies forward update descent on the actual syndrome images.

The intermediate state quotient just obtained is the standard trellis
separator: the trimmed prefix space is $U_k$ and its nondynamical subspace
is $\ker H_P$, so the effective state space is
$U_k/\ker H_P\cong\operatorname{im}H_P\cap\operatorname{im}H_F$.
This intermediate step is literature-attested by G. David Forney Jr.,
[*Codes on Graphs: Fundamentals*, arXiv:1306.6264v2](https://arxiv.org/html/1306.6264v2),
§5.5, the state-space theorem for leaf fragments, and §6.3, minimal
cycle-free realizations. Here the past fragment's trimmed projection is
$U_k$, its cross-section is $\ker H_P$, and the future fragment supplies
the matching syndrome. Those results concern the effective forward
separator, not the enlarged delete contract or physically acquired access.
They are used only as an attributed intermediate ingredient.

Since $\operatorname{im}H_P+\operatorname{im}H_F=\operatorname{im}H$,
the dimension of their intersection is $r_P+r_F-r$. Every syndrome in
this intersection has exactly $q^{k-r_P}$ prefix preimages. Therefore

$$
\dim U_k=(k-r_P)+(r_P+r_F-r)=k+r_F-r,
\tag{7.6}
$$

and (7.3) and the asserted fiber count follow by finite-field cardinality.

For the enlarged contract take distinct $p,p'\in U_k$. Delete the symbols
of $p$ in reverse order. All $k$ deletions are legal from $p$, because each
successor is one of its extendable prefixes. The same word cannot be legal
from $p'$ unless its last symbol, then its next-to-last symbol, and so on
all equal those of $p$. Thus the first disagreement yields one legal and
one illegal request. Equality of prefixes suffices to preserve every
operation and response, so the enlarged greatest stable relation on each
cut is exactly equality. Its cardinality is $|U_k|$, giving (7.4).

Finally, if $k-r_P>0$, a syndrome fiber contains distinct prefixes. Along
the distinguishing deletion word, if every delete domain were forward
saturated and every delete preserved forward equivalence, the pair would
remain related and have equal legality at every step, contradicting the
first disagreement. More directly, take the last position at which a pair
of equal-syndrome prefixes differ. Deleting their common trailing symbols
subtracts the same columns from both syndromes, so the resulting actual
prefixes are still forward equivalent. Their different final symbols make
a delete domain unsaturated at that cut. Hence the permission enlargement
requires a genuine boundary refinement. $\square$

**Proposition 7.3 (binary parity witness).** For $H=(1,1,1)$ over
$\mathbb F_2$ at $k=2$, the forward boundary has two states and the append/delete
boundary has four. The pair $00,11$ has one forward state but unequal
$\operatorname{delete}_1$ legality.

**Proof.** Here $r_P=r_F=r=1$ and every length-two word is extendable by its
parity bit. The syndrome classes are $\{00,11\}$ and $\{01,10\}$.
Deleting one is legal at $11$, with successor $1$, but is illegal at $00$.
Theorem 7.2 then gives $2^1=2$ and $2^2=4$, with factor $2$. The forward
minimal state has deliberately not retained a full original-prefix archive;
an observer already possessing that archive has a different contract.
$\square$

**Convention 7.4 (counting boundary).** Equations (7.3)--(7.4) count exact
states at a fixed, known cut. They are not installation complexity, an
algorithmic storage bound, a cumulative multi-cut state count or a physical
cost. Delete probes are executable recut permissions in the enlarged
contract. Mathematical reversibility of the prefix maps alone does not
supply those permissions. The same maps considered only as coordinate
changes must satisfy (1.2), which fails for the coarse forward boundary
when a delete domain is unsaturated.

## 8. Mathematical sources and applicability

**Mathematical citation 8.1 (dependencies and distinct boundaries).** The
following sources support the indicated intermediate steps and comparisons.

| Source | Precise use |
| --- | --- |
| [Typed Residual Resource Boundary](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_RESOURCE_BOUNDARY.md), §§1--6 | One actual source, complete typed responses and resource-relative memory. The action/transport interaction here retains that contract. |
| [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), Theorems 1.4 and 3.2 | Strict path relations require equal domains, full labels and successors; descent uses saturated actual fibers. The residual-lift interaction in Theorem 3.2 additionally tests how actions carry those relations forward. |
| [Transport--Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §1.7 | Total-domain tree normalization and basic-loop comparisons. Partial charts require actual coverage rather than only connected chart names. |
| [MaximalForwardInvariantSubkernel](../../../D5/S1/FixedPoints/MaximalForwardInvariantSubkernel.lean), `maximal_forward_invariant_subkernel` | Reused greatest invariant subkernel for one total map; not a claim that the present partial labeled atlas was compiled. |
| [StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean), `contextual_equivalence_is_greatest`, `signature_extension_refines` | Reused strong partial congruence and refinement under enlarged permissions. |
| [TypedFiniteViewKernel](../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean), `typed_finite_view_kernel` | Reused typed finite-path refinement and complete behavior kernel. |
| [DynamicsDescent](../../../D5/S0/Rewriting/Quotients/DynamicsDescent.lean), `dynamics_descends_iff` | Reused total fiber-preserving dynamics factorization; strict partial domains are separately specified here. |
| [InverseLimitCompletion](../../../D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean), `stateThread_bijective_iff_complete_and_separates` | Thread completeness and state separation are distinct realization conditions. |
| [LocalDescentGlobalCompatibility](../../../D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.lean), `local_descent_requires_global_gluing_checks` | Distinguishes local descent, inverse-limit realization and cocycle compatibility. None supplies missing actual fiber coverage. |
| [ZeroLoopPotentialEquivalence](../../../D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.lean), `closed_path_zero_iff_exists_potential` | Complete closed-path tests in a connected groupoid for additive potentials; an arbitrary selected partial loop list has weaker hypotheses. |
| Forney, [*Codes on Graphs: Fundamentals*](https://arxiv.org/html/1306.6264v2), §§5.5 and 6.3 | `literature-attested`: effective trellis separator as trimmed projection modulo cross-section, used inside Theorem 7.2. |

**Convention 8.2 (literature and proof boundary).** The synthesis connecting
complete residual route lifts, partial-atlas domains, normalizer-compatible
stable cores and permission-sensitive prefix memory is `repo-derived`,
with its ordinary proofs above. The fixed-point, kernel-factorization,
strict path-descent, inverse-limit and trellis-separator ingredients retain
the cited prior ownership. No literature priority is asserted for these
mechanisms or for the synthesis. None of the ordinary proofs here is a new
Lean verification. Gauge quotients preserve only the stated invariant task;
virtual threads, unperformed experiments and unacquired records do not
become actual by being represented mathematically.

## 追加锚（本行以下为增补区）
