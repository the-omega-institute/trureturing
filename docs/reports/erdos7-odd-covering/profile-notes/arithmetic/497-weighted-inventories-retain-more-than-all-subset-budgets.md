# Weighted inventories retain more than all subset budgets

Preserving every subset capacity still need not preserve all consequences
of a single original-label selector. In the three-fibre model from
[report494](494-three-fibre-inventories-exclude-a-pair-admissible-triple.md),
every nonnegative weight vector w supplies the necessary capacity

    N(w)=sum_d max(sum_i w_i 1_Ai(d),sum_i w_i 1_Bi(d)).     (W1)

The actual normalized axis deletions t,u and mixed-cylinder sum c satisfy

    w dot t<=N(w), w dot u<=N(w), w dot c<=N(w).             (W2)

The subset budgets are only the weights w in{0,1}^n. A concrete triple
satisfies all those budgets at an old minimizing axis point, but violates
W2 for w=(1,1,2). Adding just this one direction raises its certified
survivor-sum numerator from2 to6. This is an ordinary proof with an exact
rational certificate, not a new Lean result.

## The weighted bound uses the same numerical label everywhere

Fix one finite original family as in report494, with distinct odd numerical
labels m=d*p^j*q^k, j+k>0. The old primes are disjoint from p,q. For each
complete label, its old residue is selected from the same two references
A,B. The selector may differ between numerical labels or exponent pairs;
it cannot be chosen separately for each tested old point.

For old points x_1,...,x_n, let A_i,B_i be their finite labelled divisor
inventories, including the unit label. At fixed d,j,k, its one selector
therefore contributes at most

    max(sum_i w_i 1_Ai(d),sum_i w_i 1_Bi(d))

to the weighted number of activated fibres. Sum over d. A missing original
label contributes0 and does not invalidate this upper bound. With a=p-1
and b=q-1, the complete geometric sums satisfy

    a sum_(j>=1) p^(-j)=1,
    b sum_(k>=1) q^(-k)=1,
    ab sum_(j,k>=1) p^(-j)q^(-k)=1.

Multiply each point's union-deletion bound by w_i>=0, then sum over points
and exponent pairs. This proves W2 for t_i=a*alpha_i and u_i=b*beta_i,
where alpha_i,beta_i are actual axis union losses, and c_i=ab*gamma_i,
where gamma_i sums all actual active mixed-cylinder masses. Finite heights
only reduce the geometric sums. No independence of a conditioned old
source is assumed.

Every weight vector tests the same fixed original family. The maxima
appearing in different W1 inequalities need not be jointly attained.
W2 gives necessary budgets; even imposing all such weights does not assert
that an arbitrary relaxed axis pair has a common arithmetic realization.

## Finite weighted axis polytopes preserve the local proof

Let W be a finite set of nonnegative weight vectors containing every
nonzero0/1 subset vector. Define

    P_h(W)={v:0<=v_i<=h, w dot v<=N(w) for all w in W}.

The same actual t,u belong to P_a(W),P_b(W). Retain just the unweighted
total mixed budget N(1,...,1) for now. The original union-bound argument
then gives

    sum_i s_i >= K_W/(ab),
    K_W=max(0,min_(t in P_a(W),u in P_b(W))
                  [sum_i(a-t_i)(b-u_i)-N(1,...,1)]).        (W3)

Here s_i is the fraction of full p/q Haar in the fixed old fibre that
avoids the original later classes. It is full-family survival only when
x_i also avoids the original old-only classes, as in the actual-source
application of report494.

Additional valid axis inequalities shrink the domains, so K_W cannot
decrease. The objective remains bilinear: a minimum is attained at an
axis-vertex pair, by minimizing successively over the two compact
polytopes. Thus exact finite vertex enumeration remains valid. This does
not apply an unsupported vertex rule to an objective modified by a
pointwise maximum or an optimized mixed budget.

The other weighted mixed inequalities in W2 remain valid but are not used
to obtain W3. Exploiting them would require a separate optimization proof.

## One weight cuts an old minimizer and triples the bound

Use p=23,q=29 and the three profiles

    v1=(2, 2,-2,2,2,1,1),
    v2=(10,-2,0,2,1,1,1),
    v3=(-3,0,0,2,2,1,2).

They are indices110,8038,14062 of report495's declared profile order.
The first three coordinates use the split convention and the last four
are common factors. Literal enumeration gives50 labelled old cofactors
and the seven capacities

    (N1,N2,N12,N3,N13,N23,N123)=(20,22,40,24,40,42,58).

The old subset-only polytopes have16 and15 vertices. Their240 vertex-pair
values have minimum2, achieved at

    t=(20,20,18), u=(16,18,24).

Both vectors obey every subset budget and the appropriate axis bounds.
Their residual numerator is

    (22-20)(28-16)+(22-20)(28-18)+(22-18)(28-24)-58=2.

For w=(1,1,2), literal evaluation of W1 gives N(w)=80. But the old u has

    u1+u2+2u3=16+18+48=82>80.                              (W4)

The missing two units have an explicit source. Adding the old subset
capacities gives N(1,1,1)+N(0,0,1)=58+24=82. Exactly two inventory labels,
d=3 and d=33, have memberships A=(1,1,0),B=(0,0,1). For each such label,
the first separate maximum prefers A and contributes2, while the second
prefers B and contributes1. A single selector for that full original label
cannot do both. Their combined weight(1,1,2) contributes at most2, losing
one unit at each label. All other labels have zero loss, giving80 exactly.

Consequently all subset inequalities together do not imply this weighted
necessary condition. This is a counterexample to the sufficiency of the
subset-budget description, not a claim that u was ever realizable by
original residues.

Add the single row

    v1+v2+2v3<=80

to each axis polytope. The new P22 and P28 have16 and18 vertices. Each is
described by11 rows: three nonnegativity rows, seven subset rows with axis
bounds in the singletons, and this weighted row. Among all triples of
rows,114 have independent normals. Exact rational solution of every such
system, followed by all-row feasibility checks, produces the full vertex
sets. A small strictly positive vector is interior, so any vertex has
three independent active normals. All288 vertex-pair values are at least6.
Equality occurs at

    t=(16,20,22), u=(20,20,0),
    ((22-t_i)(28-u_i))_i=(48,16,0).

After subtracting58, W3 proves

    s1+s2+s3>=6/616=3/308.                                 (W5)

The previous bound was2/616=1/308. The value6 is sharp for this stated
relaxation; neither minimizing allocation is asserted arithmetically
realizable. The code also preserves the literal membership-pattern counts,
so each W1 contribution can be reconstructed from original cofactor labels.

## What improves, and the remaining global task

For this isolated triple, W5 rules out all three fibres being strictly
below any theta<=1/308; the old bound allowed only theta<=1/924. When
combining with the old weak pair edges, keep the common theta=1/3696.
At that common threshold this triple was already an edge in report495's
family. The stronger numerator therefore supplies no additional hyperedge
or global mass discount by itself.

The reusable conclusion is that weighted joint activation retains selector
information absent even from all subset budgets. Further work can search
for new edges, larger jointly constrained point sets, or weighted global
estimates, while keeping the same source and original full labels. This
result does not reduce report496's certified global bound or settle any
new original covering case.

Reproduce with:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_weighted_inventory_cut.py

The standard-library consumer reconstructs literal inventories, verifies
both selector alternatives label by label, enumerates the old and new
complete rational vertex sets, and checks both sharp minimizers and W4.
Its exact result is compared with the adjacent JSON. It reads no solver,
producer profile array or search history. The ordinary geometric-sum
argument above supplies the uniform statement for finite original families;
finite calculations do not claim Lean certification or unrestricted #7.
