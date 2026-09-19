[Index](../../marked_head_profile.md) · [Retained pair](225-two-original-tests-share-the-complete-retained-bridge.md) · [Survival tests](226-the-joint135125-records-strengthen-two-complete-survival-bounds.md) · [Joint row fields](229-the-retained-pair-shares-one-off-face-deletion-budget.md)

# The complete retained duals share one raw-source support

Every constraint in the retained135/125 system can be accounted for
on208's two source domains. The remaining raw capacities, group budgets,
profile rows and raw mass equality join229's actual-measure residual
formula. They use the same25-node raw source support. The deletion
prices continue to use one W and one seven-coordinate residual.

This is a complete **constraint-row** transport. The infinite assigned
tails and the old two/four/six candidates used by the complete scans
must also be transported before obtaining a complete off-face head
bound. No off-face52-cost comparison or new global K follows from
the row bound alone. These are ordinary mathematical and exact-rational
results, with no Lean verification or unrestricted Erdos7 resolution.

| Source domain | Maximum over6292 heavy duals | Maximum over2792 survival duals |
| --- | ---: | ---: |
|sigma<=1/20,rho<=1/1000|1.230555110201373...|0.0400675479710098...|
|sigma<=1/12,rho<=1/3000|0.7678101090704693...|0.0313250117314296...|

These are complete constraint-residual charges, not changes in K.
The exact four maxima are respectively
9014603737495586272939/7325640000000000000000,
20965745151310590863/523260000000000000000,
20594712571400550593513/26822664000000000000000 and
140036710744698981019/4470444000000000000000.

## 1. A specialization supported by all9084 original duals

Use the full6292 heavy duals of225 and2792 survival duals of226.
Let p>=0 be their inequality prices and z their signed equality
prices, with the original row numbering. The following properties
are checked separately for every dual:

    p532=p533=p534=p535=0,
    z4=0, z5>=0.                                      (CR1)

The first four rows are the selected25/27/75/81 survivor caps.
Equality4 fixes survivor mass on the face; equality5 fixes raw
mass. Consequently the old survivor-cap and survivor-mass residuals
have exactly zero price in these certificates. There is no need to
bound them by a positive error. The raw mass price is included in
the same support as the raw capacity rows.

Among the heavy duals,6187 raw mass prices are positive and105 are
zero. Among the survival duals,2767 are positive and25 are zero.
The evaluator requires(CR1); it does not apply this specialization
to arbitrary duals with a negative raw mass price or nonzero
survivor mass price.

## 2. All four original raw-profile families

Keep the canonical first-beta cell2 and slots(P,A,B,Q,H). The
actual source has the same exact exclusions as195/208: all P
nodes, root1 A nodes and node(2,B) have zero raw mass.

Let eta*=(1/18,1/9,1/9,1/9,1/9), let pre* be the face five-slot
availability table, and let descendant* equal eta* on nonexcluded
nodes and zero on excluded nodes. For sigma<=d and rho<=R,208
supplies the source envelopes

    prebar_cs=pre*_cs+v_ROOT(c)*I_(s=Q),
    descendantbar_cs=descendant*_cs
                     +(d/18)*I_(c=0,descendant*_cs>0). (CR2)

Here ROOT=(0,0,1,1,1), and v0,v1 are the same guarded values used
by229. Each original residue chooses one point of its own profile
simplex. Absent or source-null events have zero marked masses and
can use a dummy profile. Independent profiles give a containing
relaxation, without identifying the original residues or asserting
realizability of all relaxed points.

The four raw-profile coefficient families are

    25: I_(s=a)*descendantbar_cs/25,
    27: I_(c=a)*prebar_cs/27,
    75: I_(ROOT(c)=r,s=a)*descendantbar_cs/25,
    81: I_(c=a)*prebar_cs/81.                         (CR3)

Let beta^j_cs be the corresponding nonnegative face-row prices.
Pricing each normalized simplex gives the additional source bounds

    P25=(d/450)*max_(s!=P) beta25_(0,s),
    P75=(d/450)*max_(s!=P) beta75_(0,s),
    P27=max_c[v_ROOT(c)*beta27_(c,Q)]/27,
    P81=max_c[v_ROOT(c)*beta81_(c,Q)]/81.             (CR4)

For instance, the25 family contributes at most
(d/450)*sum_s lambda25_s*beta25_(0,s); its one simplex normalization
bounds this by the maximum in(CR4). The75 family uses its separate
root/slot simplex, and only root0/cell0 changes. The27 and81 families
each use their own cell simplex. Their four maxima must remain
separate. There are18 moving old profile rows and82 exact ones.

The original raw CRT caps remain exact because the actual source
is dominated by product Haar measure. The27/81 nested and disjoint
alternatives remain distinct. No new independence assumption is used.

## 3. One support for raw caps, group budgets and mass

Write a_i=p_i for rows0..24, b_g=p_(25+g) for rows25..27, and
tau=z5>=0. Let r*_i and B*_g be their original face right sides.
The three source groups are cell0, cell1 and root1, with face
budgets(1/36,1/12,5/36). Let u_i be229's raw link-density field
after combining all old and retained-state prices.

For q=(q5,q15), use the same actual density increment

    Dw_i(q)=(d/5)*I_(cell(i)!=0)+q5*I_H(i)
                              +q15*I_(root1,H)(i).

Let Pbar be208's fixed25-node polytope, with nonnegative masses X,
the guarded enlarged node caps, and its three enlarged group
budgets. It contains the actual coarse raw source. Define

    J(q)=max_(X in Pbar) sum_i
          [u_i*Dw_i(q)+a_i+b_group(i)+tau]*X_i
          -sum_i a_i*r*_i-sum_g b_g*B*_g-tau/4.     (CR5)

Indeed, the four raw contributions before optimization are

    sum_i u_i*Dw_i(q)*X_i,
    sum_i a_i*(X_i-r*_i),
    sum_g b_g*(sum_(i in g)X_i-B*_g),
    tau*(sum_i X_i-1/4).

Their sum is exactly the objective in(CR5). Thus the same actual
raw mass is used throughout. Paying separate capacity increments
or tau*d/2 after(CR5) would count those contributions again.

All coefficients inside the maximum are nonnegative, so the
existing disjoint-group capacity solver supplies exact feasible
primal and dual witnesses. Their values agree over the rationals.
After the face constants are subtracted, J(q) may be negative.
The evaluator preserves this sign; neither a negative J nor a
negative complete residual upper is grounds for rejecting a valid
support.

The source envelopes used here have

    cap increments: d/90 on nonexcluded cell0 nodes,
                    plus v0/18 at(0,Q), v0/9 at(1,Q),
                    and v1/9 at the three root1 Q nodes;
    group increments: ((3+d)*U/72,d/36,U/12),
    U=d/(1-d).

These are the same fixed caps and budgets already checked in229,
not a new parameter-dependent optimization domain.

## 4. Complete constraint residual and the vertex rule

Let C229 be229's source payment and ell its seven primitive
prices, retaining the common W-field price. Set

    C=C229+P25+P75+P27+P81,
    L=max_j ell_j.

For a fixed face dual and the actual nonnegative off-face vector xi,
the complete residual in229(RP11) is at most

    C+J(q)+ell.Y,
    Y>=0, sum Y<=rho_actual-G*(q5+q15),
    0<=rho_actual<=R.                              (CR6)

Because L>=0 and z4=0, increasing rho_actual to R gives a valid
upper. Hence a bound for every actual source in the domain is

    E=max_(q in {(0,0),(R/G,0),(0,R/G)})
          [C+J(q)+(R-G*(q5+q15))*L].              (CR7)

J is a support over a fixed feasible set with an affine
q-objective, so it is convex in q. The rest is affine. Every point
of the q triangle is a convex combination of its three vertices,
proving(CR7). This is not a claim that an optimized LP with moving
constraints is convex. For arbitrary nonzero signed survivor-mass
prices, the rho_actual term would have to be retained and the
fourth vertex(0,0,0) checked; those prices are excluded by(CR1).

If Uface is the checked face dual value for objective c, weak
duality in residual form now gives

    c.xi<=Uface+E.                                (CR8)

All constraints are accounted for in(CR8). The separately assigned
complete tails are outside c.xi and must be added once. A later
consumer should add their source and primitive prices before
performing the common maximum in(CR7), to retain the shared budget.

## 5. Complete inventory and certificate interface

Both original geometric branches have the same exhaustive partition:

| Constraint kind | Transported | Exact | Zero price | Total |
| --- | ---: | ---: | ---: | ---: |
| Inequalities |2516|4643|4|7163|
| Equalities |24|31|1|56|

The constructor checks every original raw row, both mass equations,
all inherited deletion rows, the new marked-state rows, the exact
profile normalizations, CRT rows and unit caps. Index sets are
disjoint and cover the full ranges. The zero-price column means
the particular dual is checked to ignore that row; it does not
mean that its off-face right side is unchanged.

The helper consumes all6292 heavy records already priced by229.
It applies the same229 field construction to every2792 survival
record, then evaluates(CR4)--(CR7) for both banks. The result stores
the combined source payment, all25 raw base and density prices,
the signed face subtraction, all seven primitive prices, the W
field hash, three vertex values and their maximum. Its lossless
table representation decodes to the complete record before use.

All18,168 complete records were independently reconstructed, using
54,504 rational raw-support optimizations by the dual-breakpoint
formula instead of the helper's greedy allocation. The stored
maximizers'36 group witnesses were also checked directly for
primal/dual feasibility and equality. The logical certificate is
16,192,787 bytes in57 physical JSON parts; all complete records
and their field hashes are retained.

`frontier/transport/complete_retained_row_transport.py --check` reconstructs
these prices from the pinned original inputs. It does not repeat
the original62,500,000-choice head scans and does not substitute
row transportation for their still-required pruning transportation.
