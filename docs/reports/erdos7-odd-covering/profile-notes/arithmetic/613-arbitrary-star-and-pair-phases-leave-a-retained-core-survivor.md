# Arbitrary star and pair phases leave a common retained-core survivor

Keep the actual pure3/pure5 source and central15 mask of
[Report604](604-fixed-pair-activation-admits-ten-central-square-stars.md).
Allow every central and outside component of its 35 retained star originals
and 120 retained pair originals to vary arbitrarily, once for the whole
family. The original numerical moduli remain pairwise distinct. The actual
product pure source then assigns the simultaneous retained survivor mass at
least

    3344320856939 / 61177884768000 > 1/19.

Using Report604's common density bound, its seven-prime Haar mass is at least

    3344320856939 / 522353396364800 > 1/160.

This concerns the 156 retained mixed labels only. It does not pay the
remaining-original or complete-height query arrays L/W. In particular it
neither proves a positive full continuation gate for arbitrary stars nor
proves unrestricted Erdős #7. Its significance for
[Report611](611-free-star-phases-require-a-layout-dependent-thinning.md) is
that failure of a common thinning does not arise from these retained
originals actually covering the source, even when the stars are freed.

## Source and full phase scope

Let V={7,11,13,17,19}. The pure3/pure5 originals are a subset of

    2 mod3, 7 mod9, 4 mod27, 13 mod81, 40 mod243, 121 mod729;
    4 mod5, 2 mod25.

There are no other pure3/pure5 originals in this statement. Missing listed
classes may be imposed as auxiliary source deletions. All pure-q originals
at q in V, including their finite heights and residues, remain arbitrary.
Use exactly Report604 FA4--FA6: normalized Haar on the 365 surviving ternary
words, its actual root-balanced quinary source, and the actual root-balanced
outside pure survivors. These form one product probability law rho. Write

    r_q=1/(q-1), a_q=1/[q(q-2)].

Every outside mod-q cylinder has rho_q mass at most r_q, and every mod-q^2
cylinder has mass at most a_q. The same actual rho obeys

    rho <= D Haar, D=2*(5/3)*product_q q/(q-2)=3458/405.

Changing the outside pure phases changes rho_q but preserves these bounds.
No choice of a separate source for a star, pair, central cell or query is
made.

The15 class, if present, is0 mod15. Delete its central root mask M=(0,0)
even if absent. The 35 star labels are, for each q in V,

    3q, 5q, 15q, 9q, 25q, 3q^2, 5q^2.

For each q<r in V the twelve pair labels are

    3^a 5^b q^e r^f,
    (a,b) in {0,1}^2, (e,f) in {(1,1),(2,1),(1,2)}.

All residues of these 155 star/pair labels are arbitrary and globally
fixed. Coincidences between their outside components are allowed but not
required. Missing and source-null slots only reduce the debit. Thus15 plus
these slots is exactly156 distinct odd mixed labels. No other mixed label
is included in the retained-core conclusion.

## Charge every event outside the mask already deleted

The central mask has probability

    rho_central(M)=243/1460.

For any central residue, the largest mass of its indicated support outside
M is as follows. The entries are computed from the same central source,
not independently chosen source distributions.

| Central support | Maximum mass outside M |
| --- | ---: |
| one mod3 row | 729/1460 |
| one mod5 column | 1/4 |
| one (mod3,mod5) point | 243/1460 |
| one mod9 leaf | 81/365 |
| one mod25 leaf | 1/16 |

For example the mod3 row0 retains (243/365)*(3/4)=729/1460
outside M; row1 has mass122/365 and row2 has mass0. The largest
mod9 leaf can be the residue1 leaf, which does not meet M. The largest
mod25 leaves lie in root2 and likewise do not meet M. Exhausting all3
rows,5 columns,15 points,9 ternary leaves and25 quinary leaves verifies the
table, including zero-mass central roles.

Denote the five table entries by R,C,P,A,B. For one q, the five
first-power stars have total mass outside M at most

    r_q*(R+C+P+A+B),

and its two square stars contribute at most

    a_q*(R+C).

Product factorization between the central and outside coordinates justifies
each individual estimate. One union bound then gives

    R+C+P+A+B=7009/5840, R+C=547/730,
    sum_q r_q=337/720, sum_q a_q=4099/77805,
    D_star <=1456983547/2423366400.

For edge{q,r}, let

    kappa_qr=r_q*r_r+a_q*r_r+r_q*a_r.

The four central variants for each exponent type are unconditional, row,
column and point. Outside M their total central coefficient is at most

    (1-rho(M))+R+C+P=1277/730.

Every particular exponent type and central variant has its own actual
residue; no alignment between them is assumed. Summing their probability
caps is valid even when different maxima cannot occur simultaneously. Thus

    sum_{q<r} kappa_qr=607991257/5986094400,
    D_pair <=776404835189/4369848912000.

Subtracting these upper debits from the unmasked source mass gives

    rho(avoid all156 retained originals)
      >=1-243/1460-D_star-D_pair
      =3344320856939/61177884768000 >1/19.

If the original15 slot is absent, the artificially deleted M only weakens
this lower bound. The estimate also remains valid when some star/pair slots
are absent. The density comparison rho<=D Haar gives the stated Haar bound.
Neither a matching-polynomial condition nor a common theta is used here.

## The continuation gap and an exact boundary that can carry it

Positive retained mass does not imply a positive Report604 L/W gate. A
complete proof still needs one actual surviving submeasure whose mass and
all later query bounds are simultaneously paid.

For a globally fixed layout and source, all retained outside constraints
only see the five variables modulo q^2. At central cell c, write
S_q(c) for its actual active star union and E_qr(c) for its actual pair
union. With p_q the actual mod-q^2 marginal, the exact survivor grid is

    Z_empty(c)=sum_x product_q p_q(x_q)
       * product_q 1[x_q notin S_q(c)]
       * product_{q<r}1[(x_q,x_r) notin E_qr(c)].

For query support T, define Z_T(c) by dropping every retained factor
involving a coordinate in T. The remaining indicator depends only on the
coordinates outside T. Consequently, for any query cylinder A_T,

    rho(A_T and retained survival at c)
       <=rho_T(A_T)*Z_T(c).

This is product-source factorization after removing restrictions. It keeps
one globally fixed layout, the same p_q in every grid, and one thinning
matrix theta for all mass and query evaluations. Subject to Report604's
existing central screens and higher-cylinder caps, these exact grids can
replace its conservative H_T grids in the continuation gate.

This identity supplies a precise target for boundary compression: aggregate
outside residues only when they have the same membership in all actual
star and pair cylinders incident to that coordinate, retaining the sum of
their actual p_q masses. Equality and parent relations must be simultaneous
across incident edges. The count of resulting classes and the largest
intermediate elimination table must be measured for the chosen layout;
five coordinates by itself is not a complexity guarantee.

A certificate for the original frontier must establish

    for every allowed globally fixed layout/source,
    there is one theta with positive full L/W gate.

The retained-core bound proved above does not settle that quantified gate.
In particular, positive witnesses from different layouts or pure-source
marginals cannot be combined as though they came from one source.

## Exact arithmetic verification

The standard-library [producer](../../frontier/cover-geometry/arbitrary_star_pair_core_bound.py)
and [exact data](../../frontier/cover-geometry/arbitrary_star_pair_core_bound.json)
reconstructs the365 ternary survivors, the actual balanced quinary masses,
all57 central roles, the156 distinct labels, and the rational debit and
density calculations. It passes10 predicates comprising17,996 finite
evaluations under Python isolation with optimization enabled. Its finite
arithmetic verifies the displayed constants; the uniform outside cylinder
caps are the explicit inherited Report604 hypotheses. This is not new Lean
verification and does not certify the missing continuation gate.

Replay the retained certificate with:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/arbitrary_star_pair_core_bound.py
