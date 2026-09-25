# Every central star and pair phase admits continuation in the root-one layout

Under the fixed outside-root layout and pure-source conditions below,
ALL central phases of the35 star originals and120 pair originals admit
one common positive continuation gate. The full ten-prime survivor has
Haar mass greater than1/1900. The entire allowed outside network of
[Report616](616-three-parent-entries-with-two-outside-parents-preserve-a-common-survivor.md)
can be attached on the same law, leaving extendible head Haar mass
greater than1/2100 and full density greater than1/(2100 Q_off).

This removes the finitely prescribed central activation patterns of
[Report604](604-fixed-pair-activation-admits-ten-central-square-stars.md)
within a different, explicitly restricted outside phase class. It pays
the complete remaining-original and query costs, extending beyond the
retained-core-only conclusion of
[Report613](613-arbitrary-star-and-pair-phases-leave-a-retained-core-survivor.md).
It does not admit arbitrary outside roots or unrestricted head labels.
These are ordinary proofs and exact arithmetic certificates, not new
Lean verification or a resolution of unrestricted Erdős #7.

Fix the actual FA1 central pure3/pure5 source, central15 phase0, and
outside primes Q=(7,11,13,17,19). The central pure inventory is the
specified FA1 inventory; arbitrary additional central pure originals are
not silently admitted. At q, the depth-one pure class is absent or0,
higher pure-q phases are arbitrary and finite, and the outside components
of3q,5q,15q,9q,25q are1,2,3,4,5 modulo q. The square-star outside
components are1 and2 modulo q². Each retained pair original projects
to root1 at each of its two outside coordinates. All central star and
pair phases are arbitrary, but fixed once globally. Missing retained
slots may be imposed as auxiliary deletions. The remaining-original
inventory and complete query coefficients are precisely the full604
L/W inventory, with the separately retained9q and25q slots removed.

The assertion concerns this actual phase class and its admitted remaining
originals. It does not remove the outside-component restrictions or the
remaining restrictions on core mixed-square labels.

Explicitly, all original numerical moduli are distinct and every residue
is fixed once for the whole actual family. The retained pair inventory is

    3^a 5^b q^e r^f, q<r in Q,
    (a,b) in{0,1}^2, (e,f) in{(1,1),(2,1),(1,2)}.

At the respective outside heights their components are1; their central
components are completely arbitrary. Every other mixed original on the
seven-coordinate core must satisfy at least one of

    maximum exponent>=3; v3<=1 and v5<=1;
    support cardinality>=5.

The special35 star and120 pair originals are retained once and removed
from that remaining inventory's debit. All originals touching23,29 or31
are unrestricted. Pure3/pure5 originals are a subset of

    2mod3,7mod9,4mod27,13mod81,40mod243,121mod729;
    4mod5,2mod25,

with no other pure3/pure5 originals. All absent retained slots may be
imposed as auxiliary deletions; their presence is not a hypothesis.

## 1. One supported source and all its queries

The actual root-balanced pure-q survivor has mass r_q=1/(q−1) on each
nonzero first root and every square-cylinder mass at most
alpha_q=1/[q(q−2)]. Its complete-height cylinder caps hold simultaneously
on this source. At one central mod9/mod25 leaf, write the seven activation
indicators as R1,C1,P,L9,L25,R2,C2.

Thin the actual star survivor root by root to masses

    root1: B_q=(1−R1)(r_q−alpha_q R2),
    root2: (1−C1)(r_q−alpha_q C2),
    root3,4,5: r_q(1−P),r_q(1−L9),r_q(1−L25),
    each other nonzero root: r_q.

The cap on the actual square cylinder guarantees enough surviving mass.
A constant thinning on each affected actual surviving root achieves the
stated mass without inserting forbidden configurations. Its nonroot1
mass is

    A_q=1−r_q−r_q(C1+P+L9+L25)−alpha_q C2(1−C1).

Use the product of these five conditional outside submeasures and keep
at most one root1 coordinate. This avoids every retained pair original:
the unconditional qr deletion already excludes two root1 coordinates,
and the remaining pair events are subsets of that deletion.

For T subset Q define, with S=Q\T,

    H_T=product_(q in S)A_q
          +sum_(q in S)B_q product_(r in S\{q})A_r.       (A)

Multiply by the fixed central15 mask. H_empty is the EXACT mass grid of
the chosen actual submeasure. For any actual query on T, drop the star
thinning on T and the pair restrictions touching T. Applying the original
pure-q caps on T leaves exactly H_T on the other coordinates. This is
pointwise domination of the SAME supported source, not a new source
chosen for that query. Dependence on the central coordinates is only
through their mod9/mod25 leaf, so the inherited central deep-prefix
screens continue to apply. Consequently all finite-height queries and
the analytically summed L/W coefficients use these same H_T.

With nonnegative selector menus S_j and coefficients c_j, write the
complete gate functional as

    K(H)=g sum_b mu_b H_empty(b)
              −sum_j c_j max_(s in S_j)sum_b s_b H_(T_j)(b),
    g=1−c_head,
    c_j=(1−c_head)L_j+c_head W_j.                       (B)

The inherited full remaining-original and moment argument yields an
actual complete-core survivor eta with

    eta(1)−c_head Gamma(eta) >= K(H).

Pure support and every remaining-original phase are fixed before the
queries; the complete query grid is only an upper bound on their masses.

## 2. The5320 aligned comparison templates suffice for fixed theta=1

Auxiliary deletion allows R2 to be the other live ternary row from R1.
If the original square role was equal to R1 it was already killed by
the whole-root deletion; if it was source-null it had zero source mass.
The other case already uses the other row. The same argument pads null
roles, takes C2 different from C1, and replaces the masked point(0,0)
by one of the seven live points. Thus

    B_q=(r_q−alpha_q)(1−I_(row R)),
    A_real=1−r_q−r_q(I_C1+I_P+I_L+I_M)−alpha_q I_C2.

Define the coherent aligned response vector

    Ahat(C)=1−r_q−(r_q+alpha_q)I_C−r_q(I_P+I_L+I_M).

As ENTIRE leaf vectors,

    A_real=[r_q/(r_q+alpha_q)]Ahat(C1)
                  +[alpha_q/(r_q+alpha_q)]Ahat(C2).     (C)

For the fixed original family the two corners need not individually be
supported submeasures avoiding its two different square columns. This
is not needed: its actual source was already constructed in Section1.
Equation(C) is an algebraic convex decomposition of that source's
response. Each H_T is affine in one whole pair(A_q,B_q), and K is
concave in H because the query costs are maxima of linear functionals.
Successively applying that concavity in five blocks shows that a common
lower bound on all products of aligned vectors gives the same bound for
the original actual source. No family-dependent theta is mixed.

Each aligned template is specified by

    R in{0,1}, C in{0,1,2,3}, P in seven live root points,
    L in{0,1,2,3,4}, M in{0,...,19}\{10}.

There are5320 templates per q. They satisfy

    amin_q=1−5r_q−alpha_q <= Ahat_q <= amax_q=1−r_q,
    0 <= B_q <= bmax_q=r_q−alpha_q,

and amin_7=29/210>0. Their uniform template means, at EVERY live cell,
are exactly

    abar_q=1−(4377/2660)r_q−alpha_q/4,
    bbar_q=(r_q−alpha_q)/2.                            (D)

The coefficient4377/2660 is1+1/4+1/7+1/5+1/19.

## 3. A second-derivative integral contains ALL higher interactions

For one fixed five-template product let

    deltaA_q=A_q−abar_q, deltaB_q=B_q−bbar_q,
    A_q(t)=abar_q+t deltaA_q,
    B_q(t)=bbar_q+t deltaB_q, 0<=t<=1.

Let Hbar be(A) at the means and D_q its first block derivative in this
direction. For q<r, put U_qr=deltaA_q deltaA_r and
V_qr=deltaA_q deltaB_r+deltaB_q deltaA_r. If T meets{q,r}, the pair
coefficients are zero. Otherwise, with R=Q\(T union{q,r}), let
h_R=product_(j in R)A_j+sum_(j in R)B_j product_(k in R\{j})A_k, and put

    QAA_(T,qr)=2 integral_0^1(1−t) h_R(A(t),B(t))dt,
    QAB_(T,qr)=2 integral_0^1(1−t) product_(j in R)A_j(t)dt.

The one-variable Taylor identity with integral remainder gives EXACTLY

    H=Hbar+sum_q D_q
             +sum_(q<r)[QAA_qr U_qr+QAB_qr V_qr].      (E)

There is no deltaB_q deltaB_r term, since(A) contains at most one B.
The factor2 accounts for the two orders in the second derivative.
Equation(E) includes every interaction of orders two through five; no
third-, fourth- or fifth-order error remains to be paid separately.

Since A_q(t)>0 and B_q(t)>=0, each coefficient polynomial is monotone
in every remaining A and B. Replace the endpoint A_j by amin_j or
amax_j, and B_j by0 or bmax_j, while retaining the same means at t=0.
Integrating these lower and upper endpoint interpolants gives rational
bounds LAA<=QAA<=UAA and LAB<=QAB<=UAB, uniformly for all remaining
three blocks, all cells and all original families in scope.

For a polynomial product of at most three affine interpolants, these
integrals are exact finite rational sums: if its t^k coefficient is a_k,
then2 integral(1−t) product dt=sum_k2a_k/[(k+1)(k+2)].

## 4. A pair cost is a simultaneous mass lower and query upper

Allocate Hbar/10 and(D_q+D_r)/4 to pair qr. Summing the ten allocations
recovers Hbar and all five first derivatives. In its pair remainder use

    mass lower: LAA U_+ + UAA U_- + LAB V_+ + UAB V_-,
    query upper: UAA U_+ + LAA U_- + UAB V_+ + LAB V_-,

where U_+=max(U,0), U_-=min(U,0), and likewise V. These inequalities
hold cell by cell. They do not assume the coefficient endpoints are
jointly attainable. Add the pair's allocated baseline to both expressions;
call the resulting mass grid l_qr and query grids u_qr.

Its lower cost is

    k_qr=g sum_b mu_b l_qr(b)
                  −sum_j c_j max_(s in S_j)sum_b s_b u_(qr,T_j)(b). (F)

The selector weights and c_j are nonnegative, so(F) is at most K of the
actual pair contribution in(E). The functional K is SUPERADDITIVE on all
real signed grids: its mass term is linear and each maximum of linear
query forms is subadditive. Therefore

    K(H) >= sum_(q<r) k_qr.                            (G)

Signed pair grids need not be probabilities or separate actual sources.
They are bounds on the decomposition of the single actual response.
The coefficient-box operation can lose sharpness, but cannot create a
false positive lower bound when its arithmetic is directed correctly.

## 5. Common source symmetry and shared coarse columns

The source and all sixteen query menus are invariant under S3 on ternary
leaves0,1,2, the four independent live-leaf permutation groups of sizes
5,5,4,5 on the quinary columns, and the whole-column exchange1<->3.
All roles in a tested pair must be transported together. The exact orbit
reduction has372 first-template representatives and317920 ordered-pair
representatives. Their orbit sizes sum to5320 and5320² respectively.
The independent source/menu check verifies all18 generators exactly.

For each ordered pair of outside primes compute a certified lower table
entry kbar_qr(c,d) over ALL template pairs whose central columns are c,d.
Every other role, including whether the two leaf roles coincide, is
minimized over. Whole-column exchange acts simultaneously on c,d and all
other roles; the source orbit calculation and its exchanged entries
cover the full table. It is legitimate for the minimizing leaf roles at
different table edges to be mutually incompatible: each table is only
a lower bound, so that relaxation cannot overstate(G).

For every actual five-template product, its five columns c_q are shared
across all ten edges. Thus

    K(H) >= sum_(q<r) kbar_qr(c_q,c_r)
          >= min_(c in{0,1,2,3}^5)
                          sum_(q<r) kbar_qr(c_q,c_r).             (H)

The final minimum has4^5=1024 assignments. No row or column is chosen
separately for different original queries in the actual construction.
Equations(A)--(H), plus certified directed rational/integer table bounds,
prove one uniform positive gate whenever the computed right side is
positive.

## 6. Exact directed arithmetic and the uniform gate

The retained producer forms every integrated coefficient with rational
arithmetic. It rounds the local mass grids down and query grids up at
scale2^21, and rounds each complete query coefficient both down and up
at scale2^24. All sixteen central selectors have the exact common
denominator58400. Because the allocated grids can be signed, a negative
mass uses the upper gain coefficient and a negative query screen uses
the lower query coefficient. These choices always lower the final gate.

The exact integer kernel evaluates317920 representatives for each of
ten pairs, fills all16 common-column entries using only the simultaneous
source symmetry, and checks all1024 shared five-column assignments.
Every local interval lies in[-2,2]. Thus all signed64-bit selector
intermediates have absolute value at most244947353600. The absolute
128-bit budget bound, including ten edges and the final250 multiplier,
is38414452315389952000000, strictly below2^120.

Its directed result is

    gamma=60482197234393807/2054767329987788800>7/250.

The bound covers every one of the5320^5 aligned five-template choices;
the source construction and convex transfer cover every actual central
star layout in the stated phase class. One fixed theta=1 works throughout.
All second through fifth interactions and the complete L/W arrays are
paid. The arrays are read from the published Report604 coefficient file
with its exact SHA256 pin; no floating optimizer output enters the proof.

The seven-coordinate complete-core law therefore satisfies

    eta(1)−c_head Gamma(eta)>=gamma,
    eta<=rho<=D H_core, D=3458/405.

Applying the inherited23,29,31 head-only normalized kernels yields

    H_head(survivor)>=alpha gamma
        =161668913207534646111/284215417083910946816000
        >1/1900, alpha=2673/138320.

The independent arithmetic check uses positive Bernstein integrals for
all84480 local interval endpoints and generic selector vectors for the
table witnesses. This cross-check is separate from the kernel's full
3179200 pair-orbit evaluations. It does not convert the ordinary proof
or the exact computation into Lean verification.

## 7. The same source can pay the Report616 outside network

The independently checked directed certificate gives

    K(H) >=60482197234393807/2054767329987788800>7/250.

Its actual complete-core eta is still below the same product pure source.
That source has singleton density caps below2 at3, at most25/16<5/3
at5, and q/(q−2) on the five other core primes. Thus the input relations
used in Report616 are unchanged, with its old numerical K replaced by
the new7/250 bound. The head-only normalized23,29,31 kernels use the
same c_head and multiply full density by200/33. All early roots can be
preloaded exactly as in that report; head kernels still ignore them.
The improved singleton2 and pair4 head caps follow on this same joint
law. Every two-/three-parent outside owner, ordinary private domain,
reverse-actual-sampling conditional bound and gluing argument from
Report616 therefore applies without a source restart.

Paying that report's complete uniform raw fees leaves

    raw good mass >7/250−1/780−4/125000−1/65536
                              −2(1/250000+1/1600)
                  =202976237/7987200000.

The full-head projection still uses alpha=2673/138320, giving

    H_head(U_ext)>180851827167/368263168000000>1/2100.

The network scope remains one fixed tuple per owner, either two parents
or three with at least two outside parents, plus its declared ordinary
private interfaces. This corollary is for the stated reference head and
fixed root-phase class. The arbitrary-ten-head transport of Report616
must not be copied without separately checking that its pullbacks
preserve this new phase class.

The certificate remains ordinary mathematics plus exact finite arithmetic,
not new Lean verification and not a solution to unrestricted Erdos7.

## Reproduction

The [rational producer](../../frontier/cover-geometry/root_one_all_stars_certificate.py),
[integer kernel](../../frontier/cover-geometry/root_one_all_stars_certificate.cpp),
and [certificate](../../frontier/cover-geometry/root_one_all_stars_certificate.json)
retain the complete source pins, interval bounds, all ten pair tables and
the common-column minimum. Python uses the standard library; the finite
orbit calculation requires a C++20 compiler. From the repository root:

```sh
python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/root_one_all_stars_certificate.py --out /tmp/root-one-all-stars-replay.json
```

The producer checks37 predicates containing830471 preprocessing evaluations,
then3179200 pair-orbit evaluations and1024 shared-column assignments. An
independent checker recomputed all84480 local interval endpoints using
positive Bernstein coefficients and checked all160 table witnesses with
generic selector vectors, as well as the1024 common-column minimum.

## Arbitrary three-parent types on this same head

[Report619](619-one-global-three-parent-network-under-the-root-one-head.md)
uses this stronger actual head gate to treat every outside owner with
one fixed tuple of at most three smaller parents, including three heads
or two heads and one outside parent. It samples the entire head first
and then all owners by the same normalized construction. Its complete
whole-prime fee leaves extendible head Haar mass greater than1/53000.
The present head and ordinary-interface restrictions remain.

## The root labels can be specified by their relations

The literal outside digits in this report can be replaced by the following
coordinatewise conditions, with the same constants and the same5320-template
certificate. Fix q in{7,11,13,17,19}. Let f_q be its actual forbidden
first pure root, or an auxiliary first-root deletion if that pure slot is
absent. Choose five pairwise distinct roots u_(q,1),...,u_(q,5), all
different from f_q. The outside first-root components of3q,5q,15q,9q,25q
are respectively these five roots. The two square stars3q² and5q² may
have ANY lifts of u_(q,1) and u_(q,2) modulo q². At every retained pair
label incident to q, its q-component must project to u_(q,1); its higher
digits may vary freely between labels. The choices at each prime are
fixed throughout the actual family. Higher pure-q phases and all retained
central star and pair phases remain arbitrary. All the other head and
outside-network hypotheses remain as stated above.

These conditions concern actual equalities, inequalities and prefix
incidence. They do not identify arbitrary high-digit assignments with one
literal assignment by a single permutation. In particular several pair
square cylinders with different lifts cannot all be sent to the same
square cylinder by an injective transport.

To prove the extension directly, take the actual root-balanced pure source
rho_q with first root f_q deleted. Each of the other q−1 roots has mass
r_q=1/(q−1), and each square cylinder has mass at most
alpha_q=1/[q(q−2)]. At a fixed central leaf, thin its actual star survivor
to the following root masses:

    u_(q,1): (1−R1)(r_q−alpha_q R2),
    u_(q,2): (1−C1)(r_q−alpha_q C2),
    u_(q,3),u_(q,4),u_(q,5):
                    r_q(1−P),r_q(1−L9),r_q(1−L25),
    every other live root: r_q.

The square-cylinder cap makes each required thinning possible on this
same actual source, whatever the square lifts or higher pure deletions.
The distinguished mass B_q and its complementary mass A_q are exactly
those in Section1. This construction therefore produces the same entire
central response vectors, rather than merely equal total masses.

The unconditional qr original has endpoints u_(q,1),u_(r,1). Its
rectangle contains every other retained original on that pair, since
all of their endpoint cylinders have these first roots. If the qr slot
is absent, impose this rectangle as an auxiliary deletion. Restricting
the product of the thinned sources to at most one distinguished root
therefore avoids all retained pair originals, irrespective of their
central phases and of all square lifts. Its exact mass and query grids
are the same H_T in(A).

For every query support T, dropping restrictions touching T and restoring
rho_q on its queried coordinates is domination of this one supported
source. The full-height caps are unchanged, so the same complete L/W
arrays, fixed theta=1, convex reduction and integer certificate apply.
The density caps of rho and the resulting head law are also unchanged;
hence both the head conclusion and the stated same-source network
corollary extend under these relational root hypotheses.

Equivalently, one may transport all first roots at q by a single
permutation sending f_q,u_(q,1),...,u_(q,5) to0,1,...,5. Carrying higher
digits within their exchanged subtrees defines a Haar-preserving rooted
tree map that sends every cylinder to a cylinder at the same height.
The same map must act on all actual originals and queries at that prime.
Higher pure phases are permitted to change because their scope was
already arbitrary. This explains the first-root covariance; the direct
construction above, not an impossible simultaneous identification of
distinct higher lifts, justifies the full extension.

The distinguished root must still be the first star's root u_(q,1).
Allowing a different distinguished role, or allowing different incident
pairs to use different roots at q, changes the retained response and is
not covered by this reuse of the certificate. This paragraph adds no new
finite computation or Lean declaration.

## The remaining endpoint-pattern problem

This is a finite structural reduction, not a positive continuation gate.
Keep the preceding relational star hypotheses, but now
allow edge{q,r} to have its own root d_(q,r) at q and d_(r,q) at r. All
twelve retained originals on this edge must project to these same two
roots; their central roles and their higher lifts may be arbitrary. This
still does not admit different first roots among the twelve labels of one
edge. Those would require a larger relation table.

### One actual source and its complete boundary

Use the same rootwise-thinned actual star submeasure nu_q. At each fixed
central leaf its five marked root masses are

    w1=(1−R1)(r−alpha R2), w2=(1−C1)(r−alpha C2),
    w3=r(1−P), w4=r(1−L9), w5=r(1−L25).

Each of the q−6 remaining live roots has mass r. Their total together with
the five marked masses is Z_q. One unconditional qr rectangle removes
the forbidden pair of roots on that edge; all other retained labels there
are contained in it. An absent qr slot can again be imposed auxiliary.
Thus the exact retained response is a five-variable factor network with
one forbidden root pair per edge. It need not have the at-most-one-root
form used by617.

For S=Q minus a query support T, let E(S) be the induced pair edges. For
F subset E(S), call F compatible if, at every vertex incident to F, all
its selected incident edges specify the same endpoint root. In that case
call the common root d_q(F). Inclusion-exclusion gives the exact polynomial

    H_T=sum_(F subset E(S), F compatible) (−1)^|F|
          product_(q incident to F) w_(q,d_q(F))
          product_(q in S not incident to F) Z_q.       (EP1)

Here an unmarked endpoint root has weight r_q. The empty F contribution
is product Z_q. EP1 has at most2^10=1024 terms. It is an identity for the
one product of actual thinned star sources, subsequently restricted by
all edge rectangles, not an independently chosen law for each F or T.
Multiplying by the central15 mask gives the full central grid.

Every queried-coordinate restriction can be dropped on this same source.
Its remaining factor graph is exactly E(S), so the full-height query
caps multiply EP1 in precisely the same domination argument as617. The
existing central screens and complete L/W arrays can therefore consume
these grids. Their positivity remains a separate obligation.

### A finite classification preserves precisely the missing relation

At vertex q the five star roots are distinguished and cannot be permuted
independently of their central activation roles. The other live roots
have equal prescribed mass r_q and enter no star. Among four ordered
incident endpoints, retain each endpoint's marked-star identity, or else
its membership in a common partition of the unmarked occurrences. Name
the unmarked blocks by first occurrence. There can be at most q−6 such
blocks. A single root relabelling acts on the whole endpoint list at q;
independent relabelling per incident edge is not allowed.

For a sufficient theorem one may restrict to live endpoint roots. If a
pair's endpoint is the forbidden pure root, all its actual pair cylinders
already have zero source mass. Replacing its unconditional rectangle by
an auxiliary live-root rectangle only strengthens the required avoidance.
This is a monotonic sufficient reduction, not equality of the two families.

Let B_k be the Bell numbers1,1,2,5,15 for k=0,...,4. For q>=11, there are

    sum_(k=0..4) binomial(4,k) 5^(4−k) B_k =1540

possible endpoint patterns. At q=7 only one unmarked root is available,
so there are6^4=1296 patterns. The full labelled five-prime graph therefore
has at most1296*1540^4=7289334581760000 combinations before exploiting any
further response equality. No permutation of the five numerical primes
is licensed by this count. This is a complete finite parameterization,
not an exhaustive evaluation of that many gates.

At q, a direct variable-elimination state can use the five marked roots,
the at most four unmarked endpoint blocks, and a single aggregate for
all unused unmarked roots. It has at most ten categories; their masses
sum to Z_q. This preserves every declared pair event. The aggregate's
mass is(q−6−number_of_used_unmarked_roots)r_q. EP1 is an alternative
evaluation that avoids enumerating all category assignments.

### Why endpoint incidence cannot be discarded

Take only the pure first-root deletions0 at7,11,13, with all higher pure
slots and all stars absent. The actual source is uniform on the6,10,12
live roots. Keep just the unconditional7*11 and7*13 pair slots.

If both slots use the same live root at7, their avoiding mass is

    1−1/60−1/72+1/720=233/240.

If the two slots use different live roots at7, their avoiding mass is

    1−1/60−1/72=349/360.

Each individual event has the same mass in the two actual families; the
overlap, and hence the simultaneous survivor, differs by1/720. The fixed
central source/mask and two unused outside coordinates can be multiplied
into both examples without removing the distinction. This is a finite
counterexample to compression that records the separate edge masses but
forgets common-root incidence. It is not a counterexample to Erdős #7 or
to existence of a positive full continuation gate.

### The actual open gate

The task is still to prove, for every coherent endpoint pattern and every
globally fixed central-star layout, one supported source/thinning with a
positive complete L/W gate. Neither the cardinality calculation nor EP1
settles it. In particular the617 convex corner for a quinary column can
make that individual root weight negative; its old proof only required
the grouped A_q to remain positive. When endpoints expose that root
separately, the old coefficient monotonicity cannot be copied unchanged.
One can retain the15960 genuine local star profiles instead, or prove a
new bound whose signed extension is justified on the exposed categories.

Useful search targets are correspondence constraints on a complete graph,
inclusion-exclusion with inconsistent endpoint assignments, partition
functions with one forbidden pair per edge, and jointly sufficient
boundary compression. Any new certificate must retain the incidence
partition at each actual prime and keep one set of central roles and one
actual source through every query.
