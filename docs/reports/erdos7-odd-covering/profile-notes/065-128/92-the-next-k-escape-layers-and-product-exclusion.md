[Index](../../marked_head_profile.md) · [Original J/K control faces](71-global-j-k-control-faces-and-exact-escape-gaps.md) · [Actual mass and global comparison](74-a-strict-global-k-gain-from-the-controlling-faces.md)

# The next K escape layers and product exclusion

Outside the six K zero controls and18 J zero controls of71, the
original complete K signed table has minimum

    gamma2=14158742250938240063000691811817435200717494240697
                /24344652964341558386865026089989867851282700000000
          =0.5815955672761912704681... .                   (EL1)

This is12.38730513022282328283... times the preceding positive
gap gamma1=gamma_K. Both mass endpoints and all18 full, partial
and empty carriers are included. The minimum is attained exactly
at386 with carrier(1,1) and592 with carrier(1,0), both at D_c.

The result identifies a larger region which new cost inequalities
can address jointly. It supplies stronger escape inequalities for
the old actual-source comparison. It does not itself improve a
cost on those faces, establish their realizability, lower the
global K target or solve unrestricted Erdos #7. These are ordinary
finite-table and product-measure results, not Lean declarations.

## 1. The full old table is recovered without recomputing source costs

For every source vertex v, carrier c and actual mass endpoint X,
the certified71 table records the signed expression

    g_(v,c)(X)=A*X+(K0-offset)*M_(v,c)+C_(v,c), A>0.

There are1296 source vertices,18 carriers and two endpoints:
D_c and raw source mass s. Hence

    g_(v,c)(s)=g_(v,c)(D_c)+A*(s-D_c)
                              >=g_(v,c)(D_c).          (EL2)

A compact [gap dictionary](../../certificates/source_norms/endpoint-bounds/k_signed_gap_dictionary.json)
stores the3344 distinct rational lower gaps and23328 dictionary
indices. The checker reconstructs both endpoints using(EL2).
The SHA-256 of the entire ordered46656-row table must equal the
already published71 table digest. This binds the compact input
to the preceding complete verification; no earlier cost/layout
enumeration is repeated.

The upper endpoint exceeds its lower endpoint by at least
3.0152767168393412457175... everywhere. Its minimum outside the
J/K union is6.1598574934289725750455... . Thus no missing upper
endpoint, partial carrier or empty carrier can undercut(EL1).

## 2. The union has four exact product regions

Use71's factor order(deficit,alpha,beta,late,z,carrier), with
simplex index0 the zero vector and index j>0 the j-1 cap basis
vector. Put B={3,4,5}. The maximal Cartesian boxes of Z_K union Z_J
are exactly

| Region | Deficit | Alpha | Beta | Late | z | Carrier |
| --- | --- | --- | --- | --- | --- | --- |
| K first | {1} | {2} | B | {1} | {0} | (1,1) |
| J first | {1} | {2} | B | B | {0} | (0,1) |
| K second | {2} | {2} | B | {2} | {0} | (1,0) |
| J second | {2} | {2} | B | B | {0} | (0,0) |

Their source dimensions are2,4,2,4. The checker exhausts every
legal single-coordinate enlargement from the24 singleton controls,
which finds all maximal Cartesian boxes and verifies their exact
union. The boxes refer to the relaxed source/carrier table, not
to asserted actual covering configurations.

Write d_j,a_j,b_j,l_j,z_j for source factor weights and pi_rc for
the same actual forbidden-carrier mixture. With b_B=b3+b4+b5 and
l_B=l3+l4+l5, the exact product mass is

    q(Z_K union Z_J)
      =a2*z0*b_B*[d1*(l1*pi11+l_B*pi01)
                              +d2*(l2*pi10+l_B*pi00)]. (EL3)

Each of the J controls has K-table gap exactly gamma1, and each
K control has gap0. On the complement every gap is at least
gamma2. Therefore the old separately concave source comparison
has product-barycentric lower bound

    B_K>=gamma1*q(Z_J)
                  +gamma2*[1-q(Z_K)-q(Z_J)].          (EL4)

Dropping the first nonnegative term also gives the simple escape
bound gamma2*[1-q(Z_K union Z_J)]. The improvement is available
with the same source and carrier weights used by71, before any
claim about new cost bounds on the enlarged region.

## 3. J and K mass cannot concentrate independently

There are two independent factors that separate these regions.
Define

    L_K=l1+l2, P_K=pi11+pi10.

K controls require both events. J controls require late indices
in B and carriers(0,1) or(0,0), each contained in the corresponding
complement. Product-factor independence consequently gives

    qK<=L_K*P_K,
    qJ<=(1-L_K)*(1-P_K).                            (EL5)

Other source factors and the matching conditions within each box
can only reduce these masses. Cauchy--Schwarz yields

    sqrt(qK)+sqrt(qJ)
      <=sqrt(L_K*P_K)+sqrt((1-L_K)*(1-P_K))<=1.       (EL6)

A useful purely rational consequence requires no positive lower
bound on qK. Put sigma=1-qK. Since L_K,P_K>=qK,

    qJ<=(1-L_K)*(1-P_K)<=sigma^2.                   (EL7)

Substitute(EL7) into(EL4), using gamma2>gamma1:

    B_K>=gamma2*sigma-(gamma2-gamma1)*sigma^2,
                       0<=sigma<=1.                (EL8)

Thus even without a new estimate covering J's faces, the product
structure restricts how much of the escaping K mass can sit at
the old small gap gamma1. Treating qK and qJ as arbitrary disjoint
masses loses this restriction.

For combination with a target decrement h, keep the denominator
bound with these same weights. The raw source mass is separately
affine in the five factors. Every K zero control has raw mass1/4,
and every source vertex has mass at most5/9. Hence the established
denominator E<=S<=s satisfies

    E<=1/4+(11/36)*sigma.                           (EL9)

Subtracting hE from the old signed comparison, and retaining any
additional independently justified cost or mass reserve, gives

    Phi_new>=-h/4+(gamma2-11*h/36)*sigma
                    -(gamma2-gamma1)*sigma^2
                    +other_valid_reserve.          (EL10)

The displayed polynomial is strictly concave in sigma for every h.
Its minimum on a closed interval occurs at an endpoint. This
reduces global consumers to exact endpoint inequalities without
counting the old escape term twice or treating E independently
of the source weights. No target decrement is asserted here.

## 4. The next two controls enlarge the K beta triangles

The two controls achieving gamma2 have factor coordinates

    386:(1,2,2,1,0), carrier(1,1),
    592:(2,2,1,2,0), carrier(1,0).

At386, the deficit cap and late cap lie in cell0, alpha is on
root1, and beta is on the other root0 cell1. At592 the two root0
cells are exchanged. Both have s=1/4 and D_c=53/360. Relative to
the preceding K regions, their beta allocation moves out of the
root1 triangle.

Let A be these two additional source/carrier points. The maximal
boxes of Z_K union Z_J union A are the same four boxes above,
except that the first K beta set becomes{2,3,4,5} and the second
becomes{1,3,4,5}. The K source dimensions become3; the two J
dimensions stay4. The additional product mass is exactly

    q(A)=a2*z0*[d1*b2*l1*pi11+d2*b1*l2*pi10].        (EL11)

On the complement of this26-point union, the next exact gap is

    gamma3=131097134374357952846687928903046514235992135314423
                /162297686428943722579100173933265785675218000000000
          =0.8077572592616973424912... .              (EL12)

It occurs at386 and592, each with carrier(1,2),(1,3) or(1,4),
again only at D_c. In particular these are different carriers
at the same source vertices; excluding a vertex wholesale would
lose the correct next obstruction.

The corresponding additional inequality is

    B_K>=gamma1*q(Z_J)+gamma2*q(A)
                     +gamma3*[1-q(Z_K)-q(Z_J)-q(A)]. (EL13)

## 5. Exact verification

The [checker](../../frontier/endpoint-bounds/k_next_escape_layers.py) verifies the
complete original table digest, all source/carrier indices and
both mass endpoints, the exact minima and all attaining controls,
both maximal-box inventories, product-mass polynomial identities
on every basis tuple, and both layered inequalities at every
lower endpoint. It also checks the disjoint late and carrier
supports underlying(EL5); the all-weight proof of(EL6)--(EL8) is
the ordinary argument above. The
[certificate](../../certificates/source_norms/endpoint-bounds/k_next_escape_layers.json)
contains the exact layer constants and source data of every new
minimizer. The dictionary is reusable result data tied to71's
full table, not a new independent source-cost calculation.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/k_next_escape_layers.py --check
```
