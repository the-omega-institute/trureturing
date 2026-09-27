[Index](../../marked_head_profile.md) · [Actual source LP](88-a-weighted-source-comparison-on-the-broad-slab.md) · [Same mean and hinges](109-the-mean-and-all-hinges-share-one-original-test.md) · [Complete dominated error](115-a-dominated-defect-controls-complete-independent-label-tails.md)

# Signed face duals transport one shared finite source

Every original finite head in109 has an explicit upper bound away from
the K faces. It uses that branch's own optimal face LP dual, retains
negative parameter changes, and subtracts that branch's face slack before
maximizing. All costs use one shared pair of actual wrong-slot weights
q5,q15 and one shared survivor defect. The resulting finite objective is
convex in(q5,q15), so its nonnegative weighted sum can be maximized on
the vertices of one shared defect polygon.

This is a finite-source transport theorem and exact rational interface.
It does not retain109's saturation-only mean credit without an actual
replacement proof. Complete omitted remainders, that credit and actual
survivor mass are explicit inputs to the full-cost interface. Profile115
supplies a valid complete nonlinear defect error, but does not make the
full shared-budget objective convex. No new global K or Lean result is
asserted here.

## 1. Actual source domain and one matrix

Use85's actual effective-source coordinates with ROOT=(0,0,1,1,1):

    eta_l=(1-deficit_l)/9,
    d_l=z-alpha_ROOT(l)-beta_l,
    n_l=eta_l*d_l-late_l, s=sum_l n_l,
    h=sum_l eta_l, h0=eta0+eta1, h1=eta2+eta3+eta4.

The vectors deficit,alpha,beta,late are nonnegative with total caps
1/2,1/4,1/4,1/72 and lengths5,2,5,5. Also3/4<=z<=1. Put

    p=z-3/4, a=1/4-alpha1, b=1/4-beta2-beta3-beta4,
    Delta=p+a+b<=1/18.                                (S1)

These are actual assigned source budgets, not independently chosen
probabilities. In particular0<=p,a,b<=1/18. The actual common carrier
law pi is nonnegative of total1 on the18 pairs
(-1,0,1)x(-1,0,1,2,3,4), and

    t_l=sum_(u,v)pi_(u,v)*(1_(ROOT(l)=u)+1_(l=v)).      (S2)

Let H be an actual best first-five slot and

    r=h/5-Lambda(F_H),
    r1=h1/5-Lambda(root1 times F_H), 0<=r1<=r.

We use the packing guard

    0<=r<min(h/5,h1/5,min(eta2,eta3,eta4)/5).          (S3)

The original small-r branch r<1/12000 is a sufficient subdomain.
The proof below uses(S3), not that numerical restriction. As proved
in85, (S1) forces the source labels5,15,45 to be present, the latter
two on root1, with distinct first-five slots P,A,B. The whole first
beta label45 belongs to a cell L in{2,3,4}. Guard(S3) forces H to
avoid P,A,B. Relabel P=0,A=1,B=2,Q=3,H=4.

There is one actual matrix

    X_(l,j)=Lambda(cell_l intersect F_j), sum_j X_(l,j)=n_l.

The caps from88 are U_(l,j)=eta_l*p_(l,j), where p is zero in P,
root1 times A and cell L times B, equals1/5 in the remaining ordinary
entries, and in Q is

    p_(l,Q)=min(1/5,3/20+Delta+r/h), l<2,
    p_(l,Q)=min(1/5,1/10+Delta+r/h1), l>=2.           (S4)

Their derivation only uses the root-wide deletion sets and(S3), so
it remains valid throughout this domain. If actual r1 is supplied,
the sharper replacements are

    u=min(r/h,r1/h1,(r-r1)/h0),
    p_(l,Q)=min(1/5,3/20+Delta+u), l<2,
    p_(l,Q)=min(1/5,1/10+Delta+r1/h1), l>=2.          (S5)

For(S5), the pure5 deletion inside H has the same five projection
above both roots, so its measure is at most each of r/h,r1/h1 and
(r-r1)/h0. The root1-wide remainder R in85 is deleted throughout
root1, giving |R intersect H|<=r1/h1. These are the only substitutions
in88's Q-cap proofs.

Necessary actual-matrix constraints include

    eta_l/5-r<=n_l<=sum_j U_(l,j), s>=h/5-r,
    sum_l(eta_l/5-X_(l,H))=r.                        (S6)

The interface checks the first line. Passing those numerical checks
does not establish the existence of an actual source matrix or an
original covering; the theorem assumes the actual objects throughout.

## 2. Fixed face duals retain signed changes

For any group I, nonnegative coefficient vector z, capacities U and
mass N, define the capacity optimum

    D(z,U,N)=max{sum_i z_i*x_i:0<=x_i<=U_i,sum_i x_i<=N}
            =min_(gamma>=0)[gamma*N+sum_i U_i*(z_i-gamma)_+].

It suffices to minimize over0 and the coefficient values. A decreasing
coefficient fill supplies a matching primal; the implementation reuses
88's solver, which checks primal feasibility, dual feasibility and exact
equality.

Use the groups G0={0},G1={1},GR={2,3,4}, each times all five slots,
and N_G=sum_(l in G)n_l. For one fixed original branch, let starred
data denote its chosen face anchor and let gamma_G* be an optimal
dual for that branch's starred objective. Then

    sum_G D(z,U,N_G)-sum_G D(z*,U*,N_G*)
      <=sum_G gamma_G*(N_G-N_G*)
        +sum_G sum_(i in G)
           [U_i*(z_i-gamma_G*)_+
                         -U_i* *(z_i*-gamma_G*)_+]. (D1)

Indeed the same gamma_G* remains a feasible dual at the actual point;
subtract its exact starred value. No unchanged active set is needed.
All differences retain their signs. Replacing them by absolute values
is valid but discards cancellation that(D1) explicitly preserves.

On the canonical full beta face the group masses are1/36,1/12,5/36.
They and the cap table are independent of the distribution of the
root1 beta budget, so the face anchors are uniform across that whole
simplex. The other K face is obtained by exchanging cells0 and1,
including all source, carrier and original-test coordinates. This
finite relabeling preserves the proof; the implementation uses the
canonical orientation.

## 3. One finite original test for the mean and all hinges

Let a_t>=0, t in{1,...,8}. Retain the original six-label load B from
{1,3,9,5,15,45}, and the original selected labels25,27,75,81 in that
order. Put k_t=min(t-1,4); in particular k1=0. The shallow positive-seven
test contributes m_(l,j)=1_(ROOT(l)=T)+1_(j=F).

Actual wrong or absent complete seven weights satisfy
0<=q5,q15<=1/5. Retain the common density

    w^q_(l,j)=1-t_l/5-(1/5-q5)*1_(j=H)
                         -(1/5-q15)*1_(l>=2,j=H),
    1/5<=w^q_(l,j)<=1.                              (F1)

The virtual cofactor3 and9 families give t_l/5 exactly. The correct-H
5 and15 families give the two further retained densities. Dropping
other nonnegative virtual contributions and using85's one error measure
V-delta gives, for0<=phi<=M,

    integral phi dmu<=integral w^q*phi dLambda+M*omega,
    omega=(V-delta)(1).                             (F2)

Define, at each cell-slot pair,

    g_(t,m)(v)=1/[5*7^max((t-v)_+-m,0)]
                        +(6/35)*max(m-(t-v)_+,0),
    f_t^q(v)=w^q*(v-t)_++g_(t,m)(v).

Each f is increasing and integer-convex. Before v reaches t, the
positive increments of g grow geometrically up to6/35 and then remain
6/35. At v=t the next slope is w^q, at least1/5>6/35. Beyond that point
the slope is constant. This also covers m=0 and threshold1.

For each original branch b=(six-label layout,T,F), form

    H_b=sum_t a_t*f_t^q(B_b),
    Z_(b,i)=sum_(t:k_t>=i)a_t*
                      [f_t^q(B_b+i)-f_t^q(B_b+i-1)]. (F3)

Convexity bounds the insertion of the ith selected cylinder by the
coefficient Z_(b,i), regardless of which previous selected cylinders
contain the point. Every Z is nonnegative. The finite raw-source head
bound is the three-group capacity LP for H_b.

For a nonnegative coefficient array z, the selected-cylinder operators
at the same actual source are

    T_(3^a)(z)=3^-a*max_l sum_j p_(l,j)*z_(l,j), a=3,4,
    T_25(z)=5^-2*max_j sum_l E_(l,j)*z_(l,j),
    T_75(z)=5^-2*max_(u,j)sum_(ROOT(l)=u)E_(l,j)*z_(l,j),

where E_(l,j)=eta_l except in the same exact source exclusions as(S4),
where it is zero. For pure3, first remove late mixed35 restrictions;
the remaining five-coordinate caps are p within each cell, and the
ternary test cylinder has mass at most3^-a. For25 and75, use its actual
first-five slot, the full raw ternary masses, and five Haar cap1/25.
These are upper bounds for the arbitrary original selected cylinders,
not independent replacement measures.

Thus the complete finite contribution is bounded by

    C_b(theta,q)=LP_theta(H_b)+sum_i T_(label_i)(Z_(b,i)). (F4)

The transfer coefficient for this combined finite old load is

    M_a=sum_t a_t*max(6+k_t-t,0).                    (F5)

It follows directly from0<=B+selected_prefix<=6+k_t in(F2). Positive-seven
terms g already use their raw-source upper and are not charged a second
copy of omega. In particular the mean term contributes5*a1 to M_a.

## 4. Preserve each branch's face slack

Apply(D1) to H_b. For each selected label the exact signed change is

    max_i A_i(theta,q)-max_i A_i*,                   (B1)

where A_i are the finite candidates in its selected operator. Keeping
(B1) is sharper than replacing it by max_i(A_i-A_i*); both are valid.
Adding(D1) and(B1) gives a computable E_b with

    C_b(theta,q)<=C_b*+E_b(theta,q).

If C*=max_b C_b*, or any independently certified common upper, put
s_b=C*-C_b*>=0. Then

    max_b C_b(theta,q)
      <=C*+max_b[E_b(theta,q)-s_b].                 (B2)

Subtract the slack of the same branch whose sensitivity is being used.
Using an optimal face dual from a different original test, or dropping
the branch identity during the maximum, has no justification from(D1).
The function preserve_slack implements the exact identity in(B2).

## 5. One defect polygon for the whole finite cost vector

Profile85 proves on its small-r slab

    G*q5+g0*q15+omega<=e,
    e=rho-(r+r1)/5>=0, g0=397/36000.                (P1)

Here G is85's positive actual five-slot gap. Any separately proved
stronger positive pair g5,g15 may replace G,g0; the implementation
accepts them explicitly. In particular117's shared packing prices can
be substituted without changing the optimization proof.

For fixed actual source theta, source constraints do not depend on q.
The LP is a maximum of affine functions of q. Each selected operator
is also a maximum of affine functions, hence C_b and max_b C_b are
convex in q. The fixed-face-dual upper is convex as well: its only
nonlinear head terms are nonnegative capacities times positive parts
of affine coefficients, and its selected terms have the same property.

For nonnegative weights beta_f and finite cost bounds F_f(theta,q),
with this established convexity, put M=sum_f beta_f*M_f. The shared
finite bound is

    max_(q in P_e)[sum_f beta_f*F_f(theta,q)
                              +M*(e-g5*q5-g15*q15)],
    P_e={0<=q5,q15<=1/5:g5*q5+g15*q15<=e}.          (P2)

The objective is convex on this compact polygon, so its maximum is
attained at a vertex. Every point is a convex combination of vertices,
and Jensen bounds its value by the largest vertex value. The rational
interface enumerates all pairwise intersections of the four box edges
and the budget line, then retains the feasible ones. It handles e=0
and the full-box case exactly.

The weighted costs share the same polygon vertex in(P2). Maximizing
each cost over its own q separately discards this compatibility. Costs
still keep independent original test branches, as required by the
existing cost-vector problem.

## 6. Complete-cost inputs and the nonlinear error boundary

Let the full cost expansion have constant a0=f(1), and suppose the
remaining actual contribution for branch b has a proved upper R_b.
Let c_b be a proved nonnegative lower bound for the additional mean
credit needed in the109 derivation, beyond deletion already retained
by(F1). This is an additive credit in that derivation, not an arbitrary
amount of deleted mass that can be subtracted again. Then the complete
branch has the conditional upper

    a0*S+C_b(theta,q)+R_b-a1*c_b+M_a*omega.          (T1)

The constant uses the actual survivor mass S. On the face,109 supplies
particular R_b* and c_b*, face mass S* and omega*=0. To transport that
whole face branch with its own slack, the complete additional error is

    a0*(S-S*)+E_b+(R_b-R_b*)
                      +a1*(c_b*-c_b)+M_a*omega.   (T2)

Taking c_b=0 is always permissible for a nonnegative additional credit,
but pays its entire former face improvement. The actual c_b* cannot
be carried over merely because the finite head LP is continuous.
Similarly the complete tail constants of98/109 are not asserted at
an arbitrary actual source without the appropriate complete-tail proof.

Profile115 establishes complete infinite error bounds from the stronger
domination nu<=Haar, nu(1)<=omega. Its functions B_k(omega) tend to zero
but are concave piecewise-affine functions, so

    finite_convex(q)+B_k(e-g5*q5-g15*q15)

need not be convex. Profile115 gives an exact interior counterexample
to a vertices-only claim. Two valid uses with the present interface are:

* Bound the infinite error uniformly by B_k(e), then use(P2) only for
  the finite part. This may discard a shared-budget gain, but is valid.
* Fix omega, use the polygon with budget e-omega and add M*omega plus
  the complete error, then perform a separate certified one-dimensional
  maximization in omega. The extra optimization is an additional task.

An arbitrary supplied branch credit or tail function likewise cannot
be declared convex. Its dependence on q must be proved, or bounded
uniformly before(P2). No TV-mass-only linear bound for unbounded label
loads is used here.

## Reproduction and scope

Run

    python3 -I -O docs/reports/erdos7-odd-covering/frontier/retained-transport/finite_source_face_transport.py --check

The semantic certificate verifies exact existing face tables, the
actual-source definitions,88's caps on their original subdomain,
tighter root-loss caps, face-dual majorization at rational source
points, exact face recovery, finite-cost convexity, shared polygon
degeneracies and a common weighted finite objective. The four retained
original branches are regression inputs, not an exhaustive maximum
over all125000 branches. The general theorem is the ordinary argument
above; the certificate does not infer it from sampled source points.

The executable APIs are source_point, prepare, branch, signed_transport,
preserve_slack, defect_vertices, shared_vertex_upper and
assemble_complete_branch. Complete-tail and additional mean-credit
hypotheses remain explicit. This interface supplies the finite part of
a whole-face neighborhood proof; it does not by itself lower the
current global comparison or settle unrestricted Erdős#7.
