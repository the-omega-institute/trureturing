# Genuine three-fibre constraints beyond every pair exclusion

For one fixed original two-centre family, three old-coordinate profiles
can each satisfy all pairwise zero-survivor budget tests while their actual
23/29 survivor fractions obey

    s1+s2+s3 >=3/308.                                         (J1)

The profiles occur in the auxiliary support of
[report492](492-mixed-split-common-pair-support-obstruction.md), including
its positive-weight refinement at the actual45/75 phases(31,16) from
[report493](493-retained-shallow-anchors-leave-the-pair-obstruction.md).
Thus a genuine multi-point inventory excludes information permitted by all
the previous pair tests. The result is an ordinary arithmetic proof with
an exact rational certificate, not a new Lean theorem or an unrestricted
Erdos#7 conclusion. It gives a local constraint, not yet a sufficient global
same-source mass bound.

## A multi-point inventory for one original family

Fix distinct odd primes p,q and a finite original congruence family with
pairwise distinct odd numerical moduli greater than1. Other prime factors
belong to a fixed finite old coordinate set disjoint from p,q. Each later
label is an original complete number

    m=d*p^j*q^k, j+k>0,

and its old residue is one of two fixed references A,B modulo d. The
selector belongs to this full numerical label; it may depend on j,k but
never changes with the tested old point or with an estimate. All original
new-coordinate residues and finite heights are arbitrary and remain fixed.

Choose any finite list of old points x1,...,xn with finite labelled divisor
inventories A_i,B_i. These may be the full finite reference valuation boxes,
which conservatively include unused original labels. The unit old cofactor
d=1 is retained. For each nonempty subset I of point indices set

    N_I=sum_d max(sum_(i in I)1_Ai(d),sum_(i in I)1_Bi(d)).     (J2)

Only d in the finite union of the boxes contributes. At each fixed new
exponent pair(j,k), numerical distinctness allows at most one original
class for each d. Its one fixed selector contributes either the A-count
or the B-count over I, hence at most their maximum. This proves the capacity
N_I simultaneously for all I. The maxima for different I need not be
jointly attained; they are upper bounds on the SAME original family.

Let alpha_i,beta_i be the actual union-deletion fractions from the p-only
and q-only axes in fibre i. Let gamma_i be the sum of masses of all active
mixed p/q original cylinders there. Put a=p-1,b=q-1 and

    t_i=a*alpha_i, u_i=b*beta_i, c_i=ab*gamma_i.

Geometric sums over positive exponents give the simultaneous necessary
budgets

    0<=t_i<=a, 0<=u_i<=b, c_i>=0,
    sum_(i in I)t_i<=N_I,
    sum_(i in I)u_i<=N_I,
    sum_(i in I)c_i<=N_I.                                    (J3)

Finite original exponent sets only reduce these complete geometric sums.
Let s_i be the fraction of full p/q Haar in fibre i surviving all original
LATER classes. The surviving axis set is a Cartesian product in these two
new coordinates. Subtracting the mixed union by its total mass gives

    ab*s_i >=[(a-t_i)(b-u_i)-c_i]_+.

No independence of any conditioned old source is used here. Consequently

    ab*sum_i s_i >=[sum_i(a-t_i)(b-u_i)-N_all]_+.              (J4)

Define the compact nonempty axis polytopes

    P_h(N)={z:0<=z_i<=h, sum_(i in I)z_i<=N_I for all I}.

The general uniform local bound is

    sum_i s_i >=K_n(N)/(ab),
    K_n(N)=max(0,min_(t in P_a,u in P_b)
                         [sum_i(a-t_i)(b-u_i)-N_all]).        (J5)

This relaxation retains all subset axis constraints and only the total
mixed constraint. More of J3 may strengthen it. It does not assert that a
minimizing relaxed budget comes from original residues. The bilinear
objective attains its minimum at a vertex pair: from any global minimizer,
first minimize over t at a vertex and then over u at a vertex, without
increasing the value. This gives a finite exact computation whenever the
inventories are finite.

If all x_i also avoid the original OLD-ONLY classes, their s_i are the
full-family survivor fibres. Old-only-covered points do not gain original
survivors from J5. In the source argument the completed actual source's
support supplies precisely this old-survival condition.

## A strict three-point instance with every pair still feasible at zero

Take p=23,q=29, old primes(3,5,7,11,13,17,19). The two centres differ in the
first digit at3,5,7 and agree through every originally queried depth at the
last four primes. Choose common auxiliary extensions there without altering
any original residue. Signed+f means(f,1),-f means(1,f), and0 means(1,1)
at the first three coordinates; each remaining f means(f,f).

Use the profiles

    v1=(2, 2,-2,2,1,2,1),
    v2=(2, 2,-2,1,2,2,1),
    v3=(2,-2, 0,2,2,2,1).                                   (J6)

Literal Cartesian enumeration of the labelled old exponent boxes gives

    (N1,N2,N12,N3,N13,N23,N123)=(20,20,40,24,40,40,58).       (J7)

The exact consumer sums original-label membership counts, rather than
applying a formula valid only when all old primes split. Its union contains
36 old labels. The retained membership-pattern histogram reconstructs all
seven values in J7.

Use three nonnegativity rows and seven subset rows, with singleton right
sides min(h,N_i), to describe P_h exactly. These polytopes have nonempty
interior: a sufficiently small positive vector satisfies all upper bounds
strictly. Any vertex must have three linearly independent active normals;
otherwise small steps in a nonzero orthogonal direction contradict
extremality. Conversely a feasible intersection of three independent active
rows is a vertex. Solving every choice of three rows by rational Gaussian
elimination therefore gives the complete vertices. There are13 for P22
and14 for P28. All182 vertex-pair values of

    F(t,u)=sum_i(22-t_i)(28-u_i)-58

are at least6. Equality is attained at

    t=(18,18,22), u=(20,20,0),
    ((22-t_i)(28-u_i))_i=(32,32,0).                           (J8)

Thus J5 proves J1 for any three points of these profiles in the SAME
original family, uniformly over all its original23/29 phases. In particular,
for every0<theta<=1/308, no three such points can all satisfy s_i<theta.
The strict small-fibre inequality matters at equality.

The value6 is sharp for this stated relaxed expression, not asserted sharp
for the actual arithmetic. For instance J8's raw area32 exceeds the
singleton mixed budget20 at each of the first two points, so it is not a
joint zero-residual realization.

Each pair separately does admit a zero witness in the older relaxation:

| Pair | axis23 allocations | axis29 allocations | mixed deletion |
| --- | --- | --- | --- |
| 1,2 | (20,20) | (20,20) | (16,16) |
| 1,3 | (20,20) | (18,22) | (20,12) |
| 2,3 | (20,20) | (18,22) | (20,12) |

Each row obeys its individual and shared axis/mixed capacities. These
separate witnesses cannot be combined into zero residuals at all three
points under the simultaneous budgets J3. This is not a clique consequence
of the positive-pair graph: the three pair bounds themselves are zero.

## Positive comparison regions and the same-source mass bridge

The profiles are indices108,98,931 of report492's explicit profile order,
and all belong to its pair-admissible upward support. At fixed references
(2,7,3,4), their auxiliary comparison masses are respectively

    506368/6348447105,
    528384/8931797875,
    352256/11789973195.                                      (J9)

All are positive, and retaining the actual extra classes31 mod45 and16 mod75
does not change any of these three masses. The consumer checks this in the
literal675-cell initial chart. These are eta masses, not lower bounds on
occupation by the completed actual source nu. No claim that every original
family has actual old survivors in all three regions is needed or made.

For a fixed theta let T={actual source points x:s(x)<theta}. Close its
attained profile support upward only in the later coordinates7,11,13,17,19,
holding3/5 factors fixed, as in report489. Growing each labelled box makes
every N_I nondecreasing, enlarges each P_h, and increases the subtracted
N_all. Thus K_n is nonincreasing. If all three J6 profiles were in this
upward closure, choose attained bad ancestors; their smaller inventories
have at least the same K3, contradicting J1. The certified triple therefore
excludes simultaneous membership in the actual upward comparison support.

Use theta=1/3696 when combining with the existing full pair graph. Its weak
pair edges have K2>=1/3, which matches2*616*theta. A triple requires
K3>=3*616*theta=1/2; J6 gives6. Raising theta to1/308 while retaining every
old weak pair edge would be invalid.

For any finite collection of valid pair/triple edges e at a common theta,
let z_v indicate the upward support. Each edge obeys

    sum_(v in e) z_v<=|e|-1.

Nonnegative rational packing weights lambda_e with

    sum_(e containing v)lambda_e<=eta(profile v)

then imply

    eta(upward support)<=eta(Q>=20)-sum_e lambda_e.           (J10)

Indeed each edge forces sum_(v in e)(1-z_v)>=1, and the vertex capacity
inequalities bound the weighted sum by omitted mass. Counting all Q>=39
mass on the upper side remains safe when the selected edges are finite;
it does not assert that every triple touching this overflow has zero bound.
The complete conditional-source comparison gives nu(T)<=eta(upward support).
If a future certificate obtains U_bound<m7, the existing source bound
nu<=(27/2)H yields

    H(original survivors)>=(2/27)*theta*(m7-U_bound)>0.       (J11)

A single J6 edge gives at most the minimum mass in J9 as a direct packing
discount, about2.99e-5. No assertion that J10 presently crosses m7 follows
from this one edge. A sufficiently strong uniform mass certificate remains
open, as do the other mixed source/reference configurations and unrestricted
Erdos#7.

## Reproduction and scope

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_three_fibre_obstruction.py

The standard-library consumer reconstructs the literal inventories, every
rational vertex and all182 objective values, checks the pair zero witnesses,
reconstructs the pinned support's profile order and membership, and computes
the exact six/eight-anchor weights. The full result is compared with the
adjacent JSON. It reuses the pinned comparison caps and support identity;
it does not rerun the complete pair audit, source producer or Lean.

Synchronous permutations of old coordinate axes or a global A/B exchange
preserve the literal N_I when applied to all three points together. Their
weights and actual chart eligibility must still be recomputed. Downward
labelled-box inclusion preserves the positive bound; upward enlargement does
not. These are precise ways to extend the certificate without assigning a
new reference or selector to each tested point.
