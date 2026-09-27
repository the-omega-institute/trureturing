[Index](../../marked_head_profile.md) · [Original private sets](357-original-private-swaps-and-prime-reset-transport.md) · [Shared capacities](359-synchronized-parent-capacity-allocation.md) · [Mean partial matching](360-mean-partial-matching-without-tail-loss.md)

# Reserving prime overlaps before charging composite parents

The shared capacity allocation of 359 separates into two budgets. Prime
parents use at most the excess already forced by the original prime
classes. Composite parents use only the remaining excess, with a sharper
exact bound determined by the original modulus palette. Applying 360's
mean partial matching gives two simultaneous scalar constraints, including
a composite-parent rank bound that is not implied by the explicitly listed
older mass constraints and the new total-rank bound, even with both of
their exact fixed-palette capacity improvements.

The separating example below is an abstract rational mass profile, not an
AP cover. Its six-prime support is already excluded by an independent
known nine-prime condition. Its only role is to distinguish a specified
finite family of inequalities. No unrestricted contradiction, literature
novelty, or Lean verification is claimed.

## 1. Reserve the original prime overlap once

Use the same lexicographically minimal hypothetical distinct odd cover as
in 350, 359 and 360. Write D for its original divisor-closed modulus set,
Lambda for its prime support, s=|Lambda|, and H for uniform measure on the
full original period. Every support prime is an original label, comparable
original classes are disjoint, and every point is covered. Set

    k(y) = number of original prime classes covering y,
    t(y) = number of original composite classes covering y,
    h = H_cov = integral (k+t-1) dH,
    P0 = product_(q in Lambda) (1-1/q),
    J = integral (k-1)_+ dH
      = sum_(q in Lambda) 1/q - 1 + P0.                 (PR1)

The expression for J follows from CRT independence of the distinct prime
coordinates. It does not assume independence of composite labels.

Choose actual partial matchings at every original prime-private point as
in 360. Retain its selected sets S_(q,e,m), their disjoint-height unions
S_(q,m), and the exact coefficients alpha_(q,m), rho_(q,m), beta_(q,m)
from 359. Split the left side of MP5 by the type of the genuine original
parent m:

    B_prime = sum_(q,m prime) beta_(q,m)/(alpha_(q,m) rho_(q,m))
                              * H(S_(q,m)),
    B_comp  = sum_(q,m composite) beta_(q,m)/(alpha_(q,m) rho_(q,m))
                                  * H(S_(q,m)).         (PR2)

For each pair, its source charge is at most its target capacity
`integral_(A_q intersect A_m) 1/k dH`. At a target point with k>0,
there are at most k(k-1) ordered prime-parent pairs and at most kt
ordered composite-parent pairs. Dividing by this same k gives

    prime-parent load     <= (k-1)_+,
    composite-parent load <= t 1_(k>=1).               (PR3)

At k=0 both loads vanish. These are pointwise bounds on the same original
world and law, not sums of separately optimized budgets. Since k+t>=1,

    B_prime <= J,
    B_comp <= M_comp <= h-J,                           (PR4)

where the exact full composite-target budget is

    M_comp = integral t 1_(k>=1) dH
           = sum_(m composite in D) (1/m)
               [1-product_(q in Lambda, q not dividing m)(1-1/q)].
                                                           (PR5)

To obtain PR5, condition on an actual composite class A_m. Every prime
dividing m is absent there by comparable-class disjointness. The other
prime coordinates retain their independent probabilities 1/q. Some parent
pairs may have no original child; counting all pairs only enlarges this
upper bound and does not invent a source or parent.

There is a useful exact accounting identity. Let phi be Euler's totient:

    M_comp = sum_(m composite) 1/m
             - P0 sum_(m composite) 1/phi(m),
    h-J-M_comp = P0 [sum_(m composite) 1/phi(m)-1]
               = integral_(k=0) (t-1) dH >= 0.         (PR6)

Thus the last scalar inequality in PR4 is precisely the usual conditional
union bound on the region avoiding all prime classes. That union bound
is not a new theorem here. The content retained by PR4 is which actual
matching-source charges must fit into each part of the common budget.

## 2. Two consequences for all prime-private sources

Let p_q(z), c_q(z) be the numbers of prime and composite parents in the
selected partial matching at z in Priv_q. Write

    pi_q = H(Priv_q),
    r_q = q-2+q^(1-H_q),
    alpha_q = q/(q-1)(1-q^(-H_q)),
    X_prime = sum_q alpha_q^(-1) integral_(Priv_q) p_q dH,
    X_comp  = sum_q alpha_q^(-1) integral_(Priv_q) c_q dH.

All heights H_q are the full original heights. CA11 and PR4 give

    X_prime <= 2 B_prime <= 2J,
    X_comp  <= B_comp <= M_comp <= h-J.               (PR7)

Choose the first-cover partial matching of 360, or a maximum matching
with a fixed tie rule. Its mean size on each complete uniform q-tail is
at least r_q. Integrating over the actual prime-private cofactor region
therefore yields

    R := sum_q (r_q/alpha_q) pi_q
       <= X_prime+X_comp <= 2J+M_comp <= h+J.          (PR8)

Since J<=h, the last bound improves MP7's R<=2h. The fixed-palette
intermediate bound `2J+M_comp` also retains the zero-prime excess in PR6.

At any source there are at most s-1 distinct prime parents. Consequently
`c_q >= p_q+c_q-(s-1)` and `c_q>=0`. The same mean-rank bound gives

    gamma_q = (r_q-(s-1))_+ / alpha_q,
    sum_q gamma_q pi_q <= X_comp <= M_comp <= h-J.     (PR9)

PR8 and PR9 use the same selections. Neither adds a second independently
allocated copy of the surplus. The exact parent-dependent coefficients
in PR2 remain stronger than their coarse type factors in PR7.

For comparison, the older type refinement, without reserving J, gives

    eta_q = max(r_q/2, r_q-(s-1)/2)/alpha_q,
    sum_q eta_q pi_q <= J+M_comp <= h.                (PR10)

Indeed `c_q+p_q/2` is at least half the matching size and at least that
size minus (s-1)/2. The undivided total allocation from 359 is already
at most `J+M_comp`; this fixed-palette improvement does not require the
two separate source bounds PR7. Pointwise
`2 eta_q = r_q/alpha_q + gamma_q`, so PR10 says
`R + sum_q gamma_q pi_q <= 2(J+M_comp)`. Separate upper bounds on the
two summands in PR8 and PR9 retain information lost by this combined bound.

## 3. Multiple resets do not provide a second prime-overlap budget

In 357's PT11--PT12, the reset target V_S consists of points whose exact
set of covering original labels is the prime set S. Its source charge
is at most `(|S|-1)H(V_S)`. The V_S are disjoint, and each is contained
in the region k=|S|, t=0. Therefore the entire PT12 charge is at most J.

It is valid to add that charge to B_comp and bound their sum by h. But
this is dominated by `B_comp+J<=h` from PR4. No additional return
surplus is obtained by counting PT12 again after the prime-overlap
reservation. PR6 also shows why the scalar statement M_comp<=h-J,
considered without its selected-source lower bounds, only restates
conditional coverage.

## 4. An exact separation of the listed scalar constraints

This section specifies rational numbers only. Take

    Lambda = {3,5,7,11,13,17},
    Q = product_(q in Lambda) q^2 = 65155115025,
    D = {d>1 : d divides Q}.

There are 728 distinct odd nonunit moduli, of which 722 are composite.
All prime heights are two. Fix h to the palette's actual reciprocal
excess, rather than treating it as an adjustable parameter:

    h = product_q (1+1/q+1/q^2)-2 = 50464907/79554475,
    J = 9623/36465,
    P0 = 6144/17017.

For every composite d put

    cap_d = P0/phi(d),
    C = sum_(d composite) cap_d = 1454272/3468465,
    v = C-P0 = 264128/4535685.

Here cap_d is the exact mass of A_d inside the no-prime region in any
realization with comparable-class disjointness; v would be the excess
there. In the abstract profile these formulas specify the comparison
bounds, without asserting that such a realization exists.

For each prime define

    mu_q = P0/(q-1),
    L_q = mu_q max(0, 1-sum_(d composite, q not dividing d) 1/phi(d)),
    U_q = mu_q [1-max_(d composite, q not dividing d) 1/phi(d)].

The lower bound is the union bound in the region where q is the only
prime label present. The upper bound subtracts the contribution of one
actual q-free composite AP in that region. First define the composite
masses using two disjoint groups:

    G5 = {d composite : 5 divides d, 7 does not divide d},
    G7 = {d composite : 7 divides d, 5 does not divide d},
    A5 = sum_(d in G5) cap_d = 346432/2433431,
    A7 = sum_(d in G7) cap_d = 13417984/153306153.

Both A5 and A7 exceed v. Put

    pi_d = cap_d (1-v/A5)   if d in G5,
           cap_d (1-v/A7)   if d in G7,
           cap_d           otherwise.               (PR11)

Exactly v is removed from each group, so

    sum_(d composite) pi_d = C-2v = P0-v
                          = 17855296/58963905.

Now put

    pi_3=L_3,  pi_5=L_5,  pi_7=L_7,  pi_17=U_17,
    pi_11=(1/10) sum_(d composite:11|d) pi_d,
    pi_13=[J+M_comp-sum_(q!=13) eta_q pi_q]/eta_13.   (PR12)

Here `M_comp=h-J-v` and the eta_q are the exact height-two coefficients
of PR10. This saturates PT6 at 11 and the old fixed-palette total type
budget. The resulting prime masses are:

| q | pi_q |
| --- | --- |
| 3 | 2370976/19654635 |
| 5 | 24613312/766530765 |
| 7 | 103328/8423415 |
| 11 | 87699055669184/13940884311278925 |
| 13 | 20359625422507357996/883348201944976192425 |
| 17 | 320/17017 |

The standalone checker verifies the following specific constraint family
with exact rational arithmetic:

1. D is distinct, odd, nonunit and divisor-closed, with heights two;
   h is its reciprocal excess; h>=J and `sum_comp 1/phi(d)>=1`.
2. For each composite, `max(0,cap_d-v)<=pi_d<=cap_d<=1/d`;
   `P0-v<=sum_comp pi_d<=P0`.
3. For each prime, `L_q<=pi_q<=U_q<=mu_q<=1/q`;
   `sum_prime pi_q<=sum_q mu_q`, the exact-one-prime regional mass.
4. The total private mass lies in `[1-h,1]`.
5. Every PT6 inequality `sum_(d composite:q|d) pi_d<=(q-1)pi_q` holds;
   those for q=5, q=7 and q=11 are equalities.
6. MP7 holds even with the fixed-palette total capacity `J+M_comp` in
   place of h. PR10 is an equality. The new exact PR8 bound
   `R<=2J+M_comp`, and even the coarse PR9 bound
   `sum_q gamma_q pi_q<=h-J`, also hold.
7. PT12 holds even with upper bound J in place of h. Its support-set
   formula agrees exactly with its kappa-coefficient formula from 357.
8. Each PT13 stage charge is at most
   `(1/P)[1-product_(q<P)(1-1/q)]`. This prime-label overlap baseline is
   a known lower bound on actual u_P from the earlier original prime
   classes. Thus that necessary stage bound cannot exclude the profile;
   no actual u_P or v_P has been supplied or claimed to be realized.

The per-composite lower bound in item 2 follows, for an actual cover,
by charging nonprivate points of A_d inside k=0 to the nonnegative
excess t-1 there. The total lower bound follows from
`1_(t>=2)<=t-1` on that region. Thus these checks include regional
restrictions as well as individual AP and total-mass upper bounds.

Nevertheless, writing

    delta = 26728255069959585256/1236687482722966669395
          > 0.0216,

the exact values obey

    sum_q gamma_q pi_q - M_comp = delta > 0,
    2J+M_comp-R = delta,
    sum_q eta_q pi_q = J+M_comp = 2887427701/5011931925,
    M_comp = 1564794466/5011931925 = h-J-v.            (PR13)

Thus the listed scalar family, including the exact new total-rank bound
and the coarse new composite-rank bound, does not imply the exact
composite-rank bound. This is a statement about that finite scalar
relaxation only. There are no supplied AP residues, actual private regions, period-grid
integrality, exact V_S masses, or common selected sets S_(q,e,m); the
full parent-dependent MP5/CA9 system is not being tested. Nor is this
the family of all known necessary conditions: the independent
[nine-prime result](../../../../../Library/Arith/schroeder2026nine.md) already
rules out this six-prime support. No new prime-support lower bound is
inferred from the example.

## 5. Literal AP checks and scope

The [standalone checker](../../frontier/cover-geometry/prime_overlap_reservation.py) also
enumerates the three distinct even-cover fixtures from 357, with periods
12, 144 and 960. It checks comparable-class disjointness, the pointwise
ordered-pair loads of PR3, the exact CRT formulas for J and M_comp,
the no-prime excess identity PR6, and the actual multiple-reset maps
into the exact-prime-only regions. The resulting values are:

| Period | h | J | M_comp | h-J-M_comp | PT12 charge |
| --- | --- | --- | --- | --- | --- |
| 12 | 1/3 | 1/6 | 1/12 | 1/12 | 1/8 |
| 144 | 13/36 | 1/6 | 1/12 | 1/9 | 1/9 |
| 960 | 79/120 | 3/10 | 17/64 | 89/960 | 1367/7680 |

The period-12 fixture has all required original parents. Selecting actual
maximum partial matchings on every prime-private point gives

    B_prime=1/8, B_comp=1/12,
    X_prime=1/4, X_comp=1/12,
    R=5/18, sum_q gamma_q pi_q=1/12.

The checker verifies every selected source's full-height containing
cylinder and actual target capacity before adding its charge. The other
two fixtures lack some original parents, as reported in the output, and
are not used to claim an all-private matching-source bound. The three
fixtures are even covers, not candidate odd covers.

Normal execution and an isolated optimized execution of a physically
relocated copy, launched from `/` with spaces in its path, give identical
standard output, empty standard error and exit code zero. The program
uses only the standard library and keeps its checks active under `-O`.
These exact finite checks support the stated ordinary proofs and the
specified scalar separation; they do not replace an unrestricted
covering argument.
