[Index](../marked_head_profile.md) · [Actual resets](357-original-private-swaps-and-prime-reset-transport.md) · [Shared capacities](359-synchronized-parent-capacity-allocation.md) · [Mean matching](360-mean-partial-matching-without-tail-loss.md) · [Reserved prime overlap](361-prime-overlap-reservation-for-composite-parents.md)

# Common-source antichains constrain private mass and selected parents

All original prime-private regions are reset images of one common
no-prime carrier. On that carrier their simultaneous indicators are
determined by the intersection of the supports of the actual covering
composite labels. Keeping this joint structure gives a reverse bound on
the residual private masses and a sharper upper bound on the number of
selected prime parents. The latter improves 361's composite-source lower
bound while using the same selected matchings and target budget.

These are finite ordinary proofs. The actual examples below have even
moduli and test the source inequalities. A separate rational example only
distinguishes a stated scalar relaxation. No unrestricted odd-cover
contradiction, new prime-support exclusion, literature novelty, or Lean
verification is claimed.

## 1. One original carrier determines every prime pattern

Use the same hypothetical extremal distinct odd cover as in 361, with
original moduli D, prime support Lambda, full period Q, and original
uniform Haar law H. Every support prime is an original label; comparable
original classes are disjoint; and the whole period is covered. Normalize
the prime classes to `A_q=0 mod q` by one CRT translation. Write

    Z = {x : x belongs to no original prime class},
    P0 = H(Z) = product_(q in Lambda)(1-1/q),
    E(x) = {d composite in D : x in A_d},
    K(x) = intersection_(d in E(x)) supp(d).              (CS1)

For every x in Z, E(x) is nonempty by whole coverage and is an antichain
under numerical divisibility by comparable-class disjointness. Every
coordinate includes its full original prime-power height.

Let T_S reset only the first digits at the primes in S to zero, keeping
all tails and all other coordinates. A composite meeting S disappears,
because it is disjoint from a prime class now present. A composite whose
support avoids S is unchanged. Thus, exactly,

    E(T_S x) = {d in E(x) : supp(d) intersect S is empty},
    t_S(x) = #{d in E(x) : supp(d) intersect S is empty}.  (CS2)

Here E(T_S x) counts only composite labels; the prime labels present at
T_S x are exactly S. Put `C_S=product_(q in S)(q-1)` and let B_S be the
region whose exact set of present prime labels is S. The map
`T_S:Z -> B_S` has exactly C_S preimages at every target. Consequently,
for every real function g on B_S,

    integral_Z g(T_S x) dH(x) = C_S integral_(B_S) g dH. (CS3)

No independence of composite labels is used. The finite CRT fibres have
the stated size on the same full Q, without dropping tail coordinates.

Let `pi_d=H(Priv_d)` for every original label. For one prime q, T_q x is
private to A_q precisely when every active composite contains q. Hence

    H({x in Z:q in K(x)}) = (q-1) pi_q.                (CS4)

For |S|>=2, let V_S be 357's region whose complete set of covering
original labels is exactly the prime set S. Then

    C_S H(V_S)
      = H({x in Z : S meets supp(d) for every d in E(x)}).
                                                           (CS5)

The event in CS5 says that S hits every active support. It is generally
different from `S subset K(x)`. Equation CS2 also gives the full composite
incidence on each B_S through CS3, rather than treating the pattern
regions as independent allocations. PT11 keeps only the singleton
active families in the right side of CS5.

## 2. All private deficits come from the same residual antichains

For each composite d the exact no-prime incidence is

    cap_d = H(A_d intersect Z) = P0/phi(d).

The primes dividing d are already absent on A_d; the other prime roots
give the remaining CRT factors. Define

    delta_d = cap_d-pi_d,
    rho = P0-sum_(d composite) pi_d,
    v = sum_(d composite) cap_d-P0,
    epsilon_q = (q-1)pi_q-sum_(d composite:q|d) pi_d.   (CS6)

Here v is the aggregate excess on Z, not a stage v_P from 357; rho is
the no-prime nonprivate mass, not 359's cylinder factor rho_(q,m).

For an actual active antichain A, put
`lambda_A=H({x in Z:E(x)=A})`. Its singleton mass is
`lambda_{ {d} }=pi_d`. The nonsingleton masses satisfy simultaneously

    sum_(|A|>=2) lambda_A = rho,
    sum_(|A|>=2,d in A) lambda_A = delta_d,
    sum_(|A|>=2,q in intersection_(d in A) supp(d)) lambda_A
      = epsilon_q,
    sum_(|A|>=2) (|A|-1)lambda_A = v.                 (CS7)

These are one joint representation, not separate existence claims for
different q. At a nonsingleton point with q in K, at least two actual
labels contain q. Therefore

    0 <= epsilon_q <= rho,
    2 epsilon_q <= sum_(d composite:q|d) delta_d.      (CS8)

Equivalently the second inequality is

    2(q-1)pi_q <= sum_(d composite:q|d)(cap_d+pi_d).

PT6 supplies only `epsilon_q>=0`. The new reverse bounds limit how much
prime-private mass can remain after subtracting the private composite
sources, using the same residual region that supplies all of them.

CS7 also supports finite linear comparisons beyond one prime at a time.
For example, if fixed real coefficients satisfy

    sum_(d in A) a_d
      - sum_(q in intersection_(d in A) supp(d)) b_q >= c

for every allowed nonsingleton active antichain A, then multiplying by
lambda_A and adding gives

    sum_d a_d delta_d - sum_q b_q epsilon_q >= c rho. (CS9)

Restricting allowed antichains to the actual compatible original APs is
valid. Allowing every numerical antichain gives a relaxation. Neither
version's marginal feasibility alone certifies an AP realization, the
required residue compatibility across different antichains, or the
matching selections studied next.

The multiplicity boundary is exact:

    v-rho = sum_(|A|>=3)(|A|-2)lambda_A >= 0.          (CS10)

If rho=v, the residual consists only of pairs, although singleton
private regions may remain. There must be one nonnegative pair family
w_(d,e) on incomparable, actually intersecting original labels with

    sum_(d<e) w_(d,e)=v,
    sum_(e!=d) w_(d,e)=delta_d,
    sum_(d<e:q divides gcd(d,e)) w_(d,e)=epsilon_q.    (CS11)

Under this saturation, a compatible pair's residual mass equals its full
intersection with Z, of mass `P0/phi(lcm(d,e))`, since no triple
intersection remains in Z.
Saturation is a conditional boundary, not an assumed property. If D
contains pure powers p^a, q^b, r^c of three different primes, with
a,b,c>=2, intersecting those three classes with Z has exact mass
`P0/[phi(p^a)phi(q^b)phi(r^c)]`, by CRT, and gives

    v-rho >= P0/[phi(p^a)phi(q^b)phi(r^c)] > 0.       (CS12)

Thus that palette cannot attain the pair-only residual boundary.

## 3. Lift actual selected children back to the common source

Choose the same first-cover partial matching or maximum partial matching
on every Priv_q as in 360 and 361. At a source y in Priv_q, each selected
child `d=q^e m` has a specified nonzero first-q root, the same full q-tail
as y, and the same other coordinates. Move y to that actual root. The
resulting point x lies in Z and in the actual original child A_d.

For fixed q, a matching uses at most one child per root. Distinct source
points cannot lift to the same x, since T_q x recovers the source. Thus
the lifted selections have multiplicity at most one at each x. Each
fixed-child lift is a coordinate bijection preserving original H; its
total mass is exactly the integral of the selected-child count. No
normalization, changed tail law, or resampled target is involved.

Let

    F_q = {d in D : q|d and d/q^(v_q(d)) is prime},
    u_q = sum_(d in F_q) pi_d,
    Delta_q^F = sum_(d in F_q) delta_d,
    P_q = integral_(Priv_q) p_q(y) dH(y),
    Csel_q = integral_(Priv_q) c_q(y) dH(y),

where p_q and c_q count selected prime and composite parents. Every
child in F_q is composite and has a nontrivial prime cofactor. Divisor
closure provides all original parents in the hypothetical extremal cover.

A lifted prime-parent selection must satisfy both `q in K(x)` and
`E(x) intersect F_q nonempty`. On singleton active families its total
mass is at most u_q. On the residual region its mass is at most
epsilon_q, since q is common to every active support, and at most
Delta_q^F, by counting active F_q labels. These refer to the same lifted
set. Consequently,

    P_q <= u_q+min(epsilon_q,Delta_q^F),
    P_q <= U_q := min((s-1)pi_q,
                      u_q+min(epsilon_q,Delta_q^F)).  (CS13)

The first term in U_q is the distinct-prime-parent count already used
in 361. The part `u_q+Delta_q^F=sum_(d in F_q) cap_d` is the sum of
the old exact child-containing capacities from CA5. The additional part
has the useful equivalent form

    u_q+epsilon_q
      = (q-1)pi_q-sum_(d composite:q|d,d not in F_q) pi_d.
                                                           (CS14)

It subtracts actual private mass whose unique original covering child
cannot produce a prime parent. Its validity for P_q requires the
selection lift; CS8 alone concerns residual marginals and contains no
selection variable. Substituting an upper bound for epsilon_q in CS13
is valid after that link has been established, not a replacement for it.

Keep 361's original-height coefficients

    r_q=q-2+q^(1-H_q),
    alpha_q=q/(q-1)(1-q^(-H_q)).

The full-tail mean theorem gives `P_q+Csel_q>=r_q pi_q`. Applying CS13
and then the same composite-parent target allocation from 361 yields

    sum_q (r_q pi_q-U_q)_+/alpha_q
      <= sum_q Csel_q/alpha_q = X_comp
      <= B_comp <= M_comp <= h-J.                   (CS15)

Here h,J,M_comp are exactly PR1 and PR5 of 361, in particular

    M_comp = sum_(d composite) (1/d)
               [1-product_(q in Lambda:q not dividing d)(1-1/q)].

The selected sets in CS15 are the original ones used for the target
allocation. No second J or M_comp budget is added. Since
`U_q<=(s-1)pi_q`, the new lower bound is at least PR9's
`sum_q (r_q-(s-1))_+ pi_q/alpha_q`.

## 4. Strict source improvement on an actual even cover

The period-960 fixture from 357 has q=5, H_5=1, s=3 and

    pi_5=1/120, F_5={10},
    u_5=1/120, epsilon_5=1/960, Delta_5^F=7/120.

Thus CS13 gives

    U_5=3/320 < min((s-1)pi_5, sum_(d in F_5)cap_d)
              = min(1/60,1/15).

Because r_5=4, the unweighted composite-cofactor lower bound improves
from `1/60` to `23/960`. Literal maximum partial matching selection gives
`P_5=1/120` and `Csel_5=1/40`, satisfying the improved bound.

The selection link is a real extra condition on a scalar relaxation.
Keep this fixture's actual private and residual marginals, but introduce
formal counts `P_fake=C_fake=1/60`. They obey the two older upper bounds
on P and `P_fake+C_fake=4 pi_5`, while `P_fake>3/320`. They are not actual
selected sets. This only demonstrates that the scalar residual constraints
and those older count constraints do not themselves imply CS13; the
actual-child lift is needed.

The period-960 fixture lacks original parents 15, 32, 64, 96 and 192;
the period-144 fixture lacks 8, 9 and 16. In these fixtures a composite
numerical cofactor of an actual selected child need not be an original
parent. The checker reports these omissions and verifies the source
inequalities, not the full target-budget chain CS15. Prime parents in
F_q are present, so the prime-parent source estimate still applies.

## 5. Residual constraints also distinguish the scalar budgets

A second check separates CS8 from the specific mass and rank constraints
enumerated in 361. Use its six-prime, full-height-two divisor palette and
exactly its composite masses PR11. Keep pi_3, pi_5, pi_7 and pi_11; set

    pi_13=(1/12)sum_(d composite:13|d) pi_d
         =268201172110192/60941579989305015,
    pi_17=1/100.

The self-contained checker reconstructs these numbers from the closed
definitions. It verifies all the old individual and total regional mass
bounds, every PT6 inequality, PT12 with upper bound J, each PT13 charge
against its prime-label overlap baseline, and the exact PR8--PR10
budgets `R<=2J+M_comp`, `sum gamma_q pi_q<=M_comp`, and
`sum eta_q pi_q<=J+M_comp`. MP7 follows and is checked as well.

Nevertheless the q=17 reverse residual bound fails by the exact amount

    epsilon_17-(1/2)sum_(17|d)delta_d
      =48194175100436/422451039735725 > 0.            (CS16)

This is only a nonimplication between the stated scalar inequalities.
There are no supplied residues, common active antichains, or matching
selections. The independent known nine-prime condition already excludes
six-prime odd covers. Also this profile has rho=v although its palette
contains 9,25,49, so CS12 supplies another obstruction to realization.
Neither fact is a new prime-support result, nor does either invalidate
361's expressly limited scalar separation.

## 6. Exact checks and remaining obligation

The [standalone standard-library checker](../frontier/common_source_antichain_capacity.py)
enumerates the complete even-cover periods 12, 144 and 960. It checks
the common active antichains, every reset subset on every no-prime point,
the full-height fibre sizes, exact prime-only and composite incidences,
the shared residual identities and pair boundary, and literal maximum
partial matching lifts. The three no-prime carriers have 4, 48 and 256
points, giving 2,256 reset point-pattern comparisons. All three fixtures
have rho=v; their actual pair masses are checked against full CRT.
A separate local pure-power intersection on period 33,075 tests the
positive triple boundary while retaining the original 3-height three;
that local family is explicitly not a whole cover.

Normal execution and a physically relocated isolated optimized run from
`/`, with spaces in the script path, have identical standard output,
empty standard error and exit code zero. All checks use exact rational
arithmetic and remain active under `-O`. The program has no sibling
imports or input-file dependency.

Whole coverage is used to make every active family on Z nonempty and to
identify rho and v with nonnegative residual mass and excess. Original
prime labels and their disjointness from their multiples give the reset
identities. Full-tail coverage and numerical distinctness supply 360's
mean rank. Divisor closure is needed for the original-parent target
budget in CS15, not for the common-source identities or prime-parent
source estimate on the fixtures.

The unresolved step is to prove these common antichain and selected-source
constraints incompatible for every allowed odd palette and all original
heights. No such uniform dual certificate or covering contradiction is
provided here.
