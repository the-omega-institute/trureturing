[Index](../marked_head_profile.md) · [Synchronized matching](354-synchronized-prime-private-cofactor-matching.md) · [Shared capacities](359-synchronized-parent-capacity-allocation.md)

# A sharp mean partial matching bound on every prime-private tail

The local full-tail hypotheses of 354 imply more than the existence of a
rare full matching. On a uniform complete q-tail of original height H,
the maximum nonpure matching rank has mean at least

    E[rank] >= q-2+q^(1-H).                           (MP1)

The local construction in 354 attains equality. Selecting a partial
matching at every tail therefore removes the good-tail restriction from
359's shared capacity inequality. For odd q the resulting coefficient
has a positive height-independent part. This is a necessary constraint
on the same hypothetical extremal cover, not a nonexistence theorem.
No Lean verification or literature novelty is claimed.

## 1. First-use cylinders and the mean rank

Fix a cofactor state x in the actual prime-private cofactor region R_q
of 354. Put N=H-1 and use uniform measure on all q^N complete tails.
There are q-1 nonprime first-q roots. Each compatible original label
`q^e m` supplies one literal prefix at one root, of depth h=e-1 and
color m. Each root is covered at every tail. Numerical distinctness
ensures at most one label globally for each pair (color, depth).
The pure color m=1 has no depth-zero label on these roots.
The local argument only requires integer q>=2 and these prefix conditions.

At each root and tail choose its shallowest covering label. Resolve
same-depth ties by a fixed label order, chosen before seeing the tail
and independent of all future tail digits. This last condition matters:
an arbitrary tail-dependent deterministic tie rule need not give the
prefix events used below.

Let s_c(t) be the number of roots choosing nonpure color c, and s_*(t)
the number choosing the pure color. Let K(t) count the nonpure colors
used at least once. Keeping one chosen label of each nonpure color
gives a partial matching: different colors come from different roots,
since a root chose only one label. Consequently

    rank(t) >= K(t),
    s_*(t) + sum_c s_c(t) = q-1.                     (MP2)

For each nonpure color with s_c(t)>0, record its shallowest chosen
label. Its depth h and prefix determine an entire first-use cylinder
of measure q^(-h). Indeed, all selection decisions at depths at most h
are fixed on that cylinder. Deeper labels cannot displace a shallower
choice. A shallower use of c is therefore absent on the entire cylinder,
and the recorded depth-h use is present throughout it. The fixed tie
order makes this assertion valid also at equal depths.

The first-use cylinders for one color are disjoint; otherwise one
would extend another and the deeper one could not be a first use.
Let T be the total number of nonempty first-use cylinders, over all
nonpure colors. At a first use of depth h, any additional chosen label
of this color has depth j>h. There is at most one such label per depth.
Its conditional probability is at most q^(h-j), since its prefix is
either disjoint from or contained in the first-use cylinder. Hence

    E[s_c-1 | a first-use cylinder of depth h]
      <= sum_(j=h+1)^N q^(h-j)
       = (1-q^(h-N))/(q-1).                         (MP3)

Write epsilon=q^(-N). Multiplying MP3 by each cylinder's mass and
summing over first uses gives

    sum_c E[s_c] <= q/(q-1) E[K] - T epsilon/(q-1).

For the pure color, its unique possible label at each positive depth
has mass q^(-j). A chosen pure label is a subset of that cylinder, so

    E[s_*] <= sum_(j=1)^N q^(-j)
             = (1-epsilon)/(q-1).

Together with MP2 these imply the finite correction

    q E[K] >= q(q-2) + epsilon(1+T).                (MP4)

In particular E[K]>q-2. The integer-valued K is at most q-1, so some
tail has K=q-1. Its q-1 different colors each supply a first-use
cylinder, giving T>=q-1. Substituting this into MP4 yields

    E[rank] >= E[K] >= q-2+epsilon,

which proves MP1 without using the rare-full-matching estimate as
a premise. The argument includes H=1, with empty positive-depth sums.

## 2. Sharpness and the role of the tail law

The sharp construction from 354 gives q-2 roots distinct nonpure
depth-zero colors. Along a continuing path for the remaining root,
put those q-2 colors and the pure color on q-1 different children at
each depth. Continue through the last child, and put a new nonpure
color at the final leaf. Each color occurs at most once per depth.
Every root is covered at every tail. The rank is q-2 off the final
leaf and q-1 on that leaf, so its mean is exactly q-2+q^(1-H).
Thus q-2 is the best height-independent constant under these local
hypotheses. Additional global cover conditions are not asserted to
attain this local example.

Uniformity of the complete tail is essential. For example, take q=3,
N=2, roots 0 and 1, and use the pure color at root 0 on the depth-one
prefix t=0 mod 3 and at root 1 on the depth-two prefix t=0 mod 9.
Give root 0 fresh nonpure colors on t=1,2 mod 3. Give root 1 a fresh
nonpure color on each leaf t=1,...,8 mod 9. All these nonpure colors
can be different. The local hypotheses hold and every tail is covered,
but at t=0 the nonpure graph has rank zero. A point mass on that tail
cannot satisfy MP1. Its uniform-tail mean rank is 14/9.

Both examples are local prefix models, not whole integer covers.
They distinguish a statement about complete uniform tail averages
from one about arbitrary correlated or selected tail laws.

## 3. One shared capacity budget on all prime-private points

Use the same lexicographically minimal hypothetical odd cover as in
350, with original Haar law H, original prime-private sets Priv_q,
and original moduli forming a divisor ideal above one. In particular
every nonpure cofactor selected below is a genuine original parent.
Keep 359's notation

    pi_q = H(Priv_q),
    H_cov = integral (N_original-1) dH,
    alpha_q = q/(q-1) (1-q^(-H_q)).

At every point z in Priv_q, select any partial nonpure matching in
the graph at its actual cofactor and full tail; write k_q(z) for its
size. For example use the first-cover construction above, or a maximum
matching with a fixed tie rule. Define S_(q,e,m) and S_(q,m) as in 359
for the children and parents selected at these points. A parent is
selected at most once at each source, so the sets over e remain
disjoint and the source identity is now

    sum_m H(S_(q,m)) = integral_(Priv_q) k_q(z) dH(z).

The containing cylinders, prime exclusions, and pointwise 1/k allocation
of target capacity in CA5--CA11 do not require a full matching. Thus,
using exactly that one common target budget, they give

    sum_(q,m) beta_(q,m)/(alpha_(q,m) rho_(q,m))
      * H(S_(q,m)) <= H_cov.                       (MP5)

In particular beta_(q,m)/rho_(q,m)>=1/2 and
alpha_(q,m)<=alpha_q imply

    sum_q 1/(2 alpha_q)
      * integral_(Priv_q) k_q(z) dH(z) <= H_cov.    (MP6)

No independently allocated prime budgets are added here. MP5 uses
359's simultaneous ordered-parent capacity allocation, including its
inverse prime-multiplicity factor at every target point.

By 354, Priv_q is exactly `{a_q} x T_q x R_q`. Its conditional tail
law given the cofactor under original Haar is uniform on the entire
T_q. Choosing the first-cover partial matching, MP1 therefore gives

    sum_q (q-2+q^(1-H_q))/(2 alpha_q) * pi_q
      <= H_cov.                                    (MP7)

The same follows from maximum matchings. For every odd q the limiting
coefficient as H_q increases is `(q-2)(q-1)/(2q)>0`. In contrast to
an estimate restricted to a rare full-matching tail, MP7 weights the
whole original prime-private set. For smaller q, R_q is still not the
chronological pre-q survivor; this change does not identify those sets.

More generally let finite nonnegative measures lambda_q be supported
on Priv_q, with `lambda_q<=M_q H` and M_q>0. CA10 and the same partial
selections give

    sum_q 1/(2 M_q alpha_q)
      * integral_(Priv_q) k_q(z) d lambda_q(z) <= H_cov.
                                                        (MP8)

If each lambda_q is conditionally uniform over the complete q-tail
given the cofactor, choosing first-cover or maximum partial matchings
and integrating MP1 further gives

    sum_q (q-2+q^(1-H_q))/(2 alpha_q)
      * lambda_q(Priv_q)/M_q <= H_cov.              (MP9)

Without that conditional uniformity, MP8 remains valid for actual
selected matchings, but MP9 does not follow. A density upper bound
alone gives no uniform-tail rank lower bound. The distinct lambda_q
are compared to the same H with their explicit bounds; no simultaneous
attainment of separately optimized laws is assumed.

The scalar consequence MP7 does not retain the actual parent supports
or column heights. MP5, and CA10 with the new selection sets, retain
those sharper coefficients; separating prime from composite parents
also retains CA11's factors 1/2 and 1 respectively.

## 4. Exact checks and remaining scope

The [standalone checker](../frontier/mean_partial_matching.py) verifies
first-cover selections, whole first-use cylinders, their antichains,
MP3--MP4, and the mean bound using exact rational arithmetic. Maximum
matching by augmenting paths is independently compared with all
root-subset Hall deficiencies. It checks 16 sharp local models with
q in {2,3,5,7} and H in {1,2,3,4}, and the nonuniform-tail control.

For the actual distinct even covers of periods 12, 144 and 960 used
in 357, it compares every local active prefix graph with literal
membership in the full original AP family, keeping all tail digits.
Together the checks cover 47 local models, 950 full-tail states,
3,505 first-cover root choices, 130 first-use cylinders, 29,122 Hall
subsets, and 368 actual-root label comparisons.

The period-12 fixture has every required original cofactor parent and
tests MP5--MP9 on all prime-private points, including a nonconstant
source density `1+(x mod 3)/4` with M_q=2. The exact chains are:

| Source law | Coarse bound | Partial-rank integral | CA9 or CA10 charge | Allocated capacity | H_cov |
| --- | --- | --- | --- | --- | --- |
| Original Haar | 5/36 | 1/6 | 5/24 | 1/4 | 1/3 |
| Stated density, divided by M_q=2 | 23/288 | 29/288 | 35/288 | 1/4 | 1/3 |

The period-144 fixture lacks parents 8, 9 and 16; period 960 lacks
15, 32, 64, 96 and 192. They test the local full-tail rank theorem only,
not the full all-private budget. An absent parent is not replaced by
an invented AP. None of these even covers is an odd-cover example.

Normal execution and a physically relocated isolated optimized run
from `/`, with a script path containing spaces, produce identical
standard output and empty standard error, with exit code zero. The
checker uses only the standard library and keeps checks active under
`-O`. These finite checks do not replace the general prefix and
capacity proofs or establish a contradiction for unrestricted covers.
