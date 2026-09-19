[Index](../../marked_head_profile.md) · [Joint actual source](244-three-complete-j-heads-share-raw-survivor-and-marked-deletion.md) · [J pure-five caps](../129-192/130-the-whole-j-face-forces-source-anti-alignment.md) · [Complete seven bridge](219-one-late-source-split-controls-complete-saturated-j-heads.md)

# Two retained original tests sharpen the complete J heads

On both entire actual saturated J faces, retaining the two independently
chosen original labels135 and125 inside the same actual raw/survivor
partition gives these stronger complete bounds:

| Original function | Previous complete upper | New complete upper |
| --- | ---: | ---: |
| AP13 | 0.196328294280874964726631393... | 0.194906849653694321563546053... |
| 0 | 6.009969384412894581015263297... | 5.694565687831699609719876961... |
| 16 | 4.802983468473917584278889581... | 4.550682696982637133600824798... |

Each function retains all6,250,000 original containing choices, the whole
late-split interval and the complete exponent tails. The minimal new
model has3306 variables,6354 inequalities and18 equalities. It keeps all
old244 marked deletion constraints and adds no extra deletion rows.

The exact new complete bounds, in the displayed order, are

    225629041830357889/1157625000000000000,
    1791636462292567187058853909283901779303/314622143374512991758741000000000000000,
    165366610325299466178084118303859134302751/36338857559756250548134585500000000000000,

All three bounds strictly improve their preceding complete244 bounds.
These are source inequalities on the same domain; the separate cost
optimizers are not asserted to be simultaneously realized.

## One actual four-state observation

Keep244's actual raw measure Lambda, survivor mu, retained density w and
original25-rectangle/16-mask partition C_(c,s,m). Let the independently
chosen original135 and125 test cylinders define

    S0=J135 minus J125, S1=J125 minus J135,
    S2=J135 intersect J125,
    S3=complement of J135 union J125.

For i=0,1,2 define u_i=Lambda restricted to S_i and v_i=mu restricted
to S_i, measured on each original atom C_(c,s,m). The fourth state is
implicit. These nonnegative actual measures satisfy, on each atom,

    sum_i u_i<=X, sum_i v_i<=Y,
    v_i<=w*u_i,
    Y-sum_i v_i<=w*(X-sum_i u_i).                    (JR1)

The last line bounds the actual complement. Independent marginal choices
would not justify it; here all states come from the same actual partition.
The old244 raw, survivor, coarse deletion and ten marked residual
constraints remain unchanged. No extra deletion credit is taken outside
the objective, and neither deletion measure is required to split across
the new states in this containing model.

There are1200 additional raw-state masses,1200 survivor-state masses and
30 independent residue-profile weights. Together with244's876 variables,
this gives3306 nonnegative variables. The common late coordinate remains

    theta=1/135+(1/270)*x, 0<=x<=1.

Thus every original source uses one actual theta for all old and new states.

## J-specific profiles and complete survivor caps

Use219's normalized deep-ternary table p_(c,s) and absolute
descendant-five table E_(c,s). They have different meanings.

An original135 cylinder fixes one ternary parent cell and one first-five
slot. Restricting219's depth3 ternary profile to that slot gives the raw
bound p_(c,s)/27. Introduce a separate25-element simplex lambda135 and
impose

    sum_(c,s)lambda135(c,s)=1,
    sum_m(u0+u2)(c,s,m)<=lambda135(c,s)*p_(c,s)/27. (JR2)

For an actual positive-source event, its own parent and slot give its
point profile. In particular, this uses the normalized p table; replacing
it by the absolute raw cap would incorrectly insert a second ternary
mass factor.

An original125=5^3 cylinder has one first-five slot common to every
ternary cell. The absolute descendant table supplies its raw cap
E_(c,s)/125. Its independent five-element simplex obeys

    sum_s lambda125(s)=1,
    sum_m(u1+u2)(c,s,m)<=lambda125(s)*E_(c,s)/125.  (JR3)

An absent or source-null event has zero marked raw and survivor masses
and may use any point profile. Relaxing these actual point profiles to
mixtures retains every original configuration without declaring arbitrary
mixtures realizable. The two original residues remain independent.

Raw Haar domination gives the complete survivor135 cap1/135. For125,
130(J8) gives the J-specific pure-five inequality

    mu(F)<= (13/30)*5^-b for every original depth b>=2.

At b=3 this yields13/3750. Hence

    sum(v0+v2)<=1/135,
    sum(v1+v2)<=13/3750.                            (JR4)

The K value2/625 is not a J input. No K-specific forced27 location or
K numerical source bound is used.

## Every intersection and the complement remain included

For independently chosen compatible original cylinders,
Lambda(J_a intersect J_b)<=1/lcm(a,b); incompatible intersections are
empty. Applied to the old selected labels, the raw intersection caps have
these denominators:

| New label |25|27|75|81|
| --- | ---: | ---: | ---: | ---: |
|135|675|135|675|405|
|125|125|3375|375|10125|

Use u0+u2 for the first row and u1+u2 for the second, summing over old
masks containing the corresponding original bit. The common new event
also satisfies

    sum u2<=1/3375.                                 (JR5)

These conditions add no unproved residue compatibility. Both nested and
disjoint original27/81 alternatives remain inside the same containing
model; neither branch is selected as if it were exhaustive by itself.

Every actual mass coordinate and profile weight is at most1, as is the
normalized late coordinate. Independent unit upper rows therefore permit
exact repair of proposed duals. With244's old587 inequalities and16
equalities, the full inventory is

    inequalities =587+50+2400+2+8+1+3306=6354,
    equalities =16+2=18.                            (JR6)

Here50 counts the new raw profiles,2400 counts the marked/complement
links,2 the survivor caps,8 the old/new intersections and1 the new/new
intersection. No additional product or marked-deletion condition is imposed.

## The exact two-indicator increment and complete tails

For thresholds t>=2, let V=B+popcount(m) with original shallow head
B=1+I3+I9+I5+I15+I45. On S0,S1,S2 the newly retained indicator counts
are respectively n_i=1,1,2. The exact additional retained integral is

    sum_i [u_i*(g_t(V+n_i)-g_t(V))
           +v_i*((V+n_i-t)_+-(V-t)_+)].             (JR7)

The common state receives the actual two-indicator increment, which is
not replaced by twice a single increment. The same raw source carries g,
and the same actual survivor carries the hinge. At threshold1 the old
head B receives no newly retained labels and no term(JR7) is added.

The function g is244's complete retained seven bridge for the four original
projections21,35,63,105, including every unit7 power. The new finite retained
load is at most12; the defining bridge formula applies at every integer
load and has constant raw increment once V>=t. No exponent-height cutoff
is introduced.

The original135 and125 labels are two distinct assigned terms of the
complete remainder2471/81000. The mixed label135 has assigned cap1/135;
the pure-five label125 has assigned cap13/3750. Therefore

    Rpair=2471/81000-1/135-13/3750
         =7951/405000>0.                            (JR8)

For positive hinge coefficients a_t, add(JR7) to244's actual-survivor/raw
objective and retain the exact complete external payment

    a1*(53/600+1/28)
       +sum_(t>=2)a_t*(7951/405000+1/28).           (JR9)

This removes designated summands from a known nonnegative cap series. It
does not subtract upper estimates from unknown actual mass. Each selected
old label is retained or paid once. Every omitted old and positive-seven
label, at every exponent height, remains in its complete tail.

## Exact duals and exhaustive original choices

Each target retains12,500 original shallow layouts, ten independent21/35
choices and50 independent63/105 choices, or6,250,000 containing choices.
The new135/125 residues vary within their independent profile simplexes
at every such choice. The same finite LP includes the entire theta interval.

Complete219 affine bounds provide the first two pruning stages. Their
maximum-of-minimum uses both endpoints and any strict interior crossing
at a common theta. A preceding244 dual is reused only when its regenerated
whole objective hash is identical, and all its876 columns are checked.
Such a branch is pruned only if that complete bound is at most the current
certified scan maximum. Remaining branches use the new3306-column dual.

For Az<=b, Ez=e and z>=0, a valid rational dual satisfies

    y>=0,  A^T*y+E^T*h>=objective,                   (JR10)

with unrestricted equality prices h. Its exact value b^T*y+e^T*h bounds
the retained integral; adding(JR9) supplies the complete branch bound.
Numerical optimization only proposes prices. The canonical verifier clears
positive denominators and checks every rational column and signed value
with integers. Unit-row repairs are checked by the same test.

All pruned branches have a certified upper no larger than the final scan
maximum. The maximizing record identifies a branch of the containing upper
calculation; it does not assert that an actual family attains its LP optimum.
The three original functions retain their own independent test labels and
unchanged all-load hinge expansions, including their exact constant-mass
terms. No simultaneous optimizer is assumed across different costs.

## Complete scan counts and lossless certificate

| Target | Two-projection branches | Pruned there | Four-projection branches | Pruned there | Reused244 dual | New LP branches |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| AP13 | 125000 | 124994 | 300 | 296 | 3 | 1 |
| 0 | 125000 | 106492 | 925400 | 925233 | 0 | 167 |
| 16 | 125000 | 106128 | 943600 | 943424 | 0 | 176 |

For every row,50 times the pruned-two count plus the four-projection
count equals6,250,000; the last three columns partition all four-projection
branches. Across the three targets, all18,750,000 containing choices are
covered. The bank contains344 distinct exact duals, every one consumed,
and all1137264 rational column inequalities are checked. The old affine
compiler additionally checks42 unscaled endpoint and common-crossing values.

The rational-table/run-length codec is the existing lossless serialization
infrastructure: it retains every inequality price, unrestricted equality
price and exact signed objective value. The producer checks exact decoded
bank equality, and the standard-library canonical verifier decodes before
checking the complete model and every branch. It supplies no additional
source estimate or K-specific mathematical premise.

## Actual-source transport and remaining boundary

The same canonical relabelling as130/219/244 transports the whole source,
survivor, old masks, new four-state partition and both new profiles to the
second J orientation and every admissible source-cell permutation. Finite
additional cylinder observations135/125 also pass through the existing
labelwise diagonal construction. The complete geometric tail bounds remain
uniform, so the inherited limiting-face interpretation is unchanged.

The [helper](../../frontier/j-geometry/j_face_retained135125_heads.py),
[certificate](../../certificates/source_norms/j-geometry/j_face_retained135125_heads.json)
and [optional proposal generator](../../frontier/retained-transport/propose_j_face_retained135125_heads.py)
retain the exact complete model, original functions, branch partitions,
rational duals and all tails.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_face_retained135125_heads.py --check
```

These are ordinary complete source inequalities on both saturated actual
J faces. They do not supply an off-face neighborhood, a new full52-cost
numerator/denominator ratio, Lean verification or an unrestricted Erdos7
resolution.
