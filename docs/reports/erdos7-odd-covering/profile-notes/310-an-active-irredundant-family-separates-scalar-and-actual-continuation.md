[Index](../marked_head_profile.md) · [Original scalar obstruction](304-an-actual-star-blocks-a-universal-scalar-restart-at19.md) · [Joint-load transfer](../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md)

# An irredundant actual family escapes the scalar route at arbitrary heights

For the new primes q=23,...,101 and arbitrary positive finite heights Hq,
there is an actual family whose every forbidden class has a private integer
and whose every new mixed class removes a point of the preceding survivor
set. All probabilities on its final survivors still have an old19 marginal
with Gamma19>53.71877660361228481616353125, the unchanged actual-star bound
of304. Nevertheless explicit family-aware kernels continue through all18
new primes with no killed mass and with second-moment multiplier less than
3.097096558845, uniformly in all the new heights.

Taking every Hq=8 gives1855 distinct odd original moduli. Even T6 with those
actual finite-height coefficients has incoming capacity below53.112508689463
through101, so it cannot certify this family from any valid scalar seed.
This removes the explanation that the successful actual kernels merely
exploit height1. The height1 capacity is instead57.72791655030322..., which
is above the retained lower bound; no finite-coefficient impossibility is
claimed for that height1 case.

This is one explicit noncovering family and a specialization of existing
transfer and capacity formulas. It is not a universal improvement, not the
saturated J source, and not a Lean result or a solution of unrestricted #7.

## Original classes, actual support and irredundancy

Use exactly the old304 primes P={3,5,7,11,13,17,19}, heights H3=31 and Hp=8
otherwise. At any prime define the pure cylinder F_(p,e) by residue
p^(e-1)-1 and the side cylinder C_(p,e) by residue2p^(e-1)-1, modulo p^e.
All F and C cylinders at one prime are pairwise disjoint. Their first
e-1 digits are p-1, followed respectively by0 or1.

Retain precisely the following1567 old classes:

    F_(p,e), p in P, 1<=e<=Hp;
    C_(3,i) times C_(p,j), p>3, 1<=i<=31, 1<=j<=8.

The other old304 classes had zero residues and were already contained in
pure zero classes. Removing them leaves the same old support R and period
Q0. The complete DIVISOR TEST inventory defining Gamma_Q0 is unchanged;
removing a forbidden class does not remove its independent test label.

At each new prime q retain these2Hq classes:

    F_(q,e);
    {x3=1 modulo3} times C_(q,e), 1<=e<=Hq.

Every new mixed class has original modulus3*q^e and its unique CRT residue.
All moduli are nontrivial odd and distinct. The full period is
Q=Q0 product_q q^Hq. The CRT point x3=1 and xp=2 at every other prime is an
explicit complete survivor, because root2 is disjoint from all F and C
cylinders at each prime greater than3.

Each class has the following private point. Unspecified coordinates are2,
and the default ternary coordinate is-1 modulo3^31.

| Original class | Coordinates replacing those defaults |
|---|---|
| old F_(p,e) | xp=p^(e-1)-1 |
| old C_(3,i) times C_(p,j) | x3=2*3^(i-1)-1, xp=2*p^(j-1)-1 |
| new F_(q,e) | xq=q^(e-1)-1 |
| new {x3=1 mod3} times C_(q,e) | x3=1, xq=2*q^(e-1)-1 |

The pure ternary class replaces the default ternary coordinate in the first
row. Pairwise disjointness of F and C cylinders and all clean default roots
show that each point lies in exactly its designated original class. This
also proves that every new mixed class actually removes points surviving
all earlier prime steps. In the Hq=8 instance, the companion constructs all
1855 literal CRT integers and checks each against all1855 original classes.

## The unchanged actual lower bound

Let Sp be the complement of the pure F union, Cp the side C union, and
Dp=Sp minus Cp. The unchanged old star support is

    R={-1 modulo3^31} times product_(p>3) Sp
         disjoint-union C3 times product_(p>3) Dp.

The retained304 potential certificate proves Gamma_Q0(nu)>L for EVERY
probability nu on R, where L=53.71877660361228481616353125. Every probability
on the final enlarged survivor set has old marginal on R. Consequently its
old marginal obeys that same bound, even if it was chosen knowing all later
labels. This uses the actual support and its original complete tests; no
relaxed moment witness or independent choice of a maximizing load is used.
The new companion consumes304's stored exact L and stored full-height
capacity. It does not recompute the old potential tables or old capacities.

## Exact actual fibres at every finite height

Let A={x3=1 modulo3}, a literal band of the old support, and fix a new q and
its actual height H. Define

    c=sum_(e=1..H) q^-e=(1-q^-H)/(q-1),
    Aq(H)=sum_(e=1..H) (2e+1)q^-e.

The pure F union and side C union are disjoint and each has Haar mass c.
The actual pure-survivor base Uq is uniform on Sq with Haar density1/(1-c).
Its actual mixed fraction is

    alpha_q(x)=1_A(x)*c/(1-c)<=1/(q-2).

Choose delta_q=1/(q-2). Since alpha<=delta, the prescribed clipped kernel
restricts Uq to the actual good set and normalizes that fibre. Relative to
full Haar it is exactly

    Kq(x,dy)=1_Sq(y)/(1-c) dy,               x outside A;
    Kq(x,dy)=1_(Sq minus Cq)(y)/(1-2c) dy,   x in A.

Each row has mass1 and lies on actual survivors. Thus Kq^-=Kq and every
assigned killed charge beta_q=(alpha_q-delta_q)_+/(1-delta_q) is zero.
The mixed class is nonetheless active: if the incoming law gives A positive
mass, its actual mixed union has positive mean fraction nu(A)c/(1-c).
The normalized kernel moves mass off this nonempty forbidden set.

At any current depth1<=t<=H, every prefix has Haar mass q^-t. The uniform
good density therefore gives an upper cap. A prefix2 modulo q^t is wholly
inside the clean first root2, hence attains that cap. The exact prefix
maximum is

    M_t(x)=q^-t/(1-c-1_A(x)c)
           =q^-t[1/(1-c)+1_A(x)c/((1-c)(1-2c))].       (AH1)

This uses the actual same fibre that defines alpha. It is not a cap
assigned independently of the forbidden labels.

## Family-aware transfer and the uniform height limit

For the actual positive incoming measure sigma, apply the existing W1
weighted-prefix transfer at all current depths and then subadditivity of
Gamma on positive measures. Formula(AH1) gives

    Gamma_new(sigma Kq)
      <= Gamma_old(sigma)
          +Aq(H)[Gamma_old(sigma)/(1-c)
                 +c Gamma_old(1_A sigma)/((1-c)(1-2c))]
      <= [1+Aq(H)/(1-2c)] Gamma_old(sigma).            (AH2)

Each current exponent layer keeps its OWN complete old test load, with its
original inherited residues. W1 bounds their weighted integrals on the
same actual measure; it does not set those loads equal or require them to
have a common maximizing test. The last inequality uses1_A sigma<=sigma.

The old marginal is preserved at each step, and A remains the same actual
ternary band. No intermediate conditioning or artificial coupling is
inserted. Every finite incoming second moment can therefore be continued
through this family without a survival denominator loss.

The complete geometric sums give

    c<1/(q-1),
    Aq(H)<(3q-1)/(q-1)^2,

and hence, uniformly at every positive finite height,

    1+Aq(H)/(1-2c)
       < 1+(3q-1)/[(q-1)(q-3)].                      (AH3)

Across all18 primes, the product of the right sides is
3.097096558844337...<3.097096558845. For Hq=8 the finite product is
3.097096558803898... . This is a uniform exponent-height bound on this
fixed finite prime horizon; no infinite-prime assertion follows.

When H=1, c=1/q and Aq=3/q. The two coefficients in(AH2) are exactly
3/(q-1) and3/[(q-1)(q-2)], giving a height1 whole-horizon multiplier of
2.960570582014057... . Both thresholds1/(q-2) and1/(q-1) are at least
the actual alpha=1_A/(q-1), so they produce identical clipped kernels.

## Actual finite-height scalar capacity

For comparison, retain the existing T6 recurrence but use its actual
finite-height coefficients

    a_q=Aq(H), b_q=c_q(H)^2/4,
    R_q(f,delta)=f[1+a_q/(1-delta)]
                  /[1-b_q f/(delta(1-delta))].

The same304 inverse-capacity algebra applies to any positive a_q,b_q.
For a required output G its incoming capacity is

    C_q(G)=G/[1+a_q+2G b_q+2 sqrt(G b_q(a_q+G b_q))].

At the final prime101 the strict feasible input endpoint is1/c_101(H)^2.
Propagating backwards through the preceding17 primes with exact directed
integer-square radical enclosures gives

| Common new height | Through101 input-capacity enclosure, displayed |
|---|---:|
|1|57.72791655030322...|
|8|53.11250868946259...|
|full-height304 coefficients, reused|53.11250868851412...|

Both newly computed intervals have width less than10^-35. Thus at height8
the capacity is below53.112508689463<L, excluding every valid scalar seed
for this actual old support even after using its finite heights. At height1
it exceeds L; that weaker instance does not establish this finite-height
obstruction. The capacity comparison and the successful(AH2) kernels refer
to different information interfaces on the same actual original family.

## Exact support mass and checker scope

For an independent positivity check, use the old sums c_p=sum_(e<=Hp)p^-e.
The old Haar survivor density and the active-band density are

    r=3^-31 product_(p>3)(1-c_p)+c_3 product_(p>3)(1-2c_p),
    a=(1/3) product_(p>3)(1-2c_p).

The enlarged actual Haar survivor density is exactly

    (r-a) product_newq(1-c_q)+a product_newq(1-2c_q)>0.

For Hq=8 it is0.047066078271868324... . All original classes and every
private integer are retained by the certificate. Exact disjoint F/C
counts, the normalized three-piece fibre partition, and literal clean
prefixes verify(AH1) without enumerating q^H residues.

The [standard-library helper](../frontier/active_irredundant_star_all_heights.py) supports
--base, --write, --check, an optional --output for isolated staging, and
--later-height(default8). Its default [certificate](../certificates/source_norms/active_irredundant_star_all_heights.json) retains the construction. All
certificate reads and writes use the unchanged canonical IO.

The Hq=8 check verifies1855 legal original classes and their exact lcm,
one complete survivor, 3,441,025 literal private-point membership tests,
actual F/C disjointness, all exact prefix maxima in36 fibre states,
H1 kernel/coefficient degeneration, both new finite-height capacity
intervals and the finite and complete-height multipliers. It performs no
LP, arbitrary-family scan or old304 potential replay. These calculations
verify this explicit construction; the preceding arguments supply its
arbitrary-height interpretation and the scope of the reused theorems.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/active_irredundant_star_all_heights.py --check
```
