[Index](../marked_head_profile.md) · [Whole J source](130-the-whole-j-face-forces-source-anti-alignment.md) · [One J source split](219-one-late-source-split-controls-complete-saturated-j-heads.md) · [Complete factorial partition](128-the-complete-factorial-tail-retains-its-head-off-the-face.md) · [Shared square](199-one-six-label-head-controls-the-square-and-both-complete-crosses.md)

# One original J head controls complete square and factorial moments

On both whole actual saturated J faces, every complete independently labelled
original357 test A satisfies

    integral A^2 dmu <=371/80=4.6375,
    integral Phi5(A)dmu <=6353/7200=0.882361111111...,
    Phi5(v)=(v-5)_+*(v-4)/2.

These integrals use the same unnormalized actual survivor measure mu, whose
mass is3/20. The existing mean bound integral A dmu<=16/25 remains available.
One original six-label layout controls the square head and both complete
crosses before maximization. The factorial inequality likewise retains its
own single original head. Every omitted exponent and pair tail is included.
This supplies general moments for later J consumers; no complete52-cost
ratio, off-face bound, global continuation or unrestricted result follows
from these moments alone.

## Actual J source and its single common parameter

Use219's canonical first J orientation, with ROOT=(0,0,1,1,1), cells
(L,M,N)=(2,3,4), and slots(P,A,B,Q,H). Its normalized deep-ternary table p,
absolute descendant-five table E and retained density w are distinct:

    eta=(1/18,1/9,1/9,1/9,1/9),
    p(0,.)=p(1,.)=(0,1/5,1/5,3/20,1/5),
    p(L,.)=(0,0,0,1/10,1/5),
    p(M,.)=p(N,.)=(0,0,1/5,1/10,1/5),
    E(c,s)=eta_c*1_(s!=P)*1_(not(c>=2,s=A))*1_(not(c=L,s=B)),
    w(c,s)=1-[1_(c<2)+1_(c=1)+1_(s=H)+1_(c>=2,s=H)]/5.

The absolute source cap table is eta_c*p(c,s), with theta removed from(M,B)
and1/90-theta removed from(N,B), where

    1/135<=theta<=1/90.

The two root0 cell budgets are1/24,1/12, and the combined root1 budget is1/8.
Their total is the actual source mass1/4. The eight positive root1 caps sum
to1/8+1/120, and each is at least1/90 on the entire interval. Thus, for every
fixed nonnegative25-entry coefficient z,219's exact relaxed source LP is

    U_theta(z)=sum cap_theta(c,s)*z(c,s)
               -(1/120)*min_(positive root1 entries)z(c,s).

Fill the cap vector and remove1/120 at a least-priced supported entry to
obtain a feasible optimizer; the matching lower price proves its LP value.
This argument bounds the actual source and does not assert that the relaxed
optimizer is realizable. U_theta(z) is affine in theta for fixed z. The
normalized table p used for deep cylinders does not include an additional
factor eta; using absolute source caps there would undercount the cylinders.

For any nonnegative head H, retain both J-specific deletion corrections:

    C3(H)=sum_s q_s*min(H(0,s),H(1,s))/90,
    q=(0,1/5,1/5,3/20,1/5),
    C5(H)=sum_c eta_c*(1+1_(c>=2))*min_s H(c,s)/100.

At saturation the actual deleted measure equals the sum of virtual
deletions. These two distinct complete forbidden families are also distinct
from the shallow families already represented in w. Therefore219 proves

    integral H dmu <=U_theta(wH)-C3(H)-C5(H).

The pure3 correction uses its exact slot marginal q/90 and permits either
root0 cell. No K-specific forced27 location is assumed.

## The complete old-tail operator and raw row

Retain the original head B=1+I3+I9+I5+I15+I45, so1<=B<=6. Write the rest
of the complete test as O+Z, where O contains zero-seven exponent pairs
outside{0,1,2} times{0,1}, and Z contains every positive-seven label.
For nonnegative25-entry z define

    T(z)=max_c sum_s p(c,s)z(c,s)/18
         +[max_s sum_c E(c,s)z(c,s)
           +max_(r,s)sum_(ROOT(c)=r)E(c,s)z(c,s)
           +max_(c,s)E(c,s)z(c,s)]/20
         +max_(c,s)z(c,s)/72.

These are the complete pure3, pure5, root5, cell5 and mixed-tail cap sums.
Each original label retains its independent residue. Since mu<=w*Lambda,
the old cross obeys integral B*O dmu<=T(wB).

Let M0,...,M5 be the six finite mask families: the whole grid, either root,
each cell, each slot, every root-slot rectangle, and every cell-slot
rectangle. Define the complete raw old-label row

    R_theta(z)=sum_(i=0,...,5) max_(m in Mi)U_theta(z*m)+T(z).

The six terms account for1,3,9,5,15,45 in each independent positive-seven
old-cofactor test. T includes every remaining old exponent. Positive-seven
depths have complete relative cap sum1/5, so

    integral B*Z dmu <=R_theta(B)/5.

These are bounds on the same actual source. Independent LP maxima only
enlarge the upper bound; they do not substitute different laws into the
original integral.

## Complete LCM tail pairs and every diagonal

Source130 supplies the four surviving pure-family coefficients

    (pure3,pure5,root5,cell5)=(11/20,13/30,1/3,1/9).

Their starting depths are3,2,2,2. The mixed old tail a>=3,b>=1 has coefficient1
against3^-a*5^-b. In particular the pure5 coefficient13/30 already includes
the complete J pure3deep deletion; it is valid for arbitrary original test
residues. The complete old-tail diagonal is

    Odiag=(11/20)/18+(13/30+1/3+1/9)/20+1/72=53/600.

The raw-source coefficients in128's notation are

    (s,N3,N9,D,h,h1,max eta)=(1/4,1/8,1/12,3/4,1/2,1/3,1/9).

The root1 total is1/8, the larger root0 cell has mass1/12, and every root1
cell has raw mass at most1/18, so these N3,N9 bounds cover the whole J domain.
The remaining coefficients follow from max d=3/4 and the fixed pure3 masses.
Using their complete geometric sums gives

    Lraw=sum_(a,b>=0)Cr(a,b)=3/4,
    Qraw=sum_(a,b>=0)(2a+1)(2b+1)Cr(a,b)=57/16.

These are sums of assigned cylinder caps. They are not obtained by
subtracting unknown moments. The positive-seven diagonal is Zdiag=Lraw/5.

For completeness, count old-tail labels in each exponent rectangle by

    N_O(a,b)=(a+1)(b+1)-(min(a,2)+1)*(min(b,1)+1).

Taking its two finite differences after squaring counts ordered O-by-O
pairs at each LCM. Applying the same differences to N_O(a,b)*(a+1)*(b+1)
counts O-by-all-old pairs. Outside the head the resulting multiplicities are

| Region | kOO | kOA |
| --- | --- | --- |
| a>=3,b<=1 | (2a-5)(2b+1) | (2a-2)(2b+1) |
| a<=2,b>=2 | (2a+1)(2b-3) | (2a+1)(2b-1) |
| a>=3,b>=2 | (2a+1)(2b+1)-12 | (2a+1)(2b+1)-6 |

Inside the head both counts vanish. With C0 the surviving old-tail cap and
Cr the raw cap, the complete unordered distinct-pair partition is

    POO=(1/2)sum_O(kOO-1)*C0,
    POZ=(1/5)sum_O kOA*Cr,
    PZZ=(1/2)[(4/15)*Qraw-Lraw/5],
    Ptail=POO+POZ+PZZ=5089/7200.

Here4/15 is the complete ordered positive-seven depth-pair factor, and the
subtracted assigned subseries Lraw/5 removes exactly its diagonal. Each
remaining subseries is nonnegative. The weighted geometric identities in128
evaluate all regions, including the full infinite complement. Restoring
both diagonals gives the complete ordered tail square

    integral(O+Z)^2 dmu <=2Ptail+Odiag+Zdiag=5947/3600.

The helper also counts original label pairs directly in an8-by8 exponent
prefix and matches the LCM multiplicities at every exponent pair. The
finite-difference identities and geometric sums above supply the all-height
argument; finite enumeration alone does not supply that extension.

## One head for each complete moment

For each of the12500 original independent layouts ell, combine before
maximizing:

    Qhead(ell,theta)=U_theta(wB^2)-C3(B^2)-C5(B^2)
                     +2T(wB)+(2/5)R_theta(B).

This is exactly the B^2+2BO+2BZ partition with valid upper bounds on its
three terms. The same B is used in each term.

For the factorial moment put h=(B-4)_+. The pointwise inequality from128 is

    Phi5(B+O+Z)<=Phi5(B)+h*(O+Z)+(O+Z)*(O+Z-1)/2.

Let G=I3*I9*I5*I15. It is a fixed cell-slot rectangle when
r3=ROOT(c9)=r15 and s5=s15, and is empty otherwise. The elementary indicator
inequality h<=I45+G keeps both original rectangles, including when they
coincide. Thus a valid complete factorial head is

    Fhead(ell,theta)=U_theta(w*Phi5(B))-C3(Phi5(B))-C5(Phi5(B))
                     +T(wh)+[R_theta(I45)+R_theta(G)]/5.

The total factorial bound adds Ptail, the unordered distinct omitted pairs.
The total square adds the ordered tail square, including its diagonals.
These two tail quantities are not interchangeable.

## The whole theta interval and both J orientations

For each fixed layout, U_theta at any fixed coefficient is affine. Each
finite mask maximum in R_theta is a maximum of affine functions, hence
convex. T and both deletion corrections are independent of theta.
Consequently Qhead and Fhead are convex functions of this one common theta.
For theta=(1-lambda)*LO+lambda*HI, either complete bound is at most the
corresponding convex combination of its endpoint values, hence at most the
larger endpoint. This argument concerns each displayed complete bound; it
does not apply endpoint maximization to a minimum of two alternative bounds.

All12500 layouts are checked at both endpoints, giving25000 exact component
records. The maxima are

    max Qhead=2687/900,
    max Fhead=79/450.

Adding5947/3600 and5089/7200 respectively gives371/80 and6353/7200. Both
comparison maxima occur at layout(1,4,2,1,2,4,2), theta=1/90. No actual
family attaining these relaxed bounds is asserted.

As in219, root1 permutations transport every ordered distinct choice of the
first beta and largest late cells. Exchanging root0 cells transports the
second J face together with its source, density, corrections and all
original tests. The complete layout inventory is invariant under these
permutations. Thus no other actual J orientation or independent-label choice
is omitted. Finite complete tests pass to infinite heights by monotone
convergence; all cap sums, including their polynomial depth weights, converge.
For actual limiting saturated configurations the same uniform complete
weighted tails justify the corresponding moment limsup interpretation.

## Exact certificate and consumer boundary

The [helper](../frontier/j_face_shared_square_factorial.py) and
[certificate](../certificates/source_norms/j_face_shared_square_factorial.json)
bind219's entire source dependency closure, the exact J geometry and the
complete128 tail identities. They retain all exact tail components, complete
endpoint-record digests and every maximizing witness. All LP coefficients
are explicitly converted to rational numbers before219's minimum-price
division, so even constant integer heads remain exact under Python arithmetic.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j_face_shared_square_factorial.py --check
```

Later positive-cost consumers may use these moments together with the
existing mean and actual mass on the same saturated J domain. They must
still retain all original costs, signed mass terms, AP survival blocks and
complete count tails in their own comparison. These moment bounds are
ordinary mathematical results with exact arithmetic evidence, without a
Lean, off-face or unrestricted Erdos7 claim.
