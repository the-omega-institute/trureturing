[Index](../../marked_head_profile.md) · [Actual source families](../001-064/48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Complete actual repacking](161-an-actual-repacking-attains-the-full-deep-five-cap.md) · [Pure-five moments](164-the-pure-five-first-and-second-moments-have-a-sharp-joint-envelope.md) · [Pure-three moments](171-the-pure-three-path-has-a-joint-complete-moment-bound.md)

# The isolated pure-three/five cross is actually sharp

For independently labelled complete pure-power tests on the
saturated K faces, put

    Z3=sum_(a>=1)I_(J_a), Z5=sum_(b>=1)I_(F_b).

The isolated cross satisfies the sharp bound

    integral Z3*Z5 dmu<=17/200,
    2*integral Z3*Z5 dmu<=17/100.                 (AC1)

The unchanged actual original-label families of161 approach
equality with one common survivor measure. No new packing or
additional compatibility assumption is needed. Thus a smaller
uniform bound for this cross alone is impossible on the stated
face closure.

This does not prove sharpness of the complete square or its
current bound2203/450. The cross-extremizing tests below do not
simultaneously maximize either of164 and171's marginal moments.
A joint total-moment improvement remains possible. No52-cost
comparison, global K bound, covering system or Lean theorem is
asserted here.

## 1. Isolate exactly two ordered pairs in each mixed LCM bin

The existing arbitrary-cylinder caps give six complete terms:

| Pure-power pair range | Bound in integral Z3*Z5 |
| --- | ---: |
| a=1,b=1 |8/225|
| a=2,b=1 |4/225|
| a>=3,b=1 |(1/5)*sum_(a>=3)3^-a=1/90|
| a=1,b>=2 |(4/15)*sum_(b>=2)5^-b=1/75|
| a=2,b>=2 |(4/45)*sum_(b>=2)5^-b=1/225|
| a>=3,b>=2 |sum_(a>=3,b>=2)3^-a*5^-b=1/360|

Their sum is17/200. These are the complete source-face caps
exported by k_face_complete_ratio.cylinder_cap; the last two
infinite directions use exact geometric series. Nonnegative
monotone convergence justifies the entire cross sum.

For an LCM exponent pair(a,b), a,b>=1, all ordered original
exponent pairs have multiplicity(2a+1)(2b+1). Exactly two are
the pure-axis pair(a,0),(0,b) and its reverse. Every other pair
contains at least one truly mixed label. The complete old
mixed-exponent allowance decomposes as

    593/450 = 17/100 + 1033/900.                 (AC2)

The second summand is untouched. In particular(AC1) cannot
replace the entire mixed-label LCM category.

## 2. Use the existing161 family without changing any label

The five surviving ternary cells are

    C0=[0]_9, C1=[3]_9, C2=[1]_9,
    C3=[4]_9, C4=[7]_9.

Use exactly48's source_label(a,b,398) and161's mixed_label(a,b).
Thus all source and mixed-seven rows, including their seven
digit classes, remain as in161. For every N>=3 there is one
residue at each nonunit original modulus3^a5^b7^e with
0<=a,b,e<=N, namely(N+1)^3-1 distinct odd moduli.

The following features of that explicit constructor suffice
to compute the new tests:

- Source pure-three classes at a>=3 are
  T_a(0,1)=[3^(a-1)]_(3^a). The late source uses
  T_a(0,2)=[2*3^(a-1)]_(3^a) with the five familyF_(2,b).
- Source pure-five, alpha and beta families use respectively
  F_(1,b),F_(2,b),F_(3,b), where
  F_(j,b)=[j*5^(b-1)]_(5^b). Alpha and late can share their
  five cylinders because their ternary carriers are disjoint.
- The mixed-seven cofactor3 is on root1, and cofactor9 is inC1.
  Every deeper pure-three forbidden cofactor lies inC1.
- Every forbidden cofactor with a positive five exponent lies
  in H=[4]_5. Its subfamilies and seven classes are exactly the
  disjoint packing already proved in161. All deeper mixed
  ternary carriers are inC1.

In particular, inside Q=[0]_5 the three source digit families
are1,2,3, with alpha and late sharing digit2; digit4 is free.
No source family is dropped to create that free test region.

Choose the auxiliary test residues

    J1=[1]_3, J2=C3=[4]_9,
    J_a=T_a(0,2) for a>=3;
    F1=[3]_5, F_b=F_(4,b) for b>=2.             (AC3)

These specify the independently labelled tests in the cap
problem; they do not add duplicate forbidden moduli to the
original family. All cross rectangles avoid C1 and H. Therefore
only the shallow forbidden cofactor3 can meet them, and it
meets only J1 and J2. Every other original forbidden label is
still present and is disjoint from these cross rectangles.

The existing disjointness proof for161 preserves every old
cofactor mass and gives the same source parameters and mass
limit(theta398,53/360). The helper also checks that the entire
sorted original-label digest equals161's digest at each tested
height; the family is literally unchanged.

## 3. Keep the physical seven normalization in the finite formula

Write

    t_N=sum_(a=3..N)3^-a=(1-3^(2-N))/18,
    B_N=sum_(b=2..N)5^-b=(1-5^(1-N))/20,
    q_N=1/5+B_N,
    u_N=(5+7^-N)/6,
    kappa_N=(1-7^-N)/(5+7^-N).                  (AC4)

Here u_N is the actual pure-seven survivor mass, and kappa_N
is the normalized mass of any single complete finite seven
digit family. It is the same measure used by every source and
test term. The exact surviving mass remains

    S_N=5/9-t_N-q_N
         -kappa_N*(4/9+t_N+q_N/9-t_N*q_N).       (AC5)

Source restriction and the single possible forbidden cofactor
give the exact cross intersections:

| Pair | Exact finite normalized survivor |
| --- | ---: |
| J1,F1 |(1-kappa_N)*2/45|
| J2,F1 |(1-kappa_N)/45|
| J_a,F1, a>=3 |3^-a/5|
| J1,F_b, b>=2 |(1-kappa_N)*5^-b/3|
| J2,F_b, b>=2 |(1-kappa_N)*5^-b/9|
| J_a,F_b, a>=3,b>=2 |3^-a*5^-b|

For example F1 deletes source cellC2, leaving two root1 cells;
F_b for b>=2 is source free on root1. The deep J_a tests avoid
source pure-three deletion and their late-source five family
F_(2,b), because every tested five cylinder uses digit3 or4.
The disjoint seven packing then subtracts precisely kappa_N
times the applicable cofactor3 rectangle.

Summing the complete finite test family gives

    C_N=integral Z3_N*Z5_N dmu_N
       =(1-kappa_N)/15+t_N/5
          +[4*(1-kappa_N)/9+t_N]*B_N.           (AC6)

Replacing kappa_N by1/5 prematurely would omit the positive
correction

    (1/5-kappa_N)*(1/15+4B_N/9).                (AC7)

It must be retained in a finite exact claim. Let

    epsilon3=1/18-t_N, epsilon5=1/20-B_N.

The complete finite error is exactly

    17/200-C_N=epsilon3/4+(16/45+t_N)*epsilon5
                  -(1/5-kappa_N)*(1/15+4B_N/9). (AC8)

All three terms tend to zero. The expression is positive:
epsilon3/4=1/(8*3^N), while the magnitude of the final term
is at most8/(375*7^N), which is smaller. Consequently the same
actual finite-family sequence satisfies

    S_N ->53/360, C_N ->17/200.                 (AC9)

This explicit arbitrary-height calculation proves the claimed
sharpness in the actual face closure, without promoting a
finite enumeration to an infinite theorem.

## 4. Cross equality is not simultaneous marginal equality

For this very same family and these same tests, J2 is insideJ1,
all deep J_a are disjoint outside root1, and all F_b are
pairwise disjoint. The limiting moments are

    integral Z3=49/360,
    integral(Z3^2+2Z3)=19/40 <34/45;
    integral Z5=37/450,
    integral(Z5^2+2Z5)=37/150 <49/180.           (AC10)

For the ternary calculation, the limiting masses of J1,J2 and
the deep union are respectively7/90,1/30,1/40. Thus its moment
is3*(49/360)+2*(1/30)=19/40. The five calculation uses Z5<=1.
The comparison values34/45 and49/180 are171 and164's complete
lambda=2 marginal bounds.

Hence this witness does not obstruct an improvement obtained
by coupling the cross to those marginal moments. It only
excludes decreasing the standalone coefficient17/100 while
leaving the other pieces independently bounded as before.

The [helper](../../frontier/cover-geometry/pure_axis_cross_sharpness.py) checks
the unchanged complete original inventory, every old-cofactor
mass, the physical seven normalization and each cross pair
at N=3,4,5. At N=3 it independently constructs the actual union
on all1,157,625 CRT residues and evaluates both the full survivor
mass and Z3_N*Z5_N directly. The
[certificate](../../certificates/source_norms/cover-geometry/pure_axis_cross_sharpness.json)
also records the exact complete upper partition, finite error,
same-family marginal moments and the original-label hashes.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure_axis_cross_sharpness.py --check
```
