[Index](../marked_head_profile.md) · [Complete pure-three deletion](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md) · [Projected complete families](125-the-complete-off-face-omitted-tails-recover-every-face-constant.md) · [Pure-five moments](164-the-pure-five-first-and-second-moments-have-a-sharp-joint-envelope.md) · [Complete factorial consumer](168-the-first-five-support-lowers-the-complete-factorial-bound.md)

# The pure-three path has a joint complete moment bound

On both complete saturated actual K faces, let Z be the sum of
independently labelled pure-three test indicators over every depth
a>=1. For every lambda>=0,

    integral(Z^2+lambda Z)
      <=max(77/180+59lambda/360, 2/5+31lambda/180).       (T3.1)

At lambda=2 the bound is34/45, improving the old scalar block37/45
by1/15. This block is disjoint from164's pure-five replacement.
Consequently the complete square upper bound improves from2233/450
to2203/450. Keeping168's factorial gains, all52 original costs and
the complete denominator gives the complete saturated-face bound

    K<=458.9241624449242... .                           (T3.2)

This is an ordinary all-depth upper-bound theorem, not an actual
family sharpness result. It does not supply an off-face or global
bound, Lean verification, or an unrestricted Erdos7 resolution.

## 1. The full projection gives different caps on different cells

Use the same actual survivor measure mu as75/125. In the canonical
orientation ROOT=(0,0,1,1,1), and the saturated shallow3/9 carrier
is(1,1). Thus the complete attenuation vector in125 OT1 is

    a=(1,4/5,4/5,4/5,4/5).

Saturation makes the entire OT2 nonnegative residual sum zero.
In particular both shallow and deep pure5/root15 defects vanish,
as does omega. Hence Xi5=Xi15=W=0 in OT3. This uses the complete
families; shallow saturation alone would not suffice. Before any
maximum over cells, the actual measure inequality is

    mu^3|cell_l <= [a_l*d_l-(1+ROOT(l))/20]*eta|cell_l.  (T3.3)

Here d0=d1=3/4 and d_l=1/2-beta_l on the three root1 cells.
Since beta_l>=0 and eta is dominated by ternary Haar measure,
every independent depth-a cylinder J_a contained in cell l,
a>=3, satisfies

    mu(J_a)<=c_l*3^-a,
    c=(7/10,11/20,3/10,3/10,3/10).                    (T3.4)

The last three entries discard the nonnegative subtraction
4beta_l/5. They therefore hold on the whole beta face, not just
its vertices. The second K orientation follows by the same
root0-cell exchange used in75.

From75 the two depth-one root caps and five depth-two cell caps are

    A=(7/90,7/90),
    B=(1/40,1/18,1/30,1/30,1/30).                    (T3.5)

Other ternary roots or cells are null for the actual survivor
measure. Tests in them contribute zero. In an upper-bound problem
with nonnegative moment coefficients they can be ignored or
relaxed to an allowed choice. This does not identify distinct
modulus labels or impose common residues on different tests.

## 2. Keep the two shallow choices when bounding the whole tail

Fix the independently chosen first root r and second cell j.
Their contributions to the moment are bounded by

    (1+lambda)*A_r
        +(1+lambda+2*I(ROOT(j)=r))*B_j.                (T3.6)

For each cell l set

    n_l=I(ROOT(l)=r)+I(l=j).

At each deeper exponent the original test may choose any cell.
Two compatible ternary cylinders of different depths intersect
in the deeper cylinder; incompatible ones are disjoint. Replacing
actual compatibility by membership in the same depth-two cell
only increases the bound. Choosing cell l at depth a therefore
has reward at most

    c_l*(2n_l+1+lambda)*3^-a,

and then increments n_l by one. No nested sequence of residues is
assumed. This is a relaxation of all independent original tests.

Put q=1/3. For a general current count vector n define

    V_l(n)=c_l*[(2n_l+1+lambda)/(1-q)+2q/(1-q)^2],
    V(n)=max_l V_l(n).

Let R_l(n)=c_l*(2n_l+1+lambda). Then

    R_l(n)+q*V_l(n+e_l)=V_l(n).                      (T3.7)

If k differs from l, V_k(n+e_l)=V_k(n), while
R_l(n)<=(1-q)*V_l(n). Therefore

    R_l(n)+q*V(n+e_l)<=V(n)                         (T3.8)

for every choice l. Iterating bounds every finite allocation;
the remaining discounted potential is O(N*3^-N) and vanishes.
Always choosing an initially maximizing cell attains this value
in the allocation relaxation. This is not a construction of an
actual original covering family.

Including the initial factor3^-3, the complete deep contribution
is bounded by

    max_l c_l*(n_l+1+lambda/2)/9.                    (T3.9)

For a fixed actual measure, the moment expansion is nonnegative,
so monotone convergence justifies the all-depth statement. For
varying finite sources and independently varying labels in the
inherited face limit, use the global raw bound mu_N(J_a)<=3^-a.
The moment terms with deepest exponent greater than A have the
uniform bound

    sum_(a>A)(2a-1+lambda)*3^-a -> 0.

At each fixed finite depth, take the inherited convergent source
subsequence and stabilize the finitely many residue labels. The
uniform tail estimate then passes the complete moment bound to
the face limit; this step is separate from monotone convergence.

## 3. Fifty exact affine lines have a two-piece envelope

For each(r,j,l), combine(T3.6) and(T3.9). There are2*5*5=50
affine functions. Every candidate is at most77/180 at lambda=0,
at most263/270 at lambda=10/3, and has slope at most31/180.
The checker verifies these three inequalities with rational
arithmetic for every candidate, not just a sampled lambda grid.

The choices(r,j,l)=(0,1,1) and(0,1,0) give respectively

    77/180+59lambda/360,
    2/5+31lambda/180.

They meet at10/3. Linear interpolation on[0,10/3], followed by
the slope comparison on[10/3,infinity), proves(T3.1) for every
lambda>=0. A separate memoized seven-step allocation check covers
arbitrary changes of cells; it is a regression check, whereas
(T3.7)-(T3.9) prove the infinite result.

## 4. Replace exactly one disjoint block of the complete square

The old full LCM square assigns to the unit/pure3 crosses and
pure3/pure3 pairs the upper bound

    3*(7/90)+5*(1/18)+(7/10)*sum_(a>=3)(2a+1)*3^-a
      =37/45,
    sum_(a>=3)(2a+1)*3^-a=4/9.                     (T3.10)

Their actual total is integral(Z^2+2Z), so(T3.1) replaces it by
34/45. The unit-unit mass remains exactly once. Pure-five/unit
and pure-five/pure-five pairs are the separate block improved
in164. Crosses involving both primes, truly mixed test labels,
and all positive-seven categories retain their previous bounds.
There is no second subtraction from an already estimated total.

Thus

    Q<=374/75-11/450-1/15=2203/450.                (T3.11)

Using the forced27 fact in B_j and the projected five deletion
in(T3.4) is legitimate: these are upper bounds on distinct terms
of the moment expansion, under the same actual measure.

## 5. Reaggregate the complete comparison

The consumer retains168's52 cost bounds and reconstructs its
signed numerator. The square coefficient is positive. It replaces
only Q by(T3.11), then reruns the existing common-cost majorant
propagation. Every original independent cost occurs exactly once.
The actual mass and mean remain53/360 and1151/1800; the complete
denominator stays50511415637/632754738000, including all AP11
blocks, the AP13 loss and the complete remaining count tail.

The exact comparison and the improvement over168 are stored in
the [certificate](../certificates/source_norms/pure_three_joint_moments.json).
The [helper](../frontier/pure_three_joint_moments.py) checks the full
source hash closure using multipart-aware certificate reads.
All computations use exact rational arithmetic. No factorial
head maximum is silently rescanned with an unrelated source.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/pure_three_joint_moments.py --check
```

The resulting comparison remains above403. The new theorem
reduces one complete contribution; it does not settle the
unrestricted covering problem.
