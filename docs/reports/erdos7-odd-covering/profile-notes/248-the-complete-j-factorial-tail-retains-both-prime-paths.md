[Index](../marked_head_profile.md) · [Original J moments](241-one-original-j-head-controls-complete-square-and-factorial-moments.md) · [Actual J source](130-the-whole-j-face-forces-source-anti-alignment.md) · [Five-path bound](168-the-first-five-support-lowers-the-complete-factorial-bound.md) · [Three-path bound](174-the-pure-three-factorial-tail-retains-its-original-head.md)

# The complete J factorial tail retains both prime paths

On both entire saturated actual J faces, every independent original
complete357 load A satisfies

    integral Phi5(A) dmu <=6313/7200,
    Phi5(n)=(n-5)_+*(n-4)/2.

The improvement over241's6353/7200 is1/180. The same actual
unnormalized survivor mu has mass3/20. All original residues, the
whole common late-parameter interval and every exponent tail remain.
This bound replaces two disjoint blocks inside the original
factorial partition before maximizing over the shallow head.

The argument applies the existing168/174 discounted-allocation
bounds to the J source coefficients derived below. No numerical
K-face density or forced27 condition is used. A complete52-cost
consumer must separately rebuild its numerator and denominator;
this factorial bound alone is not a403 comparison or an off-face
result.

## 1. Cell-specific J caps for every deep pure-three test

Use130's canonical ternary cells c=0,...,4, with the first beta
source cell L=2 and ROOT=(0,0,1,1,1). Its(J6) gives, for every
depth-a original pure-three cylinder J contained in cell c,

    mu(J)<=c3_c*3^-a, a>=3,
    c3=(11/20,2/5,1/5,2/5,2/5).                  (JP1)

Indeed the two root0 coefficients are11/20 and2/5. In root1
the coefficient is2/5-beta_c. The first beta source label has
beta_L>=1/5; every other beta coefficient is nonnegative.
Discarding further beta deletion therefore yields(JP1).
This controls every residue in its cell, not only the actual
forbidden cylinder. A zero test outside the five source cells
can be retained as zero or included in a larger nonnegative
allocation bound.

## 2. Slot-specific J caps for every deep pure-five test

Let(P,A,B,Q,H) be the five distinct first-five source slots in130.
For any original cylinder F of depth b>=2 in slot s,

    mu(F)<=c5_s*5^-b,
    c5=(0,1/10,29/90,13/30,4/15).                 (JP2)

To derive the coefficients, first retain exactly130(J8)'s
shallow forbidden3 and9 deletions and its complete deep-three
deletion E3. Their common baseline is

    [h-(h0+eta1)/5-1/90]*q(F)=(13/30)*q(F).

The measure q is the raw pure-five survivor. On A,B,H there
are no deeper pure-five source deletions, so q restricted to
these slots is quinary Haar. Distinct source slots allow the
following additional restrictions:

- P is already removed by the first pure-five source label.
- A removes the entire root1 source mass1/3. Neither shallow
  forbidden3 nor9 acts there, and E3 is supported in root0.
  Thus its coefficient is13/30-1/3=1/10.
- B removes the first beta source cell L, of ternary mass1/9.
  This cell is also in root1, giving13/30-1/9=29/90. Further
  beta and late-source removal is nonnegative and is discarded.
- Q retains the bound13/30, using q(F)<=Haar5(F).
- H is source-free. The two distinct saturated shallow forbidden
  cofactors5 and15 lie respectively in H and root1 times H.
  They remove an additional(h+h1)/5=(1/2+1/3)/5=1/6 per
  unit quinary Haar mass. These families were not included in
  the(J8) baseline. Saturation makes their virtual deletions
  additive in the actual deleted measure, hence the coefficient
  is13/30-1/6=4/15.

This is a bound for the original survivor's five marginal.
No conditioning, renormalization or new reference measure is
introduced. Projected overlap of forbidden families does not
invalidate addition: their measures are additive before projection
on the saturated actual source.

## 3. Preserve one original shallow head in both replacements

Fix one of the12500 independent original layouts

    ell=(r3,c9,s5,r15,s15,c45,s45),
    B=1+I3+I9+I5+I15+I45, h=(B-4)_+.

Let p(c,s),d(c,s),w(c,s) be241's normalized deep-three table,
absolute descendant-five table and retained density. The original
head-cross estimates give the coefficients

    A3_c=sum_s p(c,s)w(c,s)h(c,s),
    A5_s=sum_c d(c,s)w(c,s)h(c,s).                 (JP3)

In particular h may equal2. A weighted cross coefficient is not
replaced by its unweighted mass cap. Put

    R3=sum_(a>=3) I_(3^a), R5=sum_(b>=2) I_(5^b).

The two actual positive blocks of241's factorial decomposition are

    X3=integral[h*R3+binom(R3,2)] dmu,
    X5=integral[h*R5+binom(R5,2)] dmu.             (JP4)

They are disjoint classes of terms. Mixed-prime pairs, root-five,
cell-five, old/positive-seven and positive-seven/positive-seven
terms remain unchanged.

For nonnegative a_j,c_j, discount r in(0,1) and current counts n,
use168/174's potential

    V_j(n)=(a_j+c_j*n_j)/(1-r)+c_j*r/(1-r)^2,
    V(n)=max_j V_j(n).

Choosing cell or slot k gives reward a_k+c_k*n_k and increments
only n_k. The k component satisfies the exact Bellman identity;
every other component remains unchanged, and the reward is at
most(1-r)V_k(n). Therefore

    a_k+c_k*n_k+r*V(n+e_k)<=V(n).                 (JP5)

This bounds every independently changing allocation. It imposes
no nesting or common residue requirement on original tests.
Cylinders in different cells or slots are disjoint; those in the
same cell or slot may also be disjoint, which only lowers their
actual intersections. The terminal discounted potential is
O(N*r^N) and tends to zero.

Using initial factors3^-3 and5^-2 yields

    X3<=Q3=max_c(A3_c/18+c3_c/36),
    X5<=Q5row=max_s(A5_s/20+c5_s/80).             (JP6)

## 4. Retain the original first-five event explicitly

A second bound on X5 uses the exact same-head identity

    K=I3+I9+I15+I45, G=1_(K=4), H'=1_(K>=3),
    h=G+I5*H'.                                   (JP7)

The overlap when all five indicators hold is necessary. If f=s5
is the original first-five slot, define

    e_f=min(c5_f,sum_c d(c,f)w(c,f)H'(c,f)),
    O5G=max_s sum_c d(c,s)w(c,s)G(c,s)/20.

The same Bellman bound applied to the I5*H' term and the complete
pure-five pair term gives

    X5<=Q5cond=O5G+max(c5_f/80+e_f/20,
                           max_(s!=f)c5_s/80).   (JP8)

Use Q5=min(Q5row,Q5cond). Both expressions bound the same
positive block in the same actual measure.

## 5. Replace the complete pair charges exactly once

The original scalar pure-three and pure-five unordered-pair
charges in241 are

    P3=(11/20)*sum_(a>=3)(a-3)*3^-a=11/720,
    P5=(13/30)*sum_(b>=2)(b-2)*5^-b=13/2400.      (JP9)

The checker reconstructs241's complete pair partition and matches
these to its two corresponding ordered subseries divided by2.
Its full distinct-tail-pair total remains5089/7200. Define

    Delta3=Q3-max_c A3_c/18-P3,
    Delta5=Q5-max_s A5_s/20-P5.                   (JP10)

Since max c3=11/20 and max c5=13/30, both changes are nonpositive.
Subtracting the old block and adding its replacement in the
same original head gives

    Phi5(A) integral
      <=J241(ell,theta)+Delta3(ell)+Delta5(ell)
                          +5089/7200.            (JP11)

Here J241 is the entire corrected factorial head, including its
old-tail and positive-seven crosses. No numerical saving is
subtracted from a separately optimized downstream total.

Both Delta terms are independent of the late parameter theta.
The inherited J241 bound is convex in theta: its raw rows are
sums of maxima of affine source objectives. Its endpoint maximum
therefore bounds the entire interval[1/135,1/90]. The checker
covers all12500 original layouts at both endpoints.

The unique maximizing record is

    ell=(1,4,2,1,2,4,2), theta=1/90,
    old complete upper=6353/7200,
    Delta3=-1/240, Delta5=-1/720.

Consequently the new complete upper is6313/7200 and the gain is
1/180. The all-layout maximum is recomputed; this conclusion does
not presume that the old controller remains maximizing.

All tail summands are nonnegative and dominated by the complete
geometric and polynomial cap series. For a fixed actual source,
monotone convergence passes finite expansions to the infinite
sum. For varying finite-source approximants, the original raw
cylinder bounds give uniform remainders O(sum_(a>A)a*3^-a) and
O(sum_(b>B)b*5^-b). Stabilizing finitely many labels and then
sending the tail cutoff to infinity preserves the inherited
face-limit statement. Both J orientations transport the source
cells, slots, deletions and original layouts together.

## 6. Exact artifact and remaining scope

The [helper](../frontier/j_face_pure_path_factorial.py) and
[certificate](../certificates/source_norms/j_face_pure_path_factorial.json)
retain the density coefficients, complete pair partition, both
replacement histograms, all-layout component digest and maximizing
witness. All arithmetic is rational; the canonical checker needs
only the Python standard library and the pinned source providers.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j_face_pure_path_factorial.py --check
```

The result is an ordinary complete-source inequality with exact
arithmetic verification. The improved square from245 may be used
on the same domain, but no complete52-cost improvement is asserted
here. No actual-family attainment, off-face transport, Lean theorem
or unrestricted Erdős7 resolution is claimed.
