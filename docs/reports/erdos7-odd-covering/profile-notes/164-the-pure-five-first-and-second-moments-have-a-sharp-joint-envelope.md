[Index](../marked_head_profile.md) · [Slot and deep-three bounds](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md) · [Actual sharpness family](161-an-actual-repacking-attains-the-full-deep-five-cap.md)

# The pure-five first and second moments have a sharp joint envelope

On either saturated actual K face, with the entire admissible beta
face retained, let F_b be the independently chosen original test
cylinder of modulus5^b and put

    Y=sum_(b>=1)1_(F_b).

For every lambda>=0 there is the sharp bound

    integral_mu (Y^2+lambda*Y)
      <=max(7/60+7lambda/90, 83/900+37lambda/450). (JM1)

The two lines meet at lambda=11/2. Each line is attained as a limit
of actual finite original-modulus families, using the same source
sequence161 and different choices of the original test residues.
In particular

    integral Y^2<=7/60,
    integral(Y^2+2Y)<=49/180.                    (JM2)

These are joint estimates. The separately sharp first-five cap,
deep-five caps and deep/deep intersection caps from161 do not
attain their sum in every joint objective: choosing the first
five slot also fixes which deeper tests can meet it.

Substituting the second estimate in the original complete square
improves its full-face bound from374/75 to

    Q<=2233/450.                                (JM3)

Every other LCM category is unchanged. This theorem concerns the
saturated faces. It is not an off-face estimate, a full52 comparison,
a new global K bound or a solution of unrestricted Erdos7.

## 1. Retain both the first-slot masses and the deeper density caps

Use75's source slots(P,A,B,Q,H): the first pure-five, alpha and
beta source slots, the remaining deep-source slot, and the unique
first slot free of all five-source deletion. They are five
different first-level cylinders. The first test has mass at most

    (A_P,A_A,A_B,A_Q,A_H)
      =(0,2/75,14/225,7/150,7/150).              (JM4)

For every depth b>=2 cylinder F contained in slot j there are the
stronger slot-specific density bounds

    mu(F)<=c_j*5^-b,
    (c_P,c_A,c_B,c_Q,c_H)
      =(0,2/15,14/45,2/5,7/30).                (JM5)

Here mu denotes the original survivor's five-coordinate marginal;
no new measure or independent resampling is introduced.

To prove(JM5), retain exactly75's complete forbidden3,9 families
and the single complete deep-pure-three family. On an arbitrary
five set the resulting baseline is at most2/5 times its Haar mass.
The deep-three subtraction is the entire q(F)/90, including27
once. Inside A the first alpha source label removes root1. After
accounting for the already retained forbidden3 weight, this costs
an additional(4/5)*(1/3)=4/15 per unit Haar mass. Inside B the
first beta source label removes one root1 cell, costing an
additional(4/5)*(1/9)=4/45. This does not assume that later beta
labels use the same cell.

Inside H, saturation makes the source measure equal to the pure
ternary source times Haar5. The distinct forbidden5 and15 families
remove an additional(h+h1)/5=(1/2+1/3)/5=1/6 per unit Haar mass.
The full forbidden union is additive on the saturated face, so
these deletions may be combined even if their old projections
intersect. P is already removed by the first pure-five source
label. Q keeps the baseline2/5. These give exactly(JM5), uniformly
for all the beta distributions in75.

## 2. Arbitrary original labels reduce to a discounted allocation

Two five-adic cylinders are either disjoint or nested. For a<b,
if F_a and F_b meet, their intersection is F_b. Let j_b be the
first slot containing F_b, and let n_j(b) count the earlier test
labels in that slot. Thus

    mu(F_b)+2*sum_(a<b)mu(F_a intersect F_b)
       +lambda*mu(F_b)
      <=c_(j_b)*(2n_(j_b)(b)+1+lambda)*5^-b     (JM6)

for b>=2. A previous label in another first slot contributes
nothing. A previous label in the same slot need not contain F_b;
counting all such labels only enlarges the upper bound. No nesting
of the independently chosen original residues is assumed.

The first term is at most(1+lambda)A_(j_1). Afterwards every depth
chooses one of five slots, whose count rises by one. The time
weight decreases by r=1/5 at each successive depth.

## 3. An exact discounted allocation lemma

Let c_j>=0, r in(0,1), lambda>=0, and let n_j be the current
counts. For the future reward c_j*(2n_j+1+lambda) upon choosing
slot j, define

    V_j(n)=c_j*[(2n_j+1+lambda)/(1-r)
                                    +2r/(1-r)^2],
    V(n)=max_j V_j(n).                           (JM7)

This is exactly the infinite discounted reward from choosing the
same slot j forever. It also bounds every changing allocation.
For a first choice k, write R_k=c_k*(2n_k+1+lambda). If the next
potential uses j=k, direct expansion gives

    R_k+r*V_k(n+e_k)=V_k(n)<=V(n).

If it uses j!=k, that slot's count has not changed. Also
R_k<=(1-r)V_k(n)<=(1-r)V(n), so

    R_k+r*V_j(n+e_k)<=V(n).

Taking the maximum over j proves the Bellman inequality

    R_k+r*V(n+e_k)<=V(n).                       (JM8)

Iterate(JM8). Counts grow at most linearly, so the terminal
potential multiplied by r^N tends to zero. This bounds every
infinite allocation by V(n). Choosing an initially maximizing
slot forever attains V(n). The lemma therefore gives the exact
support of this allocation relaxation, not just a finite-depth
search result.

## 4. The five-slot maximum has two exact affine pieces

After the first test uses slot j, its count is1 and all other
counts are0. The depth-two factor is5^-2. Apply(JM7) with r=1/5:

    deep contribution
      <=max((7+2lambda)c_j,
                    (3+2lambda)*max_(k!=j)c_k)/40.            (JM9)

The full upper is the maximum, over first slot j and repeated
deep slot k, of the25 affine expressions

    (1+lambda)A_j
      +c_k*[(7 if k=j else3)+2lambda]/40.        (JM10)

Substituting(JM4),(JM5) reduces this exactly to(JM1). One rational
verification suffices on each interval: every candidate line is
below the first envelope at0 and11/2; beyond11/2 it is below at
the endpoint and has slope at most37/450. The two active choices
are first B with deep B, and first B with deep Q.

The proof also controls the infinite moment expansion itself.
The terms in(JM6) are nonnegative and bounded by a constant times
b*5^-b. Their sum converges, so monotone convergence from finite
original tests gives the complete all-depth statement. Infinite
pointwise values on a null set do not invalidate the integral.

## 5. Both lines have actual full-family limiting witnesses

Use161's exact repacking, retaining every original mixed-seven
label and the same normalized survivor. Let t_N,h_N,kappa_N be
its finite geometric quantities. On the whole first slot B=[3]_5,
the projected measure has constant density

    d_(B,N)=h_N-1/9-kappa_N*(1/3+t_N) ->14/45.   (JM11)

Indeed only the beta source cell C2 is removed there; all positive
five mixed carriers are in H. The remaining complete three/nine
and deep-three deletion is independent of the five coordinate.
The same proof as161's first-cylinder calculation therefore holds
on every measurable subset of B, not merely B itself.

Choose every original test F_b=[3]_(5^b). They are nested in B.
Their finite moments are exactly

    integral Y_N=d_(B,N)*sum_(b=1..N)5^-b,
    integral Y_N^2=d_(B,N)*sum_(b=1..N)(2b-1)5^-b.

Since the two complete geometric sums are1/4 and3/8, this gives

    (integral Y,integral Y^2) ->(7/90,7/60).     (JM12)

For the other choice keep F_1=B and take F_b=[20]_(5^b), b>=2.
These deep tests are nested inside Q and disjoint from B. By161
their density tends to2/5. Consequently

    (integral Y,integral Y^2)
      ->(14/225+(2/5)/20,14/225+(2/5)*(3/40))
       =(37/450,83/900).                        (JM13)

Both are actual finite original-label sequences approaching the
same saturated face; no independent cap maxima are substituted
for witnesses. For lambda<=11/2 use(JM12), and for lambda>=11/2
use(JM13). This proves sharpness throughout the stated range.
Finite N need not lie exactly on the limiting saturated face.
There is also a uniform tail bound for the finite actual witnesses:
u_N>=5/6 implies mu_N(F_b)<=(6/5)*5^-b, so the omitted moment
tail is at most(6/5)*sum_(b>m)(2b-1+lambda)*5^-b, which tends to
zero independently of N. Thus extending these finite tests to
complete tests does not conceal an exchange of uncontrolled tails.

## 6. The complete square has a disjoint category substitution

In143's complete zero-seven square, the terms with both ternary
exponents zero are the unit-unit term S, the pure-five square
Y^2, and its two crosses with the unit. The old bound for the
last two together was

    3*(14/225)+(2/5)*sum_(b>=2)(2b+1)*5^-b
       =89/300.                                (JM14)

The whole sum in(JM14) is replaced by(JM2) at lambda=2, namely
49/180. The unit-unit term S is retained separately, as are all
pairs with a positive ternary exponent and every positive-seven
pair. Their LCM categories are disjoint from this substitution.
The exact saving is

    89/300-49/180=11/450,
    374/75-11/450=2233/450.

This proves(JM3). It is not a second subtraction of the same
forbidden family: the proof changes how the pure-five tests are
bounded jointly, while retaining the original full category
partition. A complete52 consumer and transport away from the
saturated face require their own same-source proofs.

The [helper](../frontier/pure_five_joint_moments.py) records all25
candidate lines, checks the exact envelope and its switch, and
independently optimizes finite seven-step allocations for four
lambda values and every first slot. Its actual witness check
constructs all63 original moduli at height3 and directly measures
the Y and Y^2 histograms on the full1,157,625-residue CRT period,
for both nested configurations. The
[certificate](../certificates/source_norms/pure_five_joint_moments.json)
retains exact rational results. The discounted lemma and geometric
limits supply the all-depth proof; finite computations do not
replace it. No Lean theorem or frozen state is claimed.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/pure_five_joint_moments.py --check
```
