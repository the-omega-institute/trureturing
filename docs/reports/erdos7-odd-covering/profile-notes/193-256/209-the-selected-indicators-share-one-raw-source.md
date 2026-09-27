[Index](../../marked_head_profile.md) · [Complete second-depth bridge](204-a-second-seven-depth-strengthens-both-complete-heavy-costs.md) · [Independent original intersections](201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md)

# The selected indicators share one raw source

The four selected zero-seven labels25,27,75,81 can be retained together
in one raw-source linear program. This improves both original heavy
costs while preserving every original independent residue, the same
six-label head, all six positive-seven projections, and every infinite
tail. The consumer retains207's complete52-cost vector and denominator.

The resulting exact heavy-cost bounds are

    Cost0 <=1434891713993480665143496527366776791
              /249700113789296025205350000000000000
           =5.746459992422281...,
    Cost16<=34057061774853834829716139076539327141
              /7416093379542091948598895000000000000
           =4.592318358450429... .

The complete comparison improves207's426.31906080567376... to

    K<=980141580999201339774108248263002986360134069903
        /2301471644338258981874507034446859225000000000
      =425.8760186815254... .

The improvement is0.44304212414836.... It remains22.8760186815254...
above the terminal403 threshold on these faces.

The domain is the two complete actual saturated K faces, r=rho=0,
with surviving mass53/360. These are ordinary source inequalities and
exact rational certificate checks. There is no claim of actual
attainment, an optimal LP dual, off-face or global improvement, Lean
verification, or a resolution of unrestricted Erdos7.

## 1. A common raw-source refinement

Use201's canonical25 old rectangles indexed by k=(c,s), with c,s in
{0,...,4}, and the same raw measure Lambda. Write J0,J1,J2,J3 for the
actual indicator events of moduli25,27,75,81. For S contained in
{0,1,2,3}, define

    x_(k,S)=Lambda(rectangle k intersect {j:Jj=1}=S).       (JS1)

These400 variables are nonnegative and refer to one actual measure.
They do not represent four independently chosen marginal measures.
The same source tables as201 give

    sum_S x_(k,S)<=raw_k,
    sum_(k in G,S) x_(k,S)<=budget_G.                     (JS2)

There are25 rectangle caps and three group budgets. The latter keep
the entire allowed distributed-beta source; no beta vertex is selected.

Each original selected modulus has its own independently chosen
residue projection. Let its legal projection profiles be p_(j,a,k).
Writing d_(c,s) for201's descendant-five coefficient and h_(c,s) for
its pre coefficient, the profiles are

    j=0: 1_(s=a)*d_(c,s)/25,                    a in {0,...,4};
    j=1: 1_(c=a)*h_(c,s)/27,                    a in {0,...,4};
    j=2: 1_(ROOT(c)=r,s=a)*d_(c,s)/25,         (r,a) in {0,1}x{0,...,4};
    j=3: 1_(c=a)*h_(c,s)/81,                    a in {0,...,4}. (JS3)

These are precisely the fixed-projection raw cylinder caps underlying
201's original P25,P27,P75,P81 operators. They bound raw source
marginals; the survivor density must not be substituted in them.
The root condition for75 is retained, with its original cap rather
than an additional unwarranted factor of1/3.

Introduce nonnegative variables lambda_(j,a) and require

    sum_a lambda_(j,a)=1,
    sum_(S containing j) x_(k,S)
                   <=sum_a lambda_(j,a)*p_(j,a,k).        (JS4)

For an actual original residue, choose the corresponding point mass
lambda_(j,a). Thus every actual configuration lifts to(JS1)--(JS4).
Relaxing point masses to convex mixtures enlarges the containing set;
it does not require the original residue to be randomized. The four
projection simplexes remain separate. An absent label has zero event
marginals and can use any one of its legal projections.

Finally retain only201's four already proved actual CRT bounds:

    sum_(k,S containing {0,1}) x_(k,S)<=1/675,
    sum_(k,S containing {1,2}) x_(k,S)<=1/675,
    sum_(k,S containing {0,3}) x_(k,S)<=1/2025,
    sum_(k,S containing {2,3}) x_(k,S)<=1/2025.             (JS5)

The common raw measure is dominated by Haar3 times Haar5. The
intersection of a selected pure3 cylinder with either five cylinder
has the displayed cap; incompatible residues give an empty event.
No independence of the survivor is used. There are425 nonnegative
variables,132 inequalities and four equality normalizations in total.
No additional pair or higher-intersection cap is assumed.

## 2. The original threshold prefixes determine the objective

Keep204's original head

    B=1+I3+I9+I5+I15+I45

and its six independent positive-seven projections. At rectangle k,
let m_k count21,35,63,105, and ell_k count147,245. The complete
seven bridge is, with q=(t-v)_+, M1=1+m and M2=1+ell,

    g_t(v;m,ell)
      =(6/35)*(M1-q)_+
       +(6/245)*(M2-(q-M1)_+)_+
       +1/[5*7^(2+(q-M1-M2)_+)].                        (JS6)

This retains every unit7^e and the same complete complementary tails
as204. Let kt=min(t-1,4) for1<=t<=8, so k1=0. The actual selected
contribution at threshold t is the prefix count

    n_t(S)=|S intersect {0,...,kt-1}|.                   (JS7)

For nonnegative coefficients a_t, the single raw objective is

    V(x)=sum_(k,S) x_(k,S)*sum_t a_t*[
        w_k*(B_k+n_t(S)-t)_+
        +g_t(B_k+n_t(S);m_k,ell_k)].                    (JS8)

It is essential to use n_t(S), not the full|S|at every threshold.
In particular the first hinge has no selected label in its prefix.

For any feasible-dual upper U on(JS8), the complete original hinge
combination is bounded by

    sum_t a_t*integral(A-t)_+ dmu
         <=U+sum_t a_t*(R_kt+2669/88200)-a1*C(layout).  (JS9)

The R_kt are the original complete omitted zero-seven tails. The
positive-seven remainder2669/88200 is204's full remainder after
retaining147 and245. The forbidden-family mean credit C(layout) is
the same original109 credit, used exactly once. Since k1=0, joining
the selected indicators changes none of that credit's hypotheses.

Every actual source supplies a feasible point by(JS1)--(JS5), and
(JS8) is its actual joint bridge integral. This is why a feasible
dual, without a primal optimum or an attainment assertion, suffices.

## 3. Rational duals separate proposal generation from verification

Write the inequalities Ax<=b and normalizations Ex=1, with x>=0.
A rational certificate consists of y>=0 and unrestricted z such that

    A^T y+E^T z>=c.                                    (JS10)

Then c^T x<=b^T y+sum_j z_j for every actual feasible x. The canonical
checker reconstructs all constraints and all425 objective entries
and checks(JS10) and its value using exact fractions.

The separate proposal program uses SciPy only to suggest dual
coefficients. It quantizes them to a common rational denominator,
then repairs feasibility exactly:

- Increase each z_j enough to dominate every lambda column in its
  normalization group. These changes touch no raw-mass column.
- For each rectangle, increase its source-cap dual by the positive
  maximum remaining deficit over its16 raw columns. That source-cap
  row has coefficient1 on exactly these columns and zero on lambda.

The repaired certificate is checked before it is retained. Exact
optimality is unnecessary. The ordinary canonical command below
neither imports SciPy nor runs a numerical optimizer. The stored
objects are rational dual certificates, not numerical solver claims.

## 4. Three earlier complete bounds certify every omitted branch

The original head has12500 choices. There are10 independent21/35
projections,50 independent63/105 projections, and10 independent
147/245 projections. Thus each heavy cost has62,500,000 containing
choices, with every original modulus keeping its own labels.

For a given branch, let V2,V4,V6 denote201's two-projection upper,
201's four-projection upper, and204's six-projection upper. They bound
the same complete cost. The candidate upper for this branch is

    min(V2,V4,V6,Vjoint).                               (JS11)

A fully evaluated controller supplies an initial candidate. At each
subsequent stage, if a previously certified upper is no larger than
the maximum accepted candidate already found, the entire family of
remaining choices is safely covered by that bound. Otherwise the
next stage is evaluated. The running maximum is updated only with
(JS11), never with Vjoint alone. A final rational check confirms that
every pruned upper is below the resulting maximum.

The canonical reconstruction counts all branches and records a digest
of their exact decisions. Only seven joint-dual evaluations per cost
are needed, including the initial controller; every other containing
choice is accounted for by a complete earlier bound. This pruning
changes evaluation cost, not the mathematical domain.

## 5. Complete costs and the full consumer

For each original heavy function f, the checker reconstructs

    f(v)=f(1)+sum_(t=1..8)a_t*(v-t)_+, all integer v>=1,

including every finite transition, its eventual slope and constant.
All a_t are nonnegative. The mass term f(1)*53/360 is kept explicitly.
Each cost has its own branch scan and its own original test; their
maximizing residues are not required to be shared across tests.

The52-cost consumer starts from207, replaces the two improved heavy
entries, and applies only the existing exact whole-load majorants.
It preserves207's improved linear and quadratic costs, complete square,
negative mass term, independent AP11 and AP13 losses, and complete
count remainder. Its denominator remains

    1423627769987/17084377926000>0.                      (JS12)

All source inequalities apply to finite original prefixes with the
same nonnegative complete cap remainders. The inherited uniform
geometric first-moment tail control passes to arbitrary exponent
heights and diagonal limits. The first-beta permutations and the
second face orientation transport every source row and independent
residue profile together, as in201/204. No finite-height assumption
is introduced by the finite LP.

The two scans evaluate658543 and672643 original source-capacity LPs,
respectively. Each uses seven joint certificates, with six distinct
duals after exact objective deduplication. The stored twelve duals
are each verified in all425 columns. These counts describe the
complete certified scan, not a sampling experiment.

The [canonical helper](../../frontier/source-budgets/joint_selected_source_comparison.py)
and [certificate](../../certificates/source_norms/source-budgets/joint_selected_source_comparison.json)
retain the exact bounds, all rational duals, source pins, complete
branch counts and52-cost consumer. The
[proposal generator](../../frontier/cover-geometry/propose_joint_selected_duals.py)
exists for regenerating numerical suggestions followed by exact repair.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/joint_selected_source_comparison.py --check
```
