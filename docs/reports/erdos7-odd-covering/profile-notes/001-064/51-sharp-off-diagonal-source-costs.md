[Index](../../marked_head_profile.md) · [Actual source endpoints](50-sharp-source-survival-endpoints.md) · [Cell-cost source comparison](42-whole-hinge-absorption-sharpens-actual-survival.md)

# Sharp off-diagonal source costs and a two-baseline Jensen correction

At source parameter theta404, a single sequence of actual finite
original-label families and original test families simultaneously
approaches the following sharp source-cost values:

| Cost | Sharp limiting supremum |
| --- | --- |
| psi4 | 1148669/7717500 |
| psi5 | 179422823/1620675000 |
| g4=psi4-omega*min(1,h4) | 382661/2572500 |
| g5=psi5-omega*min(1,h5) | 179394011/1620675000 |

Here omega=(1/5,2/5,0,0,0) is cell dependent, the integrals are against
the raw actual35 source Lambda, and psi_t is the complete original
zero7 cost from the existing comparison. The sharp supremum means:
every sequence of finite source families approaching theta404 has
limsup of the indicated test integral at most the stated value,
while the explicit sequence below realizes all four limits together.

The same forbidden families have normalized actual357 survivor mass
S tending to D404=3/20, and their shallow-carrier mixtures tend to the
point mass at(0,1). Thus these source costs are compatible with the
actual mass and carrier endpoint. No attainment of full357 test costs,
deletion clips, or a final K comparison is asserted.

The psi4 value is strictly below its previous source envelope:

    6975217/46305000-1148669/7717500=83203/46305000.

The other three values equal their existing complete source envelopes.
These are ordinary mathematical results with exact rational evaluation;
no Lean verification is claimed.

## 1. A universal correction retaining two original five blocks

Retain the source hypotheses and measures of profile31: eta is raw
pure3 survivor measure, lambda is the ternary marginal of Lambda,
lambda(cell l)=n_l, eta(cell l)=eta_l, and

    0<=d lambda/d eta<=d_l, d_l>=1/4.

Let g_l be fixed, nonnegative increasing convex cell costs with affine
tails. The same argument applies to scalar costs. Write

    p_n=4/5^n, n>=2,
    q_(n,l)(v)=[g_l(nv)-g_l(n)]/n,
    bar_g_l(v)=sum_(n>=2)p_n*q_(n,l)(v)-g_l(v)/5.

Let A0 and A1 be the original zero-five and first-positive-five
ternary test blocks, and b,c their shallow baseline vectors, each in
the existing ten-baseline set. Missing test labels can be completed
as in the inherited source theorem. All statements below keep each
original block's residues fixed through every auxiliary outcome.

For integers u,v>=1 define the nonnegative pointwise Jensen gap

    J_l(u,v)=[g_l(2u)+g_l(2v)]/2-g_l(u+v).

Let E0,E1 be the unions of the deep ternary test cylinders of A0,A1.
Each has eta mass at most sum_(a>=3)3^-a=1/18. Outside E0 union E1,
the two block values are exactly b_l,c_l. Therefore

    integral_eta J_l(A0,A1)
      >=sum_l eta_l*J_l(b_l,c_l)-max_l J_l(b_l,c_l)/9
      =: L_g(b,c).                                 (1)

The integral notation on the left uses the corresponding cell cost
on each cell. On the exceptional union its integrand is still
nonnegative; discarding it loses at most the displayed baseline
maximum times1/9. The lower bound L_g may be negative. No positive
part is needed or taken.

For a cell cost u_l, define the complete deep increment sum

    T(u_l;a)=sum_(k>=0)3^(-k-3)*[u_l(a+k+1)-u_l(a+k)].

Use the inherited fixed-baseline source and pure bounds

    Z_g(b)=sum_l[n_l*g_l(b_l)+eta_l*bar_g_l(b_l)]
             +max_l T(d_l*g_l+bar_g_l;b_l),
    P_eta(u;c)=sum_l eta_l*u_l(c_l)+max_l T(u_l;c_l).

The combined increment cost is increasing convex because
d_l*g_l+bar_g_l=(d_l-1/5)*g_l+sum_n p_n*q_(n,l).
Thus the inherited deep-prefix bound applies to these exact sums.

Keep the same c for the original A1 through the complete positive5
mixture, and define

    R_g(c)=sum_(n>=2)p_n*[
       sum_l eta_l*g_l(n)+P_eta(q_n;c)
                           +(n-2)*max_a P_eta(q_n;a)].

The corrected source upper bound is

    F_g^J(theta)=max_(b,c)[Z_g(b)+R_g(c)-(4/25)*L_g(b,c)].    (2)

For every actual finite original35 test T,

    integral_Lambda g(T)<=F_g^J(theta).                    (3)

To prove(3), start with the same pure5 cylinder comparison as the
existing source theorem. In its n=2 term use the exact identity

    g(A0+A1)=[g(2A0)+g(2A1)]/2-J(A0,A1).

This subtracts p2 times the true integral of J; p2=4/25. For every
other n use the original Jensen upper bound. Centering at g_l(n)
then gives precisely Z_g and the positive-block costs above. Apply
(1), retain the one A1 baseline c in every n term, and only then
maximize over the two actual shallow baselines. The remaining n-2
positive blocks keep their independent old upper bounds. No source
payment, deletion loss, or normalization is charged a second time.

### Complete tails and continuity

Take a common integer cutoff K>=2 such that
g_l(v)=sigma_l*v+kappa_l for all v>=K. For n>=K,
q_(n,l)(v)=sigma_l*(v-1). Put

    T0=sum_(n>=K)p_n=5^(1-K),
    T1=sum_(n>=K)n*p_n=T0*(K+1/4),
    P_aff(c)=sum_l eta_l*sigma_l*(c_l-1)+max_l sigma_l/18.

The entire tail of R_g(c), including its constants, is

    T1*sum_l eta_l*sigma_l+T0*sum_l eta_l*kappa_l
      +T0*P_aff(c)+(T1-2*T0)*max_a P_aff(a).           (4)

Every deep sum T has a finite affine entrance and an exact geometric
tail. Thus(2) is a finite maximum of continuous expressions, with no
height cutoff imposed on the actual labels. It is separately convex
in the inherited source parameter groups: the original fixed-baseline
upper expressions are separately convex, and for fixed b,c the new
subtraction is affine in eta. This observation does not assert that
the corrected comparison dominates the old comparison at every
parameter; both remain valid upper bounds.

## 2. The same actual source and test families

Use note50's off-diagonal finite source family of height N>=3.
In its notation, with C0=[0]9,C1=[3]9,C2=[1]9,C3=[4]9,C4=[7]9,

    T_a(c,j)=[c+j*3^(a-1)]_(3^a),
    F_(j,b)=[j*5^(b-1)]_(5^b).

Its source labels are[2]3,[6]9,T_a(0,1) for pure3, F_(1,b) for pure5,
root1 x F_(2,b) for3*5^b, C2 x F_(3,b) for9*5^b, and
T_a(4,1) x F_(3,b) for all deeper mixed35 labels. All displayed
exponents are at most N. The pure7 and mixed7 labels are exactly the
off-diagonal construction of note50.

Write

    t_N=(1-3^(2-N))/18, q_N=(1-5^-N)/4,
    k_N=(1-7^-N)/(5+7^-N).

The source parameters have beta in C2, late deletion in C3, and
approach theta404. Their raw source mass is5/9-t_N-q_N. With the
same seven labels the actual normalized survivor mass is

    S_N=5/9-t_N-q_N-k_N*(1/3+2*q_N/3)->3/20.

For the original test at each modulus3^a5^b,0<=a,b<=N, choose its
CRT coordinates to be7 modulo3^a and4 modulo5^b. The unit test is1.
Its complete test load factors exactly as

    Z_N=B3_N*B5_N,
    B3_N=1+sum_(a=1..N)1_[7]_(3^a),
    B5_N=1+sum_(b=1..N)1_[4]_(5^b).                (5)

These test residues are independent of the forbidden residues. Every
positive5 test block is the same original B3_N. On the five surviving
cells the shallow ternary baseline is

    b=(1,1,2,2,3),

the existing baseline9. Its deep test cylinders form one nested chain
inside C4. There is no pure3 or late source deletion in C4, and in the
limit lambda restricted to C4 equals(1/2)eta there. Every cylinder
[4]_(5^b) lies in F_(4,1), which is entirely free of all five-coordinate
source deletion across the pure3 survivor.

### Direct infinite integral

Let B3,B5 be the almost-everywhere limits of(5). For any of the four
costs in the opening table define

    V_l(v)=sum_(b>=1)5^-b*[g_l((b+1)v)-g_l(bv)],
    H_4(v)=d4*g_4(v)+V_4(v).

Here subscript4 denotes the cell, not the hinge threshold. The free
nested five cylinders and the nested ternary chain give directly

    I(g)=sum_l[n_l*g_l(b_l)+eta_l*V_l(b_l)]
          +sum_(k>=0)3^(-k-3)*[H_4(4+k)-H_4(3+k)].   (6)

This identity integrates the explicit original test against its
actual source. It does not substitute a comparison measure. Each
sum has an exact affine geometric tail: if g_l(v)=sigma_l*v+kappa_l
above K, then the five tail starting at b=m, mv>=K, is
(5^(1-m)/4)*sigma_l*v, and the eventual H_4 increment is
(d4+1/4)*sigma_4.

## 3. Exact matching upper bounds

At theta404, direct evaluation of(6) and the complete source upper
bounds gives

| Cost | Old F_g | Corrected F_g^J | Actual I(g) |
| --- | --- | --- | --- |
| psi4 | 6975217/46305000 | 1148669/7717500 | 1148669/7717500 |
| psi5 | 179422823/1620675000 | 179422823/1620675000 | 179422823/1620675000 |
| g4 | 382661/2572500 | 382661/2572500 | 382661/2572500 |
| g5 | 179394011/1620675000 | 179394011/1620675000 | 179394011/1620675000 |

The corrected bound evaluates all100 shallow-baseline pairs. For
psi4 and g4 its maximizing pairs at theta404 are(9,7),(9,8),(9,9);
for psi5 and g5 the maximizing pair is(9,9). The actual witness uses
(9,9), with Jensen gap exactly zero. The strict psi4 improvement
arises because the old independent zero-block and positive-block
maxima cannot keep their old values once this gap is retained.

The g4 and g5 source envelopes are also saturated directly at every
step: their zero5 maximizing baseline is9 with deep cell4, and the
same baseline/deep choice maximizes each positive pure term. The
values of P_eta(q_n;baseline9) for g4 at n=2,3,4 are
47/210,257/630,1/2. For g5 at n=2,3,4,5 they are
73/441,199/630,181/420,1/2. The complete affine-tail value is1/2 in
both cases. No different original block is chosen for these terms.

### Finite-family convergence and sharpness

The forbidden35 survivor sets decrease with N, while Z_N increases
almost everywhere to B3*B5. The latter is Haar-integrable: its mean
on the full product space is(1+1/2)*(1+1/4)=15/8. All four costs are
nonnegative and bounded by their argument. Dominated convergence
therefore proves that the actual finite integrals tend to(6).

The finite carrier mixture is

    pi_(0,1)=1-7^-N, pi_empty=7^-N.

If the absorbed costs use its actual omega_N=(1-7^-N)*omega, the
clipped factor is at most1, so their pointwise difference from the
fixed limiting costs is at most(2/5)*7^-N. Their raw integrals have
the same limits. A concentrated finite mixture is not assumed.

Conversely,(3) applies to every finite source and test family.
Continuity of F_g^J at theta404 bounds every approaching sequence's
limsup by the table value. The construction supplies the matching
limits, proving sharpness for all four costs simultaneously. For g4,
g5 and psi5 the old F_g gives the same upper limit already.

## Scope

The attained objects are source35 integrals, the source parameter
limit, actual total survivor mass, and the shallow-carrier limit.
The positive original7 blocks have separately chosen original residues
within a complete357 test. Their independently maximized source bounds
cannot be jointly attained by choosing(5) without another argument. In particular, subtracting the
psi4 saving again from the positive7 complement would double-count a
zero7 improvement. This result supplies no new global K value or
resolution of unrestricted Erdos #7.

The independent standard-library checker
[source_cost_endpoint_attainment.py](../../frontier/source-budgets/source_cost_endpoint_attainment.py)
reconstructs actual forbidden-source masks at heights3,4,5 and checks
twelve original-test cost integrals against the nested-cylinder formulas.
It evaluates both complete geometric tails in(6), all400 baseline pairs
for the four corrected bounds, and the finite carrier-mixture cost error.
The sharp fractions and maximizing pairs agree with a separate
raw-cost evaluation of the same finite maxima and tails. These exact
calculations verify the numerical premises; the universal bounds and
convergence follow from the proofs above.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/source_cost_endpoint_attainment.py
```

The program is read-only by default and accepts `--output PATH` for an
exact rational JSON result. No full357 extremum or global K value is
computed by this checker.
