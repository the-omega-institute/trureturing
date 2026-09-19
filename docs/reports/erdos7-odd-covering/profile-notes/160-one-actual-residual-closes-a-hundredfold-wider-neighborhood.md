[Index](../marked_head_profile.md) · [Actual packing guards](117-the-actual-slot-defects-share-a-stronger-packing-polytope.md) · [Independent indicators](152-independent-shallow-indicators-sharpen-the-complete-mean-and-square.md) · [Exposed source prices](156-exposing-each-loss-gives-exact-rational-joint-price-bounds.md) · [Complete source comparison](157-a-signed-tail-comparison-covers-the-one-over-twenty-seven-neighborhood.md) · [Complete seven-containing pair prices](158-the-seven-containing-pair-tails-have-one-exposed-source-price.md)

# One actual residual closes a hundredfold wider neighborhood

For both actual K orientations and every admissible first-beta
distribution, the complete original comparison is below509 on

    sigma<=1/27, 0<=rho<=1/1000, 0<=r<=1/520.       (RS1)

All52 original independent tests, all five denominator objectives,
the complete square and every original infinite tail are retained.
The proof uses two closed residual intervals, with the same actual
rho in the cost bounds, the packing budget and the source-mass floor:

| Actual residual interval | Complete comparison upper |
| --- | ---: |
|0<=rho<=1/20000|482.0442111467803...|
|1/20000<=rho<=1/1000|508.9706821709662...|

The uniform upper in(RS1) is the exact rational number

    2055988989348894746208694371953111463993946420129607181271
    /4039503769803141973441446174858683760305244047010000000.

This expands158's residual radius by a factor100 at the same source
and slot-loss radii. It is an ordinary continuous-source result with
exact rational certificates. It is not a global K bound, a Lean
theorem or a resolution of unrestricted Erdos7. The complement of
(RS1) still requires a separate complete comparison.

## 1. Reprove the actual geometry on the wider domain

Put delta=1/27, rho0<=1/1000 and

    rbar=min(1/520,5rho0), hplus=1/2+delta/18,
    h1min=1/3-delta/18, etamin=1/9-delta/18.

The minimum uses two actual hypotheses: r<=1/520 in(RS1), and
r<=5rho from the shared defect budget. It does not infer a smaller
actual rho from the slot-loss cap. By156,

    Delta=(u_a+u_z+u_b)/4<=3delta/[4(3-2delta)].   (RS2)

The same bound applies to the availability norm in the source
projection. Combining(RS2) with117's total root1 deficit bounds,
the five actual91 gaps have the following lower bounds at the
largest rbar=1/520:

| Actual gap | Lower bound |
| --- | ---: |
|h/5-r|51/520|
|h1/5-r|8129/126360|
|min_(c>=2)eta_c/5-r|2513/126360|
|h1(1/10-Delta)-2r|52181/1996488|
|(h1-h0)/5-r|773/25272|

Hence G>=2513/126360>0, stronger than91's old241/22500.
Every actual cell still has eta_c>=1/18. The retained-deep
objectives have coefficient floor

    3/5-18(13/1215)=11/27>0.                     (RS3)

Also z<=3/4+delta/4<4/5, and the source budgets that force the
distinct first labels exceed1/4-3delta/4>1/20. The actual first-beta
label still has beta_L>=1/5-b, where b is the deficit of the total
root1 beta mass. No single beta cell is assumed to carry all that
mass. Thus117's general first-slot proof applies, including the
closed r endpoint. The old numerical r<1/2500 wrapper is not used.

The134 simplex uses its original, possibly smaller, gap g. On
these two rectangles it is positive and no larger than the above
G. Therefore y>=0 and

    sum y<=rho0-g(q5+q15),
    y=(E5-gq5,E15-gq15,E27,Ege4,E5deep,E15deep,omega),
    r<=5y1, r1<=5y2                               (RS4)

remain valid. In particular these are shared coordinates for one
source, not independent allowances for separate tests.

## 2. Combine the heavy source-norm prices before evaluating them

Use151's signed heavy branch expression C*s+G_branch. Its complete
identical raw-zero block cancels before taking a source price.
Thus no C times a source-mass norm is charged again. For a fixed
original branch define v=max_i[f(b_i+1)-f(b_i)],
k=max_i[C-f(b_i)], and c=max_i[(f(b_i+1)-f(b_i))*c5_i].
All are nonnegative.

Let R_n,R_eta,R_d be the full raw-source prices after subtracting
the exact common zero block; let Z_d and Z_plus be the zero-block
availability and positive-five pure prices. The142/151 formula
collects into the three nonnegative coefficients

    L_n=R_n+||psi||infinity+2k/5,
    L_eta=R_eta+||correction||infinity+Z_plus+2c/25+3k/20,
    L_d=R_d+Z_d+k/90+2s0(v+k), s0=13/1215.       (RS5)

The last term in L_d pays both the common2s0*v*D marker error
and the separate2s0*k*D selected-deep shift. They are on the
same exposed source-price vector, without dropping either term.
Apply156's exact support once to norm_prices(L_n,L_eta,L_d).

For157's unchanged improved caps v0,v1 and three source budget
increments dN, define

    cap=delta/90+v0/6+v1/3,
    budget=sum dN+delta/45+3rbar,
    B_nonH=14delta/225+cap+budget+16delta*hplus/135,
    B_H=2delta/225+18s0*rbar.                    (RS6)

The complete branch error is at most

    support156(norm_prices(L_n,L_eta,L_d),delta)
      +2delta*(k/4+c/10)/5+v*max(B_nonH,B_H)
      +max(v,hplus*v/(5G))*rho0.                (RS7)

The original pointwise91 proof depends here on the actual gap and
nonnegative coefficients already re-established in section1.
Its remaining allowance is rho-(r+r1)/5<=rho<=rho0. This is one
residual term. The helper evaluates all100 original branches for
each of the two heavy tests and takes the maximum error afterwards.
For the outer rectangle the two G errors are0.4392864934762260...
and0.3503251913017230...; their weighted sum is0.7483969563895111....

## 3. Extend the individual indicator formula, retaining all tails

The public152 wrapper explicitly has rho0<=1/100000, while139's
public H1 wrapper has rho0<=1/2600. Neither is invoked outside its
stated domain. Instead the following derivation reuses their lower
level exact formulas on the newly proved domain.

152 SI2 is the pair of actual H-column identities; it has no rho
cutoff. SI3--SI7 use delta's source bounds, positive h1min and
actual r,r1. Their cap perturbation is Ubar+r*a, with the full
delta*r contribution already retained in SI4. SI8--SI12 use only
the indicator support and delta<=1/27. Both numerator inequalities
that give Cbar>=1+tbar and Cbar>=kbar stay positive. SI13 uses the
source loss and the signed slot migration r/h<=10y1. Finally SI14
is(RS4), already valid by section1. Consequently the exact SI15
bound remains valid, separately for all47 indicators and all three
first-beta cells:

    C_phi<=Fbar_phi-A_phi*+alpha_phi*delta
                +rho0*max(lambda_phi,B_phi/g).  (RS8)

For non-3 indicators the finite dual's5R_phi and the slot migration
10dH add on y1. For modulus3, the H identities instead contribute
1 on y1 or2 on y2. Each layout's own maximum is evaluated before
taking the maximum for its modulus. A modulus cap may also be
clipped by1/modulus. No claim that SI16's old maximizing branch
persists to the wider domain is needed.

The four complete tails are rebuilt directly with errors
(kbar*rho0,rho0+delta/240,rho0,rho0). For each family,

    sum_(n>=b) min(e,H*p^-n)
       =(N-b)e+H*p^-N/(1-1/p),                 (RS9)

where N is its exact first crossing; for e=0 the error is zero.
The corresponding square uses the complete weighted error
e*(N^2-b^2)+H*sum_(n>=N)(2n+1)p^-n. These are full infinite sums,
not tails cut at N. The raw positive-seven source bounds from
139 AD13 and143 depend on delta alone. Thus152 SI18--SI20 apply
with the newly calculated independent caps and exact crossings.

At rho0=1/1000 the resulting complete values are

    H1<=0.5383787212312245...,
    Q<=5.379777606099303... .                    (RS10)

Their five shallow caps, in modulus order(3,9,5,15,45), are
(0.08857912712442158...,0.06161808697709441...,
0.06462886991738306...,0.03845168656118736...,
0.02071197510390434...). Every exponent tail and every LCM
category is retained.

## 4. Use one actual residual to close the outer shell

For each rectangle rho<=rho0, recompute all26 finite objectives:
five denominator objectives, H2, eleven mean costs and nine joint
quadratic costs. All125000 original heads are retained at each of
the three q vertices. Keep every selected operator, all infinite
cost tails and the independent original test labels. The complete
old-old factorial pair tail is unchanged. The other two pair tails
use158's shared source price, as does its complete positive-seven
complement. The two raw81 controllers remain unchanged.

Write A=53/360, cE=1-1/614922, and let CH be the weighted heavy
barrier. With157's cS,cQ,C0 and row40 weight w40, put

    M=cS+CH+w40+cQ.

The aggregation exposes a signed endpoint N0 and a denominator
endpoint d0 satisfying, on the whole rectangle,

    numerator<=N0+M*(S-A)-CH*(s-1/4),
    denominator>=d0+cE*(S-A).                   (RS11)

These follow from the same actual source. In particular N0 is not
an unconditional numerator upper. By146 and151,

    S-A>=rho, s>=1/4.                          (RS12)

On an honest shell rho>=rho_min, if
D_S(T)=(T-C0)cE-M>=0, then

    (T-C0)*denominator-numerator
       >=(T-C0)*d0-N0+D_S(T)*rho_min.           (RS13)

Thus take

    T=C0+(N0+M*rho_min)/(d0+cE*rho_min).        (RS14)

Both denominators and both D_S(T) are checked positive. For the
outer rectangle, discarding the last term in(RS13) would give
509.2469821662041..., which does not prove the target. At T=509,
the endpoint term is-0.01870592241098636..., while
D_S(509)=418.5572100993014.... The actual shell lower bound
rho_min=1/20000 gives the positive signed margin

    118429480904518273001731049958570001422799798482818729
    /53300081233340241898400808280918144703349548400000000000
       =0.002221938093978707... .               (RS15)

The inner rectangle is separately proved with rho_min=0 and
rho0=1/20000. It has comparison482.0442111467803... and margin
2.117707248648729... at509. The two closed intervals meet exactly,
so no intermediate residual is omitted and no positive lower
bound is applied at rho=0.

## 5. Exact certificates and reproducibility boundary

The two source boxes have19,500,000 evaluated original heads in
total and624 independent rational LP comparisons. The recorded
heads preserve every vertex, coefficient, maximizing witness and
integer-objective digest. The producer is
[residual_shell_k_comparison.py](../frontier/residual_shell_k_comparison.py).
Its [original-head data](../certificates/source_norms/residual_shell_original_heads.json)
and [complete certificate](../certificates/source_norms/residual_shell_k_comparison.json)
use the repository's multipart certificate reader and writer.

The ordinary check validates the pinned scan/source identities and
reconstructs every complete support, both heavy branch tables, all
indicator caps, complete tails and both signed comparisons. It does
not silently count a replay as a fresh full head enumeration. The
optional rescan repeats every original finite objective and checks
its complete digest against the recorded scan:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/residual_shell_k_comparison.py --check
python3 -I -O docs/reports/erdos7-odd-covering/frontier/residual_shell_k_comparison.py --check --rescan
```

These exact evaluations support the continuous inequalities above;
they do not assert that any relaxed maximizing source or head is
attained by an actual covering family.
