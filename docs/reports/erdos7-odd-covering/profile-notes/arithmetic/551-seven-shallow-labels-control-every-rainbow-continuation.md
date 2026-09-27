# Seven shallow labels control every rainbow continuation

Keep exactly the 192 original classes through prime 11 from
[report548](548-rainbow-transport-forces-a-next-row-saving.md), including
its original color table, pure heights N=4 and first-11 heights E=4.
Allow an arbitrary finite Q-smooth continuation, Q={5,7,11,13,17,19},
with largest primes 13,17,19, at most two originals per numerical modulus, arbitrary globally fixed
phases and no bound on the exponents. These 192 classes remain ALL
originals whose largest prime is at most 11.

The ONE final actual PA law has complete query norm strictly below
257/51. In particular the factorization, nested-chain and first-root
restrictions on the 13-row in report548 can all be removed.
Section 6 extends this conclusion to every finite N,E>=4 in the same
rainbow construction, with one uniform positive margin. The prefix then
has 4N+2N^2+36E classes, still comprising all originals through prime 11.

At the finite anchor N=E=4, the quantitative step is a uniform bound on
every complete old query L under the same actual unnormalized lambda11:

    integral (L-2)_+ dlambda11 <= Hstar,
    Hstar=14304757879004833932649/79759312825447505250000
         =0.17934906122261435... .                    (SL1)

Each old numerical label 5^a*7^b*11^c can choose its own arbitrary phase,
without compatibility with another label's coordinate chains. The proof
uses a four-label union certificate and three further individual deficits.
Every other query height is paid by an exact convergent cap sum.
This is an ordinary proof with exact finite verification, not Lean
verification or arbitrary-family two-copy closure.

## 1. The unchanged source and unconditional cylinder caps

Use the actual source of report548, with

    w5=313/625, w7=1601/2401,
    sigma=H5|S5 tensor H7|S7,
    eta=the actual mixed5/7 union restriction,
    lambda0=sigma-eta.

For each old point let G be the active colors in the original table and
K=|G|. Its allowed 11-fraction and actual capped density are

    g_K=1-1464*K/14641,
    h_K=min(5/3,1/g_K), s_K=h_K*g_K<=1.

All calculations below use this same lambda11=lambda0 K11, with no
normalization or replacement of original phases. In particular the table
is precisely the one printed in report548; the root colors are not
independently changed between different phase comparisons.

For every cylinder at numerical label d=5^a*7^b*11^c define

    P_d=r5(a)*r7(b)*r11(c),
    r5(0)=w5, r7(0)=w7,
    rp(e)=p^(-e) for p=5,7 and e>=1,
    r11(0)=1, r11(c)=(5/3)*11^(-c) for c>=1.

Then lambda11(C_d)<=P_d for EVERY phase. If c=0, integrate the actual
11-kernel first and use s_K<=1 and lambda0<=sigma. If c>0, use h_K<=5/3
and the Haar mass 11^(-c), then again lambda0<=sigma. A positive-depth
pure-survivor cylinder has mass at most p^(-e). These arguments do not
require the phases to factor as the numerical label varies.

The complete nonunit cap sum is

    Psum=sum_(d>1)P_d
        =(w5+1/4)*(w7+1/6)*(7/6)-w5*w7
        =85599701/216090000.

The comparison union mass and unchanged PA 13-hinge charge are

    U_PA=w5*w7-(w5-1/5)*(w7-1/7)*(28/33)
        =9914617/49520625,
    F13=Psum-U_PA=93139019/475398000.                 (SL2)

## 2. A literal stability identity keeps the joint union

Complete a query by including the unit and one cylinder per nonunit
numerical label. Write L=1+sum_(d>1)1_(C_d). Pointwise,

    (L-2)_+=sum_(d>1)1_(C_d)-1_(union_(d>1)C_d).

The cap sum is finite, so the indicator sum is finite lambda11-almost
everywhere, and Tonelli and monotone convergence apply. Consequently

    F13-integral(L-2)_+ dlambda11
      =sum_(d>1)[P_d-lambda11(C_d)]
          +lambda11(union_(d>1)C_d)-U_PA.            (SL3)

Every term in the displayed sum is nonnegative. A finite set of labels
therefore suffices if it retains both its actual deficits and a lower
bound for the SAME actual union. One cannot replace that union by
independently selected endpoint phases.

For a finite query, add arbitrary fixed phases at all missing labels.
The completion increases its hinge, and the complete cap sum bounds the
limit. Thus SL3 produces an all-height upper bound for every finite query;
no conclusion about deep heights is inferred from shallow enumeration.

## 3. Jointly enumerate the phases at 5,7,11,25

Write A=C5, B=C7, C=C11, D=C25, and set

    Delta0=sum_(d=5,7,11,25)[P_d-lambda11(C_d)]
              +lambda11(A union B union C union D)-U_PA.

The four caps are

    P5=1601/12005, P7=313/4375,
    P11=501113/9904125, P25=1601/60025.

There are exactly 5*7*11*25=9625 phase tuples, including roots that only
partly survive or do not survive. Direct exact integration of the original
finite boxes gives the following complete minimum table. Its row labels
refer to the ORIGINAL report548 colors.

| Phase modulo 11 | Minimum Delta0 over phases at 5,7,25 |
| ---: | --- |
| 0 | 18373149183/549266265625 |
| 1 | 183789428011379/6433555769265625 |
| 2 | 473425299883862959/33911272459799109375 |
| 3 | 146322207570981653/11303757486599703125 |
| 4 | 18373149183/549266265625 |
| 5 | 183789428011379/6433555769265625 |
| 6 | 432074887278761359/33911272459799109375 |
| 7 | 143565513397308213/11303757486599703125 |
| 8 | 194267841158458278/11303757486599703125 |
| 9 | 73501141702295834/6782254491959821875 |
| 10 | 692859112857588722/33911272459799109375 |

Hence every phase tuple satisfies

    Delta0>=D0=73501141702295834/6782254491959821875
                =0.010837272737174554... .            (SL4)

The global minimum occurs at phases 4 modulo5, 6 modulo7, 9 modulo11,
and any of 14,19,24 modulo25. The last cylinder is contained in the
chosen 5-cylinder; all four terms still retain their distinct numerical
identities in Delta0.

The finite calculation uses inclusion-exclusion on the ACTUAL joint
measure. In particular, C25 is either contained in C5 or disjoint from
it, according to its residue modulo5. This is a statement about the
chosen phases in each tuple, not a nesting hypothesis on the query.

## 4. Three more labels have unavoidable individual deficits

Exhausting every phase at each of 55,77,121 under that SAME lambda11 gives

| d | P_d | max_phase lambda11(C_d) |
| ---: | --- | --- |
| 55 | 1601/79233 | 38566276513/2175193453125 |
| 77 | 313/28875 | 62201840963/6752727515625 |
| 121 | 501113/108945375 | 40822590747784381/13732664053968234375 |

At 55 the maximum uses 4 modulo5 and 9 modulo11. At 77 it uses 6
modulo7 and 9 modulo11. At 121 it uses any 9+11t, 0<=t<=10, or 109.
The resulting phase-independent deficits are

    d55=1795392204/725064484375,
    d77=40320705344/24760000890625,
    d121=22343160731580244/13732664053968234375,
    D1=d55+d77+d121=6054681566538784/1056358773382171875.

These three labels are disjoint from the four in Section 3. Their phases
may be chosen independently of those four phases. The maximum for each
label supplies a universal lower bound for its deficit, so no common
maximizing phase assignment is assumed.

Retain these seven deficits in SL3 and lower-bound the full union by
the four-label union. All omitted deficits are nonnegative. Thus

    F13-integral(L-2)_+ dlambda11 >=D13=D0+D1,
    D13=27531793821227986562/1661652350530156359375.

Subtracting D13 from F13 proves SL1. It remains below the required
13-only threshold by a strict rational margin:

    F13-4*c0/(T-2)-Hstar
      =2253406402672999193988368222017
         /1395034104734293274541298008000000>0,
    T=257/51,
    c0=6168733163201163811/542935350932041267200.      (SL5)

## 5. Every actual 13-row and the final common-law bound

For each actual 13-exponent e, assign its at-most-two originals per
old cofactor to two slots and complete missing labels by arbitrary fixed
phases. There is no relation required between distinct slots or current
exponents. Each completed query L_(e,j) satisfies SL1.

The actual fibre union is bounded by the weighted sum of its original
indicators. The same CP5 convexity argument used in report548, with
beta_(e,j)=6/13^e and sum beta=1, now gives

    Loss13 <=(1/4)*sum_(e,j) beta_(e,j)
                                integral(L_(e,j)-2)_+ dlambda11
            <=Hstar/4.

Therefore the absolute saving in the actual 13-row is

    S13=F13/4-Loss13>=kappa=D13/4,
    kappa=13765896910613993281/3323304701060312718750
          =0.004142231347676887... .                  (SL6)

This is a saving in the actual kernel, not only a chosen comparison
completion. For every later row use S_q=a_q F_q-Loss_q>=0. The unchanged
PA mass identity and report544's final-query estimate then give, exactly
as in report548,

    mu=(T-2)*kappa-c0
       =2253406402672999193988368222017
          /1836044886230940825847901894400000>0,
    R_Q(rho)<=T-mu<T, Q={5,7,11,13,17,19}.            (SL7)

All the other favorable terms, including the pure deficits, 1/12-m,
the later row savings and final JL, can be omitted for this lower margin.
S13 is not added to a second J13 payment for the same row. The final
normalization occurs once, on the same actual final PA law. Its mass is
positive and at most one, so the unnormalized margin gives SL7. Finite
query bounds exhaust to the complete norm under this one law.

## 6. The same certificate handles every finite prefix height N,E>=4

Use the same original pure/mixed 5/7 combs through height N and the same
18-cofactor rainbow table at every 11-exponent through E, where N,E>=4
are arbitrary finite integers. All remaining original phases are as
unrestricted as in the theorem above. Write lambda_(N,E) for the actual
unnormalized law after its 11-row. Both old and new laws live on the full
adic product; no original coordinate is discarded.

Adding the old pure and mixed comb classes shrinks their actual survivor,
so lambda0,N<=lambda0,4 as measures. The color function K is unchanged.
Put r_E=11^(-E). For K=2 and K=4 the ratios of the two allowed densities
satisfy

    h_(2,E)/h_(2,4)=(4+r4)/(4+r_E)<=1+r4/4;
    h_(4,E)/h_(4,4)=(3+2*r4)/(3+2*r_E)<=1+2*r4/3.

For K>=5 both densities equal the cap 5/3. The actual allowed 11-set
at height E is contained in that at height four. Hence

    lambda_(N,E)<=(1+epsilon)*lambda_(4,4),
    epsilon=2/(3*11^4)=2/43923.                      (SL8)

This is a comparison used in the proof. The final law for a given N,E
is still its own actual PA law.

For any seven fixed query phases, let n4 count the four cylinders at
5,7,11,25 and define the nonnegative payoff

    f=(n4-1)_+ +1_(C55)+1_(C77)+1_(C121).

For pure masses x,y the total seven-label cap minus U_PA is

    C(x,y)=5*x*y/363+10*x/231+83*y/825+4/165.

Every coefficient is positive. At the finite anchor and the limiting
pure lower bounds,

    w5_N=(1+5^(-N))/2, w7_N=(2+7^(-N))/3,
    C4=C(w5_4,w7_4)=4270892/36315125,
    Cmin=C(1/2,2/3)=22402/190575.

Sections 3--4 prove integral f dlambda_(4,4)<=C4-D13 for every joint
choice of the seven phases. Apply SL8 to this nonnegative payoff and use
w5,N>=1/2 and w7,N>=2/3. The seven-label contribution to the stability
identity for the ACTUAL new law is therefore at least

    D_uniform=Cmin-(1+epsilon)*(C4-D13)
      =9142782319955731204/553858897304769931875
      =0.016507421591396346... .                     (SL9)

The omitted numerical labels again have nonnegative deficits under that
same new law. Its PA charge F13 uses its own actual pure masses, so the
complete-query bound is

    integral(L-2)_+ dlambda_(N,E)<=F13(w5_N,w7_N)-D_uniform.

The absolute 13-row saving is at least

    kappa_uniform=D_uniform/4
      =2285695579988932801/553858897304769931875.

The constant c0 in the NC4 consumer applies throughout the PA pure-mass
rectangle. Here d5=w5,N-1/2 and d7=w7,N-2/3 remain nonnegative, and
m_N=(1-5^(-N))*(1-7^(-N))/12<=1/12. The unused pure and packing credits
retain their favorable signs. Thus, uniformly for all finite N,E>=4,

    mu_uniform=(T-2)*kappa_uniform-c0
      =722502603087750387206885808749
         /611987095715588039413526047488000>0,
    R_Q(rho_(N,E))<=T-mu_uniform<T.                  (SL10)

No first-11 classes other than this specified rainbow family are added
in SL8--SL10. Its height parameters are unrestricted above four, while
its phase geometry and the 18-cofactor table remain fixed.

## 7. Exact verification and the next missing geometry

The [standalone program](../../frontier/cover-geometry/rainbow_arbitrary13_seven_label_bound.py)
and [exact data](../../frontier/cover-geometry/rainbow_arbitrary13_seven_label_bound.json)
construct the 192 original boxes using report548's color table. Finite
prefix partitions have 73,91,141 leaves at 5,7,11. The program directly
removes each actual forbidden union, computes its actual capped kernel,
and accumulates a common joint table modulo25,7,121. Its total mass is

    lambda11(1)=121611906311383/565194987328125.

All 9625 four-label phase tuples and all 55+77+121 individual phases
are evaluated with exact integers and fractions. The cap sum, stability
margin, same-law final consumer and uniform-height transport pass 35
explicit checks. No project
producer or old data is imported; checks stay active under optimization.
No full CRT-period enumeration or Lean build was run.
An independently written program reproduced the full phase minima and
maxima from the original 192 classes. The retained result SHA256 is
`c5a9ae364a44994900f37bbea5269600d32d0dc35072a54ea73a54985a54410e`.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/rainbow_arbitrary13_seven_label_bound.py
```

The support-dependent finite query in
[report549](549-a-finite-support-dependent-query-exceeds-the-factorized-envelope.md)
still exceeds the sharper factorized constant. It lies below SL1, as
required. Thus the loss of the old constant does not obstruct the broader
arbitrary-phase continuation theorem proved here.

The prescribed pure/mixed combs and rainbow geometry remain substantive
hypotheses, even after the uniform-height extension. Extra originals
with largest prime at most 11, other first-11 geometries,
arbitrary two-copy families and unrestricted Erdős #7 are not covered.
The remaining task is a uniform joint estimate over those original
geometries, preserving their full labels, fixed phases and one law.

[A finite first-11 core](552-a-finite-first-eleven-core-controls-arbitrary-outside-phases.md) permits arbitrary phases outside one finite exponent box, using capped-kernel positive variation to control the changed actual law. Its finite core differs from the prescribed full rainbow family here.
