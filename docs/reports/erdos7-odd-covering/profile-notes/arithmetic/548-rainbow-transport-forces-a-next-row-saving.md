# Rainbow transport forces a saving in the next actual row

One finite first-11 rainbow family prevents a factorized next-row continuation from attaining the PA comparison charge. Under the SAME actual transported law, the absolute 13-row saving is at least

    kappa=878448290756953416781/159518625650895010500000
          =0.005506869728676256... .

This alone exceeds the whole mass-saving requirement c0/(257/51-2) of [report544](544-missing-original-slots-restore-a-common-law-debit.md). The unchanged final PA law consequently has complete query norm strictly below 257/51 for every continuation in the phase class specified below, including arbitrary finite 13-heights and arbitrary later 17/19 originals.

This is a restricted two-copy theorem. Every actual continuation family is finite; no height cutoff means that no uniform upper bound is imposed on its finite exponents. The 13-row chains may be arbitrary nested chains, including arbitrarily delayed divergence from the first-11 chains; their first roots must have full pure-survivor mass, and their 5/7 projections must factor by coordinate. A bound for arbitrary support-dependent 13 projections is not proved. The calculations and arguments are ordinary mathematics, not Lean verification or unrestricted Erdős #7.

## 1. The fixed finite source and the allowed continuation

Work on Q={5,7,11,13,17,19}, with at most two actual originals per numerical modulus. At p=5,7 use the pure originals

    p^(e-1), 2*p^(e-1) modulo p^e, 1<=e<=4.

For every 1<=a,b<=4 use the two mixed originals

    (3*5^(a-1),3*7^(b-1)), (3*5^(a-1),4*7^(b-1))

at modulus 5^a*7^b. As in report544, let sigma be Haar restricted to the pure survivors, eta the restriction to the actual mixed union, and lambda0=sigma-eta. Then

    w5=313/625, w7=1601/2401, m=eta(1)=4992/60025,
    lambda0(1)=w5*w7-m=53759/214375.

Define the two old 5-chains by A_(1,a)=[4]_(5^a), while A_(2,1)=[4]_5 and A_(2,a)=[9]_(5^a) for a>=2. Similarly B_(1,b)=[5]_(7^b), B_(2,1)=[5]_7 and B_(2,b)=[12]_(7^b) for b>=2. Depth zero is the whole coordinate.

For each 1<=e<=4 and each displayed cofactor 5^a*7^b, put two originals at full modulus 11^e*5^a*7^b. Slot j uses old cylinder A_(j,a) times B_(j,b). Its 11-cylinder has least-significant-first prefix (10,...,10,c), with e-1 copies of 10 and the table's color c. An entry lists colors for slots one and two; a dash means no original.

| a \\ b | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 0/4 | 2/6 | 8/8 | 1/1 | 3/3 | 5/5 | 7/7 | 9/9 |
| 1 | 1/5 | 3/7 | 9/9 | - | - | - | - | - |
| 2 | 8/8 | 9/9 | - | - | - | - | - | - |
| 3 | 2/2 | - | - | - | - | - | - | - |
| 4 | 3/3 | - | - | - | - | - | - | - |
| 5 | 6/6 | - | - | - | - | - | - | - |
| 6 | 7/7 | - | - | - | - | - | - | - |
| 7 | 9/9 | - | - | - | - | - | - | - |

This specifies 18 cofactors, 36 occurrences per 11-exponent and 144 first-11 originals, together with the 48 old originals. These 192 classes are ALL originals whose largest prime is at most eleven; no additional classes at those primes are allowed in this theorem.

The 13 continuation has the following precise restriction. For each current 13-exponent e, its at-most-two originals at each old cofactor can be assigned to two slots. In each slot there are two globally fixed nested chains D_(5,a), D_(7,b), with depth-zero whole spaces. Every occupied old cofactor 5^a*7^b*11^c uses exactly those respective 5/7 projections. The chains are reused over every c and over the other coordinate's exponent. Their first 5-root is 3 or 4; their first 7-root is one of 3,4,5,6. These are exactly the roots wholly contained in the two finite pure survivors, each retaining Haar mass 1/p. The chains may vary with e and the slot. The old 11-phase may depend arbitrarily on the full cofactor, e and slot; all current 13-phases are also arbitrary and fixed. There is no height cutoff in this continuation.

All remaining originals with largest prime 17 or 19 are arbitrary, subject to numerical multiplicity at most two. Every process below uses report348's actual PA kernels, with no intermediate renormalization and no change of any original phase.

## 2. The rainbow boundary determines the actual 11-fibre

The two chain counts at each old prime have states

    O=(1,1), C=(2,2), A_n=(n,2), B_n=(2,n), n>=3.

For one pair X,Y of old-coordinate states, let L1=X1*Y1, L2=X2*Y2 and let K be the number of distinct active colors. The eight boundary pairs

    A8/O, B8/O, O/A8, O/B8,
    A3/C, B3/C, C/A3, C/B3

each contain ten active occurrences, with all ten colors appearing exactly once. Their union is the table's full 36-occurrence inventory. Every pair with L1+L2<=10 is contained in a boundary pair; every pair with L1+L2>=10 contains one. Indeed, a branch against O has load n+2 and crosses ten at n=8; against C it has load 2n+4 and crosses at n=3; two branching coordinates already dominate a branch/C boundary. The remaining O/C pairs lie below those boundaries. Therefore

    K=min(10,L1+L2).                                      (RT1)

This inclusion argument covers every old depth, not just a finite sample. Infinite-chain endpoints follow by the same inclusion and have no effect on the integrals.

Color 9 appears only at cofactors with exponent pairs (0,7),(1,2),(2,1),(7,0). Activating any one of these forces L1+L2>=10. Conversely K=10 includes every color. Thus color 9 is active exactly when K=10.

The colored 11-cylinders are pairwise disjoint across depth and color. Put r=11^-4. At a point with K active colors, the allowed 11-fraction and actual capped density are

    g_K=1-(K/10)(1-r), h_K=min(5/3,1/g_K), s_K=h_K*g_K.    (RT2)

For K<10, the WHOLE root 9 modulo 11 is allowed. For K=10, the survivor is exactly the depth-four cylinder with all four digits 10. These statements describe the same actual lambda11=lambda0 K11.

The finite base itself is irredundant. Each displayed occurrence is uniquely colored on some rainbow boundary; an old point in that boundary avoids the old pure and mixed classes, and its designated 11-cylinder hits no other first-11 class. Old private points extend using four initial 11-digits equal to 10. CRT gives integer private points at the finite original heights. Irredundancy of arbitrary later continuations is not assumed.

## 3. A pointwise upper bound allowing every old 11-phase

Fix one completed 13-slot and an old 5/7-point. Its active cofactor count at EVERY old 11-exponent is the same number M=N5*N7 because the two coordinate chains factor and are reused. Complete missing old labels by nonnegative query terms. All added terms are comparison queries, not new originals.

For K<10 and M>=2, the baseline M makes (L-2)_+ linear; each of the M positive-depth cylinders has mass at most h_K/11^c. For M=1 there is one cylinder C_c at each positive 11-depth, and the pointwise inequality

    (sum_(c>=1)1_(C_c)-1)_+ <= sum_(c>=2)1_(C_c)

gives the bound h_K/110. For K=10, bound the first four positive-depth contributions by 4M everywhere and sum the remaining cylinder caps. The resulting upper expression has nonnegative baseline 5M-2. Thus the pointwise hinge upper bounds are

    psi_K(1)=h_K/110,
    psi_K(2)=h_K/5,
    psi_K(M)=(s_K+h_K/10)*M-2*s_K,  M>=3, K<10;

    psi_10(M)=(5/3)*r*[M*(4+11/10)-2],  M>=1.             (RT3)

The constants use the COMPLETE geometric query tails. For instance, sum_(c>=2)11^-c=1/110. For K=10 each of the first four positive-depth queries can contain the full survivor, and the remaining nested tail contributes 1/10 of its mass. These are the upper caps used in RT3. No finite query cutoff is used.

Nested cylinders inside the allowed root 9 attain the caps for K<10. For K=10, nested cylinders first containing the four-10 prefix and then lying inside it attain them. These observations concern the pointwise relaxed bound.

These maximizing 11-phases are allowed to depend on the old point only in the upper relaxation. RT3 bounds every globally fixed actual phase assignment; it does not assert simultaneous realization of the pointwise choices.

## 4. Arbitrarily delayed branch changes reduce to four cases

It is insufficient to check chains that coincide forever with a first-11 chain. A 13-chain can diverge at any depth. The following comparison covers all such possibilities.

If the 13-chain shares a first-11 root, its count on that root starts at two. For M>=2, RT3 is affine in M, with slope

    alpha_K=s_K+h_K/10 for K<10,
    alpha_10=(5/3)*r*(4+11/10).

For K>=4 these slopes are nonincreasing in K at r=11^-4. Explicitly alpha_4=1+1/(6+4r), alpha_K=(11-K+Kr)/6 for 5<=K<=9, and alpha_10=17r/2. The middle terms decrease by (1-r)/6; the two endpoint comparisons follow from 6>30r+20r^2 and r<1/21.

Whenever an old coordinate is in the shared root, K>=4. Move the entire part of a 13-chain below its first root from either first-11 second-level branch into a third second-level branch, transporting all deeper prefixes by the same tree isomorphism. The raw cylinder masses and the distribution of its count increments above two are preserved. The old first-11 state at the destination is C, while every source state dominates C. Thus K cannot increase, and the slope applied to every nonnegative count increment cannot decrease. The count-two baseline and all other coordinates stay fixed. These shared roots avoid eta, so the same comparison holds for the actual old source.

This proves dominance by type T: share the first-11 root, then use a third child. It includes chains whose original divergence was arbitrarily delayed. A chain already in a third child has the same joint count law, whatever its later path.

Only comparison test chains are moved in this argument. The actual original classes and both actual kernels K11 and K13 remain fixed.

For the 7-coordinate, any chain in mixed root 3 or 4 can be moved into root 6. The pure masses and old first-11 state O are unchanged, while eta-deletion can only decrease. Call this type D. For 5, the other full root is mixed root 3; it remains a separate D case, with its actual eta contribution retained. Hence only TT, TD, DT and DD need to be bounded.

## 5. Exact transport on the four surviving chain types

For a prime p, type T has the following raw joint distribution of the first-11 state and the 13-count:

    (O,1): w_p-1/p;
    (C,2): (p-3)/p^2;
    (C,n): (p-1)/p^n, n>=3;
    (A_n,2),(B_n,2): (p-1)/p^n each, n>=3.

Type D has

    (O,1): w_p-2/p;
    (O,n): (p-1)/p^n, n>=2;
    (C,1): (p-2)/p^2;
    (A_n,1),(B_n,1): (p-1)/p^n each, n>=3.

Tensor these RAW pure-source laws, evaluate RT3, and subtract the actual eta contribution. On eta the first-11 state is O/O, so K=2. For 5-type T, both 13-counts are one there. For 5-type D, the 7-count remains one, while the 5-count has mass m5-1/5 at one and mass 4/5^n at n>=2, where m5=(1-5^-4)/4. Multiply this last distribution by m7=(1-7^-4)/3. Thus the mixed deletion is subtracted under the same law, not discarded in a changed source.

Every infinite sum reduces exactly: old first-11 counts at least eight have K=10 regardless of the other coordinate, and count tails needed in RT3 have

    sum_(n>=3)(p-1)/p^n=1/p^2,
    sum_(n>=3)n*(p-1)/p^n=(3p-2)/[p^2*(p-1)].

The four resulting hinge bounds are

| 5 type | 7 type | Exact transported hinge upper bound |
| --- | --- | --- |
| T | T | 9087451444165575901661/79759312825447505250000 |
| T | D | 13869387400909870454063/79759312825447505250000 |
| D | T | 110198996442912490409/805649624499469750000 |
| D | D | 11556805628235524546587/79759312825447505250000 |

The largest is

    H13=13869387400909870454063/79759312825447505250000
        =0.17389050769861686... .                        (RT4)

Every slot and current 13-exponent satisfies this same bound, even if their two coordinate chains differ. The averaging weights beta_(e,j)=12/(2*13^e) sum to one. Report348 CP5 therefore bounds the actual absolute 13-row loss by H13/4.

## 6. The actual row saving closes the common-law budget

The unchanged PA 13-comparison charge uses

    F13=(w5+1/4)*(w7+1/6)*(7/6)-2*w5*w7
             +(w5-1/5)*(w7-1/7)*(28/33)
       =93139019/475398000.

Writing Loss13 for the actual absolute loss, the same-law saving is

    S13=F13/4-Loss13 >=(F13-H13)/4
        =878448290756953416781/159518625650895010500000
        =kappa.                                          (RT5)

To use this saving, let Sq=a_q Fq-Lossq at every later row. CP5 makes each Sq nonnegative, and the actual mass identity is

    lambda(1)=alpha_PA+(1/12-m)+sum_q Sq.

The final-query estimate PD2 of report544 uses the same lambda. Its sufficient margin is therefore

    A5*d5+A7*d7+A57*d5*d7
      +(T-2)*[1/12-m+sum_q Sq]+JL-c0,
    T=257/51.

No new law is defined by these savings. For any lawful completion,

    Sq=a_q Jq+[a_q(Fq-Jq)-Lossq],

and both terms on the right are nonnegative. A small completion debit cannot remove an actual row saving; it transfers that saving into the remaining comparison slack.

Using only RT5, the margin is at least

    mu=(T-2)*kappa-c0
       =9868274731167038268676761238529
          /1836044886230940825847901894400000>0.           (RT6)

All other nonnegative terms may be omitted for this lower bound. In particular no final JL estimate or saving in rows 17 and 19 is required. The PA mass lower bound is positive. Dividing once by lambda(1), and using lambda(1)<=1, gives R_Q<=T-mu<T for the one final law. As in PD3, the uniform finite-query estimate passes to the full labelwise query norm by exhaustion. This retains all original and query heights.

## 7. Verification and the remaining phase dependence

The [standalone program](../../frontier/cover-geometry/rainbow_factorized13_bound.py) and its [result](../../frontier/cover-geometry/rainbow_factorized13_bound.json) passed 53 named exact checks. These include the 18-cofactor/36-occurrence color table, all eight rainbow boundaries, a private-boundary witness for every occurrence, 324 small joint states and the safe-root property, the 192-original count, both coordinate distributions, the slope order, the eight exact TD mass/first-moment bins, all four rational integrals and RT6. The result SHA256 is `35d046b390c60ec8c3501ddf29bba4723dc58e61712d315ee67d37af9e1c3271`.

The program uses exact rational arithmetic and sums all geometric tails, imports no project producer or data, and keeps explicit failure checks active under Python optimization. The depth-independent branch comparison in Section 4 and the infinite geometric sums are separate ordinary arguments; enumerating shallow paths would not justify the allowed arbitrary chain depths. No original-period enumeration or Lean build was run.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/rainbow_factorized13_bound.py
```

The theorem excludes simultaneous sharpness of this fixed rainbow 11-row and any 13 continuation in the stated factorized phase class. It does not bound a continuation whose 5/7 phases depend on the old 11-exponent or jointly on the cofactor's other exponents. Such a query has no common product count M=N5*N7 repeated at each 11-depth, so RT3 cannot be integrated using the four joint laws above. Chains starting in the partially surviving root zero are also outside the stated class. Uniform estimates beyond these phase and root restrictions, and arbitrary-family two-copy closure, remain unresolved.

[A finite support-dependent query](549-a-finite-support-dependent-query-exceeds-the-factorized-envelope.md) strictly exceeds RT4 on this same actual lambda11. It falls outside the factorization hypothesis and leaves the larger13-only closure threshold unrefuted.
