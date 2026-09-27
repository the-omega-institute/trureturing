# Four parents from thirty-seven with a lower arbitrary-parent threshold

The complete actual head and private interfaces of [Report651](651-an-unqueried-head-coordinate-admits-four-parents-from-thirty-seven.md) admit either of the following complete network policies:

| Four-parent owner range | Arbitrary finite parent unions | Full survivor density |
| --- | --- | --- |
| `37 <= v < 2^52` | every `v >= 2^52` | `> 1/(430000 Q_off)` |
| `37 <= v < 2^74` | every `v >= 2^74` | `> 1/(520000 Q_off)` |

The first row uses Rosser--Schoenfeld1962 Theorem8. The second uses only the elementary prime-product bound already proved in Report621. Each row specifies ONE actual law; they are independently sufficient policies, not separate estimates combined across sources.

Keep651's ten literal head primes, central conventions, all fifteen square-star and twenty square-pair originals with arbitrary globally fixed full phases, and the remaining forty linear-star and twenty `qs/9qs` incidences on one fixed live-root table. Keep every ordinary domain, disjoint private interior and label assignment of647/625/619. Each owner has one fixed union of smaller declared head/network parents, after numerical duplicates and repeated syntactic descriptions have been merged. Undeclared private interiors cannot be parents. All network sizes, depths, widths and exponent heights remain arbitrary finite quantities.

This combines651's four-parent range beginning at37 with649's sixth-power Euler method on a newly specified common policy. It retains the head, phase and interface hypotheses, asserts no optimal cutoff, and does not resolve unrestricted Erdős #7. The arguments below are ordinary mathematics with exact rational certificates; no new Lean verification is claimed.

## 1. One actual source and one kernel at every owner

Use651/648's same actual head submeasure, with

    gamma = 203129722400814193208791597
              /20692505911553620784640000000,
    alpha = 2673/110656,
    zeta = 5455/5814.

Its support, lower mass, full Haar domination and actual unary source representation are unchanged. The ten head prefix caps remain

    (2,4/3,7/5,11/9,13/11,17/15,19/17,5/3,20/11,2).

On the restricted head these are used through the existing joint-prefix bounds and unary source domination. Full-history conditional caps apply to the normalized23/29/31 and outside kernels; conditioning the restricted head on survival is not asserted to preserve those caps.

Fix either `V=2^52` or `V=2^74` from the opening table. Append normalized owner kernels in increasing prime order:

1. At `37 <= v < 1253`, keep exactly651's193 fixed finite rows. Their domain parameter is `D=v-3`, their fixed threshold is `1-h/D`, and their conditional Haar cap is `(v-1)/h < v/10`.
2. At `1253 <= v < S`, where `S=3^10=59049`, use650's dense four-parent cube. Its unique integer `n>=5` satisfies `2n^4+3 <= v <= 2(n+1)^4+1`; select `[0,n)^4`, excluding the unit already paid by the ordinary domain.
3. At `S < v < V`, put `n=min{j:v<=3^j}` and select the sparse cube `[0,n)^4`, again excluding the unit. Thus `n>=11`.
4. At `v>=V`, use the arbitrary-parent `N=0` half-threshold row from625/649.

The numberS is composite, so no owner is lost at the strict switching endpoint. The same is true forV. Every normalized row is defined on every complete prior history, including wholly forbidden remaining fibres. No row conditions on eventual survival. Missing owners may be omitted. The actual head and all present rows define one joint submeasure `Pi`; adding later normalized rows preserves earlier marginals.

For either cube, `N=n^4-1`, and its remaining domain has Haar mass at least

    D/(v-1),  D=v-n^4-2.

The half-threshold row has conditional density cap

    c_v=2(v-1)/D=2+2(n^4+1)/(v-n^4-2).             (F1)

For dense rows this is at most4. For sparse rows,

    2(n^4+2)<=3^(n-1)  for all n>=11.               (F2)

Atn11 this is29286<=59049. Induction follows from the positivity of

    3(n^4+2)-((n+1)^4+2)
      =2n^4-4n^3-6n^2-4n+3.

After substituting `n=11+t`, its coefficients from constant upward are

    (23191,9060,1314,84,2).

Since `v>3^(n-1)`, (F2) gives `2<c_v<4<v/10`. The arbitrary-parent row has cap `2(v-1)/(v-3)`, which is smaller than(F1). Thus every actual row preserves651's conditional cap invariant. Its finite unqueried-coordinate comparison and fixed hinge fees apply unchanged; no omission factor is applied to the arbitrary-parent tail.

## 2. The complete four-parent cube charge

Use650's conservative comparison, with

    p=(3,5,7,11),  d=(2,4/3,7/5,11/5).

The fourth coefficient11/5 is deliberately the same as650. Full-history conditional caps, reverse elimination of queried actual rows, and the actual joint head bound prove this comparison on the one law above. Auxiliary independence evaluates its bound; actual parents may be shared and dependent.

For independent auxiliary depths with `Pr(L_i>=e)=d_i p_i^(-e)` at positivee, put `X_i=L_i+1` and

    C_n=prod_i X_i-prod_i min(X_i,n).

Every original cofactor pattern and owner height retains its globally fixed phase through the comparison. Numerical-label uniqueness, completion by positive terms, and the full geometric height sum yield the owner bound

    Pi(owner-v violation)<=E(C_n^2)/(v-n^4-2)^2.     (F3)

Define

    T_i=1+d_i[3/(p_i-1)+2/(p_i-1)^2],
    A_i(n)=d_i p_i(p_i+1)p_i^(-n)/(p_i-1)^2,
    B_i(n)=d_i p_i^(1-n)[n+1+2/(p_i-1)]/(p_i-1).

Then `T_i=E(X_i^2)`, `A_i=E((X_i-n)_+^2)` and `B_i=E(X_i(X_i-n)_+)`. Consequently

    M4(n)=E(C_n^2)
      =prod T_i-2prod(T_i-B_i)+prod(T_i-2B_i+A_i).

The pointwise product-difference inequality gives the positive majorant

    M4(n)<=U(n)
      =sum_i A_i prod_(j!=i)T_j
         +2sum_(i<j)B_i B_j prod_(k!=i,j)T_k.

Report620's bound also follows directly here:

    3^5 U(5)=7988967877739/183428437500<74,
    M4(n)<74*3^(-n)  for every n>=5.                (F4)

Indeed the scaled diagonal terms have successive ratios3/p_i<=1; the scaled cross terms have ratios at most `3/(p_i p_j)*((n+2)/(n+1))^2<1` for `n>=5`.

There are5764 primes in the dense interval `1253<=v<S`. Sum each exact(F3), rounding each fee upwards to a multiple of10^-18. This gives

    W_dense=0.000029705249700818.                    (F5)

All original heights are already included inM4; the finite window here is an actual policy interval.

For sparse bands, put `A=3^(n-1)+1`, `B=3^n` and `c=n^4+2`. Padding primes by all integers and integrating a decreasing positive function gives

    sum_(A<=v<=B, prime)1/(v-c)^2
      <=1/(A-c-1)-1/(B-c).

Sum74*3^(-n) times this exact bound forn11 through20. Forn>=21, (F2) bounds each entire band by444*9^(-n). Hence the complete remaining tail is

    sum_(n>=21)444*9^(-n)=999/(2*9^21).

The resulting complete sparse fee is

    W_sparse=0.000000007524275848771309... .          (F6)

It includes every prime aboveS, so it conservatively overcharges the sparse subset belowV. AboveV the actual row is used only once, and is paid by its arbitrary-parent estimate. No additional actual dense or sparse process is sampled there.

## 3. A complete sixth-power Euler estimate on these same rows

For a capc write

    T_p(c)=1+c[3/(p-1)+2/(p-1)^2].

As in621 and649, the full cofactor second moment at an arbitrary-parent ownerv satisfies

    M(v)<=prod_(odd p<v)T_p(c_p),
    Pi(owner-v violation)<=M(v)/(v-3)^2.            (F7)

Use the actual ten head caps, the193 actual651 finite caps and the actual dense/sparse caps below the product endpoint

    B0=3^13=1594323.

AboveB0 use(F1) as a comparison cap, including at missing primes and at actual arbitrary-parent rows whose smaller cap it dominates. These choices concern the same sequential source and retain all joint cross terms.

The complete finite product has120738 factors:

    10 head + 193 finite + 5764 dense + 114771 sparse.

Directed160-bit integer arithmetic supplies a rational interval for

    M0=prod_(odd p<=B0)T_p(c_p),
    M0<=M0_plus=3250377045.8477573... .              (F8)

It also encloses `P_odd(B0)=prod_(3<=p<=B0)p/(p-1)` for the elementary alternative. No floating-point multiplication enters these bounds.

Forp>B0, its sparse depthn is at least14. The induction underlying(F2), with the base `5(14^4+2)<=3^13`, gives `n^4+2<=p/5`. Thus

    c_p-2<=5(n^4+1)/(2p),
    3/(p-1)+2/(p-1)^2<=16/(5p).

The latter follows from `p^2-27p+16>=0` forp>=27. Since `T_p(2)>=1` and `log(1+u)<=u`,

    log(T_p(c_p)/T_p(2))<=8(n^4+1)/p^2.

Integer padding and integration give `sum_(3^(n-1)<p<=3^n)p^(-2)<=2/3^n`. Hence the full logarithmic excess obeys

    Gamma=16 sum_(n>=14)(n^4+1)/3^n
         =361960/1594323<1,
    exp(Gamma)<=C_tail=1/(1-Gamma).                (F9)

For example, the exact geometric moments used to evaluate this infinite polynomial sum are

    sum_(j>=0)j^r/3^j = (3/2,3/4,3/2,33/8,15), r=0..4.

Finally, withu=1/(p-1),

    T_p(2)=1+6u+4u^2<=(1+u)^6.

Forv>=V>B0 this proves

    M(v)<=M0_plus C_tail [P(v)/P(B0)]^6,            (F10)

where `P(x)=prod_(p<=x)p/(p-1)`. Including the endpointprimev only enlarges the bound. The sixth power follows from this actual sparse policy, rather than changing the exponent while retaining different old caps.

## 4. Two independently sufficient complete large-owner tails

The [existing citation](../../../../../Library/Arith/rosser1962approximate.md) records Rosser--Schoenfeld1962 Theorem8, printed page70, equations(3.28)--(3.29):

    P(x)>exp(gamma_E)logx[1-1/(2log^2x)]  forx>1,
    P(x)<exp(gamma_E)logx[1+1/(2log^2x)]  forx>=286.

The source scan hash remains `8e37b06f82e09421bceb2502578c47b61469141f0287e6acedb70e01765ab556`. No new verification of that external analytic theorem or Lean formalization is asserted.

BecauseB0>=3^10, dividing the bounds gives, forv>=B0,

    P(v)/P(B0)<=(201/199)logv/logB0.

The positive series forlog3 gives `logB0>13*(263/240)=3419/240`, and `log2<7/10`. For `V=2^K`, the decreasing function `f(x)=log^6(x)/x^2` satisfies

    sum_(v>=V, prime)f(v)
      <=(1/2) integral_(V-1 to infinity)f(x)dx.

The odd-integer spacing and the lower endpointV-1 are retained. Six integrations by parts, `v/(v-3)<=V/(V-3)` and `log(V-1)<7K/10` give

    E_RS(K)=M0_plus C_tail (201/199)^6 (V/(V-3))^2
      *sum_(j=0)^6 [6!/(6-j)!](7K/10)^(6-j)
      /[2(V-1)(3419/240)^6].                       (F11)

AtK52 this bounds the ENTIRE arbitrary-parent prime tail by

    E_RS(52)=0.0001641852356963253... .              (F12)

For the elementary alternative, let `P0_minus` be the positive rational lower enclosure of `P_odd(B0)` and put

    A6=M0_plus C_tail/P0_minus^6.

Report621's elementary bound `P_odd(2^k)<=4(k+1)` and odd-integer dyadic padding give

    E_elem(K)=2A6[4(K+2)]^6 2^(-K)
      /[1-(1/2)((K+3)/(K+2))^6].                  (F13)

The denominator is positive and bounds the geometric band ratio for allk>=K. AtK74 the complete fee is

    E_elem(74)=0.00018075087242434243... .            (F14)

This elementary policy uses four-parent sparse rows below2^74 and arbitrary-parent rows above it. It does not combine the2^52 switching law with a separate product estimate.

## 5. Whole-source margins and exact evidence

Keep651's certified finite hinge charge `W_finite=zeta W_hinge` and the ordinary Type I fee1/65536. By(F5)--(F6), their complete debit before the arbitrary-parent tail leaves

    gamma-W_finite-W_dense-W_sparse-1/65536
      =0.00026116402244245483... .                  (F15)

Every estimate above concerns the one actual source for its chosenV. Removing the union of paid actual violations leaves raw mass at least

    V=2^52: 0.00009697878674612955...,
    V=2^74: 0.00008041315001811241... .

The retained exact rational comparisons are

    alpha*(gamma-W_finite-W_dense-W_sparse
                  -1/65536-E_RS(52))>1/430000,
    alpha*(gamma-W_finite-W_dense-W_sparse
                  -1/65536-E_elem(74))>1/520000.    (F16)

The same simultaneous private filling and Haar projection as651 then extend every surviving head point by an actual outside assignment. Dividing by the actual outside resolving productQ_off and applying CRT gives the two full-density statements.

The [portable certificate](../../frontier/cover-geometry/four_parent_sparse_euler_six_certificate.py) and [exact data](../../frontier/cover-geometry/four_parent_sparse_euler_six_certificate.json) read the pinned sibling651 coefficient certificate. It retains the exact dense moments, ten sparse band charges, complete infinite remainder, directed finite products, both selected complete policy budgets, input and producer hashes and367993 explicit checks. It runs with assertions disabled as well:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/four_parent_sparse_euler_six_certificate.py

The [independent verifier](../../frontier/cover-geometry/four_parent_sparse_euler_six_independent.py) and [data](../../frontier/cover-geometry/four_parent_sparse_euler_six_independent.json) reconstruct the prime list by trial division, use reversed exact blocks of64 factors before256-bit directed rounding, derive cube moments from direct mixed moments, and evaluate the logarithmic excess with a quartic telescoper. Its251162 checks confirm that its product intervals lie inside the producer intervals and independently verify both complete policy margins. Run:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/four_parent_sparse_euler_six_independent.py

The numerical certificate evaluates the coefficients and strict comparisons. The common-source construction, comparison induction, infinite completion and analytic inequalities are the ordinary proofs above. No current posterior, separate favorable source, discarded phase or independently selected marginal substitutes for their joint hypotheses.

The remaining unrestricted gaps are the sixty head incidences and central conventions, the private-interface conditions, and more than four parents at owner primes below the chosenV. The new result reduces the arbitrary-parent threshold while preserving the four-parent allowance from37; it does not remove those remaining conditions.
