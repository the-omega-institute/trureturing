[Index](../marked_head_profile.md) · [Fixed numerator](49-full-linear-and-quadratic-carriers-refine-the-frontier.md) · [Actual survival boundary](56-exact-survival-limits-the-fixed-numerator-comparison.md)

# Exact transformed-cost numerator reference on the actual tensor witness

On the actual357 tensor witness of profile56, all46 independent
AP-transformed cost directions and the complete raw81 comparison
can be evaluated exactly. Retaining the original profile49 slopes,
weights and signed barriers, their reference numerator is

    N_tensor=23094865026612742148637380191186516404121
               /809513462087178042210684534266400000000
            =28.5293155805797... .                      (TN1)

Combining it with the same witness's three-hinge denominator
Dmax=12117093811/128357460000 and the unchanged offset gives

    R_tensor=C0+N_tensor/Dmax
      =121572514359610080325508696442387688309540973
        /375446616877965477311787984731139192120000
      =323.80772364004497...<403.                       (TN2)

This is a reference evaluation of the AP-transformed independent
costs on one actual357 test witness. It is not a uniform bound on K,
and does not assert attainment of the complete physical AP numerator.
The AP comparison steps remain in the transformed cost functions.

Profile56 holds its numerator fixed and obtains a necessary target
above413. This calculation shows that the same witness alone does
not force a target above403 if the numerator comparison is also
changed. Producing new uniform inequalities for that numerator,
with the actual common law and all independent tests retained,
remains a separate proof obligation. No Lean verification or
resolution of unrestricted Erdos #7 is claimed.

## 1. The complete actual distribution and its first two moments

Keep exactly profile56's forbidden family, original tensor test
A=B3*B5*B7, pure7 normalization and mixed7 deletion. Write Lambda
for the raw actual35 source. Its masses and the raw surviving357
measure have limits along genuine finite original-label families.

The pure3 and source35 ternary distributions are

    eta(1)=1/6, eta(2)=2/9, eta(k)=2/3^k for k>=3,
    lambda(1)=1/8, lambda(2)=5/72,
    lambda(k)=1/3^k for k>=3.

The cofactor-weighted ternary distribution is

    nu(1)=5/18, nu(2)=4/9, nu(k)=5/3^k for k>=3.

For degree d=0,1,2 define

    G_d(p,k)=sum_(j>=k)j^d/p^j,
    E_d=1/6+(2/9)*2^d+2*G_d(3,3),
    L_d=1/8+(5/72)*2^d+G_d(3,3),
    V_d=5/18+(4/9)*2^d+5*G_d(3,3),
    P_d=4*G_d(5,2).

The source-free nested five test chain then gives the exact raw35
moment

    Z_d=L_d+(4/5+P_d-1)*E_d.                           (TN3)

For the mixed7 cofactors the entire old-coordinate moment is

    H_d=11/60+P_d/3+V_d*(P_d+1/20).                    (TN4)

The first term retains the b=0 cofactor mass where B5=1. Unlike
the positive-threshold hinges of profile56, an arbitrary numerator
cost can be nonzero there, so this term cannot be omitted.

The normalized pure7 test moment is

    Q_d=29/35+(36/5)*G_d(7,2).

Every mixed7 deleted point has B7=1. The raw actual surviving moment
is therefore

    M_d=Z_d*Q_d-H_d/5.                                 (TN5)

The resulting values are

| d | Z_d | H_d | Q_d | M_d |
| --- | --- | --- | --- | --- |
| 0 | 1/4 | 1/2 | 1 | 3/20 |
| 1 | 17/24 | 101/72 | 6/5 | 41/72 |
| 2 | 53/16 | 83/12 | 5/3 | 331/80 |

These formulas use complete geometric moments. Explicitly, writing
g=1/[p^(k-1)*(p-1)],

    G_0(p,k)=g,
    G_1(p,k)=g*[k+1/(p-1)],
    G_2(p,k)=g*[k^2+2k/(p-1)+(p+1)/(p-1)^2].           (TN6)

The second-moment limit is justified on the actual finite families.
Under the product Haar law, the full tensor has

    E A^2=[3*4/2^2]*[5*6/4^2]*[7*8/6^2]=35/4.

The finite pure7-normalized densities are bounded by6/5. The finite
source and deleted indicators converge pointwise, and the old
cofactor multiplicity is bounded by4. Thus fixed functions of at
most quadratic growth are integrably dominated. Dominated convergence
applies to all costs below, not just the first-moment hinges.

## 2. Exact low atoms provide an independent integration method

Let z_v be the raw35 mass of B3*B5=v. Equation56(ES2) gives

    z_1=11/120, plus the divisor sum below,
    z_2=1/40, plus the divisor sum below,
    z_v=3/(5*3^v), plus the divisor sum below, v>=3,

where the divisor sum is

    sum_(m|v,m>=2)(4/5^m)*eta(v/m).

Let h_v be the complete cofactor-weighted old-coordinate mass at
B3*B5=v. Including its load-one term,

    h_v=(11/60)*1_(v=1)+(4/(3*5^v))*1_(v>=2)
          +nu(v)/20+sum_(m|v,m>=2)(4/5^m)*nu(v/m).       (TN7)

With p7(1)=29/35 and p7(n)=36/(5*7^n) for n>=2, the raw actual
surviving357 mass at A=v is

    mu_v=sum_(n|v)p7(n)*z_(v/n)-h_v/5.                 (TN8)

These are masses of the actual surviving set and hence nonnegative.
In particular mu_1=23/630 and mu_2=949/29400, matching profile56.

Each transformed cost f in the pinned inventory has degree d=1 or2
and an exact integer tail

    f(v)=a*v^d+b for all integers v>=K_f.

Equations(TN5) and(TN8) therefore give an exact finite correction:

    integral f(A)=a*M_d+b*M_0
        +sum_(1<=v<K_f)mu_v*[f(v)-a*v^d-b].             (TN9)

This is not a truncation of the load distribution. Its entire
unbounded tail is contained in M_d and M_0. The program independently
integrates the complete35 tensor series, the complete7 expectation
and the complete removed-cofactor series. Those direct calculations
agree with(TN9) for each of the46 costs and every low raw81 term.

## 3. All46 original cost directions retain their current barriers

The functions f_i are precisely the AP(4,5) inventory used by
profile49:41 linear-growth directions and five exceptional quadratic
directions. Their tags retain the original AP exponent tuples,
physical caps(11,5/3),(13,12/7), complete auxiliary tails and current
comparison weights. The41 linear directions consist of16 R17
blocks,16 R19 blocks,8 R5 blocks and the complete linear cost.

Each f_i is evaluated at the same actual357 tensor test. This
choice is admissible for each independent test direction; it does
not identify the residues of arbitrary test families in the universal
comparison. In particular an integral of an AP-transformed scalar
cost is not automatically the value of its underlying physical AP
event or of the whole physical numerator.

For every direction use the current profile49 barrier C_i, not an
earlier norm input with a different barrier. Define its actual signed
margin by

    m_i^tensor=C_i*D-integral f_i(A), D=3/20.            (TN10)

The exact result retains all46 integrals, barriers and margins,
and compares each with its profile49 conditional lower bound at404/A.
Every actual margin is at least that valid lower bound.

The independent source-square comparison uses the signed barrier45:

    integral A^2=331/80,
    m_g^tensor=45*(3/20)-331/80=209/80.                 (TN11)

Its normalized actual test square is331/12. Neither that value nor
an older global source-square norm may replace45 in(TN11). The
barrier is part of the current numerator's algebra.

With the same complete weights w_i and quadratic complement
oQ=1600217/12882870, form

    M41_tensor=sum_(i=1..41)w_i*m_i^tensor,
    Mquad_tensor=sum_(j=1..5)m_j^tensor+oQ*m_g^tensor.

Their exact values are

    M41_tensor=1403815808094034022292136972100798417473
                 /206270257166444404986376347673650000000,
    Mquad_tensor=14968600089610903/6267335894820000.      (TN12)

## 4. Complete raw81 terms and the numerator identity

Let p_n be the pinned auxiliary product-count probabilities for the
same physical caps at11 and13. The six low terms are n=1,...,6:

    R81_tensor=sum_(n<7)p_n*n^2*integral(A^2-81/n^2)_+.

The atoms7,8 and the entire n>=9 tail remain in the unchanged
coefficient cG multiplying the signed source-square margin. They
are not omitted or counted again in R81_tensor. Exact evaluation gives

    R81_tensor=750819647769257810204356047857
                  /137822200043865453517964062500.       (TN13)

Keep profile49's H16,H41,A81,cG,AC,C0. Replacing only its source
comparison margins and low raw81 costs by these actual reference
values defines

    N_tensor=(AC*H16+H41+A81)*D
               -AC*Mquad_tensor-M41_tensor
               -cG*m_g^tensor+R81_tensor.               (TN14)

Substitution gives(TN1). The program independently expands(TN14)
into the46 original integrals, their barrier coefficients, the
complete square coefficient and the remaining multiple of D.
This checks the aggregate identity without treating a source norm
as the signed barrier.

The fixed49 numerator exceeds this reference by exactly

    Nfixed-N_tensor
      =1315971908012882252657830266821512121321
         /155675665785995777348208564282000000000
      =8.453292307237808... .                           (TN15)

Its nonnegative components, with all numerator weights included, are

| Contribution | Difference on this witness |
| --- | ---: |
| 41 linear margins | 5.22878041484079... |
| Five quadratic margins and their complement | 1.8162990629365463... |
| Six low raw81 costs | 1.3731242804051256... |
| raw81 square-tail margin | 0.03508854905534697... |

These are actual-witness differences, not uniform gains available
on every source parameter or test layout. The calculation identifies
where this witness leaves room in the fixed comparison; it does not
construct inequalities recovering those differences globally.

Use profile56's unchanged actual three-hinge denominator in(TN14),
not its later exact-dilation improvement. This gives(TN2) on precisely
the same reference law and witness. The numerical separation from
profile56's413.354 boundary comes from changing its fixed-numerator
premise; it does not contradict that boundary.

## 5. Reproducible scope

The [checker](../frontier/exact_tensor_numerator_reference.py) and
[exact result](../certificates/source_norms/exact_tensor_numerator_reference.json)
pin profile49, profile56's checker and data, the AP cost inventory,
and their mathematical inputs. There is no temporary-file dependency.
They reconstruct the three complete moments, every required low-load
atom, the46 independent cost integrals by both methods, all six raw81
terms, the signed barrier45, the aggregate numerator and the reference
ratio. The profile56 hinge integrals are independently recovered from
the new atom/moment formula.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/exact_tensor_numerator_reference.py --check
```

Default execution is read-only; `--check` also compares the canonical
result. Only explicit `--output PATH` writes a result. All mathematical
checks remain active under `-O`.

The ordinary distribution proof provides the infinite-family limit
and complete-tail identities. The checker verifies the exact
concrete costs and their arithmetic. A uniform numerator improvement,
a global K bound and the unrestricted covering problem remain open.
