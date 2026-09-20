[Index](../../marked_head_profile.md) · [All numerator costs](65-endpoint-numerator-from-common-cost-constraints.md) · [Uniform endpoint survival](67-exact-endpoint-survival-and-its-scalar-boundary.md) · [Complete positive-five square](69-complete-positive-five-tails-in-one-square-layout.md)

# A complete endpoint ratio using the uniform actual survival bound

For the actual endpoint class with source404, S=D=3/20 and forbidden
carrier(root0,cell1), the complete current AP numerator satisfies

    N_endpoint<=35.77996171992922... .                  (ER1)

Combining this uniform numerator with profile67's uniform physical
survival denominator

    d_survival>=4067559874193/52947452250000
               =0.07682257977187183...

gives the endpoint comparison

    C0+N_endpoint/d_survival<=487.3421133369318... .     (ER2)

Both bounds apply to every original test in the specified endpoint
class. The denominator in(ER2) is the uniform actual comparison
bound of67, and no selected tensor denominator enters the calculation.
The same denominator with profile65's old numerator gives
490.2195838875208..., so the strict endpoint improvement is
2.8774705505889795... .

This does not update the global K certificate or the finite
neighborhood theorem of68. It is an ordinary endpoint theorem with
exact rational arithmetic, not Lean verification. Unrestricted
Erdős #7 and the rest of the source-domain comparison remain open.

## 1. Only one scalar constraint changes

Use profile65's54 upper constraints for every independently labelled
complete original357 test A. Their first two are

    integral A dmu<=L=1157/1800,
    integral A^2 dmu<=Q.

The other52 are exactly its46 old transformed-cost bounds and six
raw81 low-count bounds. The mass remains D=3/20. Profile69 improves
the uniform square constraint to

    Qnew=114/25, Qold=469/100, Qold-Qnew=13/100.        (ER3)

Every original test satisfies all54 constraints separately. Combining
them within one test makes no assertion that different tests share
residues, loads, or a maximizing configuration.

Retain all52 of profile65's exact rational majorants. For a target f_i,
its unchanged coefficients satisfy

    f_i(v)<=alpha_i+sum_j lambda_ij*g_j(v),
    lambda_ij>=0, for every integer v>=1.              (ER4)

Let lambda_i denote its multiplier on the square constraint g_1(v)=v^2.
The raw majorant bound therefore changes by exactly

    P_i(Qold)-P_i(Qnew)=lambda_i*(13/100).             (ER5)

As in65, use the minimum of P_i and the old valid cap B_i. For each
of the nine targets having lambda_i>0, the old majorant already
satisfies P_i(Qold)<=B_i. Since decreasing Q decreases P_i, the
majorant remains active throughout[Qnew,Qold]. Targets with lambda_i=0
do not change. Thus the minimum obeys the exact same sensitivity:

    U_i(Qold)-U_i(Qnew)=lambda_i*(13/100).             (ER6)

The nine sensitive targets are the five quadratic transformed costs
and raw81 counts3,4,5,6. All41 linear transformed costs and the raw81
counts1,2 remain included with their existing upper bounds. The checker
validates each min branch and rechecks every majorant on its whole
positive-integer domain, including its exact polynomial tail.

## 2. All signed barriers and complete count tails remain in the numerator

Write C_i,w_i for the original transformed barriers and weights. Keep
the same constants H16,H41,A81,AC,C0 and the same complete square
complement

    oQ=1600217/12882870.

At the fixed mass D, define

    M41=sum_(i<41)w_i*(C_i*D-U_i),
    m_g=45*D-Qnew=219/100,
    Mquad=sum_(41<=i<46)(C_i*D-U_i)+oQ*m_g.            (ER7)

The square barrier remains45. The46 target indices here are the
same transformed costs as65; the six raw81 targets follow them.

Let p_n be the unchanged AP11/AP13 product count law. Its six low
raw81 contributions and complete remaining square coefficient are

    R81=sum_(n=1..6)p_n*n^2*U_(46+n-1),
    cG=sum_(n=7,8)p_n*n^2+sum_(n>=9)p_n*n^2.         (ER8)

The n>=9 term is evaluated by the exact complete count-tail formula.
No count beyond a finite grid is dropped. With the unchanged signed
comparison,

    Nnew=(AC*H16+H41+A81)*D
                  -AC*Mquad-M41-cG*m_g+R81.           (ER9)

This gives(ER1). The checker separately expands(ER9) into the residual
mass term, all52 positive-weight cost terms, and the square term.
The two rational expressions agree exactly.

## 3. Exact sensitivity of the entire numerator

Let a_i denote the positive coefficient of target U_i in that
expanded numerator: it is w_i for the41 linear costs, AC for the
five quadratic costs, and p_n*n^2 for the six raw81 costs. The direct
coefficient of Q is AC*oQ+cG. Equations(ER5)--(ER9) therefore give

    Nnew=N65-Beta*(Qold-Qnew),
    Beta=AC*oQ+cG+sum_(i=0..51)a_i*lambda_i
        =82443364318785420250033717
           /48484093902073830000000000
        =1.7004208531833371... .                      (ER10)

This is the sensitivity of these fixed majorants on[Qnew,Qold]; it
does not assert optimality among all possible majorants. Its exact
numerator gain is

    N65-Nnew=82443364318785420250033717
                /372954568477491000000000000
             =0.22105471091383383... .                (ER11)

The full gain splits into four disjoint groups:

| Group | Numerator improvement |
| --- | ---: |
| 41 linear costs | 0 |
| Five quadratic costs and their complete complement | 0.1613119312433678... |
| Six low raw81 costs | 0.05576307492346521... |
| Remaining raw81 square coefficient | 0.003979704747000846... |

Their exact rational sum is(ER11). This checks that the extra square
gain is propagated through all its consumers without adding the same
payment twice.

## 4. The uniform denominator and the remaining scalar obstruction

Profile67 proves a denominator lower bound for every independently
labelled original survival test on this same endpoint class. It
retains the complete physical AP11 auxiliary count law. Since that
denominator bound is positive, combining it with(ER1) proves(ER2).
Different tests need not attain the numerator and denominator bounds
simultaneously for this uniform upper comparison.

For arbitrary finite source sequences tending to this endpoint, the
first and second moment bounds and original cost limits have the
uniform complete tails established in62,65 and69. Thus(ER4)--(ER9)
give the claimed numerator limsup. The physical survival comparison
has the liminf lower bound of67. Positivity then gives(ER2) as a
uniform endpoint limsup. This limiting statement supplies no radius
on which Qnew or(ER2) holds for finite nearby sources.

For the fixed new numerator to certify403 by the same separate ratio,
the required denominator would be

    Nnew/(403-C0)=0.09381072603245746...,

which exceeds the current guarantee by0.016988146260585625... .

Moreover, the two abstract scalar laws W,V from67 still satisfy all57
constraints after replacing Qold by Qnew. In particular

    integral v^2 dW=3.9207001965230535...<4.56,

and V also remains below the new cap. The checker evaluates every
updated constraint for both laws. They still attain all the survival
targets and the complete AP11 tail used in67. Hence the sharp
denominator obstruction for this scalar relaxation persists even
with the stronger square bound.

This does not assert that W or V is an actual congruence-family load
law. Further progress can exclude these abstract laws by actual
geometry, retain a joint relation across tests, strengthen the
numerator, or change the physical comparison. Recombining only the
same57 scalar inequalities cannot raise the denominator guarantee.

## 5. Reproduction

The [checker](../../frontier/endpoint-bounds/endpoint_uniform_ratio.py) pins profiles65,
67 and69 with their source dependencies. It reuses all52 original
majorants, verifies their all-integer polynomial tails, reconstructs
every signed barrier and complete AP tail, and checks both numerator
expansions against the exact sensitivity identity. The
[certificate](../../certificates/source_norms/endpoint-bounds/endpoint_uniform_ratio.json)
contains all52 per-cost changes, complete gain groups, the actual
uniform denominator, and the remaining gap.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/endpoint_uniform_ratio.py --check
```

Only the Python standard library and pinned repository cost routines
are used. Default execution is read-only; only `--output PATH` writes
through the existing certificate writer. These checks establish the
stated exact arithmetic conditional on the cited ordinary mathematical
theorems; they do not turn an endpoint result into a global certificate.
