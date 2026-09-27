[Index](../../marked_head_profile.md) · [Whole-face cylinder bounds](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md) · [Whole-face hinges](83-common-seven-hinges-on-both-complete-k-control-faces.md) · [All-load majorants](65-endpoint-numerator-from-common-cost-constraints.md)

# A complete comparison on both K-control faces

For actual families approaching either entire controlling beta face
398,410,422 with carrier(1,1), or616,628,640 with carrier(1,0),
at saturated mass S=D=53/360, the complete AP comparison satisfies

    N<=36.325086046320646686969...,
    d>=148190644027/1898264214000
      =0.078066395043466799506341...,
    C0+N/d<=486.904279236051191431614... .                    (KC1)

This is uniform over all beta distributions on these actual faces,
independent original test residues and unbounded exponent heights.
It strengthens the comparison on the full two-dimensional faces
controlling the old global K target. It does not replace the
whole-domain global bound509.4606868254497..., supply an off-face
neighborhood, reach403, or resolve unrestricted Erdos #7. It is an
ordinary proof with exact rational verification, not a Lean result.

The previously obtained404 comparison479.9407720451339... has a
different source and carrier hypothesis. It is not used as a
uniform estimate on the present faces.

## 1. A complete square estimate follows from the whole-face cylinder caps

Let B_(a,b) bound the actual raw35 mass of any original cylinder
of modulus3^a*5^b, and let C_(a,b) bound its surviving marginal.
Profiles72 and75 give the following bounds throughout both faces:

| Modulus | Raw cap B | Surviving cap C |
| --- | ---: | ---: |
| 1 | 1/4 | 53/360 |
| 3 | 5/36 | 7/90 |
| 9 | 1/12 | 1/18 |
| 3^a, a>=3 | (3/4)*3^-a | (7/10)*3^-a |
| 5 | 1/10 | 14/225 |
| 5^b, b>=2 | (1/2)*5^-b | (2/5)*5^-b |
| 15 | 1/15 | 8/225 |
| 3*5^b, b>=2 | (1/3)*5^-b | (4/15)*5^-b |
| 45 | 1/45 | 4/225 |
| 9*5^b, b>=2 | (1/9)*5^-b | (4/45)*5^-b |
| 3^a*5^b, a>=3,b>=1 | 3^-a*5^-b | same as B |

These caps apply to arbitrary cylinder residues, including residues
formed by intersections of independently labelled tests. Such an
intersection is either empty or one cylinder of the least common
multiple modulus. By profile62's ordered-pair counting, with
W(k)=2k+1, the complete zero-seven square is bounded by

    sum_(a,b>=0)W(a)W(b)C_(a,b).

For positive-seven depth e, dropping mixed7 deletion gives cap
6*B_(a,b)/(5*7^e). The full pair sum is therefore

    Q=sum_(a,b)W(a)W(b)C_(a,b)
          +(2/3)*sum_(a,b)W(a)W(b)B_(a,b),            (KC2)

where sum_(e>=1)6*W(e)/(5*7^e)=2/3 is complete.
Using

    sum_(a>=3)W(a)*3^-a=4/9,
    sum_(b>=1)W(b)*5^-b=7/8,
    sum_(b>=2)W(b)*5^-b=11/40,

the raw and zero-seven sums are respectively

    R=1/4+3*(5/36)+5*(1/12)+(3/4)*(4/9)
                       +(37/18)*(7/8)+(4/9)*(7/8)=173/48,

    Z=53/360+3*(7/90)+5*(1/18)+(7/10)*(4/9)
       +3*(14/225)+9*(8/225)+15*(4/225)
                       +(74/45)*(11/40)+(4/9)*(7/8)=4651/1800.

Consequently every original test satisfies

    integral A^2<=Q=Z+(2/3)*R=374/75,
    45*D-Q=983/600.                                  (KC3)

This rebuilds the square from surviving cylinder caps. It does
not subtract another deletion credit from a previously charged
square bound. The unit-unit pair contributes the actual mass D.

## 2. Extend the old cost constraints using their genuine convex functions

Profile75 supplies the uniform first-moment bound L=1151/1800.
Together with(KC3), start the54 scalar constraints with L and Q.
The remaining52 consist of all46 old AP transformed costs and
six raw81 costs, exactly as in profiles65 and82.

Fix the first face and carrier(1,1). The true conditional margins
m_i(beta) of profile49 are concave in the beta simplex. Their
barriers C_i are constant, and D=53/360 is constant throughout
this face. Thus the cost upper functions

    b_i(beta)=C_i*D-m_i(beta)

are convex. For any barycentric expression
beta=sum_j t_j*beta^(j), t_j>=0, sum_j t_j=1,

    b_i(beta)<=sum_j t_j*b_i(beta^(j))
                                <=max_j b_i(beta^(j)). (KC4)

All three vertices belong to profile49's fully evaluated set.
Each stored conditional margin is a lower bound for the same
genuine conditional function, so its corresponding stored cost
is a valid vertex upper bound in(KC4). No convexity of a patched
table is required. The old raw81 source operators are also convex
in beta: their source masses and available densities are affine,
and their expressions are built from affine terms, nonnegative
weighted sums and maxima, including the complete weighted tails. Apply(KC4) to these six costs
as well. The other source factors and carrier are held fixed.

The checker takes the maximum of each of these52 cost bounds at
398,410,422, and separately at616,628,640 with carrier(1,0).
Both face-wide vectors agree. This argument extends only the old
globally defined cost functions. The new bounds L,Q and the two
hinges are already uniform by their own whole-face proofs.

Now apply every unchanged all-load majorant of profile65:

    f_i(v)<=alpha_i+sum_j w_ij*f_j(v), w_ij>=0,
    cost_i<=min(b_i,alpha_i*D+sum_j w_ij*b_j).          (KC5)

Each inequality is verified for every positive integer load,
including its complete eventual polynomial tail. The52 resulting
cost bounds improve42 entries of the inherited face-wide vector.
There is no finite load cutoff and no assertion that the tests
share their maximizing residues.

## 3. Use the same complete signed numerator

The fixed AP schedule gives the expansion

    N=r*D+sum_i beta_i*cost_i+c_square*Q,              (KC6)

where r<0, all52 beta_i>0 and c_square>0. These coefficients
depend on the AP schedule and fixed barriers, not on source404.
They are the expansion retained by profiles65 and82. Only the
actual mass and valid cost bounds have changed here.

In particular the signed mass contribution is r*(53/360), not
its404 value. The coefficient c_square retains both the complete
transformed-square complement and the raw81 square tail. The
six low raw81 terms retain their own positive weights in the
sum. Substituting(KC5) yields the numerator in(KC1).

## 4. The full AP11 law supplies a uniform survival denominator

Use profile83's whole-face bounds

    U4=62639/308700, U5=565031/3601500.

The exact complete survival estimate is

    d>=D-U4/6-(1/7)*sum_(n>=1)p_n*n*U(5/n),
    p_1=28/33, p_n=50/(3*11^n) for n>=2.

For n=1 use U5. For n=2,3,4, every integer load v>=1 obeys
the interpolation used in profile67, giving

    U(t)=(4-t)*(L-D)/3+(t-1)*U4/3, 1<=t<=4.

For n>=5, n*(v-5/n)_+=n*v-5. The entire tail is therefore
summed exactly using its zeroth and first moments. This yields

    d>=(945008/922383)*D-(45253/1844766)*L
                            -(346061/1844766)*U4-(4/33)*U5
      =0.078066395043466799506341... .                       (KC7)

The direct AP11 expansion and its coefficient form agree as
rational numbers. Since d and the upper numerator are positive,
(KC6)--(KC7) prove(KC1). The denominator is uniform over actual
families on both faces; no selected witness denominator is used.
No sharpness claim is made for the resulting scalar relaxation
or for the actual quotient.

## 5. Limits and exact reproduction

The cylinder-square tail control is the same complete lcm-weighted
geometric domination as profile62. It is uniform over changing
original test residues. The first-moment and hinge passages are
provided by75 and83. The finitely many AP cost inequalities pass
to the limiting face, with their full quadratic tails; the AP11
affine remainder is controlled by the uniform first moment.
Thus(KC1) includes arbitrary finite families approaching a face
point with the stated mass and carrier limits.

The [checker](../../frontier/endpoint-bounds/k_face_complete_ratio.py) pins the
whole-face geometry and all old cost inputs. It verifies three
finite-box decompositions with complete complementary pair tails,
all six source vertices and both carrier choices,52 all-load
majorants, signed numerator coefficients and two complete AP11
denominator expansions. The
[certificate](../../certificates/source_norms/endpoint-bounds/k_face_complete_ratio.json)
retains the exact rational comparison and all cost inputs.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/k_face_complete_ratio.py --check
```

The remaining global obligation is to control actual sources off
these saturated faces with comparably strong inequalities. The
present result does not license interpolation of486.904279... into
the old whole-domain vertex table.
