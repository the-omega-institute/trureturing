[Index](../marked_head_profile.md) · [Common positive-five square](69-complete-positive-five-tails-in-one-square-layout.md) · [Product-section deletion](77-complete-pure3-deletion-gives-a-uniform-linear-gap.md)

# Complete pure3 deletion sharpens the common square

For the actual404 endpoint class, S=D=3/20 and carrier(0,1), every
complete original357 test with independent original residues satisfies

    limsup integral A^2 dmu <=4.555785363598363... .     (DS1)

The exact upper bound is defined in(DS8). Its attributable new-source
gain over profile69's114/25 consists of7/3600. A further rational
gain comes from converting that profile's already positive comparison
slack. The latter is not reported as new deletion geometry.

The same six-label layout controls the survivor and raw-source terms.
Every exponent tail is complete. This is an ordinary endpoint and
approaching-sequence theorem, with no new global K or Lean claim.

## 1. Pay the extra deletion on a single occurrence of the common load

Use profile69's notation X=B+T, where B is the common shallow load
of{1,3,9,5,15,45}, and T contains all pure3 labels of depth at least3.
Let F contain the zero-seven pure5 test labels of depths b>=2, and
G the zero-seven3*5^b tests of those depths. The descendant-five
cell-cap table V and its five column sums are

    c=(0,1/9,5/18,4/9,5/18),                        (DS2)

in source-slot order(P,A_s,Beta,Q,H). Define

    q5(B)=max_s sum_l V_l,s*B_l,s.

The complete forbidden pure3 family gives the additional deleted
five-coordinate marginal q(J)/90 from profile77. For a depth-b
test cylinder J in A_s, Beta or H, the pure5 source is absent,
so q(J)=5^-b. The corresponding full-column cap therefore improves
from c_s*5^-b to(c_s-1/90)*5^-b. For J in Q, profile77's retained
q(J) argument gives

    mu(J)<=(13/30)*q(J)<=(4/9-1/90)*5^-b.

For J in P the surviving mass is zero. Thus every nonzero slot
has the same uniform column-cap gain1/90 per unit cylinder length.

Since B_l,s>=1, split off its unit occurrence:

    integral B*1_J dmu
      =mu(J)+sum_l(B_l,s-1)*mu(cell_l times J).

Apply the new column cap only to mu(J), and the old V table to
the remaining nonnegative summands. For every nonzero slot this gives

    integral B*1_J dmu<=(q5(B)-1/90)*5^-b.            (DS3)

It also holds for slot P, because q5(B)>=max_s c_s=4/9. This step
does not multiply the deletion by an independently maximized value
of B. It keeps precisely the same B as the common square comparison.

## 2. Two disjoint complete pair groups improve

Uniformly over all slots, the new pure5 cylinder cap is
(13/30)*5^-b. For arbitrary independent test residues,

    F^2<=sum_(b>=2)(2b-3)*1_(J_b).

Indeed each intersection is contained in its deeper cylinder, and
there are2b-3 ordered pairs with maximum depth b. With

    sum_(b>=2)5^-b=1/20,
    sum_(b>=2)(2b-3)*5^-b=3/40,

we obtain

    integral F^2 dmu<=13/400,
    2*integral B*F dmu<=q5(B)/10-1/900.              (DS4)

The first bound improves the old1/30 by1/1200. The second improves
the old common-layout bound by1/900. Their ordered-pair sets are
disjoint: BF and FB have one shallow label, while FF has both
labels among the pure5 depths b>=2.

Keep the complete independent TF intersection bound1/180. Hence

    integral(2*X*F+F^2) dmu<=q5(B)/10+133/3600.       (DS5)

Profile69's corresponding constant was7/180=140/3600, so the
exact new gain is

    1/900+1/1200=7/3600.                             (DS6)

The TF, FG and G pair groups, all other positive-five labels and
every positive-seven occurrence retain their existing estimates.
The new deletion is supported in root0; an independent ternary
test can avoid it. Its projected five marginal also does not give
an extra bound on an arbitrary test seven-coordinate intersection.
Thus neither of those groups receives an unsupported extra credit.

## 3. Reuse the common-layout comparison and its strict slack

Write Z(B), R(B) and Rstar as in profiles64 and69. The complete
square upper expression of69 is

    E+7/180+11/360+(4/15)*Rstar
      +max_B[Z(B)+(q5(B)+q15(B))/10
                         +(2/5)*sqrt(R(B)*Rstar)],

where E=109/90 and Rstar=212153/87480. Replacing just7/180 by
133/3600 immediately gives the valid simpler bound16409/3600.

The published12500-layout certificate additionally gives

    K=138187/52488,
    g(B)=K-Z(B)-(q5(B)+q15(B))/10>=0,
    [(5/2)*g(B)]^2-R(B)*Rstar>=s0,
    s0=495114037/9685512225>0.                       (DS7)

These are retained results, not a new enumeration. All terms
subtracted from K are nonnegative, so g(B)<=K. Also0<=R(B)<=Rstar.
Put x=(5/2)*g(B) and y=sqrt(R(B)*Rstar). Then x>=y>=0,
x^2-y^2>=s0 and x+y<=(5/2)*K+Rstar. Consequently

    g(B)-(2/5)*sqrt(R(B)*Rstar)
      >=(2/5)*s0/[(5/2)*K+Rstar]=delta0>0.

This supplies a uniform gap for the original square expression.
Combining it with the disjoint new-source gain gives the exact bound

    Q81=114/25-7/3600-delta0
       =4.555785363598363...<1139/250.                (DS8)

The signed barrier45 margin is45*(3/20)-Q81. The original finite
layout certificate and its complete analytic tails justify(DS7);
no comparison is made using floating-point square roots.

## 4. Quantifiers and reproduction

The pair sums above include all depths a,b,e. The complete pair-cap
tails of profile62 dominate them uniformly, so the same labelwise
compactness argument of69 and77 passes the endpoint statement to
limsup along finite actual families. Different test labels may
choose different residues at every stage.

The [checker](../frontier/endpoint_square_complete_pure3_deletion.py)
consumes the existing layout minimum and the new product-section
coefficient. It checks the column sums, the disjoint full pair gains,
and the exact rational slack conversion. Its
[certificate](../certificates/source_norms/endpoint_square_complete_pure3_deletion.json)
records the source contribution and the pre-existing slack contribution
separately.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_square_complete_pure3_deletion.py --check
```

The original12500-layout calculation is reused without repeating its
enumeration. The ordinary proof supplies the pair ownership, uniform
geometric inequalities and complete-limit passage.
