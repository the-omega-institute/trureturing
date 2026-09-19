[Index](../marked_head_profile.md) · [The original retained source](251-two-retained-original-tests-sharpen-the-complete-j-heads.md) · [The complete two-depth bridge](256-a-second-seven-depth-sharpens-the-complete-retained-j-heads.md) · [Selected-intersection inequalities](201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md)

# Second-depth cofactors sharpen the complete J survival hinge

On both entire actual saturated J faces, the original AP13 function has the complete bound

    integral (A-4)_+ dmu
      <=71949293357559869/370440000000000000
       =0.1942265774688475... .                    (JC1)

The preceding complete bound was

    5415097003260174967/27783000000000000000
      =0.1949068496296359... .

The exact improvement is

    337500025771157/496125000000000000
      =0.0006802721607884242... .

The result retains the independent original labels441 and735 at the second
seven depth. The source model remains the same3306-variable model with6354
inequalities and18 equalities. All3,125,000,000 containing choices are covered:
every one of the original62,500,000 choices has50 independent new-label
completions. Neither an actual optimizer nor simultaneous attainment of
other moment bounds is asserted.

## The same source, independent original labels, and every exponent

Keep the actual raw source Lambda, its actual survivor mu, the25 old
rectangles, the16 masks of25/27/75/81, the four membership states of135/125,
and the common late parameter theta in[1/135,1/90]. Their masses, marked
deletions, complement domination, raw CRT caps and separate original
profile variables are exactly those of251/256.

The first-depth projection count is still

    m=I_(ROOT(c)=r21)+I_(s=s35)+I_(c=c63)
                         +I_(ROOT(c)=r105,s=s105).

The second-depth count becomes

    e=I_(ROOT(c)=r147)+I_(s=s245)+I_(c=c441)
                         +I_(ROOT(c)=r735,s=s735),
    0<=e<=4.                                      (JC2)

The original labels are441=9*7^2 and735=15*7^2. The new cell choice c441
has five possibilities; the new(root,slot) choice for735 has ten. They
are independent of each other and of all earlier labels. No residue is
copied from63,105,147 or245. The usual containing completion of an absent
or source-null label by a live projection is valid because the bound is
nondecreasing in these indicators. It is an upper configuration, not an
existence claim for a particular family.

For q>=0, the complete retained seven cap series is

    G_(m,e)(q)=(6/35)*(1+m-q)_+
      +(6/245)*(1+e-(q-1-m)_+)_+
      +1/[5*7^(2+(q-2-m-e)_+)].                    (JC3)

This is256's formula with the larger permitted second-depth count. Order
all1+m depth-one indicators first, all1+e depth-two indicators second,
then the original unit7^k indicators for every k>=3. Deleting the first q
indicators bounds the remaining positive part pointwise. Integrating each
remaining indicator's cap gives(JC3), including the entire geometric tail.
The argument uses arbitrary original residues and does not require nesting
of their seven coordinates.

Write g(v)=G_(m,e)((4-v)_+). For a density weight w, define

    F(v)=w*(v-4)_+ +g(v),  w>=2/5.

Its increments are nonnegative and nondecreasing. Below4 they read the
ordered cap list in reverse; once v>=4, g is exactly constant and every
increment of F is w>=2/5>6/35. The raw kernel g alone is not asserted to
be convex. The verifier checks the finite transition range for every
permitted m,e,w and the exact constant expression for g at and above the
threshold. Thus the subsequent all-v argument has no large-load cutoff.

## The new labels remove their own assigned tail payments

The original J raw old-cofactor caps for9 and15 are1/12 and1/15. These
are the same original-cofactor caps used for63 and105 in219. Their assigned
second-depth terms in the nonnegative complete seven tail are

    cap441=(6/245)*(1/12)=1/490,
    cap735=(6/245)*(1/15)=2/1225.

Consequently

    Z8=Z6-1/490-2/1225
      =37/1225-9/2450=13/490>0.                   (JC4)

A partial affine that retains441 but leaves735 unpaid in its bridge uses
Z7=Z6-1/490. Each tail is the exact complement of its own retained set.
These are subtractions of designated cap-series summands, not of upper
estimates from unknown actual probabilities.

The joint source objective retains all25/27/75/81/135/125 states. Its old
zero-seven remainder is unchanged:

    Rpair=R4-cap135-cap125
         =2471/81000-1/135-13/3750=7951/405000.

Its complete constant is Rpair+Z8. The affine bounds below retain four
old labels and use R4+Zk for their own positive-seven partition. They do
not combine a joint-source tail with a different affine retained set.
Every original old or positive-seven label is retained or paid once.

## Why the fourth old prefix is legal for the fourth hinge

The choice min(t-1,4) in the older affine compiler was a choice of retained
prefix. It is not a restriction on the telescoping identity. For the single
target t=4, keep all four independent old labels

    (M1,M2,M3,M4)=(25,27,75,81).

At each old rectangle, for its fixed shallow load B>=1, put

    delta_k=F(B+k+1)-F(B+k),  k>=0.

Integer convexity gives0<=delta_0<=delta_1<=delta_2<=delta_3. For the actual
binary indicators I1,...,I4, telescoping is exact:

    F(B+I1+I2+I3+I4)-F(B)
      =sum_(i=1)^4 I_i*delta_(I1+...+I_(i-1)).     (JC5)

This equality holds for every B and every indicator configuration. It
neither changes the original AP13 threshold nor assumes independent events.
Retaining81 moves its own assigned cap from R3 to the fourth explicit term;
the remaining old tail is precisely R4. Above the threshold the increments
are exactly w, so(JC5) and its bounds continue for every larger load.

The original selected-cylinder operators P25,P27,P75,P81 upper-bound the
integrals of nonnegative rectangle arrays on the same actual Lambda. In
particular P27 and P81 use the normalized ternary profiles p/27 and p/81;
these are not replaced by absolute source caps. The step bounds of201 are
valid for any nonnegative ordered delta array:

    V1<=P25(delta_0),
    V2<=min(P27(delta_1),
             P27(delta_0)+max(delta_1-delta_0)/675),
    V3<=min(P75(delta_2),
             P75(delta_1)+max(delta_2-delta_1)/675). (JC6)

For the additional fourth step let l=delta_1, u=delta_2, h=delta_3 and
kappa=max(u-l,(h-l)/2), pointwise. Since I27<=1,

    I81*delta_(I25+I27+I75)
      <=I81*l+I81*(I25+I75)*kappa,

    I81*delta_(I25+I27+I75)
      <=I81*u+I81*I25*(h-u).                      (JC7)

The first inequality follows by checking the three possible values of
I25+I75; the second uses I27+I75<=2. Neither needs nested or disjoint case
assumptions. On the same actual raw measure, CRT gives

    Lambda(test81 intersect test25)<=1/2025,
    Lambda(test81 intersect test75)<=1/2025.

Thus the complete fourth-step bound is

    V4<=min(P81(h),
             P81(l)+max(max(2*(u-l),h-l))/2025,
             P81(u)+max(h-u)/2025).                (JC8)

This is the existing201 fourth-step inequality applied to the newly retained
fourth step of H4. The all-v identity(JC5), ordered increments, original
cylinder operators and exact R4 tail justify the application. Finite
positive numerical instances are not substituted for this argument.

## Complete affine and joint-source certificates

For each old shallow layout and each partial positive-seven projection,
combine the exact raw source capacity, the four selected-step bounds,
the original J deletion correction and that partial bound's complete tail.
Only the raw capacity depends on theta. The two endpoint values therefore
define a complete affine upper on the entire common interval.

Every such affine bounds the same original full AP13 function. Their
pointwise minimum is valid; its maximum is found at the two endpoints or
at an interior intersection of two lines. All these intersections are
checked exactly. Independent rational formulas, without the scaled lookup
tables, verify600 endpoint evaluations of the seven- and eight-projection
compilers. The continuation and telescoping proofs establish the general
formula, while these readings check its implementation.

For the remaining original controller, the joint objective is precisely
256's X/Y/U/V objective with(JC2)--(JC3) and constant Rpair+Z8. The50 exact
duals each check all3306 columns against the unchanged6354 inequalities
and18 equalities. The complete source LP includes theta, so these are
not endpoint-only LP bounds. The previous256 duals are used only after
regenerating the identical original objective and rechecking every column;
each such old complete bound applies to all50 new-label completions.

The certificate's50 new duals use the existing rational-table/run-length
codec. No SciPy or numerical optimizer is required to write or check this
certificate from the supplied rational prices.

## Exhaustive original-domain accounting

The scan covers

    12500 layouts *10 first projections *50 next projections
      *10 second-depth projections *5 c441 *10 (r735,s735)
      =3125000000 containing choices.

Let T,F,S be the numbers bounded at the two-, four-, and six-projection
levels, with all valid bound types included at each level. Let U be the
number bounded after c441, E the number bounded by a full eight-projection
affine, and D the number bounded by a checked seed dual. The exact ledger is

    25000*T+500*F+50*S+10*U+E+D=3125000000.        (JC9)

The certificate recomputes this ledger and every branch-decision digest:

| Level or bound | Checked branches | Bounded branches |
| --- | ---: | ---: |
| Original two-projection affine |125000|124990|
| Enhanced two-projection affine |10|4|
| Original four-projection affine |300|294|
| Enhanced four-projection affine |6|2|
| Original six-projection affine |40|8|
| Enhanced six-projection affine |32|8|
| Rechecked original256 dual |24|23|
| Partial441 affine |5|0|
| Full441/735 affine |50|0|
| Checked joint seed dual |50|50|

There are no uncovered branches. The largest discarded upper is no larger
than(JC1). A total of50 seed and24 existing duals gives244644 exact column
checks:165300 new-seed columns and79344 original-source columns. No new LP
solve is needed after these prices have been supplied.

The maximizing certificate branch is the original layout(1,4,2,1,2,4,2),
original projection(1,4,4,1,4,1,4), and new projection(4,1,4). This identifies
the largest retained bound, not an attained original source configuration.

## Scope and reproducibility

The same source relabelling transports the whole source, survivor, marked
states and all eight independently chosen projections to the other J
orientation. The additional two finite original cylinder observations fit
the existing labelwise diagonal construction; every remaining exponent
is covered by the unchanged complete geometric tails.

The canonical certificate is
`certificates/source_norms/j_face_second_cofactor_survival_heads.json`.
Its exact reproducible check is

```sh
python3 frontier/j_face_second_cofactor_survival_heads.py --check
```

The result concerns the original AP13 function on the complete actual J
domain. It does not identify independent moment witnesses with one actual
family, extend off the saturated faces, produce a complete52-cost comparison,
or resolve unrestricted Erdős7. No Lean verification is asserted.
