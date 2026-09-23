[Index](../../marked_head_profile.md) · [Original endpoint mean](../001-064/59-endpoint-linear-source-deletion-bound.md) · [Scalar survival boundary](67-exact-endpoint-survival-and-its-scalar-boundary.md) · [Complete pure3 deletion on the K faces](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md)

# Complete pure3 deletion gives the uniform endpoint mean16/25

For every actual finite original-label family approaching source404,
carrier(0,1) and survivor mass S=D=3/20, every independently labelled
complete original357 test A satisfies

    limsup integral_survivor A<=16/25,
    liminf[6*S-integral_survivor A]>=13/50.              (CP1)

This improves profile59's mean bound1157/1800 by exactly1/360. The
new ingredient is the complete forbidden pure3 cofactor tail. Its
saturation forces an exact product section on root0, supplying an
additional deletion measure on every five-coordinate event.

The scalar witness W of67 has first moment1157/1800, exceeding(CP1)
by1/360. It is therefore excluded uniformly by its mean alone. In
particular actual endpoint tests cannot approach equality in the old
1157/1800 bound. No conditional theorem using that equality is needed.

This is an ordinary uniform endpoint theorem, not a quantitative
finite neighborhood, a new global K value or a Lean result. A later
consumer can use the improved mean in its joint cost constraints;
no improved uniform survival denominator is asserted here.

## 1. Saturation fixes the source sections of forbidden deep3 labels

Retain the actual source Lambda, pure3 measure eta, surviving marginal
mu, and deleted marginal delta of59. At source404,

    eta=(1/18,1/9,1/9,1/9,1/9),
    d=(3/4,3/4,1/4,1/2,1/2),
    n=(1/24,1/12,1/36,1/24,1/18),
    s=1/4, S=D=3/20.

Every alpha and beta source label lies on root1. All additional
late35 source deletion lies in cell3, also on root1. Let U_P be the
complete pure5 source union and set

    q(F)=Haar5(F minus U_P)

for a five-coordinate measurable set F. Since the only source
deletions on root0 are pure3 and pure5,

    Lambda(J times F)=eta(J)*q(F), J subset root0.      (CP2)

At the saturated mixed7 mass, profile57 gives delta=V as measures
and zero individual cap deficiency for every original cofactor.
Fix any forbidden cofactor3^a at seven depth e, where a>=3. Its
old-coordinate cap is(3/4)*3^-a, so its ternary cylinder J_(a,e)
attains that mass. A cylinder in root1 has source mass at most
(1/2)*3^-a and cannot attain the cap. Thus J_(a,e) lies in root0.
Using q(full)=3/4 and(CP2), equality forces eta(J_(a,e))=3^-a.
Consequently

    Lambda(J_(a,e) times F)=3^-a*q(F)                  (CP3)

for every F and every original pair(a,e). The cylinders may differ
independently across both exponents. No nesting or common residue
is inferred from equality of their masses.

Let delta_deep3 be their part of the virtual deleted measure. Since
delta=V and all contributions are nonnegative, it is a valid part
of the actual deletion. Equation(CP3) gives the exact full marginal

    delta_deep3(full ternary times F)
       =sum_(a>=3,e>=1)u_e*3^-a*q(F)
       =(1/18)*(1/5)*q(F)=q(F)/90,                  (CP4)

where u_e=6/(5*7^e). Both geometric tails are complete. The old
cofactors here are3^a with a>=3; they are distinct from the four
families3,9,5,15 used in59's selected-deletion bound.

## 2. Every first-five test has a smaller uniform cap

Profile59 provides the source slots P,A_s,B,Q,H, where A_s is the
source alpha slot. All deeper pure5 source cylinders lie in Q with
total five mass1/20. The pure5 complement in these first slots is

    q(P)=0, q(A_s)=q(B)=q(H)=1/5, q(Q)=3/20.          (CP5)

Keep the four selected forbidden families of59:

    delta_selected>=(1_root0+1_cell1+1_H
                                  +1_(root1 intersect H))*Lambda/5.

Their cofactor labels differ from those in(CP4), so the complete
deep3 measure can be retained in addition. Applying the resulting
measure inequality to each arbitrary first-five test slot gives

    mu(full ternary times F)
       <= integral_(full ternary times F) w dLambda-q(F)/90,
    w=1-(1_root0+1_cell1+1_H+1_(root1 intersect H))/5.  (CP6)

The source-slot bounds from59, uniformly over its late-deletion
parameter x in[1/90,1/72], are

    (P,A_s,B,Q,H)<=(0,1/45,1/18,2/45,1/18).

Subtract(CP5)/90. A convenient common upper table becomes

    (P,A_s,B,Q,H)<=(0,1/50,4/75,77/1800,4/75).

Its maximum is4/75, so every independently chosen test residue
of modulus5 obeys

    mu(test5)<=4/75.                                (CP7)

The checker additionally evaluates the exact affine source tables
at both allowed x endpoints before the subtraction. This verifies
all intermediate x as well. The cap improvement over1/18 is1/450.

## 3. Retain the pure5 complement throughout the complete deep-five tail

Let F be any five-coordinate cylinder of depth b>=2. Retain just
the forbidden root0 and cell1 families, together with(CP4). Their
selected surviving density multiplier is nonnegative. Dropping
alpha, beta and late source deletion gives

    integral_(full ternary times F)
                 [1-(1_root0+1_cell1)/5] dLambda
      <=[h-(h0+eta1)/5]*q(F)=(4/9)*q(F),             (CP8)

where h=1/2, h0=1/6 and eta1=1/9. The q(F) factor must remain
in(CP8) until after subtracting the deletion in(CP4). Thus

    mu(full ternary times F)
      <=(4/9-1/90)*q(F)
      =(13/30)*q(F)<=(13/30)*5^-b.                  (CP9)

This is a uniform bound for every original residue at depth b.
The complete b>=2 test sum is at most

    (13/30)*sum_(b>=2)5^-b=13/600.

The former coefficient4/9 gave1/45. The tail improvement is
1/45-13/600=1/1800. It is separate from the first-depth gain in(CP7).

An inequality of the form c*5^-b-q(F)/90 would not justify(CP9)
without a lower bound on q(F). Keeping the same q(F) in the positive
and negative terms of(CP8)--(CP9) avoids that invalid replacement.

## 4. The entire unchanged test inventory

All other test categories retain59's valid caps. The complete
linear sum is

| Category | Upper contribution |
| --- | ---: |
| Unit | 3/20 |
| 3 | 11/120 |
| 9 | 2/45 |
| 3^a, a>=3 | 11/360 |
| 5 | 4/75 |
| 5^b, b>=2 | 13/600 |
| 15 | 1/25 |
| 3*5^b, b>=2 | 1/60 |
| 9*5^b, b>=1 | 1/36 |
| 3^a*5^b, a>=3,b>=1 | 1/72 |
| All positive-seven test labels | 3/20 |

The last line is the unchanged raw35 comparison(1/4+1/2)/5 and
includes its old-unit labels. Every exponent tail is present. The
sum of the table is

    1157/1800-1/450-1/1800=16/25,
    6*(3/20)-16/25=13/50.                           (CP10)

Different test moduli may have different residues. The sum uses
uniform individual cylinder estimates and linearity of integration;
it does not assume those maxima can be attained simultaneously.
Within(CP6) and(CP9), the retained forbidden families are disjoint
as lists of original labels. Their projected supports need not be
disjoint, since the endpoint measure identity delta=V already gives
the permitted sum of their contributions.

## 5. Approaching finite families and the scalar witness

For sequences of actual finite source and test families tending to
the specified endpoint, take a joint labelwise diagonal subsequence.
Each fixed forbidden and test cylinder stabilizes, while the complete
forbidden-union tails give convergence of the source measures. Pure7
normalizers remain at least5/6. Complete geometric test-cylinder
bounds give uniform first-moment tails, so the full integrals pass
to the limiting endpoint. That endpoint satisfies(CP2)--(CP10), proving
the limsup and signed-margin liminf in(CP1). There is no extra
linear-saturation assumption on the tested load A.

The law W of67 has mass3/20 and first moment1157/1800. The gap1/360
in(CP1) directly excludes it as an actual endpoint load law or as a
limit of such laws with convergence of first moments. This does not
claim that every nearby abstract law is excluded. The improved mean
is new information for a scalar relaxation, whose optimum can be
recomputed separately.

## 6. Exact reproduction

The [checker](../../frontier/endpoint-bounds/endpoint_linear_complete_pure3_deletion.py)
pins59's complete cap tables and67's W law. It verifies the two
complete original-cofactor tails, the pure5-complement coefficients,
every first-five affine column, the disjoint first/deep-five gains,
and the complete original-test sum. The
[certificate](../../certificates/source_norms/endpoint-bounds/endpoint_linear_complete_pure3_deletion.json)
records their exact rational values.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/endpoint_linear_complete_pure3_deletion.py --check
```

Only the standard library and pinned repository cap routines are used.
The original-label geometry and limiting quantifiers are supplied by
the ordinary proof above. Default execution is read-only; only explicit
`--output PATH` writes. The new mean preserves all earlier valid upper
bounds while strengthening the endpoint information available to later
numerator and survival consumers.
