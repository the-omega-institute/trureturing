# Actual mixed-loss obstructions and a single-query repair

Two explicit finite families of pairwise distinct odd numerical moduli
greater than one refute an attempted enlargement of the actual-loss
criterion in [report541](541-shared-ternary-roots-certify-sixteen-mixed-heads.md). Their actual pure-product mixed losses exceed `173/250`. They do not refute a supported common-law
bound `R < 565/51`: that bound follows for both examples from ordinary
conditioning, with clipping at the single numerical query `d=3` in the
153-original example. All probabilities below use the same fixed original
residues, complete pure source, and full actual survivor. A general single-query bound also extends the sufficient DIRECT-query
loss threshold to `20657/28270`. No Lean claim is made, and no
original-period scan is used.

## 1. Explicit original families and private points

Let `P={3,5,7,11,13,17,19}` and `Q=P\{3}`. Put

    c_p(d,e)=d*p^(e-1)+(p^(e-1)-1)/(p-1),
    C_p(d,e)={x_p=c_p(d,e) mod p^e}.

For `d!=1`, distinct pairs `(d,e)` define disjoint cylinders: compare the
first position at which either word departs from the all-1 prefix. The
pure originals at p are `C_p(0,e)`, `1<=e<=H_p`. Their survivor mass and a
remaining digit-channel mass are

    w_p=1-sum_(e=1)^H_p p^(-e),
    u_p(K,H_p)=sum_(e=1)^K p^(-e)/w_p.

For each mixed box in the following specifications, take *every* exponent
combination in its indicated ranges. Its full numerical modulus is the
product of the corresponding prime powers, and its full residue is the
unique CRT residue obtained from the displayed local digits. Each
original is present once.

**Primary:** `H_3=7`, `H_q=3`. Every mixed box uses ternary digit 2 at
depths `a=1..4`; every outside coordinate uses depths `b=1..2`. There are
six star boxes, with outside digit 2 at each `q in Q`, and five pair boxes:

| Outside support | Local digits |
| --- | --- |
| 5,7 | 3,3 |
| 5,11 | 4,3 |
| 7,11 | 4,4 |
| 7,13 | 5,3 |
| 7,17 | 6,3 |

This gives `25+48+80=153` originals, all mixed moduli divisible by 3.

**Fallback:** `H_3=6`, `H_q=2`. Six star boxes have ternary digit 2 at
depths `1..5` and outside digit 2 at depths `1..2`. One triangle box has
the same ternary coordinates and digit 3 at 5 and 7, each at depths
`1..2`. One old box has no ternary coordinate and digit 4 at 5 and 7,
each at depths `1..2`. This gives `18+60+20+4=102` originals.

Different role supports and exponent tuples give distinct numerical
moduli. All supports lie in P, so the moduli are odd and greater than one.

There is also an explicit private point for every original. Work at the
finite CRT period `N=product_p p^H_p`. For the target original, use local
residue

    x_p=(p^H_p-1)/(p-1)+(d-1)*p^(e-1)

on each specified coordinate `(p,d,e)`, and the neutral residue
`(p^H_p-1)/(p-1)` elsewhere. CRT gives one integer `x in [0,N)`.
The one nonneutral digit makes it belong to the target cell and to no
other depth cell on that coordinate. Pure, star, and pair roles cannot
coincide at this point: unspecified coordinates are neutral, and roles
with a common active coordinate use different digits when necessary.
For the fallback old box the ternary coordinate is neutral. Thus every
original has a private point, and each family is irredundant.

The producer supplies all 255 full moduli, CRT residues, and private
points, and checks every private point against *all* originals of its
family. It never scans `[0,N)`.

## 2. The exact losses exceed the uniform threshold

Let `rho0=product_p H_p(.|S_p)` be the complete pure-survivor source.
The remaining coordinate channels are disjoint and independent across
primes. Consequently each mixed box is a genuine Cartesian event under
this one source. Inclusion-exclusion of the eleven primary boxes, or
eight fallback boxes, computes the actual mixed union exactly; it does
not sum independent copies of shared coordinates.

For the primary example the ternary-channel mass is `t=540/547`.
Writing `u_q=u_q(2,3)`, the star-complement mass is

    C=product_q(1-u_q)=22097298208000/56737195542797.

Within that complement let `r_q=u_q/(1-u_q)`. The five pair-event masses
are `r5*r7`, `r5*r11`, `r7*r11`, `r7*r13`, `r7*r17`.
Only the second/fourth and second/fifth pair intersections are nonempty;
there are no nonempty triple intersections. Their union mass is

    h=2241842719/9285721000.

Thus the outside union has mass

    E=1-C+C*h=148997081921279/211475001568607,

and the actual mixed union is exactly the ternary event times that union:

    ell=t*E=80458424237490660/115676825858028029,
    ell-173/250=102515185933815983/28919206464507007250>0.

For the fallback let S be the outside star union, H the digit-3 5/7
rectangle, and O the old digit-4 rectangle. The ternary-channel mass is
`t=363/365`. The exact outside probabilities give

    Pr(O)=48/779,
    Pr((S union H)\O)=70128970342/110567283205.

Hence

    ell=Pr(O)+t*Pr((S union H)\O)
       =27943515594546/40357058369825,
    ell-173/250=164312026271/403570583698250>0.

In both cases set `s=1-ell`, `Omega=product_p w_p`, and let U be the
full actual survivor. Their full Haar masses are respectively

    H(U)=Omega*s=346765800571444864/4970375566622841375>0,
    H(U)=Omega*s=12413542775279/173200065313275>0.

Neither family covers its full CRT period.

## 3. A single ordinary probability cap repairs the primary certificate

For any probability rho on the prime product define the complete
nonunit query norm

    R_P(rho)=sum_(d>1, P-smooth) max_r rho([r]_d).

For these pure sources, at every positive p-height a clean cylinder
attains the cap `1/(p^e*w_p)` (choose first digit 2). Product independence
and nonnegative geometric summation therefore give the exact source norm

    R0=R_P(rho0)=product_p[1+1/((p-1)*w_p)]-1.

Use the *same* full-survivor law `rho=rho0(.|U)=H(.|U)`. For each query
label d, with `q_d=max_r rho0([r]_d)`,

    max_r rho([r]_d)<=min(1,q_d/s).

Keeping the ordinary `1` bound at just `d=3` and using `q_d/s` elsewhere
gives the general single-label bound

    R_P(rho)<=min(1,q3/s)+(R0-q3)/s.

For the primary family,

    R0=4183137340318400011792327/1238951421369984756482048,
    q3=1/(3*w3)=729/1094>s.

The unclipped estimate `R0/s` exceeds `565/51`. The clipped estimate is

    R_P(rho)<=1+(R0-q3)/s
      =26143266279751984807415409/2640435704882446344912896
      =9.9011183...<565/51,

with exact positive margin

    565/51-[1+(R0-q3)/s]
      =158539592991230959697600381/134662220949004763590557696.

Equivalently, the exact unnormalized query debit identity

    D(U)=sum_d[q_d-max_r rho0([r]_d intersect U)],
    R_P(rho)=(R0-D(U))/s

already has the elementary lower bound

    D(U)>=q3-s=83728472902439765/231353651716056058.

This exceeds the proposed required debit

    R0-(565/51)*s
      =1533857235086619334074499/442305657429084558064091136.

The displayed required-debit number is therefore not a new obstruction:
it is already surpassed by clipping one query at its elementary
probability bound. No new law or query-dependent source is needed.

For the fallback example even the unclipped estimate suffices:

    R_P(rho)<=R0/s
      =494830944996550043425/45303671245920620544<565/51.

These statements certify these two fixed families. They neither prove a
uniform theorem for the proposed enlarged classes nor refute such a
common-law theorem. The refuted assertions are specifically the uniform
mixed-loss threshold and, in the primary example, sufficiency of the
*unclipped* global-inflation upper estimate.

## 4. A larger direct-query threshold for arbitrary actual pure layouts

Let the original family now be ANY finite distinct-modulus P-smooth family,
with globally fixed arbitrary phases and arbitrary finite heights. Its
actual pure survivors have masses `w_p >= (p-2)/(p-1)`. This bound follows
by the geometric union bound even if some pure originals overlap.
Set `a_p=1/w_p`, and form the ONE complete pure-product source rho0.
For each nonunit numerical query label d,

    q_d=max_r rho0([r]_d)<=K_d=d^(-1)*product_(p|d)a_p.

Define

    Rcap=sum_(d>1) K_d=product_p(1+a_p/(p-1))-1,
    K3=a3/3, s=1-ell,

where ell is the actual mixed union mass under this rho0. If s>0,
conditioning on its actual full survivor gives

    R_P(H(.|U))<=min(1,K3/s)+(Rcap-K3)/s
                 <=1+(Rcap-K3)/s.                    (LQ1)

Only the numerical label d=3 is removed from the geometric sum. Its cap
need not be attained by an actual query for LQ1 to hold. There is no
independent source selection for different labels.

Let `B=product_(q in Q)(1+a_q/(q-1))>=1`. Then

    Rcap-K3=B-1+a3*(B/2-1/3).

This expression increases in every a_p: its derivative with respect to
a3 is `B/2-1/3>=1/6`, and its coefficient of B is positive. Substitution
of all complete pure bounds therefore gives

    Rcap-K3<=4096/935-1-2/3=7613/2805.                (LQ2)

Combining LQ1--LQ2 proves the conditional uniform statement

    ell<20657/28270
       => R_P(H(.|U))<565/51.                       (LQ3)

The threshold is exactly `1-(7613/2805)/(565/51-1)` and exceeds173/250.
This proves a stronger sufficient DIRECT-query bridge. It does not show
that every arbitrary mixed family meets its premise. Nor does LQ3 alone
establish the extra entropy/unused-label requirements of the existing G.
A failure of the older173/250 test is thus not automatically a failure of
the common-law route.

## 5. Both concrete laws satisfy the existing joint budget

For the two explicit irredundant families, within each prime the retained
pure cylinders are pairwise disjoint. The complete numerical-slot identity from report541 applies
under their respective SAME actual pure sources:

    b=R0-sum_p(a_p-1),
    v=sum_(mixed original d) K_d,
    R_unused(H(.|U))<=(b-v)/s.

The exact upper bounds for primary and fallback are respectively

    4709029096130540354408049/2640435704882446344912896<2,
    84147242070973392673/45303671245920620544<2.

Their full-survivor densities are respectively

    4970375566622841375/346765800571444864<15,
    173200065313275/12413542775279<15.

Use the original `alpha=7235955529/6075000000000`, `Lambda=1/alpha>800`.
The rational exponential bounds `19/7<e<68/25`, certified by positive
Taylor sums and a geometric tail, give

    (19/7)^3>15,       (68/25)^20<800^3.

Thus each concrete law has entropy below3, density belowLambda, and

    R_unused+D_H<2+3=5<20/3<log Lambda.

Both belong to the SAME original G and satisfy the claimed direct-query
bound there. These are statements about the two explicit actual laws;
they do not extend G membership to every family meeting only LQ3.

## 6. Reproduction and verification boundary

The [standalone producer](../../frontier/cover-geometry/shared_support_loss_obstructions.py)
and [exact data](../../frontier/cover-geometry/shared_support_loss_obstructions.json)
contain all255 original numerical moduli, globally fixed CRT residues,
and explicit private points. They check all33,813 within-family
private-point memberships and the actual box inclusion-exclusion sums.
The producer passes427 named checks, including the conditional bridge
constants, all128 pure-cap corners and the concrete joint-budget bounds.
The corner calculation supplements the general monotonicity proof in
Section4; it does not replace that proof.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/shared_support_loss_obstructions.py
```

Only Python3.10+ and its standard library are required. The output defaults
to the sibling `.json`; `--output PATH` selects a different destination.
No previous producer or result data is imported. Execution from a different
working directory through a script path containing spaces reproduced the
same JSON bytes on the tested macOS host. Its SHA256 is
`fe9da80f715564aea03f0e2a3c25c0984f6127feaa8a8fb5adba58662add4b3f`.

An independently written probability calculation uses1,728 primary and256
fallback categorical outside cells instead of box inclusion-exclusion.
It reproduces the exact losses, Haar survivor masses, source norms and
single-query repair. A separate check verifies all255 original rows and
all33,813 private-point memberships. Expected constants were disclosed
before these computations; they are source-independent, not outcome-blind.

The refuted claims concern a proposed uniform LOSS criterion for enlarged
support classes. The two finite families do not refute those classes'
common-law conclusion: each has a positive survivor and a certified law
in G. [Report550](550-a-shared-triangle-tower-preserves-one-common-survivor-law.md)'s
star-plus-triangle theorem remains unchanged. A uniform bound for all
mixed P-smooth supports, and unrestricted Erdős #7, remain unresolved.

[Report556](556-joint-root-queries-admit-the-old-five-seven-tower.md)
uses all seven prime-root queries jointly. Its threshold-two truncation
gives the direct-query loss threshold12808334335598/16672675894875 and
closes the uniform star-plus-triangle-plus-old5/7 support class. Its extra
inventory budget also permits every old7/13 label; the two loss
obstructions above remain valid.
