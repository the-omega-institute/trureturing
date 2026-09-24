# A finite first-eleven core controls arbitrary outside phases

Let Q={5,7,11,13,17,19}. Consider any finite family of Q-smooth moduli
greater than one, with at most two copies of each full numerical modulus
and all phases fixed globally. Keep only the 30 prescribed pure/mixed
5/7 classes through height three
from [report548](548-rainbow-transport-forces-a-next-row-saving.md).
Every other 5/7-smooth original is arbitrary within the two-copy bound.
At prime 11, prescribe originals only inside the finite exponent box

    0<=a<6, 0<=b<5, 1<=e<=3,
    numerical modulus=5^a*7^b*11^e.                 (FC1)

Inside this box, the family is exactly the 78 classes specified below;
all other cells of this box contain no originals. Outside the box,
EVERY first-11 numerical label may have arbitrary fixed phases, subject
only to the two-copy bound and finiteness of the actual family.
Every later 13/17/19 original is likewise arbitrary.

The ONE final actual PA law satisfies

    R_Q(rho)<=257/51-mu<257/51,
    mu=75634593128793577758661
        /697533477433185357828864000>0.             (FC2)

Thus the entire infinite complement of two finite low-prime windows is
unrestricted. No rainbow, nesting or coordinate-chain assumption is
imposed there. This is a conditional common-law theorem, not arbitrary
first-11 closure or unrestricted Erdős #7. It is an ordinary proof with
exact finite verification; no Lean verification is claimed.

## 1. The finite core and its actual source

Inside the old exponent box 0<=a,b<=3, a+b>0, the subfamily at
moduli5^a*7^b consists of exactly these 30 original classes:

- For p=5,7 and 1<=i<=3, the two pure residues j*p^(i-1) modulo p^i,
  j=1,2.
- For 1<=i,j<=3, the two mixed CRT classes with 5-residue
  3*5^(i-1) modulo5^i and 7-residue t*7^(j-1) modulo7^j, t=3,4.

Every old numerical label with a>=4 or b>=4 may additionally have up to
two arbitrary globally fixed phases. There is no requirement that these
extra originals continue the combs.

Let lambda0 be the Haar restriction to the COMPLETE actual old survivor,
and lambda0,ref the restriction for just the 30 prescribed old originals.
Retaining that finite core gives lambda0<=lambda0,ref. Also lambda0<=sigma,
where sigma is the product of the COMPLETE actual pure-survivor
restrictions. Write their masses as x,y. The numerical two-copy bound
and retention of the prescribed pure classes give

    1/2<=x<=63/125, 2/3<=y<=229/343.              (FC0)

Indeed each entire pure-p forbidden union has mass at most2/(p-1), while
the three fixed levels already forbid2*sum_(i=1)^3 p^(-i). Additional
mixed originals can only shrink lambda0 and do not change this argument.

For a cofactor exponent d>0, define old slot j=0,1 at p=5,7 by

    r_p(j,d)=t_p                 if j=0 or d=1,
             t_p+p               otherwise,
    t5=4, t7=5.

Exponent zero imposes no condition. The finite core uses precisely these
13 cofactor entries and their two color values:

| (a,b) | colors for slots 0,1 |
| --- | --- |
| (0,0) | (0,4) |
| (0,1) | (2,6) |
| (0,2) | (8,8) |
| (0,3) | (1,1) |
| (0,4) | (3,3) |
| (1,0) | (1,5) |
| (1,1) | (3,7) |
| (1,2) | (9,9) |
| (2,0) | (8,8) |
| (2,1) | (9,9) |
| (3,0) | (2,2) |
| (4,0) | (3,3) |
| (5,0) | (6,6) |

For each entry, each slot j and e=1,2,3, combine its old 5/7 residues
with the 11-residue

    11^(e-1)-1+color_j*11^(e-1) modulo11^e.

These are the 78 prescribed first-11 originals. In particular the five
higher-cofactor entries of report548 are NOT prescribed here; they lie
outside FC1 and may be omitted or replaced by arbitrary phases.

Write lambda_core for the law obtained from the actual lambda0 using
only these 78 first-11 originals, and lambda_ref for the law obtained
from lambda0,ref using that same core. For an old point, let K count its
active distinct colors. The allowed 11-fraction and density of this reference kernel are

    g_K=1-133*K/1331, h_K=min(5/3,1/g_K).

The finite reference is a subfamily of every admitted actual family.
The first-11 core kernel is fixed pointwise on the full old coordinates,
so positivity and lambda0<=lambda0,ref give

    lambda_core<=lambda_ref.                       (FC3)

The actual law after ALL first-11 originals will be denoted lambda11;
its kernel need not have the reference color form. These comparison laws
bound payoffs without modifying an original or replacing the final law.

## 2. A bounded payoff supplies the finite certificate

Use the seven numerical query labels 5,7,11,25,55,77,121 from
[report551](551-seven-shallow-labels-control-every-rainbow-continuation.md).
Every query phase at each label is independently arbitrary and fixed.
Let n4 count the four cylinders at 5,7,11,25, and put

    f=(n4-1)_+ +1_C55+1_C77+1_C121, 0<=f<=6.

For pure masses x,y, the seven cylinder caps minus the PA reference
union equal

    C(x,y)=5*x*y/363+10*x/231+83*y/825+4/165,
    Cref=C(63/125,229/343)=366878/3112725,
    Cmin=C(1/2,2/3)=22402/190575.

The finite reference has 30 old originals plus 78 core originals.
Exact integration under its actual capped kernel gives

    lambda_ref(1)=37407967/171199875.

The four-label joint union calculation exhausts all 9625 phases:

| Phase modulo11 | Minimum four-label deficit plus union credit |
| ---: | --- |
| 0 | 28700629/855999375 |
| 1 | 1737867697/60775955625 |
| 2 | 678342615403/48559988544375 |
| 3 | 628920310603/48559988544375 |
| 4 | 28700629/855999375 |
| 5 | 1737867697/60775955625 |
| 6 | 619035849643/48559988544375 |
| 7 | 616564734403/48559988544375 |
| 8 | 835361396278/48559988544375 |
| 9 | 526471991278/48559988544375 |
| 10 | 197791493626/9711997708875 |

The three other individual maxima, exhausting all 253 phases, are

    max lambda_ref(C55)=267593/15073135,
    max lambda_ref(C77)=25285599/2730083125,
    max lambda_ref(C121)=13280282789/4414544413125.

The four-label minimum and sum of the other three cap deficits are

    D0=526471991278/48559988544375,
    D1=3627674504/630649201875,
    Dcore=D0+D1=805802928086/48559988544375.

Consequently, for EVERY joint choice of the seven phases,

    integral f dlambda_ref<=Cref-Dcore.

Apply FC3 to f>=0. All coefficients of C are positive, so throughout the
actual pure-mass rectangle FC0,

    C(x,y)-integral f dlambda_core
      >=Dbase=Dcore+Cmin-Cref
      =338800827094/20811423661875.               (FC4)

The maxima need not be attained together: each individual deficit is a
lower bound valid for every phase, and its label is distinct from the
four labels retained in the actual joint union.

## 3. Adding arbitrary originals can increase density, but only by a controlled amount

Let A be an allowed fibre with normalized Haar mass a, and A' a subset
with mass b<=a. For a density cap c, set

    h=min(c,1/a), h'=min(c,1/b),
    k_A=h*1_A, k_A'=h'*1_A'.

For a zero-mass set define the capped density to be c; its kernel is zero
almost everywhere. Then h'>=h and

    b*h'=min(c*b,1)<=min(c*a,1)=a*h.

The positive variation is therefore

    integral(k_A'-k_A)_+=b*(h'-h)
      <=h*(a-b)<=c*H(A\A').                       (FC5)

In particular, for any 0<=f<=M,

    integral f*k_A'<=integral f*k_A+M*c*H(A\A').

This accounts for renormalization within each actual fibre. Mere
inclusion of the allowed sets would not justify domination of their
capped kernels.

For the present first-11 row, c=5/3 and M=6. Let J_actual be the sum over all
outside-box actual originals of

    11^(-e)*lambda0(the original old cofactor cylinder).

A union bound on the newly forbidden sets and FC5, integrated against
this SAME lambda0, give

    integral f dlambda11
      <=integral f dlambda_core+10*J_actual.           (FC6)

No independent source, alternative residue choice or normalization is
introduced in this comparison.

## 4. Pay every outside-box label with a convergent exact sum

The old cofactor cap is r5(a)*r7(b), with
r5(0)=x, r7(0)=y and r_p(d)=p^(-d) for d>0. Write

    A=x+1/4, B=y+1/6,
    Ahi=1/(4*5^5), Bhi=1/(6*7^4).

The outside of FC1 splits into two disjoint parts:

- e>=4, with arbitrary a,b>=0;
- e=1,2,3, with a>=6 or b>=5.

Summing all numerical labels with two slots per label yields

    J_actual<=J(x,y)
      =2*[A*B/(10*11^3)
          +(Ahi*B+A*Bhi-Ahi*Bhi)*(1-11^(-3))/10].

This is the full convergent tail, not a finite-height extrapolation.
It includes the unit old cofactor when applicable and retains both
numerical slots. Actual overlaps only decrease the union bound.
The expression increases with x,y, whose upper bounds in FC0 are the
reference pure masses. Hence

    J_actual<=Jmax=4051379/34239975000.                 (FC7)

Combining FC4--FC7 gives the uniform seven-label deficit under the ACTUAL
new law:

    C(x,y)-integral f dlambda11
      >=D=Dbase-10*Jmax
      =8796931120759/582719862532500.               (FC8)

## 5. The same actual-law consumer closes every later continuation

The actual new first-11 kernel still has fibre mass at most one and
density at most5/3. Thus every query label retains report551's
unconditional cap, including arbitrary phases at all heights. For a
completed old query L, its exact stability identity is

    F13-integral(L-2)_+ dlambda11
      =sum_(d>1)[P_d-lambda11(C_d)]
         +lambda11(union_(d>1)C_d)-U_PA.

Here F13,P_d,U_PA use the actual pure masses x,y. Retain the seven
label deficits and the four-label union; all omitted deficits are
nonnegative. FC8 implies

    integral(L-2)_+ dlambda11<=F13-D.

Cap summability justifies Tonelli and complete-height exhaustion. Apply
the usual CP5 argument separately to each actual 13-exponent and its two
numerical slots, with weights6/13^e. It bounds the actual 13-row loss and
saving by

    Loss13<=(F13-D)/4,
    S13>=D/4=8796931120759/2330879450130000.          (FC9)

All later 17/19 row savings are nonnegative. The same PA/NC4 consumer
uses T=257/51 and

    c0=6168733163201163811/542935350932041267200.

The actual pure deficits are nonnegative by FC0. If m is the mass of
the actual mixed union inside the actual pure survivors, the full
numerical two-copy bound gives

    m<=2*sum_(a,b>=1)5^(-a)*7^(-b)=1/12.

Thus the mixed packing slack also remains nonnegative, regardless of the
additional old phases. Therefore the unnormalized final margin is

    (T-2)*D/4-c0=mu>0.

Normalize the ONE final actual law once. Its mass is positive and at
most one, so R_Q<=T-mu, proving FC2. No second J13 credit is counted for
the saving already used in FC9; the final JL term is also left unused.

## 6. Verification and remaining boundary

The [standalone program](../../frontier/cover-geometry/rainbow11_finite_core_bound.py)
and [exact data](../../frontier/cover-geometry/rainbow11_finite_core_bound.json)
construct the literal108 original boxes and integrate their actual
capped first-11 kernel. Prefix partitions have53,49,131 leaves at5,7,11;
the program enumerates all9625 joint phases and253 individual phases.
All22 named exact checks pass, including a separate finite-box
subtraction formula for the outside cap sum and the strict NC4 margin.
The variation lemma has455 exact rational stress cases in addition to
its general proof above. A separately written implementation reproduces
the phase certificate and final constants.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/rainbow11_finite_core_bound.py
```

The retained JSON SHA256 is
`b4b7131ffbce0c3e1d177c22c6ec3568d09285f5cdd087974473a00e621e2ef3`.
No Lean build or full CRT-period enumeration was run.

The first-11 box FC1 still prescribes both its occupied and empty cells;
the old box0<=a,b<=3 still prescribes its 30 original phases. Everything
outside these two finite windows is arbitrary under the stated finite
Q-smooth two-copy hypotheses. Removing the finite-core assumptions
requires a new uniform estimate or an independent source of savings. This result does not settle
arbitrary first-11 families, arbitrary two-copy closure or Erdős #7.

[Arbitrary core colors](553-arbitrary-core-colors-and-arbitrary-outside-phases.md)
are possible in a larger two-window theorem: all144 first-11 colors,
including different colors at different depths of each old slot, may be
chosen independently. The proof keeps first-11 loss and next-row response
in one joint estimate. Both results allow arbitrary originals outside
their respective finite windows; their core hypotheses differ.
