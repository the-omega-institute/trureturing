# Arbitrary core colors and arbitrary phases outside two finite windows

Let Q={5,7,11,13,17,19}. For the finite two-copy families specified below,
all 144 colors in a first-11 core may be chosen independently and globally,
and every original outside two finite exponent windows may have arbitrary
fixed phases and finite heights. The ONE final actual PA law satisfies

    R_Q(rho)<=257/51-mu<257/51,
    mu=6056459552437856401017774855403
       /612014962076980275282633964800000>0.             (AC1)

The upper bound is approximately5.029319752469421. A joint estimate of the
actual first-11 loss and seven-label response proves AC1 uniformly over
all10^144 core color tables. Neither a rainbow constraint nor a prescribed
color table or cross-depth color-reuse constraint remains. The old
interface geometry, a common 11-ray and the old slot inventory INSIDE the finite core remain assumptions.

This is an ordinary repository-derived proof with an exact finite
optimization, not Lean verification or unrestricted Erdős #7.
[Report552](552-a-finite-first-eleven-core-controls-arbitrary-outside-phases.md)
uses a smaller core with prescribed colors; the present result frees all
colors in a larger core. Neither finite-window scope contains the other.

## 1. The two windows and their numerical labels

Every original modulus is Q-smooth and greater than one; the actual family
is finite, with at most two occurrences per full numerical modulus and
one globally fixed residue per occurrence.

Inside the old window0<=a,b<=4, a+b>0, retain exactly these48 classes:

- For p=5,7, e=1,...,4 and j=1,2, the pure residue j*p^(e-1) modulo p^e.
- For a,b=1,...,4 and t=3,4, the mixed CRT residue
  (3*5^(a-1),t*7^(b-1)) modulo5^a*7^b.

All old originals with a>=5 or b>=5 are arbitrary. The first-11 window is

    0<=a,b<=7, 1<=e<=4, modulus=5^a*7^b*11^e.          (AC2)

Its occupied old cofactor pairs are precisely

    (0,b), b=0,...,7;
    (1,b), b=0,1,2;
    (2,b), b=0,1;
    (a,0), a=3,...,7.

Each of these18 pairs has two slots, indexed j=0,1. At p=5,7 and old
depth d>0 the slot residue is t_p if j=0 or d=1, and t_p+p otherwise,
where t5=4 and t7=5. Depth zero imposes no condition.

Choose ANY color c_(a,b,j,e) in{0,...,9} independently at each slot and
each of the four first-11 depths, with residue

    11^(e-1)-1+c_(a,b,j,e)*11^(e-1) modulo11^e.

Thus the least-significant-first digits are e-1 copies of10 followed by
the chosen color. The core has144 occurrences at72 full numerical
labels. The other184 numerical labels inside AC2 are empty. Equal colors
are allowed, including identical occurrences within the two-copy bound.

Every first-11 original outside AC2, and every later13/17/19 original,
is arbitrary. Outside AC2 even the 11-rays are unrestricted. The
theorem prescribes no infinite comb and imposes no uniform height bound
on the arbitrary finite continuation.

## 2. The same-law joint score

Let lambda0 be Haar restricted to the COMPLETE actual old5/7 survivor.
Write x,y for the actual pure-survivor masses. The first-11 capped kernel
has density k, allowed-fibre fraction g and fibre mass s:

    k=min(5/3,1/g)*1_allowed, s=min(1,5g/3),
    lambda11=lambda0 K11.

At g=0 set k=0. The PA quantities from
[report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md)
and the seven-label caps of
[report551](551-seven-shallow-labels-control-every-rainbow-continuation.md)
are

    F11(x,y)=x/42+y/20+59/840,
    C(x,y)=5xy/363+10x/231+83y/825+4/165,
    G(x,y)=F11(x,y)/3+C(x,y)/4.

For independently chosen query phases at5,7,11,25,55,77,121, put

    f=(1_C5+1_C7+1_C11+1_C25-1)_+
          +1_C55+1_C77+1_C121, 0<=f<=6.

The first-11 saving and seven-label deficit under this SAME actual law are

    S11=F11/3-lambda0(1)+lambda11(1),
    Dseven=C-sup_queries integral f dlambda11.

Consequently their joint score is

    S11+Dseven/4
      =inf_queries [G-lambda0(1)+(1/4)integral(4-f) dlambda11]. (AC3)

The deficit Dseven need not be positive by itself. AC3 retains the
dependence between first-11 loss and next-row response. Maximizing their
adverse contributions separately would discard that dependence.

## 3. Relax all global color tables pointwise

First use only the48 old classes and144 core occurrences. Their raw old
source lambda0,ref has

    xref=313/625, yref=1601/2401,
    lambda0,ref(1)=53759/214375.

At an old point, let M count its active old slots and m=min(M,10).
At depth e let G_e be their distinct colors and K_e=|G_e|. The two
unit-cofactor slots ensure1<=K_e<=m. Every actual table is contained in
the relaxation choosing all four G_e independently at every old point.
Set

    z1=K1/11, z2=K2/121, zT=(11*K3+K4)/14641,
    g=1-z1-z2-zT, h=min(5/3,1/g).

The forbidden cylinders at different depths are disjoint, even when
colors change with depth: the first non-10 digit identifies the depth.
Thus these are the exact allowed fraction and capped density.

Let n count the query indicators at5,7,25; put B=1_(n>=1) and
A=4-(n-1)_+. Let u,v indicate the old parts of C55,C77. The three
root-level11 queries have coefficients B,u,v. Write t=B+u+v and let
t_* sum the coefficients of those queries whose root is10.

A root query j<10 has allowed Haar fraction(1-1_(j in G1))/11;
root10 has fraction1/11-z2-zT. The121 query has THREE kinds:

- first digit j<10: fraction(1-1_(j in G1))/121;
- digits(10,j), j<10: fraction(1-1_(j in G2))/121;
- digits(10,10): fraction1/121-zT.

Denote these kinds by r=0,1,2. At fixed cardinalities the color-dependent
losses are nonnegative. Within each depth, merging all nonsentinel query
colors into one color weakly decreases the local optimized integral:
for K_e<10 that color can be avoided, and for K_e=10 it must be included.
The SAME merged query color is legal globally. This comparison holds at
every old point. Hence the relaxed minimum over every query color tuple
is exactly the minimum over8 root-sentinel masks times3 kinds, or24
patterns. Colors at depth1 and2 may be optimized independently only in
the explicitly enlarged pointwise relaxation.

For such a pattern the largest allowed sum of weighted query fractions
at fixed K1,...,K4 is

    q=t/11+1/121-t_*(z2+zT)-1_(r=2)*zT
       -[(t-t_*)/11+1_(r=0)/121]*1_(K1=10)
       -[1_(r=1)/121]*1_(K2=10).

The local relaxed objective is therefore

    J(K1,K2,K3,K4)=h*[A*g-q].                          (AC4)

It is essential to optimize the four cardinalities, not assume all are
maximal. Enumerate K1,K2=1,...,m. For each pair the numerator and g are
affine in w=11*K3+K4. On g>=3/5 the objective is a ratio of affine
functions with positive denominator; on g<=3/5 it is affine. Each piece
is monotone or constant and the two agree at g=3/5. Its integer minimum
therefore occurs at an attainable endpoint or next to this single kink.

The kink requires

    w=14641*(2/5)-1331*K1-121*K2.

Since12<=w<=120, only K1=K2=4 can cross it, at w=242/5=48.4.
For m<=4 there is no interior crossing. For m>=5 the neighboring
attainable integers are48 and49, represented by(K3,K4)=(4,4),(4,5).
Thus for every K1,K2 it suffices to test

    (K3,K4)=(1,1),(m,m),
    and also(4,4),(4,5) if K1=K2=4 and m>=5.           (AC5)

This gives at most2m^2+2 candidates for each local type. It is a complete
finite reduction, not a height extrapolation.

## 4. Exact finite integration and the relaxation boundary

Partition the old coordinates using the literal pure, mixed and slot
cylinders, with query cuts modulo25 and7. The5- and7-prefix partitions
have73 and91 leaves. Remove the old forbidden union and aggregate by
(x5 mod25,x7 mod7,min(M,10)); there are144 groups with rational Haar
weights. The old query phases range over

    a5=0,...,4; a7=0,...,6; a25=0,...,24;
    a55_old5=0,...,4; a77_old7=0,...,6.

There are30625 tuples for each of24 patterns, hence735000 integrated
objectives. The exact relaxed minimum of integral(4-f) dlambda11 is

    Imin=420749579455862173508/553884116843385453125.    (AC6)

Only pattern0 minimizes globally: all three root queries use one common
non-10 color, and the121 query has that same first digit, kind r=0.
The old phases are(4,6,a25,4,6), with a25 in{14,19,24}.
Substitute AC6 in AC3, using Cref=4270892/36315125, to obtain

    S11+Dseven/4>=kappa_ref
      =280758968969368570519/39879656412723752625000.   (AC7)

This holds for all10^144 global core color tables. The minimizing
pointwise color choices are not an actual global equality witness.
Indeed take x5=4 modulo5^7 and compare y7=6 with y7=3 modulo7.
Both old regions survive and activate exactly the SAME ten old slots.
At the minimizing query, the first region has(A,t)=(3,3), the second
(A,t)=(4,2). Their unique minimizing cardinalities are respectively
(9,10,10,10) and(10,10,10,10). In the first, choosing K1=9 instead of10
improves the local value by5/363; in the second it worsens it by35/121.
A globally fixed coloring cannot assign two cardinalities to identical
active slots. This incompatibility does not affect the lower-bound
argument: the enlarged feasible class has a minimum below every actual
family, and that lower bound already suffices.

## 5. Arbitrary extra old originals preserve the joint comparison

Return to the complete actual old source. Retention of the48 old core
classes gives lambda0<=lambda0,ref. The full two-copy pure cap and the
four prescribed disjoint pure levels give

    1/2<=x<=313/625, 2/3<=y<=1601/2401.

For now use only the core first-11 kernel, with the actual chosen
colors. For each fixed query tuple, the expression in AC3 equals

    G(x,y)-integral[1-s+(1/4)integral f*k dH11] dlambda0. (AC8)

The square-bracketed integrand is nonnegative. It is the same function
under lambda0 and lambda0,ref. Shrinking the old source therefore
decreases the subtracted term. This comparison uses AC8, not measure
monotonicity of the signed integrand4-f.

Every nonconstant coefficient of G is positive, so AC7--AC8 give

    J_core>=kappa_ref-(Gref-Gmin),
    Gref-Gmin=G(313/625,1601/2401)-G(1/2,2/3)
             =10687/466908750.                       (AC9)

The final law still uses every actual old original and the actual pure
parameters. The reference source is used only to bound a nonnegative
charge.

## 6. Joint variation pays all first-11 originals outside the window

At one old point, let A be the core allowed11-set and A' a subset after
all additional first-11 originals. Write a=H11(A), b=H11(A'), delta=a-b,
h=min(c,1/a), h'=min(c,1/b), c=5/3. At zero mass use density c, whose
kernel is zero almost everywhere. The kernel difference has negative
mass h*delta and positive mass p=(h'-h)b. Since b*h'<=a*h,

    0<=p<=h*delta.

The bounds -2<=4-f<=4 yield

    (1/4)integral(4-f)(k_A'-k_A)dH11
       >=-h*delta-p/2>=-(3/2)h*delta>=-(5/2)delta.     (AC10)

This pays the first-11 loss and response change jointly. Integrate
against the SAME actual lambda0. The deletion mass is at most the sum,
over outside-window originals, of11^(-e) times their raw old-cylinder
mass.

For old cofactor exponents a,b, use caps r5(a)r7(b), where r5(0)=x,
r7(0)=y and r_p(d)=p^(-d) for d>0. Set

    A=x+1/4, B=y+1/6,
    a_hi=1/(4*5^7), b_hi=1/(6*7^7).

The complement of AC2 splits disjointly into e>=5 with all a,b, and
1<=e<=4 with a>=8 or b>=8. Its full two-copy cap sum is

    J_actual<=2*[A*B/(10*11^4)
           +(a_hi*B+A*b_hi-a_hi*b_hi)*(1-11^-4)/10]
       <=Jmax=149819363/16442035995000.               (AC11)

The final evaluation uses the reference upper masses xref,yref. The
subtraction in AC11 counts overlapping numerical exponent ranges,
not overlapping probability upper bounds. All finite heights and the
unit old cofactor are included. Total cap sum minus finite-box cap sum
gives the same exact value.

Combining AC9--AC11 with AC7 proves

    S11+Dseven/4>=kappa_final
      =557875428274563578713/79759312825447505250000.   (AC12)

## 7. Arbitrary later rows and one final normalization

After every first-11 addition the actual kernel still has density at
most5/3 and fibre mass at most one. Report551's complete-query cylinder
caps therefore remain valid. Its stability identity for any completed
old query L gives

    integral(L-2)_+ dlambda11<=F13-Dseven.

Apply CP5 at every actual13-exponent and its two numerical slots. The
weights6/13^e over those slots sum to one, giving

    Loss13<=(F13-Dseven)/4, S13>=Dseven/4.

This remains valid when Dseven is negative. Hence S11+S13>=kappa_final;
all later-row savings are nonnegative. The actual mixed deletion has
mass m<=2*sum_(a,b>=1)5^(-a)7^(-b)=1/12. The actual pure deficits are
also nonnegative. The same-law PA/NC4 consumer, with

    T=257/51,
    c0=6168733163201163811/542935350932041267200,

has raw margin at least(T-2)*kappa_final-c0=mu>0. The actual final PA
subprobability has positive mass at most one. Normalize it once to
obtain AC1, and exhaust the complete query labels using their summable
caps. No second credit is taken for either row saving, and the final
mixed-deletion query credit is left unused.

## 8. Exact verification and remaining boundary

The [standalone producer](../../frontier/cover-geometry/first11_allcolor_finite_window_bound.py)
and [exact data](../../frontier/cover-geometry/first11_allcolor_finite_window_bound.json)
construct the literal old cylinders and all144 aggregate cells. The
producer uses the complete local reduction AC5, evaluates all735000
global query cases with bounded integer arithmetic, and reevaluates each
of the24 minima using Python fractions. It also integrates the earlier
actual canonical table as a comparison, reconstructs the NC4 constants
from full geometric moments, and verifies the outside cap sum and margin.
All34 named checks pass; its2184 rational variation cases supplement the
general proof of AC10. The retained JSON SHA256 is
`b66190c1430ff958c3650a16d1b4a622824e481f2f9485b55995221d6ee80283`.

The program requires Python3.10+ and a C++17 compiler supporting signed
128-bit integers, such as GCC or Clang. Generated source and binaries
exist only in a temporary directory. The default output is beside the
script; --output and --compiler are explicit options.
Execution from a different working directory through a script path
containing spaces, without loading shell startup files, produces exactly
the same JSON bytes on the tested macOS host. Other operating systems
were not tested.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/first11_allcolor_finite_window_bound.py
```

An independently written source partition and integer optimizer agree
on all144 group weights, all24 global minima and the finite-window
consumer constants. An independent exhaustive local calculation checks
the reduction against9,696,384 cardinality cases. This was
source-independent verification; the expected minimum was disclosed
beforehand, so it was not an outcome-blind test. No Lean build or full
CRT-period enumeration was run.

The old48-class window, fixed old slots, common ray inside AC2, and
its184 empty numerical labels remain
substantive restrictions. Removing these hypotheses requires further
estimates. Arbitrary first-11 geometry, arbitrary two-copy closure and
unrestricted Erdős #7 remain unresolved.
