[Index](../../marked_head_profile.md) · [Previous](03-arbitrary-height-transfer-for-matching-kernels.md) · [Next](05-the-actual-rectangle-gives-two-further-square-savings.md)

<a id="the-weighted-upper-quantile-lemma"></a>
### The weighted upper-quantile lemma

Put α=min(1,M/K). Let X_α be the upper α-quantile of X, splitting the
boundary atom as necessary, and put T_α=αEX_α. For every complete old
load A and nonnegative increasing convex g,

    Eμ[k g(A)]≤KαE g(X_α).                                   (VH3)

Proof: write w=k/K, so 0≤w≤1 and Ew≤α. At a quantile boundary t choose
z=g(t)≥0. Then

    E[w g(A)]≤αz+E(g(A)−z)_+
               ≤αz+E(g(X)−z)_+=αE g(X_α).

The middle step uses the old increasing-convex comparison. It neither
asserts nor requires independence of k and A. This is the same
upper-quantile argument already used for survivor conditioning, now
applied to the old-point weight.

For 0≤j≤K≤12, D_j is positive, decreasing and concave. Every numerator
in (VH1) is a positive affine function with nonnegative slope. Such a
ratio is increasing and convex: differentiating twice gives

    (N/D)''=−2N'D'/D²+N[2(D')²/D³−D''/D²]≥0.

The same differentiation applies to each of the four individual
diagonal coefficients, not just their sum F_j. Consequently every
individual low or high coefficient is monotone, and each scalar bound
f_j used below satisfies

    f_j≤f_0+(f_K−f_0)j/K.                                   (VH4)

In particular, for each complete old load A,

    Eμ[f_k A]≤f_0M+(f_K−f_0)T_α.                            (VH5)

The same statement holds for partial original cofactor loads by
completing them before applying the inequality.

<a id="better-high-class-mass-and-square-bounds"></a>
### Better high-class mass and square bounds

For the actual finite higher heights put

    u_p=Σ_(t=1)^(H_p−1)p^(−t),
    v_p=Σ_(t=1)^(H_p−1)(2t−1)p^(−t), w_p=4u_p+v_p.

Uniform bounds for all finite heights use

    u11=1/10, u13=1/12, w11=13/25, w13=31/72.

Define

    T_j=(R_j+a_j)u11+(C_j+a_j)u13+a_j u11u13,
    E_j=(R_j+3a_j)w11+(C_j+3a_j)w13+a_j w11w13,
    χ_j=F_j+E_j.                                             (VH6)

The functions T_j,χ_j are again increasing and convex. Apply (VH5) to
each original exponent group in the high-class union bound. Distinct
original labels give at most one old cofactor class per divisor in each
group, exactly as in the existing height theorem. The actual removed
mass is at most

    Λ=T_0M+(T_K−T_0)T_α.                                   (VH7)

This improves the worst-K value T_KM whenever K>M: since X≥1 and α<1,
T_α<M, and T_K>T_0 whenever a higher digit is present.

There is also a rebate in the high square terms. Every complete old
load A_e is at least one, and therefore A_eA_f≥1 pointwise. If a high
pair has cap κ_j, replace κ_k A_eA_f by

    κ_K A_eA_f−(κ_K−κ_k).

Integrating uses E A_eA_f≤G. Summing all high pairs, and retaining the
existing common-diagonal low-group rebate, gives

    Γ(ν0)≤χ_KG−Eμ(χ_K−χ_k)
           ≤U:=χ_KG−(χ_K−χ_0)(1−α).                        (VH8)

Thus the same minimum-load argument applies to both the low and high
parts. In particular the low contribution alone retains the stronger
mean-hole saving (F_K−F_0)(1−α), which dominates the previously available
γ(K−M)_+ bound.

If Λ<1, condition ν0 on actual high-class survival. Every full load has
square at least one, so

    Γ(ν)≤J:=(U−Λ)/(1−Λ).                                   (VH9)

U≥1 follows from its valid bound on the square of a complete load. The
survival probability used here and below is s=1−Λ; it is a lower bound
on the true surviving mass, not an equality claim.

<a id="a-weighted-full-comparator"></a>
### A weighted full comparator

Let τ be the reference law that is uniform on each available 10×12
rectangle, given the old point x, and uniform on all higher digits.
Its constant conditional prefix caps give the independent auxiliaries
N=N11N13 used in MH3, independent of X. The weighted C1 comparison is
valid for the finite old measure kμ as well as for μ. Combining it with
(VH3) and Jensen for the complete old loads gives, for every nonnegative
increasing convex g,

    Eτ g(L)≤E g(XN),
    Eτ[k g(L)]≤KαE g(X_αN).                                (VH10)

The conditional reference kernels can depend on x through the available
sets: their common caps are what make the auxiliary N independent of x.
Each old load used after comparison is fixed before x is sampled.

The actual degree-weighted kernel has pointwise density at most d_k
relative to τ. Apply (VH4) to d, noting d_0=1. Then

    Eν0 g(L)≤E g(XN)+(d_K−1)αE g(X_αN).                     (VH11)

Define the finite comparison measure on old load values

    W_old=Law(X)+(d_K−1)αLaw(X_α),
    Dbar=mass(W_old)=1+(d_K−1)α.                            (VH12)

Multiply its old values by the independent N11N13; call the resulting
finite measure W. It has the same mass Dbar. The full comparator for
ν is the upper s-mass of W, normalized to mass one, equivalently the
upper ell-quantile of W/Dbar with ell=s/Dbar.

Indeed for every nonnegative increasing convex h and every real z,

    Eν h(L)≤z+(1/s)∫(h(y)−z)_+ dW(y).                       (VH13)

Take z at the corresponding quantile boundary. This proves a common
full convex comparison on exactly the law used in (VH9).

The formula is not an average-density replacement. The excess density
has been assigned to the upper old-load quantile X_α, which accounts
for the worst permitted correlation with hole count. The old finite
measure has total mass Dbar, so it must be normalized or integrated as
a finite measure; treating its atoms as a probability would be wrong.

<a id="strict-improvement-over-the-worst-k-comparison"></a>
#### Strict improvement over the worst-K comparison

For every nonnegative g,

    ∫g dW=E g(XN)+(d_K−1)αE g(X_αN)≤d_K E g(XN),

since the upper old quantile is a submeasure of Law(X). Simultaneously
Λ≤T_KM and U≤χ_KG. Thus (VH9) and (VH13) improve the same-law worst-K
height and density bounds. For K>M, the square, removed-mass, and
every finite hinge bounds improve strictly at positive higher heights.
The hinge statement uses the unbounded positive auxiliary N: even the
discarded lower old quantile contributes a positive hinge expectation.

<a id="dependence-on-k"></a>
#### Dependence on K

At fixed ε and within a common valid kernel range, all these bounds
are nondecreasing as K increases. For K≥M, write α=M/K. The secant
slopes(f_K−f_0)/K increase by convexity, and expectations under the
upper α-quantile increase as α decreases. These observations prove
monotonicity of Λ and of the raw comparison cost in (VH13). Also

    U=χ_0G+(χ_K−χ_0)(G−1)+M(χ_K−χ_0)/K

is nondecreasing, since G≥1. The survivor lower bound decreases, so J
and the final full comparator increase. For K≤M the formulas reduce
to the already monotone worst-K values. This is monotonicity of the
guaranteed bounds, not a claim about the optimized Γ of different
physical laws.

Choosing a different ε for each K changes the comparison and requires
separate evaluation. The exact verifier evaluates ε=1/(207K) for
K=1,…,12; no tail scheduling is part of that computation.

<a id="exact-k12-input"></a>
### Exact K=12 input

Take ε=1/2484 and the infinite geometric majorants, which cover every
finite 11/13 height. Then

    α=271/1032,        T_α=1633/1118,
    d_K=1664/1491,     Dbar=1585595/1538712,
    Λ=164881/2683200,  s=2518319/2683200,
    U=3968983906721/166180896000,
    J=51464038499033/2027599359660.                          (VH14)

The upper old α-quantile starts at 4. Its raw subprobability atoms are
1631/13416 at 4 and the original X masses at 5,6,8,12, with zero below 4.
Consequently W_old has these exact atoms:

| Value | Unnormalized mass |
| ---: | ---: |
|1|581/6966|
|2|3031/6966|
|3|146/1053|
|4|5552881/25718472|
|5|1280/165501|
|6|1920/18389|
|8|1664/55167|
|12|832/55167|

After multiplying by the independent auxiliaries,

    ∫y dW(y)=226440629/56347200,
    W{1}=6391/92880, W{2}=807835/2173392,
    ell=s/Dbar=3754813629/4122547000.

The upper s-mass of W starts at 2, strictly inside its atom. The final
comparison law Z therefore has

    Pr(Z=2)=37653203663/101379967983,
    Pr(Z=z)=W{z}/s for integer z>2,
    EZ=46851298771/11264440887.                              (VH15)

Numerically J≈25.38175910 and EZ≈4.159220972. The corresponding
worst-K bounds are J≈25.53775188 and comparison mean≈4.246698684.
The next theorem uses these head inputs in a fully certified tail continuation.

<a id="reuse-verification-and-scope"></a>
### Reuse, verification and scope

The kernel PSD bound is supplied by the independent degree-weighted
point-hole proof. Existing repository inputs are C1–C3 for arbitrary
finite old measures, AP2–AP7 for conditional comparison with original
labels, MT7 for the low minimum-load rebate, the established high pair
count, and the old 315 comparator X. The upper-quantile lemma itself is
standard reuse. The quantitative new combination retains the same
hole-count weight through high deletion, square, density and profile;
it does not create a bind-only Lean wrapper.

The adjacent standard-library verifier recomputes these exact inputs for K=1,…,12, all individual coefficient chord inequalities and 300 hinge comparisons. The symbolic argument establishes the continuous-domain bounds; the finite checks verify the displayed arithmetic.

<a id="all-cross-point-labels-with-arbitrary-heights-and-unrestricted-tails"></a>
## All cross-point labels with arbitrary heights and unrestricted tails

**Theorem.** Let a finite family have distinct odd nonunit moduli, and let
the full 3/5/7 part of every original modulus divide 315. Choose the
canonical supported old law μ. At each old point x suppose there are
10 first 11-digits avoiding all active classes of moduli d·11, and
12 first 13-digits avoiding all active classes of moduli d·13, for d|315.
The available sets may depend on x. Then the family cannot cover.
There is no restriction on the residues of the classes of moduli d·143,
on any higher 11/13 exponents, or on the number, exponents and interactions
of tail primes from 17.

Choose such available sets A_x,B_x. The actual d·143 classes remove
at most twelve distinct points of A_x×B_x, with hole count k(x) bounded
by one complete old cofactor load. Thus 0≤k≤12 and Eμk≤271/86.
Apply AH1–AH9 and VH1–VH15 to these actual holes, without adding virtual
holes. All complete original labels remain distinct even when their
projections coincide. After lifting to the full original heights and
conditioning away high head classes, the same supported law has

    J_head≤51464038499033/2027599359660,
    Θ_head(t)≤E(Z−t)_+,   EZ=46851298771/11264440887.

Use this complete comparator in AP2 and the separate square bound in
AP5. The fixed schedule in `arbitrary_holes12_tail17` processes every
prime from 17 through 2903: 414 steps, global prime index 420. Directed
exact arithmetic gives

    C_tail≤205435101024428611/250000000000000000,
    survivor mass≥44564898975571389/250000000000000000,
    Γ_stop≤1751428432885843299077/178259595902285556
           <9826<9833<420(log420+loglog420−3)^2.              (AH10)

For the last inequality, independent positive rational atanh sums give
log420>604025/100000 and loglog420>179844/100000. The resulting lower
bound is 4916713392381/500000000>9833. AP6 and the T1–T6 transfer to
BBMST Theorem 6.1 continue through every later prime. If the family
ends sooner, the positive prefix survivor mass already suffices. CRT
then supplies an integer outside every original class.

The verifier retains 768 low product states and includes the entire
omitted tail through the exact comparator mean. Probabilities and
moments are rounded upwards on a grid of 10^-18, and every hinge
correction has a nonnegative coefficient. An independent implementation
with trial-division prime generation and a 10^-24 grid confirms Γ<9826.
The prior single-hole certificate is retained unchanged and gives its
stronger numerical bound on that smaller class.

This theorem removes the earlier point-hole restriction entirely. The
axis hypothesis is still substantial: at any old point the active
first-power 11-axis classes must forbid at most one distinct digit,
and likewise for 13. Several different forbidden axis digits can
violate that hypothesis. Higher 3/5/7 powers also remain outside this
statement. The result is an ordinary proof with exact certificates,
not an unrestricted solution of Erdős #7 or an end-to-end Lean theorem.


<a id="unrestricted-axis-deletions-and-the-optimal-scalar-clipped-bound"></a>
# Unrestricted axis deletions and the optimal scalar clipped bound

For every family of distinct nonunit moduli dividing
315·11^H·13^J, H,J≥1, the construction below gives one probability
supported on the full survivors with

    Γ≤42723250051/1147550665 ≈37.229946663.                    (VC1)

There is no restriction on the original axis deletions or point-hole
pattern. The bound covers all finite H,J. The full3/5/7part must still
divide315. The same law has a full increasing-convex comparator of mean

    1263555626/229510133 ≈5.50545,

specified below. These are head bounds, not a completed unrestricted-tail
continuation. An exact robust linear program proves that(VC1)is the
best bound from the stated scalar clipped certificate for all C≥1;
it does not prove optimality among actual supported laws.

<a id="actual-varying-rectangles-and-their-area"></a>
### Actual varying rectangles and their area

Use the canonical supported old315law μ, with common old comparator X,
EX=M=271/86, Γ315(μ)≤G=1131/86, and complete old loads in{1,…,12}.
First exclude the actual pure11and13root classes. If a root class is
absent, an arbitrary virtual root exclusion only restricts support.
The reference first-digit carrier is a10×12rectangle.

Let u(x),v(x) be the numbers of distinct remaining rows and columns
deleted by actual axis classes. By original-modulus distinctness there
are complete old layouts A,B with

    u≤A−1, v≤B−1.

Let D be a third complete old layout whose load bounds the number of
active mixed11·13·d labels. There is at most one original label per
d|315; repeated cells only reduce the number of holes. If N(x) is the
actual remaining first-digit cell count, then

    N(x)≥S(A,B,D):=[(11−A)_+(13−B)−D]_+.                    (VC2)

This retains the rectangular overlap u·v. It does not spend one common
vertex budget on both axes or select a fixed smaller rectangle. It
allows N=0 and makes no independence assumption about A,B,D.

Let τ sample x from μ, then sample uniformly from the10×12reference
rectangle and all extra11/13digits. Write s(x)=N(x)/120. Fix C≥1 and
define a subprobability measure ξ on the actual low survivors by the
following density relative to τ:

    f(x,y)=1_low-survives(x,y) min(C,1/s(x)).

Set f=0 when s=0. Its old row mass is

    h_C(x)=min(1,Cs(x)),    Z=Eμ h_C≤1.                      (VC3)

Thus empty fibres receive zero mass automatically, and the old marginal
is allowed to change. The density is at most C, while the old marginal
is bounded by μ. These two properties are used separately.

<a id="exact-area-information"></a>
### Exact area information

For each of A,B,D impose all known marginal hinge bounds

    t: 0,1,2,3,4,5,6,8;
    θ(t):271/86,185/86,100/81,61/81,16/39,7/26,5/37,2/37,

and the square bound1131/86. Let P range over probability distributions
on the1728triples{1,…,12}³ satisfying these constraints. Then

    Z≥Z_*(C):=min_P E_P min(1,C S(A,B,D)/120).                (VC4)

This is an information relaxation: its distributions need not arise as
three actual arithmetic layouts. A feasible dual gives a universal
lower bound, and exact feasible primal distributions establish sharpness
within this specified marginal information.

At C=1 the exact optimum is

    Z_*(1)=3705715/6185808.

One pointwise certificate is

    S≥110−7(A−1)_+−4(A−2)_+−(A−6)_+
           −5(B−1)_+−4(B−2)_+−(B−6)_+−(D−1)_+.

At C=3/2 the exact optimum is1004221/1246752. Their finite marginal-profile optima are exact; the global clipped certificate below resolves the choice of C.

The constant used in(VC1)is

    C*=40/31,        Z_*(C*)=74101/97929.                    (VC5)

Its particularly short pointwise dual is

    min(1,S/93)
      ≥1−3(A−2)_+/31−2(A−4)_+/93
          −7(B−2)_+/93−2(B−4)_+/93−(D−2)_+/93.             (VC6)

The finite certificate verifies(VC6)for every triple. Averaging the
five hinge terms gives exactly the value in(VC5).

<a id="high-class-deletion-and-the-complete-square-bound"></a>
### High-class deletion and the complete-square bound

The uniform higher-digit reference has per-prefix caps
11^(−(a−1))/10,13^(−(b−1))/12 and their product. The sum over all
actual high original labels therefore has τ-mass at most

    λ0=M[(13/120)(1/10)+(11/120)(1/12)
                           +(1/120)(1/10)(1/12)]
       =24119/412800.                                       (VC7)

This is the existing distinct-cofactor height count; finite heights only
decrease it. Since ξ≤Cτ, the actual high deleted ξ-mass β is at most
Cλ0. No disjointness or preservation of every old fibre is assumed.

For a complete fine test layout, group its load by the full11/13
exponent pair. The old-only group A00 has

    ∫h_C A00² dμ≤G−Eμ(1−h_C)=G−1+Z.

Every other ordered pair has at least one positive new exponent.
The ξ-prefix intersection mass is at most C times the reference cap;
the old load product has expectation at most G by Cauchy–Schwarz.
The sum of all reference coefficients, including the old-only pair, is

    χ0=(1+(3+13/25)/10)(1+(3+31/72)/12)
       =187759/108000.

Consequently

    Γ(ξ)≤G−1+Z+C(χ0−1)G.                                   (VC8)

Here Γ is extended homogeneously to finite measures, as in the existing
weighted rectangle transfer. This uses the actual old marginal cap and
does not replace the entire right side by CΓ(τ).

Delete all actual high classes and normalize. The remaining mass is
at least Z_*(C)−Cλ0. Every full load is at least one, so deleting β
saves at least β from its square integral. Whenever the mass bound is
positive, the resulting single supported probability ν_C satisfies

    Γ(ν_C)≤1+[G−1+C(χ0−1)G]/[Z_*(C)−Cλ0].                  (VC9)

At(VC5)the denominator is

    Z_*(C*)−C*λ0=229510133/336875760>0,

and(VC9)is exactly(VC1). At heights H=J=1 there are no high exclusions
and the reference square factor is13/8. The same C* gives

    Γ≤99014608/3186343 ≈31.075.

This improves the earlier unrestricted first-height sequential bound
388385/10979≈35.375. It is not asserted to be the optimal first-height
choice of C.

<a id="full-profile-on-the-same-law"></a>
### Full profile on the same law

Under τ the existing conditional comparison gives the common auxiliary

    Y=X N11 N13,

with independent factors and Pr(Np=1)=1−1/(p−1),
Pr(Np=k)=p^(1−k)for k≥2. The old/reference sets are fixed at10×12;
actual low deletions are in ξ and may vary arbitrarily with x.

The final law has density at most C/[Z_*(C)−Cλ0]relative to τ. Hence
its full increasing-convex comparator is the normalized upper ρ_C
quantile of Y, where

    ρ_C=Z_*(C)/C−λ0.

At C*, this fraction is229510133/434678400. The boundary is strictly
inside the atom at3. The reference mean and first masses give

    E comparator
      =3+[EY−3+2Pr(Y=1)+Pr(Y=2)]/ρ_C
      =1263555626/229510133.                                (VC10)

This comparator and(VC1)bound the same ν_C*. The scalar density
comparison is a limitation of the current argument: C=1 has a weaker
square bound≈41.440but a slightly smaller comparison mean≈5.447.
Thus square improvement must not be advertised as a simultaneous
improvement of every profile value. These head bounds alone do not provide a certified unrestricted-tail continuation.

<a id="a-sharper-first-moment-under-the-same-law"></a>
### A sharper first moment under the same law

The old marginal cap also gives a first-moment estimate stronger than
(VC10). For each complete old test load A, the unit term gives
`∫h_C A dμ≤M−1+Z`. All positive new-exponent groups have total reference
first-moment coefficient `Nmean−1`, where

    Nmean=E(N11 N13)=(111/100)(157/144)=5809/4800.

Their ξ-integral is at most `C(Nmean−1)M`. Deleting high-class mass β
saves at least β from every complete-load integral. The same normalization
as (VC9) therefore gives

    sup_test Eν_C L
      ≤1+[M−1+C(Nmean−1)M]/[Z_*(C)−Cλ0].

At C=40/31 this is

    M*=1242116000/229510133≈5.41203120.                     (VC11)

It holds simultaneously with the actual square bound (VC1) and the
full comparator (VC10). The comparator's own mean remains the larger
`1263555626/229510133`; inserting M* in an identity for that comparator
would be invalid.

<a id="global-optimization-of-this-scalar-certificate"></a>
### Global optimization of this scalar certificate

For a fixed C, the dual to(VC4)maximizes

    Z=ν+Σ_i y_i b_i,
    y_i≤0,
    ν+Σ_i y_i f_i(l)≤1,
    ν+Σ_i y_i f_i(l)≤C S_l/120   for every triple l.

The f_i are the27marginal hinge/square features and b_i their bounds.
Set A0=G−1,B0=(χ0−1)G. To minimize(VC9)over all C≥1 and all valid
dual lower bounds, apply the standard linear-fractional substitution

    t=1/(Z−Cλ0), z=Ct, v=νt, w_i=y_it.

The objective becomes1+A0t+B0z, subject to

    v+Σ_iw_i b_i−zλ0≥1,
    v+Σ_iw_i f_i(l)≤t,
    v+Σ_iw_i f_i(l)≤z S_l/120,
    w_i≤0, t≥0, z≥t.

This is one linear program with30variables and3458constraints. Finite
LP duality makes the formulation exact for the current information
relaxation. A positive feasible denominator exists by(VC5); scaling
forces equality in the normalization constraint at an optimum.

The retained exact primal and dual have equal objective

    1+41575699386/1147550665.

The primal yields C=40/31; the dual has15nonzero inequality multipliers.
The independent verifier checks every primal inequality, every dual
sign, all30stationarity coordinates and exact equality. This proves
global optimality for this particular scalar clipped proof, without a
parameter grid. Improving its all-height square conclusion requires
additional information, such as the actual weighted old test energy,
rather than further optimization of C within the same certificate.

The measure construction reuses the residual-capacity and weighted
conditional comparisons above. The quantitative input is the actual
two-axis area objective, retaining its rectangular overlap, and its
exact optimization under the three complete old marginal profiles.
This is an ordinary proof with exact rational certificates, not an
end-to-end Lean theorem or an unrestricted solution of Erdős #7.

<a id="retaining-the-common-old-shape-and-survivor-count"></a>
## Retaining the common old shape and survivor count

The same construction at the fixed constant C=40/31 satisfies the stronger
simultaneous bounds

    Γ≤2167128283/58962460 ≈36.754373597,
    sup_test Eν L≤24790300/4595881 ≈5.394025651.               (SC1)

These hold for every family of distinct nonunit moduli dividing
315·11^H·13^J, with arbitrary finite H,J≥1 and arbitrary axis and point
deletions. The full 3/5/7 part must divide 315. The improvement retains
information from the six canonical 45 shapes and their actual septenary
survivor count. This is the 45×7 divisor geometry of the odd part of
5040=16·315.

Fix the one old shape S selected by the original family, write n=|S|,
and let N be its actual 315 survivor count. Every test load and every
axis/cross activation load is evaluated on this same law. The possible
pairs (S,N) comprise 144 branches: N ranges from (77,78,78,75,74,74),
respectively, to 6n for the six shapes. None of the different loads may
choose a different branch.

<a id="deleted-energy-at-a-fixed-survivor-count"></a>
### Deleted energy at a fixed survivor count

Put D=6n−N=Σₓb(x), using the actual deleted-digit counts from (D1).
For a nonnegative old cost h(A(x)), let T_D be the sum of the D smallest
entries among five copies of each h(A(x)). Since 0≤b(x)≤5,

    Σₓb(x)h(A(x))≥T_D.

The original cofactor labels give an additional lower bound. For every
η≥0, the identity b h=ηb−b(η−h), followed by
b≤Σ_d 1_Cd, gives

    Σₓb(x)h(A(x))
      ≥ηD−Σ_(d∈{3,5,9,15,45}) max_C Σ_(x∈S∩C)(η−h(A(x)))_+.
                                                                  (SC2)

Thus the maximum of T_D and all the right sides of (SC2) is a valid
deleted-energy lower bound L_D(A,h). The finite verifier takes η from
zero and the actual cost values. This finite selection is sufficient
for the bound; no optimality over η is required.

For h_t(a)=(a−t)_+, use (D3) to obtain

    Eμ(L−t)_+
      ≤max_A [5H_t(A)+min_(0≤k≤t)(H_k(A)+M_(t−k))
                         −L_D(A,h_t)]/N.                        (SC3)

For h(a)=a², (D4)'s numerator gives

    Eμ L²≤max_A [6ΣA²+2R(A)+Q−L_D(A,h)]/N.                     (SC4)

Intersect these bounds with the already proved constants for this same
shape. The resulting M_(S,N), G_(S,N), θ_(S,N)(2), θ_(S,N)(4) all hold
simultaneously for every complete old test layout. Effective old layouts
suffice: completing an inactive test cylinder only increases a load.
All 27,720 such layouts are checked directly.

The elementary old bound Φ(3)≤5 and old load≤6 also give
Eμ(L−6)_+≤10/N by the fibre inequality. Consequently any two complete
loads U,V on the same old law satisfy the useful joint restriction

    Eμ U²+50 Eμ(V−6)_+≤max_(S,N)(G_(S,N)+500/N)=761/39.       (SC5)

It retains a common arithmetic branch even when U and V are different
layouts. Separate globally maximized square and hinge constants discard
that information.

<a id="transfer-on-each-common-branch"></a>
### Transfer on each common branch

Use exactly the existing pointwise inequality (VC6). Its average on one
branch gives the low-mass lower bound

    Z_(S,N)=1−[17θ_(S,N)(2)+4θ_(S,N)(4)]/93.

The same branch's higher deletion bound is λ_(S,N)=89M_(S,N)/4800.
Set s_(S,N)=Z_(S,N)−(40/31)λ_(S,N). Applying (VC9) and the first-moment
argument to that one branch gives

    Γ≤1+[G_(S,N)−1+(40/31)(χ0−1)G_(S,N)]/s_(S,N),
    sup_test Eν L
      ≤1+[M_(S,N)−1+(40/31)(5809/4800−1)M_(S,N)]/s_(S,N).
                                                                  (SC6)

Here χ0=187759/108000 as before. Every s_(S,N) is positive. The largest
square bound occurs in the first shape at N=81, where

    M=253/81, G=1131/86, θ(2)=100/81, θ(4)=32/81,
    Z=5705/7533, s=68561/100440.

Substitution gives the intermediate square bound
547762402/14740615≈37.160077921. The actual-rectangle refinement below
gives the square bound in (SC1). The largest first-moment
bound occurs in the same shape at N=84 and gives the other bound in
(SC1); these are uniform bounds on the same constructed law, not a claim
that one family attains both extrema.

The smallest certified full mass is 68561/100440. Hence that law's
density relative to the old uniform reference is at most
(40/31)/(68561/100440). It also has the full increasing-convex comparator
given by the upper

    ρ=68561/129600

quantile of the existing Y=X N11 N13. Its boundary is at 3 and its mean
is 1264886009/229953594. The comparator and both actual moment bounds in
(SC1) apply to the same law.
