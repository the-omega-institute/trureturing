[Index](../../marked_head_profile.md) · [Previous](22-comparing-the-two-killed-steps.md) · [Next](24-actual-radial-families-retain-a-strict-common-test-loss.md)

<a id="actual-maximizing-tests-constrain-the-killed-pair-matrix"></a>
### Actual maximizing tests constrain the killed pair matrix

Fix one finite actual family, its normalized physical incoming law
sigma and its actual killed kernel K_p^-. Set eta=sigma K_p^- and
z=eta(1). The finite complete original test-label set J includes the
unit label. Partition it into J0 and J+ according to whether the
current exponent is zero or positive. For one globally legal test put

    A=sum_(i in J0) I_i, C=sum_(i in J+) I_i,
    L=A+C, P_ij=integral I_i I_j d eta,
    X(P)=integral(2AC+C^2)d eta
        =sum_(i or j in J+)P_ij.                     (KB1)

The sum in KB1 is over ordered pairs in J times J.
The finite residue choices give an actual maximizing test for X(P).
Assigned bad mass b is fixed while its test residues vary, so this
also maximizes F_p^-(W)=Wb+X(P). The measure eta, forbidden union and
physical normalization do not change when one test residue changes.
All statements below hold at arbitrary finite original heights.

For ell in J+, replacing I_ell by any other legal residue indicator J
changes X(P) by exactly

    integral (J-I_ell)(2(L-I_ell)+1)d eta.            (KB2)

At a maximum the chosen score is at least each replacement score.
Average over all m_ell classes of this original modulus, whose
indicators sum to1. This yields

    m_ell[2 sum_(j!=ell)P_(ell,j)+P_(ell,ell)]
        >=2 sum_(j!=ell)P_(j,j)+z.                   (KB3)

For a positive current height e, retain that label's old residue and
its literal current parent prefix of depth e-1, with indicator V.
Its p next-digit siblings partition V. Averaging the same replacement
scores over those p alternatives gives

    p[2 sum_(j!=ell)P_(ell,j)+P_(ell,ell)]
        >=2 sum_(j!=ell)P_(V,j)+P_(V,V).              (KB4)

Entries involving V use the same eta. V is the virtual parent of
this particular original label; it is not the independently chosen
original test at a smaller modulus. A shallow cylinder retains all
its extensions. A sibling may be omitted from the averaging only
when its score is identically zero under the whole actual measure;
being killed in some old rows is insufficient.

Zero-current labels have a different score because KB1 omits A^2.
For ell in J0 the replacement change is

    2 integral (J-I_ell) C d eta.                    (KB5)

Full residue averaging and literal old-coordinate sibling averaging
therefore give, respectively,

    m_ell sum_(j in J+)P_(ell,j)
        >=sum_(j in J+)P_(j,j),                      (KB6)

    p sum_(j in J+)P_(ell,j)
        >=sum_(j in J+)P_(V,j).                      (KB7)

In KB7, p is an old prime with positive exponent in that label; the
unit label has no sibling refinement. Applying
KB3 to a zero-current label would optimize an extra A^2 term and is
not justified. Every legal replacement comparison occurs after
integrating across all old rows, with one replacement residue used
throughout those rows.

For an upper optimization let R contain the exact b, chosen P and
virtual-parent entries of every actual candidate, with any retained
source, union and CR constraints. Let g_r(P) be the left side minus
right side of any KB3--KB7 constraint. Every actual maximizing test
satisfies g_r(P)>=0. Thus, for fixed lambda_r>=0,

    sup_(actual families)F_p^-(W)
      <=sup_((b,P) in R)
          [Wb+X(P)+sum_r lambda_r g_r(P)].           (KB8)

Indeed at the actual maximum the added term is nonnegative, and
its data belong to R. The positive sign is required: an outer
candidate with negative optimality residual is penalized. One may
instead impose g_r>=0 directly. These constraints do not permit
independent maximization of separate Gram entries.

At17 the incoming probability is nu13; at19 it is normalized physical
mu17=nu13 K17. KC takes separate Xi suprema, so each step may use
its own maximizing complete test for this upper bound. A common
maximizer for the two steps is not assumed. The existing generic Gram
projection is unchanged. KB3--KB7 add the correct objective's actual
optimality conditions; their numerical improvement to the unrestricted
KC frontier has not been computed. No new Lean declaration is added.

<a id="a-scalar-countermodel-for-every-square-shift-in-the-fixed1719-continuation"></a>
### A scalar countermodel for every square shift in the fixed17/19 continuation

The21 scalar observations currently retained for the supported AP(4,6)13
law do not close the following fixed17/T8,19/T8 common-N functional,
even after optimizing the square shift and choosing any pointwise-majorizing
clip. There is one abstract positive integer-valued source satisfying all21
observations for which the direct functional has minimum

    67033659073176343/16899387908832000
        =3.966632367681379... >0.                         (ASB1)

The minimum occurs at shift121. This is a countermodel to the specified
scalar relaxation. It is not an actual congruence family or an asserted
realization under the AP13 construction, and it gives no lower bound on
an actual killed frontier. Other schedules and additional observations
are outside the conclusion.

<a id="the-fixed-functional-and-its-pointwise-majorants"></a>
#### The fixed functional and its pointwise majorants

For p in{17,19}, keep threshold8 and define

    a_p=(3p-1)/(p-1)^2,
    c_p=(p-1)/(p-9),
    kappa_p(z)=(p-1)/(p-1-min(z,8)).

For a real square shift0<=tau<=484 put W=484-tau. The direct cost and
the clipped cost, for z,y>=0 and K>=0, are

    H_direct(p,W;z,y)=W(z-8)_+/(p-9)+a_p kappa_p(z)y^2,
    H_K(p,W;z,y)=W(z-8)_+/(p-9)
             +a_p[c_p y^2-(c_p-kappa_p(z))min(y^2,K)].  (ASB2)

The notation H_direct does not mean the K=0 instance of H_K. Since
min(z,8)<=8 and p>9, every denominator is positive and kappa_p(z)<=c_p.
Thus the exact identity

    H_K-H_direct
       =a_p(c_p-kappa_p(z))(y^2-min(y^2,K))>=0           (ASB3)

holds for every K>=0, including choices of K depending on the row or
on tau. More generally, any pointwise majorant of H_direct has the same
lower-bound obstruction established below.

Let N be independent of the abstract source X, with the complete
auxiliary law for the capped17 step:

    Pr(N=1)=15/17,
    Pr(N=n)=32/17^n for every integer n>=2.             (ASB4)

The independence in ASB4 belongs only to this auxiliary scalar model.
It is not an independence assertion about original forbidden congruences.
Use z=y=X at17 and z=y=NX at19. The scalar functional under consideration is

    D(tau)=E(X^2-tau)_+ - W
       +E H_direct(17,W;X,X)
       +E H_direct(19,W;NX,NX).                        (ASB5)

The same source X is used in all three terms. Replacing either direct
cost in ASB5 by a pointwise majorant can only increase D(tau).

<a id="one-source-satisfying-the-complete-stated-observation-set"></a>
#### One source satisfying the complete stated observation set

Take

    Pr(X=1)=7/100,  Pr(X=11)=93/100.                   (ASB6)

This is a normalized positive probability. Its observations are

    E X=103/10,  E X^2=563/5,
    E(X-h)_+=(93/100)(11-h) for1<=h<=10,
    E(X-h)_+=0 for11<=h<=17,
    E(X^2-16)_+=1953/20,
    E(X^2-81)_+=186/5.                                 (ASB7)

Every value in ASB7 is at most the corresponding published scalar upper
bound: mean, square and H1--H17 from
[the continuation certificate](../../certificates/shared_square_continuation_certificate.json), and the two square hinges
from [the square certificate](../../certificates/shared_cell_square_certificate.json). The verifier checks all21
inequalities separately and retains their exact slacks. In particular,
the close comparison at H6 has strictly positive slack

    1144980123755523/246025127976511-93/20
        =19265573294937/4920502559530220 >0.

The source-square bound is the same improved Gamma13 used by the
continuation certificate. The SQ16 shift identity and the SQ81 source
identity are checked against the pinned source files. The certificate's
statement is exactly these21 upper observations; no additional conditional
profile, original-label relation, or probability-construction constraint
has been checked for ASB6.

<a id="complete-auxiliary-tails-and-exact-cost-coefficients"></a>
#### Complete auxiliary tails and exact cost coefficients

For a diagonal input t>=1, the direct cost splits into an affine function
of W:

    H_direct(p,W;t,t)=W b_p(t)+s_p(t),
    b_p(t)=(t-8)_+/(p-9),
    s_p(t)=a_p kappa_p(t)t^2.

The geometric law ASB4 has total probability1 and exact moments

    E N=9/8,  E N^2=89/64.

For either source atom x in{1,11}, every n>=8 satisfies nx>=8. Therefore
the complete19 tail, without any truncation or renormalization, is

    sum_(n>=8) Pr(N=n)b19(nx)
       =[x E(N;N>=8)-8 Pr(N>=8)]/10,
    sum_(n>=8) Pr(N=n)s19(nx)
       =(14/45)x^2 E(N^2;N>=8).                        (ASB8)

The exact tail moments in ASB8 are

    Pr(N>=8)=2/410338673,
    E(N;N>=8)=129/3282709384,
    E(N^2;N>=8)=8329/26261675072.

They follow by writing n=8+k in the three convergent geometric sums
sum r^k, sum k r^k and sum k^2 r^k, with r=1/17. The verifier also derives
them by subtracting the finite n<8 part from the full moments, and checks
a second complete decomposition at cutoff16. The two decompositions agree
separately for each source atom and for both coefficients of the cost.
For x=11, all n>=1 already lie in the upper branch, supplying the further
independent identities

    E b19(11N)=[11 E N-8]/10,
    E s19(11N)=(14/45)121 E N^2.

Writing B for the total coefficient of W and S for the direct square
contribution, the exact results are

    E b17(X)=279/800,
    E b19(NX)=667826190311/1641354692000,
    B=620124319573/820677346000
        =0.7556250000021324...,

    E s17(X)=168851/3840,
    E s19(NX)=20576332556971219/422484697720800,
    S=313229334820050587/3379877581766400
        =92.67475736690733... .                         (ASB9)

<a id="every-square-shift-and-every-pointwise-majorizing-clip"></a>
#### Every square shift and every pointwise-majorizing clip

Substituting ASB9 into ASB5 gives the exact expression

    D(tau)=E(X^2-tau)_+ + S-(484-tau)(1-B).             (ASB10)

The two source values have squares1 and121. Consequently D is continuous
and affine on each of[0,1],[1,121],[121,484], with slopes respectively

    -B,  7/100-B,  1-B.

The exact inequalities7/100<B<1 make these slopes negative, negative and
positive. Hence the global minimum over every real admissible shift is
at tau121, where the square hinge vanishes. Direct substitution gives

    D(121)=S-363(1-B)
           =67033659073176343/16899387908832000>0.

This proves ASB1 over the entire continuous shift interval, rather than
only an integer grid. ASB3 then proves the same strict obstruction for
every pointwise-majorizing clip, for each shift. Changing the clip cannot
make this already positive direct value negative.

Therefore an argument that enlarges the source to all abstract laws
satisfying just the21 stated observations cannot certify negativity of
this fixed17/T8,19/T8 common-N functional. A successful continuation must
exclude ASB6 by additional information, change the functional, or use a
different schedule or construction. This conclusion does not say that
ASB6 arises from compatible original prefixes, that the actual AP13 law
has these moments, or that an actual legal test attains any of these
costs. In particular ASB1 is not a refutation of the finite killed-frontier
requirements or a settlement of unrestricted Erdős7.

The [standard-library verifier](../../verify_scalar_all_shift_barrier.py) pins both observation certificates,
recomputes all21 comparisons and complete tails, and compares its entire
[output certificate](../../certificates/scalar_all_shift_barrier_certificate.json). Its rational piecewise calculation supports the
ordinary proof above; neither finite checks nor stored certificate fields
are represented as a Lean proof. Use `python3 -I -O` with
`--source-directory` if the pinned inputs are in a different directory.

<a id="actual-ap13-zero-block-equality-and-a-positive-killed-maximum-gap"></a>
### Actual AP13 zero-block equality and a positive killed maximum gap

For a concrete actual AP13 source, zero-current anchoring can give exactly the physical global maximum, even with a nonconstant old test, a varying natural cap and positive mixed charge. The same example has a strictly smaller killed maximum. Thus retaining the original zero block alone need not improve the physical charge-plus-square upper bound; retaining the actual killed overlap addresses a different loss and is quantitatively relevant here.

The full original test domains have288 labels. Their exact physical maxima and rigorous killed-maximum intervals are listed below. The later RS calculation proves that each killed lower endpoint is the exact maximum.

| p | physical global square maximum | killed global square maximum, lower and upper bounds |
|---|---:|---:|
|17|20.744427331665257...|[20.740224222517096...,20.7407634733786...]|
|19|20.2733090180926...|[20.269665723218274...,20.27021145401735...]|

Every bound concerns the entire original complete-test domain, including independently chosen zero and positive current blocks. The killed maximum is bracketed, not claimed to have been computed exactly. The source's exact old square is795613/46656=17.052747770919066... and its Haar density is1001/384. It satisfies the published SQ observations by strict margins. These are ordinary finite-family results, not a generic17/19 certificate or a covering-system resolution.

<a id="what-zero-current-anchoring-can-preserve"></a>
#### What zero-current anchoring can preserve

Fix any old probability mu, one actual normalized current kernel, all old complete labels and a finite current height H. Suppose its depth-e prefix cap is gamma(x)p^-e. Write

    Gamma(w)=sup_A E_mu[w A^2],
    s_H=sum_(e=1..H)p^-e,
    a_H=sum_(j=1..H)(2j+1)p^-j.

Expanding every original ordered pair and applying2uv<=u^2+v^2 gives

    Gamma_new <= Gamma(1+s_H gamma)
                         +(a_H-s_H)Gamma(gamma).       (ZB1)

Indeed, the coefficient of A0^2 is1+s_H gamma. The coefficient of a positive old block Ae^2 is gamma times

    p^-e+sum_(f=1..H)p^-max(e,f),

and those positive coefficients sum to a_H-s_H. No old layout or residue is identified in this inequality. Since Gamma(1+s_H gamma)<=Gamma(1)+s_H Gamma(gamma), ZB1 preserves a nonnegative support-function gain over Gamma(1)+a_H Gamma(gamma). That gain is zero if one old test simultaneously maximizes the two weighted squares. The all-height limits are s=1/(p-1) and a-s=2p/(p-1)^2; these are exact complete coefficient sums, not truncated auxiliary laws.

For a fixed actual mask its charge b is independent of the test. Adding Wb to ZB1 therefore preserves the same gain and the same equality cases for every W>=0. The shared-cell SQ observations bound univariate old costs; they do not themselves assert that the two weighted maxima have different optimizing layouts.

<a id="one-genuine-actual-ap13-source"></a>
#### One genuine actual AP13 source

Take Q=3^8*5*7*11*13=32837805. For every nonunit divisor d of Q include the single actual forbidden class0 modulo d. Their union is exactly the nonunits. The actual uniform357 source is uniform on its units. At11 and13 all mixed classes with residue0 are inactive on the previous unit source; the pure class0 removes its zero root. Consequently the prescribed AP11/T4 and AP13/T6 kernels, followed by the single final conditioning, give exactly the uniform unit law mu on Z/QZ. The final conditioning has mass1. This is an instance of the actual AP13 construction, not an independently chosen atomic law.

Let x denote the ternary coordinate and

    E_j={x=1 mod3^j}, 1<=j<=8,
    R=sum_(j=1..8)1_Ej.

Under the ternary unit law,

    Pr(R=0)=1/2,
    Pr(R=j)=3^-j for1<=j<=7,
    Pr(R=8)=1/(2*3^7).

The other four coordinates are independent uniform nonzero roots. For a complete old test centered at1, the ternary load is1+R. Its other-prime factor has square expectation

    S=product_(q=5,7,11,13)(1+3/(q-1))=273/64.

Every unweighted prefix-pair cap is attained by this centered test, so the exact old complete-square maximum is

    S E(1+R)^2=795613/46656.

The actual source density is Q/phi(Q)=1001/384. For the fixed centered test, its square-hinge at81 is64423/14580, computed by the finite ternary and four-Bernoulli product law. No convex-cost maximum is needed: the exact square bound G implies E A<=sqrt(G), E(A-h)_+<=G/(4h) for h>0, and E(A^2-tau)_+<=G for tau>=0. These prove all21 published source upper observations, each with positive slack recorded in the certificate.

<a id="the-actual-current-masks-and-exact-charges"></a>
#### The actual current masks and exact charges

For p=17 or19 add the actual pure class0 modulo p and the eight distinct original mixed labels3^j p, j=1,...,8. Their CRT residues satisfy

    old coordinate=1 modulo3^j,
    current coordinate=j modulo p.

There are152 distinct actual forbidden moduli in total. In row R=j the actual mixed union is exactly the j roots1,...,j among the p-1 pure survivors. Thus

    alpha_j=j/(p-1), delta=7/(p-2),
    g_j=1/(1-min(alpha_j,delta)),
    beta_j=(alpha_j-delta)_+/(1-delta).

Only beta_8 is positive, and beta_8=1/(p-1). The exact global charges are

    b17=1/69984, b19=1/78732.                           (ZB2)

Put t_j=g_j/(p-1) and q_j=1-beta_j. The good-root physical and killed masses both equal t_j; the physical bad roots each have mass beta_j/j. These row masses sum to1. The entire current root p-1 is clean on every old row.

The literal actual pure mass is(p-1)/p. Its full-Haar cap is p g_j/(p-1), whereas SH26's generic pure envelope is(p-1)g_j/(p-2). The strictly positive difference

    g_j/[(p-2)(p-1)]

is retained separately. No claim that generic pure-density savings vanish is made.

<a id="global-physical-maximality-not-only-a-favorable-test"></a>
#### Global physical maximality, not only a favorable test

For any fixed independent old blocks A0,A1, putting every current-positive original label on the common clean root simultaneously attains all its current pair caps. Their exact largest physical and killed squares for those old layouts are

    E[A0^2+t(2A0 A1+A1^2)],
    E[q A0^2+t(2A0 A1+A1^2)],                         (ZB3)

respectively. These are upper bounds for arbitrary current-root assignments by the actual kernel cap, including cases in which roots vary with the original old divisor. Thus the current optimization is eliminated over the full domain, as in the existing clean-root result CS1.

The function g_R is a nondecreasing step function of the nested E_j. Hence

    mu g =g_0 mu+sum_(j=1..8)(g_j-g_(j-1)) mu|E_j

is a positive combination of uniform laws restricted to those actual nested cylinders. For each such component, every old modulus-cylinder mass is maximized by the residue1. Expanding pairs proves that the same complete centered test simultaneously maximizes E A^2 and E t A^2. In particular ZB1 at H1 is an equality:

    Gamma_phys=Gamma(1)+3Gamma(t).                    (ZB4)

The maximizing zero and positive old blocks are equal to that centered test, but no such equality was assumed in the optimization domain. The zero-block gain Gamma(1)+Gamma(t)-Gamma(1+t) is exactly0, despite g varying and b>0. Adding any fixed Wb preserves equality for the whole physical cost.

<a id="exact-removal-of-the-independent-other-prime-axes"></a>
#### Exact removal of the independent other-prime axes

The current kernel depends only on x and the current prime coordinate. For either its physical or killed measure, the full complete-square maximum equals S times the maximum on the3^8 p subproblem.

For the upper bound, first replace every other-prime test-root choice by the common root1. Conditional on the ternary/current coordinates, each original pair has nonnegative mass, and this replacement attains its other-prime cylinder-intersection cap simultaneously. It therefore increases or preserves the square. Group the resulting labels by their original other-prime divisor d. Each group is a complete3^8 p test L_d, with its own ternary/current residues. Cauchy-Schwarz under the positive physical or killed submeasure gives E L_d L_e<=Gamma_(3,p). Summing the remaining other-prime pair masses gives S. Conversely, taking the same maximizing3^8 p test in every group attains this upper bound. Finite maxima exist.

This argument retains every original label, and it applies specifically because the four other coordinates are independent of this actual kernel. It is not a reduction for an arbitrary AP13 source.

<a id="a-full-domain-killed-upper-bound-and-a-better-killed-witness"></a>
#### A full-domain killed upper bound and a better killed witness

Work on the ternary subproblem. Let

    G3=E(1+R)^2,
    Jt=E[t_R(1+R)^2],
    w_j=q_j+t_j.

From ZB3 and2A0 A1<=A0^2+A1^2,

    Gamma_killed^(3,p)<=Gamma_3(w)+2Jt.              (ZB5)

The weight w_j increases for j=0,...,7; its value at8 may fall. For a ternary depth a>=1, every nonspine prefix has constant R<=a-1. The greatest such mass is its ordinary prefix mass times w_(a-1). The spine prefix has weighted mass sum_(j>=a)Pr(R=j)w_j. Thus its exact maximal weighted cylinder mass is

    C_a=max{w_(a-1)/(2*3^(a-1)),
                          sum_(j=a..8)Pr(R=j)w_j},
    C_0=E w.

Every ordered pair of old3^a labels has intersection either empty or a prefix of its maximal depth. There are2a+1 ordered exponent pairs of maximal depth a. Therefore

    Gamma_3(w)<=sum_(a=0..8)(2a+1)C_a.              (ZB6)

This is a rigorous upper bound over every complete old layout, including nonnested ones. It does not assume that the maximizing cylinders for different depths are compatible; in this example the separate caps at depths7 and8 are off-spine and need not be jointly attained. Combining ZB5-ZB6 and multiplying by S gives the displayed killed upper bounds.

For a lower bound choose a single old center z=1+Q/3. Its other-prime coordinates are1, its ternary prefixes through depth7 remain on the spine, and its depth8 prefix is a different child of E7. Use this old layout in both current blocks and the same clean current root. On the two off-spine children of E7 its ternary loads are9 and8, while on E8 its load is8. Formula ZB3 evaluates this complete literal test exactly and gives the displayed lower bound.

This new test has a strictly larger killed square than the physically maximizing centered test: the improvements are26299/35831808 at17 and137683/184757760 at19. Thus the physical maximizer is demonstrably not a killed maximizer. The killed maximum remains within intervals of widths0.000539250862 and0.000545730800, respectively; no exact-max claim is made.

The global maximum loss is nevertheless bounded below sharply enough to be nontrivial:

    Gamma_phys-Gamma_killed >=49231/13436928
                 =(49231/192)b17 at17,
    Gamma_phys-Gamma_killed >=572299/184757760
                 =(1716897/7040)b19 at19.             (ZB7)

The factors exceed256 and243. This is a forced loss over the full test domain, not the killed loss of only one selected test.

<a id="an-explicit-normalized17-history-for-the19-fixture"></a>
#### An explicit normalized17 history for the19 fixture

The direct19 fixture above has original17 height0; its intervening17 step is the identity. No original17 labels were removed. To make17 explicitly present, retain the identical actual AP13 source and include every nonunit old divisor of Q*17 with residue0 before the19 step. The additional actual17 pure class is0; all actual mixed17 classes are inactive on the unit input. Thus the prescribed normalized AP17/T8 law is mu17=nu13 times uniform nonzero17 roots, with mixed charge0 and no intermediate conditioning.

Apply the same eight19 mixed classes to this actual mu17. All19 square values, its Xi frontier, and the upper/lower maximum-loss bounds above multiply exactly by19/16, the complete17 test-square factor. The charge b19 remains1/78732. The original domain now contains576 complete test labels and296 distinct forbidden moduli; its full period is Q*17*19. The certificate records the entire extension. This is a legitimate KC19 normalized physical input with a nontrivial pure17 step; it is not a claim for a preceding17 step having positive mixed charge. The positive17-charge fixture and this19 fixture are separate actual families and their displayed F values must not be summed as one chain.

<a id="what-this-says-about-the-kc-frontier"></a>
#### What this says about the KC frontier

For this fixed actual family the positive-current killed frontier is exactly

    Xi_p^-=3S Jt,
    F_p^-(403)=403b_p+3S Jt.                          (ZB8)

The clean current root makes every positive pair survive; the common centered old test simultaneously attains the weighted caps. These exact F values are3.6974380198225503... and3.2256798774636306.... The example therefore does not threaten the numerical KC target. It shows that a physical zero-block gain and a killed saving have distinct behavior: the former can vanish at a genuine global maximum while the latter is forced and the optimal full killed test changes.

The shared-cell source observations alone do not provide the missing general weighted correlations. A generic improvement must control actual mask/test structure, or retain a quantitative relation between the killed baseline and the positive-current frontier; the finite explicit relation here uses special nested geometry and independent other-prime axes.

The [verifier](../../verify_actual_zero_block.py) reconstructs every old divisor and every literal current CRT class, checks all152 forbidden labels and288 test labels, all row normalizations, source moments, physical global-max formulas, the full-domain killed upper bound and the complete moved-test lower bound. All rational constants and test-inventory digests are compared against its [certificate](../../certificates/actual_zero_block_certificate.json). The global claims are supported by the ordinary arguments above; no Lean declaration or unrestricted endpoint is asserted.

<a id="the-common-original-test-and-the-losses-in-the-kc-comparison"></a>
### The common original test and the losses in the KC comparison

The exact killed kernel already retains the zero-block square, as in
GC2 and ZB3. The following algebra identifies which quantities must
remain coupled when tightening KC13. It is an optimization interface,
not a new Lean declaration or a proved uniform improvement.

Use nu=nu13, normalized physical K=K17, killed K-=K17^-, and the
nonnegative removed kernel D=K-K-. Set

    beta17=D1, mu=nu K, xi=nu K-,
    beta19=1-K19^-1, eta=xi K19^-.

For a single complete original test L, let B be its literal zero19
block and A the literal zero17 block of B. Their inherited residues
are fixed throughout. Define

    R17=B^2-A^2, R19=L^2-B^2,
    G17=K- R17, G19=K19^- R19.

Both R terms and both G terms are nonnegative. Kernel expansion gives
the exact identity

    Q_eta(L)=nu(A^2-484)
       +nu[G17+beta17(484-A^2)]
       +xi[G19+beta19(484-B^2)].                     (CT1)

The final bracket f19 is signed. Its physical-input replacement is
xi f19=mu f19-nu D f19. The domination xi<=mu alone does not permit
dropping the last term. In particular a negative f19 on removed17
mass reverses the desired comparison.

For0<=tau<=484 set W=484-tau, h=(A^2-tau)_+,
j=(tau-A^2)_+, b17=nu beta17, b19=mu beta19, and
d=beta17+K- beta19. Another exact expansion is

    Q_eta(L)=nu h-W+W(b17+b19)+nu G17+mu G19
                -Delta_tau(L),                     (CT2)

    Delta_tau(L)=nu[d h]+eta j
       +xi[beta19 R17]+nu D G19+W nu D beta19 >=0.   (CT3)

Indeed eta(A^2-tau)=nu h-nu[d h]-eta j,
eta R17=nu G17-xi[beta19 R17], eta R19=mu G19-nu D G19,
and eta1=1-b17-b19+nu D beta19. Substituting proves CT2--CT3
without a positivity assumption on the final mass or any cutoff of
original labels. At tau0, the first term and the R17 correction
together equal nu[beta17 A^2]+xi[beta19 B^2].

For a fixed family one can take the supremum of
nu h+nu G17+mu G19-Delta_tau(L) over the same original L.
Separately maximizing its positive terms and subtracting the deficit
of one selected test is invalid. Even CT3 is not the entire gap in
KC13: replacing nu h by T13 and the two actual G integrals by their
separate Xi suprema can introduce further gaps.

KB3--KB7 apply to maxima of the separate positive-current Xi objective.
They cannot be imposed without proof on maxima of this new joint
objective. For the full Q objective, every label instead uses the
full-square replacement score integral_eta J(2(L-I_ell)+1), including
zero-current labels. Its whole-residue best-response condition is

    m_ell[2 sum_(j!=ell)P_(ell,j)+P_(ell,ell)]
         >=2 sum_(j!=ell)P_(j,j)+eta1,               (CT4)

where all entries now use the final eta. This is the same elementary
replacement argument with the correct objective, not a new abstract
theorem.

A useful task-specific observation is the actual surviving low-load
band E={A^2<=c}, c<tau. CT3 gives

    Delta_tau(L)>=(tau-c)eta(E),
    eta(E)>=nu(E)-nu[1_E beta17]-mu[1_E beta19].      (CT5)

Only nonnegative restricted bad masses use xi<=mu here. Thus a bound
on the bad mass inside the same inherited test's low-load band has
a quantitative use. The existing21 scalar upper observations do not
supply those conditional masses, and CT5 has not yet yielded a
uniform KC bound.

There is no height-independent positive lower bound for eta(A=1).
For any H>=1 take distinct actual moduli3^n,1<=n<=H, with residues
a_n=3^(n-1)-1. At those same test moduli choose
b_n=2*3^(n-1)-1 and retain the unit test. The two classes at depth n
are the two side children of the common ternary branch whose earlier
digits are all2. Each family consists of mutually disjoint classes,
and their combined union leaves exactly -1 modulo3^H.

The actual survivor fraction is (1+3^-H)/2. The test load on its
uniform survivor law takes only values1 and2, with

    Pr(A=1)=2/(3^H+1) tending to0.                   (CT6)

Absent11/13/17/19 exclusions preserve this observation under the AP
construction. All original test labels are present. Hence even this
genuine family rules out a uniform positive unit-load mass, while a
larger band such as A^2<=4 has full mass. A successful CT5 argument
must control an appropriate band and its actual deletions, or split
the families into cases with proved additional hypotheses.
