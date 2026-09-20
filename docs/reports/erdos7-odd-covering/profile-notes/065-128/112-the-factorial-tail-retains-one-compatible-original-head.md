[Index](../../marked_head_profile.md) · [Complete factorial tail](108-a-complete-second-factorial-tail-improves-four-quadratic-costs.md) · [Common mean and hinge head](109-the-mean-and-all-hinges-share-one-original-test.md)

# The factorial tail retains one compatible original head

On both complete actual saturated K faces, the complete second-factorial
load tail has a layout-dependent upper bound

    T5(A)<=J(ell)+2539/3600,
    J(ell)=Hcap(ell)+O(w*h4(B_ell))+C7cap(ell).       (FH1)

Here ell is the layout of A's original six zero-seven head labels. The
three head terms retain this same layout before maximization. In
particular, a nonnegative multiple of J can be added to109's same-layout
mean/hinge objective before taking its maximum.

The independent scalar maximum does not improve108:

    max_ell J(ell)=139/900,
    max_ell J(ell)+2539/3600=619/720.                (FH2)

It has exactly two maximizing layouts in the canonical source table,
(1,3,2,1,2,3,2) and(1,4,2,1,2,4,2). Both lie in root1. A fully compatible
root0 layout(0,0,1,0,1,0,1) instead has J=53/450. These are maxima of
specified upper-bound operators; they do not claim that actual covering
families attain them. Any improvement from combining this operator with
other costs must be checked on that combined objective.

The scope remains r=rho=0, D=53/360, on the entire actual faces
(398,410,422),(1,1) and(616,628,640),(1,0). All original labels and
infinite tails are retained. This is an ordinary exact-arithmetic
result, with no off-face extension, new global K, Lean verification or
unrestricted Erdos #7 resolution.

## 1. Retain the compatibility that identifies the factorial head

Use108's source tables p,R,w,d and ROOT=(0,0,1,1,1), with
R(c,s)=eta_c*p(c,s), eta=(1/18,1/9,1/9,1/9,1/9). Let

    ell=(r3,c9,s5,r15,s15,c45,s45),
    B=1+I3+I9+I5+I15+I45,
    Phi(v)=(v-5)_+*(v-4)/2,
    h4(v)=(v-4)_+.

The intersection G=I3*I9*I5*I15 is nonempty only when

    r3=ROOT(c9)=r15 and s5=s15.                    (FH3)

When compatible, it is exactly the45 rectangle(c9,s5). Since1<=B<=6,
Phi(B) is the indicator that all five nonconstant head indicators
occur. Thus H=integral Phi(B)dmu is zero unless(FH3) also has

    c45=c9 and s45=s5.                             (FH4)

For a surviving compatible rectangle,75 gives mu<=w*Lambda. The
complete forbidden27 family is a distinct family not used in w. It is
forced into cell1 and deletes q(F)/135 on cell1 times any five-event F,
where q(F)=Haar5(F minus the complete pure5 source union). For the five
slots,

    q_s=(0,1/5,1/5,3/20,1/5).

Consequently the fixed-rectangle surviving cap is

    H_(c,s)=w(c,s)*R(c,s)-I_(c=1)*q_s/135.          (FH5)

Define Hcap(ell) as H_(c9,s5) when(FH3),(FH4) both hold, and zero
otherwise. Every entry of(FH5) is nonnegative and at most4/225, so
this keeps108's head bound. It does not replace that bound by a
weaker source cap. The forced27 deletion follows from75's complete
saturation measure and is not a claim that projected deletion sets
are disjoint.

## 2. The cross term retains fixed rectangles and complete rows

The pointwise indicator inequality from108 is

    h4(B)<=I45+G.                                  (FH6)

If(FH3) fails, its second term is zero. Otherwise both right-hand
terms are fixed original45 rectangles, with their own head labels.

For any fixed rectangle(c,s), a complete raw LCM row against all
old labels has the upper bound

    S_(c,s)=6*R(c,s)+p(c,s)/9+3*d(c,s)/20
                                +I_(d(c,s)>0)/360. (FH7)

The four terms correspond to the disjoint exponent regions:

| Old exponents | Complete raw contribution |
| --- | ---: |
| a<=2,b<=1 | 6*R(c,s) |
| a>=3,b<=1 | 2*(sum_(a>=3)3^-a)*p(c,s)=p(c,s)/9 |
| a<=2,b>=2 | 3*(sum_(b>=2)5^-b)*d(c,s)=3*d(c,s)/20 |
| a>=3,b>=2 | I_(d(c,s)>0)*(sum_(a>=3)3^-a)*(sum_(b>=2)5^-b)=I_(d(c,s)>0)/360 |

In the first region, each compatible old label contains the fixed
rectangle; incompatible intersections are empty. In the next two
regions, the source cylinder bounds are respectively3^-a*p(c,s)
and5^-b*d(c,s). The last region uses the full Haar product cap.
When d(c,s)=0, this entire fixed source rectangle is empty; this is
why its entire row, including the last region, is zero.

These are raw old-coordinate source caps for positive-seven
intersections. They do not apply a surviving factor w to positive-seven
tests. Their complete seven weights sum to1/5. Hence

    C7cap(ell)=[S_(c45,s45)
                   +I_((FH3))*S_(c9,s5)]/5         (FH8)

bounds the complete positive-seven cross term. It is uniform in all
independent positive-seven residues and imposes no identification with
109's selected positive-seven root or slot. Every S entry is at most
7/40, preserving108's C7 bound7/100. For example S_(0,1)=1/10 whereas
S_(1,1)=7/40.

## 3. Keep the full old tail and the full tail-pair complement

The old-tail operator is exactly108(FT5), namely

    O(z)=(1/18)*max_c sum_s p(c,s)*z(c,s)
        +(1/20)*max_s sum_c d(c,s)*z(c,s)
        +(1/20)*max_(r,s)sum_(ROOT(c)=r)d(c,s)*z(c,s)
        +(1/20)*max_(c,s)d(c,s)*z(c,s)
        +(1/72)*max_(c,s)z(c,s),
    z=w*h4(B_ell).                                (FH9)

It bounds all original old-tail labels using their complete geometric
series. The maximum of(FH9) remains1/15. No beta mass is fixed to a
face vertex, and no common original residue is substituted for the
independent labels.

108's nonnegative tail-pair cap partition remains

    P_TT<=2539/3600.                              (FH10)

It includes all old-old, old-seven and seven-seven pairs and removes
only the known diagonal cap subseries. There is no subtraction of
unknown actual moments.

The pointwise factorial-tail inequality

    Phi(B+R)<=Phi(B)+h4(B)*R+R*(R-1)/2

now gives(FH1) with this same ell. Its passage from finite label sets
to every complete test uses monotone convergence and the finite complete
bounds(FH7),(FH9),(FH10), as in108.

The checker enumerates all12500 independent head layouts. The two
maximizers in(FH2) have

    (Hcap,O,C7cap)=(4/225,1/15,7/100).

For the compatible root0 example above, the respective values are
1/90,1/15,1/25, whose sum is53/450. First-beta permutations2,3,4
transport every source and descendant table and preserve ROOT. The
compatible root0 cell exchange transports the whole canonical
construction to the second K face. The same inequalities therefore
hold on both complete faces.

## 4. Positive combinations may share the head before maximization

Let h_t(v)=(v-t)_+ and suppose an exact complete cost expansion has

    f(v)=a+sum_t c_t*h_t(v)+theta*Phi(v),
    a>=0, c_t>=0, theta>=0.                        (FH11)

For the same complete test A and original head ell, let M(ell,xi)
be109's complete bound for sum_t c_t*integral h_t(A)dmu, where xi
records its selected positive-seven root and slot. This bound includes
all its own remaining old and seven tails. Then

    integral f(A)dmu
       <=a*D+max_(ell,xi)[M(ell,xi)+theta*J(ell)]
                                             +theta*2539/3600. (FH12)

Every term is an upper bound for its indicated nonnegative summand of
the same cost. The fixed-rectangle C7 estimate is uniform in xi and
can therefore be used in this common maximum. A deletion contribution
may legitimately appear in both the mean and factorial estimates,
because those estimates integrate different positive cost functions.
It must not be subtracted again as an additional independent credit.

(FH12) is also valid for any other already proved same-layout upper
bound M; no claim of an attained common source maximizer is needed.
The precise cost expansion, nonnegative coefficients and resulting
maxima remain the consumer's obligations.

`frontier/moments-survival/whole_factorial_same_head.py` exports `FactorialHead(bridge)`.
Its `factorial_head_bound(layout,B=None)` returns J as an exact fraction;
`head_bound_numerator(layout,B=None)` returns5400*J. The separate
constant `PAIR_TAIL_UPPER` is2539/3600. The certificate records the
complete fixed-cell caps, all-layout digest, exact two maximizers and
the unchanged independent scalar bound.
