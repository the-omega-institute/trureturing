[Index](../marked_head_profile.md) · [Complete face profile](98-a-complete-stop-loss-profile-strengthens-the-whole-face-comparison.md) · [One head](109-the-mean-and-all-hinges-share-one-original-test.md) · [Actual finite transport](116-signed-face-duals-transport-one-shared-finite-source.md) · [Projected pure3 defect](119-the-complete-pure-three-family-has-one-projected-defect.md) · [Projected deep5 defects](122-two-complete-deep-five-families-transport-the-mean-credit.md) · [Complete mean credit](124-one-original-head-transports-the-whole-deep-mean-credit.md)

# The complete off-face omitted tails recover every face constant

All five old-coordinate remainders R_k and the complementary
positive-seven remainder Zplus of98/109 have explicit computable
off-face upper bounds. They retain every original exponent label,
independent test residues and the same capacity/union defect vector
used by124. On both complete saturated K faces they recover the
original constants exactly. Thus these first-moment tail inputs to
116/124 need no unspecified remainder estimate.

This is an ordinary measure argument with an exact rational helper.
It supplies a complete-tail interface, not a new global K or an
unrestricted Erdős #7 solution. The nonlinear defect optimization
remains a separate obligation; no Lean verification is claimed.

## 1. One actual source and one defect vector

Use the actual source measure Lambda and the deleted survivor
mu=Lambda-delta of57. Let eta be the raw pure3 survivor measure,
q the raw pure5 survivor measure, z=q(1), and

    ROOT=(0,0,1,1,1), D=max_l d_l,
    h=sum_l eta_l, h0=eta0+eta1, h1=eta2+eta3+eta4.

The source inequalities include Lambda<=eta tensor q and the sharper
ternary projection Lambda^3<=d_l*eta on cell l. In particular
mu^3<=D*eta, mu^5<=h*q, and h1>h0. Keep the actual normalized
shallow3/9 mixture pi on the18 carriers, including the absent-carrier
symbol -1. Define

    t_l=sum_(u,v)pi_(u,v)*(I_(ROOT(l)=u)+I_(l=v)),
    a_l=1-t_l/5, 3/5<=a_l<=1,
    kappa=h1/(h1-h0).                             (OT1)

The complete virtual shallow3/9 deletion is exactly(1-a)*Lambda.
Write W=V-delta>=0, omega=W(1), and retain the complete disjoint
family defects

    E5=h/25-V5sh(1), E15=h1/25-V15sh(1),
    E3=D/90-V3deep(1),
    E5d=h/100-V5deep(1), E15d=h1/100-V15deep(1).

Every one is nonnegative, and

    E5+E15+E3+E5d+E15d+omega<=rho.                (OT2)

These are full shallow defects: if116 uses x5,x15 and the source
slacks r,r1, then E5=x5+r/5 and E15=x15+r1/5. If124 splits E3,
use E3=E27+Ege4, not an additional copy. The helper's domain checks
are necessary actual-source bounds; they are not a realizability
certificate for arbitrary rational inputs.

## 2. Complete pure3 test tails from the full five families

Apply122's projection proof to all b>=1, combining its shallow
and deep five families. Their complete nominal coefficient is

    sum_(b>=1,e>=1)5^-b*6/(5*7^e)=1/20.

The positive projection deficits therefore satisfy

    Xi5=eta/20-(V5sh+V5deep)^3>=0,
    Xi5(1)=E5+E5d,
    Xi15=eta|root1/20-(V15correct)^3>=0,
    Xi15(1)<=kappa*(E15+E15d).                    (OT3)

The last bound prices every wrong-root original label by its
capacity deficit, exactly as in122; absent labels keep their full
nominal capacities. All these families are distinct from shallow3/9.
Dropping other nonnegative virtual families gives, on cell l,

    mu^3<=[a_l*d_l-(1+ROOT(l))/20]*eta
                                      +Xi5+Xi15+W^3.

Set

    c3=max_l[a_l*d_l-(1+ROOT(l))/20],
    eps3=E5+E5d+kappa*(E15+E15d)+omega.

Since d_l>=1/4, c3>=1/20, and c3<=D. Thus c3*eta is a positive
reference. The positive excess nu3=(mu^3-c3*eta)_+ obeys

    nu3(1)<=eps3, nu3<=(D-c3)*eta.

For every independently labelled pure3 test cylinder J_a, a>=3,

    mu(J_a)<=c3*3^-a+min(eps3,(D-c3)*3^-a).       (OT4)

The raw-minus-reference coefficient D-c3 follows directly from
mu^3<=D*eta. It strengthens using the entire raw mass as an error
envelope and remains valid for arbitrary changing test residues.

## 3. Pure-five, root-five and cell-five test tails

From119's full pure3 projection and the same actual shallow density,

    c5=sum_l eta_l*a_l-1/90,
    eps5=E3+(z-D)/90+omega,
    mu^5<=c5*q+Xi+W^5,
    Xi(1)=E3+(z-D)/90.

Here c5>=13/45>0 and mu^5<=h*q. Taking the positive excess over
c5*q gives, for every five cylinder F_b, b>=2,

    mu(F_b)<=c5*5^-b+min(eps5,(h-c5)*5^-b).       (OT5)

For tests with ternary exponent1, only the shallow3/9 deletion
is needed on root1. Put

    c1=sum_(l>=2)eta_l*a_l,
    B1(b)=c1*5^-b+min(omega,(h1-c1)*5^-b),
    B0(b)=h0*5^-b.

The root1 projection is bounded by c1*q+(W restricted to root1)^5, and its raw
bound is h1*q. Root0 retains its raw bound. Therefore every
independent3*5^b test obeys

    mu(test)<=max(B0(b),B1(b)).                   (OT6)

When h0<=c1 the B0 branch can be dropped, without any E3 or root-spill
error. This always holds on qK>=1-sigma,0<=sigma<=2/27: the one
total source-deficit budget gives

    h1>=1/3-sigma/18, h0<=1/6+sigma/18,
    c1-h0>=(3/5)*h1-h0
              >=1/30-4*sigma/45>=13/486>0.       (OT7)

On cell l put c_l=eta_l*a_l. The same positive-excess argument
uses raw coefficient eta_l and yields

    B_l(b)=c_l*5^-b+min(omega,(eta_l-c_l)*5^-b),
    mu(test9*5^b)<=max_l B_l(b).                  (OT8)

Each cell uses its own raw-minus-reference envelope before taking
the maximum. Neither(OT6) nor(OT8) requires forced27;124 still uses
that separate fact for its bounded mean correction. The remaining
deep mixed category a>=3,b>=1 uses its full raw product sum

    sum_(a>=3,b>=1)3^-a*5^-b=1/72.               (OT9)

## 4. Exact summation and deletion of selected original labels

All four families(OT4)--(OT8) have finitely many branches of form

    c*p^-n+min(e,H*p^-n), c,e,H>=0.

For a branch with e>0, let its crossing be the first n at or beyond
the family's start with H*p^-n<=e. Let N be the maximum crossing
over the branches; branches with e=0 have identically zero error.
Below N the finite maximum is summed exactly. At and above N all
branches are geometric, so the maximum has coefficient

    max_branches[c+H*I_(e>0)].

The helper also permits the minimum with the family's raw cap,
which merely clips this coefficient after N. For any finite set
of removed original depths O, the complete remaining tail is the
coefficient times

    p^-N/(1-p^-1)-sum_(n in O,n>=N)p^-n.          (OT10)

This is an infinite-tail identity, not a truncation estimate. All
original-label omissions below N are removed before the finite
sum. No relation between residues at different n is imposed.

Use the selected-label order25,27,75,81. For prefix length k=0..4,
sum the four complete families with the following omissions:

| Family | Start | Removed original depths |
| --- | ---: | --- |
| pure3 | a=3 | a=3 if k>=2; a=4 if k>=4 |
| pure5 | b=2 | b=2 if k>=1 |
| root-five | b=2 | b=2 if k>=3 |
| cell-five | b=2 | none |

Add1/72 from(OT9), obtaining R_k. These are the complete old
remainders after the same six base-head and k selected original
labels used in98/109. If m_i is the assigned cap for the ith selected
label, then exactly

    R_k=R_0-sum_(i<=k)m_i.                       (OT11)

This subtracts assigned terms from the same assigned-cap series;
it does not subtract an upper bound from an unrelated unknown sum.

## 5. The complementary positive-seven remainder

The raw old nonunit cap sum is

    N3=max(n0+n1,n2+n3+n4),
    C=N3+max_l n_l+D/18
                           +(h+h1+max_l eta_l)/4+1/72.

For every original positive-seven depth e, its relative pure7
survivor cap is u_e=6/(5*7^e). Dropping mixed7 deletion gives the
complete nonunit sum C/5. The head retains all unit7^e labels as
well as21 and35 at e=1. Their assigned coefficients are respectively
u1*N3 and u1*h/5. Therefore the complete complementary bound is

    Zplus=C/5-(6/35)*(N3+h/5).                    (OT12)

Both subtractions remove exactly named terms of the assigned cap
series. All other original moduli and all seven depths remain.

## 6. Exact face recovery and the shared-budget boundary

On either entire saturated K face, all defects and z-D vanish.
In the orientation with deficit cell0, the coefficients are

    c3=7/10, c5=2/5, c1=4/15, max_l c_l=4/45,
    D-c3=1/20, h-c5=1/10, h1-c1=1/15,
    eta0-c_0=0, eta_l-c_l=1/45 for l!=0.

The cell0/cell1 exchange gives the other face. These formulas hold
throughout the whole root1 beta simplex, not just at its vertices.
Consequently

    (m1,m2,m3,m4)=(2/125,7/270,4/375,7/810),
    R0=163/1800, Rk=R0-sum_(i<=k)m_i,
    C=37/72, Zplus=779/12600.                    (OT13)

Every endpoint difference from98/109 is zero. For a nonnegative
hinge combination a_t, the omitted contribution supplied to116/124
is explicitly

    sum_t a_t*(R_(k_t)+Zplus),
    k1=0, k_t=min(t-1,4) for t>=2.               (OT14)

Each R_k uses the same actual defect vector(OT2). The same omega
can occur in a bounded-head integral and these separate tail
integrals: their coefficients add as bounds on different integrands.
This does not grant independent rho allowances to the families.

The min terms and their crossings do not establish convexity in
the defect vector. Inserting(OT14) into124's finite convex problem
therefore requires a fresh valid optimization argument. In
particular123's explicit non-vertex counterexample still prevents
a blanket vertex-only claim. Ordinary finite checks of this
interface cannot supply that missing global inequality.

## Exact checks

[complete_off_face_omitted_tails.py](../frontier/complete_off_face_omitted_tails.py)
exports `complete_tails(dat,pi,defects,z)`. It returns integer-keyed
R_k values, selected caps, Zplus, exact complete-series crossings,
family parameters and the original shared defect vector. Its
[certificate](../certificates/source_norms/complete_off_face_omitted_tails.json)
checks both face orientations at each beta vertex and their barycenter.

Three genuine finite original-label configurations retain independent
seven residues and compute actual union deletion. They include aligned
carriers, pure3 root spill and wrong-root five carriers. The helper
checks the single residual budget, cylinder caps, independently labelled
finite omitted loads for every prefix, and the positive-seven complement.
All absent deeper capacities remain in the full defects; the ordinary
measure arguments and(OT10) supply the unbounded exponent range.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/complete_off_face_omitted_tails.py --check
```
