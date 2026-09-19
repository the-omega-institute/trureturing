[Index](../marked_head_profile.md) · [Endpoint pure3 deletion](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md) · [Common actual measure](57-common-deleted-measure-coupling.md) · [Shared defect budget](117-the-actual-slot-defects-share-a-stronger-packing-polytope.md)

# The complete pure-three family has one projected defect

The complete forbidden pure3 family has a quantitative five-coordinate
projection away from the saturated K faces. Its difference from the
endpoint reference is a positive measure, with an exact mass identity.
Consequently75's complete pure-five descendant bound has an explicit
off-face error that includes every original exponent depth.

Write q for raw five-coordinate Haar restricted to the actual pure5
survivor, z=q(1), dmax=max_c d_c, and V3deep for the virtual forbidden
cofactors3^a*7^e with a>=3,e>=1. With projection onto the five coordinate,

    Xi=q/90-(V3deep)^5>=0,
    Xi(1)=E3+(z-dmax)/90,
    E3=dmax/90-V3deep(1)>=0.                       (PD1)

Here E3 is one existing nonnegative summand of the actual unused
cofactor capacity T-V(1). The identities use one actual source and
independent original residues, including absent labels. They make
no assertion that forbidden27 lies in a particular cell off the face.

## 1. A product cap gives a measure inequality for every original label

Before alpha, beta and late source deletions, the old source is
dominated by ternary Haar tensor q. Thus for any genuine original
ternary cylinder J of depth a and every five-measurable set F,

    Lambda(J times F)<=3^-a*q(F).                  (PD2)

This does not require J to retain its full Haar mass, lie on root0,
avoid the late source, or agree with another original residue.
For an absent label its actual restricted measure is zero and the
same inequality remains valid.

Let lambda_(a,e)^5 be the five projection of Lambda restricted to
the actual old cofactor at label(a,0,e), or zero if it is absent.
The complete seven cap weights are u_e=6/(5*7^e). Therefore

    sum_(a>=3,e>=1)u_e*lambda_(a,e)^5
       <=sum_(a>=3,e>=1)u_e*3^-a*q=q/90,           (PD3)

using sum_(a>=3)3^-a=1/18 and sum_(e>=1)u_e=1/5.
All measures are positive, so monotone convergence justifies the
complete sum. Its left side is exactly(V3deep)^5, proving Xi>=0.

The established actual pure3 cylinder cap is

    Lambda(J)<=dmax*3^-a.

Thus E3 is nonnegative. Formula106(M4) includes dmax/18 inside the
cofactor sum before division by5, so dmax/90 is precisely this
family's complete contribution to T. Taking total masses in(PD3)
gives(PD1); since d_c=z-alpha_ROOT(c)-beta_c, dmax<=z.

At either complete saturated K face, z=dmax=3/4 and E3=0. Hence
Xi=0 as a measure and(PD1) recovers75's exact q(F)/90 deletion
on every five-measurable F. The proof now also quantifies failure
of that identity at positive actual capacity deficit.

## 2. The family shares the same residual with all other defects

Use57 and85's actual quantities

    delta=projected mixed7 deletion, mu=Lambda-delta,
    omega=(V-delta)(1), rho=(T-V(1))+omega.

The complete cofactor5,15 and deep pure3 families have disjoint
original modulus labels. Consequently

    E5+E15+E3+omega<=rho.                          (PD4)

If117's valid gap prices are retained, this implies

    E3+omega
       <=rho-(r+r1)/5-G5*q5-G15*q15.              (PD5)

These are allocations from one residual. In particular one cannot
first give rho to each of5,15 and deep3, then add the resulting gains.
The selected deep-family defect E_D in102 is contained in E3 when
its selected cofactors are part of this family. It is not another
disjoint summand that can be added to E3 in(PD4). A consumer retaining
both interfaces must use the family partition or their containment.

## 3. A positive reference controls the actual five marginal

Keep the actual shallow3/9 carrier mixture pi. Set

    t_c=sum_(u,v)pi_(u,v)*(I_ROOT(c)=u+I_c=v),
    a_c=1-t_c/5, 3/5<=a_c<=1,
    h=sum_c eta_c, c5=sum_c eta_c*a_c-1/90.         (PD6)

The corresponding virtual shallow deletion is exactly(1-a)*Lambda.
The deep pure3 family is distinct from it. Dropping the remaining
nonnegative virtual families, and transferring with V-delta once,
gives the measure inequality

    mu^5<= (a*Lambda)^5-(V3deep)^5+(V-delta)^5.

Since Lambda on each ternary cell is dominated by its raw pure3
survivor tensor q, (a*Lambda)^5<=(sum eta_c*a_c)*q. Substitute(PD1):

    mu^5<=c5*q+Xi+(V-delta)^5.                    (PD7)

The effective source has1/2<=h<=5/9, so

    c5>=(3/5)*(1/2)-1/90=13/45>0.

Thus c5*q is a positive measure. Define

    nu5=(mu^5-c5*q)_+,
    e=E3+omega+(z-dmax)/90.

The same positive-part argument as115 yields

    mu^5<=c5*q+nu5,
    nu5(1)<=e, nu5<=mu^5<=h*Haar5.               (PD8)

This last domination uses the actual source, not a claimed bound on
the unbounded density of V-delta. It rules out an arbitrary atomic
error carrying positive mass at infinitely many nested five labels.

For any separately labelled first-five test F, for example,

    mu^5(F)<=c5*q(F)+min(e,h/5).                  (PD9)

No independence between different test events is needed.

## 4. The entire descendant-five tail has an exact error

For arbitrary independent original five cylinders F_b of depth b>=2,
including absent test labels by enlargement, (PD8) gives

    sum_(b>=2)mu^5(F_b)
       <=c5/20+R5(e,h),
    R5(e,h)=sum_(b>=2)min(e,h*5^-b).              (PD10)

Here sum_(b>=2)q(F_b)<=sum_(b>=2)5^-b=1/20. For e=0, R5=0.
For e>0, let N>=2 be the first integer with h*5^-N<=e. Then

    R5(e,h)=(N-2)*e+(5*h/4)*5^-N.                (PD11)

The final term is the entire remaining tail. The implementation
directly reuses66's exact `min_geometric` function for this sum.
There is no finite-height replacement of the original family.

On the K face, a=(1,4/5,4/5,4/5,4/5), h=1/2 and
sum eta_c*a_c=37/90. Therefore c5=2/5, e=0 and(PD10) is1/50,
exactly75's complete pure-five descendant cap. Root/cell-restricted
15/45 tests and the remaining mean-head corrections require their
own interfaces; (PD10) does not silently supply them.

## 5. Concentration gives an explicit uniform version

Let qK>=1-sigma with0<=sigma<1/2. By106, choose the whole K
orientation with selected deficit cell0 and distinguished carrier
(1,1), each of weight at least1-sigma. The other orientation swaps
cells0 and1. Let D0=deficit0 and Drest=sum_(c!=0)deficit_c. Then

    D0>=(1-sigma)/2, Drest>=0, D0+Drest<=1/2,
    h=(5-D0-Drest)/9<=1/2+sigma/18.              (PD12)

The distinguished carrier's raw ternary mass is(4-Drest)/9. Since
other carriers have nonnegative coefficients,

    c5<=(5-D0-Drest)/9
               -(1-sigma)*(4-Drest)/45-1/90
       <=2/5+13*sigma/90.                        (PD13)

The coefficient of Drest in the first line is-(4+sigma)/45<0.
Keeping this common deficit budget is stronger than separately
bounding h, the root and the cell. The weaker bound
2/5+sigma/6-sigma²/45 is also valid, but is not used in(PD13).

Concentration gives alpha0<=sigma/4 and beta0+beta1<=sigma/4.
The two root0 availability candidates imply

    z-dmax<=alpha0+min(beta0,beta1)<=3*sigma/8,
    (z-dmax)/90<=sigma/240.                       (PD14)

Consequently, for any proved upper u>=E3+omega,

    sum_(b>=2)mu^5(F_b)
       <=1/50+13*sigma/1800
           +R5(u+sigma/240,1/2+sigma/18).         (PD15)

One may use u from(PD5), or conservatively u=rho. The former still
depends on the actual shared carrier defects. The concave-error
warning of115 applies to R5 as well: substituting the remaining
budget into it does not preserve a finite convex vertex problem.
This is a quantitative full-tail estimate on the specified actual
domain, not a conclusion about the complete global comparison.

## Verification and remaining boundary

[pure_three_projected_defect.py](../frontier/pure_three_projected_defect.py)
checks the complete coefficients, the concentrated formulas, and
four finite actual source/cofactor configurations using the existing
original-label constructor. Their deep pure3 carriers lie in cell1,
root1, independently varied residues, or are absent. Seven caps and
actual union deletion are computed separately. The program checks
the projected positive measure and its exact capacity identity,
the actual survivor excess, and independent descendant-five tests.

The [certificate](../certificates/source_norms/pure_three_projected_defect.json)
keeps these useful exact values and complete tail evaluations. Finite
experiments test the source identities; arbitrary heights and changing
residues are covered by(PD2)--(PD3) and monotone convergence.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/pure_three_projected_defect.py --check
```

Forced27 concentration, the entire109 mean correction and the complete
numerator remain additional obligations. There is no new global K,
Lean verification or unrestricted solution claim.
