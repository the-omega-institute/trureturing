# Pure-union savings control all four later rows under one law

Let Q={5,7,11,13,17,19}. For any finite family of nonunit Q-smooth
moduli with at most two original occurrences per numerical label, keep
all original residues globally fixed. The existing actual PA law has
complete nonunit query norm strictly below T=257/51 whenever ANY of
the following conditions holds:

1. Numerical modulus11 has at most one original occurrence.
2. Numerical modulus13 has at most one original occurrence.
3. Numerical moduli17 and19 each have at most one original occurrence.

Every other label may occur twice, at arbitrary finite heights and with
arbitrary phases. No old5/7 window or old-coordinate factorization is
required. In particular, an actual all-laws lower witness above T must
have two occurrences at11 and13, and two at at least one of17 and19.
These are necessary conditions on such a lower witness, not an exhibited
witness or a resolution of unrestricted Erdős #7.

The proof bounds the ACTUAL row loss by separating the pure-prime union
from the nonpure old-cofactor count. Savings from all four rows add in
one actual mass identity. This extends the first11 inequality of
[report558](558-first-eleven-inventory-and-an-actual-phase-counterexample.md);
it is ordinary mathematics and exact rational computation, not new Lean
verification.

## 1. The actual process and the fixed comparison

Use the PA construction of
[report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#retaining-the-actual-pure-anchor-masses).
Let x>=1/2 and y>=2/3 be the complete pure5 and pure7 survivor masses.
Start with lambda0, Haar restricted to the full actual5/7 survivor.
Its mass is xy-m, where0<=m<=1/12 is the mixed5/7 union mass inside the
pure product. The raw pure-product restriction is denoted sigma.

At each q=11,13,17,19 and complete old history h, let g_q(h) be the Haar
fraction avoiding exactly the original classes assigned to that row.
The actual kernel has density min(C_q,1/g_q(h)) on this allowed set,
and is zero if it is empty. Its row mass is s_q=min(1,C_q*g_q). Use

| q | Threshold t_q | Density cap C_q | Charge coefficient a_q |
| --- | ---: | ---: | ---: |
|11|2|5/3|1/3|
|13|2|3/2|1/4|
|17|4|2|1/4|
|19|4|9/5|1/5|

These satisfy a_q=2C_q/(q-1) and C_q-1=a_q*t_q. Let ell_q=1-s_q
be the local row loss, and Loss_q its integral against the actual prefix
subprobability. Each kernel is fixed by the same original family; it is
never changed to fit a comparison query.

The existing completed-kernel comparison gives absolute prefix hinge
bounds F_q(x,y), baseline mass alpha(x,y), and final hinge Phi(x,y),
with

    alpha=xy-1/12-sum_q a_q*F_q,
    lambda(1)=alpha+(1/12-m)+sum_q S_q,
    S_q=a_q*F_q-Loss_q>=0,                              (PU1)
    lambda(L-1)<=2*lambda(1)+Phi

for every finite complete final query L including the unit. The actual
lambda is supported on the full survivor, has positive mass, and has
mass at most one. Normalize it ONCE to nu=lambda/lambda(1). This law
need not be uniform Haar on the survivor.

## 2. Keep the actual pure-q forbidden union separate

Fix one q row. Let r_q be the Haar mass of the actual union of its
pure-q originals. This set depends only on the q-coordinate. Define

    theta_q=(q-1)*r_q/2,  delta_q=1-theta_q.

At most two originals per pure numerical label give0<=theta_q<=1 by
the complete geometric sum. Overlap of pure cylinders only reduces this
actual union mass.

At current exponent e>=1, assign each numerical label's at most two
originals to slots j=1,2 once, keeping its full residue fixed. Let
n_(e,j)(h) count the active NONPURE old cofactors in this slot. Define

    beta_(e,j)=(q-1)/(2*q^e), sum_(e>=1,j=1,2) beta_(e,j)=1,
    G_q(h)=sum_(e,j) beta_(e,j)*(n_(e,j)(h)-(t_q-1))_+,
    b_q(h)=sum_(e,j) beta_(e,j)*min(n_(e,j)(h),t_q-1).

Here0<=b_q<=t_q-1. Only finitely many n_(e,j) are nonzero, but the
weight identity retains the whole absent-exponent tail. No missing
original is inserted into the actual forbidden union.

The union bound for NONPURE current cylinders, together with the actual
pure union, gives

    1-g_q(h)<=r_q+(2/(q-1))*(G_q(h)+b_q(h)).             (PU2)

This does not assume any disjointness of different nonpure cylinders,
or of their intersection with the pure union.

Where ell_q>0, the exact kernel identity and PU2 yield

    ell_q=C_q*(1-g_q)-(C_q-1)
          <=a_q*(theta_q+G_q+b_q-t_q)
          <=a_q*(G_q-delta_q).

On this positive-loss set, ell_q<=1 and delta_q>=0 give

    (1+a_q*delta_q)*ell_q
       <=a_q*G_q-a_q*delta_q*(1-ell_q)
       <=a_q*G_q.

The ENDPOINT inequality also holds on the zero-loss set by nonnegativity:

    (1+a_q*delta_q)*ell_q<=a_q*G_q.                    (PU3)

This local inequality
is the same for every permitted old history and every actual residue
assignment. It retains the cost of the pure union before the old-query
comparison.

## 3. Integrate against the same actual prefix

For a fixed slot,1+n_(e,j) is a legal old query with one unit term and
at most one cylinder per occupied nonunit old numerical cofactor. Add
arbitrary fixed query phases at missing labels only when applying the
comparison. Its threshold-t_q hinge dominates
(n_(e,j)-(t_q-1))_+.

The actual prefix is dominated by the same completed-kernel process
started from sigma. The PA comparison therefore bounds every such
integral by F_q(x,y), irrespective of that slot's full-label phases.
Weighting by beta, whose complete sum is one, gives

    integral G_q d lambda_<q <=F_q(x,y).

Integrating PU3 now proves

    Loss_q<=a_q*F_q(x,y)/(1+a_q*delta_q),
    S_q>=a_q^2*F_q(x,y)*delta_q/(1+a_q*delta_q).         (PU4)

The integral uses the actual prefix at this q. Later rows use their own
actual prefixes from the same sequential process. Adding their absolute
savings in PU1 is valid; multiplying unrelated optimized conditional
probabilities or switching the final law would not be justified.

The pure union can be replaced by an explicit numerical inventory upper
bound. If c_(q,e) in{0,1,2} is the number of pure-q originals at exponent
e, then

    theta_q<=p_q=sum_(e>=1)(q-1)*c_(q,e)/(2*q^e)<=1.

The lower bound in PU4 decreases as theta_q increases. Thus p_q gives
a possibly weaker but fully numerical sufficient condition. Using the
actual union is stronger when pure cylinders overlap.

## 4. One joint sufficient region

The raw auxiliary old-prime count law has mass x-1/5 or y-1/7 at count1
and weights(p-1)/p^n at counts n>=2. Increasing x or y adds positive
mass at count1. Every F_q is an integral of a nonnegative hinge against
the tensor product with the fixed later auxiliary laws. Hence it is
nondecreasing in x and y, and its minimum occurs at x=1/2,y=2/3.
The exact minima are

| q | f_q=F_q(1/2,2/3) |
| --- | ---: |
|11|97/840|
|13|47/240|
|17|202266823897/1875745872000|
|19|807126826607839/4914954383539200|

Write

    Gamma=sum_q a_q^2*f_q*(1-theta_q)/(1+a_q*(1-theta_q)),
    kreq=6168733163201163811/1650097635185615616000.

The existing NC4 identity, with d5=x-1/2 and d7=y-2/3, is

    (T-2)*alpha-Phi=-c0+A5*d5+A7*d7+A57*d5*d7,
    c0=(T-2)*kreq,

where all three A coefficients are positive. Combining it with PU1 and
PU4, and retaining the nonnegative packing credit1/12-m, proves

    (T-2)*lambda(1)-Phi >=(T-2)*(Gamma-kreq).            (PU5)

Consequently Gamma>=kreq implies R_Q(nu)<=T. If Gamma>kreq, set
Delta=(T-2)*(Gamma-kreq)>0. Finite labelwise maximizing queries under
this SAME nu, followed by increasing query boxes, give

    R_Q(nu)<=T-Delta/lambda(1)<=T-Delta<T,               (PU6)

since lambda(1)<=1. The infinite-height completion is the existing PA
comparison; no query tail is discarded. This criterion does not require
calculating, or knowing in advance, which query attains any supremum.

## 5. Missing one root occurrence gives uniform margins

If numerical modulus q itself occurs at most once, every deeper pure
label may still occur twice. Thus

    theta_q<=((q-1)/2)*(1/q+2/[q*(q-1)])
            =(q+1)/(2*q).

The resulting lower bounds for S_q are

| Restricted root label | Guaranteed absolute saving |
| --- | ---: |
|11|97/19152|
|13|47/9280|
|17|202266823897/71278343136000|
|19|2421380479823517/851925426480128000|

Either of the first two alone exceeds kreq. The sum of the last two
also exceeds it; neither of those two lower bounds alone does. PU6
therefore supplies these explicit same-law bounds:

| Sufficient root condition | Uniform query upper bound |
| --- | ---: |
|At most one occurrence at11|2733779746141627138211/542935350932041267200|
|At most one occurrence at13|79279616946006192818519/15745125177029196748800|
|At most one at17 and at most one at19|451123045202905459499/89627423011003637760|

All three are strictly below257/51. Missing all occurrences of a root
is included. No condition is imposed on higher powers of that prime or
on mixed labels containing it. The shared union condition in Section4
also applies when these simple root criteria do not.

If repeated identical classes are retained as two occurrences, two
root-q copies with the SAME residue have union mass1/q and satisfy the
same bound on theta_q. The necessary condition for a lower witness can
therefore be sharpened to two DISTINCT root residues at11 and13, and
two distinct root residues at at least one of17 and19.

## 6. Exact computation and open boundary

The [standalone calculation](../../frontier/cover-geometry/pure_union_pa_savings.py)
reconstructs every F_q, alpha and Phi from their raw auxiliary atom
weights and COMPLETE means, using finite corrections at products below
each threshold. Its [exact data](../../frontier/cover-geometry/pure_union_pa_savings.json)
include all four anchor corners, the positive NC4 coefficients, the
joint-saving requirement, all four root savings and all three final
query bounds. It imports no old producer or result table.

All30 checks pass. The retained JSON SHA256 is
`b4a04e443b5563c06b30b1dfd8480103225a8e4e338cae2c1e1d50c27435291c`.
A separate calculation reconstructs the four prefix hinges and the
NC4 constants and matches every displayed corner and final bound.
Executing a copied script at a path containing spaces from another
working directory gives identical JSON bytes on the tested macOS host.
Other operating systems were not tested.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure_union_pa_savings.py
```

The program requires only Python3 and accepts `--output`. The finite
arithmetic does not substitute for PU2--PU5's ordinary proof for arbitrary
families. No Lean was added or built.

If all four pure unions approach their full two-copy geometric masses,
theta_q approaches1 and this particular saving tends to zero. Finiteness
does not give a uniform positive deficit. The dense regime still needs
a joint estimate involving actual nonpure unions, transported source
deletions or final-query response. The two-copy problem without the
stated sufficient conditions, and its separate connection to unrestricted
Erdős #7, remain unresolved.
