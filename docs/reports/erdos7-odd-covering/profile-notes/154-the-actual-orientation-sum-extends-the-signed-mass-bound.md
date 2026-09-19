[Index](../marked_head_profile.md) · [Signed polynomial](150-signed-source-monotonicity-strengthens-the-product-mass-bound.md) · [Common actual losses](153-the-six-source-losses-share-one-actual-concentration-budget.md)

# The actual orientation sum extends the signed mass bound

For the original actual source, both distinguished K orientations satisfy

    qK>=1-sigma, 0<=sigma<=1/3
      ==> S0<=53/360+sigma/10,
          0<E<=S=S0+rho<=53/360+sigma/10+rho.     (JO1)

This extends150's domain6/49 without changing its slope or the actual
residual. The new ingredient is the sum of the two original orientation
contributions. Separate product inequalities permit simultaneously
spending concentration on deficit and carrier losses; the actual sum
does not. This is a denominator upper bound for signed comparisons,
not a lower bound on survival or a complete global improvement.

## 1. Retain the actual two-orientation sum

Use150's six losses a,z,b,d,l,p in[0,sigma]. Put

    A=(1-a)*(1-z)*(1-b)=1-y,
    x=(sigma-y)/(1-y), u=d, v=1-(1-l)*(1-p).

The selected orientation from148 gives

    A*(1-u)>=1-sigma, A*(1-v)>=1-sigma,
    0<=y<=sigma, 0<=u,v<=x<=sigma.              (JO2)

In the original formula write h_i=l_i*pi_i. The actual deficit
weights and the h weights each sum to at most1. The selected entries
are d_1=1-u and h_1=1-v; hence d_2<=u and h_2<=v. Thus

    qK=A*(d_1*h_1+d_2*h_2)
       <=A*((1-u)*(1-v)+u*v),
    u+v-2uv<=x.                                (JO3)

The simultaneous use of(JO2),(JO3) is essential. In particular,

    u+v-2uv-(1-x)*(u+v)
       =u*(x-v)+v*(x-u)>=0.

As x<1, it follows that

    u+v<=x/(1-x)=(sigma-y)/(1-sigma).           (JO4)

This bound contains one shared concentration loss, with no
probabilistic independence assumption.

## 2. Bound the same signed polynomial

The coordinate-monotonicity reduction and exact cap cancellation
from150 remain unchanged. With its source upper relaxation F,

    S0<=F,
    P:=360*(F-53/360)
      =24a+36z+8b+(14+5z)*u+5l+C*p,
    C=16+8z+6a+2b.                             (JO5)

The three common losses each are at most y. For0<=y<=1/3,

    36y-(24a+36z+8b)
       =12a*(1-3z)+b*(36*(1-a)*(1-z)-8)>=0.   (JO6)

The first factor is nonnegative because z<=y<=1/3. The second is
positive because (1-a)*(1-z)>=A=1-y>=2/3.
Also

    C-(14+5z)=2+3z+6a+2b>=0,
    C<=16*(1+y).

The late/carrier terms satisfy

    C*v-(5l+C*p)=l*(C*(1-p)-5)>=0,             (JO7)

since C>=16 and p<=1/3. Substitution of(JO4),(JO6),(JO7) in(JO5)
therefore yields

    P<=36y+C*(u+v)
      <=36y+16*(1+y)*(sigma-y)/(1-sigma).

Finally,

    36sigma-[36y+16*(1+y)*(sigma-y)/(1-sigma)]
      =(sigma-y)*(20-36sigma-16y)/(1-sigma)>=0. (JO8)

Here20-36sigma-16y>=20-52/3=8/3>0 throughout the domain.
Thus P<=36sigma, proving(JO1). Every source coordinate and the
original carrier cap were retained until150's justified monotonicity
operation; no realizability of the relaxed maximizer is asserted.

## 3. The former relaxed obstruction is excluded

The witness in150 had

    sigma=1/8, y=123/1000, u=v=2/877.

It saturated both separate products. But its necessary actual
concentration upper bound is

    qK<=(1-y)*(1-2u+2u^2)<1-sigma.

It therefore violates(JO3). This explains why it obstructed the old
two-product certificate without obstructing the present actual-source
theorem. No earlier theorem or exact non-extension calculation is
discarded.

The [helper](../frontier/joint_orientation_carrier_mass.py) verifies
the predecessor's signed polynomial and all new polynomial identities,
the domain margins, and the exact exclusion of that witness. Its
`bound_S0` and `bound_E` API checks the sigma<=1/3 domain explicitly.
These algebra checks supplement the ordinary proof above; samples
do not prove a continuum claim. No Lean or unrestricted Erdos7
resolution is asserted.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/joint_orientation_carrier_mass.py --check
```
