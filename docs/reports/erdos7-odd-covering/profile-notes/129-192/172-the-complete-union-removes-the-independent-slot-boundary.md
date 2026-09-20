[Index](../../marked_head_profile.md) · [Previous global union](167-two-complete-source-neighborhoods-remove-the-outer-crossing.md) · [Full slot radius](169-the-complete-source-bound-needs-no-independent-slot-loss-cutoff.md) · [Wide source rectangle](170-a-complete-head-scan-transports-across-source-radii.md) · [Wider full-slot source](173-the-full-slot-source-domain-extends-to-one-over-twenty-six.md)

# The complete union removes the independent slot boundary

Combining173 and170 on their actual source domains, and retaining
the complete outside comparison, gives

    K<=509.291456192200206973... .                  (FU1)

This improves167 by0.009886743261384647266... . All eight original
fallbacks and both terminal errors remain. The smaller complete
sufficient gap above403 is106.292031192518348871... . The
unrestricted Erdős7 problem remains unresolved; canonical118 is
unchanged, and no Lean or frozen-state claim is made.

The earlier independent local slot-loss boundary is removed.
The controlling inequality now lies at sigma=0,rho=1/1000 in
the complement of the complete local domain. This is a boundary
of the retained inequalities, not a claim that a finite actual
family attains their simultaneous equality.

## 1. The complete source union has no independent slot cutoff

The two closed domains, each including both K orientations, are

    D0: sigma<=s0=1/26, rho<=R0=1/1000;
    D1: sigma<=s1=1/18, rho<=R1=1/13000.           (FU2)

Every actual source satisfies r<=5rho. Thus D0 implies r<=1/200,
exactly the full range proved in173, while D1 implies r<=1/2600,
inside170's complete theorem. There is no additional r condition
whose complement requires a separate local treatment.

On D0,173 gives the complete bound504.917585788797449...;
on D1,170 gives506.975514690183036952... . Each retains all52
independent original tests, the full survival denominator, one
actual residual and the actual mass coefficient, and every
infinite exponent/count tail. Both bounds are strictly below(FU1).

Outside D0 union D1 the remaining cases are exhaustive:

- sigma<=s0 implies rho>=R0;
- s0<=sigma<=s1 implies rho>=R1;
- sigma>=s1 retains rho>=0.

The weak endpoints may belong to either valid adjacent argument.
Only the same actual source is tested for domain membership;
no local gain is transferred to an unrelated source.

## 2. Low-source marked and unmarked reserves

Retain the original constants and46 outer cost alternatives from167:

    a=53/360,
    B(s)=B0-B1*s+B2*s^2,
    e(s)=gamma2*s-(gamma2-gamma1)*s^2,
    A=54.27497997750398...,
    P=37.97187303103495...,
    Q=0.515666653007543...,
    L5=13.762429399039852... .

For sigma<=s0<21/500 and r<=rcut=3/1000 the original marked
comparison, at target decrement h from K0, is

    Phi>=B(sigma)-Q*sigma+e(sigma)
          -h*(a+sigma/10)+(A-h-P-L5)*rho.        (FU3)

Here the slot-loss payment already used r<=5rho once. Outside
D0, rho>=R0. Since A-h-P-L5>0, substituting R0 is valid. The
remaining quadratic is concave, so sigma=0 and sigma=s0 suffice.

For sigma<=s0 and r>=rcut, use the original unmarked reserve,
discard its nonnegative escape term, and retain both lower bounds
rho>=R0 and rho>=rcut/5. Since R0>rcut/5,

    Phi>=(A-h)*R0-h*(a+s0/10).                  (FU4)

The split at rcut is an unchanged hypothesis of the outside
marked theorem. It is not reinstating an independent cutoff in
the complete local domain D0.

## 3. Bridge and remaining source intervals

On s0<=sigma<=s1 outside D1, the complete unmarked reserve and
the inherited signed mass bound give

    Phi>=e(sigma)-h*(a+sigma/10)+(A-h)*R1.       (FU5)

It is concave; checking s0 and s1 proves the entire bridge. The
marked credit and its losses are both absent in this branch.

Above s1 the unchanged zero-floor expressions are

    e(sigma)-h*(a+sigma/10), s1<=sigma<=1/3;
    e(sigma)-h*(a+5sigma/9), 1/3<=sigma<=1/2;
    e(sigma)-h*[1/4+11sigma(1-sigma)/36],
                                      1/2<=sigma<=1.          (FU6)

The middle expression at1/2 is a left-limit bound. Both sides
of every mass-bound switch are retained. The required concavity
conditions are verified for the same selected h.

## 4. All endpoints and terminal terms

The minimum of the eleven endpoint decrement capacities is

    h=[B0+(A-P-L5)/1000]/[a+1/1000]
      =0.169232323483165731305... .              (FU7)

The exact fractions are in the certificate; the following values
are rounded for display.

| Outside endpoint | Decrement capacity |
| --- | ---: |
| Low source marked, sigma=0 |0.169232323483166|
| Low source marked, sigma=1/26 |0.170582740100794|
| Low source, large r |0.356911682630843|
| Residual bridge, sigma=1/26 |0.170386803029639|
| Residual bridge, sigma=1/18 |0.227900910878580|
| Early middle, sigma=1/18 |0.200688395544335|
| Early middle, sigma=1/3 |0.744702812493349|
| Old middle, right side at1/3 |0.404504313192766|
| Old middle, left limit at1/2 |0.369733237073824|
| Far, sigma=1/2 |0.481439874657831|
| Far, sigma=1 |0.187803742997240|

Only the first endpoint has equality. The residual coefficients
A-h-P-L5 and A-h remain positive, and every other signed endpoint
margin is positive. The bridge requires residual radius at least

    Rcrit=[h*(a+s0/10)-e(s0)]/(A-h)
         =0.000073698019254073422296...<1/13000. (FU8)

The far endpoint and both endpoints of every intervening interval
are checked separately; (FU8) alone is not a global criterion.

All eight complete fallback bounds stay strictly below K0-h.
The original positive survival factor justifies division, and
both complete terminal errors are carried forward unchanged.
These facts prove(FU1) over the entire inherited comparison domain.

The [helper](../../frontier/source-budgets/full_slot_union_outer_comparison.py)
reconstructs167's complete partition, pins both complete new
local inputs and their transitive sources, and checks the full
complement using rational arithmetic. The
[certificate](../../certificates/source_norms/source-budgets/full_slot_union_outer_comparison.json)
retains every endpoint, local comparison, fallback and terminal
quantity. Multipart inputs use certificate_io.read_artifact_bytes.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/full_slot_union_outer_comparison.py --check
```

Improving a comparison strictly inside D0 or D1 alone will not
change(FU7). A larger usable residual neighborhood or a stronger
outside marked reserve is needed to move this controlling bound.
