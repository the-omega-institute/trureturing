[Index](../../marked_head_profile.md) · [Previous complete union](177-the-marked-branch-pays-only-its-actual-slot-cutoff.md) · [Wide source rectangle](170-a-complete-head-scan-transports-across-source-radii.md) · [Fresh one-twentieth domain](181-a-fresh-complete-comparison-covers-source-radius-one-twentieth.md)

# The wider source union reaches the far escape boundary

The complete global comparison is

    K<=509.272884772686132267... .                  (WU1)

It joins181's complete source-radius1/20 domain with170's
source-radius1/18 domain. Their entire complement is controlled
by the original unmarked reserve. No marked theorem is applied
beyond its domain, and no marked cost credit is needed outside
these two complete local domains.

All eight original fallback comparisons and both terminal errors
remain. The smaller complete sufficient gap above403 is
106.273459773004274166... . Unrestricted Erdős7 remains unresolved;
canonical118 is unchanged and no Lean or frozen-state claim is made.

## 1. Two complete actual-source rectangles

Use the same actual source variables sigma=1-qK, rho and r. The
complete local domains are

    D0: sigma<=s0=1/20, rho<=R0=1/1000;
    D1: sigma<=s1=1/18, rho<=R1=1/13000.          (WU2)

Both include the two K orientations. The actual inequality
r<=5rho implies r<=1/200 on D0 and r<=1/2600 on D1, exactly
within their complete proved ranges. There is no independent
local slot cutoff.

181 gives K<=505.701239618792632674... on D0.170 gives
K<=506.975514690183036952... on D1. Both include all52 original
independent tests, one actual residual and actual mass coefficient,
the complete denominator and every infinite exponent/count tail.
Both bounds are strictly below(WU1).

Outside their union, the exhaustive residual floors are

    rho>=R0 when0<=sigma<=s0;
    rho>=R1 when s0<=sigma<=s1;
    rho>=0  when s1<=sigma<=1.                   (WU3)

Closed boundaries can be handled by either valid adjacent
argument. Every use of a local comparison tests its own actual
source for membership; no local improvement is transported to
another source without a proof.

## 2. The unmarked reserve suffices everywhere in the complement

Let A, gamma1 and gamma2 be the original complete constants,
a=53/360, and

    e(s)=gamma2*s-(gamma2-gamma1)*s^2.

Before changing K0, the original unmarked reserve is at least
e(sigma)+A*rho. On sigma<=1/3 the signed mass bound is
a+sigma/10+rho. Thus, at target decrement h,

    Phi>=e(sigma)-h*(a+sigma/10)+(A-h)*rho.       (WU4)

Using the appropriate floor from(WU3) is valid when A-h>0.
In particular the low-source complement now has enough residual
reserve on its own. It no longer needs a split according to r
or any of the marked-cost losses used in the preceding proof.

For the other source ranges retain the original mass bounds:

    a+5sigma/9+rho,                 1/3<=sigma<1/2;
    1/4+11sigma(1-sigma)/36+rho,     1/2<=sigma<=1. (WU5)

Each corresponding Phi is concave in sigma. The middle expression
at1/2 is used only as the left-limit endpoint of that interval;
the far expression covers the actual boundary point. Both sides
of each change in mass bound are retained.

## 3. Ten endpoints and one far-source controller

Take

    h=4gamma1
      =15240056495574031935365456355486859072608164346131
        /81148843214471861289550086966632892837609000000000
      =0.187803742997240436534... .              (WU6)

All ten endpoint capacities below are rounded for display;
the certificate compares exact rational values.

| Complete outside endpoint | Decrement capacity |
| --- | ---: |
| Low, sigma=0 |0.366173028334|
| Low, sigma=1/20 |0.535288847616|
| Bridge, sigma=1/20 |0.209575471892|
| Bridge, sigma=1/18 |0.227900910879|
| Early, sigma=1/18 |0.200688395544|
| Early, sigma=1/3 |0.744702812493|
| Middle, right side at1/3 |0.404504313193|
| Middle, left limit at1/2 |0.369733237074|
| Far, sigma=1/2 |0.481439874658|
| Far, sigma=1 |0.187803742997|

The unique minimum is sigma=1. There e(1)=gamma1 and the mass
upper bound is1/4, giving(WU6). Every other endpoint has strictly
positive signed margin. The inequalities

    A-h>0,
    gamma2-gamma1>0,
    gamma2-gamma1-11h/36>0

prove the needed residual monotonicity and concavity. Thus these
ten checks prove the complete outside bound, not merely a sampled
set of sources.

The eight unchanged fallback bounds are each strictly below K0-h.
The original positive survival factor still permits division.
Both terminal errors and their original boxes are retained,
yielding the complete remaining gaps recorded in the certificate.
Together with(WU2), these facts prove(WU1).

## 4. What this boundary does and does not establish

The improvement over177 is0.017416939967601856554... . The source
bridge no longer controls. Within this particular scalar outside
template, improving constants strictly inside D0 or D1 will not
move the endpoint sigma=1, qK=0.

This does not prove an actual finite family attains simultaneous
equality in the escape reserve and the1/4 mass bound. That
compatibility is a separate mathematical question. A stronger
joint source/mass estimate at the far endpoint, or another
complete local description of its source geometry, is needed
to improve this template further.

The [helper](../../frontier/comparison-bounds/wide_unmarked_union_comparison.py)
reconstructs the complete preceding comparison and pins181/170
with their transitive sources. The
[certificate](../../certificates/source_norms/comparison-bounds/wide_unmarked_union_comparison.json)
retains every local domain, endpoint, fallback and terminal term.
All arithmetic is rational and multipart inputs use
certificate_io.read_artifact_bytes.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/wide_unmarked_union_comparison.py --check
```
