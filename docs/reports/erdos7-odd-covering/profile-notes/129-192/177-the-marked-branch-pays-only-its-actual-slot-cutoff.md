[Index](../../marked_head_profile.md) · [Original source-dependent reserve](147-source-dependent-credits-cross-the-old-middle-bottleneck.md) · [Unsimplified signed reserve](155-the-signed-mass-bound-reaches-the-current-source-credit-ceiling.md) · [Complete source union](172-the-complete-union-removes-the-independent-slot-boundary.md)

# The marked branch pays only its actual slot cutoff

Retaining the marked theorem's own slot-loss restriction improves
the complete global comparison to

    K<=509.290301712653734124... .                  (CS1)

Both complete source domains from172, all eleven outside endpoints,
eight original fallbacks, both terminal errors and every infinite
tail remain. The smaller complete sufficient gap above403 is
106.290876712971876023... . This does not resolve unrestricted
Erdős7; canonical118 is unchanged and no Lean claim is made.

## 1. Keep the slot loss separate from the actual residual

The unsimplified complete reserve in155(JC2), derived from147's
46 fixed original cost alternatives, is

    R>=B(sigma)-Q*sigma+e(sigma)+(A-P)*rho-L*r.    (CS2)

It holds when sigma<=21/500 and r<=rstar=3/1000. The same actual
source satisfies the signed mass bound

    E<=a+sigma/10+rho, a=53/360.

Thus at target decrement h the marked comparison is

    R-hE>=B(sigma)-Q*sigma+e(sigma)
          -h*(a+sigma/10)+(A-P-h)*rho-L*r.        (CS3)

The exact slot price is

    L=1998435125243256214147273
       /726047366819799521296800.

The earlier residual substitution r<=5rho remains true. On the
current complementary region, however, sigma<=1/26 and rho>=1/1000,
so5rho>=1/200>rstar. The marked branch already has the stronger
r<=rstar. Applying that restriction directly to(CS3), and using
A-P-h>0, gives

    R-hE>=B(sigma)-Q*sigma+e(sigma)
      -h*(a+sigma/10)+(A-P-h)/1000-L*(3/1000).    (CS4)

Relative to172, each low-source marked endpoint gains exactly

    L*(5/1000-3/1000)=L/500
      =0.005504971759615941110... .                (CS5)

This is a tighter bound on the same negative term, not a second
credit. It uses no marked estimate outside its declared domain.
When r>=rstar, the entire original unmarked branch remains as in172.

## 2. The lower source bridge now controls

The two low-source marked endpoint capacities become respectively
0.2063723128658819... and0.2067833749858580... . Every other
endpoint retains172's reserve and payment coefficient. Concavity
continues to reduce each entire source interval to its endpoints.

The unique minimum is now the unmarked bridge endpoint

    sigma=s0=1/26, rho=R1=1/13000,
    h=[e(s0)+A*R1]/[a+s0/10+R1]
      =0.170386803029638579980... .                (CS6)

The local bounds504.917585788797449... and506.975514690183036952...
remain strictly below K0-h. All eleven signed endpoint margins
are nonnegative, with equality only at(CS6). The residual
coefficients A-P-h and A-h are positive. The unchanged eight
fallback comparisons are also strictly below the new target,
and the original positive survival factor still permits division.

Therefore K<=K0-h proves(CS1), improving172 by
0.001154479546472848674... . Both terminal errors are carried
forward unchanged; their inclusion is what yields the complete
remaining gap stated above.

The controller is an endpoint of the retained inequality system.
No actual finite family attaining every relaxed equality is asserted.
Further enlargement of the low-source residual radius alone does
not move(CS6). Increasing its source reach or the wider rectangle's
residual reach, while retaining their complete local bounds, can
change this particular obstruction.

The [helper](../../frontier/source-budgets/capped_slot_outer_comparison.py) reconstructs
the preceding complete union and verifies the original unsimplified
slot price, the new endpoints, local comparisons, fallbacks and
terminal quantities. The
[certificate](../../certificates/source_norms/source-budgets/capped_slot_outer_comparison.json)
stores exact rational values and the complete input hash closure.
Multipart certificates use certificate_io.read_artifact_bytes.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/capped_slot_outer_comparison.py --check
```
