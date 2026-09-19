[Index](../marked_head_profile.md) · [Same-law fallback construction](35-ap45-layout-costs-and-complete-core-tails.md) · [Allocated comparison](53-allocated-seven-thresholds-sharpen-actual-survival.md) · [Global assembly](221-the-assigned-j-reserve-enters-the-complete-global-comparison.md)

# Each complete fallback uses its own square bound

The eight fallback branches in221 inherit complete values from53.
Each already has its own same-law Gamma13 bound, but its row
potential uses the larger global Gamma13 target. Substituting
the certified branch value improves every fallback. The largest
complete fallback decreases from436.051121410074... to

    417.795824371042067... .

This remains14.795824371042067... above403. The other seven
branches stay below403. The effective-source cases, full global
bound508.832228516835... and terminal errors are not improved
by this substitution alone. Unrestricted Erdos7 remains unresolved.

## 1. Same source, same AP law and same complete tails

For each original fallback b,35 supplies three certified pure
masses u3,u5,u7 and a source density bound db. Define

    A_b=db*u3*u5*u7,
    oldcaps_b=((3,1/u3),(5,1/u5),(7,1/u7)).

Let X denote the corresponding complete product-cap variable.
These are source comparison variables, not an assertion that
the actual test load has an independent product distribution.
The original branch assumptions and source-domination proof
remain exactly those of35.

With H_b(t)=A_b*E(X-t)_+, the same AP(4,5) survival comparison is

    rho_b=919/924-H_b(4)/6-4*H_b(5)/33-H_b(5/2)/22>0.

The auxiliary count N uses the same cap5/3 at11 and cap12/7 at13.
For a square threshold T, the existing complete fallback upper is

    E_b(T)=[G*q2-T*q0
        +sum_(n<ceil(sqrt(T))) p_n*n^2
          *min(A_b*E(X^2-T/n^2)_+,G-1)]/rho_b,      (FB1)

where q0 and q2 are the exact remaining probability and second
moment of N. G is the same certified uniform source-square cap
102715/2916 used by53. Every exponent and count continuation is
retained by the full geometric moments; none is discarded by
the finite sum in(FB1).

The branch's already computed values are

    gamma_b=16+E_b(16),
    t81_b=E_b(81),
    h_b(t)=A_b*E(X*N-t)_+/rho_b, t=5,6,7,8.         (FB2)

Thus gamma_b is a valid same-law bound in the exact slot where35
requires a Gamma13 value. It is not an old AP(4,6) bound, nor a
bound from a different fallback branch.

## 2. Substitute before applying the row potential

Write Gamma_* for53's global target. The complete inherited
fallback row has the form

    Kold_b=C0+AC*(Gamma_*-16)+L_b+t81_b,
    AC=2371/2880>0,                               (FB3)

where L_b is the unchanged positive combination of the complete
hinges h_b(5),...,h_b(8), with the original17/19 row coefficients.
The row-potential inequality accepts any certified same-law
Gamma13 upper on this branch. Replacing Gamma_* by gamma_b gives

    Knew_b=C0+AC*(gamma_b-16)+L_b+t81_b
          =Kold_b-AC*(Gamma_*-gamma_b).            (FB4)

The checker verifies gamma_b<=Gamma_* for each branch, and it
independently assembles the first line of(FB4) from the complete
hinges. There is no subtraction of an unproved improvement from
an actual unknown cost. It is a direct use of the previously
certified branch upper in a positive-coefficient inequality.

## 3. All eight branch values

| Original branch | Previous complete bound | Branch-local complete bound |
| --- | ---: | ---: |
|3 absent,5 absent,7 absent|218.5747204525|145.6290133575|
|3 absent,5 absent,7 present|235.4224729495|166.7164346740|
|3 absent,5 present,7 absent|245.8354492391|179.7382305461|
|3 absent,5 present,7 present|268.9880196490|208.7208466045|
|9 absent or ineffective,5 absent,7 absent|292.2257972402|237.8010027906|
|9 absent or ineffective,5 absent,7 present|338.6343500831|295.8863306524|
|9 absent or ineffective,5 present,7 absent|360.5767679009|323.3273846424|
|9 absent or ineffective,5 present,7 present|436.0511214101|417.7958243710|

For the last branch, the exact new value is

    3404213816079321070322396619648097696278819877
    /8148032166678761182742305326245791763280000.

Its saving is18.255297039031582..., leaving the positive gap
stated above. No assumption that9 is effective is added to
dispose of this remaining branch.

`frontier/branch_local_fallback_comparison.py --check` recomputes
all eight original values using their complete product moments,
matches both53 and221, and then verifies(FB4) by direct row
assembly. The certificate retains every branch's source inputs,
survival lower bound, local gamma, complete T81, four hinge
uppers, old value, saving and new value. No main-source vertex
scan or retained-head scan is needed for this calculation.

This is an ordinary analytic comparison with exact-rational
verification, not a Lean result or a completed global403 test.
