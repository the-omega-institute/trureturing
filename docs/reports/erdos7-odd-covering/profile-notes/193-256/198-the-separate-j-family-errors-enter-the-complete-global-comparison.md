[Index](../../marked_head_profile.md) · [Separate complete family errors](197-the-whole-j-reserve-keeps-each-original-family-error.md) · [Complete J replacement](196-the-actual-j-reserve-crosses-the-paired-table-capacity.md)

# The separate J family errors enter the complete global comparison

Using197's complete J-neighborhood reserve in196's full source
partition gives

    K<=68572621261645300524301011071832409249310755528079
         /134762826943554332736552326279349824852277192000
      =508.839290603239377074363522208900... .       (JF1)

The complete improvement over196 is0.0027166427235462530....
All52 local costs, full denominators, eight fallback branches and
both terminal errors remain. The sufficient threshold403 is not
reached. No actual-family sharpness or Lean verification is claimed.

## 1. Choose a paired target from the larger actual J neighborhood

Keep the original constants K0,H=gamma1/eJ,eK,eJ,eB from186.
Use197's proved rectangle

    d=1/2500, R=1/100000,
    qJ>=1-d, rho<=R,
    reserve_J>=499570949/75937500000.             (JF2)

Set aH=H*eK and etaH=gamma2-H*eB. Define the exact positive ratio

    epsilon=[etaH*d-(aH+etaH)*d^2]
             /[eJ-(eJ-eB)*d+(eK-eB)*d^2]
           =0.0028166427235462530...,
    h=H+epsilon, K=K0-h.                       (JF3)

For this target let

    fK=-h*eK, fJ=gamma1-h*eJ, fB=gamma2-h*eB,
    a=fJ-fK, eta=fB-fJ, Anew=A-(23/42)*h.

All coefficient signs required in196 hold: fK<fJ<0<fB,
a,eta,Anew>0 and K0-offset-h>0. Fresh reconstruction of every
original53 allocated row verifies all46656 lower/upper endpoint
inequalities at decrements0 and h, with the same original digests
and outside controls. Thus196's true-function Jensen argument
proves

    Phi_h>=fJ-a*x+eta*(1-x-y)+Anew*rho,
    x=qK, y=qJ, sqrt(x)+sqrt(y)<=1.            (JF4)

No earlier decrement-limited numerical table is simply extrapolated.

## 2. Every complementary source case remains covered

The complete181 and195 inner rectangles are unchanged. Their full
bounds505.70123961879... and499.19449167554... lie below(JF1).
Both include the whole actual range r<=5rho.

For the two inner complementary strips in196 AJ7, the four concave
endpoint lower margins become

    0.007346251794107836...,
    0.03605704405154761...,
    0.00010058300481220936...,
    0.018843350078693807... .                   (JF5)

They are all positive. The exact square-root brackets and the
correct negative J-mass coefficient are retained.

In the outer region0<=x<=11/12, use the same exhaustive split as196:

- If y<=1-d and x<=d^2, (JF4) is at least
  fJ+eta*d-(a+eta)*d^2, which equals zero exactly by(JF3).
- If y<=1-d and x>=d^2, set t=sqrt(x). The concave lower quadratic
  fJ+2eta*t-(a+2eta)*t^2 is positive at both ends
  t=d,sqrt(11/12). Its first value exceeds the preceding zero
  by eta*d*(1-d); its second rigorous lower value is
  0.00086511955532610607636... .
- If y>=1-d, then x<=d^2. At rho>=R, (JF4) is at least
  fJ-a*d^2+Anew*R=0.00032555350187764905032...>0.
- If y>=1-d and rho<=R, replace only the original true old49
  direction40 margin using197. With its unchanged positive weight
  w40, the complete signed lower comparison is at least
  fJ-a*d^2+w40*reserve_J=0.00031409099508109431347...>0.

The last case uses197's four shallow errors, two complete pure-axis
tails and zero additional mixed-family error on the same actual
capacity budget. Its whole-rectangle reserve is reconstructed
before use. It replaces196's older reserve; it is not added as a
second credit to a margin that has already been improved.

These cases cover every original source. The zero in the first
case is a value of this sufficient relaxation, not an assertion
that any actual family attains(JF1).

## 3. Complete consumer

The [helper](../../frontier/j-geometry/j_family_global_comparison.py) and
[certificate](../../certificates/source_norms/j-geometry/j_family_global_comparison.json)
retain the exact paired target choice, fresh original allocation
checks, full197 reserve and both complete local comparisons. They
check all52 original local indices, positive complete denominators
and remaining actual-mass coefficients, all eight original
fallback comparisons and both unchanged complete terminal errors.
Both final errors still leave positive gaps above403.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_family_global_comparison.py --check
```

The formulas prove arbitrary independent-label and infinite-tail
coverage through the ordinary source arguments. The rational
checks evaluate and verify these bounds; they are not a finite
substitute for the original unrestricted quantifiers.
