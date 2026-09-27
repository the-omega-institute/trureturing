[Index](../../marked_head_profile.md) · [Previous general ceiling](404-a-sharper-common-law-and-its-witness-choice-boundary.md) · [Full cap architecture](425-full-six-pair-cap-mixtures-have-an-exact-laminar-dual.md)

# Retuning the actual tree mixture gives a smaller general ceiling

Every actual source with all six pair ternary trees and a full
five-ary projection tree admits one probability whose complete
original-divisor squared load is strictly below

    C0 = 7797466329/1272826915 = 6.1261010724... .                (RT1)

The same conclusion holds for arbitrary permitted choices of the
seven actual tree witnesses in the construction below. It improves
report 404's general ceiling `309/50=6.18`. The ceiling is approached
by an existing witness family at the chosen coefficient; optimality
of that coefficient among other choices is not asserted.

This is an ordinary proof using a finite exact case split and
all-height analytic bounds, not Lean certification. The ceiling
exceeds six and does not establish the required finite comparison
`Gamma_(1,K)<=2t_K`. It gives an upper bound for the full architecture
of report 425 by constructing a particular member of it; the
probability is fixed before every independently chosen phase.

## 1. The same actual components, with a variable coefficient

Let `K>=0` and `S subset {1,2,3,4} times Z/7^K`. Assume its full
projection contains a complete five-ary tree and every row-pair
projection contains a complete ternary tree, all of depth `K` with
lowest digits read first. Choose any actual labelled uniform
five-tree law `mu` and any six actual labelled uniform pair-tree
laws `eta_rs` on this same source. Set

    beta_r=mu(row r),
    omega=sum_(r<s) (1-beta_r-beta_s) eta_rs/3,
    nu_alpha=alpha mu+(1-alpha)omega.                            (RT2)

The nonnegative pair weights sum to one. The component choice and
all weights are fixed once; they do not depend on the layout phases.
These are precisely the actual witnesses and omitted-row mixture
of reports 402 and 404. This report changes the coefficient and its
uniform estimate, without imposing any further source structure.

Write `f_j=5^-j`, `q_j=3^-j`, and `d_alpha=2(1-alpha)/3`. The
same-law caps from those reports are

    m_j=alpha f_j+(1-alpha)q_j,
    c_j(b)=alpha min(b,f_j)+d_alpha(1-b)q_j.                     (RT3)

Every pure depth-`j` prefix has mass at most `m_j`, and its
intersection with row `r` has mass at most `c_j(beta_r)`.

For a word of mixed-label rows `r_0,...,r_K`, let
`n_j=#{i<j:r_i=r_j}`. The retained row-sensitive expansion of all
original labels, including divisor one, bounds the square by

    F_K^alpha(beta,r) = sum_(j=0)^K (2j+1)m_j
      + sum_(j=0)^K [(2j+3+2n_j)c_j(beta_(r_j))
                    +2 sum_(i<j)c_j(beta_(r_i))].              (RT4)

This is the existing independent-row calculation of 402/404 with
RT3 substituted. Incompatible seven-adic prefixes only remove
intersections. An absent-row-zero mixed phase can be replaced by
an actual-row phase without decreasing the load. Thus bounding
RT4 over all four-row words and the full probability simplex
bounds every original independent layout under RT2.

For the remainder of the uniform proof, restrict

    3/5 <= alpha <= 46/73.                                     (RT5)

## 2. Constant words and late first changes, at every height

For a constant word, its row contribution is
`sum_(j=0)^N (6j+3)c_j(b)`. It is concave in `b`. At `b=1/5`,
its right derivative, for `N>=2`, is

    3alpha-2(1-alpha)S_N(1/3)
      <= (73alpha-46)/9 <= 0,
    S_N(z)=sum_(j=0)^N (2j+1)z^j.                              (RT6)

The left derivative is larger by `9alpha`; since `S_N(1/3)<=3`,
it is at least `18alpha-6>=24/5>0`. Therefore `b=1/5` is a global
maximizer. Its full value is

    A_N(alpha)=4alpha S_N(1/5)
               +(13/5)(1-alpha)S_N(1/3)-(12/5)alpha,
    A_N(alpha)<A_infty(alpha)=39/5-(27/10)alpha.                 (RT7)

All omitted summands are positive, so the finite inequality is
strict. At `N=0,1`, direct maximization instead gives
`1+3alpha` and `2+22alpha/5`; both are less than five throughout
RT5, below every ceiling used below.

Now suppose the first row change occurs at depth `h>=3`. For
positive depth define `u_j=max_b c_j(b)` and `v_j=c_j(1/5)`.
As in 404, the prefix through `h-1` is bounded by its constant-word
optimum, the first change loses `2h` in the total row coefficient,
and all subsequent depths lose at least two. The resulting excess
over `A_K(alpha)` is at most

    D_(h,K)^alpha=(6h+3)(u_h-v_h)-2h u_h
                   +sum_(j=h+1)^K [(6j+3)(u_j-v_j)-2u_j].       (RT8)

Put `a=5(1-alpha)/3`. The old coefficient `2/5` caps from report
402 obey, at every positive depth,

    u_j^alpha=a u_j^old+(1-a)f_j,
    v_j^alpha=a v_j^old+(1-a)f_j.

Consequently

    D_(h,K)^alpha=a D_(h,K)^old
        -(1-a)[2h5^-h+2sum_(j=h+1)^K 5^-j] < 0.               (RT9)

Here `0<a<1`, and report 402, RA4--RA7, proves
`D_(h,K)^old<0` for every `K>=h>=3`. This reuses that all-height
inequality, rather than replacing it by tests of selected heights.
Every late-first-change word is therefore below RT7.

## 3. A complete finite split for early changes, with an infinite tail

For words whose first change is at depth one or two, retain all
depths zero through five. Normalize row names by order of first
appearance, starting with zero and using at most four names. There
are exactly 172 such length-six prefixes. Each actual prefix is a
row permutation of one of them; simultaneous row permutation of
`beta` preserves its full simplex domain.

For a prefix, let `w_(r,j)` be the coefficient of `c_j(beta_r)`
in RT4 and write `g_r(b)=sum_(j=0)^5 w_(r,j)c_j(b)`. Its left
and right slopes are

    ell_r(b)=alpha sum_(j:b<=f_j) w_(r,j)
              -d_alpha sum_j w_(r,j)q_j,
    dr_r(b)=alpha sum_(j:b<f_j) w_(r,j)
              -d_alpha sum_j w_(r,j)q_j.                       (RT10)

A common slope `s` with `dr_r(beta_r)<=s<=ell_r(beta_r)` proves
global optimality over the simplex. At `beta_r=0` only the lower
inequality is required; at one only the upper is required.
Concavity gives `g_r(x)<=g_r(beta_r)+s(x-beta_r)`, and the common
linear term cancels after summing the coordinates.

The exact checker constructs and verifies this certificate for
every one of the 172 prefixes at each endpoint of RT5. The endpoint
maxima are:

| Coefficient | Maximum through depth five | Attaining prefix | `beta` |
| --- | ---: | --- | --- |
| `3/5` | `69206569/11390625` | `011111` | `(4/5,1/5,0,0)` |
| `46/73` | `37571354/6159375` | `011111` | `(4/5,1/5,0,0)` |

The finite optimizer only supplies candidate masses. Each candidate
is independently checked by RT10 against the entire real simplex.
The prefix generator exhausts restricted-growth words with at most
four names and first change at one or two; this is a finite case
split, with no claim that length six exhausts infinite row words.

The remaining depths are bounded analytically. Every nonconstant
word has total row coefficient at most `6j+1`. Throughout RT5,

    u_j=alpha f_j+d_alpha(1-f_j)q_j.

Thus the infinite tail after depth five is

    T5(alpha)=sum_(j=6)^infty [(2j+1)m_j+(6j+1)u_j]
      =alpha sum_(j=6)^infty (8j+2)5^-j
       +(1-alpha)sum_(j=6)^infty
            [(6j+5/3)3^-j-(4j+2/3)15^-j].                   (RT11)

These are geometric and differentiated geometric sums; all original
tail summands are positive. Adding RT11 to the endpoint maxima
gives the same affine line at both endpoints:

    L5(alpha)=211322621/37209375
                    +(26817379/37209375)alpha.                 (RT12)

For a fixed prefix and `beta`, RT4 plus RT11 is affine in `alpha`.
Its maximum over all prefixes and `beta` is convex in `alpha`.
The two endpoint bounds therefore imply the upper bound RT12 on
the entire interval RT5. This interpolation uses the same
coefficient, row distribution, and components in every term.

Any finite word of height at least five omits a strictly positive
part of RT11, so its early-change profile is strictly below RT12.
A shorter early-change word can be extended through depth five;
all added terms are nonnegative, and the positive infinite tail
still makes the final bound strict. This accounts for all heights.

## 4. The resulting general bound and its precise sharpness scope

The two controlling lines meet at

    alpha0=157821008/254565383,
    A_infty(alpha0)=L5(alpha0)=C0.                              (RT13)

The interval condition RT5 holds. Constant words, late first
changes, and early first changes exhaust every row word. Sections
2--3, together with RT4, therefore prove

    for every K>=0, every admissible actual S,
    and every permitted choice of actual tree witnesses in RT2:
      max_(all complete independent original layouts)
          E_(nu_alpha0) L^2 < C0 < 309/50.                     (RT14)

The same proof gives `max(A_infty(alpha),L5(alpha))` throughout
RT5. For example, the simpler coefficient `31/50` gives the strict
general ceiling `11397469799/1860468750<613/100`. Equation RT13
minimizes the two displayed upper lines; it is not a proof that
`alpha0` minimizes the actual worst-witness or source minimax value.

For this **fixed** coefficient, however, the limiting ceiling `C0`
cannot be lowered while allowing arbitrary witnesses. Report 404's
actual sharpness family has full-tree row masses `(1/5,4/5,0,0)`
and an aligned original layout with exact expectation `A_K(alpha)`
from RT7. These actual expectations approach `A_infty(alpha0)=C0`.
The upper bound RT14 and these lower examples therefore establish
sharpness of the supremum over heights and witness choices at
`alpha0`. They do not assert equality with `C0` at finite height.

The same reused family already has, at height four,

    E_(nu_alpha0) L^2=961223193283/159103364375
       =6+6603007033/159103364375 > 6.                          (RT15)

This is an actual obstruction to claiming six for this prescribed
recipe and these witnesses. It does not rule out other cap
components, other weights, or arbitrary probabilities on that
source. In particular RT14 does not settle the full architecture's
target condition in report 425 or unrestricted Erdős #7.

## 5. Reusable exact implementation

[`retuned_tree_common_law.py`](../../frontier/cover-geometry/retuned_tree_common_law.py)
provides arbitrary exact-coefficient `profile_bound`,
`certify_profile_maximum`, `maximize_profile`, `make_law`, and
`verify_law`. It reuses report 404's row coefficients and report
402's actual tree-witness, source, and component validation.
`certified_ceiling` returns the proved all-height bound only on RT5;
constructing a law at another coefficient does not certify that bound.

The concave optimizer fills marginal-slope segments whose endpoints
are `0,5^-N,...,1`; the separate supergradient checker verifies its
output. Default controls verify all 344 endpoint certificates,
the interval/crossing identities, the constant-word derivative
inequalities, the late-change algebra, compatibility with the
existing `3/5` profiles, and the actual above-six boundary RT15.
Malformed or nonoptimal inputs are rejected under `-O` as well.

Run from the repository root:

    python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/retuned_tree_common_law.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/retuned_tree_common_law.py

The `--stdin` interface accepts an exact JSON object with `height`,
`source`, and optional `coefficient`; rational coefficients are
integer values or rational strings, never floating-point numbers.
It returns one constructed actual probability and the checks
appropriate to that coefficient. No files are written.

This is a `repo-derived` refinement of the existing 402/404 proof
and actual construction, using standard concavity, supporting
slopes, and geometric sums. It introduces no new source assumption
or claim of a new minimax principle. The finite exact certificates
support the stated analytic case split; they do not replace its
all-height argument.
