[Index](../../marked_head_profile.md) · [Previous complete H4 source](288-retaining375-strengthens-the-complete-j-survival-hinge.md)

# Joint positive175/189 strengthens the complete J survival hinge

On both entire actual saturated J faces, the original load `A` on the
actual survivor measure `mu` satisfies

    integral (A-4)_+ dmu
      <= 118025942856670081/617400000000000000
       = 0.19116608820322332523485584710074505993... .

The previous complete375 bound was
`767945288466086119/3969000000000000000`. The exact improvement is

    16112397678112297/6945750000000000000.

The improvement uses the two original positive-seven labels `175=25*7`
and `189=27*7`. Their old-coordinate parent events have independent
residue profiles. They refine the actual raw state; no independence of
events or converse realization of the linear relaxation is assumed.

## Exact conditional cap on the refined raw atoms

Keep the eight old labels `25,27,75,81,135,125,225,375` and all source
constraints of 288. On each of its raw atoms let `v` be the old load,
`m` the original number of first-depth extra events, and `e` the number
of second-depth extras. The original full conditional seven kernel is,
with `q=(4-v)_+`,

    g(v,m,e) = (6/35)*(1+m-q)_+
             + (6/245)*(1+e-(q-(1+m))_+)_+
             + 1/(5*7^(2+(q-(1+m)-(1+e))_+)).

This is the sum of the ordered conditional cap list after deleting its
first `q` entries: the first-depth caps, second-depth caps, and complete
infinite geometric suffix. This upper-bound construction does not assume
probabilistic independence. The same conditional cap argument applies
after appending the two retained first-depth events.

Write `J25,J27` for their old-coordinate parent indicators. Split each
original raw atom of mass `x` into the three nonempty membership masses
`u10,u01,u11`, with nonnegative values and sum at most `x`. The complement
is `x-u10-u01-u11`. On a state `s`, write `n(s)` for its one or two set
bits. Exact partition of the new conditional cap expression gives

    g(v,m,e)*x
      + sum_(s=10,01,11) [g(v,m+n(s),e)-g(v,m,e)]*u_s.

These are raw masses. The survivor states and their exact `(v-4)_+`
contribution remain unchanged. There is no duplicate survivor copy for
each new raw membership state.

Every added coefficient is nonnegative and at most `n(s)*6/35`. For
`v>=4` it is exactly `n(s)*6/35`; for `v=1,2,3` the finite transitions
follow directly from the displayed formula. The new first-extra count
can reach six. The formula and complete geometric suffix remain valid
at that count; no old table restricted to four extras is substituted.

## Independent profiles and original CRT constraints

Each of the two new parent profiles has five coordinates, nonnegative
and summing to one. In the original rectangle `(c,s)`, the cofactor25
marginal uses its own slot profile with cap `desc(c,s)*q_s/25`; the
cofactor27 marginal uses its own row profile with cap `pre(c,s)*r_c/27`.
The two profile vectors are independent choices. Their complete global
raw caps are respectively `1/50` and `1/36`.

For each fresh cofactor `a` and each old retained label `d`, preserve the
raw CRT bound `1/lcm(a,d)`. The joint fresh-parent raw cap is `1/675`.
Only these original-coordinate bounds are imposed; no matching of the
new residue choices with the old25 or old27 residue is assumed.

The extension preserves all 12941 original375 variables, 30454 original
inequalities, and 20 equalities. It adds 19200 nonempty joint raw-state
variables and ten independent profile coordinates, giving 32151
variables, 56133 inequalities, and 22 equalities. Its exact matrix hash
is `4da5961945a50079d14a49fc0017409abeba79624086971f2c0747d63e8e494d`.

Every original source, survivor, marked-deletion, common late-interval,
and occupied/complement density constraint remains. The new membership
variables are constrained separately inside each genuine original raw
atom; they are not three overlapping copies of the same mass.

## Remove only the two designated assigned tail caps

The previous positive-seven remainder is `13/490`. The old assigned
payments for the two newly retained labels are exactly

    (6/35)*(1/50) = 3/875,
    (6/35)*(1/36) = 1/210.

Remove these once because their full conditional contribution is now
in the refined kernel. The remaining positive-seven tail is

    13/490 - 3/875 - 1/210 = 337/18375.

The entire old-label tail remains `5071/405000`. Consequently every
branch has exactly the same full constant

    5071/405000 + 337/18375 = 612439/19845000.

All other exponent and cofactor heights remain in their original
complete nonnegative tails. There is no finite-height approximation.

## Complete original-domain partition

The fixed threshold is the exact upper on the same original controller
from 288, with both new profile simplexes present. The unchanged complete
old prefix method covers every original independent two/four/six/seven/
eight-projection choice. At this threshold its remaining list has 970
original leaves. Individually rechecking all 104 available original375
branch objectives and duals closes 54 of them. The remaining 916 leaves
each receive a certificate for their own complete joint-source objective.

The exact coverage identity is

    3124999030 + 54 + 916 = 3125000000.

The number counts the original eight-projection domain. Every one of
its linear programs also contains both complete independent new parent
profile simplexes, including all their possible residue choices.
The new profiles have not been fixed to two favorable residues.

An old375 dual is reused only for the exact same full original branch
tuple, after rebuilding and checking that branch's own objective and
complete constant. Each of the 916 residual leaves adopts the minimum
of its new complete bound and its own strongest valid old bound. The
final full upper is the maximum of the fixed controller threshold and
all 916 adopted bounds. That maximum equals the value stated above.
It is a certificate maximum, not an actual-source attainment claim.

The [checker](../../frontier/j-source/j_face_joint_positive175189_survival_heads.py)
and [certificate](../../certificates/source_norms/j-source/j_face_joint_positive175189_survival_heads.json)
reconstruct the unchanged source, the full prefix partition, every
original375 reuse, every new objective, and all complete tail constants.
The 916 distinct joint-source duals check 29450316 exact rational
columns. The 104 original375 reuses add 1345864 exact column checks.
Canonical replay uses the existing rational codec and standard-library
exact arithmetic; no optimizer or scratch-directory input is needed:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-source/j_face_joint_positive175189_survival_heads.py --check
```

This is a complete H4/AP13 source inequality on the two entire saturated
actual J faces. A complete 52-cost comparison is a separate consumer.
Actual-family attainment, extension away from these faces, a global join,
Lean verification, and unrestricted Erdős7 are not conclusions of this
source result.
