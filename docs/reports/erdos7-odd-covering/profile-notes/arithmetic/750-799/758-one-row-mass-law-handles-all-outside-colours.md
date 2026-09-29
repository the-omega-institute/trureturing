# One old-row mass law handles all outside colours and multioutside phases

The [full-survivor source repair](757-a-full-shallow-uniform-obstruction-admits-a-fixed-row-law.md)
keeps one complete383-slot phase family fixed. Here a source certificate
keeps only eleven core phases and fifty-five singleton OLD phases fixed.
It allows every singleton outside-root choice and every shallow
multioutside phase choice, simultaneously. Its prescribed old-row masses
stay fixed; the actual conditional law is rebuilt on the surviving roots.

The literal certificate below gives Haar survivor density greater than
1/2320 for every such family, arbitrary ordered outside primes above7,
and arbitrary finite core3/5/7 heights. Outside exponents remain at most1.
The claim for every possible core and singleton old-phase dictionary,
and unrestricted Erdős #7, remain open. These are ordinary mathematical
proofs and exact finite computations, not new Lean verification.

## A sufficient interface with no outside-root colours

Put D={d:d|315}, and fix at most one original at each nonunit core label
d in D. Choose a complete eleven-slot dictionary containing those actual
phases, adding declared auxiliary restrictions only at absent labels.
Let X be its full survivor set in Z/315. Such padding produces a smaller
supported source; it does not replace any present original's phase.

Let p1<...<p5 be outside primes above7, and P=(11,13,17,19,23). At every
outside axis exclude the actual pure forbidden root, or one auxiliary
root if the pure original is absent. For every nonunit d|315 fix the old
phase a_(j,d) of the singleton original p_j*d. An absent singleton slot
may again receive a declared auxiliary restriction. Every outside root
of those originals is arbitrary, including the already forbidden pure
root. All labels and phases refer to ONE actual configuration.

For x in X define

    h_j(x)=#{d|315,d>1:x=a_(j,d) mod d},
    ell_j(x)=P_j-1-h_j(x).

The count h retains numerical labels, including overlaps. If A_j(x) is
the actual singleton-surviving root set and r_j(x)=|A_j(x)|, then

    r_j(x)>=p_j-1-h_j(x)>=ell_j(x).                 (1)

Each matching label deletes at most one additional live root. Collisions
and roots already excluded by the pure original only improve (1).

Choose nonnegative row MASSES u_x, not all zero, with u_x=0 if any
ell_j(x)<=0. On every positive row define the actual source F0 by

    F0(x,y1,...,y5)=u_x/product_j r_j(x),
    provided y_j belongs to A_j(x) for every j.     (2)

Other cells have mass zero, including every zero-mass row. All
denominators in (2) are positive by (1). This is one actual conditional
product law, supported on the chosen core and singleton survivors.
Its total mass is sum_x u_x, and its old marginal is exactly u.

For each numerical query slot (d,J), d|315, J subset{1,...,5}, define

    C_(d,J)(u)=max_(a mod d)
       sum_(x in X,x=a mod d,u_x>0)
            u_x/product_(j in J)ell_j(x).          (3)

An empty product is1. An actual query with outside roots t_J has mass

    sum_(x=a mod d)u_x product_(j in J)
              [1_(t_j in A_j(x))/r_j(x)]
       <=C_(d,J)(u).                              (4)

This upper bound uses the same u in every slot. It discards membership
indicators by replacing them with1; it does not assert jointly attainable
maximizers or introduce fictitious actual root sets. In particular (4)
is valid at11 even if no root survives over all old rows.

## Complete payment for the remaining originals

For d|315 put

    Sat(d)={3:9|d} union {5:5|d} union {7:7|d},
    kappa(d)=product_(p in Sat(d))p/(p-1)-1.

These are the complete saturated-core geometric-tail coefficients used
in the [arbitrary-core-height bridge](754-last-three-shallow-supports-with-arbitrary-core-heights.md).
Define

    M(u)=sum_x u_x
      -sum_(d|315,J subset{1,...,5})
          [kappa(d)+1_(|J|>=2)] C_(d,J)(u).        (5)

There are372 nonzero slots:320 with nonzero kappa, plus52 additional
multioutside slots having kappa=0. The indicator accounts for one
possible actual original at each shallow multioutside numerical label.
All their old phases and outside phases are arbitrary and globally fixed.
Distinctness of the original numerical moduli is what permits this count.

Restrict F0 by those shallow multioutside originals to obtain F. By the
union bound and (4), its lost mass is at most

    sum_(d,J:|J|>=2) C_(d,J)(u).

Restriction cannot increase any query-cylinder mass. Consequently

    mass(F)-sum_(d,J)kappa(d) max_phase F(C_(d,J,phase))
       >=M(u).                                    (6)

No conditional product structure of F is assumed. Both its mass and
its query debits are estimated from the single source (2).

Extend F uniformly through all extra core3/5/7 digits of a given finite
carrier. An original with higher core exponents reduces to one saturated
shallow query and pays an additional inverse-prime-power factor.
Summing the factors over all nonempty excess vectors gives kappa(d).
This includes every higher-core numerical label and every outside
subset, with no finite tail omitted. Thus M(u)>0 gives positive survivor
mass after every finite such extension. It gives a sufficient condition;
M(u)<=0 alone is not a covering certificate or actual-source obstruction.

## Haar conversion and larger primes use the same source

Let Q0=315*product_j P_j and

    D0=max_(u_x>0) u_x/product_j ell_j(x).

At the minimum primes, F0 has density at most Q0*D0 relative to normalized
Haar. The same is true after restriction and uniform extension through
extra core digits. Equation (6) therefore gives

    Haar(actual final survivors)>=M(u)/(Q0*D0).    (7)

For larger ordered primes p_j>=P_j use the same u and rebuild (2) on
the actual roots. Every guaranteed denominator increases, so the
cylinder upper bounds decrease and the margin cannot get worse. Also

    315*product_j p_j * max_x u_x/product_j r_j(x)
      <=315*max_x u_x product_j p_j/[p_j-1-h_j(x)]
      <=Q0*D0.                                    (8)

For each fixed h>=0 the ratio p/(p-1-h) decreases on its positive
denominator domain. This proves (8) row by row before taking the maximum.
Thus (7) is uniform for larger ordered outside primes as well; increasing
the carrier alone would not establish the needed density direction.

## A literal certificate and a failed fixed rule on the same dictionary

The [literal input](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_allcolors_row_envelope_input.json)
contains only eleven core originals, fifty-five singleton old phases,
and75 integer row-mass pairs. Its core phases have exactly75 surviving
rows. The chosen masses total10005, are at most252, and are positive on65
rows. The minimum lower fibre counts over all75 rows are(3,5,8,11,16).
No outside-root assignment or multioutside phase is supplied or needed.

The complete372-slot sum has normalized cost

    5530630489432951012717/5640168003796085760000 <1.

Its margin and Haar bound are exactly

    M=109537514363134747283/563734932913152000,
    Haar>=109537514363134747283/254050670860642656000000
         >1/2320.

All present core and singleton old phases must match the literal input.
Slots may be absent, since the declared complete source then imposes
additional restrictions. Any singleton outside roots, any subset of the
312 shallow multioutside labels with arbitrary phases, and arbitrary
finite higher-core extensions are admitted by the same lower bound.

A previously useful fixed old45 rule repeats the masses

    (6,2,6,6,5,6,6,6,6,6,6,6,6,6,2,6)

at the increasing old45 rows

    (2,7,8,14,16,17,19,23,28,29,32,34,37,38,43,44).

That rule's envelope cost on THIS SAME old dictionary is

    10508340548778384757/9848780886776832000 >1.

This refutes universal success of that fixed rule with this envelope.
It does not exclude other row masses: the certificate above succeeds.
Nor does a negative lower estimate determine the actual reserve of a
particular outside-colour assignment. The three questions remain distinct:
success of a fixed rule, feasibility of (5) over all u, and existence of
some actual final supported law outside this sufficient construction.

## Exact finite verification and remaining quantifiers

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_allcolors_row_envelope.py)
reconstructs the actual core rows, all55 old-label incidences, denominator
guards, all372 rational maxima, complete budget, and Haar bound from the
pinned input. It also recomputes the fixed-rule failure. It uses no LP
solver, previous cap values, final survivor tensor, or search history.
The [retained exact result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_allcolors_row_envelope.json)
must equal a fresh complete recomputation. An independent calculation
uses integer common denominators and all residue bins for every slot;
all372 maxima, the margin, Haar bound and failed-rule cost agree.

The general sufficient theorem (1)--(8) handles every old dictionary
for which its hypotheses and positive margin are established. This
literal certificate establishes one such dictionary. The unresolved
step is to construct a suitable u for EVERY actual core configuration
and EVERY old singleton phase dictionary, or to identify an actual
dictionary refuting this sufficient method. More than five outside
prime axes and higher outside powers remain further requirements of
unrestricted Erdős #7.
