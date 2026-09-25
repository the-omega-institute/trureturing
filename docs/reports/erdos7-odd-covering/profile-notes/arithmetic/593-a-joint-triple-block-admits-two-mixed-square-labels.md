# A joint triple block admits two mixed-square labels

Let P={3,5,7,11,13,17,19}. In the nine-prime family of
[Report591](591-two-centre-star-boundary-closes-complete-height-three-tails.md),
also allow the two numerical labels

    147=3*7^2, 245=5*7^2

with arbitrary globally fixed residues. Thus all pure powers, all
squarefree mixed labels, all mixed labels with some exponent at least 3,
and these two additional labels are allowed on P; every original touching
23 or 29 is unrestricted. For any finite collection of pairwise distinct
such numerical moduli, the complete survivor satisfies

    H(U)>=304081382950091/333864960000000000>1/1100.     (JB1)

There is no cutoff on any original or query height. The two added square
labels do not consume a separate extra-weight allowance. Their joint
geometry is retained inside the boundary, together with the already
allowed label 105=3*5*7. This is an ordinary proof with a finite exact
arithmetic certificate, not a new Lean result or unrestricted Erdős #7.

The same statement transports to any nine ordered odd primes, with
the added labels r_1*r_3^2 and r_2*r_3^2 and the corresponding exponent
restriction on the first seven primes. The existing digit-injection
argument in [Report592, Section5](592-joint-second-moment-extends-cubic-tails-to-ten-primes.md)
preserves these exponent vectors and the density lower bound.

## 1. Keep three constraints in one actual prefix block

Use precisely Report591's product source rho: complete actual pure
survivors, root-balanced coordinates at p>=5, and ternary root masses
t,1-t in [1/3,2/3]. Its density remains at most D=3458/405 times Haar.
Keep the eleven old auxiliary stars J, including the central 15 cell.

Move the 105 original out of the remaining squarefree union estimate and
into the joint block. If it is absent or rho-null, fill that slot with
one fixed auxiliary cylinder. All positive-mass actual originals keep
their actual residues. Incorporate the actual 147 and 245 cylinders
when present; an absent one makes no deletion.
Absent or rho-null square slots are represented by zero deletion and
dummy child identities distinct from active children in the relaxed
endpoint model. This does not assert that their actual 7-cylinders
have zero mass, or change an active original's phase.

At prime 7 every retained first root has rho_7 mass 1/6, and every
depth-two cylinder has mass at most 1/35. Let the two added cylinders
have parents u_3,u_5, child identities v_3,v_5, and masses alpha,beta.
They are enabled respectively on one ternary row and one quinary column.
If they have the same parent and child, they are the same 7-cylinder,
so alpha=beta. Otherwise their 7-cylinders are disjoint.

For each central cell (i,j), let R_ij be the union of the old 21/35
forbidden 7-roots enabled on that cell, together with the 105 root when
its central cell is (i,j). Put

    h_3=1_(147 enabled on cell and u_3 not in R_ij),
    h_5=1_(245 enabled on cell and u_5 not in R_ij).

The exact remaining 7-coordinate mass is

    f_7(i,j)=1-|R_ij|/6-alpha h_3-beta h_5
                 +alpha h_3 h_5 1_(same parent and child). (JB2)

This counts whole-root deletions and child-cylinder intersections on one
actual rho_7 law. It does not replace the two child masses by independent
probability laws. Put the central cell (0,0) equal to zero, as before.

## 2. The same six screens, with a more informative factor

For T subset {7,11,13,17,19}, define the central table as follows.
If 7 is outside T, retain f_7; if 7 is in T, drop the whole 7-block
factor. Multiply by the original star-avoidance factors at each
q in {11,13,17,19} outside T, and by the central 15 mask.

Apply TC8's six averaging/maximum rules to this table. An original or
query whose support contains 7 is still bounded using its original
rho_7 cylinder cap and by dropping the whole conditional 7-block.
For support not containing 7, integrating the coordinate gives exactly
JB2. These are upper bounds on the same actual source, before any
query maximization. Dropping constraints never changes the source itself.

Let J_new denote the full augmented joint block and let U_P be the
complete actual P-survivor. Define

    eta=rho restricted to U_P intersect J_new^c.

Its mass is bounded below by the exact block mass minus the remaining
original charges. The remaining TC9--TC10 geometric series are unchanged.
Only the squarefree 105 charge is removed, since that original now belongs
to J_new. Its old coefficient was 1/24 times E_{ {7} }.
The complete query sum keeps EVERY label, including 105,147 and245,
whether occupied by an original or unused. Thus, for G=566/49,

    G eta(1)-R_P(eta)>=G a_new-L_new*G-Q_new.           (JB3)

In the 192-row encoding, the combined coefficient at index 129 decreases
by G/24. All remaining coefficients are nonnegative. No query coefficient
is removed, and neither new square label is charged twice.

## 3. Why finitely many mass endpoints and equality types suffice

Fix the positions and parent/child equality relations. When the two
children are distinct, enlarge the possible mass pairs to
[0,1/35]^2; when they coincide, use the single interval [0,1/35].
This is a relaxation of the actual pure-source constraints, not an
assertion that all endpoint combinations are jointly realizable.

For each fixed value of the other parameters, JB2 is affine in one
child mass. The block mass is affine, and every screen is affine or
a maximum of affine functions. Consequently the right side of JB3
is separately concave in the child masses and in t. Moving these
coordinates to endpoints in turn can only decrease its minimum.
It suffices to check t=1/3 or2/3 and child masses 0 or1/35, with the
same mass used for coincident children. Joint concavity is not assumed.

An old 7-star layout has a row, a quinary column, and a bit saying
whether its two parents coincide. Permute the three nonzero quinary
columns to put that column at either 0 or1; the other four primes'
columns are still enumerated freely. There are eight resulting old
7-layout types. The two square parents require at most two additional
root names; the 105 root requires at most one more. At most five
different retained roots occur, within the six available roots.
All parent equalities and the possible equality of the two children
are enumerated explicitly.

At an endpoint, 210 f_7(i,j) is an integer: a full root costs 35 and
a maximal child costs 6. After setting the central cell to zero,
equal seven-entry factor vectors give identical screens in JB3.
Deduplicating only these vectors leaves, for the eight types,

    374,347,416,320,347,277,410,311

vectors, totaling 2802. This equivalence is specific to the sufficient
estimate: it does not claim to preserve complete 7-query behavior,
since queries containing 7 deliberately drop that block.

The other four primes have 16^4 layouts. Including the two ternary
endpoints gives exactly

    2802*16^4*2=367263744

cases. This finite enumeration covers arbitrary original heights through
the already summed geometric coefficients, not by truncating them.

## 4. An exact lower certificate with outward rounding

Scale all rational combined coefficients by 10^9 and round them UP;
round G DOWN at the same scale. Every screen and block mass is
nonnegative, so the resulting gate is a lower bound for JB3.
The common screen denominator is

    12*210*10*12*16*18=87091200.

The full integer scan gives the uniform lower bound

    delta_low=8514278722602548/87091200000000000
             =304081382950091/3110400000000000>0.      (JB4)

The bound on every signed accumulation is
2278969786717747200<2^63-1. No floating-point comparison decides
positivity or selects the certified minimum.

The minimizing record has other-prime code17476, old 7-block type2,
factor-vector index94 and t=2/3. Direct rational reconstruction of
the unrounded expression there gives

    1094562606487082737/11196100999347264000
       >delta_low.

The conclusion uses the lower bound from the complete scan, not just
this witness. Applying the existing raw 23/29 continuation on this eta
gives Haar density at least

    49 delta_low/(616D)
       =304081382950091/333864960000000000>1/1100,

as claimed in JB1. Arbitrary originals touching either new prime,
including pure powers and all old-coordinate heights, remain included.

## 5. Evidence and scope of the next step

The [producer](../../frontier/cover-geometry/joint_square_105_profile.py)
generates all equality types and endpoint
vectors from the definitions above, builds the outward-rounded
coefficient input, runs the complete
[integer engine](../../frontier/cover-geometry/joint_square_105_scan.cpp),
and reconstructs the minimizing witness by exact fractions. Its
[data](../../frontier/cover-geometry/joint_square_105_profile.json) retain
the source fingerprints, coverage counts, integer bound and extrema.
The original first-root source is unchanged.

The producer's 15 checks pass. Independent atom-by-atom generation gives
the same 2802 vectors, and a separate full integer scan gives the same
minimum. The proof of the endpoint reduction and the complete geometric
series remains the mathematical argument in Sections2--3.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_square_105_profile.py

This result uses joint deletion to improve the boundary. It does not
assume that pure-power loss forces spare capacity in a deep query:
two square cylinders and a different uncut child can simultaneously
approach the depth-two cap under one actual pure-source law.

The result also cannot simply be combined with Report592's ten-prime
statement. A separate configuration has full star code419682, the same
7-block type2/vector94, and t=2/3. There the second-moment envelope gives

    s_0=26619658763210221/134406974782080000,
    Wbar=326571723197924737/9498026926080000,
    169s_0-Wbar=-1810821875393558417/1985087627550720000<0.

Thus that envelope does not certify the seed170 needed by the stated
three-prime continuation. This is a failure of that sufficient estimate,
not a covering or a lower bound against every survivor probability.

Arbitrary remaining mixed squares and unrestricted additional prime
support are still unresolved. The positive result identifies a useful
relation to retain next: original classes sharing the same prime-power
prefix must be combined with the squarefree constraints crossing that
prefix, while all subsequent queries are charged on the same source.

[Report594](594-five-joint-blocks-admit-ten-mixed-square-labels.md)
implements all five such joint blocks and permits ten added square labels.
Its new same-source seed-180 certificate combines that wider inventory
with continuation through31. The negative seed-170 envelope above is
retained as stated; it did not rule out another sufficient seed bound.
