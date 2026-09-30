# All current query maxima can agree while the same next original splits the certificate

The full vector of current marked-query maxima is not a state closed under
actual future deletions. The example below has two actual sources with
identical retention, complete old315 marginals, every conditional outside
marginal involving at most TWO coordinates, and all320 nonzero-coefficient
current query maxima. Both current higher-core margins are positive.
The SAME next distinct-modulus original makes one margin negative while
leaving the other positive.

The sources come from one explicitly declared weighted prior and literal
odd numerical originals. They are not Haar conditioning on the entire
shallow survivor set. Both actual families still admit a positive common
background source, including after the next deletion. This is a failure
of the proposed boundary summary, not an odd covering or an obstruction
to every source law. All arguments and calculations are ordinary finite
mathematics, not Lean verification.

## 1. One prior and two actual24-original families

Use the eleven old originals

    (3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
    (21,0),(35,0),(63,0),(105,0),(315,0).

Their old315 survivor set X has102 points and contains2 and11. These two
points agree modulo9 and differ modulo5 and7. Add the pure original
0 mod p at p=11,13,17,19,23.

On(x,y11,y13,y17), the COMMON prior assigns:

- weight1 to every x in X and outside roots
  y11 in{3,...,10}, y13 in{3,...,12}, y17 in{3,...,16};
- weight791 to all16 corner cells x in{2,11}, y11,y13,y17 in{1,2}.

The background has114240 cells. The total raw prior mass is126896.
Extend by independent UNIFORM live-root probability laws at19 and23,
so these two extra axes do not change the displayed raw masses. Their
complete free-query multiplier is

    (1+1/18)(1+1/22)=437/396.

At each corner row, family A removes the four odd-parity triples and
family B removes the four even-parity triples, with parity computed from
(y11-1)+(y13-1)+(y17-1). The four deletion labels at row2 have old cofactors
5,7,15,21, and those at row11 have cofactors35,45,63,105. Every chosen
cofactor distinguishes2 from11, so a deletion targets only its intended
corner row on the prior. All background roots are at least3 and survive.

The eight actual CRT originals are:

|numerical modulus|A forbidden phase|B forbidden phase|
|---:|---:|---:|
|12155|3147|2432|
|17017|13652|4643|
|36465|12377|25247|
|51051|2|9011|
|85085|37181|12156|
|109395|108461|11936|
|153153|143651|134642|
|255255|240671|45476|

Together with the old and pure originals, each family has24 DISTINCT odd
nonunit moduli. Every phase is fixed once globally. The three-axis carrier
is765765; including19 and23 gives334639305.

Both actual sources retain the whole background and eight corner cells,
with total raw mass120568. No independently favorable conditional sources
are combined.

## 2. Equal pairwise relations and equal current maxima

Uniform even and odd parity on three binary coordinates have the same
marginals on every proper subset. Thus at EACH old point, the two actual
sources have the same unnormalized outside marginals of order0,1,2.
The exact consumer compares37266 retained marginal entries; equality of
the normalized conditional marginals follows because the old row masses
also agree. Independent live19/23 factors preserve this equality for all
single-coordinate and pairwise marginals among the full five axes.

Moreover, switching roots1 and2 in one of the first three axes exchanges
the two surviving parity patterns while fixing the background. This is a
bijection of the source supports preserving the old coordinate and source
weights, and it permutes each free-query phase dictionary. Consequently
ALL free-phase query maxima agree. The consumer explicitly checks all80
base nonzero-kappa slots; their four19/23 extensions give all320 slots.
The phase attaining a maximum is not part of this summary.

Using [Report752](752-joint-deletion-credit-distinguishes-equal-marginal-sources.md)'s homogeneous coefficient

    R(F)=sum_(d,J) kappa(d) max_(a,t)F(C_(d,J,a,t)),
    J(F)=mass(F)-R(F),

both actual sources therefore have

    R(F)=1145418515/9504,
    J(F)=459757/9504>0.                               (B1)

The same current scalar margin AND its entire320-entry cap vector have
been retained. Adding only those current maxima to pairwise marginals
does not distinguish the two sources.

## 3. One actual continuation with opposite signs

Now add the SAME original to both families:

    352496 mod765765.

Its CRT conditions are x=11 mod315 and y11=y13=y17=1. The modulus has not
occurred before, so the continuation preserves numerical distinctness.
It removes one surviving corner cell from A, of raw mass791, and removes
no mass from B.

For A, the only changed base nonzero-kappa query maximum is d=9 with no
queried outside coordinate:

    33208 -> 32417.

Every other base maximum can use an unchanged maximizing phase. Extending
this changed slot by19 and23 produces the four affected five-axis slots.
The total higher-core credit is

    (1/2)*791*(437/396)=345667/792.

Therefore the exact common-source update is

    J(A after)=459757/9504-791+345667/792
              =-2909903/9504<0,
    J(B after)=459757/9504>0.                         (B2)

The phases of the new original are held fixed. Transporting the new phase
along with a source permutation would be a different operation and would
not test this boundary's promised response to the specified continuation.

This pair proves that the map consisting of current retention, complete
old marginal, all conditional pairwise marginals, and all current marked
maxima cannot have a deterministic correct update for every actual new
original. It merges two real states that require different successor
margins and different survival records.

## 4. The missing interface is phase-indexed intersection data

For each query slot, Report752 identifies the needed correction as

    credit_l=min_c [M_l-F(C_l,c)+G(C_l,c)].

Keeping M_l alone discards both which phases are near-maximal and where
the actual deletion lies. In this example even the deleted mass itself
is not determined by the pairwise coordinate tables: it queries a triple
relation at the fixed old row11. The actual full triple table would
separate the sources before the continuation.

For this one future original, its mass and its intersections with the
competitive query phases suffice. For a larger declared continuation
family, retain the corresponding union scopes or certified intersection
bounds, as in [Report750](750-marked-boundaries-and-joint-deletion-updates.md)'s exact joint update. A current numerical score is
not a substitute for the relations needed by its own next update.

The COMMON background alone has positive raw margin2912955/64 and survives
both current families and the new original. Hence the negative value in
(B2) does not show failure of every source on A's actual survivor set.
This distinction is necessary: the example diagnoses information lost by
the summary, not the arithmetic noncoverage problem itself.

## 5. Exact verification

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullcap_continuation.py)
reconstructs every prior cell by literal CRT, applies all actual deletion
phases, compares all conditional marginal tables and current query maxima,
and recomputes the same new original's mass, cap changes and exact
slack-plus-intersection credits. It checks the common surviving positive
background before and after the next original as well.

Run from the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullcap_continuation.py
```

The [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_fullcap_continuation.json)
is compared with a complete replay. An independent calculation reconstructs
the background analytically, using its disjoint outside alphabet, and
filters the16 CRT corner cells using the literal originals. It reproduces
all320 current query maxima, the pairwise marginal equality, both successor
margins, and the exact next-original losses. No numerical solver, phase
optimization premise, or Lean verification is used.

The contrast with [Report753](753-six-shape-actual-source-joint-query-catalogue.md)
is the declared operation: free phase maximization permits source-root
permutation; a specified new original keeps its physical phase fixed.
A summary sufficient for the first task can omit precisely the relation
needed for the second task's next update.
