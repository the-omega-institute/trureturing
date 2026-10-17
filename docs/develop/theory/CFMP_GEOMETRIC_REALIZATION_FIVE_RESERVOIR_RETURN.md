# CFMP five-reservoir exceptional return chains

Sections 1–245 refer to [the preceding paired-reservoir theory](CFMP_GEOMETRIC_REALIZATION_TWO_RESERVOIRS.md).
The section numbering continues that theory; all inherited hypotheses remain in force.

## 246. Hypotheses and precise conclusion

Retain the mixed-flat five-reservoir setting through Section 245, with
exactly four interacting owners K={tau,rho,eta,xi}, distinct transverse
labels, shared original edge labels, complete circular normal links,
and minimum original degree six. Put P={M,Z,U}. The source is
 tau=(Z,M,C,D,M,C),
and consider the remaining exceptional family
 rho=(C,M,Z,U,M,Z).
Both {M,Z,C} faces of tau pair to rho. Thus rho has two unused actual
faces {U,M,Z}. Suppose both pair to eta. We prove eta cannot be entirely
high-labelled (all six of its edge slots labelled in P).

This is a conditional exclusion of one actual double-return branch.
It does not exclude the other common-return family, a split return to
two different owners, or a double return to a non-entirely-high owner.

We use the published facts that every face containing two distinct P
labels pairs inside K, at most one owner is entirely high-labelled
(Sections 238–240), and no special edge has fixed transverse pair
contained in P. We count original edge occurrences throughout.

## 247. The two remaining eta faces must reach xi

Assume eta is entirely high-labelled. A face {U,M,Z} has three distinct
labels, so eta's transverse pair consists of two of them; one axis is
the third. Its other axis is also in P. In particular every face of eta
contains two distinct P labels and is marked. Eta has at most three
U slots: two if U is transverse, possibly one additional U axis, or at
most two if U is axial.

The two eta faces paired to rho have been used as actual occurrences.
There remain two eta faces. They cannot pair to an unused tau face:
tau's unused faces are {D,M,C}, which contain only one distinct P label.
All rho faces have already been used. If eta's remaining faces pair to
each other, every U-incident face in rho and eta is paired within these
two owners: rho's other faces {C,M,Z} contain no U and pair to tau.
The nonempty set of their U normal intervals is consequently closed,
with at most 1+3=4 original slots. A closed nonempty subset is the whole
connected normal circle of the actual U edge, contradicting degree six.
This argument also covers eta roles whose remaining faces contain no U.

All remaining eta faces are marked, so their partners belong to K.
The only remaining possibility is that both pair to xi. This conclusion
uses actual face occurrences and allows repeated axial labels in eta.

## 248. The low axis of xi closes a degree-one edge

Both incoming faces of xi have only P labels, since eta is entirely
high-labelled. One such face already forces xi's transverse pair to
consist of two distinct P labels and its incident axis to have a P
label. Xi cannot itself be entirely high-labelled by Sections 238–240.
Its other axis therefore has a label B outside P. No transverse or
first axial slot can have that label. A special B is impossible because
its fixed pair would be contained in P. Thus B is C or D and occurs
exactly once in xi, as an axis.

Every face incident to this B axis contains B and the two distinct P
transverse labels, hence is marked. Neither incoming face from eta can
be incident to B, as those faces have only P labels. Thus the two B
faces are precisely xi's two remaining face occurrences. Their partners
must belong to K. Tau has only its unmarked {D,M,C} faces unused; rho
and eta have no unused faces. Consequently the two B faces must pair
to each other. Their unique B edge slots are the two ends of xi's one
original B normal interval, so this interval is a closed component of
the actual B normal circle. Connectedness forces degree(B)=1, contrary
to minimum degree six.

This contradiction proves the claim. It covers repeated high axes,
self-pairings of distinct faces, and arbitrary global multiplicities.
No assertion that an arbitrary low-partner U face stays marked is used:
marking at the last step follows from xi's two distinct high transverse
labels. The external low-only region remains unrestricted.


## 249. Inherited setting and conclusion

Retain the mixed-flat five-reservoir hypotheses through Section 245.
Let tau=(Z,M,C,D,M,C) and rho=(C,M,Z,U,M,Z), with both tau faces
{M,Z,C} paired to rho. Suppose rho's two remaining {U,M,Z} faces both
pair to eta. Write xi for the fourth interacting owner. Use the entirely-high double-return exclusion in Sections 246–248.

We prove that, after exchanging the two unused owner names if needed,
 eta=(M,U,Z,B,U,Z),
 xi=(Z,U,B,Q,U,B),
where B and Q are each C or D. Both remaining eta faces {B,U,Z} pair
to xi. Both remaining xi faces {Q,U,B} leave the interacting core.
The actual Z edge has degree exactly six. Outside the core, no genuine
single-high transverse-U owner can also have a U axis. If Q=B, both
exit faces must meet the unique single-high transverse-U owner; if
Q differs from B, they may also meet axial-U/{C,D} owners.

This is a necessary chain with an explicit low boundary. It does not
exclude the remaining configurations or assert their realizability.
All counts below refer to original slots and actual face occurrences.

## 250. The first low axis and its forced successor

Eta is not entirely high by the prerequisite. Its incoming {U,M,Z}
face forces a pair of distinct high transverse labels and a third high
axis. Its other axis B lies outside P={M,Z,U}; it cannot be special,
since no special edge has a fixed pair contained in P. Thus B is C or D.

If eta has U as its high axis, the unique U interval in eta and rho's
unique U interval close across their two paired faces. This forces
U degree two. If eta has Z as its high axis, it has pair {U,M}; then
all Z intervals in tau, rho and eta form a closed set of 1+2+1=4 slots:
tau's two Z faces pair to rho, whose two remaining Z faces pair to eta.
These contradictions leave eta=(M,U,Z,B,U,Z).

Its remaining faces {B,U,Z} are marked. They cannot self-pair because
B is its unique axial occurrence, which would close a degree-one B
edge. They cannot meet tau's unused unmarked {D,M,C} faces or any rho
face, all of which are occupied. Consequently both pair to xi.

At {B,U,Z}, xi has one of three axial roles. If its axis is B and its
pair is {U,Z}, then a distinct other axis gives a closed B circle of
two slots with eta. If its other axis is also B, xi's remaining two
marked faces must self-pair: the other core faces are occupied or
unmarked. All B slots in eta and xi then close, at most three slots.
Both violate minimum degree six.

If xi has U axis and pair {B,Z}, its U slots number at most two and
all its U faces are marked. All U slots in K are then marked and their
number is at most rho's one plus eta's two plus xi's two, namely five.
They form a nonempty closed U circle, contradiction. The only role
left is xi=(Z,U,B,Q,U,B).

If Q is M or Z, all U faces in K are marked and the U count is 1+2+2=5,
again impossible. If Q is U, xi has three U slots and some incident
faces are unmarked; this case requires the additional budget below.
At this point Q is U, C, D, or special. No such Q is Z. All Z slots
in tau,rho,eta,xi are respectively 1,2,2,1 and all their incident faces
are already paired within that chain. This is the complete Z circle,
so its degree is exactly six.

## 251. The exit cannot close inside the core

Xi's remaining faces are {Q,U,B}. They have only one distinct P label.
They cannot match tau's unused faces, which contain M and not U; rho
and eta have no free faces. If these two xi faces self-pair, all B
intervals in eta and xi close: eta has one B slot, and xi has two,
or three if Q=B. Every B-incident face of either owner has been paired
within these two owners. This closed nonempty B subset has at most
four slots, contradiction. Thus both exit faces leave K.

## 252. The original U budget excludes a repeated-U exit

Each of the four interacting owners has genuine P expense greater
than pi. Their total exceeds 4*pi, while all genuine M/Z expense in
the entire triangulation is 3*pi. Therefore core U expense exceeds pi,
and all genuine U expense outside K is strictly less than pi.

An outside owner carrying U is genuine (U occurs in no flat owner).
It is either axial-U with transverse pair {C,D}, or single-high
transverse-U with distinct pair {U,b}, b in {C,D}. There is at most one
owner of the latter type. Such an owner cannot have a U axis: since
u>m and b<m-2, one has u>b+2. In the exact individual response for its
transverse U angle, the two positive coefficients satisfy
 A+B=2*(u-1)/(u+b)>1.
The established response inequality gives theta_U+2*beta_U>pi.
These are three original U slots of that owner, already exceeding the
entire remaining outside-U budget. This argument does not presume
that its other axis is different from U.

If Q=U, an exit face {U,U,B} cannot belong to an axial-U/{C,D} owner.
Any outside matching owner must have distinct transverse pair {U,B}
and a U axis, just excluded. Hence Q is not U.

## 253. A special exit axis cannot supply a complete special circle

If Q is special, {Q,U,B} cannot meet an axial-U/{C,D} owner. Both exits
must therefore meet the same single-high transverse-U owner, since
there is at most one. Its transverse pair is {U,B} and an axis is Q.
If its other axis is different from Q, its two Q faces pair to xi's
two Q faces, closing two original Q slots. If the other axis is also Q,
its remaining two {Q,U,B} faces can meet neither an axial-U/{C,D} owner
nor a second transverse-U owner. Xi has no unused faces. They must
self-pair, closing all three Q slots of xi and that owner. In both
cases minimum degree six fails. Thus Q is C or D.

For Q=B, the repeated-low face {B,U,B} cannot match an axial-U/{C,D}
owner, whose three labels are distinct. Both exits must reach the
single available transverse-U owner. For Q distinct from B, the face
is {C,D,U}, and axial-U/{C,D} exits remain possible. These alternatives
retain the external low-only region, arbitrary repeated owners and
self-pairings; no further exclusion is claimed.
