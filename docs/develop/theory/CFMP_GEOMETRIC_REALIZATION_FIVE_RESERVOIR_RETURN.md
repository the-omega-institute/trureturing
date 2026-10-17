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

## 254. Exact inherited setting and theorem

Retain the mixed-flat five-reservoir hypotheses of the paired-reservoir
 theory through Sections 245 and 246–253 of its return continuation.
The original finite face-paired carrier has complete connected circular
normal links and minimum original edge degree six. Every chosen paired
frame (R,A,B,O,A,B) has two distinct transverse labels A,B in H.
Lengths are positive and shared by actual global labels; every original
edge angle sum is 2*pi. Repeated axial labels, repeated neighboring
owners, parallel face pairings, and self-pairings of distinct faces are
allowed. No extra closure is imposed on the external low-only region.

Write H={M,C,D,Z,U}, P={M,Z,U}. The established reduction gives exactly
four distinct interacting genuine owners K={tau,rho,eta,xi}, where an
interacting owner contains two distinct P labels. The unique flat owner
has one M pi slot; Z and U occur in no flat. Thus the total genuine P
angle budget is pi+2*pi+2*pi=5*pi. Every interacting owner consumes
strictly more than pi of this budget (Sections 213–216 and 231–234).
Every face with two distinct P labels, called marked below, pairs to
another face in K. At most one owner is entirely high, meaning all six
slots lie in P (Sections 238–241). No special label has a fixed transverse
pair contained in P. These statements concern actual original slots.

The source is tau=(Z,M,C,D,M,C). Both its {M,Z,C} faces pair to one
owner rho. Sections 242–245 leave two possible roles. We prove that
 rho=(C,M,Z,U,M,Z)
is impossible. Consequently only the other role
 rho=(M,Z,C,Q,Z,C), with Q arbitrary,
remains. This theorem does not exclude that axial-M family and does not
prove five-reservoir realization.

For lower-case cosh values, the inherited strict bounds (in particular
Section 191 and its subsequent reductions) are
 c,d>1, m>1+c+d, z>1+m+c, u>m.
In particular c,d<m-2, m,u>3, and z>m+2>5.

## 255. The split return is impossible

Assume the exceptional role. Rho's two unused face occurrences have
three distinct labels {U,M,Z}. They cannot meet tau's unused faces
{D,M,C}. If they pair to one another, rho's unique U normal interval
closes, giving degree(U)=1. All these faces are marked, so their partners
belong to K. The remaining possibilities are a double return to one
of eta,xi or a split return, one face to each.

Suppose the return splits. Each of eta and xi has an incoming face with
three distinct high labels. Its transverse pair is two of these labels
and an incident axis is the third. If the owner is not entirely high,
its other axis is outside P; a special axis is excluded by the fixed
high-pair condition. Thus this other axis is C or D and is its unique
occurrence of that low label. Every face of either such owner is marked.
Every face of an entirely high owner is marked as well, because its
transverse labels are distinct and high.

If neither is entirely high, each has at most two U slots: one if U is
its high axis, or two if U is transverse. Tau has no U and rho has one.
Every U-incident face of these core owners is marked and therefore pairs
within K. Their nonempty set of U normal intervals is closed and has
at most 1+2+2=5 original slots. It must equal the whole connected normal
circle of the actual U edge, contrary to minimum degree six. This
argument includes every possible choice of the high axis.

Both eta and xi cannot be entirely high by the at-most-one theorem.
If exactly one is entirely high, denote the other by eta and its low
axis by B. Eta's two B-incident faces have multiset {B,A1,A2}, where
A1,A2 are two distinct P labels. They are marked and cannot be the
incoming {U,M,Z} face. They cannot pair to tau, whose unused faces have
only one distinct P label; rho has all four faces occupied; and xi,
being entirely high, has no B face. Within eta the only B faces are
these two. Thus they must pair to each other. Since B occurs exactly
once in eta, the two ends of that original B normal interval close,
forcing degree(B)=1. All alternatives contradict the hypotheses.
This proof uses the connected actual edge circle, not connectedness of
an arbitrary marked-face graph.

## 256. The double return and its scalar domain

It remains that both unused rho faces pair to eta. The complete public
exclusion and classification in Sections 246–253 give
 eta=(M,U,Z,B,U,Z), xi=(Z,U,B,Q,U,B),
where B,Q independently lie in {C,D}. Both remaining eta faces pair to
xi. All four owners tau,rho,eta,xi are distinct and genuine. The two xi
exit faces may meet the low external region; no extra equation on them
is assumed here. This classification includes B=Q and B different from Q.

For a genuine frame (r,a,b,o,a,b), put
 L=(a+b)^2-(r-1)(o-1), J=(r+1)(o+1)-(a-b)^2.
Both quantities are strictly positive. Thus the exact four choices
(b,q)=(c,c),(c,d),(d,c),(d,d) satisfy all eight inequalities
 L_tau=(m+c)^2-(z-1)(d-1)>0,
 J_tau=(z+1)(d+1)-(m-c)^2>0,
 L_rho=(m+z)^2-(c-1)(u-1)>0,
 J_rho=(c+1)(u+1)-(z-m)^2>0,
 L_eta=(u+z)^2-(m-1)(b-1)>0,
 J_eta=(m+1)(b+1)-(u-z)^2>0,
 L_xi=(u+b)^2-(z-1)(q-1)>0,
 J_xi=(z+1)(q+1)-(u-b)^2>0.

Since u>b and q<z, J_xi>0 implies
 0<u-b<sqrt((z+1)(q+1))<z+1.
Consequently m<u<m+z-1. The next scalar lemma only needs
 c>1, m>c+2, z>m+c+1, b<m-2, m<u<m+z-1.
We prove the strict inequality
 J_rho/(4*m*z)+J_eta/(4*u*z)<1/4.

## 257. Complete scalar certificate

### Clearing the exact denominators

Set \(k=c+1\). Multiplication by the positive number \(4muz\) gives

\[
4muz\left(\frac14-\frac{J_\rho}{4mz}
                   -\frac{J_\eta}{4uz}\right)=P,
\]

where

\[
P=(m-k)u^2+(z^2-3mz+m^2-k)u+mz^2-m(m+1)(b+1).
\]

Let

\[
P_0(u)=(m-k)u^2+(z^2-3mz+m^2-k)u+mz^2-m(m+1)(m-1).
\]

Then

\[
P=P_0(u)+m(m+1)(m-b-2)>P_0(u).
\]

It suffices to prove \(P_0(u)>0\).

### A positive Bernstein certificate

Put

\[
h=m-k-1>0,\qquad v=z-m-k>0,\qquad
\theta=\frac{u-m}{z-1}\in(0,1).
\]

For the quadratic polynomial \(P_0\), define

\[
C=P_0(m),\qquad
B=2P_0(m)+(z-1)P_0'(m),\qquad
E=P_0(m+z-1).
\]

The exact quadratic identity is

\[
P_0(u)=C(1-\theta)^2+B\theta(1-\theta)+E\theta^2.
\]

All three coefficients admit manifestly positive expressions:

\[
C=m\bigl[2k^2-k+1+(4k+m)v+2v^2\bigr],
\]

\[
\begin{aligned}
B={}&v^3+(3k+4m-1)v^2
 +(3k^2+6km-3k+2m^2+m)v\\
 &+h^3+(k+2)h^2+(k^2+3)h
 +2k^2(k-1)+2k+2,
\end{aligned}
\]

and

\[
\begin{aligned}
E={}&v^3+(2k+3m-1)v^2
 +(k^2+2km-k+3m^2-m)v\\
 &+2h^3+(5k+3)h^2+(3k^2+5k+2)h+(k+1)^2.
\end{aligned}
\]

Here \(k>2\), \(m=k+1+h>3\), and \(h,v>0\). Every displayed
coefficient is positive: for example, the coefficient of \(v\) in
\(B\) is \(3k(k-1)+6km+2m^2+m\), and that in \(E\) is
\(k(k-1)+2km+m(3m-1)\). Therefore \(C,B,E>0\).
As \(0<\theta<1\), the Bernstein identity yields \(P_0(u)>0\),
so \(P>0\). Division by \(4muz>0\) proves the claimed strict bound.


## 258. Two strict individual response bounds

The exact paired response from Sections 95–96 is as follows. For a,b>1,
 kappa(a,b)=(sqrt(a^2-1)+sqrt(b^2-1))/(a+b).
If s=beta_a+beta_b is the sum of the two distinct transverse angles,
then tan(s/2)=kappa(a,b)*sqrt(L/J). For either axial angle theta_r,
 tan(theta_r/2)*tan(s/2)=lambda_r,
 lambda_r=kappa(a,b)*sqrt((r-1)/(r+1)).
All these angles are genuine and 0<s<pi. Their multiplicities in the
owner are theta_r,theta_o,2*beta_a,2*beta_b.

Put t=z-m>c+1. The upper bound on u gives
 J_rho<(c+1)(2*m+t)-t^2<2*m*(c+1).
Since L_rho+J_rho=4*m*z+2*c+2*u>4*m*z,
 L_rho/J_rho>2*z/(c+1)-1
              >1+2*m/(c+1)>3+2/(m-1).
Likewise
 J_eta<=(m+1)*(b+1)<m^2-1,
 L_eta+J_eta=4*u*z+2*m+2*b>4*m^2,
so L_eta/J_eta>3+4/(m^2-1).

Kappa is a weighted average of sqrt(1-1/a^2) and sqrt(1-1/b^2).
Since z>m and u>m, both kappa(m,z)^2 and kappa(u,z)^2 are strictly
greater than 1-1/m^2. Define
 x=kappa(m,z)*sqrt(L_rho/J_rho),
 y=kappa(u,z)*sqrt(L_eta/J_eta).
Then
 x^2>3+2/m-1/m^2>3, y^2>3+1/m^2>3.

Kappa is strictly increasing in each argument. Indeed the sign of its
partial derivative in a is that of
 (a*b+1)-sqrt((a^2-1)*(b^2-1)),
which is positive since the difference of the squares is (a+b)^2.
As m,u>3 and z>5, both kappas exceed
 kappa(3,5)=(sqrt(2)+sqrt(6))/4,
whose square is (2+sqrt(3))/4.

## 259. The joint response exceeds the actual total budget

Set r=J_rho/(L_rho+J_rho), s=J_eta/(L_eta+J_eta).
Both are positive. Their denominators strictly exceed 4*m*z and 4*u*z,
respectively, so the scalar lemma gives r+s<1/4. Writing a=r+s and
using r*s<=a^2/4 gives
 (L_rho/J_rho)*(L_eta/J_eta)
 =1+(1-a)/(r*s)>=1+4*(1-a)/a^2>49.
(The last expression decreases for 0<a<1/4 and equals 49 at 1/4.)
Therefore
 x*y>7*(2+sqrt(3))/4>3+2*sqrt(3).
Since x,y>sqrt(3), expanding their positive shifted product gives
 x+y<x*y/sqrt(3)+sqrt(3).
It follows that x*y-x-y>1: at x*y=3+2*sqrt(3), the lower bound
 x*y*(1-1/sqrt(3))-sqrt(3)
is exactly 1, and it increases strictly with x*y.

Let s_rho=2*atan(x), s_eta=2*atan(y). Since x,y>1,
atan(x)+atan(y) is in (pi/2,pi). The inequality x*y-x-y>1 gives
 (x+y)/(x*y-1)<1; the tangent addition formula then yields
 atan(x)+atan(y)>3*pi/4.
Hence s_rho+s_eta>3*pi/2.

For rho use its high U axis, and for eta its high M axis. Each
transverse pair has both values greater than 3, so kappa^2>8/9;
the chosen high axis has value greater than 3, giving lambda>2/3.
The elementary response argument of Sections 238–239 implies
 theta_high+s>3*pi/4. For completeness, if theta_high+s<=3*pi/4,
the positive numbers theta_high/2 and s/2 have sum at most 3*pi/8;
their tangent product is at most tan^2(3*pi/16)<2/3, contradicting
its exact value lambda>2/3. The product bound follows from
cos(A-B)<=1 in the cosine expression for tan(A)tan(B), with A+B<pi/2.
For the numerical strict comparison one may use
 tan^2(3*pi/16)<tan^2(pi/5)=5-2*sqrt(5)<2/3.

The exact combined P expense of rho and eta is
 (theta_U(rho)+2*s_rho)+(theta_M(eta)+2*s_eta)>3*pi.
Their other axial labels C and B are low, so this counts precisely their
original P slots, with no duplication. Tau and xi are two further
distinct interacting owners; each consumes more than pi of P expense.
Thus these four actual owners already consume more than 5*pi, contrary
to the complete genuine P budget. External low-partner exits cannot
repair a violated upper budget. This excludes the double return.

Together with Section 255, every possible pairing of rho's two unused
faces has been excluded. The exceptional-U common-return family is
therefore impossible. The arbitrary-Q axial-M common-return family
remains open; no general five-reservoir or unrestricted CFMP conclusion
is asserted.
