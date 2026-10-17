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

## 260. Inherited setting and conclusion

Retain the original mixed-flat five-reservoir hypotheses through Section
259 of the return continuation. All edges have shared positive lengths,
complete connected circular normal links, original degree at least six,
and total dihedral angle 2*pi. Each chosen paired frame
(R,A,B,O,A,B) has distinct transverse labels A,B in H. The labels in
S=E\H occur only axially. Repeated axes, repeated neighboring owners,
parallel face pairings and self-gluings of distinct faces remain allowed.

Write H={M,C,D,Z,U}, P={M,Z,U}. The four distinct interacting owners K
are the genuine owners containing two distinct P labels. Each consumes
more than pi of the genuine P budget, whose total is 5*pi: M has budget
pi, while Z and U each have budget 2*pi and occur in no flat owner.
Every P label occurs in at least two distinct K owners. The unique flat
owner has transverse pair {C,D}; no flat owner contains Z or U.
These are the established reductions in Sections 205–234.

The source is tau=(Z,M,C,D,M,C). Its two {M,Z,C} faces pair to one
other owner rho. Sections 242–245 and the exceptional-U exclusion in
Sections 254–259 leave rho=(M,Z,C,Q,Z,C). We prove that Q=U.
This is a necessary role classification; it does not exclude this last
role or prove five-reservoir realization.

For lower-case cosh values the retained strict premises are
 c,d>1, m>1+c+d, z>1+m+c, u>m.
Thus c,d<m-2 and m>3. Since rho is genuine,
 (m+1)(q+1)>(z-c)^2>(m+1)^2,
so q>m. It follows that Q is Z, U or a special label in S.

## 261. A uniform individual-Z expense estimate

We record the exact response needed in both exclusions. Consider any
genuine paired owner with transverse pair {Z,C} and an axial cosh value
r>=m. Its other axis is arbitrary. Let theta_r denote the chosen axial
angle, beta_Z the transverse Z angle, and t=cot(theta_r/2)>0. The
individual paired response of Sections 95–96 gives
 beta_Z=atan(A*t)+atan(B*t),
 A=(sqrt(z^2-1)+sqrt(c^2-1))/(z+c)*sqrt((r-1)/(r+1)),
 B=(sqrt(z^2-1)-sqrt(c^2-1))/(z+c)*sqrt((r-1)/(r+1)).
Both A and B are positive, since z>m>c>1. Their sum is
 A+B=2*sqrt(z^2-1)/(z+c)*sqrt((r-1)/(r+1))>1.
Here is a direct verification of the strict bound. For fixed c>1,
 sqrt(z^2-1)/(z+c)
is strictly increasing in z: its derivative has numerator z*c+1>0.
For fixed z it is decreasing in c. The axial factor is increasing in r.
Use z>m, c<m-2 and r>=m to compare with z=m,c=m-2,r=m. At that boundary
 2*sqrt(m^2-1)/(2*m-2)*sqrt((m-1)/(m+1))=1.
The comparison is strict in the actual domain.

Consequently beta_Z>atan(t). Indeed, if A*B*t^2>=1, the sum of the two
arctangents is at least pi/2, which exceeds atan(t). Otherwise its sum
lies in (0,pi/2) and its tangent is
 (A+B)*t/(1-A*B*t^2)>t.
In either case, since atan(t)=pi/2-theta_r/2, we obtain
 theta_r+2*beta_Z>pi.                         (261.1)
These are three actual slots of one owner; no assumption on the other
axis, or on distinct neighboring owners, was used.

## 262. The repeated-Z axis is impossible

Suppose Q=Z. Since all four K owners consume more than pi of P expense,
core P expense exceeds 4*pi. The entire genuine M+U budget is 3*pi,
so core Z expense exceeds pi. All genuine Z expense outside K is
therefore strictly less than pi.

Any owner incident to a face with multiset {Z,Z,C} must have distinct
transverse pair {Z,C} and a Z axis. Z occurs in no flat, so that owner is
genuine. Applying (261.1) with r=z>m shows that its three Z slots already
consume more than pi. Thus no owner outside K can receive either of
rho's two remaining {Z,Z,C} faces.

These faces cannot match tau's unused {D,M,C} faces. If they pair to
each other, every Z-incident face of tau and rho is paired within these
two owners. Their nonempty set of 1+3=4 original Z normal intervals
would be a closed component of the actual Z circle, contradicting
minimum degree six. Hence at least one face meets eta or xi, the two
remaining K owners. Denote one such receiver by eta.

Tau and rho contain no U. The two-owner occurrence property for U
therefore implies that both eta and xi contain U. Eta's incoming face
{Z,Z,C} forces pair {Z,C} and a Z axis. Its only remaining place for U
is its other axis. Thus eta=(Z,Z,C,U,Z,C), up to the frame symmetries,
and (261.1) gives more than pi of Z expense from eta.

Tau has more than pi of M/Z expense by the established source estimate
(Section 210). In rho, (261.1) with its M axis gives
 theta_M(rho)+2*beta_Z(rho)>pi.
The distinct owners tau,rho,eta therefore spend more than 3*pi on M/Z,
contrary to the entire genuine M/Z budget. These three charges use
original slots of distinct owners, even when other incidences repeat.
Thus Q is not Z.

## 263. A special opposite axis is impossible

Suppose Q belongs to S. Every occurrence of the actual global label Q
is axial, because transverse labels belong to H. Start with rho, whose
Q axis has fixed transverse pair {Z,C}. Across either Q-incident face,
the matching face has labels {Q,Z,C}. At its receiver Q must again be
axial; therefore that receiver's fixed transverse pair is {Z,C}.

Propagate this fact along the actual Q normal circle. Every original
Q interval is reached, because this circle is connected. Consequently
every actual owner containing Q has transverse pair {Z,C}, even if an
owner supplies two Q intervals or is revisited by the traversal. Every
such owner is genuine: it contains Z, which has no flat occurrence.
This argument neither assumes distinct neighbors nor replaces the
normal circle by a graph on owner names.

Let n be the number of distinct actual owners containing Q. In each
owner select one of its Q slots. Apply (261.1) with r=q>m to its selected
axial angle and its two original transverse Z angles. Summing over these
n distinct owners yields a strict expense greater than n*pi. The chosen
Q angles sum to at most the full Q budget 2*pi. The chosen transverse Z
slots are distinct original slots across the selected owners and sum
to at most the full genuine Z budget 2*pi. Hence n*pi<4*pi and n<=3.

Each selected owner has at most two Q slots, since Q can only occupy its
two axes. Rho has exactly one, since its other axis is M and Q is special.
All original Q slots belong to these n owners by the propagation above.
Thus degree(Q)<=1+2*(n-1)<=5, contrary to minimum degree six.

The special case is impossible. Together with Section 262 and q>m, the
only remaining opposite-axis label is Q=U. The theorem preserves all
original multiplicities and the external low-only region. It supplies
no exclusion of rho=(M,Z,C,U,Z,C), which remains the next open family.

## 264. Exact setting and theorem

Retain the original mixed-flat five-reservoir hypotheses through Section
263, with shared positive lengths, all original 2*pi angle equations,
complete connected circular edge links of degree at least six, and
chosen paired frames with two distinct transverse H labels. Write
H={M,C,D,Z,U} and P={M,Z,U}. The four distinct interacting genuine
owners are K={tau,rho,eta,xi}. The published reductions give
 tau=(Z,M,C,D,M,C), rho=(M,Z,C,U,Z,C),
with the two {M,Z,C} faces paired between tau and rho. Assume in this
note that neither eta nor xi contains M.

The unique flat owner has an axial M pi slot and transverse pair {C,D}.
The genuine M budget is pi. Z and U occur in no flat and each has
budget 2*pi. Lower-case cosh values satisfy
 c,d>1, m>1+c+d, z>1+m+c, u>m.
All repeated axes, repeated owners along circles, and distinct-face
self-gluings remain permitted. External low-only components are not
assumed closed inside K.

We prove that this case necessarily has
 max(c,d)<2*min(c,d)+1,
and at least one of the two genuine axial-M/{C,D} owners constructed
below has a special opposite axis. Thus the entire unbalanced case and
the entire both-low-opposite-axes case are excluded. The balanced cases
with one or two special opposite labels are not excluded here; nor is
the case that eta or xi contains M. No five-reservoir closure is claimed.

## 265. The actual M circle has exactly six original slots

The three original M intervals of tau (two transverse) and rho (one
axial) form a path with its two ends on tau's unused {M,C,D} faces.
The M edge on each paired {M,Z,C} face is unambiguous, since those
three labels are distinct.

Every other M owner is outside K by the assumed absence of M from
eta,xi. The complete single-high-M classification (Sections 205–221)
leaves the unique flat, at most two genuine axial-M/{C,D} owners, and
at most one transverse-M exception (B,M,B,B,M,B), B=C or D. The
exception has only face multisets {M,B,B} and cannot receive {M,C,D}.

Every axial-M/{C,D} owner has exactly one M slot. If both axes were M,
then (m-1)^2>(c+d)^2 would make it axial-flat with two M pi slots,
contrary to p_M=1. Its one M interval has both ends on {M,C,D} faces.
Following the actual circle from a free tau endpoint therefore remains
within the axial-M/{C,D} class until it returns to the tau/rho path.
Connectedness leaves no additional disjoint M interval or transverse-M
exception. There are at most
 2+1+1+2=6
original slots: tau's two, rho's one, the flat's one and at most two
genuine axial-M slots. Minimum degree six forces equality.

Consequently there are exactly two distinct genuine owners
 A_i=(M,C,D,R_i,C,D), i=1,2,
and the exact original M equation is
 S+theta_M(A_1)+theta_M(A_2)=pi,
 S=2*beta_M(tau)+theta_M(rho).                    (265.1)
An opposite R_i cannot be M by the preceding argument, or Z/U, because
m>1+c+d and z,u>m would make that axial pair flat, contradicting the
absence of Z/U from all flat owners. Therefore R_i is C,D or special.
For a special R_i its fixed pair is {C,D}, so Theorem112.1 gives
1<r_i<1+c+d. The same upper bound holds for the low alternatives.

## 266. A strict one-third M budget already paid by the source pair

We prove
 S>pi/3.                                        (266.1)
The published source response gives
 theta_Z(tau)+2*beta_M(tau)>pi.
The original Z equation implies
 theta_Z(tau)+2*beta_Z(rho)<=2*pi.               (266.2)
Both inequalities concern original slots; other Z contributions have
only been omitted as nonnegative.

Put theta=theta_M(rho), h=theta/2, t=cot(h)>0. The exact individual
response for rho's transverse Z angle is
 beta_Z(rho)=atan(A*t)+atan(B*t),
 A=[sqrt(z^2-1)+sqrt(c^2-1)]/(z+c)*sqrt((m-1)/(m+1)),
 B=[sqrt(z^2-1)-sqrt(c^2-1)]/(z+c)*sqrt((m-1)/(m+1)).
Here 0<B<A<1, and their product is
 p=A*B=(z-c)/(z+c)*(m-1)/(m+1)>1/3.
Indeed z>m+c+1 first gives
 p>(m-1)/(m+2*c+1),
and c<m-2 makes this last expression greater than 1/3.
Also A+B<=1+p, since (1-A)*(1-B)>=0.

If theta>pi/3, (266.1) is immediate. Otherwise h<=pi/6 and t>=sqrt(3).
At t=sqrt(3), p*t^2>1, so beta_Z(rho)>pi/2 and
 theta+2*beta_Z(rho)>4*pi/3.
For t>sqrt(3), the tangent addition formula on the branch (pi/2,pi)
gives
 beta_Z(rho)=pi-atan((A+B)*t/(p*t^2-1)).
For fixed t, (1+p)/(p*t^2-1) is strictly decreasing in p. Therefore
 (A+B)*t/(p*t^2-1)<= (1+p)*t/(p*t^2-1)
                        <4*t/(t^2-3).
The sum atan(t)+atan(t/3) lies in (pi/2,pi), with the latter ratio as
the absolute value of its tangent. Thus
 beta_Z(rho)>atan(t)+atan(t/3),
and, since h+atan(t)=pi/2,
 theta+2*beta_Z(rho)>pi+2*atan(t/3)>4*pi/3.
This proves that inequality whenever theta<=pi/3 as well.

If S<=pi/3, then theta<=pi/3 and adding the source inequality gives
 [theta_Z(tau)+2*beta_Z(rho)]+S>7*pi/3.
This contradicts (266.2) and S<=pi/3. Hence (266.1) holds. By (265.1),
 Theta=theta_M(A_1)+theta_M(A_2)<2*pi/3.         (266.3)

## 267. Unbalanced transverse values are impossible

Set a=max(c,d), b=min(c,d), choosing either actual label in a numerical
tie. Suppose a>=2*b+1. For either A_i, the individual transverse-a
response as a function of its M angle x is
 beta_a(x)=atan(lambda_plus*cot(x/2))
              +atan(lambda_minus*cot(x/2)),
 lambda_plus/minus=[sqrt(a^2-1) +/- sqrt(b^2-1)]/(a+b)
                                      *sqrt((m-1)/(m+1)).
Both lambda parameters are in (0,1). Each arctangent response is
strictly decreasing and strictly convex on (0,pi), so their sum is too.
The response is the same function in both owners, independently of
their opposite axes.

Its parameter product satisfies
 lambda_plus*lambda_minus
 =(a-b)/(a+b)*(m-1)/(m+1)
 >(a-b)/(a+b+2)>=1/3,
using m>a+b+1 and a>=2*b+1. At x=pi/3 the product of the two arctangent
arguments consequently exceeds one, so beta_a(pi/3)>pi/2.
Jensen's inequality and (266.3) now give
 beta_a(theta_M(A_1))+beta_a(theta_M(A_2))
 >=2*beta_a(Theta/2)>2*beta_a(pi/3)>pi.
Each angle occurs twice in its owner. These four original a slots
already exceed the whole edge-a budget 2*pi, contradiction.
Hence a<2*b+1. This exclusion allowed either or both R_i to be special,
with arbitrary overlap of their complete stars.

## 268. Both opposite labels low is impossible in the balanced range

It remains to consider b<=a<2*b+1 and suppose both R_i are C or D.
Each opposite value r_i is then at least b. We prove for every such
owner that theta_M(A_i)>pi/3, contradicting (266.3).

The exact axial cosine has positive denominator
 D=m^2+a^2+b^2+2*m*a*b-1
and numerator
 N(r)=2*a*b+m*(a^2+b^2)-(m^2-1)*r.
Since r>=b and m>1, D-2*N(r)>=D-2*N(b).
Put h=m-a-b-1>0. Direct expansion gives
 D-2*N(b)
 =2*(a+1)*(a+b)*(2*b+1-a)
  +2*[(a-b)*(2*b+1-a)+3*b^2+4*b+1]*h
  +(1+2*b)*h^2.
All terms are nonnegative in b<=a<=2*b+1, and the coefficient of h
is strictly positive. Therefore D-2*N(r)>0. It follows that
 cos(theta_M(A_i))=N(r)/D<1/2,
so its principal genuine angle exceeds pi/3. The two distinct A_i
then contribute more than 2*pi/3, contrary to (266.3).

The both-low case is thus excluded in the balanced range, while Section
267 already excluded the unbalanced range with any opposite-axis roles.
Every surviving no-extra-core-M configuration must have balanced low
values and at least one special R_i. This is an actual subcase exclusion
under the unchanged original hypotheses, not a claim that the strengthened
special-star scalar inequalities or the entire residual family are
inconsistent. The complete special-axis stars remain required in the
next case analysis.

## 269. Inherited actual hypotheses and conclusion

Retain the original mixed-flat five-reservoir hypotheses through Section
268 of the return continuation, including distinct transverse labels,
actual shared positive lengths, complete connected circular edge links,
and minimum original degree six. Assume neither of the two remaining
interacting owners eta,xi contains M. Sections 264–268 give the exact
six-slot M circle with two distinct genuine owners
 A_i=(M,C,D,R_i,C,D), i=1,2,
and
 Theta=theta_M(A_1)+theta_M(A_2)<2*pi/3.
The unique flat owner is sigma=(M,C,D,O,C,D), with O=C,D or special.
We prove O is C or D. This excludes the whole special-O subcase,
regardless of whether the two R_i labels coincide or their stars overlap.
It does not exclude the remaining low-O, special-R_i configurations or
the cases in which eta or xi contains M.

## 270. The response transfer applies with two owners

Put s=c+d and
 K=(sqrt(c^2-1)+sqrt(d^2-1))^2/s^2,
 T=(m-1)/(m+1), lambda_M^2=K*T.
At least one of the two genuine M angles is less than pi/3, since their
sum is less than 2*pi/3. The transfer calculation in Section 209, which
explicitly uses only the existence of one angle at most pi/3, therefore
applies. It does not require three axial-M owners. Its conclusions are
 K*T>1/3,
 F(m)=2*(m-1)/s^2-T*(c-d)^2/s^2<1/3.
The flat source supplies the actual product inequality
 (m-1)*(o-1)>=s^2.
Consequently
 lambda_O^2=K*(o-1)/(o+1)
             >=K/[1+2*(m-1)/s^2]>1/7,
as in the same transfer calculation. For clarity about the last step,
0<T<1 and (c-d)^2/s^2<1 give
 1+2*(m-1)/s^2=1+F(m)+T*(c-d)^2/s^2<7/3.
Also K>1/3 follows from K*T>1/3 and T<1. Therefore the displayed
ratio is strictly greater than (1/3)/(7/3)=1/7.

## 271. The two M owners already spend more than two pi on C/D

For 0<lambda<1 define
 b_lambda(theta)=atan(lambda*cot(theta/2)), 0<theta<pi.
This is strictly decreasing and strictly convex, as established in the
paired response calculation. A genuine pair-CD owner with chosen M
axis has actual transverse C/D expense 4*b_lambda_M(theta_M).
Jensen and Theta<2*pi/3 give
 4*[b_lambda_M(theta_M(A_1))+b_lambda_M(theta_M(A_2))]
 >=8*b_lambda_M(Theta/2)
 >8*b_lambda_M(pi/3)>2*pi,
because lambda_M>1/sqrt(3) and cot(pi/6)=sqrt(3).
These are the original four transverse slots of each of two distinct
owners. Any additional C/D axial slots are omitted as nonnegative.

## 272. A special flat opposite axis forces a disjoint excess

Suppose O is special. Its connected actual normal circle propagates
fixed transverse pair {C,D}, because O occurs only axially. The unique
flat owner supplies exactly one O slot of angle pi. Every other O slot
is genuine. There are h=degree(O)-1>=5 such original slots, with angles
phi_j in (0,pi) satisfying sum_j phi_j=pi.

No genuine O owner is A1 or A2: one containing M and O with fixed pair
{C,D} has exactly the same six shared lengths as sigma, so would be
flat. Thus the genuine O-star owners are disjoint from A1,A2.
An owner may have two O axes. Charging 2*b_lambda_O(phi_j) for each
original O slot counts its transverse sum once per axial occurrence,
hence at most twice, which its actual four C/D transverse slots pay.
Repeated visits to an owner do not introduce extra charges.

The total genuine transverse C/D expense of these O owners is at least
 2*sum_j b_lambda_O(phi_j)
 >=2*h*b_lambda_O(pi/h)
 >=10*b_lambda_O(pi/5).
The last inequality follows since x*b_lambda_O(pi/x) increases in x:
its derivative is b_lambda_O(v)-v*b_lambda_O'(v)>0.
Since lambda_O>1/sqrt(7) and
 cot(pi/10)^2=5+2*sqrt(5)>7,
we have b_lambda_O(pi/5)>pi/4. The O owners therefore consume more
than 5*pi/2 of C/D angle. Together with the disjoint A1,A2 expense,
the actual genuine C/D cost exceeds 2*pi+5*pi/2>4*pi, contradicting
the combined original C and D budgets.

Thus O cannot be special. In the no-extra-core-M case, the flat opposite
label must be C or D, the low values must be balanced by Section 267,
and at least one R_i must be special by Section 268. All remaining
special-axis stars still need their complete original equations; no
closure of the five-reservoir family is asserted.

## 273. Exact setting and public inputs

Retain the original mixed-flat five-reservoir hypotheses through Section
272 of the return continuation. The carrier is the actual original
finite face pairing, with positive lengths shared by global edge labels,
complete connected circular normal links, and original degree at least
six. All original edge angle sums are 2*pi. Chosen paired frames have
two distinct transverse labels in H={M,C,D,Z,U}. Special labels outside
H occur only axially. Repeated axes, repeated neighboring owners,
parallel face pairings and self-gluings of distinct faces are allowed.

There are four distinct interacting genuine owners K={tau,rho,eta,xi},
where interacting means containing two distinct labels in P={M,Z,U}.
Each consumes more than pi of genuine P angle. Total genuine P angle
is 5*pi: M has pi and Z,U each have 2*pi. The unique flat owner is
sigma=(M,C,D,O,C,D). The retained source and common return are
 tau=(Z,M,C,D,M,C), rho=(M,Z,C,U,Z,C).
The shared cosh values satisfy c,d>1,m>1+c+d,z>1+m+c,u>m.

Assume for contradiction that neither eta nor xi contains M. Sections
264–272 then supply two distinct genuine owners outside K,
 A_i=(M,C,D,R_i,C,D), i=1,2,
the exact six-slot M circle, and
 Theta=theta_M(A_1)+theta_M(A_2)<2*pi/3.
They also prove that O is C or D, and that the four transverse C/D
slots of each A_i together cost more than 2*pi across the two owners.
For precision this last statement is the strict inequality
 E_A=2*sum_i[beta_C(A_i)+beta_D(A_i)]>2*pi.
Since sigma has its other pi axis at O in {C,D}, the total genuine C/D
budget is 3*pi. We prove this branch impossible. The conclusion forces
at least one of eta,xi to contain M; it does not exclude those cases
or establish five-reservoir realization.

## 274. Both opposite axes are special and smaller than both low values

For a genuine frame (r,a,b,o,a,b), let
 L=(a+b)^2-(r-1)*(o-1)>0,
 D_r=r^2+a^2+b^2+2*r*a*b-1,
 D_o=o^2+a^2+b^2+2*o*a*b-1.
The cosines of the two transverse angles have common positive
denominator sqrt(D_r*D_o). Their numerators are
 N_a=b*(r+o)+a*(r*o+b^2-a^2+1),
 N_b=a*(r+o)+b*(r*o+a^2-b^2+1).
Their exact difference is N_a-N_b=-(a-b)*L. Therefore a>=b implies
beta_a>=beta_b, strictly if a>b.

If the actual flat-opposite label O were the numerically larger of C,D,
its transverse expense in A1,A2 would be at least E_A/2>pi. That exceeds
its entire genuine budget pi. The same argument excludes equal low
values. Thus O is the strictly smaller low label. Write its value b
and the other low value a>b. The flat product and genuine A_i products
now give
 (m-1)*(b-1)>=(a+b)^2>(m-1)*(r_i-1).
Hence r_i<b. Sections 265 and 268 already restrict R_i to C,D or special;
neither low label has a value below b. Both R_i are therefore special.
They may be the same actual label or distinct labels with equal values.

## 275. A uniform low-only axial-slot inequality

Consider any genuine owner with fixed transverse pair {a,b}, where
a>=b>1, a chosen axial value 1<r<b, and opposite value 1<o<1+a+b.
Write theta for its r-axis angle and s_angle=beta_a+beta_b. We prove
 s_angle>theta.                                  (275.1)
Set
 L=(a+b)^2-(r-1)*(o-1)>0,
 J=(r+1)*(o+1)-(a-b)^2>0,
 kappa=(sqrt(a^2-1)+sqrt(b^2-1))/(a+b).
The exact paired response gives
 tan(theta/2)^2=(r-1)/(r+1)*J/L,
 tan(theta/2)*tan(s_angle/2)=kappa*sqrt((r-1)/(r+1)).
Both theta and s_angle lie in (0,pi). Thus (275.1) is equivalent to
 sqrt((r-1)/(r+1))*J/L<kappa.

The expression on the left strictly increases in each of r,o wherever
J,L>0: the square-root factor increases in r, J increases in each
variable, and L decreases in each variable. Increase to r=b and
 o=1+a+b. Along that rectangle J remains positive and L remains
positive, since its minimum at the final corner is (a+b)*(a+1)>0.
It suffices to show the corner expression is at most kappa.
At that corner J=(b+1)*(a+b+2)-(a-b)^2 and L=(a+b)*(a+1).
After multiplication by positive factors, the corner comparison is
 2*b+1-a<=sqrt((a^2-1)*(b+1)/(b-1)).
The left side is at most b+1, and the right side is at least b+1,
because a>=b. Equality is possible only at a=b. Since the actual
r and o are strictly below the corner, the actual comparison is strict.
This proves (275.1), including possible repeated axial labels.

## 276. Complete special circles and the high-angle payment

Let S0 be the set of distinct actual labels among R1,R2, and n=|S0|,
so n is one or two. For each label R in S0, its connected original
normal circle propagates fixed transverse pair {C,D}. Indeed, across
an R-incident face the special label R must again be axial, and the
other two face labels are C,D. Connectedness reaches every original
R slot, even when an owner or an axial label repeats.

None of these R labels occurs in the unique flat sigma, whose axes are
M and the low label O. Therefore every R slot is genuine and its full
angle sum is 2*pi. None of their owners belongs to K: fixed pair {C,D}
with a special R axis leaves at most one axis for a P label, so such an
owner cannot contain two distinct P labels.

Write alpha_i=theta_{R_i}(A_i). Because r_i<m, the two exact axial
responses of A_i give
 tan(alpha_i/2)/tan(theta_M(A_i)/2)
 =sqrt([(r_i-1)/(r_i+1)]/[(m-1)/(m+1)])<1.
Thus alpha_1+alpha_2<Theta. Removing these two distinct original slots
from the complete R circles leaves total angle
 T_remaining=2*n*pi-alpha_1-alpha_2.
All remaining slots lie in genuine owners outside K and outside A1,A2.

Partition these residual slots by whether their opposite axis is high,
meaning labelled in P, or low-only, meaning outside P. A residual slot
with high opposite label Y has one R axis and one Y axis. It has exactly
one selected special slot, even if S0 contains two labels. Its angle
psi is strictly less than theta_Y, by the same axial-response comparison
and r<b<m<=y. Distinct such selected slots belong to distinct owners
and select distinct actual high-axis slots.

There is in fact at most one such high-opposite residual slot. The
published four-core bound in Sections 231–234 allows at most eight
actual high-containing owners. The four K owners, sigma, A1 and A2
are seven distinct such owners. Every high-opposite residual owner is
outside this set and contains exactly one selected R slot. Hence only
one remains possible. The following summed budget also works directly
without relying on this cardinality refinement.

Let H be the sum of those selected high-axis angles and Psi the sum of
their R angles. The four K owners spend more than 4*pi of the total
5*pi P budget. The A_i spend Theta on their distinct M axes. Therefore
 Theta+H<pi.
If there are no high-opposite residual slots, H=Psi=0; otherwise Psi<H.
In all cases Psi<=H<pi-Theta.
Consequently the low-only residual selected slots have total angle
 T_low=2*n*pi-alpha_1-alpha_2-Psi
       >(2*n-1)*pi+Theta-alpha_1-alpha_2>pi.
No bound on the number of low-only owners, or closure of the external
low-only region within the high core, was used.

## 277. The remaining low-only owners exceed the entire available budget

A low-only residual selected slot has r<b and opposite label either
C,D or special. In the first case its opposite value is below 1+a+b.
In the second case the connected special circle has the same fixed pair
{C,D}, so its value is below 1+a+b by the special fixed-pair barrier.
Thus (275.1) applies to every one of these original slots.

Charge beta_C+beta_D to each such selected slot. An actual owner has at
most two selected special axial slots, across all labels in S0. It
therefore receives at most two such charges, which its actual transverse
C/D expense 2*(beta_C+beta_D) pays. This remains true for a repeated R
axis and for an owner whose two axes are the two different selected
special labels. Summing (275.1), the genuine C/D expense of these low-only
owners is strictly greater than T_low>pi.

These owners are disjoint from A1,A2, whose transverse C/D expense E_A
is greater than 2*pi. The combined genuine C/D expense is therefore
greater than 3*pi, contradicting the exact genuine C/D budget after
the low flat-opposite pi slot. This excludes the entire assumed
no-extra-core-M branch. At least one of the remaining interacting
owners eta,xi must contain M. The residual cases with that extra core
M occurrence remain open, with all original equations still required.

## 278. Actual setting and conclusion

Retain the original mixed-flat five-reservoir hypotheses and all public
reductions through Section 277 of the return continuation. In particular
all edge labels carry shared positive lengths, every original edge has
a connected circular normal link of degree at least six, and chosen
paired frames have two distinct transverse labels. Original face and
edge occurrences, rather than neighboring owner names, are counted.
Repeated axes, repeated neighbors and distinct-face self-gluings remain
allowed.

Write P={M,Z,U} and K={tau,rho,eta,xi} for the four distinct interacting
genuine owners. Every face containing two distinct P labels is marked
and pairs inside K. The source and forced common return are
 tau=(Z,M,C,D,M,C), rho=(M,Z,C,U,Z,C).
Tau's two {M,Z,C} faces pair to rho's two M-incident faces. The remaining
tau faces are {M,C,D}, unmarked. The two unused rho faces are {U,Z,C},
both incident to its unique U axis. The newly proved no-extra-core-M
exclusion says at least one of eta,xi contains M.

We prove that rho's two unused face occurrences pair to different
owners eta and xi. Thus their common-return alternative is completely
excluded. The surviving split return is not excluded here; this is not
a proof of five-reservoir realization.

The two rho faces cannot self-pair, since that would close rho's single
U normal interval and force degree(U)=1. They cannot meet tau's unused
faces. As they are marked, they must meet eta or xi. Suppose for
contradiction that both meet eta. We separate whether eta contains M.

## 279. A common receiver containing M is impossible

Every face of a chosen paired frame contains both transverse labels.
Since eta has an incoming face {U,Z,C} with no M, any M occurrence in
eta is axial and opposite this face. There is exactly one such M axis:
if both axes were M, every face would contain M. The incoming face has
three distinct labels, so up to paired-frame symmetries there are exactly
three possible roles:
 (i) eta=(M,U,Z,C,U,Z),
 (ii) eta=(M,U,C,Z,U,C),
 (iii) eta=(M,Z,C,U,Z,C).
The two incoming face occurrences are precisely the two faces of the
non-M axis in each of these roles.

In (ii), all Z intervals in tau,rho,eta form a closed subset of the
actual Z circle. Tau has one Z axis, rho two transverse Z slots, and
eta one Z axis. Their incident faces have all been paired in this chain:
tau to rho across {M,Z,C}, then rho to eta across {U,Z,C}. There are
exactly 1+2+1=4 slots, contradicting minimum degree six.
In (iii), the unique U axes in rho and eta close across their two paired
faces, giving a closed two-slot U circle, again impossible.

In (i), eta's two remaining face occurrences are {M,U,Z}, incident to
its unique M axis. They are marked. They cannot meet tau's unused faces,
and all rho faces are occupied. Self-pairing would close eta's single
M interval. Consequently both remaining eta faces must meet xi.

An incoming {M,U,Z} face forces xi's transverse pair to contain two
of these three distinct high labels, with its incident axis the third.
Thus every xi face is marked, independently of its other axis. Its two
remaining faces cannot meet tau's unmarked free faces; rho and eta
have no unused faces. They must pair to each other.

Now all M-incident faces of eta and xi are paired within these two
owners. Eta's incoming {C,U,Z} faces have no M. Its M axis has its two
ends paired to xi. Every xi face pairs either to eta or to xi itself.
Hence their nonempty set of original M intervals is closed. Eta supplies
one M slot; xi has at most three M slots. Indeed M is either transverse,
with two slots and at most one additional M axis because the incoming
axis is another high label, or axial, with at most two slots. The closed
subset has at most four original M slots. Connectedness of the actual
M circle contradicts minimum degree six. This excludes (i) as well.

## 280. A common receiver without M forces an isolated M interval

Suppose eta contains no M. Then xi contains M by Section 277. Again
its incoming {U,Z,C} face has three distinct labels. The incident axis
of eta is U, Z, or C.

If this axis is U and eta's other axis is not U, eta has pair {Z,C}
and a unique U slot. Its two U faces are exactly the two incoming faces;
together with rho's unique U interval they close a two-slot circle.
Thus this role could survive only if both eta axes are U. In that case
all four eta faces have labels {U,Z,C} and are marked. This statement
allows the two incoming faces to come from different repeated axes.

If the incident axis is Z and the other axis is not Z, eta has pair
{U,C} and a unique Z slot. The same original Z-circle argument as in
Section 279 closes tau's one, rho's two and eta's one Z slots, impossible.
Thus this role could survive only if both eta axes are Z. All four eta
faces are again {U,Z,C} and marked, with all incoming choices allowed.

If the incident axis is C, eta has transverse pair {U,Z}. Every one of
its faces is marked, regardless of its other axis. These three cases
exhaust the paired roles, so every remaining eta face is marked.

Eta's two unused faces contain no M and therefore cannot meet tau's
free {M,C,D} faces. All rho faces are occupied. If the eta faces pair
to each other, every U-incident face of rho and eta is paired within
those two owners: rho's other two faces are {M,Z,C}, with no U.
Their U normal intervals form a nonempty closed subset of at most
rho's one plus eta's three, namely four original slots. This violates
minimum degree six, including all repeated-U possibilities. Therefore
both remaining eta faces must pair to xi.

Each such incoming xi face contains no M and contains two distinct
high labels U,Z. Since xi contains M, M must be its unique opposite
axis, by the same face-occurrence argument as in Section 279. Its two
remaining face occurrences are precisely those incident to this M axis.
Xi's transverse pair contains at least one of U,Z, since it is a pair
of distinct labels from an incoming face containing both. Thus the two
M-incident xi faces are marked. They cannot pair to tau's unmarked
remaining faces, and rho and eta have no free faces. They must pair
to each other, closing xi's unique M interval and forcing degree(M)=1.
This final contradiction excludes the common receiver without M.

Both common-receiver alternatives are impossible. Therefore rho's two
unused faces split, one to eta and one to xi. No connectivity of a
marked-face graph, closure of the external low-only region, or extra
geometric inequality was assumed. The only circle closures used above
are explicitly closed subsets of the original connected edge links.
The actual split-return configurations remain open.

## 281. Exact inherited setting and closing claim

Retain the original mixed-flat five-reservoir hypotheses through Section
277, and the complete forced-split theorem in Sections 278–280 of the
return continuation. In particular the original finite face-paired
carrier has positive lengths shared by global edge labels, angle sum
2*pi at every original edge, and connected circular normal links with
original degree at least six. The chosen paired frames have distinct
transverse labels in H={M,C,D,Z,U}; these are five distinct actual global
labels. Repeated axes, repeated neighboring owners, parallel face
pairings and self-pairings of distinct faces remain allowed.

Write P={M,Z,U}. The four distinct interacting genuine owners are
K={tau,rho,eta,xi}. Every face containing two distinct P labels is marked
and its partner belongs to K. The established actual source and return
are
 tau=(Z,M,C,D,M,C), rho=(M,Z,C,U,Z,C).
Tau's two {M,Z,C} face occurrences pair to rho's two M-incident faces.
Tau's other two faces are {M,C,D}. Rho's remaining two faces {U,Z,C}
are, by the forced-split theorem, paired one to eta and one to xi.
Thus every face occurrence of rho is occupied. Section 277 ensures
that at least one of eta,xi contains M.

We prove these inherited conclusions are inconsistent. Consequently
there is no mixed-flat critical configuration under these original
five-reservoir paired hypotheses. This closing statement concerns this
inherited paired class; no unrestricted CFMP assertion is made here.
A geometric realization corollary requires the separately applicable
existence and original manifold hypotheses, and is not asserted in this
local closing argument.

## 282. Each remaining M owner has exactly one M interval

Let V be the nonempty subset of {eta,xi} consisting of owners containing
M. Each owner v in V receives one actual face with three distinct labels
{U,Z,C}, none equal to M.

Every face of a chosen paired frame contains its two transverse labels.
Therefore M cannot be transverse in v. At least one of its axes is M
because v contains M. Both axes cannot be M: every face contains an
axis edge and would then contain M, contradicting the incoming face.
Thus v has exactly one original M occurrence, an axial one. The incoming
{U,Z,C} face is opposite that M axis.

The transverse pair of v is a pair of distinct labels chosen from
{U,Z,C}, so it contains at least one of U,Z. Both faces incident to the
M axis therefore contain M and another distinct P label. They are
marked. Their label multisets are exactly one of {M,U,Z}, {M,U,C}, or
{M,Z,C}. Each contains exactly one M edge occurrence. Neither is the
incoming M-free face from rho.

## 283. Occupied faces force a closed circle of at most two slots

A partner of any M-incident face of an owner in V lies in K, because
that face is marked. It cannot lie in rho, whose four original face
occurrences have already been paired: two to tau and one each to eta
and xi. It cannot be one of tau's two {M,Z,C} faces, which are occupied
by rho. Tau's only unused faces are {M,C,D}. These cannot match any of
{M,U,Z}, {M,U,C}, {M,Z,C}, since C,D are distinct from M,U,Z and from
each other.

The partner therefore belongs to eta or xi. An owner in {eta,xi}\V has
no M occurrence and cannot receive an M-labelled face. Hence every
M-incident face of every owner in V pairs to an M-incident face of an
owner in V. This assertion allows self-pairings and both possible
receiver owners; it does not require their other faces to be paired in
any particular way.

Each owner in V has exactly one original M normal interval. The two
endpoints of every such interval are paired to endpoints of intervals
in the same set. The nonempty union of these intervals is consequently
a closed union of components of the original M normal link. That link
is a connected circle, so the subset is the entire M circle. It contains
exactly |V|<=2 original intervals, contrary to degree(M)>=6.

This contradiction excludes every surviving split return. Together
with the complete common-return exclusion of Sections 278–280, it
exhausts the two unused rho face occurrences. The preceding reductions
therefore leave no mixed-flat configuration in the inherited paired
five-reservoir class. No distinct-neighbor assumption, marked-graph
connectedness, or closure of an external low-only region was introduced.

## 284. The precise class and theorem

Let N be a connected orientable compact 3-manifold with nonempty
boundary, every boundary component a closed surface of genus at least
two. Fix an actual finite ideal face-pairing triangulation of N, whose
ideal vertex links are exactly those boundary surfaces. Let E be its
actual global edge set, and suppose every original edge degree is at
least six, counting all local edge occurrences.

Suppose E=H disjoint union S with |H|<=5. In every tetrahedron choose
an actual vertex frame whose six global labels, in order
(12,13,14,34,24,23), are
 (R,A,B,O,A,B), with A,B in H, A!=B, R,O in E.
The chosen transverse pair can vary between tetrahedra. Axes may repeat
or also belong to H. Self-gluings and parallel face pairs are allowed
subject to the stated actual manifold conditions.

Then the same original triangulation has a genuine nondegenerate
hyperideal realization with totally geodesic boundary. This is a theorem
for the displayed paired-frame class with at most five actual reservoir
labels. It is not a theorem for arbitrary minimum-six triangulations.

## 285. Strict angles and the common positive length input

The original volume's Theorem 42.2 applies under exactly the manifold,
boundary and minimum-degree hypotheses above. Starting from normalized
angles a_o=2/d(P(o)), it transports vertex deficits across the actual
link surfaces while preserving every original edge sum. For a boundary
link S_nu the total deficit is -2*chi(S_nu)>0. The theorem gives strictly
positive angles, strict local vertex sums below pi, and every original
edge sum equal to 2*pi. No assumption that the initial unmodified angle
assignment already has strict vertex sums is used.

Restore the ideal vertices to the original finite face pairing. Its
faces are all paired, giving the closed triangulated pseudo-manifold
used by the hyperideal variational theorem; deleting the ideal vertices
and truncating recovers N. The positive angle structure satisfies the
hyperideal definition in Luo–Yang, *Volume and rigidity of hyperbolic
polyhedral 3-manifolds*, arXiv:1404.5365v2, Definition 6.1.
Their Theorem 6.3 and Theorem 1.4 supply a volume maximizer and a common
positive global generalized length vector producing its angles. Every
original edge still has angle sum 2*pi. Each tetrahedron is genuine or
has two opposite pi angles and four zero angles. These are the reused
inputs recorded in the original volume's Corollary 43.1; the present
corollary does not claim this existence theorem as new.

The source is https://arxiv.org/html/1404.5365v2; the relevant statements
are Theorem 1.4, Definition 6.1, and Theorem 6.3(a),(c).

## 286. Applying the completed flat exclusion

The fixed paired-frame certificate uses actual global edge labels, so
the common length vector automatically gives equal lengths in each
repeated transverse pair. No independent per-tetrahedron assignment or
new symmetry hypothesis is needed. All actual normal links are circles,
and all original degrees and face maps are unchanged.

For |H|<=4, the paired-reservoir volume's Theorem 172.1 already proves
realization under these same original hypotheses. For |H|=5, suppose
the variational length vector has at least one flat owner. It cannot
have only flat owners: every flat owner has zero local vertex deficit,
whereas the sum of the vertex deficits on each boundary link equals
-2*pi*chi(S_nu)>0 by the original edge equations and the link Euler
identity. Thus a nonempty flat set would give a mixed-flat configuration.
It satisfies the exact five-reservoir assumptions of Section 184 and
the subsequent original-length and face-transport reductions. The
completed exclusion through Section 283 rules this out. Hence every
tetrahedron is genuine.

## 287. Realization of the original face pairing

Each paired hexagonal face has the same three alternating original
edge lengths on its two sides, because the metric uses one length for
each actual global edge. A right-angled hyperbolic hexagon is determined
by those lengths, so the prescribed face correspondence is realized by
an isometry. Glue the genuine truncated hyperideal tetrahedra using
these isometries. The complete original angle sums 2*pi remove all cone
defects along the glued edges. The truncation faces meet the hexagonal
faces orthogonally and glue to the boundary surfaces without bending;
the boundary is totally geodesic. The actual manifold hypothesis ensures
the prescribed face quotient is N itself, including repeated labels and
self-gluings. This realizes the original triangulation as claimed.

No two-copy seed, separate genuine-witness premise, dual-girth condition,
prohibition of parallel face pairs, role balance or tetrahedron-transitive
action is added. The strict-angle construction and Luo–Yang existence
step are reused; the new five-reservoir input is the complete flat
exclusion. No example separating this class from every earlier criterion,
Lean certification, or unrestricted CFMP conclusion is claimed.

## 288. An eight-tetrahedron example and its exact scope

The following actual finite ideal face pairing has eight tetrahedra, five actual
global edges of degrees `(16,8,8,8,8)`, and one connected closed orientable
ideal-vertex link of genus 4. It is a connected orientable compact 3-manifold
after truncation. Every tetrahedron has a vertex-induced paired frame
`(R,A,B,O,A,B)`, and every simultaneous choice of paired frames across all eight tetrahedra
forces the union of their transverse reservoir labels to contain all five actual edges.

Thus this is a concrete strict separation from the paired-frame class with at
most four transverse reservoirs. Its minimum edge degree is 8, so it also lies
outside a blanket minimum-degree-at-least-9 hypothesis. No local label appears
three times, in any vertex frame. This is not a claim of separation from every
older geometric criterion, nor of minimality among all such triangulations.
No unrestricted CFMP or public priority claim is made.

## 289. Local labels and all sixteen face pairs

Use tetrahedra `P0,M0,P1,M1,P2,M2,P3,M3` with vertices `1,2,3,4`.
The label words in edge order `(12,13,14,34,24,23)` are:

| Type | Both copies' label word | Forced transverse pair |
|---|---|---|
| 0 | `(4,0,1,2,0,1)` | `{0,1}` |
| 1 | `(1,0,2,3,0,2)` | `{0,2}` |
| 2 | `(2,0,3,4,0,3)` | `{0,3}` |
| 3 | `(3,0,4,1,0,4)` | `{0,4}` |

`Fj` means the face opposite vertex `j`. A map `q1q2q3q4` sends vertex `j` to
`qj`; restrict it to the stated source face. The omitted vertex is mapped to the
omitted target vertex, so the listed full permutation also fixes its parity.

| Source | Target | Full vertex map |
|---|---|---|
| `P0:F3` | `P3:F1` | `3214` |
| `P0:F4` | `P3:F2` | `1432` |
| `M3:F1` | `M0:F4` | `4123` |
| `M3:F2` | `M0:F3` | `2341` |
| `P1:F3` | `M1:F3` | `1234` |
| `P1:F4` | `P0:F1` | `2341` |
| `M0:F1` | `P0:F2` | `2143` |
| `M0:F2` | `M1:F4` | `1432` |
| `P2:F3` | `M2:F3` | `1234` |
| `P2:F4` | `P1:F1` | `2341` |
| `M1:F1` | `P1:F2` | `2143` |
| `M1:F2` | `M2:F4` | `1432` |
| `P3:F3` | `M3:F3` | `1234` |
| `P3:F4` | `P2:F1` | `2341` |
| `M2:F1` | `P2:F2` | `2143` |
| `M2:F2` | `M3:F4` | `1432` |

Every one of the 32 faces appears once, and every map preserves all three edge
labels of its face. Give `P0,...,P3` positive vertex-order orientation and
`M0,...,M3` negative orientation. Each pairing has
`s(target)=-sign(map)*s(source)`, so it reverses the induced face orientations.
The dual graph is connected; for example the face table connects `P0` to
`P1,P3,M0`, then `P1` to `P2,M1`, `P2` to `M2`, and `P3` to `M3`.

## 290. Actual global edge equivalence classes

The exact classes below are computed from the face identifications. They are
also proved directly by the first-return cycles in Section 291: every displayed
occurrence is visited, while label preservation prevents classes from merging.
There is consequently no gap between a prescribed color and an actual edge.

- Edge `0`, degree 16: `M0:13`, `M0:24`, `P0:13`, `P0:24`, `M1:13`, `M1:24`, `P1:13`, `P1:24`, `M2:13`, `M2:24`, `P2:13`, `P2:24`, `M3:13`, `M3:24`, `P3:13`, `P3:24`.
- Edge `1`, degree 8: `M0:14`, `M0:23`, `P0:14`, `P0:23`, `M1:12`, `P1:12`, `M3:34`, `P3:34`.
- Edge `2`, degree 8: `M0:34`, `P0:34`, `M1:14`, `M1:23`, `P1:14`, `P1:23`, `M2:12`, `P2:12`.
- Edge `3`, degree 8: `M1:34`, `P1:34`, `M2:14`, `M2:23`, `P2:14`, `P2:23`, `M3:12`, `P3:12`.
- Edge `4`, degree 8: `M0:12`, `P0:12`, `M2:34`, `P2:34`, `M3:14`, `M3:23`, `P3:14`, `P3:23`.

The five lists are disjoint and exhaust all 48 local edges.

## 291. All oriented normal first-return circles

A state `T:a>b/Ff` is an ordered local edge with endpoints `a,b` and exiting
face `Ff`. Cross that face with its stated map, carry both endpoints in their
order, then exit through the other face containing the image edge. Each list
below is cyclic: its last state transitions to its first state exactly,
including the ordered endpoints. Every underlying local edge occurs once.

### Actual edge 0: 16 sectors

1. `M0:1>3/F2`
2. `M1:1>3/F2`
3. `M2:1>3/F2`
4. `M3:1>3/F2`
5. `M0:2>4/F1`
6. `P0:1>3/F4`
7. `P3:1>3/F4`
8. `P2:2>4/F3`
9. `M2:2>4/F1`
10. `P2:1>3/F4`
11. `P1:2>4/F3`
12. `M1:2>4/F1`
13. `P1:1>3/F4`
14. `P0:2>4/F3`
15. `P3:2>4/F3`
16. `M3:2>4/F1`

### Actual edge 1: 8 sectors

1. `M0:1>4/F2`
2. `M1:1>2/F3`
3. `P1:1>2/F4`
4. `P0:2>3/F4`
5. `P3:4>3/F1`
6. `P0:4>1/F2`
7. `M0:3>2/F4`
8. `M3:4>3/F2`

### Actual edge 2: 8 sectors

1. `M0:3>4/F1`
2. `P0:4>3/F1`
3. `P1:3>2/F1`
4. `P2:2>1/F3`
5. `M2:2>1/F4`
6. `M1:4>1/F3`
7. `P1:4>1/F2`
8. `M1:3>2/F4`

### Actual edge 3: 8 sectors

1. `M1:3>4/F1`
2. `P1:4>3/F1`
3. `P2:3>2/F1`
4. `P3:2>1/F3`
5. `M3:2>1/F4`
6. `M2:4>1/F3`
7. `P2:4>1/F2`
8. `M2:3>2/F4`

### Actual edge 4: 8 sectors

1. `M0:1>2/F3`
2. `M3:4>1/F3`
3. `P3:4>1/F2`
4. `P0:2>1/F3`
5. `P3:2>3/F4`
6. `P2:3>4/F2`
7. `M2:4>3/F2`
8. `M3:2>3/F1`

Thus each actual edge has a circular normal link, with no endpoint reversal.
The displayed cycles also cover every ordered-edge/exiting-face state: cyclic
shifts choose each of the 48 local edges, reversing the ordered endpoints
chooses either endpoint order, and reversing traversal chooses either exiting
face. These four choices per local edge give all 192 states. Each has the
same first-return length as its displayed cycle and no endpoint reversal.

## 292. Every vertex-link corner fan

There is one link triangle `(T,v)` for each of the 32 local tetrahedron vertices.
Its corner `(T;v,w)` is the endpoint at `v` of edge `vw`. Its two incident sides
come from the two faces containing that edge. The following ten cyclic lists
are all the actual link-vertex fans. Here `T:v>w` means the corner `(T;v,w)`;
it does not mean a directed edge in a new triangulation.

- Label 0, endpoint fan 0: `M0:1>3`, `M1:1>3`, `M2:1>3`, `M3:1>3`, `M0:2>4`, `P0:1>3`, `P3:1>3`, `P2:2>4`, `M2:2>4`, `P2:1>3`, `P1:2>4`, `M1:2>4`, `P1:1>3`, `P0:2>4`, `P3:2>4`, `M3:2>4`.
- Label 0, endpoint fan 1: `M0:3>1`, `M1:3>1`, `M2:3>1`, `M3:3>1`, `M0:4>2`, `P0:3>1`, `P3:3>1`, `P2:4>2`, `M2:4>2`, `P2:3>1`, `P1:4>2`, `M1:4>2`, `P1:3>1`, `P0:4>2`, `P3:4>2`, `M3:4>2`.
- Label 1, endpoint fan 0: `M0:1>4`, `M1:1>2`, `P1:1>2`, `P0:2>3`, `P3:4>3`, `P0:4>1`, `M0:3>2`, `M3:4>3`.
- Label 1, endpoint fan 1: `M0:4>1`, `M1:2>1`, `P1:2>1`, `P0:3>2`, `P3:3>4`, `P0:1>4`, `M0:2>3`, `M3:3>4`.
- Label 2, endpoint fan 0: `M0:3>4`, `P0:4>3`, `P1:3>2`, `P2:2>1`, `M2:2>1`, `M1:4>1`, `P1:4>1`, `M1:3>2`.
- Label 2, endpoint fan 1: `M0:4>3`, `P0:3>4`, `P1:2>3`, `P2:1>2`, `M2:1>2`, `M1:1>4`, `P1:1>4`, `M1:2>3`.
- Label 3, endpoint fan 0: `M1:3>4`, `P1:4>3`, `P2:3>2`, `P3:2>1`, `M3:2>1`, `M2:4>1`, `P2:4>1`, `M2:3>2`.
- Label 3, endpoint fan 1: `M1:4>3`, `P1:3>4`, `P2:2>3`, `P3:1>2`, `M3:1>2`, `M2:1>4`, `P2:1>4`, `M2:2>3`.
- Label 4, endpoint fan 0: `M0:1>2`, `M3:4>1`, `P3:4>1`, `P0:2>1`, `P3:2>3`, `P2:3>4`, `M2:4>3`, `M3:2>3`.
- Label 4, endpoint fan 1: `M0:2>1`, `M3:1>4`, `P3:1>4`, `P0:1>2`, `P3:3>2`, `P2:4>3`, `M2:3>4`, `M3:3>2`.

Every consecutive pair, including last-to-first, is joined by the relevant
face map from Section 289. All ten fans are disjoint. The two fans at edge 0 have
length 16; the other eight have length 8. They exhaust all 96 local corners,
and each corner has exactly two incident side identifications. Therefore every
link vertex has a circular fan and a disc neighborhood. All 96 triangle sides
are paired by a fixed-point-free involution, so every link-edge interior also
has a disc neighborhood, and the resulting surfaces have no boundary. These
are local manifold checks; Euler characteristic is not being used to assume
surface manifoldness.

For complete explicit connectivity evidence, the following 31 face-induced
identifications form a spanning tree on all 32 link triangles:

- `M0:1 ~ M3:2`
- `M0:1 ~ M3:4`
- `M0:1 ~ M1:1`
- `M3:2 ~ P3:2`
- `M3:2 ~ M2:4`
- `M3:4 ~ M0:3`
- `M3:4 ~ P3:4`
- `M1:1 ~ P1:1`
- `M1:1 ~ M2:1`
- `P3:2 ~ P0:2`
- `P3:2 ~ P2:3`
- `M2:4 ~ P2:4`
- `M0:3 ~ P0:4`
- `M0:3 ~ M1:3`
- `P1:1 ~ M1:2`
- `M2:1 ~ P2:1`
- `M2:1 ~ M3:1`
- `P2:3 ~ P1:4`
- `P2:4 ~ P3:3`
- `P2:4 ~ M2:3`
- `P0:4 ~ P1:3`
- `M1:2 ~ P1:2`
- `M1:2 ~ M0:4`
- `P2:1 ~ M2:2`
- `M3:1 ~ M0:2`
- `M3:1 ~ P3:1`
- `P1:4 ~ M1:4`
- `P3:3 ~ P0:1`
- `P3:3 ~ P0:3`
- `M2:3 ~ M3:3`
- `P1:3 ~ P2:2`

There is therefore exactly one actual ideal vertex and one connected link.
The link is orientable directly: order the three corner labels of triangle
`(T,v)` by increasing `w != v`, then give it sign `s(T)*(-1)^(v-1)`.
Every side identification reverses the induced side orientations. This is
checked directly on the 96 directed side occurrences by restricting the
signed vertex permutations in Section 289.

After the local and global surface checks, its cell counts are
`V=10`, `E=48`, `F=32`, hence `chi=10-48+32=-6=2-2*4`.
The sole link is a closed orientable genus-4 surface. Truncation produces the
required compact connected orientable 3-manifold: face interiors have ordinary
paired neighborhoods, every original edge has a circular normal link without
reversal, and the actual ideal vertex link is the verified surface above.

## 293. Exactly five transverse reservoirs under all vertex frames

Each type has exactly two equal opposite edge pairs, namely the pair labeled 0
and the pair labeled `i+1`. The remaining opposite pair has two distinct labels,
also distinct from `0,i+1`. Vertex permutations preserve opposite-pair incidence.
Hence a frame `(R,A,B,O,A,B)` with `A!=B` must use precisely the two equal pairs
as its transverse pairs. It follows that type `i` always forces `{0,i+1}`.

For a local word `(r,a,b,o,a,b)` with four distinct labels, exactly eight of the
24 vertex permutations yield paired frames. Their four words, each appearing
twice, are

- `(r,a,b,o,a,b)`;
- `(r,b,a,o,b,a)`;
- `(o,a,b,r,a,b)`;
- `(o,b,a,r,b,a)`.

The other sixteen permutations fail the required equalities. Across all 24
permutations there are twelve distinct words, each occurring twice, and every
word has multiplicity profile `(2,2,1,1)`. Indeed the unequal opposite pair
must remain the axial pair; its stabilizer in the 24 vertex permutations has
order eight. The four displayed words each occur twice. This accounts for all
192 vertex-frame choices over the eight tetrahedra, and no triple-repeated
label can appear by reframing.

The union of the forced pairs `{0,1},{0,2},{0,3},{0,4}` is all five proved-distinct
actual global edges. No reservoir set of size at most four works, even with
independent vertex-frame choices in every tetrahedron. Conversely, all five
work in the displayed frames. The minimum is exactly five.

For reference, there is already an elementary strict angle structure: assign
angle `pi/8` to each occurrence of edge 0 and `pi/4` to every other occurrence.
Each edge sum is `2*pi`, and every local vertex sum is `5*pi/8 < pi`. This checks
the angle-structure hypotheses directly. It does not by itself replace the
common-length, nondegeneracy, and face-isometry steps of a geometric realization.

## 294. Even multiplicities in the five cyclic-type family

This is a **structural obstruction only for the five cyclic types**
`sigma_i=(i,i+1,i+2,i+3,i+1,i+2)`, `i mod 5`, retaining their five distinct global
label names. It is not a nonexistence theorem for six-tetrahedron paired examples.

The face-color triples are `T_i={i,i+1,i+2}`. A copy of type `i` has two faces of
triple `T_i` and two of triple `T_(i+1)`. Every allowed color-preserving map
between faces with the same triple extends to an even permutation of the four
listed vertices. For same-type maps the possibilities are identity or `2143`.
For a low face of type `i` mapped to a high face of type `i-1`, the four full
maps are `4213`, `3124`, `2431`, `1342`, all even; reverse maps are even too.
These exhaust the possibilities because each triangle has three distinct colors.

Suppose an orientable face pairing exists, and let `d_i` be the number of
positive copies minus the number of negative copies of type `i`, where signs
are relative to its listed vertex order. Every allowed face map is even, so
it must pair opposite signs. Counting faces of triple `T_i` gives

`2*d_i + 2*d_(i-1) = 0`.

Thus `d_i=-d_(i-1)` around an odd five-cycle, forcing every `d_i=0`.
Every type multiplicity must be even. In particular `(2,1,1,1,1)` is impossible
in this specified family, independent of the face matching choices.
If all five original types occur and each nominal color is to be exactly one
actual global edge, each type occurs at least twice and every edge degree is
at least 12. This five-type family, with all five types present, therefore
cannot give a degree below nine. The eight-tetrahedron example instead uses
the four types in Section 289.

## 295. Genuine realization of this original triangulation

The verified truncation is a connected orientable compact 3-manifold with
one nonempty boundary component, a closed surface of genus four. Every
original edge degree is at least eight, hence at least six. Taking H to be
the five actual global edges and S empty gives the required vertex-induced
paired frames with distinct transverse labels. All hypotheses of the
realization theorem in Sections 284–287 are therefore satisfied.

Applying Section 287 gives a genuine nondegenerate hyperideal realization
of this same eight-tetrahedron face pairing with totally geodesic boundary.
No subdivision or separate per-tetrahedron length assignment is introduced.
The explicit strict angle structure in Section 293 is consistent with that
application, while the common-length and nondegeneracy conclusions use the
completed realization theorem.

This example requires five reservoirs under every simultaneous choice of
paired vertex frames and has minimum degree eight. It consequently separates
the displayed five-reservoir paired class from the at-most-four-reservoir
paired class on this original triangulation, and does not satisfy a blanket
minimum-degree-at-least-nine hypothesis. No claim of census novelty, global
minimality, or separation from every earlier geometric criterion is made.

## 296. Assumptions and statement

Retain the assumptions of Section 130: an actual finite ideal face
pairing with connected circular edge links, every original degree at
least six, fixed vertex-induced paired frames (R,A,B,O,A,B) with
A,B in H and A!=B, one common positive generalized length field, and
all original angle sums 2*pi. Axes can repeat and self-gluings are
allowed. There is no bound on the number of reservoir labels.

Assume a flat exists. Choose M maximal in cosh-length among all
pi-selected reservoir labels, and write m=x_M, as in Section 132.

**Theorem.** Every reservoir U with u=x_U>m-2 has a genuine occurrence.
Every flat transverse occurrence of such U has angle pi; consequently,
after the genuine witness is established, there are no flat transverse
occurrences of U at all. An axial U occurrence can still be flat zero
in an owner selecting a different, lower reservoir transversely; this
last possibility is not excluded by the theorem.

The result extends the genuine-witness step of Sections 184–186 to an
arbitrary number of reservoir labels. It does not extend the entire
five-reservoir return classification or assert general flat exclusion.

## 297. Transverse zero occurrences are impossible

Consider a flat owner with reservoir pair {U,A}. If it selects A,A,
the transverse-flat inequality of Lemma 111.1 requires

    a-u >= sqrt((r+1)*(o+1)) > 2.

Since A is selected, a<=m; whereas u>m-2. This is impossible.
If the owner instead selects its axes, each selected H axis has shifted
value at most m-1<u+1<u+a. Each selected special axis has shifted value
strictly below u+a by the fixed-pair special-edge barrier, Theorem112.1.
The product of the two shifted axis values is therefore strictly less
than (u+a)^2, contrary to the axial-flat condition of Section130.
Thus the only possible flat selection is the transverse U,U pair.
This proves the first assertion without any bound on |H|, including
u>m, when selecting U itself is also impossible by maximality of M.

## 298. Saturation and the original axial runs

Suppose U has no genuine occurrence. Then every original U slot is
flat and its complete edge equation gives exactly two pi slots.
Every transverse U slot has angle pi by Section297 above. Every axial
zero U slot belongs to an owner selecting a transverse reservoir P.

For a fixed unordered reservoir pair {P,Q}, there is at most one such
actual zero owner: only the strictly larger pair value can be selected,
and one owner already contributes two pi slots to that selected global
label. This uses the full selected-label equation, not an assumption
that different visits around U correspond to different owners.

Furthermore no axial-zero owner can have two U axes. If it did, its
transverse-selected value p and companion q would satisfy

    p-q >= sqrt((u+1)^2)=u+1.

Since q>1 and u>m-2, this gives p>u+2>m. But P is a pi-selected
reservoir, contradicting the definition of M. Therefore each actual
zero owner supplies at most one original axial U occurrence.

First suppose every U occurrence is axial. By the original-slot
transport in Section131, its fixed reservoir pair is constant around
the connected U circle. There is at most one zero owner, supplying at
most one U occurrence. Together with the exactly two pi slots, this
gives degree(U)<=3, contrary to minimum degree six.

Otherwise U has a transverse occurrence. Its flat owner selects U,U,
and its two transverse U slots exhaust the two pi slots in the complete
U equation. These are the only transverse occurrences of U. Every
other U occurrence is axial and zero.

Remove these two distinct original transverse intervals from the U
normal circle. The remaining original intervals form at most two
consecutive axial runs, possibly empty. The two removed intervals may
belong to the same tetrahedron, as indeed they do; they remain two
separate intervals in the actual normal link. The complementary
reservoir pair is constant along each run by Section131. The preceding
fixed-pair argument allows at most one zero owner in each run, and the
no-two-U-axes argument allows at most one U occurrence of that owner.
Thus each run has at most one original interval, giving

    degree(U)<=2+1+1=4.

This again contradicts minimum degree six. Repeated visits, parallel
face pairings and self-gluings change which endpoints are paired, but
not the count of original intervals in these complete runs. Therefore
U must have a genuine occurrence.

A flat transverse U owner would already contribute 2*pi to U and
leave no positive genuine contribution. Hence no such owner remains.
This proves the theorem. QED.

## 299. The exact six-reservoir boundary

The genuine escape tau=(Z,M,C,D,M,C) of Theorem134.1 witnesses four
distinct reservoir labels. The upper-gap theorem of Section182 supplies
another actual label U outside those four with u>T(m,z)>m-2. The theorem
above witnesses U without using reservoir cardinality.

For exactly six labels H={M,C,D,Z,U,V}, the only possibly unwitnessed
label is therefore V, and it must satisfy v<=m-2. If V is unwitnessed,
every transverse-selected flat owner must select V, since all five
other labels are genuinely witnessed. There is at most one such actual
owner. Every flat axial zero slot of any label belongs to that owner,
if it exists. Transverse zero slots in axial-flat owners are still
possible and are not discarded.

This identifies the first five-label cardinality issue precisely:
the witness of the upper-gap label does not require five labels, but
Section187's conclusion that every reservoir is witnessed, and hence
that every flat owner selects its axes, does not follow for six from
this argument. Even if the sixth label is witnessed, its additional
face roles remain outside the published five-label case analysis.
No actual realization of the residual low-label pattern, six-label
flat exclusion, or six-label geometric realization is claimed here.

## 300. Exact assumptions and conclusion

Retain the actual paired-framework hypotheses of Section130 and a
nonempty flat set, with exactly six distinct reservoir labels. Use the
genuine escape and upper-gap label to write

    H={M,C,D,Z,U,V}, tau=(Z,M,C,D,M,C),
    m>=1+c+d, z>=1+m+c, p_M=1, p_Z=0,
    u>T(m,z)>m-2.

Here p counts original flat pi slots. The arbitrary-reservoir upper-
witness theorem supplies genuine witnesses for M,Z,U and excludes all
their flat transverse occurrences. C,D already occur in genuine tau.
Suppose V is the only unwitnessed reservoir, so p_V=2 and v<=m-2.
All degrees and counts below refer to the original face quotient.

**Theorem.** After naming the larger of C,D by A and the smaller by B,
with values a,b, the following necessary conclusions hold:

1. a>=1+v+b, in particular a>b and a>v.
2. Exactly two actual axial-flat owners have V transversely. One has
   frame (A,V,B,Q,V,B); the other has frame (U,V,L,T,V,L), where L=A or B.
   They are distinct. Their selected A and U slots are unique, so
   p_A=p_U=1 and m-2<u<=m.
3. If an owner F_V selects V transversely, it is unique and has
   transverse companion B. The degree of V is six or seven. Without
   F_V its degree is exactly six.
4. The original source flat sigma=(M,C,D,O,C,D) and the two owners
   above have their other selected axial labels O,Q,T in {B,V} union S.
   Across these three actual owners there is at most one B pi slot.
   If F_V exists none of O,Q,T is V; otherwise they contain at most
   two V slots, counting repetitions.

Thus an unwitnessed sixth label must be a degree-six or degree-seven
actual edge with this specific flat-owner configuration. In particular,
if all six reservoir edges have degree at least eight, every reservoir
is genuinely witnessed and every flat owner selects its axes. This
last conclusion is not an exclusion of axial flats or a six-reservoir
geometric-realization theorem.

## 301. Count every V occurrence

A transverse-selected flat must select an unwitnessed reservoir, because
its two pi slots exhaust that label's original equation. Consequently
it must select V, and there is at most one such actual owner F_V.
A flat axial zero occurrence of V must belong to F_V. This owner cannot
have V on both axes: the transverse-flat inequality would require
v-l>=sqrt((v+1)^2)=v+1 with l>1. Thus F_V has at most one axial V slot.

If F_V exists, its two transverse V pi slots exhaust p_V=2; all axial
V slots are zero and belong to F_V. If F_V does not exist, all axial V
slots have angle pi, and there are exactly two of them.
Every other V occurrence is transverse zero in an axial-flat owner.
Let k be the number of these actual owners. Each contributes exactly
two transverse V slots, irrespective of any additional V axis.
Therefore the exact degrees are

    degree(V)=2+2*k+t,  t in {0,1}, if F_V exists;
    degree(V)=2+2*k,                 otherwise.

The second formula counts any axial V slots in these same owners
separately, as original slots. Minimum degree six implies k>=2 in
both cases.

All transverse labels of any flat belong to {C,D,V}: M,Z,U have no
flat transverse occurrences. Each of the k owners thus has pair {V,C}
or {V,D}. It differs from sigma, whose pair is {C,D}.

## 302. Every such owner uses U or the larger low label

Every axial-flat owner has at least one selected H axis: two special
axes violate the fixed-pair special barrier. None of the k owners has
a selected M axis, since sigma already uses the unique M pi slot.
None has selected Z, since p_Z=0. Their selected H axes therefore lie
in {C,D,U,V}.

Consider one without a U axis, with pair {V,L}, where L=C or D. Let
X be its selected H axis of largest cosh value x. Its other axis is
either H-valued and at most x, or special and has shifted value less
than v+l. The axial-flat product implies respectively

    (x-1)^2 >= (v+l)^2, or (x-1)*(v+l) > (v+l)^2.

In either case x>=1+v+l. Thus X is neither V nor L; it must be the
other member of {C,D}. The latter is strictly larger than L and V.
Such an owner therefore selects the larger low label A and has pair
{V,B}, with a>=1+v+b.

Since A is witnessed by tau, p_A<=1. There is at most one owner of
this kind. Since U is witnessed, p_U<=1, and there is at most one of
the k owners with a U axis. These two possibilities exhaust them.
Thus k<=2. Together with k>=2 this forces exactly one of each kind.
In particular A and U each supply one selected slot and no others.
The selected U value is at most m by maximality of M, giving
m-2<u<=m. The precise frames in the statement follow by interchanging
the axial positions when necessary.

Substituting k=2 into the exact degree formulas proves degree(V)=6 or7,
and degree(V)=6 if F_V is absent. If F_V exists its companion is C orD,
since the other three reservoirs cannot be transverse in any flat.
It cannot be A, because transverse selection would require v>a,
whereas a>=1+v+b. Its companion is therefore B.

## 303. Remaining selected slots and open cases

The three owners sigma, the selected-A owner and the selected-U owner
are distinct, by their transverse pairs or their unique selected slots.
Their respective first axes M,A,U exhaust the pi budgets of these three
witnessed labels. Z cannot be selected. Their other axes O,Q,T are
therefore in {B,V} union S. The genuine B witness gives p_B<=1, so at
most one of those original slots has label B, including repeated labels
within or between owners. The complete V equation gives at most two V
pi slots; if F_V exists its transverse slots already use both.

No number of low-only genuine owners is bounded here. The special
opposite axes, the actual remaining face pairings and every genuine
angle equation are still to be satisfied. The theorem does not assert
that these necessary residual roles are realizable. It leaves open
both the displayed saturated degree-six/seven cases and the separate
case in which all six reservoir labels are genuinely witnessed.

## 304. Statement and exact input

Retain the actual finite paired-frame face quotient of Section130:
connected circular normal links, every original degree at least six,
frames (R,A,B,O,A,B) with distinct transverse A,B in H, common positive
generalized lengths, and every original angle equation 2*pi. Assume
exactly six reservoir labels and a nonempty flat set. No original slot,
repeated axis, self-gluing or special edge is removed.

**Theorem.** Every reservoir has a genuine occurrence. Every flat owner
therefore selects its axial pair. This is a structural theorem; it
neither excludes all axial flats nor gives six-reservoir realization.

Choose the maximal pi-selected reservoir M and genuine escape

    tau=(Z,M,C,D,M,C), H={M,C,D,Z,U,V},
    m>=1+c+d, z>=1+m+c, p_M=1, p_Z=0.

The upper-gap theorem182 supplies U outside M,C,D,Z with u>T(m,z)>m-2.
The arbitrary-reservoir upper-witness theorem296–298 witnesses U and
excludes every flat transverse occurrence of M,Z,U. C,D are witnessed
in tau. Consequently only V can be unwitnessed. If it is, v<=m-2.

We first prove a complete-star lemma that allows additional low labels,
then show that an unwitnessed V would violate it. Only the weak escape
inequalities above are used; the five-label strict-source theorem191
is not imported.

## 305. One upper-gap label cannot have value at most m

**Lemma.** In the same actual framework suppose the reservoir set is
{M,Z,U} disjoint union L, where C,D belong to L, every B in L has
1<b<=m-2, and U is genuinely witnessed with u>m-2. Suppose the escape
and pi data of Section304 hold and Z has no flat transverse occurrence.
Then u>m. Labels in L need not be genuinely witnessed.

**Proof.** Suppose u<=m. Every H value except Z is at most m, so Z is
largest. We have m>3,z>m+2,c,d<m-2. All transverse Z owners are genuine.
An owner with axial Z and pair {M,B}, b<m, is genuine: axial selection
would select Z, transverse M selection would spend two pi slots of M,
and transverse B selection would require b>m. An axial Z owner with
pair {M,U} is also genuine, since both M and U are witnessed and hence
neither can be selected transversely. These are all axial Z owners
whose genuineness will be used. Other axial Z zero slots are not
assumed absent.

Take the maximal axial Z run through tau with pair {M,C}. Each owner
is genuine and has at most one Z axis, since (z-1)^2>=(m+c)^2 would
make two Z axes flat. At each such slot the exact individual response
has positive coefficients with sum greater than one:

    2*sqrt(m*m-1)/(m+c)*sqrt((z-1)/(z+1))>1.

The arctangent addition formula gives theta_Z+2*beta_M>pi.
A wholly axial Z circle would have at least six such owners and exceed
the complete M/Z genuine capacity 3*pi. Thus the run is proper.
Each boundary owner has frame (B,Z,A,Q,Z,A), {A,B}={M,C}.
For H axes q<=z; for special axes q<1+z+a. Hence q<1+z+a.
The transverse Z cosine numerator is strictly increasing in q and at
1+z+a equals

    [a+z*(1+z+a)]*(1+a+b-z)<=0.

Each boundary Z angle exceeds pi/2. Both distinct boundary slots must
belong to one owner rho, since two owners would exceed Z's 2*pi budget.
Their total is greater than pi. The run's axial angle sum is less than
pi and its doubled transverse M sum is at most pi; summing its strict
per-owner inequality forces exactly one run owner, tau.
The return is (C,Z,M,Q,Z,M) or (M,Z,C,Q,Z,C).

The complete special-star exclusions of Section176 apply to pairs
{Z,M} and {Z,C}. Their required inputs are: genuine transverse Z
owners, m,z>3, z>2*c+3, actual M/Z capacities pi and 2*pi, special
minimum degree six, and every other axis below 1+z+a. All hold here.
Those weighted-star arguments make no claim that all L labels are
witnessed. Thus no special axis occurs in an owner of either pair.

For the companion-C return, genuineness gives
q>(z-c)^2/(m+1)-1>=m, so Q=Z. Any owner of pair {Z,C} with an axis
other than Z has that value at most m; the same cosine numerator bound
makes its two Z angles obtuse, so it must be rho. The alternative with
both axes Z has four Z angles of cosine
z*(c+1)/(2*z*z+c-1)<1/2; its expense exceeds 4*pi/3 and cannot coexist
with rho. Thus rho is the only owner with that pair. Its residual
{Z,Z,C} faces transport every Z slot back into rho, in either axial or
transverse role. Together with tau this closes at most four original
Z intervals, contradicting connectedness and degree six.
Hence rho=(C,Z,M,Q,Z,M), with Q in H and q>c.

No owner uses only M and Z: the standard two-value vertex response of
Section157, with all values greater than three, makes its six-angle
M/Z expense greater than pi. It would differ from tau and rho, each
already costing more than pi of M/Z. Now any owner with pair {Z,M}
has only H axes and at least one axis B other than M,Z, with b<=m.
Its other axis r<=z. Put

    L0=(z+m)^2-(b-1)*(r-1),
    J0=(b+1)*(r+1)-(z-m)^2.

Both are positive, and the exact expansion gives

    L0-2*J0 >= (m-3)*(m+1)+(z-m)*(m-1)+3*(z-m)^2 >0.

The transverse-sum coefficient kappa squared exceeds 8/9, so its four
M/Z transverse slots cost more than pi. Together with tau and rho,
this forbids every such owner other than rho itself.

If Q=M or Z, the residual face multiset {Z,M,Q} forces its next Z slot
back into this unique pair-{Z,M} owner, closing at most four intervals.
If Q=B in L, B!=C because q>c. An axial Z target would have pair {M,B};
it is genuine as checked above and costs theta_Z+2*beta_M>pi by b<=m-2.
A transverse Z target either has pair {Z,M}, hence is rho, or pair
{Z,B} with an M axis. The latter is genuine and costs

    theta_M+2*gamma_Z>pi,

since its positive response coefficients have sum
2*sqrt(z*z-1)/(z+b)*sqrt((m-1)/(m+1))>1.
Either new role differs from tau and rho by its fixed pair and violates
the remaining M/Z budget. Thus this Q case also closes the short circle.
These exclusions hold for every B in L, including an unwitnessed one.
Only Q=U remains: rho=(C,Z,M,U,Z,M).

Across rho's residual {Z,M,U} faces, the Z roles are axial with pair
{M,U}, transverse with pair {Z,M} (only rho), or transverse with pair
{Z,U} and an M axis. If the third role never occurs, the complementary
arc of the complete Z circle is a single axial {M,U} run with
n=degree(Z)-3>=3 original intervals. All are genuine as checked above.
At each such interval its M response is

    beta=atan(A*t)+atan(B*t), t=cot(theta/2),
    A=(sqrt(m*m-1)+sqrt(u*u-1))/(m+u)*sqrt((z-1)/(z+1))>1/2,
    B=(sqrt(m*m-1)-sqrt(u*u-1))/(m+u)*sqrt((z-1)/(z+1))>=0.

For theta>=pi/2, theta+beta>pi/2. Otherwise t>1 and
cot(theta)=(t-1/t)/2<t/2<A*t, giving the same strict bound.
Assigning one beta per axial Z interval uses at most the two actual
M slots in its owner, including an owner with both axes Z. Therefore
these intervals cost more than 3*pi/2 of M/Z, while tau and rho leave
less than pi. This contradiction forces a third distinct genuine owner
eta=(M,Z,U,Q,Z,U). Its actual M/Z expense obeys theta_M+2*gamma_Z<pi.

## 306. The exact third-owner contradiction

Here 1<u<=m<z, u>m-2, and q<q0=1+z+u. Set

    k=z+u, h=z-u, alpha=sqrt((m-1)/(m+1)),
    L=k*k-(m-1)*(q-1)>0, J=(m+1)*(q+1)-h*h>0.

The exact axial and transverse responses give

    tan(theta/2)^2=alpha^2*J/L,
    gamma=atan(A*t)+atan(B*t), t=cot(theta/2),
    A+B=2*sqrt(z*z-1)*alpha/k, A*B*t*t=(h/k)*L/J.

Both A,B are positive. Increasing q to q0 strictly decreases L/J:
L remains positive up to q0, where L0=k*(k-m+1)>0, while J is positive
and increasing. Thus

    A+B+A*B*t*t > F(u)
      =2*sqrt(z*z-1)*alpha/(z+u)
       +(z-u)*(z+u-m+1)/[(m+1)*(z+u+2)-(z-u)^2].

On u<=v<=m the first term of F decreases. The second numerator
N(v)=(z-v)*(z+v-m+1)>0 has derivative m-1-2*v<3-m<0.
Its denominator J0(v)>0 has derivative m+1+2*(z-v)>0.
Consequently F(u)>=F(m). At m, J0(m)=(z+1)*(3*m+2-z)>0 and

    F(m)=2*sqrt(z*z-1)*alpha/(z+m)+(z-m)/(3*m+2-z).

Both terms increase strictly in z on m+2<=z<3*m+2: their derivative
signs follow from m*z+1>0 and 2*m+2>0 respectively. Hence

    F(m)>sqrt(1-4/(m+1)^2)+1/m>1.

For the final inequality, the squared comparison with 1-1/m reduces
to (m-1)*(2*m*m+m+1)>0. All denominators are positive since m>3.
Therefore A+B+A*B*t*t>1. If gamma>=pi/2 then theta+2*gamma>pi.
Otherwise the positive tangent branch yields

    tan(gamma)=(A+B)*t/(1-A*B*t*t)>t,

and again theta+2*gamma>pi. This contradicts eta's actual complete-
budget bound. The lemma is proved. No absent axial Z zero occurrence
was silently replaced by a genuine one: every used run has its fixed
pair and genuineness checked, and the connected residual arc cannot
exit that pair without the expressly enumerated transverse boundary.

## 307. The saturated sixth label forces the forbidden u<=m case

Suppose V is unwitnessed. Every transverse-selected flat must select V,
and there is at most one such owner F_V. Every axial zero V slot lies
in F_V. If F_V exists it has at most one V axis, since two would require
v-b>=v+1 for a positive companion. Its two transverse slots exhaust
p_V=2. Without F_V exactly two axial V slots have angle pi and no axial
V slot is zero.

Let k be the number of axial-flat owners with V transverse. Each has
two such slots. The exact V degree is 2+2*k+t, t in {0,1}, when F_V
exists, and 2+2*k otherwise. Therefore k>=2.
Every one has pair {V,C} or {V,D}, since M,Z,U have no flat transverse
occurrence. It differs from the source sigma, whose pair is {C,D}.
It cannot select M, already selected once in sigma, or Z. It has at
least one selected H axis, by the special-edge barrier. Its selected
H axes are consequently among C,D,U,V.

If such an owner has no U axis, choose its largest selected H value x.
For pair {V,B}, where B=C or D, the other axis is H-valued and at most
x, or special with shifted value less than v+b. Axial flatness implies
x>=1+v+b in either case. Thus X is neither V nor B; it is the other
low label A, strictly larger than both. Every owner without U therefore
selects that same larger label A. Since A is witnessed, p_A<=1, so
there is at most one such owner. Also p_U<=1, giving at most one owner
with U selected. Since k>=2, both kinds must occur and U is selected.
Maximality of M gives u<=m.

Apply the complete-star lemma with L={C,D,V}. All its premises hold:
c,d<m-2 and v<=m-2; U is genuinely witnessed and u>T>m-2;
Z has no flat transverse occurrence; the original source data remain
unchanged. The lemma instead gives u>m, contradiction.
Thus V is witnessed too. No flat can select a transverse pair of any
reservoir, since that would exhaust a witnessed edge's equation.
Every flat therefore selects its axes, proving the theorem.

## 308. Remaining six-reservoir problem

This proves six-reservoir genuine witnesses and axial-flat classification
without a seed, degree-eight strengthening, or extra incidence premise.
It excludes the entire unwitnessed-sixth branch, not all flat fields.
With all six labels witnessed, the additional reservoir may exceed the
upper-gap threshold and participate in new genuine return roles. The
published five-reservoir role exhaustion does not cover those roles.
No six-reservoir realization or unrestricted CFMP conclusion follows.

## 309. Statement and dependencies

Retain the actual finite paired-framework hypotheses: connected circular
normal links, degree at least six, fixed distinct-transverse paired frames,
one common positive generalized length vector and every original 2*pi
edge equation. Assume exactly six reservoir labels and a nonempty flat set.
Choose the maximal-selected escape and upper-gap label as before:

    H={M,C,D,Z,U,V}, tau=(Z,M,C,D,M,C),
    m>=1+c+d, z>=1+m+c, p_M=1, p_Z=0,
    u>T(m,z)>m-2.

Use the six-reservoir witness theorem: every reservoir is genuinely
witnessed and every flat selects its axes. Hence each reservoir has at
most one original flat pi slot. The arbitrary-reservoir upper-witness
result also excludes every flat transverse occurrence of any label
whose value exceeds m-2. The one-upper-gap lemma allows arbitrarily
many other labels of value at most m-2.

**Theorem.** There are at most two actual flat tetrahedron owners.
This is a bound on the whole original flat set, not just one face
component. It does not bound the number of genuine owners, remove
external low-only regions, or prove six-reservoir flat exclusion.

## 310. The low sixth-label case

Suppose v<=m-2. The one-upper-gap complete-star lemma, with low set
{C,D,V}, gives u>m. Thus neither U nor Z can be a selected flat axis.
Nor can M,Z,U be transverse in a flat. Every flat's reservoir pair
therefore lies in {C,D,V}. The source sigma, with pair {C,D}, uses the
unique M pi slot. Every other flat avoids M entirely as a selected axis.

Any such other flat has at least one selected H axis, since two special
axes violate the fixed-pair barrier. Choose its largest selected H
value x. Its other axis is either H-valued at most x or special with
shifted value strictly below the sum of its transverse pair values.
The axial-flat product implies that x is at least one plus that sum.
Thus X lies outside its transverse pair and is numerically larger than
both members. Since its available H axes and pair all lie in {C,D,V},
it selects the unique numerically largest member A of this three-label
set and has the other two labels as its pair. If the numerical maximum
is tied, there is no such owner at all.

The genuine A witness gives p_A<=1, so at most one such additional
owner exists. Together with sigma this gives at most two flat owners.
An A pi slot already used by sigma only reduces this bound.

## 311. The two-upper-gap case first gives at most three

Suppose v>m-2. No flat has any of M,Z,U,V transversely, so every flat
has reservoir pair {C,D}. At least one selected H axis is present in
each flat. Choose its largest selected H value x. As in Section310,
axial flatness implies x>=1+c+d, so X cannot be C or D. It is not Z,
which has p_Z=0. Thus every flat selects at least one of M,U,V.

Each of these three genuinely witnessed labels has at most one pi
slot, so there are at most three actual flat owners. Suppose there
are exactly three. Each must use exactly one of the available M,U,V
slots, and all three are used. Therefore p_M=p_U=p_V=1 and
m-2<u,v<=m. Every H label except Z has value at most m, and z>m.
For each flat, its selected label X in {M,U,V} is its largest H axis:
its other axis cannot use another one of M,U,V, since the three owners
already require all three distinct slots. Hence each chosen X satisfies
x>=1+c+d as well as x>m-2.

## 312. Each of the three selected axes forces a different dominant Z run

Fix one of these three flat owners and its selected X. Its complete
genuine angle budget is pi, and its only flat X occurrence is its one
axial pi slot: flat transverse X occurrences are excluded by x>m-2,
and axial zeros do not occur because every flat selects its axes.

Its entire X circle cannot be axial. Otherwise its fixed pair is
{C,D}; there are g=degree(X)-1>=5 genuine X occurrences. They have
distinct owners, since two X axes with x>=1+c+d would be flat.
The dominant-axis inequality gives 2*theta_X+beta_C+beta_D>pi for each.
Their actual C/D expense is therefore greater than
2*g*pi-4*pi>=6*pi, contrary to complete C/D capacity 4*pi.

Thus the maximal axial X run through the selected flat is proper.
Its two distinct transverse boundary X slots are genuine; their angles
sum to at most pi, so choose one at most pi/2. Actual face transport
gives an owner (W,X,A,B,X,A), {A,B}={C,D}. The exact transverse-X
cosine numerator increases with w and at w0=1+x+a equals

    [a+x*(1+x+a)]*(1+a+b-x)<=0.

Consequently w>=1+x+a>m, because x>m-2 and a>1. The special-edge
barrier excludes W in S. Among H only Z has value greater than m,
so W=Z. This owner gives a dominant axial Z run with pair {X,A}.
For distinct X in {M,U,V}, these fixed pairs are distinct: A belongs
to {C,D}, disjoint from all three X labels.

## 313. The actual Z circle allows at most one such dominant run

All Z occurrences are genuine: every flat is axial-selected, p_Z=0,
and flat transverse Z occurrences have already been excluded. A wholly
axial Z circle would have one fixed pair, so cannot contain the three
distinct pairs just obtained. Their runs are proper.

At a boundary of a dominant axial Z run with pair {A,B}, the genuine
receiver has frame (B,Z,A,Q,Z,A). Every H axis is at most z and every
special axis has q<1+z+a, so in all cases q<1+z+a. The increasing
transverse-Z numerator at this upper endpoint is

    [a+z*(1+z+a)]*(1+a+b-z)<=0.

Thus the boundary Z angle is greater than pi/2. The complete Z budget
permits only one actual owner rho with two such transverse slots.
Every dominant run uses both distinct slots of rho as its boundaries.

At a transverse Z slot of rho, let its companion be A and its axes
B,Q. The two complementary face pairs are {A,B} and {A,Q}.
If both sides bordered dominant axial runs, dominance would give
z>=1+a+b and z>=1+a+q, hence

    (z-a)^2 >= (b+1)*(q+1).

This contradicts the genuine strict inequality for rho. Each of its
two original Z slots therefore supports at most one dominant-run
boundary incidence. One proper run already uses both. Two distinct
proper dominant runs are impossible, a contradiction.

The proposed three-flat case is excluded. Combined with Sections310–311,
there are at most two actual flat owners, as claimed. QED.

The argument allows arbitrary repeated axes, repeated visits in the
original normal circles and distinct-face self-gluings. The remaining
one-flat and two-flat six-reservoir configurations still require new
joint geometric and face-transport arguments; this theorem alone does
not assert that either residual configuration exists or is impossible.


## 314. Two strict upper labels in the actual six-edge distinct-frame case

Retain the original finite paired-frame quotient with complete connected
normal circles, minimum original degree six, common positive lengths and
all original angle equations 2*pi. Suppose there are exactly six actual
global edge labels, no special edges, and every paired frame
(R,A,B,O,A,B) has four distinct labels R,A,B,O. Assume a nonempty flat set.
The public six-witness theorem through Section 308 makes every label
genuinely witnessed and every flat axial-selected. Each label has at most
one flat pi slot. The arbitrary upper-witness theorem excludes every
flat transverse occurrence of a label with value greater than m-2.

Choose the maximal-selected reservoir M and its usual genuine escape

    tau=(Z,M,C,D,M,C),
    m>=1+c+d>3, z>=1+m+c>m+2, p_M=1, p_Z=0.

All lower-case values are coshes of original shared lengths. M has total
genuine angle pi. Z occurs in no flat owner, so its total genuine angle
is 2*pi. The argument below uses only the stated response formulas and
original circles; it does not invoke the five-label exhaustion.

**Theorem.** Some actual edge other than Z has value greater than m.
Consequently, after naming it U, the entire six-edge distinct-frame
mixed-flat configuration has the following form:

    H=E={M,C,D,Z,U,V}, u>m, z>m,
    sigma=(M,C,D,V,C,D), 1<v<=m,
    (m-1)*(v-1)>=(c+d)^2.

Sigma is the unique flat owner and the only owner of transverse pair
{C,D}. Thus both its M and V axial runs consist of one original interval.
This is a structural reduction, not exclusion of the remaining flat.

## 315. A uniform expense for a third-role owner

We first isolate the response estimate used below. Let m>3,z>m+2,
1<q<=m and r<=m. Suppose (M,Z,Q,R,Z,Q) is genuine. Write theta for
its axial M angle and gamma for its transverse Z angle. Then

    theta+2*gamma>pi.                                      (315.1)

For q<=m-2 the positive response coefficients have sum

    2*sqrt(z*z-1)/(z+q)*sqrt((m-1)/(m+1))>1.

This follows by comparison with z=m,q=m-2, where the sum is one.
Hence gamma>atan(cot(theta/2)) and (315.1) follows.

For m-2<q<=m, use the exact rational comparison already proved in
Sections 202–204; its scalar argument is reproduced here to state its
full domain. Set k=z+q, h=z-q>0 and alpha=sqrt((m-1)/(m+1)). The actual
other axis satisfies r<=m<r0=1+z+q. Define

    L=k*k-(m-1)*(r-1)>0,
    J=(m+1)*(r+1)-h*h>0,
    t=cot(theta/2),
    A/B=[sqrt(z*z-1) +/- sqrt(q*q-1)]/k*alpha.

A,B are positive, and

    A+B=2*sqrt(z*z-1)*alpha/k,
    A*B*t*t=h/k*L/J.

L/J strictly decreases as r increases to r0. At that endpoint,

    L0=k*(k-m+1)>0,
    J0=(m+1)*(k+2)-h*h>0.

The latter follows by increasing J from its positive actual value.
Therefore

    A+B+A*B*t*t > F(q),
    F(q)=2*sqrt(z*z-1)*alpha/(z+q)
       +(z-q)*(z+q-m+1)/[(m+1)*(z+q+2)-(z-q)^2].

On the interval from q to m, the first term decreases. The numerator
N(x)=(z-x)*(z+x-m+1) is positive and has derivative
m-1-2*x<3-m<0. The positive denominator J0(x) strictly increases,
with derivative m+1+2*(z-x)>0. Hence F(q)>=F(m), including q=m.

    J0(m)=(z+1)*(3*m+2-z)>0,
    F(m)=2*sqrt(z*z-1)*alpha/(z+m)+(z-m)/(3*m+2-z).

Both terms strictly increase in z on m+2<=z<3*m+2. Thus

    F(m)>sqrt(1-4/(m+1)^2)+1/m>1.

The final comparison follows by squaring positive terms; the required
numerator is

    (2*m-1)*(m+1)^2-4*m*m
      =(m-1)*(2*m*m+m+1)>0.

Consequently A+B+A*B*t*t>1. If gamma>=pi/2, then gamma>atan(t).
Otherwise its tangent is (A+B)*t/(1-A*B*t*t)>t. In either case
2*gamma>pi-theta, proving (315.1). No label-count premise is present
in this scalar estimate, and r<=m is stronger than its needed bound.

## 316. A unique strict upper label is impossible

Suppose, for contradiction, every actual edge other than Z has value
at most m. Every Z slot is genuine. Along the maximal axial Z run
through tau the pair is {M,C}. At each owner the individual response
has positive coefficients whose sum exceeds one:

    2*sqrt(m*m-1)/(m+c)*sqrt((z-1)/(z+1))>1.

The same elementary arctangent comparison gives theta_Z+2*beta_M>pi.
Four-distinctness gives one axial Z slot per such owner. If the whole
Z circle were axial, degree at least six would contradict the entire
M/Z capacity 3*pi. Hence the run is proper.

At each of its transverse boundary slots, write the receiver as
(B,Z,A,Q,Z,A), with {A,B}={M,C}. Its other axis obeys q<=m<z.
The transverse-Z cosine numerator increases with q. At q=1+z+a it
is

    [a+z*(1+z+a)]*(1+a+b-z)<=0.

Since the actual q is strictly below this endpoint, its Z angle is
strictly greater than pi/2. Each such owner has two equal transverse
Z slots. The two distinct run boundaries therefore belong to a single
actual owner rho; two distinct owners would exceed Z's total 2*pi.
The original rho Z expense exceeds pi. Every run owner costs more
than pi in M/Z, so the remaining capacity below 2*pi forces the run
to consist of exactly tau.

The possible companion-C return (M,Z,C,Q,Z,C) has

    (m+1)*(q+1)>(z-c)^2>=(m+1)^2,

so q>m. The only possible label would be Z, but four-distinctness
forbids that repeated label. Therefore

    rho=(C,Z,M,Q,Z,M),

where Q is distinct from M,Z,C and q<=m. All owners with fixed pair
{Z,M} have their two axes at most m. For any such genuine owner with
axis values r,s<=m, put

    L=(z+m)^2-(r-1)*(s-1),
    J=(r+1)*(s+1)-(z-m)^2.

Then

    L-2*J=3*z*z-2*z*m+3*m*m-3*r*s-r-s-3
          >=3*z*z-2*z*m-2*m-3>0.

Define the squared paired coefficient

    K=((sqrt(z*z-1)+sqrt(m*m-1))/(z+m))^2.

The transverse angle sum is beta_Z+beta_M=2*atan(sqrt(K*L/J)),
and K>8/9 since m,z>3. Hence
K*L/J>16/9, and its four transverse M/Z slots cost more than pi.
Tau already costs more than pi. Two distinct pair-{Z,M} owners
would consequently exceed 3*pi. Thus rho is the unique such owner,
and all owners other than tau,rho have M/Z capacity strictly below pi.

The unused rho faces have labels {Z,M,Q}. Across such a face, a Z
slot is axial with pair {M,Q}, transverse with pair {Z,M}, or
transverse with pair {Z,Q} and an M axis. The second role can only
be rho. Every owner of the third role is genuine and satisfies (315.1),
so it is impossible under the remaining capacity below pi.

Actual continuation now makes the other arc between rho's two Z
slots one axial run with fixed pair {M,Q}. It contains
n=degree(Z)-3>=3 original Z intervals, and all its owners are genuine.
For any such slot of angle theta and its transverse M angle beta,

    beta=atan(A*cot(theta/2))+atan(B*cot(theta/2)),
    A=[sqrt(m*m-1)+sqrt(q*q-1)]/(m+q)*sqrt((z-1)/(z+1)),
    B=[sqrt(m*m-1)-sqrt(q*q-1)]/(m+q)*sqrt((z-1)/(z+1))>=0.

Because q>1 and q<=m,
sqrt(q*q-1)>sqrt((m-1)/(m+1))*(q-1), giving A>1/2.
For theta>=pi/2, theta+beta>pi/2 is immediate. For theta<pi/2,
t=cot(theta/2)>1 and cot(theta)=(t-1/t)/2<t/2<A*t, giving the same
strict bound. Four-distinctness makes these n owners distinct and
each charge theta+beta uses only one of its two original M slots.
Their actual M/Z expense exceeds n*pi/2>=3*pi/2, contradicting the
remaining capacity below pi. The supposed unique upper label cannot
exist. This proves the first assertion.

## 317. The whole six-edge source pair is unique

Name a second edge of value greater than m as U. Since C,D<m-2,
U lies outside M,C,D,Z. The source's other axis must be the sixth
label V: it is distinct from M,C,D by the frame hypothesis and cannot
be U or Z, which exceed the maximal selected value. Thus v<=m and
sigma=(M,C,D,V,C,D).

If v<=m-2, Section 310 shows that every other flat would select the
largest of {C,D,V}, with the remaining two as its transverse pair.
Its other selected axis cannot be M (the source uses its only pi
slot), U,Z (unselected), either transverse label, or the already used
largest low label. Four-distinctness and the six actual labels exhaust
all possibilities, so no second flat exists.

If v>m-2, every flat has transverse pair {C,D}, since M,V,Z,U have
no flat transverse occurrence. Its distinct selected axes can only
be M and V: U,Z are unselected, and C,D belong to its pair. Both M
and V pi slots are already used by sigma. Again no second flat exists.

Finally any owner with pair {C,D} has two distinct axes from
{M,V,Z,U}. Since z,u>m>=v, their shifted product is at least
(m-1)*(v-1)>=(c+d)^2. Such an owner would be flat and hence is sigma.
The one-flat and one-CD-owner conclusions are global actual-owner
statements. They do not eliminate the remaining changed-pair source
faces or prove six-reservoir realization. QED.


## 318. Complete-circle upper bound for the largest actual length

In an actual finite paired quotient with four distinct labels in every
frame, connected normal circles of degree at least six and complete
angle equations 2*pi, let X be a label whose entire star is genuine.
Suppose x is a largest actual cosh length. Let a1>=a2 be the two
largest values at distinct other actual labels. Then

    x < 1+a1+a2.

This is a necessary actual-star bound, not a scalar existence claim.
For the mixed-flat six-edge setting with Z,U>m and all remaining
values at most m, it gives

    abs(z-u)<m+1.

The stronger one-sided Z bound derived from the source run may also
be retained. No six-reservoir flat exclusion follows from these gaps.

## 319. The dominant-axis estimate

For a genuine frame (r,a,b,o,a,b) with r>=1+a+b, write
s=a+b, delta=a-b, T=(r-1)/(r+1),
K=(sqrt(a*a-1)+sqrt(b*b-1))^2/s^2 and lambda=sqrt(K*T).
Let theta be the r angle and S=beta_a+beta_b. The exact response is
S=2*atan(lambda*cot(theta/2)). We claim 2*theta+S>pi.

Define

    F(r)=[2*(r-1)-T*delta^2]/s^2.

The genuine half-angle square is
T*[(r+1)*(o+1)-delta^2]/[s^2-(r-1)*(o-1)].
It increases strictly with o wherever its denominator is positive,
so tan(theta/2)^2>F(r), its value at o=1. This comparison remains
valid when F(r) is negative. On r>=s+1, F increases because
F'(r)=2*[1-delta^2/(r+1)^2]/s^2>0, and lambda increases.
At r0=s+1, put D=s*(s+2) and H=a*a+b*b-2>0. Then

    1-F(r0)=2*H/D,
    lambda(r0)=(sqrt(a*a-1)+sqrt(b*b-1))/sqrt(D)>H/D.

The strict inequality follows from D>H and
sqrt(a*a-1)+sqrt(b*b-1)>=sqrt(H). Consequently
F(r)+2*lambda>1 throughout the domain.

If theta>=pi/2 the claimed estimate is immediate from S>0.
Otherwise t=cot(theta/2)>1. If lambda>=1/2, then
lambda*t>(t-1/t)/2=cot(theta).
If lambda<1/2, the proved inequality gives
F(r)>1-2*lambda>0 and t^2<1/F(r)<1/(1-2*lambda),
which gives the same strict comparison. Thus
atan(lambda*t)>pi/2-theta, proving 2*theta+S>pi.
This establishes the per-owner estimate without an extra angle premise.

## 320. The original-circle proof of the maximum gap

First suppose X has a transverse occurrence with companion A and
axes R,O. The four labels are distinct. The genuine inequality gives

    (x-a)^2<(r+1)*(o+1).

Since x>=a, it follows that

    x<a+sqrt((r+1)*(o+1))
      <=a+1+(r+o)/2.

For any three distinct other labels, a+(r+o)/2<=a1+a2:
if A carries a largest value, each of r,o is at most a2; otherwise
A is at most a2 and the average of r,o is at most a1. Hence the
claimed strict bound follows.

Otherwise every X occurrence is axial. Connectedness transports one
fixed pair {A,B} around its whole circle. Four-distinctness gives
one X slot per owner, so there are n=degree(X)>=6 distinct genuine
owners. Suppose x>=1+a+b. The established dominant-axis response
inequality (the same one used in Sections 209 and 312) gives at each
owner

    2*theta_X+beta_A+beta_B>pi.

Summing uses the actual X angles exactly once and only half of the
two transverse A/B slots per owner. Thus

    n*pi < 2*sum(theta_X)+sum(beta_A+beta_B)
         <= 4*pi+(2*pi+2*pi)/2 = 6*pi.

This contradicts n>=6. Therefore x<1+a+b<=1+a1+a2.
All charging is by original slots at distinct actual owners; repeated
visits or distinct-face self-pairings do not change the count. QED.

## 321. Application and exact scope

In the current mixed-flat six-edge class, the maximal selected value
is m, while Z and another edge U exceed m. Every flat is axial-selected,
and no flat has a transverse occurrence of a value greater than m-2.
Consequently both Z and U have wholly genuine stars. Apply the lemma
to the larger of z,u. The two largest other values are the smaller of
z,u and m. This proves abs(z-u)<m+1, including ties among lower values.

In particular a local source-front angle assignment with u>=z+m+1
cannot extend to the actual complete U star. It may still be a correct
counterexample to a weaker scalar relaxation that omitted this bound.

## 322. The inventory-one combined-angle obstruction

Retain the six-edge, four-distinct-label paired setting of Sections
314–321: original shared positive lengths, complete connected normal
circles, degree at least six, and original angle sums 2*pi. The unique
flat owner is sigma=(M,C,D,V,C,D), with selected axes M,V. Its transverse
C,D angles are zero, so the genuine M,V capacities are pi each and the
genuine C,D,Z,U capacities are 2*pi each. Lower-case letters denote
coshes of the corresponding shared lengths.

The following conditional obstruction concerns three distinct genuine
owners with the precise roles

    tau=(Z,M,C,D,M,C),
    rho=(U,V,D,C,V,D),
    eta=(M,V,D,Z,V,D).                              (322.1)

Here eta has axes M,Z. Call (322.1) inventory one. No assertion that
every remaining configuration has this inventory is made.

**Theorem (repo-derived).** Suppose the inventory obeys

    c,d,v>1, m>1+c+d, 1<v<=m-2,
    z>1+m+c, m<u<z+m+1,
    (m-1)*(v-1)>=(c+d)^2.                          (322.2)

Require all six strict genuine inequalities

    Lt=(m+c)^2-(z-1)*(d-1)>0,
    Jt=(z+1)*(d+1)-(m-c)^2>0,
    Lr=(v+d)^2-(u-1)*(c-1)>0,
    Jr=(u+1)*(c+1)-(v-d)^2>0,
    Le=(v+d)^2-(m-1)*(z-1)>0,
    Je=(m+1)*(z+1)-(v-d)^2>0.                      (322.3)

Assume also the bad-eta condition and the retained actual partial
M-angle budget, respectively,

    theta_M(eta)+theta_Z(eta)<=pi,
    2*beta_M(tau)+theta_M(eta)<=pi.                (322.4)

Then, writing S=beta_V+beta_D at rho and eta,

    theta_D(tau)+2*S(rho)+2*S(eta)>3*pi.           (322.5)

Consequently no actual configuration satisfying these premises exists:
the nine original slots in (322.5) have genuine V/D capacity at most
pi+2*pi. The scalar implication (322.2)–(322.5) is proved below without
using the C,Z,U budgets. Both inequalities in (322.4), including the
whole stated partial M budget, remain premises throughout.

For clarity, the paired response formulas used in the proof are
reproduced here. Put

    K=(sqrt(v^2-1)+sqrt(d^2-1))/(v+d),
    w=sqrt((d-1)*Jt/[(d+1)*Lt]),
    x=K*sqrt(Lr/Jr), y=K*sqrt(Le/Je),
    A=[sqrt(m^2-1)+sqrt(c^2-1)]/(m+c)*sqrt(Lt/Jt),
    B=[sqrt(m^2-1)-sqrt(c^2-1)]/(m+c)*sqrt(Lt/Jt).

Then

    theta_D(tau)=2*atan(w), beta_M(tau)=atan(A)+atan(B),
    S(rho)=2*atan(x), S(eta)=2*atan(y),
    tan(theta_M(eta)/2)^2=(m-1)*Je/[(m+1)*Le],
    tan(theta_Z(eta)/2)^2=(z-1)*Je/[(z+1)*Le].       (322.6)

All genuine angles lie in (0,pi); A,B are positive since m>c. The
M budget forces beta_M(tau)<pi/2 and therefore

    Ht=(m+c)*Jt-(m-c)*Lt>0,
    4*(m-1)^2*Lt*Jt*Je<=Ht^2*Le.                  (322.7)

These two conditions are equivalent to the M budget: on this branch
tan(beta_M)=2*sqrt(m^2-1)*sqrt(Lt*Jt)/Ht and the budget is
tan(beta_M)<=cot(theta_M(eta)/2). Squaring positive quantities yields
(322.7). Similarly the bad-eta condition is equivalent to

    (m+1)*(z+1)*Le^2>=(m-1)*(z-1)*Je^2.           (322.8)

These are exact reformulations, not replacements by weaker budgets.
The generalized hyperideal angle conventions agree with Luo–Yang,
*Volume and rigidity of hyperbolic polyhedral 3-manifolds*,
[arXiv:1404.5365v2](https://arxiv.org/html/1404.5365v2).
The inventory-specific implication here is a deduction from the
displayed paired formulas and original-slot capacities.

## 323. The bad-eta bound and a genuine rho endpoint

Set p=sqrt((m-1)*(z-1)) and q=sqrt((m+1)*(z+1)). The axial
half-angle product makes bad-eta equivalent to q*Le>=p*Je, or

    p*q<=v^2+d^2+2*v*d*(q-p)/(q+p).                (323.1)

Indeed expand q*[(v+d)^2-p^2]>=p*[q^2-(v-d)^2] and divide
by p+q. Since z>m>1,

    q/p<=(m+1)/(m-1), 0<(q-p)/(q+p)<=1/m.

It follows that

    z<Zb(m,v,d):=1+[v^2+d^2+2*v*d/m]/(m-1).       (323.2)

Here p*q>(m-1)*(z-1), and Zb increases with each positive v,d.

We first show c<m/2, using neither the flat product nor the M budget.
If c>=m/2, then m>4, d<m/2-1 and v<=m-2. The right side of
(323.1) is strictly less than (m-2)^2*(5/4+1/m). But

    p*q>(m-1)*(z-1)>(m-1)*(m+c)>=3*m*(m-1)/2,
    3*m*(m-1)/2-(m-2)^2*(5/4+1/m)
      =(m^3+10*m^2-4*m-16)/(4*m)>0,

a contradiction. The last numerator is positive for m>4 because
m^3-4*m>0 and 10*m^2-16>0.

At u0=z+m+1 the rho L numerator is

    Lr0=(v+d)^2-(z+m)*(c-1)=Le+z*(m-c)-m*c+1>Le>0.

The strict comparison uses c<m/2 and z>m. Increasing u from its
actual value to u0 decreases Lr linearly but keeps it positive, while
Jr increases from its positive actual value. Hence the whole scalar
interpolation remains genuine. Furthermore

    d(Lr/Jr)/du=[-(c-1)*Jr-(c+1)*Lr]/Jr^2<0.

Thus S(rho) strictly decreases. It suffices to prove (322.5) at this
genuine endpoint. This is a comparison of rho's response with fixed
other parameters, not a claim that the changed u preserves a global
shared-length metric or any unrelated star.

## 324. The source D angle exceeds 2*pi/3

The exact axial M cosine of eta is N_e/D_e, where

    D_e=m^2+v^2+d^2+2*m*v*d-1,
    N_e=2*v*d+m*(v^2+d^2)-(m^2-1)*z.

Its v-derivative has sign numerator

    (N_e)_v*D_e-N_e*(D_e)_v
      =2*(m^2-1)*[-d^3+d*m*z+d*v^2+d+m*v+v*z]>0. (324.1)

Indeed d<m-2<m and z>m. Increasing v to m-2 decreases theta_M(eta)
and preserves the M budget. Le increases, and Je stays positive since
1<v,d<m and z>m. Tau is unchanged. For this lemma only, take v=m-2;
no bad-eta or flat-product premise is needed along this interpolation.

Put q=tan(theta_D(tau)/2)^2 and

    delta=(m-c)*(d-1)/[(m+c)*(d+1)], 0<delta<1.

The positive branch Ht>0 in (322.7) gives q>delta. Solving
q=(d-1)*Jt/[(d+1)*Lt] for z gives z=Zn/Zd, with

    Zd=(d^2-1)*(q+1),
    Zn=q*(m+c)^2*(d+1)+(m-c)^2*(d-1)+(q-1)*(d^2-1),
    LeN=(m+d-2)^2*Zd-(m-1)*(Zn-Zd),
    JeN=(m+1)*(Zn+Zd)-(m-d-2)^2*Zd,
    Bq=(m+c)*(d+1)*q-(m-c)*(d-1),
    F(q)=Bq^2*LeN-4*(m-1)^2*(d^2-1)*q*JeN.       (324.2)

The full M budget implies F(q)>=0. More explicitly, if
G=Ht^2*Le-4*(m-1)^2*Lt*Jt*Je, substitution gives the identity

    F(q)=G*(d-1)^2*Zd/Lt^2,

whose multiplier is positive. F is a cubic polynomial in q; write
F(q)=sum_{j=0}^3 f_j(m,c,d)*q^j.

If q<=3, put h=(3-q)/(q-delta)>=0. Then q=Qn/Qd, where

    Qn=(m-c)*(d-1)*h+3*(m+c)*(d+1),
    Qd=(m+c)*(d+1)*(1+h)>0.

Define the following polynomial after the indicated substitutions:

    PD(a,b,e,h)=-sum_{j=0}^3 f_j*Qn^j*Qd^(3-j),
    c=1+a, d=1+b, m=3+a+b+e.                      (324.3)

Here a,b,e>0. The complete coefficient identity in Section 331
expresses PD as 1,450 monomials with positive integer coefficients,
including constant 56623104. Consequently PD>0 even when h=0.
Since PD=-Qd^3*F(Qn/Qd), this contradicts F(q)>=0. Thus q>3 and

    theta_D(tau)>2*pi/3, w>sqrt(3).                (324.4)

We will also use a simpler consequence of (324.1). Its d counterpart
is obtained by interchanging v,d, and the z derivative of N_e/D_e
is negative. Increasing v,d to m-2 and decreasing z to m increases
this algebraic cosine. The derivative signs hold on that entire
comparison rectangle, with positive D_e; no genuine endpoint is
required. At the endpoint

    D_e-2*N_e=(m+1)*(7*m-9)>0.

Hence theta_M(eta)>pi/3, and the retained M budget gives

    beta_M(tau)<pi/3.                             (324.5)

## 325. A strict quarter bound for the source companion

The source flat inequality and v<=m-2 give

    (c+d)^2<=(m-1)*(m-3)=(m-2)^2-1,
    c+d<m-2, d<m-c-2<m-3, m>4.                   (325.1)

For the last assertion use c+d>2 and m>3. Define the source M
cosine, as an algebraic function of z,d, by

    C(z,d)=N(z,d)/sqrt(D(z)*D(d)),
    N(z,d)=c*(z+d)+m*(z*d+c^2-m^2+1),
    D(t)=t^2+m^2+c^2+2*t*m*c-1.                  (325.2)

It increases strictly in both z,d. For example, its z-derivative
has the sign of

    N_z*D(z)-N*(z+m*c)
      =(m^2-1)*[c*(d*z+m^2-c^2+1)+m*(d+z)]>0.

The d derivative is symmetric. Positivity holds for z,d>1 and m>c,
including outside the genuine angle domain.

For this first bound set d0=m-c-1 and z0=Zb(m,m-2,d0). Then
d<d0 and z<z0, so the actual source cosine is less than C(z0,d0).
Suppose c>=m/4. Since c<m-2, write

    m=4+b, b>0, c=[m/4+(m-2)*a]/(1+a), a>=0.

Define the degree-six polynomial in c

    A4(m,c)=m^2*(m-1)*[D(z0)*D(d0)-4*N(z0,d0)^2]
           =sum_{j=0}^6 A4_j(m)*c^j,
    P4(a,b)=4^6*sum_{j=0}^6 A4_j(m)
              *[m/4+(m-2)*a]^j*(1+a)^(6-j), m=4+b. (325.3)

The factor in A4 cancels its denominators exactly. Section 331 gives
the complete expansion of P4: 69 positive integer coefficients and
positive constant 314572800. Hence P4>0, so A4>0. Since D(z0),D(d0)
are positive, |C(z0,d0)|<1/2. The actual source cosine is smaller,
contradicting (324.5). Therefore

    c<m/4.                                       (325.4)

## 326. Coarse exact length bounds

Solving w^2>3 from (324.4) for z gives

    z>Z3(m,c,d)
      :=[(2*d+1)*(m^2+c^2)+(2*d+4)*m*c+d^2-1]
           /[2*(d^2-1)].                         (326.1)

In fact (d-1)*Jt-3*(d+1)*Lt=4*(d^2-1)*(z-Z3). This Z3 increases
with c and decreases with d. Its d derivative is

    -[(m^2+c^2)*(d^2+d+1)+m*c*(d^2+4*d+1)]/(d^2-1)^2<0.

Combine z<Zb, z>Z3, c>1, v<=m-2 and d<m-3. They require

    Zb(m,m-2,m-3)-Z3(m,1,m-3)>0.

This difference equals Nm/[2*m*(m-4)*(m-2)*(m-1)], where

    Nm=2*m^5-34*m^4+124*m^3-121*m^2-109*m+192.

If 4<m<=11, substitute m=(11+4*a)/(1+a), a>=0. Direct expansion is

    -(1+a)^5*Nm((11+4*a)/(1+a))
      =900*a^5+13383*a^4+74765*a^3+187297*a^2
         +184925*a+26296>0,

contradicting the positive difference. Thus m>11.

If v<=6, the same monotonicity requires
Zb(m,6,m-3)-Z3(m,1,m-3)>0. This difference is

    -Nv/[2*m*(m-4)*(m-2)*(m-1)],
    Nv=18*m^4-192*m^3+833*m^2-1331*m+576,
    Nv(11+b)=18*b^4+600*b^3+7565*b^2+43131*b+94714>0.

If d<=6, it instead requires Zb(m,m-2,6)-Z3(m,1,6)>0, equal to

    -Nd/[70*m*(m-1)],
    Nd=13*m^4-67*m^3+242*m^2-3618*m+1680,
    Nd(11+b)=13*b^4+505*b^3+7469*b^2+46597*b+92320>0.

Both are contradictions since b=m-11>0 and all denominators are
positive. We have obtained the strict necessary bounds

    m>11, v>6, d>6.                              (326.2)

The positive weighted mean K therefore exceeds sqrt(35)/6. By
bad-eta and z>m,

    Le/Je>=sqrt((m-1)*(z-1)/[(m+1)*(z+1)])
         >(m-1)/(m+1)>5/6,
    y^2>(35/36)*(5/6)=175/216>81/100.

The last difference is 1/5400, so y>9/10. This is not the stronger
inequality y>1 or S(eta)>pi/2.

## 327. A stronger affine source-companion bound

Put ell(m)=6*m/25-3/2. For m>11, one has 1<ell(m)<m/4. We prove

    c<ell(m).                                    (327.1)

Suppose instead ell(m)<=c<m/4, and now set

    d0=m-c-2, z0=Zb(m,m-2,d0).

By (325.1), d<d0, and then (323.2) gives z<z0. The algebraic source
cosine increases in both variables, so its actual value is below
C(z0,d0). Define

    AA(m,c)=m^2*(m-1)^2*[D(z0)*D(d0)-4*N(z0,d0)^2]
           =sum_{j=0}^6 AA_j(m)*c^j.              (327.2)

This is a polynomial with its denominators exactly canceled. The
contrary domain is parametrized by

    m=11+b, b>0, c=[ell(m)+(m/4)*a]/(1+a), a>=0.

Define

    PA(a,b)=100^6*sum_{j=0}^6 AA_j(m)
              *[ell(m)+(m/4)*a]^j*(1+a)^(6-j), m=11+b. (327.3)

Its complete expansion in Section 331 has 77 positive integer
coefficients and constant 2579520001436709588480. Thus PA>0 and
AA>0. As before |C(z0,d0)|<1/2, contrary to (324.5). This proves
(327.1) as a consequence of the original premises.

## 328. A strict endpoint rho ratio

Work at the genuine endpoint u0=z+m+1 of Section 323. Set

    lambda=21/5, Q=v^2+d^2, T=v*d,
    ac=(1+lambda)*c+(lambda-1)=(26*c+16)/5,
    C0=ac*(m+1)+2*lambda*(c+1).

Direct expansion gives

    Lr-lambda*Jr=(1+lambda)*Q+2*(1-lambda)*T
                    -ac*(z+m)-2*lambda*(c+1).

Substitute the strict upper bound z<Zb. The resulting T coefficient
is 2*(1-lambda)-2*ac/[m*(m-1)]<0. Hence using T<=Q/2 gives

    Lr-lambda*Jr>[2-ac*(m+1)/(m*(m-1))]*Q-C0.      (328.1)

The coefficient of Q is positive: (327.1) gives

    ac<156*m/125-23/5<5*m/4,
    (m+1)/(m-1)<6/5,

so that coefficient exceeds 1/2. The inequalities z>Z3 and z<Zb,
together with T<=Q/2, also give

    Q>m*(m-1)/(m+1)*(Z3(m,c,d)-1).

Since Z3 decreases with d and d<d0=m-c-2, (328.1) implies

    Lr-lambda*Jr>G(m,c),
    G=[2*m*(m-1)/(m+1)-ac]*(Z3(m,c,d0)-1)
                         -ac*(m+1)-2*lambda*(c+1). (328.2)

The denominator

    5*(m+1)*(c-m+1)*(c-m+3)

is positive because c<m/4 and m>11 make its last two factors
negative. Multiplying G by this denominator gives the polynomial

    BR(m,c)=sum_{j=0}^4 BR_j(m)*c^j.

For m=11+b, b>0 and c=[1+ell(m)*a]/(1+a), a>=0, define

    PR(a,b)=50^4*sum_{j=0}^4 BR_j(m)
              *[1+ell(m)*a]^j*(1+a)^(4-j), m=11+b. (328.3)

This parametrization covers 1<c<ell(m); allowing a=0 only adds
the boundary c=1. Section 331 gives all 30 coefficients of PR,
each a positive integer, with constant 1376937500000. Thus G>0 and
Lr>(21/5)*Jr. Endpoint genuineness gives Jr>0, so

    x^2=K^2*Lr/Jr>(35/36)*(21/5)=49/12>4,
    x>2.                                         (328.4)

## 329. The tangent branch and the original-slot contradiction

We have x>2, y>9/10 and w>sqrt(3). Therefore xy>1. The ratio
R=(xy-1)/(x+y) increases strictly with either positive variable:
its derivatives are (y^2+1)/(x+y)^2 and (x^2+1)/(x+y)^2. Hence

    R>8/29>2-sqrt(3)>sqrt(1+w^2)-w.               (329.1)

The middle comparison follows from sqrt(3)>50/29, equivalently
2523>2500. The last uses strict decrease of sqrt(1+w^2)-w.

Since xy>1, atan(x)+atan(y) lies in (pi/2,pi), and

    tan(atan(x)+atan(y)-pi/2)=R,
    tan(pi/4-atan(w)/2)=sqrt(1+w^2)-w.

Both arguments compared here lie in (0,pi/2). Thus (329.1) proves
atan(x)+atan(y)>3*pi/4-atan(w)/2, equivalently

    2*atan(w)+4*atan(x)+4*atan(y)>3*pi.

This is (322.5) at the endpoint. The original u has a strictly larger
rho transverse sum by Section 323, so (322.5) holds there as well.

Its actual charge consists of one axial D slot of tau, two V and two
D slots of rho, and two V and two D slots of eta. The owners are
distinct, and the paired repetitions are distinct original occurrences.
Thus the charge is a subset of the full genuine V/D sum, at most
pi+2*pi. Additional owners cannot decrease it. This contradiction
proves the theorem.

## 330. Scope of the conditional exclusion

The theorem excludes exactly the actual inventory (322.1) under
(322.2)–(322.4), including eta's axes M,Z and its bad-eta inequality.
It does not force that inventory, handle eta with axes Z,U, or treat
the other source inventory or all remaining source-face configurations.
In particular it is not a six-edge flat-exclusion theorem or a general
geometric-realization theorem. Scalar constraints are used only as
necessary conditions; no scalar assignment is claimed to construct a
face pairing or complete actual normal circles.

The endpoint comparison changes only a local response for the purpose
of a lower bound. The complete actual partial M budget and all six
strict genuine tests are explicit premises. The proof does not replace
the combined V/D charge by a separate V-only assertion or assume
S(eta)>pi/2. The maximum-gap result supplies the relevant actual
upper gap u<z+m+1; no lower gap or missing C,Z,U capacity is used
to strengthen the scalar implication.

## 331. Complete exact polynomial coefficient identities

The following finite identities specify every coefficient of the four
polynomials in (324.3), (325.3), (327.3) and (328.3). They use only
integer coefficients and the rational substitutions displayed there.
They can be reconstructed by ordinary multiplication and collection
of powers; no angle approximation or sampling is involved.

For PD, a row i,j,k : (r0,r1,r2,r3) denotes

    a^i*b^j*e^k*(r0+r1*h+r2*h^2+r3*h^3).

PD is the sum of exactly the rows below. All omitted triples have
zero coefficient. Within a row all four h coefficients, including
zeros, are given. There are 1,450 nonzero coefficients, with minimum
8, maximum 7064551424 and constant 56623104. Every displayed entry
is nonnegative, and the constant is positive, proving PD>0 on the
nonnegative orthant and hence on the domain used in Section 324.

PD coefficient rows:

    0,0,0 : (56623104,0,0,0)
    0,0,1 : (127401984,0,0,0)
    0,0,2 : (123863040,0,0,0)
    0,0,3 : (68124672,0,0,0)
    0,0,4 : (23224320,0,0,0)
    0,0,5 : (5031936,0,0,0)
    0,0,6 : (677376,0,0,0)
    0,0,7 : (51840,0,0,0)
    0,0,8 : (1728,0,0,0)
    0,1,0 : (297271296,21233664,0,0)
    0,1,1 : (634650624,56033280,0,0)
    0,1,2 : (585990144,63111168,0,0)
    0,1,3 : (306266112,39739392,0,0)
    0,1,4 : (99256320,15344640,0,0)
    0,1,5 : (20450304,3730176,0,0)
    0,1,6 : (2618496,558720,0,0)
    0,1,7 : (190656,47232,0,0)
    0,1,8 : (6048,1728,0,0)
    0,2,0 : (712900608,110493696,3932160,0)
    0,2,1 : (1439662080,272498688,11010048,0)
    0,2,2 : (1256718336,285769728,13172736,0)
    0,2,3 : (620040192,166920192,8822784,0)
    0,2,4 : (189242880,59586048,3634176,0)
    0,2,5 : (36606336,13358592,947712,0)
    0,2,6 : (4385088,1844160,153600,0)
    0,2,7 : (297696,144000,14208,0)
    0,2,8 : (8784,4896,576,0)
    0,3,0 : (1031831552,262750208,19529728,196608)
    0,3,1 : (1965522944,602099712,50266112,606208)
    0,3,2 : (1613897728,583324672,54960128,798720)
    0,3,3 : (745632768,312867584,33427456,588800)
    0,3,4 : (211800960,101911168,12419072,266752)
    0,3,5 : (37841472,20719808,2901760,76544)
    0,3,6 : (4150432,2579936,419200,13696)
    0,3,7 : (255568,180992,34496,1408)
    0,3,8 : (6776,5520,1248,64)
    0,4,0 : (1003438080,377929728,44089344,917504)
    0,4,1 : (1798610944,798912512,103456768,2564096)
    0,4,2 : (1380946944,708151296,102333440,3033088)
    0,4,3 : (591376896,344376064,55803904,1985536)
    0,4,4 : (153967104,100678336,18395648,788736)
    0,4,5 : (24868128,18161952,3768832,195584)
    0,4,6 : (2425104,1980752,471296,29760)
    0,4,7 : (130112,119904,33120,2560)
    0,4,8 : (2928,3096,1008,96)
    0,5,0 : (690806784,366751744,59785216,1929216)
    0,5,1 : (1162846208,708712448,126625792,4836352)
    0,5,2 : (828746240,567787520,111894016,5070848)
    0,5,3 : (324597248,246337984,53828096,2900224)
    0,5,4 : (75892928,63253664,15410048,988928)
    0,5,5 : (10760240,9828800,2688128,205888)
    0,5,6 : (894320,900032,278976,25568)
    0,5,7 : (39216,44088,15696,1728)
    0,5,8 : (672,864,360,48)
    0,6,0 : (345554944,253517824,54194176,2410496)
    0,6,1 : (545581056,442655744,102329344,5351936)
    0,6,2 : (357486336,315536256,79500032,4893696)
    0,6,3 : (125749760,119564128,33029376,2393856)
    0,6,4 : (25664416,26182512,7974976,680576)
    0,6,5 : (3061088,3358072,1135328,114080)
    0,6,6 : (202880,241600,91520,10832)
    0,6,7 : (6464,8512,3664,512)
    0,6,8 : (64,96,48,8)
    0,7,0 : (126849024,128415744,34570240,1986560)
    0,7,1 : (187844608,199554048,57283072,3843840)
    0,7,2 : (111664896,123956544,38314880,3000832)
    0,7,3 : (34371648,39846112,13354752,1219520)
    0,7,4 : (5873592,7131776,2607040,277152)
    0,7,5 : (551184,706152,283376,35008)
    0,7,6 : (25824,35392,15736,2256)
    0,7,7 : (448,672,336,56)
    0,8,0 : (34080768,48263168,15898624,1132544)
    0,8,1 : (47436288,65411328,22645504,1869952)
    0,8,2 : (25080768,34406208,12672064,1210880)
    0,8,3 : (6495648,8995416,3553408,392000)
    0,8,4 : (869824,1231024,524800,66640)
    0,8,5 : (56896,83392,38608,5624)
    0,8,6 : (1408,2176,1104,184)
    0,9,0 : (6599680,13460992,5306368,455168)
    0,9,1 : (8684032,15470976,6315904,623168)
    0,9,2 : (3956000,6609632,2836640,321024)
    0,9,3 : (808576,1315344,599072,77488)
    0,9,4 : (75200,122000,59352,8736)
    0,9,5 : (2560,4224,2208,368)
    0,10,0 : (892416,2752512,1274368,128768)
    0,10,1 : (1123328,2574784,1216576,140256)
    0,10,2 : (416976,836568,410768,53824)
    0,10,3 : (59712,112384,57968,8592)
    0,10,4 : (2880,5280,2880,480)
    0,11,0 : (79488,401216,214528,25088)
    0,11,1 : (97792,286192,153952,20368)
    0,11,2 : (26464,62752,34696,5168)
    0,11,3 : (1984,4256,2448,408)
    0,12,0 : (4160,39488,24000,3200)
    0,12,1 : (5184,19072,11504,1720)
    0,12,2 : (768,2112,1296,216)
    0,13,0 : (96,2352,1600,240)
    0,13,1 : (128,576,384,64)
    0,14,0 : (0,64,48,8)
    1,0,0 : (226492416,0,0,0)
    1,0,1 : (445906944,0,0,0)
    1,0,2 : (371589120,0,0,0)
    1,0,3 : (170311680,0,0,0)
    1,0,4 : (46448640,0,0,0)
    1,0,5 : (7547904,0,0,0)
    1,0,6 : (677376,0,0,0)
    1,0,7 : (25920,0,0,0)
    1,1,0 : (1130102784,79036416,0,0)
    1,1,1 : (2105671680,182255616,0,0)
    1,1,2 : (1661681664,175767552,0,0)
    1,1,3 : (721428480,92160000,0,0)
    1,1,4 : (186393600,28454400,0,0)
    1,1,5 : (28694016,5186304,0,0)
    1,1,6 : (2439360,517824,0,0)
    1,1,7 : (88416,21888,0,0)
    1,2,0 : (2561409024,383188992,12386304,0)
    1,2,1 : (4496080896,821723136,30326784,0)
    1,2,2 : (3338575872,733925376,31125504,0)
    1,2,3 : (1360914432,355003392,17433600,0)
    1,2,4 : (329127936,100796928,5787648,0)
    1,2,5 : (47251392,16869312,1145856,0)
    1,2,6 : (3731616,1548384,125952,0)
    1,2,7 : (125232,60480,5952,0)
    1,3,0 : (3481518080,843096064,56836096,507904)
    1,3,1 : (5729411072,1668907008,126992384,1368064)
    1,3,2 : (3973292032,1366967808,118137856,1547264)
    1,3,3 : (1504082944,602271488,59542016,956416)
    1,3,4 : (335299648,154702400,17656832,351232)
    1,3,5 : (43975072,23275296,3102976,77312)
    1,3,6 : (3140432,1911024,301760,9536)
    1,3,7 : (94280,66592,12640,512)
    1,4,0 : (3155189760,1112494080,117604352,2174976)
    1,4,1 : (4842954752,2014140416,237389824,5260288)
    1,4,2 : (3108117504,1494461440,197656064,5282304)
    1,4,3 : (1077332224,590142784,88201984,2861568)
    1,4,4 : (216931424,134231968,22871808,907264)
    1,4,5 : (25264656,17638736,3466624,169536)
    1,4,6 : (1568344,1244744,286496,17440)
    1,4,7 : (39792,36528,10032,768)
    1,5,0 : (2004873216,979963904,144752640,4157440)
    1,5,1 : (2854105088,1603857408,260684800,8913408)
    1,5,2 : (1675608320,1061216256,191171840,7819008)
    1,5,3 : (521922048,367715168,73943936,3634176)
    1,5,4 : (92306288,71933680,16286720,966528)
    1,5,5 : (9160856,7918120,2042176,147168)
    1,5,6 : (464016,450600,134544,11856)
    1,5,7 : (8928,9984,3528,384)
    1,6,0 : (914114560,606750720,117671936,4667392)
    1,6,1 : (1199428608,884224512,186082816,8727808)
    1,6,2 : (634312704,511008512,117685120,6547328)
    1,6,3 : (172961792,150932144,38326976,2536192)
    1,6,4 : (25790728,24345240,6875136,542656)
    1,6,5 : (2043200,2101728,667808,63088)
    1,6,6 : (75136,85776,31192,3544)
    1,6,7 : (832,1088,464,64)
    1,7,0 : (300721152,270632960,66282496,3404800)
    1,7,1 : (361167360,344176896,90140416,5436544)
    1,7,2 : (168364416,168839392,47767232,3387840)
    1,7,3 : (38660160,40760408,12559712,1048704)
    1,7,4 : (4554208,5072984,1717248,168992)
    1,7,5 : (255648,304720,114656,13320)
    1,7,6 : (5120,6688,2848,392)
    1,8,0 : (70694400,87587840,26374656,1684480)
    1,8,1 : (77116416,94532224,29978752,2231232)
    1,8,2 : (30666816,37762432,12767648,1107552)
    1,8,3 : (5569680,6974176,2536912,256416)
    1,8,4 : (460192,593840,234448,27600)
    1,8,5 : (13696,18560,8048,1104)
    1,9,0 : (11557120,20409600,7406336,571648)
    1,9,1 : (11355136,17946688,6751552,602464)
    1,9,2 : (3647312,5466736,2163952,222992)
    1,9,3 : (466368,684992,288200,34240)
    1,9,4 : (20224,29824,13456,1840)
    1,10,0 : (1244544,3339392,1436800,131200)
    1,10,1 : (1091968,2242144,984160,103024)
    1,10,2 : (254880,462160,210680,25224)
    1,10,3 : (17216,29376,14064,1920)
    1,11,0 : (79104,364256,183168,19456)
    1,11,1 : (61504,165872,83728,10104)
    1,11,2 : (7936,17312,8960,1224)
    1,12,0 : (2240,23792,13792,1680)
    1,12,1 : (1536,5504,3152,432)
    1,13,0 : (0,704,464,64)
    2,0,0 : (396361728,0,0,0)
    2,0,1 : (668860416,0,0,0)
    2,0,2 : (464486400,0,0,0)
    2,0,3 : (170311680,0,0,0)
    2,0,4 : (34836480,0,0,0)
    2,0,5 : (3773952,0,0,0)
    2,0,6 : (169344,0,0,0)
    2,1,0 : (1874460672,127991808,0,0)
    2,1,1 : (2985099264,252592128,0,0)
    2,1,2 : (1956741120,202752000,0,0)
    2,1,3 : (677191680,84971520,0,0)
    2,1,4 : (130705920,19664640,0,0)
    2,1,5 : (13356288,2388672,0,0)
    2,1,6 : (565056,119232,0,0)
    2,2,0 : (4000481280,575373312,16515072,0)
    2,2,1 : (5974179840,1050329088,34725888,0)
    2,2,2 : (3665166336,776404992,29835264,0)
    2,2,3 : (1183650816,298504704,13487616,0)
    2,2,4 : (212372352,63220608,3407616,0)
    2,2,5 : (20086272,7028832,459264,0)
    2,2,6 : (783264,322464,25920,0)
    2,3,0 : (5081169920,1164206080,69591040,532480)
    2,3,1 : (7064551424,1947342848,132395008,1232896)
    2,3,2 : (4014460928,1309309696,102119936,1171968)
    2,3,3 : (1192312064,454456256,41114368,589312)
    2,3,4 : (194965184,86270720,9183616,166912)
    2,3,5 : (16624640,8544880,1089152,25536)
    2,3,6 : (577392,347856,54112,1664)
    2,4,0 : (4263567360,1398415360,130945024,2076672)
    2,4,1 : (5472653312,2118065152,222579712,4267520)
    2,4,2 : (2842967296,1275039232,151673856,3552512)
    2,4,3 : (761762304,391229792,53251072,1540352)
    2,4,4 : (110460512,64701056,10221376,369664)
    2,4,5 : (8168608,5487496,1025088,47008)
    2,4,6 : (238752,187128,42288,2496)
    2,5,0 : (2479392768,1106974720,144787456,3572736)
    2,5,1 : (2908547072,1495252992,216399360,6411008)
    2,5,2 : (1357684224,789346176,127558016,4575488)
    2,5,3 : (319591296,208042992,37943936,1662272)
    2,5,4 : (39483632,28761232,6005600,324480)
    2,5,5 : (2378928,1960584,477984,32208)
    2,5,6 : (52512,50208,14664,1248)
    2,6,0 : (1019011072,605775872,104100864,3555840)
    2,6,1 : (1078732800,715137024,133965312,5454336)
    2,6,2 : (441820032,321765248,66365184,3241984)
    2,6,3 : (87872192,69873192,16041568,946592)
    2,6,4 : (8676880,7564264,1961216,140864)
    2,6,5 : (379360,368768,110224,9720)
    2,6,6 : (4800,5376,1904,208)
    2,7,0 : (295994880,233618944,50810368,2254080)
    2,7,1 : (278108160,234406784,54706944,2871040)
    2,7,2 : (96488832,86244912,21844320,1362848)
    2,7,3 : (15231312,14448472,4016816,299440)
    2,7,4 : (1068928,1087312,336752,30176)
    2,7,5 : (25472,28448,10032,1088)
    2,8,0 : (59650560,63431680,17032960,942720)
    2,8,1 : (48605952,51934144,14719424,956128)
    2,8,2 : (13491792,14634240,4435264,339280)
    2,8,3 : (1505760,1678080,550384,49768)
    2,8,4 : (56320,65696,23680,2544)
    2,9,0 : (7991680,11872640,3868032,259776)
    2,9,1 : (5451136,7434496,2512736,196400)
    2,9,2 : (1086784,1423920,506920,46208)
    2,9,3 : (64448,83584,31744,3384)
    2,10,0 : (653952,1457920,568768,45408)
    2,10,1 : (350272,620256,246560,22704)
    2,10,2 : (38144,60416,24912,2648)
    2,11,0 : (27168,105664,48832,4560)
    2,11,1 : (9664,22880,10576,1128)
    2,12,0 : (320,3424,1856,200)
    3,0,0 : (396361728,0,0,0)
    3,0,1 : (557383680,0,0,0)
    3,0,2 : (309657600,0,0,0)
    3,0,3 : (85155840,0,0,0)
    3,0,4 : (11612160,0,0,0)
    3,0,5 : (628992,0,0,0)
    3,1,0 : (1771241472,117669888,0,0)
    3,1,1 : (2343075840,193167360,0,0)
    3,1,2 : (1224253440,123863040,0,0)
    3,1,3 : (316477440,38891520,0,0)
    3,1,4 : (40538880,5996160,0,0)
    3,1,5 : (2060928,364032,0,0)
    3,2,0 : (3544350720,487833600,12042240,0)
    3,2,1 : (4373667840,736542720,21258240,0)
    3,2,2 : (2125688832,432420864,14788608,0)
    3,2,3 : (509154816,123902208,5109504,0)
    3,2,4 : (60147840,17415936,883968,0)
    3,2,5 : (2806080,966912,61632,0)
    3,3,0 : (4182138880,901386240,46284800,286720)
    3,3,1 : (4765831168,1236711424,73170944,561152)
    3,3,2 : (2124701696,654403712,45191424,437504)
    3,3,3 : (462634496,167641600,13748608,171520)
    3,3,4 : (49123904,20915392,2081856,34240)
    3,3,5 : (2032480,1025152,126880,2816)
    3,4,0 : (3223203840,976517120,78471168,1009664)
    3,4,1 : (3350097920,1198920192,109331968,1728256)
    3,4,2 : (1345107456,560099072,58709632,1159808)
    3,4,3 : (259305216,124728064,15290752,384320)
    3,4,4 : (23823712,13279680,1948000,63520)
    3,4,5 : (826080,542400,97872,4224)
    3,5,0 : (1696877568,686086144,76964864,1544704)
    3,5,1 : (1583104000,738633472,92544256,2263936)
    3,5,2 : (558191104,296146112,41987712,1270784)
    3,5,3 : (91639552,55032768,8985792,341728)
    3,5,4 : (6849792,4694952,904176,43920)
    3,5,5 : (178656,143232,33528,2112)
    3,6,0 : (619308544,326206464,48084480,1339904)
    3,6,1 : (507553280,299469056,48484864,1633408)
    3,6,2 : (151441408,98893504,17829696,735680)
    3,6,3 : (19894624,14373296,2938160,150512)
    3,6,4 : (1078720,874688,207864,13400)
    3,6,5 : (16064,15104,4304,352)
    3,7,0 : (155504640,106131200,19824640,720000)
    3,7,1 : (108514560,79766272,16079488,700096)
    3,7,2 : (25815552,20327560,4488080,236944)
    3,7,3 : (2418336,2052656,505784,32776)
    3,7,4 : (71552,66912,18896,1520)
    3,8,0 : (26027520,23290240,5387520,245120)
    3,8,1 : (14714624,13432736,3291488,177968)
    3,8,2 : (2497760,2345632,618792,40168)
    3,8,3 : (125504,123264,35712,2816)
    3,9,0 : (2714560,3292800,929344,51552)
    3,9,1 : (1132800,1294704,379536,24792)
    3,9,2 : (103872,115968,35952,2792)
    3,10,0 : (153312,270272,92192,6112)
    3,10,1 : (37120,54272,18832,1456)
    3,11,0 : (3264,9760,4000,312)
    4,0,0 : (247726080,0,0,0)
    4,0,1 : (278691840,0,0,0)
    4,0,2 : (116121600,0,0,0)
    4,0,3 : (21288960,0,0,0)
    4,0,4 : (1451520,0,0,0)
    4,1,0 : (1042513920,67092480,0,0)
    4,1,1 : (1099284480,87920640,0,0)
    4,1,2 : (429004800,42209280,0,0)
    4,1,3 : (73589760,8824320,0,0)
    4,1,4 : (4688640,679680,0,0)
    4,2,0 : (1946296320,254976000,5160960,0)
    4,2,1 : (1902827520,305479680,7434240,0)
    4,2,2 : (685830144,133521408,3987456,0)
    4,2,3 : (108111360,25362816,953472,0)
    4,2,4 : (6294144,1778304,86400,0)
    4,3,0 : (2118338560,426705920,17960960,81920)
    4,3,1 : (1894230016,460240128,22878208,134144)
    4,3,2 : (618947072,179483904,10754432,83584)
    4,3,3 : (87431680,30164032,2237760,23744)
    4,3,4 : (4495552,1858368,175936,2624)
    4,4,0 : (1484497920,412247040,27145216,258048)
    4,4,1 : (1192786432,392263168,29948672,362624)
    4,4,2 : (344375808,132748288,11998144,190272)
    4,4,3 : (41989760,18981280,2088608,44512)
    4,4,4 : (1802112,969696,134304,3936)
    4,5,0 : (697374720,253033216,23250432,346112)
    4,5,1 : (491453440,206568576,21595648,405632)
    4,5,2 : (120724096,58257536,7079392,172128)
    4,5,3 : (11956800,6656592,968112,31152)
    4,5,4 : (384480,252672,45552,1968)
    4,6,0 : (221301760,102151680,12331520,256000)
    4,6,1 : (132045440,68703872,9252736,240064)
    4,6,2 : (25971712,15142272,2326672,77264)
    4,6,3 : (1865120,1231328,222576,9640)
    4,6,4 : (34112,26304,5792,328)
    4,7,0 : (46508160,27067840,4142080,112640)
    4,7,1 : (22206080,14062544,2351872,79168)
    4,7,2 : (3123936,2153168,403088,17184)
    4,7,3 : (122560,93632,20272,1112)
    4,8,0 : (6127680,4527680,859200,29440)
    4,8,1 : (2106848,1614912,327728,13768)
    4,8,2 : (160064,128800,28688,1512)
    4,9,0 : (448960,432400,100448,4224)
    4,9,1 : (85056,79360,19264,984)
    4,10,0 : (13440,17888,5056,256)
    5,0,0 : (99090432,0,0,0)
    5,0,1 : (83607552,0,0,0)
    5,0,2 : (23224320,0,0,0)
    5,0,3 : (2128896,0,0,0)
    5,1,0 : (391200768,24256512,0,0)
    5,1,1 : (308109312,23777280,0,0)
    5,1,2 : (79782912,7593984,0,0)
    5,1,3 : (6806016,792576,0,0)
    5,2,0 : (677412864,83939328,1290240,0)
    5,2,1 : (491166720,74778624,1465344,0)
    5,2,2 : (116476416,21638400,556800,0)
    5,2,3 : (9042432,2047488,71424,0)
    5,3,0 : (674139136,126001664,4035584,11264)
    5,3,1 : (441839104,99999232,3986432,15872)
    5,3,2 : (93603328,25531904,1307776,7680)
    5,3,3 : (6392064,2113792,144256,1280)
    5,4,0 : (423943680,107035904,5371904,31488)
    5,4,1 : (244917760,73625600,4490240,37120)
    5,4,2 : (44669696,15952768,1222848,14656)
    5,4,3 : (2536128,1090176,109248,1920)
    5,5,0 : (174183936,56195840,3941120,36480)
    5,5,1 : (85478656,32186880,2677760,34560)
    5,5,2 : (12639552,5559936,568608,10464)
    5,5,3 : (535584,280896,36768,960)
    5,6,0 : (46561024,18637696,1719040,22400)
    5,6,1 : (18289856,8339840,890560,16000)
    5,6,2 : (1959200,1023184,131360,3312)
    5,6,3 : (47040,28928,4640,160)
    5,7,0 : (7760832,3804064,445120,7680)
    5,7,1 : (2184800,1183072,156352,3680)
    5,7,2 : (127936,77504,12048,392)
    5,8,0 : (725088,435472,63232,1392)
    5,8,1 : (110912,70656,11296,336)
    5,9,0 : (28480,21312,3792,104)
    6,0,0 : (24772608,0,0,0)
    6,0,1 : (13934592,0,0,0)
    6,0,2 : (1935360,0,0,0)
    6,1,0 : (91348992,5419008,0,0)
    6,1,1 : (47738880,3529728,0,0)
    6,1,2 : (6147072,562176,0,0)
    6,2,0 : (145692672,16951296,172032,0)
    6,2,1 : (69500928,9980928,148992,0)
    6,2,2 : (8113152,1436160,32256,0)
    6,3,0 : (131097600,22561792,480768,512)
    6,3,1 : (55695360,11695616,353024,768)
    6,3,2 : (5697024,1466880,64768,256)
    6,4,0 : (72668160,16545280,556800,1280)
    6,4,1 : (26503680,7263232,333568,1536)
    6,4,2 : (2245248,748800,48768,384)
    6,5,0 : (25350144,7210240,341760,1280)
    6,5,1 : (7478016,2518464,157056,1152)
    6,5,2 : (470976,191040,16320,192)
    6,6,0 : (5417856,1864064,117120,640)
    6,6,1 : (1155840,461632,36832,384)
    6,6,2 : (41088,19488,2048,32)
    6,7,0 : (645696,264128,21216,160)
    6,7,1 : (75264,34880,3440,48)
    6,8,0 : (32640,15776,1584,16)
    7,0,0 : (3538944,0,0,0)
    7,0,1 : (995328,0,0,0)
    7,1,0 : (12128256,681984,0,0)
    7,1,1 : (3151872,221184,0,0)
    7,2,0 : (17664000,1913856,9216,0)
    7,2,1 : (4147200,559104,6144,0)
    7,3,0 : (14161920,2227200,23040,0)
    7,3,1 : (2903040,565248,12288,0)
    7,4,0 : (6743040,1374720,23040,0)
    7,4,1 : (1140480,285696,9216,0)
    7,5,0 : (1903872,474240,11520,0)
    7,5,1 : (238464,72192,3072,0)
    7,6,0 : (294528,86592,2880,0)
    7,6,1 : (20736,7296,384,0)
    7,7,0 : (19200,6528,288,0)
    8,0,0 : (221184,0,0,0)
    8,1,0 : (700416,36864,0,0)
    8,2,0 : (921600,92160,0,0)
    8,3,0 : (645120,92160,0,0)
    8,4,0 : (253440,46080,0,0)
    8,5,0 : (52992,11520,0,0)
    8,6,0 : (4608,1152,0,0)

For each of P4,PA,PR, a row i : (r0,...,rn) denotes
a^i*(r0+r1*b+...+rn*b^n). Each polynomial is the sum of its rows.
All omitted coefficients are zero; internal zeros would be displayed.
These identities in particular show positivity on a,b>=0.

P4 coefficient rows:

    0 : (314572800,862617600,999481344,642877440,252277248,62160384,9462912,828024,34218,300)
    1 : (1584005120,4458053632,5376073728,3671259136,1573405696,441097216,81274848,9532696,648296,19536)
    2 : (3077308416,8713535488,10582081536,7276156928,3133784576,878998912,160815456,18516032,1217056,34752)
    3 : (3061579776,8774549504,10792640512,7512844288,3273002496,928100736,171781760,20076160,1349504,39936)
    4 : (1724645376,5157027840,6635503616,4836632576,2207429120,656062464,127328256,15600640,1097216,33792)
    5 : (556793856,1806237696,2499682304,1935181824,924071936,282288128,55111680,6612992,440320,12288)
    6 : (84934656,300810240,440156160,348930048,164888576,47808512,8339456,802816,32768)

PA coefficient rows:

    0 : (2579520001436709588480,2304659822504944402048,912393902132832733440,210299251563395316352,31147968480084581376,3081746336014652416,204567095681630208,8867591799470080,233567340531712,3155214319616,12919095296)
    1 : (26442106011838635264000,23953198019794771334400,9600687464012774979200,2237568183490877846400,334737655692913846400,33416312017475196800,2235775773783622400,97565180260851200,2582278677606400,34912679782400,140479692800)
    2 : (82139111351704176120000,76436165161828752340000,31359053438302199640000,7459658180121741560000,1136350035858647320000,115285583296571700000,7825332856853720000,345873275696160000,9255105203040000,126136434240000,505916160000)
    3 : (119534022468891402000000,114868457530700900000000,48421302894696027000000,11790377266243475000000,1833125549685310000000,189372629193180000000,13063731800095000000,585807991403000000,15875336438000000,218553618000000,877304000000)
    4 : (90952188117481200000000,90630731452978046875000,39351062280216306250000,9823571422107853125000,1560567529024725000000,164300249388153125000,11527353757956250000,524807235796875000,14414547687500000,200640450000000,807425000000)
    5 : (35158488449271562500000,36479346803437343750000,16348784057118203125000,4188970419841796875000,680380662809296875000,73034615826796875000,5213380366015625000,241063375390625000,6713518203125000,94533671875000,381718750000)
    6 : (5462912364319335937500,5929079201063964843750,2748204682549804687500,723382100013671875000,120178125908203125000,13155973473632812500,955634173828125000,44888443359375000,1267913085937500,18067871093750,73242187500)

PR coefficient rows:

    0 : (1376937500000,1235150000000,353456250000,45375000000,2725000000,62500000)
    1 : (5068874500000,4007224625000,1075910250000,132344250000,7695500000,172000000)
    2 : (6952018730000,4636908095000,1134903325000,131541880000,7345140000,159720000)
    3 : (4205107639400,2192440592600,455341649000,47157652400,2437511200,50329600)
    4 : (945026658512,327612321794,42905960896,2601218944,70598816,648736)

The P4 coefficients have minimum 300 and maximum 10792640512;
the PA coefficients have minimum 12919095296 and maximum
119534022468891402000000; the PR coefficients have minimum 648736
and maximum 6952018730000. Their respective positive constants are
314572800, 2579520001436709588480 and 1376937500000. All four
identities retain the entire clearing factors specified in their
definitions, so each positivity conclusion has exactly the sign
used in the corresponding proof. QED.

## 332. A high-axis bound for the source companion

**Theorem 332.1 (repo-derived).** Let c,d,v,m,z,r be coshes satisfying

    c,d,v>1, m>1+c+d, 1<v<=m-2,
    z>1+m+c, r>=m.                              (332.1)

Suppose eta=(Z,V,C,R,V,C) is a genuine paired frame with four distinct
labels and axial coshes z,r. Thus

    L=(v+c)^2-(z-1)*(r-1)>0,
    J=(z+1)*(r+1)-(v-c)^2>0.                    (332.2)

Then its two axial angles satisfy

    theta_Z(eta)+theta_R(eta)>pi.               (332.3)

In the six-label notation, this includes R=M and R=U when u>m.
No source-flat product, receiver, maximum-gap inequality or partial
M-angle budget is a premise of this theorem. The paired formulas use
the hyper-ideal dihedral-angle convention of Luo–Yang,
*Volume and rigidity of hyperbolic polyhedral 3-manifolds*,
[arXiv:1404.5365v2, Sections 4.1–4.2](https://arxiv.org/html/1404.5365v2).
The inequality (332.3) is the following deduction from the paired formulas.

**Proof.** Put p=sqrt((z-1)*(r-1)) and q=sqrt((z+1)*(r+1)).
Every genuine angle belongs to (0,pi), and

    tan(theta_Z/2)^2=(z-1)*J/[(z+1)*L],
    tan(theta_R/2)^2=(r-1)*J/[(r+1)*L].          (332.4)

If theta_Z+theta_R<=pi, their positive half-angle product is at most
one, equivalently p*J<=q*L. Expanding and dividing by p+q>0 gives

    p*q<=v^2+c^2+2*v*c*(q-p)/(q+p).             (332.5)

Since z>m and r>=m, monotonicity of (t+1)/(t-1) for t>1 gives
1<q/p<=(m+1)/(m-1), hence 0<(q-p)/(q+p)<=1/m. Also
p*q>p^2>=(m-1)*(z-1)>(m-1)*(m+c). Enlarging v to m-2 in the
right side of (332.5) would therefore require

    (m-1)*(m+c)<=(m-2)^2+c^2+2*c*(m-2)/m.

This is impossible, since the difference of its left and right sides is

    c*(m-c-2)+(3*m-c-4)+4*c/m>0.                (332.6)

Indeed m>1+c+d and d>1 give m-c-2>0 and
3*m-c-4>2*m-2>0. This proves (332.3). QED.

For an actual owner, (332.3) counts its one Z-axis slot and one R-axis
slot. Its two V and two C transverse slots are not additional high-axis
charges. Different actual owners with the same role vector contribute
separately. In particular, under (332.1), a bad high-axis owner with axes
Z,U cannot have transverse pair V,C. This statement concerns the source
companion C; it does not replace C by D without the corresponding order
z>1+m+d. Axes M,U are covered only if their actual values can satisfy
the axial bounds of (332.1) after renaming the larger axis.

## 333. The opposite-companion Z/U inventory

**Definition 333.1 and hypotheses.** Let lower-case letters be shared coshes, with

    c,d,v>1, m>1+c+d, 1<v<=m-2,
    z>1+m+c, u>m,
    (m-1)*(v-1)>=(c+d)^2.                         (333.1)

Consider three distinct genuine paired owners with these precise roles:

    tau=(Z,M,C,D,M,C),
    rho=(W,V,D,C,V,D), W in {M,Z,U},
    eta=(Z,V,D,U,V,D).                            (333.2)

Denote W's value by r. Thus r is one of m,z,u. All four labels in each
frame are distinct. Require all strict genuine inequalities:

    Lt=(m+c)^2-(z-1)*(d-1)>0,
    Jt=(z+1)*(d+1)-(m-c)^2>0,
    Lr=(v+d)^2-(r-1)*(c-1)>0,
    Jr=(r+1)*(c+1)-(v-d)^2>0,
    Le=(v+d)^2-(z-1)*(u-1)>0,
    Je=(z+1)*(u+1)-(v-d)^2>0.                    (333.3)

Retain the following actual partial M and V budgets:

    2*beta_M(tau)<=pi,
    2*beta_V(rho)+2*beta_V(eta)<=pi.              (333.4)

Assume, for contradiction, the bad-eta condition

    theta_Z(eta)+theta_U(eta)<=pi.               (333.5)

**Theorem 333.2 (repo-derived).** Under (333.1)–(333.5), with
S=beta_V+beta_D at rho and eta,

    theta_D(tau)+2*S(rho)+2*S(eta)>3*pi.          (333.6)

An actual configuration with the original V and D capacities pi and
2*pi cannot therefore satisfy these premises. Equivalently, in an actual
configuration having the displayed owners, numerical premises and
capacities, eta spends more than pi on its two Z/U axial slots.

**Original-slot interpretation.** The slots in (333.6) are tau's single D-axis
slot, rho's two V and two D transverse slots, and eta's two V and two D
transverse slots. The two
M slots used in (333.4) are actual tau slots; eta has no M slot. If W=M,
rho also has an actual M-axis slot, which is deliberately omitted from
our necessary partial M budget. Additional genuine owners only reduce
the available capacities. Repeated role vectors at distinct actual owners
are never identified. The three owners in (333.2) cannot coincide: tau
has no V label, while rho has C and eta does not.

The theorem has no maximum-gap premise and no premise asserting a second
transverse-M owner. Its conclusion is conditional on (333.1)–(333.5). The
proof occupies Sections 334–339.

## 334. A simultaneous upper bound for both high axes

**Lemma 334.1 (repo-derived).** Under (333.1)–(333.5), if H=max(z,u)
and Q=v^2+d^2, then H<Q/(m-1) and Q>(m-1)*(m+c+1).

**Proof and angle notation.**

For the common transverse pair V,D, put

    K=[sqrt(v^2-1)+sqrt(d^2-1)]/(v+d),
    x=K*sqrt(Lr/Jr), y=K*sqrt(Le/Je),
    w=sqrt((d-1)*Jt/[(d+1)*Lt]).                  (334.1)

Then the exact genuine paired formulas are

    theta_D(tau)=2*atan(w),
    S(rho)=2*atan(x), S(eta)=2*atan(y).           (334.2)

For a frame with transverse pair V,D and t=sqrt(L/J), write

    A=[sqrt(v^2-1)+sqrt(d^2-1)]/(v+d)=K,
    B=[sqrt(v^2-1)-sqrt(d^2-1)]/(v+d).

Its transverse angles satisfy

    beta_V=atan(A*t)+atan(B*t),
    beta_D=atan(A*t)-atan(B*t).                  (334.3)

All angles and square roots have their genuine positive branches.
In particular, if v>=d then B>=0 and beta_V>=S/2.

Define also

    Q=v^2+d^2, T=v*d, H=max(z,u),
    p=sqrt((z-1)*(u-1)), q=sqrt((z+1)*(u+1)).

The axial half-angle product makes (333.5) equivalent to q*Le>=p*Je,
or, after exact expansion,

    p*q<=Q+2*T*(q-p)/(q+p).                     (334.4)

Both z,u exceed m. Consequently

    0<(q-p)/(q+p)<1/m,
    Le/Je>=p/q>(m-1)/(m+1).                    (334.5)

Furthermore, with h=min(z,u)>m,

    p*q=sqrt((H^2-1)*(h^2-1))
         > H*(m^2-1)/m.

Indeed sqrt(1-H^(-2))>sqrt(1-m^(-2)), and
sqrt(h^2-1)>sqrt(m^2-1). Using 2*T<=Q in (334.4) therefore gives

    H<Q/(m-1),
    Q>(m-1)*(m+c+1).                            (334.6)

The second inequality follows from H>=z>m+c+1. Notice that (334.6)
controls both possible high receiver axes at once, and also r=m<H. QED.

## 335. Coarse source-order bounds

**Lemma 335.1 (repo-derived).** Under the same hypotheses, m>9, v,d>5
and c+2<2*m/5.

**Proof.**

Flatness and v<=m-2 give

    (c+d)^2<=(m-1)*(m-3)=(m-2)^2-1.

Since c+d>2 and m>3, it follows that m>2+sqrt(5)>4 and

    c+d<m-2, hence d<m-c-2<m-3.                 (335.1)

By (334.6), c>1, v<=m-2 and (335.1),

    (m-1)*(m+2)<Q<(m-2)^2+(m-3)^2,

so m^2-11*m+15>0. If 4<m<=9, however,

    m^2-11*m+15=(m-4)*(m-9)+2*m-21<0.

Thus m>9. Moreover v>5 and d>5. Otherwise the respective upper
bounds for Q contradict (334.6), because

    25+(m-3)^2-(m-1)*(m+2)=36-7*m<0,
    (m-2)^2+25-(m-1)*(m+2)=31-5*m<0.             (335.2)

In particular,

    K^2>24/25.                                  (335.3)

We also have

    c+2<2*m/5.                                  (335.4)

To prove this, define

    F(c)=(m-2)^2+(m-c-2)^2-(m-1)*(m+c+1).

Equations (334.6) and (335.1) require F(c)>0. For c<m-2,
F'(c)=2*c-3*m+5<1-m<0. At c0=2*m/5-2,

    F(c0)=-(m^2+40*m-75)/25<0

since m>9. Hence c<c0, proving (335.4). QED.

## 336. The actual V budget forces v<d

**Lemma 336.1 (repo-derived).** Under (333.1)–(333.5),
S(rho)+S(eta)>pi and v<d.

**Proof.**

For any lambda>1, direct expansion gives

    Lr-lambda*Jr
      =(1+lambda)*Q+2*(1-lambda)*T
       -[(1+lambda)*c+(lambda-1)]*r
       -(lambda-1)*c-(lambda+1).                (336.1)

Use 2*T<=Q, r<=H<Q/(m-1), and lambda=4. Then

    Lr-4*Jr
      >[2-(5*c+3)/(m-1)]*Q-3*c-5
      >5*Q/(m-1)-3*c-5
      >5*(m+c+1)-3*c-5=5*m+2*c>0.              (336.2)

The second line uses 5*c+3<2*m-7 from (335.4). Thus

    x^2>96/25,
    y^2>(24/25)*(4/5)=96/125,                  (336.3)

where the y estimate uses (334.5), m>9 and (335.3). Hence xy>1, because
9216/3125>1. On the positive arctangent branch, (334.2) gives

    S(rho)+S(eta)>pi.                           (336.4)

If v>=d, (334.3) would make
2*beta_V(rho)+2*beta_V(eta)>=S(rho)+S(eta)>pi,
contradicting the actual four-slot V budget in (333.4). Therefore

    v<d.                                        (336.5)

No individual-angle assertion such as beta_V(eta)>pi/4 was used. QED.

## 337. A strict eighth bound from the actual tau M slots

**Lemma 337.1 (repo-derived).** Under (333.1)–(333.5),
d>3*m/4, c+1<m/8 and m>16.

**Proof.**

By (336.5) and flatness,

    (c+d)^2<(m-1)*(d-1).

Completing the square yields

    (c+d)^2-(m-1)*(d-1)
      =[d+c-(m-1)/2]^2+(m-1)*[c-(m-5)/4].

Consequently

    c<(m-5)/4.                                  (337.1)

The source cosine is

    cos(beta_M(tau))=N/sqrt(D(z)*D(d)),
    N=c*(z+d)+m*(z*d+c^2-m^2+1),
    D(t)=t^2+m^2+c^2+2*t*m*c-1.

The actual partial M budget makes beta_M(tau)<=pi/2 and therefore N>=0.
The polynomial N strictly increases with each of c,d,z when m is fixed:
its three derivatives are z+d+2*m*c, c+m*z and c+m*d.

We claim d>3*m/4. If d<=3*m/4, (334.6) and v<d give z<2*d^2/(m-1).
Together with (337.1) and the monotonicity just noted, this implies

    N < N evaluated at
        c=(m-5)/4, d=3*m/4, z=2*(3*m/4)^2/(m-1)
      =-m*(3*m^3-25*m^2-21*m+52)/[32*(m-1)]<0. (337.2)

For the last sign put m=9+b, b>0; its cubic numerator becomes
3*b^3+56*b^2+258*b+25, with every coefficient positive. This contradicts
N>=0. The monotonic comparison in (337.2) is purely polynomial; it makes
no claim that the comparison point is a genuine tetrahedron.

Now f(d)=sqrt((m-1)*(d-1))-d strictly decreases when
 d>(m+3)/4. Since d>3*m/4 and m>9, flatness gives

    c<f(d)<sqrt((m-1)*(3*m/4-1))-3*m/4<m/8-1.    (337.3)

The last step follows by squaring positive quantities and using

    (7*m/8-1)^2-(m-1)*(3*m/4-1)=m^2/64>0.

We have proved

    d>3*m/4, c+1<m/8, m>16.                    (337.4)

The final statement follows from c>1. QED.

## 338. Three strict tangent bounds

**Lemma 338.1 (repo-derived).** Under (333.1)–(333.5), the parameters
in (334.1) satisfy w>4/5, x>7/2 and y>9/10.

**Proof.**

First, the exact identity

    (m+c)*Jt-(m-c)*Lt=2*N

and N>=0 imply

    w^2 >= [(m-c)/(m+c)]*[(d-1)/(d+1)]
         > (7/9)*(11/13)=77/117>16/25.           (338.1)

Here c<m/8 and d>3*m/4>12. Thus w>4/5.

Next use (336.1) with lambda=13. From c+1<m/8,
14*c+12<7*m/4-2. Therefore, using r<Q/(m-1) and 2*T<=Q,

    Lr-13*Jr
      > [2-(14*c+12)/(m-1)]*Q-12*c-14
      > m*Q/[4*(m-1)]-12*c-14
      > m^2/4-3*m/2-2>0.                        (338.2)

The last line uses Q>(m-1)*(m+c+1)>m*(m-1), c<m/8-1 and m>16.
Since Jr>0, (335.3) gives

    x^2>(24/25)*13=312/25>49/4, so x>7/2.       (338.3)

Finally, (334.5), (335.3) and m>16 give

    y^2>(24/25)*(15/17)=72/85>81/100,
    hence y>9/10.                               (338.4)

These bounds do not assert any false individual low-angle pi/4 bound. QED.

## 339. The combined-angle comparison

**Proof of Theorem 333.2.**

For positive x,y, the function (xy-1)/(x+y) strictly increases in each
variable: the derivatives are (y^2+1)/(x+y)^2 and (x^2+1)/(x+y)^2.
Equations (338.1), (338.3) and (338.4) give xy>1 and

    (xy-1)/(x+y)>43/88>(sqrt(41)-4)/5
                        >sqrt(1+w^2)-w.         (339.1)

For the middle strict comparison, both sides of
sqrt(41)<567/88 are positive, and
567^2-41*88^2=3985>0. The last comparison uses w>4/5 and strict
decrease of sqrt(1+w^2)-w for w>0.

Since xy>1, the positive arctangent identity gives

    atan(x)+atan(y)=pi/2+atan((xy-1)/(x+y)).

Also tan(pi/4-atan(w)/2)=sqrt(1+w^2)-w. Hence (339.1) implies

    2*atan(w)+4*atan(x)+4*atan(y)>3*pi.

By (334.2) this is exactly (333.6). This proves the scalar implication. QED.


## 340. Conditional exclusion by the original V/D capacities

**Corollary 340.1 (repo-derived).** Consider a finite paired quotient
with six actual global labels M,V,C,D,Z,U, shared original positive
lengths, four distinct labels in each displayed paired frame, and
nonnegative original angles and angle sum 2*pi at every global edge.
Suppose it has a flat source sigma=(M,C,D,V,C,D) with angle pi at each of its M,V axes and
zero at its C,D transverse slots. Assume the numerical premises
(333.1), and suppose three distinct genuine owners have the exact
roles (333.2). Then

    theta_Z(eta)+theta_U(eta)>pi.               (340.1)

**Proof.** The source already spends pi at M and pi at V. Nonnegativity
of all other original angles makes the genuine M,V capacities at most
pi each, while the genuine D capacity is at most 2*pi. Thus the actual
tau M slots and the four actual V slots of rho and eta obey (333.4).
If (340.1) failed, strict genuineness and Theorem 333.2 would give
(333.6). Its nine charged slots are precisely

    tau: one D-axis slot;
    rho: two V-transverse slots and two D-transverse slots;
    eta: two V-transverse slots and two D-transverse slots.

They are distinct original occurrences in three distinct owners, so
their total is at most pi+2*pi, contrary to (333.6). An equality of
lengths or role vectors at different owners does not identify their
slots. If W=M, rho's additional M-axis angle only tightens the M budget;
eta itself has no M slot. Additional genuine owners cannot reduce any
of these charges. This proves (340.1). QED.

The hypotheses of Corollary 340.1 explicitly include an opposite-
companion receiver (W,V,D,C,V,D). They do not assert that such a receiver
must exist in every source-face configuration. A receiver with transverse
companion C, namely (W,V,C,D,V,C), is a different hypothesis and is outside
the corollary. Theorem 332.1 separately controls transverse pair V,C when
one axis has the stated source-companion order; it does not provide the
missing receiver in Corollary 340.1. Other source inventories, the
remaining M/U-axis patterns, and the full six-edge and general CFMP
geometric-realization questions are not settled by these implications.

## 341. The actual-circle Z/U high-axis theorem

The opposite-companion receiver in Corollary 340.1 need not be assumed
in the following source setting. Theorem 332.1 and Corollary 340.1 will
exclude both changed-pair exits from the transported MCD/VCD faces under
a nonpositive Z/U axial excess; the actual D normal circle then gives a
contradiction. All source hypotheses are stated directly.

**Definition 341.1 and hypotheses.**

Consider a finite face-paired tetrahedral quotient with exactly the six
actual global edge labels M,V,C,D,Z,U. Every actual edge has a connected
circular normal link. Each tetrahedron owner has one fixed vertex-induced
paired frame, in edge order (12,13,14,34,24,23), of the form

    (R,A,B,O,A,B),

with R,A,B,O four distinct global labels. An actual owner is a tetrahedron
of the quotient before its faces are identified; a normal-link interval
is one original local edge occurrence, not an owner or a role vector.
Face pairings identify original face occurrences and preserve their
actual global edge labels. Distinct-face self-gluings and repeated
visits to the same owner in a normal circle are allowed.

There is one shared positive generalized length at each actual edge;
write its cosh as m,v,c,d,z,u, respectively. Original generalized
dihedral angles are nonnegative and sum to 2*pi around each actual edge.
There is a unique flat owner

    sigma=(M,C,D,V,C,D),

whose M and V axial angles are pi and whose C and D transverse angles
are zero. Every other owner is genuine and has all angles in (0,pi).
Assume there is a genuine owner

    tau=(Z,M,C,D,M,C),

and retain the exact scalar hypotheses

    c,d,v>1, m>1+c+d, 1<v<=m-2,
    z>1+m+c, u>m,
    (m-1)*(v-1)>=(c+d)^2.                         (341.1)

All genuine paired frames have the usual strict tests, with shared
coshes r,a,b,o:

    L=(a+b)^2-(r-1)*(o-1)>0,
    J=(r+1)*(o+1)-(a-b)^2>0.                     (341.2)

**Theorem 341.2 (repo-derived).** Under these hypotheses, every genuine
owner eta whose two axes are Z,U and whose
transverse pair is either {V,C} or {V,D} satisfies

    theta_Z(eta)+theta_U(eta)>pi.                  (341.3)

No degree lower bound is needed for this implication beyond the stated
connected circular links. The usual degree-at-least-six source setting
therefore satisfies the topological hypothesis, but no degree estimate
is being substituted for connectedness.

## 342. Original capacities and the unique source pair

**Proof of Theorem 341.2.** The unique flat sigma already contributes pi at each of M and V.
Consequently all genuine original M slots together have total pi, and
the same is true of V. All genuine D slots together have total 2*pi.
Any subset of these slots has at most the corresponding capacity,
because all original angles are nonnegative.

In particular every genuine owner in which M is transverse contributes
two distinct original M slots of the same angle beta_M, so

    2*beta_M<=pi.                                (342.1)

This remains true when its faces are self-glued or another owner has
the same role vector. Such identifications do not identify original
slots in the zero-curvature sum.

Sigma is the only owner with transverse pair {C,D}. To see this without
an additional face-reduction premise, any such owner's two distinct
axes lie in {M,V,Z,U}. By (341.1), z,u>m>v, so the smallest possible
product of their shifted coshes is (m-1)*(v-1). Hence its L is at most

    (c+d)^2-(m-1)*(v-1)<=0.

It cannot be genuine by (341.2). By the unique-flat premise it is sigma.
This proves the precise unique-CD-owner fact used in the link argument.

## 343. Global exclusion of the opposite-M exit

For transverse pair {V,C}, (341.3) is already Theorem 332.1 with r=u>m.
It remains to consider a genuine

    eta=(Z,V,D,U,V,D)

and suppose, for contradiction,

    theta_Z(eta)+theta_U(eta)<=pi.                 (343.1)

We first exclude any actual owner with fixed frame, up to exchanging
axes or transverse labels,

    kappa=(W,M,D,C,M,D).                          (343.2)

Such an owner is not sigma and is therefore genuine. Four distinct
labels give W in {V,Z,U}. Let w be its cosh. The exact transverse-M
cosine formula has positive denominator sqrt(D(w)*D(c)), where

    D(t)=t^2+m^2+d^2+2*t*m*d-1>0,

and numerator

    N(w)=d*(w+c)+m*(w*c+d^2-m^2+1).              (343.3)

By (342.1), beta_M(kappa)<=pi/2, hence N(w)>=0. Its slope is
d+m*c>0. At w0=1+m+d, exact expansion gives

    N(w0)=[d+m*(1+m+d)]*(1+c+d-m)<0,             (343.4)

the final inequality following from m>1+c+d. Thus

    w>1+m+d.                                    (343.5)

Since v<=m-2, W is Z or U. Apply Theorem 332.1 after interchanging the
low labels C,D, using W as its first high axis and the other member
of {Z,U} as its second high axis. Indeed its first axial value is
w>1+m+d, its second is greater than m, its transverse pair is {V,D},
and its remaining scalar and genuine hypotheses are precisely (341.1)
and those of eta. This gives (341.3), contrary to (343.1).

Therefore no owner of type (343.2) exists anywhere in the quotient under
(343.1). No premise that kappa is a source-face partner was used.

## 344. Global exclusion of the opposite-V exit

Continue under (343.1). Suppose there were an actual owner with fixed frame

    rho=(W,V,D,C,V,D).                            (344.1)

It is not sigma and is genuine; four distinct labels give
W in {M,Z,U}. The owners tau,rho,eta are distinct: tau has no V label;
rho has C, while eta does not. Strict genuineness supplies exactly the
six L/J tests in (333.3). The original M and V capacities give

    2*beta_M(tau)<=pi,
    2*beta_V(rho)+2*beta_V(eta)<=pi.

All numerical premises of Corollary 340.1 are (341.1). That corollary
therefore gives (341.3), contradicting (343.1). Equivalently, Theorem 333.2
charges more than 3*pi to tau's one D slot, rho's two V and two D slots,
and eta's two V and two D slots, although their capacities are at most
pi+2*pi. This uses no M slot of eta.

Consequently no owner of type (344.1) exists anywhere under (343.1).
Again the owner need not meet a source face. The published theorem's
conditional inventory is applied only after an actual rho is supposed
to exist; it has not been promoted to a forced receiver claim.

## 345. Exact original-face transitions

Retain the hypotheses of Section 341 and the supposition (343.1).
In a fixed paired frame (R,A,B,O,A,B), the four original faces are

    F4=(123): {R,A,B},  F3=(124): {R,A,B},
    F2=(134): {O,A,B},  F1=(234): {O,A,B}.        (345.1)

Every face therefore contains both transverse labels and one axis.
All three labels on each face are distinct. If a face has label set
{X,C,D}, its owner's transverse pair is exactly one of

    {C,D}, {X,C}, {X,D}.                         (345.2)

There is no further possibility: the fixed transverse pair occurs in
every face and must consist of two members of that three-label set.
Because the four frame labels are distinct, the remaining face label
is an axis, not a third repeated transverse label.

For X=M, the three possibilities in (345.2) are respectively:

    sigma;
    a D-axis owner with transverse pair {M,C};
    an owner (W,M,D,C,M,D), excluded in Section 343.

For X=V, they are respectively:

    sigma;
    a D-axis owner with transverse pair {V,C};
    an owner (W,V,D,C,V,D), excluded in Section 344.

The first possibility is sigma itself, not a new owner with the same
role vector, by Section 342. These classifications use the fixed chosen
frame of each receiving owner. No change of frame, metric equality or
identification of distinct labels is performed.

Every original D corner of a face {M,C,D} consequently pairs to a D
corner in sigma or to the unique axial D interval of an owner with
pair {M,C}. The analogous statement for a {V,C,D} face uses pair {V,C}.
The D corner is unique in either face, so label-preserving face gluing
sends it to the original D corner just classified, even if some coshes
happen to be equal.

## 346. A closed subset of the actual D normal circle

Before gluing, take one separate closed interval for every original
local edge whose actual global label is D. Its two endpoints are its
two original edge-in-face incidences. The actual face pairings glue
these endpoints in pairs. By hypothesis the resulting finite normal
link is one connected circle. Distinct intervals remain distinct edges
of this circle, including repeated visits to an owner and loops.

Let S consist of the following original D intervals:

1. Both transverse D intervals of sigma, its local edges 14 and 23.
2. Every axial D interval of every owner whose fixed transverse pair
   is {M,C} or {V,C}.

This selection is by actual original interval. It contains both sigma
intervals even if their endpoints are glued together, and it includes
each axial interval of every distinct owner separately.

Each sigma D interval has one endpoint on an MCD face and the other on
a VCD face. More explicitly, edge 14 is on F3 and F2, while edge 23 is
on F4 and F1. Each axial D interval with pair MC has both endpoints on
MCD faces; each axial D interval with pair VC has both endpoints on
VCD faces. Section 345 therefore proves the following endpoint-level
statement:

    Every endpoint of an interval in S is paired to an endpoint
    of another interval in S, possibly the same interval.       (346.1)

Thus the image of S is a nonempty union of complete connected components
of the normal-link graph. Indeed an endpoint-gluing vertex has its two
incident half-edges paired by the actual face identification; (346.1)
leaves no half-edge leaving S. A finite edge path starting in S stays
in S, so connectedness forces S to contain every original D interval.
This is a statement about the actual D circle, not a separately marked
graph or an assumed connected source-face graph.

But eta has two original D intervals, both transverse with companion
V and axes Z,U. It is not sigma, and neither interval is an axial D
interval with pair MC or VC. They therefore lie outside S. This
contradicts connectedness and proves that (343.1) is impossible. Together
with the source-companion case, it proves (341.3). QED.

## 347. Original occurrences and scope

No number of MCD or VCD partners is prescribed. A source face may pair
to another face of the same owner; two faces may have the same receiving
owner; an axial chain may contain arbitrarily many distinct owners or
revisit an owner in the full normal-link traversal. The argument uses
only endpoint closure (346.1), not a count of such chains or a claim that
a particular chain has two different owners. Loops in the link and
multiple edges cause no change to that closure argument. Four-distinctness
ensures that an axial D owner has one D interval, whereas a transverse
D owner has two; those two cases are never merged.

The unique-CD-owner fact is used exactly in the first case of (345.2).
The global opposite-M and opposite-V exclusions are both necessary to
the closure proof; proving absence only among the four source-face
partners would not suffice for a transported axial chain. Their global
use is justified in Sections 343–344 by actual-slot budgets and the two
published angle implications.

The unique-flat and strict source-normal-form hypotheses remain explicit
premises of Theorem 341.2. Its conclusion concerns the Z/U axial expense
in that setting, without assuming an opposite-companion receiver. It
does not exclude the unique flat source, settle the remaining M/U or
M/Z high-axis patterns, or prove six-edge or general CFMP realization.

## 348. The actual-circle M/Z theorem with an explicit upper gap

The scalar implication (322.2)--(322.5) extends to an opposite-V
owner whose other axis is M or Z, by a genuine one-axis comparison.
A separate transverse-M estimate excludes every opposite-M exit.
These two global exclusions allow the actual D-circle argument to
treat M/Z high axes without assuming a receiver inventory.

The deductions here are repo-derived from the displayed paired
response formulas, the scalar implication in Section 322, the exact
quarter-bound identity (325.3) in Section 331, and Theorem 332.1.
They retain the original generalized angle conventions of Section
322 and make no claim of a new general rigidity theorem.

**Definition 348.1 and hypotheses.**

Consider a finite face-paired tetrahedral quotient with precisely the
six distinct actual edge labels M,V,C,D,Z,U. Every actual edge has a
connected circular normal link. Each original tetrahedron owner has
one fixed vertex-induced paired frame, in local edge order
(12,13,14,34,24,23), of the form

    (R,A,B,O,A,B),

where R,A,B,O are four distinct actual labels. Original faces are
paired by maps preserving actual edge labels. Repeated role vectors,
distinct-face self-gluings, loops, and repeated visits to an owner in
a normal circle are allowed. Each original local edge occurrence is
a separate angle slot and normal-link interval.

There is one shared positive generalized length at each actual edge;
write its cosh as m,v,c,d,z,u. All original generalized angles are
nonnegative and sum to 2*pi around each actual edge. There is a unique
flat owner

    sigma=(M,C,D,V,C,D),

with axial M,V angles pi and transverse C,D angles zero. Every other
owner is genuine, with all its angles in (0,pi). A genuine owner

    tau=(Z,M,C,D,M,C)

exists. Assume exactly the numerical conditions

    c,d,v>1, m>1+c+d, 1<v<=m-2,
    z>1+m+c, u>m,
    (m-1)*(v-1)>=(c+d)^2,
    u<z+m+1.                                           (348.1)

The final inequality is an explicit additional upper-gap premise; it
is not inferred just from connected circles. In the original setting
where all actual circle degrees are at least six, the published
complete-star maximum-gap theorem in Sections 318--321 supplies it.
No degree lower bound is otherwise used here.

For shared coshes r,a,b,o, every genuine paired response obeys

    L=(a+b)^2-(r-1)*(o-1)>0,
    J=(r+1)*(o+1)-(a-b)^2>0.                          (348.2)

Its axial and transverse angles are the published original paired
angles, not angles of a changed frame.

**Theorem 348.2 (repo-derived).** Under these hypotheses, every
genuine owner eta with axes M,Z and transverse pair {V,C} or {V,D}
satisfies

    theta_M(eta)+theta_Z(eta)>pi.                       (348.3)

The conclusion is an angle-expense implication. It does not assert
that such an eta exists, force an opposite-companion receiver, exclude
the unique flat, or solve the general six-edge CFMP problem.

## 349. Original capacities and the bad M/Z owner

**Proof of Theorem 348.2.**

All genuine original M slots together have total pi, and the same
holds for V. All genuine D slots together have total 2*pi. These
statements follow by subtracting sigma's contributions from the full
angle sums. Nonnegativity bounds any subset by the same capacity.
Self-gluings do not erase an original angle occurrence.

Sigma is the only owner whose fixed transverse pair is {C,D}.
Indeed such an owner's two distinct axes lie in {M,V,Z,U}. Since
z,u>m>v, the smallest possible shifted axial product is
(m-1)*(v-1). Its L is therefore at most

    (c+d)^2-(m-1)*(v-1)<=0.

It cannot be genuine, so the unique-flat premise makes it sigma.

For eta with pair {V,C}, Theorem 332.1 applies with first axis Z and
second axial cosh r=m. Its explicit hypotheses are exactly the
relevant inequalities in (348.1), together with eta's strict L/J.
It proves (348.3). Hence suppose instead

    eta=(M,V,D,Z,V,D),
    theta_M(eta)+theta_Z(eta)<=pi.                    (349.1)

Tau and eta are distinct actual owners because tau has no V label.
Their actual M slots give

    2*beta_M(tau)+theta_M(eta)<=pi.                   (349.2)

This includes eta's real axial M occurrence. It will never be removed
from a budget or replaced by a zero charge.

## 350. Two-owner bounds without a receiver premise

The following consequences depend only on tau, eta, (348.1), (349.1),
and (349.2). In particular they do not assume an owner rho exists.

The source-flat inequality and v<=m-2 give

    (c+d)^2<=(m-1)*(m-3)=(m-2)^2-1,
    c+d<m-2, d<m-c-2<m-3, m>4.                       (350.1)

For eta, the exact axial M cosine is N_e/D_e, where

    D_e=m^2+v^2+d^2+2*m*v*d-1>0,
    N_e=2*v*d+m*(v^2+d^2)-(m^2-1)*z.

Its v derivative has sign numerator

    (N_e)_v*D_e-N_e*(D_e)_v
      =2*(m^2-1)*[-d^3+d*m*z+d*v^2+d+m*v+v*z]>0.

The d derivative is obtained by interchanging v,d; the z derivative
is negative. The signs hold throughout 1<v,d<=m-2 and z>=m.
Thus increasing v,d to m-2 and decreasing z to m strictly increases
the algebraic cosine. At that comparison point

    D_e-2*N_e=(m+1)*(7*m-9)>0.

No genuine comparison endpoint is needed. The actual genuine angle
therefore satisfies

    theta_M(eta)>pi/3, beta_M(tau)<pi/3,              (350.2)

the second statement following from (349.2).

Put p=sqrt((m-1)*(z-1)) and q=sqrt((m+1)*(z+1)). The exact
bad-eta half-angle product (349.1) is equivalent to

    p*q<=v^2+d^2+2*v*d*(q-p)/(q+p).

Since z>m>1, (q-p)/(q+p)<=1/m and
p*q>(m-1)*(z-1). Hence

    z<Zb(m,v,d):=1+[v^2+d^2+2*v*d/m]/(m-1).         (350.3)

The right side increases in both positive variables v,d.

For clarity, the published quarter-bound argument needs no rho
premise. The source M cosine, as an algebraic function, is

    C_t(z,d)=N_t(z,d)/sqrt(D_t(z)*D_t(d)),
    N_t(z,d)=c*(z+d)+m*(z*d+c^2-m^2+1),
    D_t(t)=t^2+m^2+c^2+2*t*m*c-1>0.

It increases in z,d. For example its z derivative has sign numerator

    (m^2-1)*[c*(d*z+m^2-c^2+1)+m*(d+z)]>0,

and the d version is symmetric. Set d1=m-c-1 and
z1=Zb(m,m-2,d1). Then d<d1,z<z1, and the actual source
cosine is less than C_t(z1,d1).

If c>=m/4, use m=4+b, b>0 and
c=[m/4+(m-2)*a]/(1+a), a>=0, which covers m/4<=c<m-2.
The exact polynomial from (325.3) is

    A4(m,c)=m^2*(m-1)*[D_t(z1)*D_t(d1)-4*N_t(z1,d1)^2]
           =sum_{j=0}^6 A4_j(m)*c^j,
    P4(a,b)=4^6*sum_{j=0}^6 A4_j(m)
              *[m/4+(m-2)*a]^j*(1+a)^(6-j), m=4+b.

The complete published identity in Section 331 has 69 positive
integer coefficients and positive constant 314572800. Thus P4>0,
A4>0, and |C_t(z1,d1)|<1/2. The actual cosine is smaller,
contradicting beta_M(tau)<pi/3 in (350.2). We have proved

    1<c<m/4.                                          (350.4)

Every hypothesis used in this reconstruction has been stated above;
neither a rho L/J inequality nor a rho angle is used. The bound
follows from the displayed two-owner calculation.

Finally (350.1), (350.3), and monotonicity of Zb imply

    z+m+1<Zb(m,m-2,m-3)+m+1
           =3*m-(4*m^2-m-12)/(m*(m-1))<3*m.           (350.5)

The final numerator is positive for m>4. Consequently each of
v,z,u is strictly below 3*m, using the explicit gap for u.

## 351. A uniform opposite-M transverse-angle bound

**Lemma 351.1 (repo-derived).** Let a genuine paired response
have axes r,c and transverse coshes m,d. If

    m>4, 1<c<m/4, 1<d<m-c-2, 1<r<3*m,              (351.1)

then its transverse M angle beta_M is greater than pi/3.

Its exact cosine C=N/sqrt(D(r)*D(c)) uses

    D(t)=t^2+m^2+d^2+2*t*m*d-1>0,
    N=d*(r+c)+m*(r*c+d^2-m^2+1).                    (351.2)

The r derivative has sign numerator

    N_r*D(r)-N*(r+m*d)
      =(m^2-1)*[d*(c*r+m^2-d^2+1)+m*(c+r)]>0.      (351.3)

Here m>d, and all other variables exceed one. Thus increasing r
to 3*m strictly increases C. Work now with r=3*m. In particular
c*r<m^2, by c<m/4. The d derivative has sign numerator

    E_d=N_d*D(r)*D(c)
        -N*[D_d(r)*D(c)+D(r)*D_d(c)]/2
       =(m^2-1)*P,                                (351.4)

where the exact polynomial identity is

    P=(c+r)*d^4+4*m*(c*r+1)*d^3+6*m^2*(c+r)*d^2
      +4*m*[c*r*(m^2-c*r)+m^2+c^2+r^2-1]*d
      +(c+r)*[m^4-c^2*r^2+c^2+r^2-1].              (351.5)

Every displayed summand is positive for c,r>1 and c*r<m^2.
In particular m^4-c^2*r^2>0. Hence increasing d to
d0=m-c-2 strictly increases C again. These comparisons concern
an algebraic function with positive denominators; no intermediate
or endpoint response is asserted to be genuine.

At r=3*m,d=d0 define the polynomial

    Q(m,c)=[D(r)*D(c)-4*N^2] at r=3*m,d=m-c-2.

It is positive on m>4,1<c<m/4. Here is a full finite identity
proving that assertion. Set m=4+b and
c=[1+(m/4)*a]/(1+a), so a,b>0 cover that domain. Then

    256*(1+a)^4*Q(4+b,[1+((4+b)/4)*a]/(1+a))
      =T0(b)+a*T1(b)+a^2*T2(b)+a^3*T3(b)+a^4*T4(b),

where the five coefficient polynomials are

    T0=6144*b^5+97280*b^4+602624*b^3+1831168*b^2
        +2736640*b+1612800;
    T1=768*b^6+33664*b^5+421504*b^4+2416512*b^3
        +7158144*b^2+10718080*b+6451200;
    T2=1856*b^6+57760*b^5+646432*b^4+3550400*b^3
        +10411152*b^2+15734400*b+9676800;
    T3=1424*b^6+39176*b^5+417432*b^4+2261424*b^3
        +6672544*b^2+10261120*b+6451200;
    T4=332*b^6+8910*b^5+95182*b^4+524912*b^3
        +1588368*b^2+2508160*b+1612800.              (351.6)

All 34 coefficients are positive integers. Thus Q>0 and the final
comparison cosine has absolute value less than 1/2. The actual
cosine is strictly smaller, so beta_M>pi/3, proving the lemma.

## 352. Global exclusion of the opposite-M exit

Suppose any actual owner has fixed frame, up to exchanging axes or
the two transverse labels,

    kappa=(W,M,D,C,M,D).                            (352.1)

It is not sigma, hence genuine. Four-distinctness forces
W in {V,Z,U}. Its axial cosh r is below 3*m by (350.5), including
the explicit gap when W=U. Equations (350.1) and (350.4) supply every
other condition in (351.1). Thus beta_M(kappa)>pi/3.

Kappa and eta are distinct owners because kappa has C whereas eta
does not. Their real original M slots contribute

    2*beta_M(kappa)+theta_M(eta)>2*pi/3+pi/3=pi.

This contradicts the complete genuine M capacity. Consequently no
owner of type (352.1) exists anywhere under (349.1). No claim that it
meets a source face is used. Even if a face self-glues, kappa's two
transverse M slots and eta's axial M slot remain three distinct
original occurrences.

## 353. The opposite-V comparison for all three remaining axes

Suppose any actual owner has fixed frame

    rho=(W,V,D,C,V,D).                              (353.1)

It is genuine and W in {M,Z,U}. Let r be its axial cosh. In all
three cases r<u0:=z+m+1: this is immediate for r=m or z, and it
is the explicit gap for r=u. The actual rho is strictly genuine.

Write S=beta_V+beta_D at rho and eta. Define rho's scalar
response for a varying first axis t by

    Lr(t)=(v+d)^2-(t-1)*(c-1),
    Jr(t)=(t+1)*(c+1)-(v-d)^2,
    S_r(t)=2*atan(K*sqrt(Lr(t)/Jr(t))),
    K=(sqrt(v^2-1)+sqrt(d^2-1))/(v+d)>0.

At u0, writing Le=(v+d)^2-(m-1)*(z-1)>0, one has

    Lr(u0)=Le+z*(m-c)-m*c+1>Le>0.                 (353.2)

Indeed c<m/4<m/2 and z>m. Along [r,u0], Lr decreases but
stays positive, and Jr increases from its positive actual value.
The whole interpolation is therefore genuine and

    d(Lr/Jr)/dt=[-(c-1)*Jr-(c+1)*Lr]/Jr^2<0.     (353.3)

Choose r'=(max(m,r)+u0)/2. Then r<r'<u0 and m<r'.
Apply the published scalar implication (322.2)--(322.5) with its
independent rho-axis variable u assigned r'. Tau and eta, all their
strict L/J conditions, (349.1), and the complete partial M budget
(349.2) remain unchanged. The virtual rho is genuine by (353.2)--(353.3),
and m<r'<z+m+1 supplies the old theorem's exact rho-axis order.
Its scalar conclusion is

    theta_D(tau)+2*S_r(r')+2*S(eta)>3*pi.

Since S_r(r)>S_r(r'), we obtain at the actual rho

    theta_D(tau)+2*S(rho)+2*S(eta)>3*pi.           (353.4)

This is a local comparison of scalar responses. When W=M or Z,
the virtual r' is not substituted for the global m or z anywhere
else, and is not asserted to define a shared metric or an owner.
The published result explicitly supplies this scalar implication;
its separate actual-incidence corollary is not applied to virtual
data. No receiver with axial label U is needed for this comparison.

The actual owners tau,rho,eta are distinct: tau has no V, and rho
has C whereas eta does not. The charge in (353.4) consists of tau's
one D-axis slot, rho's two V and two D slots, and eta's two V and
two D slots. Its actual capacity is at most pi+2*pi. Therefore
(353.4) is impossible, and every owner of type (353.1) is globally
absent under (349.1).

## 354. Original-corner transport and actual-circle closure

In the fixed edge order (12,13,14,34,24,23), the original faces
of any paired frame (R,A,B,O,A,B) are

    F4=(123): {R,A,B}, F3=(124): {R,A,B},
    F2=(134): {O,A,B}, F1=(234): {O,A,B}.          (354.1)

All three face labels are distinct. A face with label set {X,C,D},
where X is M or V, can therefore have only the fixed transverse
pair {C,D}, {X,C}, or {X,D}. The complete receiving possibilities
are as follows:

    Face MCD: CD -> sigma;
              MC -> an axial D interval with pair MC;
              MD -> an opposite-M owner, excluded in Section 352.
    Face VCD: CD -> sigma;
              VC -> an axial D interval with pair VC;
              VD -> an opposite-V owner, excluded in Section 353.

The first alternatives are the actual single owner sigma, by
Section 349; duplicate owners with the same CD-pair role are not
allowed. There is one D corner on each such face. Every
label-preserving original face map must send it to the receiving
D corner just classified, even when different labels have equal
numerical coshes. No paired-frame change is used.

Build the actual D normal link from one closed interval per original
local D edge occurrence, pairing its endpoints by the original face
maps. Select the set S of original intervals consisting of

1. both transverse D intervals of sigma, its edges 14 and 23;
2. every axial D interval of every owner with fixed pair MC or VC.

Each sigma interval has one endpoint on an MCD face and the other
on a VCD face: edge 14 lies on F3,F2, and edge 23 on F4,F1.
Each selected MC-pair axial interval has both endpoints on MCD
faces, and each selected VC-pair axial interval has both on VCD
faces. The complete face classification proves that every endpoint
of S is paired to an endpoint of S, possibly on the same interval.

Therefore S is a nonempty union of entire connected components of
the actual D normal-link graph. More explicitly, the original face
pairing gives two half-edges at each glued endpoint; endpoint closure
leaves no half-edge exiting S, so every finite edge path from S
stays in S. Connectedness of the actual D circle forces all of its
original intervals to belong to S.

But eta has two original transverse D intervals, with companion V
and axes M,Z. It is not sigma; neither interval is axial D. Both
are outside S, a contradiction. This proves that (349.1) is impossible
and completes the proof of Theorem 348.2.

## 355. Scope of the receiver-free M/Z implication

This argument prescribes no source partner inventory or number of
receiving owners. A source face can pair to another face of the same
owner, several faces can meet the same owner, and the actual circle
can revisit owners. The selection and transport use original edge
intervals and original face incidences throughout. Both global exit
exclusions, rather than just absence at the first source face, are
needed and were proved in Sections 352--353.

The proof retains the actual eta M-axis slot twice in its respective
valid subset budgets: first with tau to establish (350.2)--(350.4), and
then with a hypothetically existing kappa to contradict the complete
M capacity. It does not add those two subset inequalities together
or double-count eta in one total.

The one-sided upper gap u<z+m+1 is essential to the present stated
proof: it bounds an opposite-M U axis by 3*m and permits the scalar
comparison for an opposite-V U axis. It is supplied by the published
maximum-gap theorem only with that theorem's original hypotheses,
including the degree assumption; it is not a consequence of
connectedness in the weaker Section 341 normal form.

Together with Theorem 341.2, this leaves the M/U high-axis
pattern separate under the same source normal form. No full
unique-flat exclusion or general six-edge geometric realization
result is claimed.

Continuation: [six-edge high-axis expenses and the remaining owner count](CFMP_GEOMETRIC_REALIZATION_SIX_EDGE_HIGH_AXES.md).
