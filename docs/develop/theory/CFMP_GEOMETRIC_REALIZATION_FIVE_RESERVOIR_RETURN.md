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
