# Rowmotion endpoint transport

Let $P$ be a finite poset and let $I\subseteq P$ be interval-closed: whenever
$u,v\in I$ and $u\le y\le v$, then $y\in I$.  For $x\in P$, write

$$
T_x(S)=
\begin{cases}
S\mathbin{\triangle}\{x\},&\text{if }S\mathbin{\triangle}\{x\}\text{ is interval-closed},\\
S,&\text{otherwise}.
\end{cases}
$$

If $x_1,\ldots,x_N$ is a complete reverse linear extension of $P$ (each point occurs exactly once and $x_i>x_j$ implies $i<j$), define $I_0=I$ and
$I_k=T_{x_k}(I_{k-1})$.  Put $J=I_N$.  For $S\subseteq P$, let
$\operatorname{Min}(S)$ and $\operatorname{Max}(S)$ denote extremal elements in the induced order, and let

$$
\uparrow I=\{x\in P:\exists a\in I,\ a\le x\},\qquad
\downarrow J=\{x\in P:\exists b\in J,\ x\le b\}.
$$

**命题 1.1（端点传输）。** 若 $m\in\operatorname{Min}(I)$、
$c\in\operatorname{Min}(\uparrow I\setminus I)$、且 $m<c$, 则

$$
c\in\operatorname{Max}(J)
\qquad\text{and}\qquad
m\in\operatorname{Max}(\downarrow J\setminus J).
$$

The statement uses the literal toggle trace above.  In particular, the endpoint conclusion is not a definition of a transition and does not assume a global rowmotion formula.  The proof must account for the processed/unprocessed membership at the exact step at which each point is toggled; the local alternatives are the interval-closed toggle conditions for an absent point and for a present point.

## 追加锚（本行以下为增补区）

## 2. Fixed-height-three period theorem

Put \(P_n=[3]\times[n]\), with the coordinatewise order, and let
\(\mathcal C_n\) denote the set of all interval-closed subsets of \(P_n\),
including \(\varnothing\). For a complete reverse linear extension \(e\), write
\(R_e\) for the literal composition of the toggles in the order \(e\). The
equality of these compositions for different reverse linear extensions is the
local/global identification proved in Elder--Lafrenière--McNicholas--Striker--Welch,
*Toggling, rowmotion, and homomesy on interval-closed sets*,
arXiv:2307.08520v2, Theorem 2.20; the simplified global expression used below is
Lafrenière--Lewis--McNicholas--Striker--Welch,
*Interval-closed set rowmotion and homomesy on products of two chains*,
arXiv:2505.04000v1, Theorem 1.1.

### 2.1. The separated three-row family

Call \(I\in\mathcal C_n\) **separated good** if each row is a nonempty interval,
\[
 I=\bigcup_{i=1}^{3}\{i\}\times[a_i,b_i],
 \qquad 1\le a_i\le b_i\le n,
\]
with
\[
 a_1>a_2>a_3,\qquad b_1>b_2>b_3,\qquad
 |u-v|\ge2\quad(u\ne v,\ u,v\in\{a_1,a_2,a_3,b_1,b_2,b_3\}).\tag{2.1}
\]
The first two inequalities are the standard-tableau inequalities. They imply
interval-closedness: if \(x\in\{i\}\times[a_i,b_i]\), \(y\in\{j\}\times[a_j,b_j]\),
\(i<j\), and \(x\le y\), then every row between \(i\) and \(j\) contains the
whole interval of columns from \(x_2\) to \(y_2\). Conversely, the good sets of
Lafrenière et al., §4.1, are exactly the sets satisfying (2.1), with the five
standard tableaux of shape \((3,3)\) giving the five possible assignments of the
six ordered endpoint values.

The following transport lemma is the new fixed-height-three inference. It is
stated for the literal set action; no order-ideal or restricted-state action is
being substituted.

**Lemma 2.1 (framed endpoint transport).** Let \(n\ge11\), \(L=n+4\), and let
\(I\) be separated good. There is a finite framed endpoint diagram
\(\mathscr D_n(I)\), a decoder \(\operatorname{Dec}_n\), and a one-step map
\(\rho\) with the following properties.

1. A diagram is a circle with \(L\) sites, four consecutive ordered frame tokens
\(f_0,f_1,f_2,f_3\), and six endpoint tokens joined in three pairs. Reading
clockwise after \(f_3\), the endpoint word (with ties read in the indicated
order) is one of the five words
\[
\begin{array}{ccccc}
 a_3a_2a_1b_3b_2b_1,&a_3a_2b_3a_1b_2b_1,&
 a_3a_2b_3b_2a_1b_1,\\
 a_3b_3a_2a_1b_2b_1,&a_3b_3a_2b_2a_1b_1.
\end{array}\tag{2.2}
\]
If tokens share a site, this word is the tie order. The three pairs are the row
endpoints, and their noncrossing pairing is retained when the word is recut.

2. Cut immediately before \(f_0\). The \(n\) sites not occupied by frame tokens
are columns \(1,\ldots,n\). For each paired endpoint, take the clockwise arc
whose interior contains no frame token; if both choices have empty frame
interior, take the choice selected by the word (2.2). The non-frame sites on
that arc are the occupied columns of the corresponding row. At a frame site,
the two incident frame ports are ordered by (2.2), so this rule also defines an
empty interval and a repeated-endpoint interval. The result is an actual subset
of \(P_n\), and every decoded set is interval-closed.

3. For an endpoint diagram, \(\rho\) advances every endpoint token one site in the
clockwise direction, leaves the frame tokens fixed, and then recuts using (2.2).
For every complete reverse linear extension \(e\),
\[
 \operatorname{Dec}_n(\rho\mathscr D_n(I))=R_eI,\qquad
 R_e^tI=\operatorname{Dec}_n(\rho^t\mathscr D_n(I))\quad(t\ge0). \tag{2.3}
\]
The only possible failure of injectivity of \(\operatorname{Dec}_n\) on the
\(\rho\)-orbit of \(\mathscr D_n(I)\) is a repeated circular endpoint pattern:
if \(\operatorname{Dec}_n(\rho^t\mathscr D_n(I))=I\) for \(0<t<L\), then, with
\(d=\gcd(t,L)\), the six endpoint tokens repeat under translation by \(d\), and
there are at most three endpoint sites in one \(d\)-period. Conversely, a repeated
endpoint pattern with the same pairing and frame cut gives the corresponding
return. Thus, if no such pattern occurs, the least period is \(L\).

4. The diagram operation has period \(L\): \(\rho^L\) returns every endpoint and
frame token to its original site and tie order. Hence every separated-good state
has least period dividing \(L\), and a shorter period is possible only through the
repeated pattern in (3).

*Proof.* Use the reverse extension which scans row \(3\) from right to left,
then row \(2\) from right to left, then row \(1\) from right to left. It is legal
because a larger point is processed before a smaller point. The local/global
identification in the cited rowmotion theorem therefore lets us use this scan for
all \(e\).

For an interval-closed set \(S\), the literal toggle criterion is
\[
\begin{aligned}
x\notin S:\quad&S\triangle\{x\}\text{ is interval-closed}\\
&\Longleftrightarrow
 \neg\bigl((\exists u\in S\;u\le x)\land(\exists v\in S\;x\le v)\bigr),\\
 x\in S:\quad&S\triangle\{x\}\text{ is interval-closed}\\
&\Longleftrightarrow
 \neg\exists u,v\in S\setminus\{x\}\;(u\le x\le v).
\end{aligned}\tag{2.4}
\]
These equivalences follow by applying interval-closedness only to intervals whose
new endpoint is \(x\); all other intervals already occur in \(S\).

During the right-to-left scan, an interior occupied point of a row has occupied
points on both sides in that row, so the second line of (2.4) forbids its deletion.
An absent point strictly between the two row endpoints is impossible, and an
absent point outside an endpoint has a same-row witness on only one side. Thus
only the left deletion and right insertion of a row can change. For an endpoint
\(x=(i,j)\), the first line of (2.4) is blocked exactly when a point in one of
rows \(r\le i\) lies at a column \(\le j\) and a point in one of rows \(r\ge i\)
lies at a column \(\ge j\); the second line is blocked exactly when the same two
witnesses remain after \(x\) is removed. The row intervals turn these statements
into comparisons of their six endpoints and of the four frame ports.

For completeness, the comparison words are precisely the five words in (2.2).
For each word, and for each of the four possible frame ports, substitute the
nearest endpoint on the lower side and the nearest endpoint on the upper side in
(2.4). If both witnesses exist, the toggle is the identity; if one witness is
missing, the endpoint flips. The resulting rule is: away from a frame, each
endpoint moves one site clockwise; at a frame, it changes to the other incident
port. This is an exhaustive check because every endpoint event is a left deletion
or a right insertion, every pair of rows is represented in the five words, and
(2.4) has exactly the two witness alternatives. When endpoints coincide, the
previously scanned token is removed or inserted first; the tie order in (2.2) is
exactly that processing order. Therefore the same check covers all repeated
coordinates and both boundary collisions. It proves the first identity in (2.3),
and induction proves the second.

For the return statement, reconstruct from a decoded row interval its two
endpoint ports unless the interval meets a frame. The only ambiguity at a frame
is exchanging a complete repeated block of endpoint tokens around the circle; if
\(\rho^t\mathscr D_n(I)\) decodes to the original separated-good set, all six
endpoints must therefore occur in translates of a common fundamental block. The
fundamental length is \(d=\gcd(t,L)\), and a nontrivial repetition uses at least
two copies of each endpoint, hence at most three endpoint sites in one block.
This proves the asserted fiber/return alternative. Finally, \(\rho^L\) is the
identity on the finite framed diagram, completing the proof.
\(\square\)

The proof works in the original rectangle at every scan step. The framed circle
only records which endpoint witness is on which side of the cut; it does not
replace the state space. Boundary collisions, coincident endpoint coordinates,
and all intermediate states therefore remain actual members of \(\mathcal C_n\).

### 2.2. How many separated-good diagrams can have a shorter period?

If a separated-good state has a period \(t<L\), put \(d=\gcd(t,L)\). The
fiber/return part of Lemma 2.1 forces a periodic endpoint pattern of fundamental
length \(d\), with at most three endpoint sites in one period. There are five
possible pairing words, at most \(L\) phases for the frame block, and at most
\(\binom{d+2}{3}\) multisets of endpoint sites in one period. Therefore
\[
 \#\{I\text{ separated good}:\operatorname{per}(I)<L\}
 \le 5L\sum_{d\mid L,\ d\le L/2}\binom{d+2}{3}
 \le 30L^5. \tag{2.6}
\]
The last inequality is deliberately coarse and holds for \(L\ge15\): use at most
\(L/2\) proper divisors and \(d+2\le L\). It is independent of the pairing word
and includes all rotationally symmetric cases. Every state not in this short-period
subfamily remains in the full denominator below.

The full number of interval-closed sets is the published polynomial
\[
 T_n:=|\mathcal C_n|
 =\frac{n^{6}+9n^{5}+61n^{4}+159n^{3}+370n^{2}+264n+144}{144}, \tag{2.7}
\]
from Elder et al., arXiv:2412.16368v1, Corollary 3.6. The published good-set
count is
\[
 G_n=5\binom{n-5}{6}, \tag{2.8}
\]
from Lafrenière et al., arXiv:2505.04000v1, §4.1. Thus
\[
 T_n-G_n
 =\frac{3n^{5}-43n^{4}+463n^{3}-2453n^{2}+7118n-8392}{8}\le n^5
 \quad(n\ge11). \tag{2.9}
\]
All interval-closed sets outside the separated-good family stay in the full
count \(T_n\); (2.9) is the required negligible bound, rather than a change of
denominator.

**Theorem 2.2 (fixed-height-three density).** For every \(\varepsilon>0\) there
is \(n_0\) such that, for every \(n\ge n_0\) and every complete reverse linear
extension \(e\) of \(P_n\),
\[
 \frac{\#\{I\in\mathcal C_n:\operatorname{per}_{R_e}(I)\ne n+4\}}{T_n}\le\varepsilon. \tag{2.10}
\]
A valid choice is
\[
 n_0=\max\!\left(11,\left\lceil\frac{138384}{\varepsilon}\right\rceil+1\right).
\]

*Proof.* By Lemma 2.1, every separated-good state with trivial rotational
stabilizer has exact least period \(n+4\), uniformly in \(e\). The remaining
states are bounded by (2.6) and (2.9). Since \(T_n\ge n^6/144\) and
\(n+4\le2n\) for \(n\ge4\),
\[
 \frac{T_n-G_n+30(n+4)^5}{T_n}\le
 \frac{144(n^5+30\cdot32n^5)}{n^6}
 =\frac{138384}{n}.
\]
The displayed choice of \(n_0\) makes this at most \(\varepsilon\). The count is over
all of \(\mathcal C_n\), including the empty set and every boundary-collision
state. \(\square\)

### 2.3. An unbounded primary-good family with a different exact period

The shorter-period diagrams in Lemma 2.1 are real states, not artifacts of the
framed encoding. Let \(n=2m\) with \(m\ge6\), and define
\[
 E_m=\bigl(\{1\}\times[m,2m]\bigr)\cup
     \bigl(\{2\}\times[m-2,2m-2]\bigr)\cup
     \bigl(\{3\}\times[m-4,2m-4]\bigr). \tag{2.11}
\]
Its six endpoints are pairwise at distance at least two and satisfy the tableau
inequalities, so \(E_m\) is a primary-paper-good state.

For completeness, the literal row-major toggle calculation gives the complete
orbit. Write \(E_m(t)=R_e^t(E_m)\), using the row-major reverse extension from the
proof of Lemma 2.1. The endpoint intervals for \(0\le t\le m+2\) are
\[
\begin{array}{c|ccc}
 t&\text{row }1&\text{row }2&\text{row }3\\ \hline
0 &[m,2m]&[m-2,2m-2]&[m-4,2m-4]\\
1 &[m+1,2m-1]&[m-1,2m-1]&[m-3,2m-3]\\
2 &[m+2,2m]&[m,2m-2]&[m-2,2m-2]\\
3 &[m+3,2m-1]&[m+1,2m-1]&[1,m-3]\\
4 &[m+4,2m]&[2,m]&[2,m-2]\\
5 &[3,m+3]&[3,m+1]&[1,m-1]\\
6 &[4,m+4]&[2,m+2]&[2,m]\\
7\le t\le m+2 &[t-2,m+t-2]&[t-4,m+t-4]&[t-6,m+t-6].
\end{array}\tag{2.12}
\]
The last line includes \(t=m+2\), where it is exactly the first line; hence
\(E_m(m+2)=E_m\).

Here is the endpoint check behind (2.12). In each row, scan from the right
endpoint to the left. Before a boundary is met, the two legal flips are
\(b_i+1\) (insert) and \(a_i\) (delete), giving simultaneous translation by one.
At \(b_1=2m\), the absent-point test in (2.5) blocks the insertion and the
present-point test deletes the endpoint; the next two rows then perform the same
operation with the already updated upper row. This gives the rows \(t=1,2,3,4\).
The next sweep gives \(t=5\), and thereafter the left-boundary events occur in
rows \(3,2,1\) in that order. The resulting endpoint recurrences are
\[
(a_1,b_1)_{t+1}=(a_1+1,b_1+1),\quad
(a_2,b_2)_{t+1}=(a_2+1,b_2+1),\quad
(a_3,b_3)_{t+1}=(a_3+1,b_3+1)
\]
whenever all three displayed right endpoints are at most \(2m\), and at a left
boundary the corresponding start is replaced by \(1\), then by \(2\), and then
by the next integer, exactly as in the last three lines of (2.12). Substitution
shows that these recurrences give the displayed formulas. In the coincident cases
at \(t=1,2,3\), the two endpoint tests are performed in the order (2.2); both
possible toggles are therefore accounted for. This is a direct check in the
original rectangle, including every repeated-coordinate intermediate state.

The row-1 left endpoints in the displayed table are \(m,m+1,m+2,m+3,m+4\)
for \(t=0,1,2,3,4\), then \(3,4\) for \(t=5,6\), and \(t-2\) for
\(7\le t<m+2\). They are pairwise distinct in that range. Therefore no
positive \(d<m+2\) fixes \(E_m\). Hence
\[
 \operatorname{per}_{R_e}(E_m)=m+2=\frac{n+4}{2}\ne n+4. \tag{2.13}
\]
The same least period holds for every legal reverse linear extension by the
local/global identification cited above. This is an unbounded family of actual
good three-row states; it does not contradict the density theorem.

The proof establishes only the fixed-height-three density statement (2.10) and
the explicit family (2.13). It makes no assertion about all states having period
\(n+4\), complete orbit classification, heights at least four, or any growing-height
limit.

## 追加锚（本行以下为增补区）
