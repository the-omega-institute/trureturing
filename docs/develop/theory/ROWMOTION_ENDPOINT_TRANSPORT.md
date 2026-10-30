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
\(\mathscr D_n(I)\) with the following properties.

1. The diagram has six labelled endpoint tokens \(a_i,b_i\), four ordered frame
   tokens \(f_0,f_1,f_2,f_3\), and a noncrossing pairing \(a_i\)--\(b_i\). The
   six endpoint sites are the six columns in (2.1); the pairing is one of the
   five tableaux above. Sites may carry several tokens after a rotation, and
   equal sites are ordered by
   \[
   a_3<a_2<a_1<b_3<b_2<b_1. \tag{2.2}
   \]
   The frame tokens are consecutive on an oriented circle of \(L\) sites.

2. Cutting immediately before \(f_0\), reading the \(n\) non-frame sites as
   columns \(1,\ldots,n\), and taking, in each row, the cyclic interval from
   \(a_i\) to \(b_i\) selected by the order (2.2), gives back \(I\). If an
   endpoint is on a frame site, the same rule gives a (possibly repeated-endpoint)
   interval in the original rectangle. Thus the decoder always produces an
   actual subset of \(P_n\), not a quotient state.

3. Let \(\rho\) advance every endpoint token by one site while leaving the four
   frame tokens fixed, followed by the canonical recutting just described. For
   every complete reverse linear extension \(e\),
   \[
      \mathscr D_n(R_e I)=\rho\mathscr D_n(I),\qquad
      R_e^tI=\operatorname{Dec}_n(\rho^t\mathscr D_n(I))\quad(t\ge0). \tag{2.3}
   \]
   The decoder is injective on the separated-good diagrams, and therefore
   \[
      R_e^tI=I\quad\Longleftrightarrow\quad
      \rho^t\mathscr D_n(I)=\mathscr D_n(I). \tag{2.4}
   \]

4. Every diagram has \(\rho^L\mathscr D_n(I)=\mathscr D_n(I)\). Consequently the
   least period of a separated-good state divides \(L=n+4\). If the diagram has
   no nontrivial rotational stabilizer, its least period is exactly \(L\).

*Proof.* Use the reverse extension which scans row \(3\) from right to left,
then row \(2\) from right to left, then row \(1\) from right to left. It is a
legal reverse linear extension because every point in a higher row or a later
column is processed first. The global formula of Theorem 1.1 gives the same map
for every legal \(e\), so it suffices to use this scan.

For a row interval \([a,b]\), the right-to-left scan has only two possible
changes: its left endpoint can be deleted and its right endpoint can be inserted.
An interior deletion would leave two occupied points with a missing point between
them, and an interior insertion would lie between two comparable occupied points;
therefore both are illegal. The only remaining question is whether an endpoint
change is blocked by a point in one of the two other rows. With (2.1), the
answer is determined solely by the relative order of the six endpoints and by
whether the endpoint is at one of the four frame positions. Writing the six
endpoints in the order (2.2), the complete local alternatives are:

\[
\begin{array}{c|c|c}
\text{endpoint event}&\text{absent-point test}&\text{present-point test}\\ \hline
 a_i\text{ is crossed}&\text{a point of a lower row lies below and a point of an
 upper row lies above}&\text{the row interval would split}\\
 b_i\text{ is crossed}&\text{the row interval would split}&\text{a point of a lower row lies
 below and a point of an upper row lies above}.
\end{array}\tag{2.5}
\]
Here “below/above” means coordinatewise below/above the tested point. If the
first alternative in a row of (2.5) occurs, the toggle is the identity; otherwise
it flips the endpoint. This is exactly the two interval-closed toggle conditions
for an absent and a present point. Since the rows are intervals, (2.5) is an
exhaustive case split; no assumption that the six endpoint coordinates remain
distinct is used.

Now perform the scan from right to left. Away from the frame, every endpoint
crossed by the scan advances by one column. When an endpoint reaches a frame site,
(2.5) changes the selected cyclic interval to the other side of that frame. The
tie order (2.2) is precisely the order in which two such changes are processed;
thus equal endpoint coordinates and the repeated-coordinate states produced by a
boundary collision are decoded by the same rule. This proves the one-step
identity in (2.3). Induction on the number of scans proves the second identity.
The six labelled endpoints and their pairing are recovered from the decoded row
intervals whenever the initial state is separated good, so the decoder is
injective there, proving (2.4). After \(L\) advances every endpoint and every
frame cut has returned to its original site. This proves (4) and the lemma.
\(\square\)

The proof deliberately uses the original rectangle at every step. The framed
circle is only an injective bookkeeping device for the literal toggle trace; it
is not a replacement state space. In particular, collisions at \(1\) and \(n\),
coincident endpoint coordinates, and all intermediate states in the orbit remain
in \(\mathcal C_n\) and in the denominator counted below.

### 2.2. How many separated-good diagrams can have a shorter period?

A nontrivial stabilizer of a six-endpoint framed diagram repeats the endpoint
configuration at least twice around the circle. Hence the six endpoint tokens are
contained in at most three free sites in one fundamental period; the pairing has
only the five tableau choices, and the four frame tokens have at most \(L\) possible
phases. The elementary divisor count therefore gives
\[
 \#\{I\text{ separated good}:\operatorname{per}(I)<L\}\le 30L^5. \tag{2.6}
\]
The bound is intentionally coarse. To see it directly, choose a proper divisor
\(d\mid L\), choose the phase of the frame, choose at most five endpoint sites in
one \(d\)-period, and then force all remaining sites by periodicity; summing over
proper divisors and using \(d\le L/2\) gives at most \(30L^5\). This argument is
independent of the endpoint pairing and so includes every rotationally symmetric
case, not only the half-turn cases.

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

The first coordinates in the first five lines and in the last line of (2.12) are
all distinct for \(0\le t<m+2\): the first five are
\(m,m+1,m+2,m+3,m+4\), while the remaining values are \(3,4,\ldots,m-1\).
Therefore no positive \(d<m+2\) fixes \(E_m\). Hence
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
