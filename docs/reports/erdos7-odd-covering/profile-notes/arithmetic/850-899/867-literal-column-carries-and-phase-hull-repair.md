[Index](../../../marked_head_profile.md) · [Complete source and stripping](865-whole-component-digit-stripping-and-shared-parent-repairs.md) · [Same-component budget](866-whole-color-top-layer-exchange-forces-lower-row-service.md) · [Nested-slot precedent](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#69-cross-cofactor-divisor-payment-reduces-exactly-to-nonconcentrated-ancestors)

# Downward literal transports leave one possible parent liability per q-column

Keep the actual globally count-minimal distinct odd whole cover,
the numerical divisor closure, and the complete masked component
source of Report861. Fix one component C and a moving color c.
Stripping that color covers the entire deletion hole of C, as in
Report865. Numerical collisions with retained originals can be
reduced before assigning any fresh repair tags.

Within each numerical q-column, reduce retained classes literally
to unused lower moduli. This enlarges their entire arithmetic
progressions. All but at most one original parent in that column can
be retained in this way. The one possible liability occurs exactly
when the lowest deleted level belongs to the selected color.

The subsequent phase-hull repair is conditional: it requires actual
compatible divisor tags for groups of those remaining parents.
Complete color coverage does not supply those tags or phase
agreements by itself.

## An exact prefix deficiency on one numerical column

Write a numerical q-column as

$$
r q^j,\qquad r=3^a m,\quad (r,q)=1,\quad m>1,
\qquad 0\le j\le H_r.
\tag{LC1}
$$

Divisor closure supplies its complete initial segment of original
labels. The phases $\alpha_{r,j}$ of these originals remain their
actual phases; no compatibility between them is assumed.

Let $D_r\subseteq\{1,\ldots,H_r\}$ be the levels belonging to
C and $T_{r,c}\subseteq D_r$ those belonging to color c. The
normalized classes reserve the distinct numerical levels

$$
L_{r,c}=\{j-1:j\in T_{r,c}\}.
\tag{LC2}
$$

Every other original at level j can legally use a still available
level $\ell\le j$, because literal reduction gives

$$
[\alpha_{r,j}]_{rq^j}\subseteq[\alpha_{r,j}]_{rq^\ell}.
\tag{LC3}
$$

This is a different operation from first-digit stripping: the old
residue is reduced without dividing or shifting it.

For a prefix $[0,t]$, the retained old demand minus the number of
unreserved positions is exactly

$$
\begin{aligned}
\Delta_{r,c}(t)
&=|([0,H_r]\setminus D_r)\cap[0,t]|
  -|([0,H_r]\setminus L_{r,c})\cap[0,t]|\\
&=\mathbf1_{\{t+1\in T_{r,c}\}}
  -|(D_r\setminus T_{r,c})\cap[1,t]|.
\end{aligned}
\tag{LC4}
$$

Indeed $|L_{r,c}\cap[0,t]|=|T_{r,c}\cap[1,t+1]|$,
and $T_{r,c}\subseteq D_r$. The term at $t=H_r$ uses the
empty event $H_r+1\in T_{r,c}$.

If $D_r$ is nonempty, put $d_r=\min D_r$. When
$d_r\notin T_{r,c}$, every positive selected endpoint has an
earlier other-color deletion, and LC4 is nonpositive. When
$d_r\in T_{r,c}$, the maximum positive deficiency is exactly
one: it is attained at $t=d_r-1$. Set aside the actual original

$$
P_{r,c}=[\alpha_{r,d_r-1}]_{rq^{d_r-1}}.
\tag{LC5}
$$

It is retained before this exchange, since no lower level belongs
to C. Removing it subtracts one from every prefix at or beyond
$d_r-1$, precisely where a positive LC4 could occur.

In either case the remaining demand satisfies every prefix
capacity. List the remaining old levels and the unreserved levels
in increasing order and assign the kth old level to the kth
unreserved level. The prefix inequalities give $\ell\le j$
for each assignment. This proves existence of one simultaneous
injective assignment, with no intermediate collision state used as
a competing cover. If $D_r$ is empty, leave the entire column
unchanged.

Within this downward, one-old-class-per-position transport, the
unpaid count is therefore exactly

$$
\delta_{r,c}=\mathbf1_{\{\min D_r\in T_{r,c}\}}.
\tag{LC6}
$$

For an empty $D_r$, set $\delta_{r,c}=0$.

This statement does not rule out additional containment credits or
transports between different numerical columns.

## The complete hole after all column transports

Let $\mathcal Z_c$ be the actual parents LC5 over all columns
with $\delta_{r,c}=1$, and put $s_c=|\mathcal Z_c|$.
Delete C and these parents. Insert all $k_c=|C_c|$ normalized
classes, and assign every other original as above. Call the
resulting preliminary family $\mathcal F_c$.

The assignments are numerically injective within a column and
avoid the reserved levels. Different columns have different q-free
parts r, so their labels cannot collide. Every modulus remains odd
and greater than one; affected columns have $m>1$. The pure 3 and
9 guards are unchanged. The exact count is

$$
|\mathcal F_c|=N-M-s_c+k_c.
\tag{LC7}
$$

Every transported retained class contains its complete old class.
The selected normalized family covers the complete deletion hole
$E_C$. It follows that

$$
\mathbb Z\setminus\bigcup\mathcal F_c
\subseteq\bigcup_{P\in\mathcal Z_c}P.
\tag{LC8}
$$

For a proof, take an integer outside the right side and outside
$\mathcal F_c$. It misses every old original outside C, since
each such original is either a set-aside parent or lies in its
transported replacement. It therefore belongs to $E_C$, where
the selected normalized family covers it, a contradiction.

Credit any complete parent already contained in one actual class
of $\mathcal F_c$. The exact test for
$P=[\alpha_P]_{h_P}$ and $A=[\eta_A]_{d_A}$ is

$$
P\subseteq A
\iff d_A\mid h_P\ \text{and}\
\alpha_P\equiv\eta_A\pmod{d_A}.
\tag{LC9}
$$

Let $\mathcal P_c\subseteq\mathcal Z_c$ be the parents not
paid by this test. LC8 remains valid with $\mathcal P_c$ on
its right. Equality between a normalized class and an old parent
is a valid credit, including q-bearing parents. The test is only
a sufficient way to remove a liability from the list: a union of
several preliminary classes can cover a parent without one of
them containing it individually.

## Pay a group once when its literal phases permit it

For a nonempty group $K\subseteq\mathcal P_c$, write each
parent modulus as $h_P=3^{a_P}t_P$, with $(t_P,3)=1$, and
let $\beta_P$ be its literal residue modulo $t_P$. Fix
$P_0\in K$ and set

$$
g(K)=\gcd\bigl(\{t_P:P\in K\}
\cup\{\beta_P-\beta_{P_0}:P\in K\}\bigr).
\tag{LC10}
$$

The gcd uses absolute values for signed differences. Since the
positive $t_P$ are included, it is positive. Changing a residue
representative or the anchor $P_0$ leaves it unchanged. The
nonunit moduli compatible with every parent phase are exactly

$$
\{e>1:e\mid t_P\ \forall P,\
\beta_P\equiv\beta_{P'}\pmod e\ \forall P,P'\}
=\operatorname{Div}(g(K))\setminus\{1\}.
\tag{LC11}
$$

Thus the complete parent union has the enclosing AP

$$
\bigcup_{P\in K}P\subseteq[\beta_{P_0}]_{g(K)}.
\tag{LC12}
$$

This is an enlargement of the repair obligation, not an assumption
that $V_C$ is a coset or a favorable pruning of its points.
The possible q-powers of the parents remain in $t_P$ and $g(K)$.

Suppose $\mathcal P_c$ has a partition into L nonempty groups
and each group has ten nonunit divisors of $g(K)$, with all
$10L$ selected tags globally distinct. Apply Report865's shared
forest to these L enclosing APs, regarded as ternary-height-zero
parents. Together with the retained pure 3 and 9 guards, its
$23L+2$ classes cover all the enclosing APs, hence all remaining
old parent liabilities. Its numerical labels have ternary height
at least three and are fresh against $\mathcal F_c$.

The final family therefore has distinct odd nonunit moduli, covers
every integer, and has count

$$
N'=N-M-s_c+k_c+23L+2.
\tag{LC13}
$$

For an arbitrary component, all n colors are nonempty, so
$M-k_c\ge n-1$. At $n\ge83$, $L\le3$ gives a strict
count decrease. On the same component selected by CD21, the
stronger Report866 bound $M-k_c\ge465$ permits $L\le20$.
The actual nonempty partition gives an additional credit:
$L\le|\mathcal P_c|\le s_c$. Therefore

$$
23L+2-s_c\le22L+2\le464<465
\qquad(L\le21).
\tag{LC14}
$$

Thus 21 groups suffice on the CD21 component. This refinement uses
the actual parents removed from the preliminary family; an arbitrary
repair budget with unrelated s and L would not have this credit.
If $\mathcal P_c$ is empty, no repair is needed and the
preliminary family already gives a strict decrease.

Consequently, in the $n\ge83$ branch, every color in an actual
globally minimal source must have $\mathcal P_c\ne\varnothing$ and

$$
\tau\bigl(g(\mathcal P_c)\bigr)\le10.
\tag{LC15}
$$

Otherwise one group supplies ten distinct nonunit divisors and
the preceding repair applies. More generally, the stated three-
group certificate is impossible for every component, and the
twenty-one-group certificate is impossible for the CD21 component.
These restrictions do not prove that any such certificate exists.

## Reuse and remaining source condition

The ordered assignment specializes the existing nested-neighborhood
matching mechanism of Report385 DP12. PI8--PI9 supplies an earlier
one-deficit-per-column inventory assignment, but does not itself
transport complete original classes. LC3 and LC8 supply that
whole-cover interface here. The phase-hull test reuses the complete
congruence-hull and donor-containment interfaces, and the repair
forest is the already established Report865 packet.

What remains unresolved is whether one actual color supplies
enough compatible phase-hull groups, further containment credits,
or a different complete repair. No abstract noncover fixture is
used to infer either existence or nonexistence of that structure
in a whole cover.

## Verification scope

A cache-guarded exact Lean application checks the actual numerical
columns, the set-aside original parents, and one simultaneous downward
assignment. Its whole-integer consumer derives the normalized color
service from the actual component source; neither that service nor
the assignment is supplied as an extra assumption. It checks global
numerical injectivity, odd nonunit labels, the exact count, unchanged
unit-cofactor originals including the pure 3 and 9 guards, and the
complete parent-union bound on the remaining hole. Actual parent
existence uses divisor closure of the whole original family, not of
the selected component.

The same application connects actual parent-to-hull divisibility and
literal phase agreement to the existing shared forest, includes the
retained guards in its coverage, and applies global count-minimality.
The nonempty-partition cardinality and the three-, twenty- and
twenty-one-group count comparisons are also checked. The application
exits successfully with 128 accepted axiom-closure reports and no
errors or `sorryAx`; it reuses the existing forest and CRT machinery.

The explicit gcd formula LC10--LC12 and its representative-independence
argument remain ordinary mathematics; the checked forest consumer
takes their divisibility and phase interface as input. The existence
of suitable groups and globally distinct tags remains unproved.
No new Lean declaration, freezing record or coverage claim is retained.
