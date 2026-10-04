[Index](../../../marked_head_profile.md) · [Component codes](850-cofactor-dependent-protected-codes.md) · [Retained pure repair](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#15-retained-pure-powers-reduce-the-fresh-repair-forest)

# Complementary phase repair and actual pair-anchor rigidity

In a globally count-then-modulus-sum minimal distinct odd cover with
$H_3=2$, at most 29 original classes can agree with a prescribed
five-prime phase vector on at least four present cofactor coordinates.
This includes q-free originals and imposes no bound on the five prime
sizes. For q-bearing originals the bound improves to 28 when the
selected primes are at most q. A five-clique of actual moving bottom
pair anchors consequently forces the full-support owner graph to be
connected. It does not establish masked connectivity or exclude the
whole covering family.

## One original family and a simultaneous liability

Keep one EB1-minimal whole cover, with pairwise distinct odd numerical
moduli greater than one, minimizing class count first and modulus sum
second. Assume

$$
Q=9q^G W,\qquad q=113,\qquad (W,3q)=1.
$$

The actual pure 3 and 9 classes are present and disjoint, as supplied
by numerical divisor closure and comparable-original disjointness.
Every original has ternary height at most two. Minimality is global:
a competing cover may have ternary height three.

Choose five distinct primes $P=\{p_1,\ldots,p_5\}$ dividing W, put
$h=\prod_{p\in P}p$, and fix literal residues $w_p\bmod p$.
For an original modulus $d_i=3^{a_i}q^{j_i}m_i$, allowing $j_i=0$,
define

$$
I_P(w)=\left\{i:
\#\{p\in P:p\mid m_i,\ \rho_i\equiv w_p\pmod p\}\ge4
\right\}.
\tag{CP1}
$$

An original containing all five primes is included even if its phase
at the fifth prime differs. Every integer in any selected class
agrees with the prescribed vector on at least four coordinates.
No assumption is made about its ternary word, q-word, higher cofactor
exponents or other cofactor primes.

## Twenty-nine fresh classes cover the entire region

The retained pure guards cover twelve roots modulo 27 and leave
fifteen safe roots. The thirty nonunit proper divisors of squarefree h
form fifteen unordered complementary pairs $\{e,h/e\}$. Choose
fourteen pairs. Assign tag 1 to one safe root and one complementary
pair to each of the other fourteen safe roots.

At a root $r\bmod27$, a tag $e$ denotes the CRT class

$$
x\equiv r\pmod{27},\qquad x\equiv w\pmod e,
\qquad\text{with modulus }27e,
\tag{CP2}
$$

where $w\bmod h$ is the CRT combination of the prescribed residues.
The tag-1 condition is empty. This gives exactly

$$
1+2\cdot14=29
\tag{CP3}
$$

new classes with distinct tags and distinct numerical moduli. All
new moduli are odd nonunits with ternary height three, hence globally
fresh among the originals. They divide $3Q$.

To check the entire removed union, take any integer agreeing with w
on at least four of the five coordinates. A retained pure guard pays
for it if its ternary root is unsafe. The tag-1 class pays for the
single root assigned tag 1. At every other safe root, the possibly
unmatched prime belongs to at most one side of the assigned
complementary pair. The other side contains only matching primes,
so its CRT class covers the integer. This argument covers all integer
lifts and does not restrict the liability to private points.

Delete any thirty originals in $I_P(w)$ and insert these 29 classes.
Neither pure guard is deleted. The entire old union remains covered,
and the new cover has one fewer class. EB1 therefore gives

$$
\boxed{|I_P(w)|\le29.}
\tag{CP4}
$$

The count objective alone proves CP4; no price estimate, q-bearing
condition or prime-size bound is used. The retained-pure mechanism
is the one in Report 385, Section 15; the complementary pairs supply
one repair for the simultaneous union of five four-prime phases.

## A sharper q-bearing bound

Let $I_P^+(w)$ contain only the members with $j_i\ge1$, and assume
$p_{\max}\le q$. Select 29 such originals, choose four matching
primes for each, and assign it to one of the five products $h/p_t$.
Let the group sizes be $k_t$, with $\sum_t k_t=29$.

In group t the numerical moduli are distinct positive odd multiples
of $qh/p_t$. Thus

$$
\Sigma_{\rm old}
\ge q\sum_{t=1}^5\frac{h}{p_t}k_t^2
\ge h\sum_{t=1}^5k_t^2
\ge169h.
\tag{CP5}
$$

The last minimum is attained at group sizes $6,6,6,6,5$. The 29
fresh moduli constructed above have total

$$
\Sigma_{\rm new}<27\sigma(h)
\le27(6/5)^5h
=\frac{209952}{3125}h
<81h<169h.
\tag{CP6}
$$

All selected primes are at least five. Consequently equal class count
and strictly smaller modulus sum contradict EB1, proving

$$
\boxed{|I_P^+(w)|\le28\quad\text{if }p_{\max}\le q.}
\tag{CP7}
$$

Other primes in W, their exponents, and the remaining factors of the
selected originals are unrestricted by this comparison.

## Exact phase packing across all rows and heights

Let $N_{4,t}$ count originals whose cofactor support intersects P in
exactly $P\setminus\{p_t\}$, and let $N_5$ count those containing
all five primes. The counts include every ternary row and every
q-height, including zero. A four-prime owner qualifies in exactly
$p_t$ phase vectors. A five-prime owner qualifies in
$1+\sum_{p\in P}(p-1)=\sum_{p\in P}p-4$ vectors. Summing CP4 over
all h vectors gives

$$
\boxed{
\sum_t p_tN_{4,t}
+\left(\sum_{p\in P}p-4\right)N_5\le29h.
}
\tag{CP8}
$$

For q-bearing counts alone, the right side is $28h$ under CP7's
prime-size premise. These are counts of the actual numerical
originals and their phases; no independent cofactor law is used.

## Pair anchors and full-support connectivity

Use Report 850's actual moving digit set
$U\subseteq\mathbb F_q\setminus P_{\rm protected}$ and $n=|U|$.
The protected set contains the first digits of every unit-cofactor
original at every row and q-height. Moving owners retain all rows
and heights. Their full supports are

$$
R_i=\{(u,v)\in\mathcal A\times\mathbb Z/W:
 u\equiv\rho_i\pmod{3^{a_i}},\quad
 v\equiv\rho_i\pmod{m_i}\},
$$

where $\mathcal A$ is the five-word safe set modulo 9.

Define a graph $\Gamma$ on the actual cofactor primes. Its edge
$\{p,s\}$ means an actual moving bottom-row original exists with
modulus

$$
q^jp^as^b,\qquad j,a,b\ge1.
\tag{CP9}
$$

Its cofactor support must be exactly that pair, and its first q-digit
must lie in U. Numerical divisor closure does not alone supply such
an edge; its pair-supported original may have a protected digit.

Suppose $\Gamma$ contains a $K_5$ on P. Choose its ten actual pair
anchors. Anchors on disjoint pairs have coprime cofactors and permit
every safe ternary word, so their full supports intersect by CRT.
Two overlapping pairs connect through the complementary pair on the
remaining two primes. All ten anchors therefore lie in one component
$C_*$.

An owner outside $C_*$ must contain at least four primes of P in
its cofactor. Otherwise a pair disjoint from its cofactor supplies
an anchor with intersecting full support. At a complete private point
of any outside owner, hold the preserved pair and a higher-q suffix
fixed and vary the first q-digit through U. Whole coverage supplies
n different moving owners at the same preserved point. They all
remain outside $C_*$ and match the same actual P-phase on their
present coordinates. CP4 contradicts $n\ge30$. Thus

$$
\boxed{
n\ge30,\quad K_5\subseteq\Gamma
\ \Longrightarrow\ \text{the full-support owner graph is connected}.
}
\tag{CP10}
$$

CP7 improves the threshold to $n\ge29$ if all five selected primes
are at most q. These are statements about the full-support graph.
CRT intersections may lie entirely in the retained q-free cover, so
CP10 does not assert connectivity after masking by its exact hole.

## Direct reuse of Motzkin–Straus

Motzkin and Straus, *Maxima for Graphs and a New Proof of a Theorem of
Turán*, Canadian Journal of Mathematics 17, 533–540, Theorem 1,
[DOI 10.4153/cjm-1965-053-6](https://doi.org/10.4153/cjm-1965-053-6),
give the maximum weighted edge sum in terms of clique number. Apply
that theorem directly to the actual graph $\Gamma$. If $n\ge30$
and the full-support owner graph is disconnected, CP10 makes
$\Gamma$ $K_5$-free. For any nonnegative prime weights,

$$
\sum_{\{p,s\}\in E(\Gamma)}\lambda_p\lambda_s
\le\frac38\left(\sum_{p\mid W}\lambda_p\right)^2.
\tag{CP11}
$$

Normalize by the weight sum when positive; when it is zero both
sides vanish. With r actual cofactor primes, uniform weights imply

$$
|E(\Gamma)|\le\left\lfloor\frac{3r^2}{8}\right\rfloor.
\tag{CP12}
$$

Under the separate support-through-113 envelope there are at most
27 cofactor primes, so at most 273 pair edges and at least 78 missing
pairs in that ambient 27-prime set. Pairs involving an absent prime
are missing for that reason; this ambient count is not a count of
missing families on the actual support. Neither inequality controls
the number of original owners supported on a present pair.

## Exact deletion hole of a masked component

Let $E_0\subseteq\mathcal A\times\mathbb Z/W$ be the entire hole
of the retained q-free family, let $F_i=R_i\cap E_0$, and define
components using intersections of these actual masked supports.
For a component C put $V_C=\bigcup_{i\in C}F_i$. Delete exactly
the originals of C and retain every other original. Its complete
deletion hole in the CRT period is

$$
\boxed{
E_C=V_C\times\{\text{full q-words with first digit in }U\}.
}
\tag{CP13}
$$

Outside $E_0$, retained q-free originals cover. At a base point in
$E_0$ and a first digit outside U, any actual covering original is
protected and retained. At a base point in $E_0$ and a first digit
in U, all actual covering owners have masked supports containing
that same point; they belong to its unique masked component. Every
one is deleted precisely when the point lies in $V_C$. This proves
both inclusions for every higher-q suffix.

CP13 preserves all joint realizability conditions. It neither makes
$V_C$ a group or coset nor permits applying a coset-cover theorem
to it without another bridge.

## Verification scope and remaining obstruction

A scoped transient Lean check confirms the full 29-class construction
in the finite natural-residue formulation: the fourteen complementary
pairs and unit tag, fifteen safe roots from the actual disjoint pure
guards, CRT residues, distinct fresh odd nonunit labels, coverage of
the whole four-match region, automatic retention of both guards,
and reassembly with every other original retained. It proves the
30-to-29 count decrease and CP4 under explicit whole-coverage,
global count-minimality, shallow-height and pure-guard hypotheses.
All thirteen checked axiom closures contain only `propext`,
`Classical.choice` and `Quot.sound`. No q-bearing or selected-prime
upper bound is a premise of that check.

This exact application reuses the pinned finite-set, prime-product,
CRT and counting results. It adds no retained mathematical declaration.
The integer-periodicity translation, the cap-28 sum comparison,
phase packing, component deductions and published weighted theorem
application above remain ordinary deductions in this verification
scope. The check does not settle the EB1 branch.

CP4 bounds phase concentration, whereas Report 850's rectangle
counts at least $5(n-5)$ distinct actual top labels across five words
and many cofactor phases. A bound relating those two inventories is
still needed. Full-support connectivity limits the freedom of
component-dependent codes but is not itself an EB1 contradiction.
The exact masked deletion hole CP13 retains the whole-cover
condition needed for any further replacement. The height-two branch
and unrestricted Erdős #7 remain unresolved.
