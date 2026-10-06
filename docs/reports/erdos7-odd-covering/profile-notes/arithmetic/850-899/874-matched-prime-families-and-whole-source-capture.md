[Index](../../../marked_head_profile.md) · [Literal-root inventory](871-all-root-divisor-inventory-capacity.md) · [Completion criterion](872-matched-prefix-completion-and-paid-banks.md) · [Shared signatures](873-clean-colors-and-shared-output-conflict-graphs.md)

# Matched prime families and the whole-source capture bound

Keep the conditional branch of Reports871--873: a globally
count-then-modulus-sum minimal odd distinct whole cover, maximal ternary
height two, q=113 of height one, and period 9qW with W coprime to 3q.
The q-free originals F0 leave their exact complement E0 on 9W.
For a safe old word z modulo nine, let X_z be its W-coordinate fiber.
There are at least 105 actual q-bearing top originals at z, and W has
at most 27 distinct prime factors. These conditions are not asserted for every possible
odd cover.

A common first root on every prime factor is unnecessary for a shared
repair. One matching prime per selected composite original suffices.
Two matching primes per original also force the restricted three-bank
completion inequalities. Neither statement supplies a cover of E0.

## One matching prime supplies a fixed sparse repair

Let A be a nonempty set of actual top originals with numerical labels
9q m_i, all at z. Put k=|A| and M=sum_i m_i. Assume each m_i is
composite. The anchors are distinct because the original moduli are
distinct. Write rho_i for the literal cofactor phase.

Fix one auxiliary root phi_p for each cofactor prime. For each i choose
a prime p_i dividing m_i with

$$
\rho_i\equiv\phi_{p_i}\pmod {p_i}.
\tag{MF1}
$$

Let S be the image of the chosen primes and s=|S|. Other prime roots
of the same original need not agree with phi. This construction does
not require the selected originals to have the same q-color.

Choose z in {0,...,8}. Use the following three disjoint categories of
new outputs, with their simultaneous residues interpreted by CRT:

| Numerical modulus | Residue modulo 27 | Cofactor residue |
| --- | --- | --- |
| 27 | z | none |
| 27p, p in S | z+9 | phi_p modulo p |
| 27m_i, i in A | z+18 | rho_i modulo m_i |

The labels are distinct: their cofactors are respectively the unit,
primes and distinct composites. Every output has ternary height three,
so no output collides with any original. All labels are odd and greater
than one. Divisor closure puts every cofactor in P2.

Define the fixed cofactor union

$$
U_A=\bigcup_{i\in A}[\rho_i]_{m_i}\subseteq\mathbb Z/W\mathbb Z.
$$

These outputs cover every integer lift of {z} times U_A. Given a
containing packet i, its next ternary digit is zero, one or two. The
unit output covers digit zero, its selected prime output covers digit
one, and its anchor output covers digit two. One prime output can serve
many packets only because MF1 gives the same literal residue.

The exact output count and a strict cost comparison are

$$
B=k+s+1,\qquad s\le\min(k,27),
$$

$$
27\left(1+\sum_{p\in S}p+M\right)
\le81M<9qM.
\tag{MF2}
$$

Indeed the sum over the image of p_i is at most sum_i p_i, which is
at most M because p_i divides the positive m_i. Since A is nonempty,
M is at least one. This uses only the chosen primes; no estimate for
the sum of all support primes is needed.

MF2 pays the modulus sum, not the count: B is larger than k. The
additional originals captured by this fixed union determine whether
it becomes an improving exchange.

## Capturing actual traces controls the simultaneous deletion hole

Let Top_z contain all actual q-bearing top originals at z, across all
literal q-colors. For j in Top_z define

$$
T_j=X_z\cap[\rho_j]_{m_j},\qquad
D_A=\{j\in\mathrm{Top}_z:T_j\subseteq U_A\}.
\tag{MF3}
$$

In particular A is contained in D_A. Delete exactly D_A and retain all
other originals, including F0. Any integer uncovered by those retained
originals has a deleted original owner, so has old word z. It also
avoids F0, so its W-coordinate lies in X_z. Its deleted owner and MF3
then place it in U_A. The sparse repair covers the entire deletion hole.

This argument uses the original whole cover and the exact retained
source. It does not require the new outputs to cover each deleted
original outside X_z, since those points can be covered by retained
originals. Nor can separate private regions substitute for the
simultaneous deletion hole.

The deleted modulus sum is at least 9qM. If |D_A| were at least B,
replacing D_A by the B outputs would either reduce the number of
classes or preserve that number and strictly reduce their modulus
sum. Both violate the chosen minimum. Consequently

$$
\boxed{|D_A|\le k+s\le\min(2k,k+27),\qquad |D_A\setminus A|\le s.}
\tag{MF4}
$$

MF4 applies to mixed colors as well. It is a restriction on capture
by one fixed union, not a license to add together independently chosen
repairs with conflicting numerical labels.

## A single literal color gives an absolute capture bound

Now additionally require every selected original to have one common
literal q-color c. In the actual prime-cut capacity of Report871, use
q as the left tag and the chosen p_i as right tags. The left root is
c and the right roots are phi. Since q does not divide W, these tag
sets are disjoint. Every selected original crosses this cut. Thus

$$
k\le s+1\le28.
\tag{MF5}
$$

The no-subsidy capacity applies to the full actual cofactor qm_i;
removing q from that cofactor before applying the theorem would lose
this particular cut. Combining MF4 and MF5 gives

$$
|D_A|\le55.
\tag{MF6}
$$

Since |Top_z| is at least 105, it follows that X_z is not contained in
U_A. If it were, every top trace would be captured. A nonempty
one-matching-prime family in one color therefore always leaves an
actual point of the old-word source outside its cofactor union.

## Two matching primes force the restricted completion inequalities

For each selected owner let R_i be a subset of its prime factors, all
matching the same phi, with |R_i| at least two. Keep the same old word
and same literal q-color. No matching condition is imposed on its
other prime factors or on higher prime-power digits.

For any owner subfamily X and prime set T, select those owners whose
R_i meets T. Choosing one such tag per owner and applying MF5 gives

$$
\left|\{i\in X:R_i\cap T\ne\varnothing\}\right|\le |T|+1.
\tag{MF7}
$$

A singleton T shows that each matching prime occurs in at most two
owners. If two disjoint pairs of owners had intersecting R_i, choose
one intersection prime for each pair. Those four owners would meet
a set T of size at most two, contradicting MF7. Thus the owner
intersection graph has no two vertex-disjoint edges. This graph
restriction reuses Report385, Section172, GLC1--GLC4; its application
here uses the selected matching-prime sets, rather than the full
cofactor supports.

Write r=|X| and S_X=union_(i in X) R_i. Then

$$
2r\le |S_X|+3.
\tag{MF8}
$$

For completeness, if the R_i are disjoint their union has at least
2r elements. Otherwise choose an intersecting pair and a common prime
p. The other r-2 supports are pairwise disjoint, since a further edge
would be disjoint from the chosen pair. None contains p, since prime
incidence is at most two. Their union together with p therefore has
at least 2(r-2)+1 elements. This proves MF8 without a classification
of stars and triangles.

Let nu(X) be the number of divisors in the union of the selected
anchors' divisor sets. For nonempty X, the unit, the primes S_X and
the r distinct composite anchors are disjoint members of that union.
Hence

$$
\nu(X)\ge1+|S_X|+r.
$$

For r at least three, MF8 implies nu(X) at least 3r-2. For r=1,2,
use |S_X| at least two. Together, including the empty case, these give

$$
\boxed{7|X|\le3\nu(X)\quad\text{for every selected subfamily }X.}
\tag{MF9}
$$

Every divisor of a selected top anchor is in P2, hence in all three
banks. For nested divisor downsets J1 contained in J2 contained in J3,
let K_A(J) count selected anchors in J. Apply MF9 to those three
subfamilies. Their counts r1,r2,r3 are nondecreasing, so

$$
3r_1+2r_2+2r_3\le\frac73(r_1+r_2+r_3).
$$

The respective divisor unions lie in J1, J2 intersect P1, and J3
intersect P2. Therefore

$$
3K_A(J_1)+2K_A(J_2)+2K_A(J_3)
\le |J_1|+|J_2\cap P_1|+|J_3\cap P_2|.
\tag{MF10}
$$

This is Report872's completion criterion for this restricted family.
It does not include the other packets in those same downsets. Adding
their demand without rechecking the inequalities is invalid.

Since S_A lies in the 27-prime pool, MF8 also gives k at most 15. The
one-prime sparse construction can still be used, giving at most 31
outputs and, by MF4, capture of at most 30 actual top traces. Choosing
distinct prime representatives is unnecessary for these conclusions:
duplicate chosen primes produce shared outputs.

## Reuse and remaining scope

The ingredients are the existing actual prime-cut exchange, CRT,
finite union counting and Report872's application of
Edmonds--Fulkerson, *Transversals and matroid partition*,
[DOI 10.6028/jres.069b.016](https://doi.org/10.6028/jres.069b.016).
No new matroid partition theorem is claimed. The numerical source
bounds 105 and 27 are inherited from the stated conditional branch.

Exact Lean applications check the sparse CRT construction together
with its distinct fresh labels, cost, actual-source deletion and
capture bounds. A separate exact chain checks the original-cover
capacity, all-subfamily divisor bound, restricted nested-bank
inequalities and the 15-owner bound. These scoped compilations pass
with default proof budgets and only the standard axioms. The actual
minimal cover remains hypothetical; the checks prove conditional
implications, not existence of such a cover or its impossibility.

The next missing implication is global: construct one paid assignment
covering E0 while respecting conflicting roots, all old words and
lower-row packet multiplicities. One local repair uses the numerical
label 27 at one old word; it cannot independently reuse that label at
another old word. The capture restriction identifies a genuine source
obstruction to a single coherent patch, but does not show how to join
enough incompatible patches. Unrestricted Erdős #7 remains open.
