[Index](../marked_head_profile.md) · [Synchronized matching](354-synchronized-prime-private-cofactor-matching.md) · [Column height bound](355-column-height-matching-bound.md) · [Extremal source](350-extremal-paired-branch-and-source-support.md)

# An active parent's private points require a shallow rescue on another root

The greedy synchronized tuple of 354 supplies a restriction on actual
replacement witnesses. If a selected label's original parent is active
at the common cofactor-tail base, then contracting another selected
**deep** label cannot rescue any original private point of that parent.
Only a shallow selected label on a different first-p-digit root can
possibly do so. No existence of these needed rescues is asserted.

## 1. Source labels, their parents, and literal contractions

Use the extremal whole cover of 350, normalized by `A_p=0 mod p`.
Let the 354 greedy construction select

    d_i=p^(e_i)m_i,  h_i=e_i-1,  m_i>1,  p does not divide m_i,

one label on each nonzero root `r_i`, with all `m_i` distinct and
one common cofactor `x in R_p` and tail `t`. The matching time of
this label is its depth `h_i`. Define

    q_i=d_i/p,   P_i=A_(q_i),   B_i=a_(d_i) mod q_i.       (PR1)

Divisor closure supplies the original parents. Distinct p-free
cofactors imply that all `2(p-1)` moduli `q_i,d_i` are different.
`B_i` contains `A_(d_i)`, and irredundancy gives `P_i intersect B_i=empty`.

`B_i` is the containing AP on the original carrier: its p-coordinate
is `r_i+p t` modulo `p^(e_i-1)`. It is not the branch residual AP,
whose corresponding p-coordinate is `t`. Confusing them invalidates
the root restrictions below.

## 2. Greedy order controls active ancestors

A p-bearing original is active at `(t,x)` when its full cofactor
condition and full tail prefix both hold; its original first-digit
root is kept. First-digit agreement alone is not this condition.

If the true p-ancestor `A_(d_i/p^s)` is p-bearing and active, it
appears on the common path at depth `h_i-s`. The invariant in 354
says that every root with an already-seen label has been matched.
If `j` is the selected label on this ancestor's root, then

    h_j <= h_i-s < h_i.                                  (PR2)

The ancestor need not itself have been the label chosen for that root.
Every p-free ancestor is inactive because `x in R_p`. Thus each selected
label of minimum matching depth has all true p-ancestors inactive;
in particular at least one immediate parent is inactive. If all
selected exponents agree, all immediate parents are inactive.

## 3. Whole-AP intersections versus actual private rescues

Suppose `P_i` is active. Necessarily `e_i>=2`; let `s_i` be its original
first-digit root. Here `s_i!=0` because every other p-bearing original
is disjoint from `A_p`. Also `s_i!=r_i`: with equal first roots,
activity at the common full `(t,x)` would make the comparable original
parent and child intersect, contrary to irredundancy. The common child
cofactor conditions and full tail
prefix give the exact whole-AP intersection rule

    P_i intersect B_j is nonempty
      iff e_j=1, or (e_j>=2 and r_j=s_i).                (PR3)

For a deep `j` meeting `P_i`, PR2 gives `h_j<h_i`, hence `e_j<=h_i`.
The parent `P_i` fixes its p-coordinate to the common prefix through
exponent `h_i`; this already enforces the **original** child's complete
p-condition through exponent `e_j`. The contraction `B_j` enforces
that child's cofactor condition. Therefore

    P_i intersect B_j subset A_(d_j)   when e_j>=2.      (PR4)

The same containment holds for a shallow `j` with `r_j=s_i`.
These original children are different from `P_i`, so their intersections
contain no original private point of `P_i`. Consequently

    Priv(P_i) intersect B_j nonempty
      implies e_j=1 and r_j!=s_i.                       (PR5)

Such a target `j` has a p-free original parent, necessarily inactive
at `x in R_p`. This is only a necessary condition; a permitted shallow
contraction may still miss every private point.

Two concrete consequences follow.

- If the tuple has no shallow child and at least one active parent,
  simultaneous contraction fails: every original private point of
  that active parent misses every `B_j`.
- At `p=3`, any active parent blocks this contraction. Since `s_i` is
  nonzero and differs from `r_i`, it is the only other selected root.
  The selected child on `r_i` is deep, and a shallow child on `s_i`
  cannot satisfy PR5. No third nonzero root is available.

These blockers are actual private points of the original whole cover.
They are not inferred from a local example or an envelope estimate.

## 4. Arithmetic filters without an activity assumption

For arbitrary `i,j`, let `g_ij=gcd(m_i,m_j)` and
`b_ij=min(e_i-1,e_j-1)`. Exact AP compatibility gives

    P_i intersect B_j nonempty
      iff a_(q_i)=x mod g_ij
      and a_(q_i)=r_j+p t mod p^(b_ij).                 (PR6)

The second condition is void if `b_ij=0`. The original parent's
residue is essential. Full-AP compatibility is weaker than private
rescue and must not be counted as such.

A useful exclusion is

    e_i=1 and m_i divides m_j
      implies P_i intersect B_j=empty.                 (PR7)

Here `P_i=A_(m_i)` has residue different from `x mod m_i`, whereas
all of `B_j` has that residue. The target `j` may be deep or shallow.
A shallow selected cofactor dividing all selected cofactors therefore
blocks simultaneous contraction by its own original private point.

The reverse divisibility direction has a different effect. If `P_i` is
active, `e_j=1`, and `m_j divides m_i`, then

    P_i subset B_j,  hence Priv(P_i) subset B_j.          (PR7a)

Indeed, every point of `P_i` equals the common x modulo m_i, while
`B_j` is exactly x modulo m_j. Here j differs from i because the
active parent has e_i>=2. Necessarily `r_j!=s_i`: otherwise the same
points also satisfy the original child's first-p-digit condition,
giving `P_i subset A_(d_j)` for two distinct original classes with
`d_j divides q_i`, contrary to irredundancy. Thus in this conditional
configuration the permitted shallow contraction rescues the entire
original private set. Choosing a smaller private cylinder cannot
avoid it. The statement uses neither a product law nor greedy order,
and still applies when p is the largest support prime. It does not
assert that this configuration extends to a whole odd cover.

## 5. A successful exchange needs genuinely off-source rescue cycles

Consider deleting all selected children and their original parents,
and adding all `B_i`. Numerical moduli stay distinct, odd and nonunit;
the AP count drops by `p-1`. Each original child is covered by its own
new containing class.

For successful whole coverage, each original private point of `P_i`
must be covered by some `B_j`, with `j!=i`. The retained originals
cannot cover it. Thus the finite actual-private rescue graph

    i -> j iff Priv(P_i) intersect B_j nonempty

would have a nonself outgoing edge at every vertex and therefore a
directed cycle. By PR5, every active-parent vertex on such a cycle
must be immediately followed by a shallow, inactive-parent vertex.
If a cycle has `ell` vertices and `a` active parents, then

    a <= number of shallow vertices <= ell-a,
    number of inactive parents >= ceil(ell/2).          (PR8)

Cycles, inactive parents, and even these counts are not sufficient
for coverage: every private point must be rescued, and there may also
be joint-private overlaps of several deleted parents.

The exact remaining region is

    E_P=(union_i P_i) minus (union_(d not in {q_i}) A_d). (PR9)

Successful coverage is equivalent to `E_P subset union_i B_i`.
Individual private sets suffice only if the selected parents are
pairwise disjoint, or if their joint-private overlap obligations have
also been checked. PR9 is a coverage equivalence, not the new result.

Let `Z_tau=intersection_i J_(d_i) × intersection_i C_(d_i)` on the
tail-cofactor carrier. Above its every point, the zero root is covered
by the unchanged `A_p`, and each other root by its selected original
child. These labels all lie outside the parent set. Hence

    E_P intersect (F_p × Z_tau)=empty.                  (PR10)

The common cylinder proved in 354 carries none of this parent-deletion
liability. At least one blocker outside it must remain in the extremal
system; a successful exchange would contradict minimum cardinality.
If all selected children are shallow, `E_P` lies outside the entire
`R_p` cofactor region. At the largest prime its raw pre-prime killed
mass is therefore zero, as for the earlier-parent region in 350.

## 6. Independent arithmetic fixtures and their boundary

The [exact AP checker](../frontier/synchronized_parent_rescue.py) checks
three explicit finite AP lists:

- At `p=3`, active parent `58 mod63` has 12 private residues in period
  945. None meets either deep contraction; integer58 is a blocker.
- Replacing that parent by `16 mod63` preserves its first root and
  cofactor but changes the higher prefix. It is inactive at `t=1`;
  integer142 is private in that list and is rescued by the deep
  contraction `7 mod15`. Full-prefix activity cannot be omitted.
- At `p=5`, active parent `131 mod325` has 600 private residues in
  period375375. Deep contractions rescue none; the two eligible
  other-root shallow contractions rescue 100 and60 of them. Integer
  5006 is an explicit such private point.

The checker exhausts each designated parent's AP over the complete
finite period (15,15,1155 points), and checks the original APs directly.
For every active parent in each list it also checks the exponent
premise `h_j<=h_i-1` on its root. This checks the needed inequality in
the fixtures, not a claim that an arbitrary synchronized tuple comes
from the greedy construction. These lists are not asserted whole-tail
covers, whole covers or extremal odd systems;
they test AP algebra and private membership relative to the listed
families. They neither refute an odd-cover claim nor prove a legal
exchange exists. The general conclusions above use ordinary finite
proofs; no new Lean declaration or Erdős #7 resolution is claimed.
