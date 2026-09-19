# Private cylinders in a complete odd cover obstruct root transport

The old-prime digit-memory construction in [348](348-fresh-prime-root-transport-and-two-copy-reduction.md)
cannot be extended to the actual seven-copy-11 cover of
[Harrington–Sun–Wong (HSW)](../../../../../Library/Arith/harrington2021oddcovering.md)
by assigning each troublesome source class to at most one selected root.
For q=3 its output misses Haar mass at least 2/30421755; for q=5 it
misses at least 2/50702925. These statements allow every root injection
and every selection of at most one legitimate AP per output modulus.

The input is a complete odd cover, with every original exponent retained.
It is not a distinct odd cover: modulus 11 occurs seven times. The
obstruction concerns this particular source and transport interface,
not all transformations and not unrestricted Erdős #7. The results
below are ordinary finite proofs supported by exact programs, not Lean
verification or a new claim about the existence of the HSW cover.

## 1. Selected-source coverage is the exact condition

Let F be a finite whole cover with s distinct pure-p classes, where p
and q are different odd primes. All other numerical moduli are distinct
and greater than one. Let N be the t=p−s nonpure p roots and set

    G = {i in F : p does not divide m_i, q divides m_i},
    D_G = (union of G) minus (union of F minus G).

Because F covers, D_G is exactly the region uncovered on deleting all
of G. It need not equal the union of individual labels' private regions:
different labels in G may cover one another's points.

Choose S subset N of size k=min(q,t), inject S into the new q roots,
and apply 348's old-q transport to F minus G. On a selected root b
corresponding to xi, use one original source point with coordinates

    old p = xi+p x modulo the full original p power,
    old q = floor(x/q) modulo the full original q power,
    all other coordinates unchanged.

Use an original carrier p^H q^K R with H>=1, adjoining a p coordinate
if necessary. Retain the complete output carrier
p^(H−1) q^(K+1) R. This map is a bijection of that new-root fibre onto
the old xi-root fibre, including when deleted classes carried maximal
exponents. Every retained original event is preserved on this fibre.
The unselected new roots are covered by pure-q classes. Hence

    output covers  iff  S intersects projection_mod_p(D_G) trivially.

A suitable S exists exactly when at least k roots of N miss D_G. For
the original full-Haar law mu, the exact output hole mass is

    (p/q) mu(D_G intersect {old p root lies in S}).

This counts points under one joint source law; separate marginal
coverages cannot replace it.

## 2. Keeping one child requires both coverage and modulus compatibility

One can try a stronger construction. Keep the p-free, q-free original
classes unchanged. Choose a subset J of the p-divisible labels in the
selected nonpure roots. Each label i in G may be assigned to one root
xi in S or omitted. If m_i=q^beta r, its assigned child is

    x = b(xi)+q(a_i mod q^beta) mod q^(beta+1),
    x = a_i mod r,

one class of modulus q m_i. A retained label j in J has the usual
transport modulus q m_j/p. Whole coverage holds exactly when, for
every xi in S, the entire original xi-root fibre is covered jointly by
the p-free q-free classes, J, and the G labels assigned to xi.
Only appearances of G on its assigned root are preserved.

The output moduli are distinct, apart from any explicit pure-q
repetition, exactly when no assigned i in G and retained j in J satisfy

    m_j = p m_i.

This collision is global: assigning the two labels to different roots
does not make their numerical output moduli different. Deleting a
conflicting J label is allowed only if the same source-coverage
conditions still hold.

Group all candidate children of a label i in G together with the
possible label of modulus p m_i. The common output modulus is q m_i;
distinctness permits at most one AP from this group. Each such AP
fixes one new q root. For actual source witnesses on distinct selected
roots, let support(w) be their eligible groups after all unambiguous
classes are included. A necessary covering condition is

    cardinality(union of support(w_xi), xi in T) >= cardinality(T)

for every subset T of these root witnesses. A single group cannot
serve two different q roots. This Hall condition is only necessary;
passing it does not certify full coverage. Multiple points on the same
root cannot be counted as separate unit demands in this argument.

## 3. A compact representation of the complete HSW input

Use HSW arXiv:2104.00602v1, Theorem 4.2 and Figures 18–22, printed
pages 11–12, with the tree conventions on pages 4–6. Choose the
auxiliary closing prime 23. This is distinct from the prospective
transport prime q=3 or 5. The [constructor](../../frontier/whole-cover/hsw11_family.py)
gives the entire tree and literal residue family.

The root is 11, with nonpure branches 0,1,2,3 and pure classes
4,5,...,10 mod11. Every power node at r in {3,5,7,13,17,19} has
all levels h=1,...,22 and its terminal 23-node. Wedges are expanded
in increasing base-modulus order before power substitution; the child
order then stays fixed at every height. Figure 20's 16 available
moduli supply the smallest 12 base choices, retained under substitution.

There are 97 normal parameter families. Each specifies a prime support
and fixed digits d_r. Its actual classes have

    x = d_r r^(h_r−1) mod r^h_r,  1<=h_r<=22,

independently for every included power prime, together with its fixed
root digit if 11 is included. An omitted ancestor coordinate imposes
no congruence. At each r, the closing classes are

    x = 0 mod r^j,  x = j mod23,  1<=j<=22,

plus the single shared class 0 mod23. The exact period is

    M = 11*23*(3*5*7*13*17*19)^22.

The finite tree covers: at each power node, a nonzero r coordinate
selects its unique first nonzero digit and height; an all-zero
coordinate modulo r^22 reaches a terminal 23 branch. Each resulting
leaf class contains its complete path cylinder. Every represented
normal family has a source-tree occurrence, and every path has a
represented containing class. This argument includes all exponent
endpoints and zero; it does not sample the enormous period.

There are exactly 19,329,428 different labelled classes after merging
identical APs, and 169,438,511 leaf occurrences before merging. The
97 normal families account for 19,329,295 classes; the closing part
has 133 classes. Different normal supports have different moduli.
Equal supports have identical digit formulas and exponent boxes,
except the seven distinct pure-11 roots. Closing moduli contain 23
and normal moduli do not. Thus every modulus is odd and greater than
one, and only 11 repeats, exactly seven times.

## 4. Entire private cylinders, with all heights excluded

Put W=3*5*7*11*13*17*19*23=111546435. For q=3 prescribe

    (x3,x5,x7,x13,x17,x19,x23) = (1,2,2,2,2,1,1).

For each xi=0,1,2,3, set x11=xi. The only original class meeting
this whole cylinder is the literal class 1 mod3. Its residues modulo W
are respectively

    101328502, 20203822, 50625577, 81047332.

For q=5 prescribe instead

    (x3,x5,x7,x13,x17,x19,x23) = (2,1,3,3,3,1,1).

On xi=1,2,3, the only original class meeting the entire cylinder is
1 mod5. Its residues modulo W are respectively

    55280501, 85702256, 4577576.

No private-cylinder assertion is made for xi=0 with these latter digits.
All six power-prime first digits are nonzero. Every normal label
with any height above one therefore misses the entire cylinder.
All 132 nontrivial closing classes require divisibility by a power
prime and miss it too; 0 mod23 misses because x23=1. Checking the
97 height-one normal instances thus accounts for every original label.
These are infinite AP regions of density 1/W, not isolated sampled
points or cylinders from which high-power labels were silently removed.

Deleting the whole forbidden G for q=3 therefore fails on every
nonpure root. The one-child/group construction also fails:

| q | selected old roots | private-root demands | sole eligible output modulus | hole-density lower bound |
|---:|---|---:|---:|---:|
| 3 | any three of 0,1,2,3 | 3 | 9 | 2/30421755 |
| 5 | all four of 0,1,2,3 | 3 | 25 | 2/50702925 |

Indeed only the original 1 modq can cover these source regions.
The possible partner modulus 11q does not meet them. Its group may
emit one AP of modulus q^2, contained in a single new q root, so at
least two entire image cylinders are uncovered. Each image cylinder
has modulus qW/11; the root injections make them disjoint. For q=5,
the added pure-q class covers an unselected root and cannot help.

## 5. Cofactor-dependent root choices do not repair this deficit

For this input p has height one. Write the output as (b,z), where b is
the new lowest q digit and z retains the complete old q tail and every
other old cofactor coordinate. Allow the selected old roots and their
injection into new roots to depend arbitrarily on z. For q=3 select
three of the four nonpure roots at each z; for q=5 select all four.
Require every output label covering a selected point to be sound for
its actual original source label under this same map. Grant even free
covering of every unselected point; a filler may not cover selected
points. This does not assume that a cofactor-dependent unused root is
itself a pure-q AP.

For q=3 the common cofactor cylinder from section 4 is private for
1 mod3 on all four old roots. For q=5 its corresponding cylinder is
private for 1 mod5 on three of the four roots. Thus at each z in the
respective common cylinder, every allowed local injection still
produces at least three different new-root demands for the same label.
Retain the output-modulus groups defined in section 2. If the relevant
group can emit at most one AP, that AP fixes
one b and leaves at least two demands unsatisfied. The cofactor
cylinder has Haar mass 11/W, so pointwise counting gives

    output hole mass >= (2/q)(11/W).

These are exactly the preceding two bounds. The missing root positions
may now depend on z, so the uncovered set is not asserted to contain
two fixed AP cylinders. Checking every possible local root injection
suffices for the pointwise count; there is no assumption of independent
root choices or a constant map on high coordinates.

There is also a direct single-label version allowing proper event
restrictions and larger output moduli, under a stronger soundness
premise: each entire AP attributed to the original 1 modq, including
its unselected points, must be contained in that label's pullback. It
must therefore lie inside

    {x : floor(x/q) = 1 modq} = {q,q+1,...,2q−1} modq^2.

If an AP's modulus has q valuation zero, its reduction modulo q^2
visits every residue. If that valuation is one, its reduction visits
all q residues with one fixed lowest digit. Neither set lies in this
block, which has just one residue per lowest digit. Hence every
nonempty AP contained in the block has modulus divisible by q^2
and fixes one b. Consequently the same hole bounds survive such
restrictions if each original label still supplies at most one sound
AP. Soundness only at selected points does not imply the whole-AP
containment used here. Numerical modulus distinctness alone does not
imply the one-AP-per-original-label condition: splitting one original
label into several different new
moduli is outside this conclusion.

## 6. Verification scope and remaining problem

The [independent checker](../../frontier/whole-cover/hsw11_group_hall.py) traverses the
17 power nodes and 124 symbolic nonzero leaf paths, checks every
exponent box and modulus-support collision, and exhaustively excludes
the other represented labels from all seven private cylinders. It
checks all 24 root injections for q=3 and all 120 for q=5 using integer
CRT and exact rational densities. The constructor additionally returns
a tree covering witness for 1,120 test points, including maximal heights
and all terminal closing digits. Those point tests check implementation;
the complete covering argument is the finite tree proof above.

Both installed entrypoints run from physically copied files in a path
containing spaces, with cwd `/` and `python3 -I -S -O -B`; their JSON
outputs equal normal runs byte for byte. No full-period enumeration,
Lean build, new theorem declaration or frozen result is claimed.

This identifies an actual obstruction to using old prime digits as
extra memory: the source labels survive as events, but several source
branches demand incompatible uses of one numerical modulus. Keeping
more source information alone does not discharge the AP-covering and
modulus-distinctness obligations. A different valid transformation or
a seed satisfying 348's sufficient conditions is still required.
