---
bibkey: mosqueraloistanaka2026stablecategory
authors: David Mosquera-Lois and Kohei Tanaka
year: 2026
title: Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces
doi: 10.48550/arXiv.2609.39615
url: https://arxiv.org/abs/2609.39615v1
claim: Question 6.3 asks whether the stable category of every finite T₀-space is at most twice its weak category.
strata_touched:
  - D5/S3/Topology/RelativeConeRigidity
  - D5/S3/Topology/MatchedFaceIncidenceForest
  - D5/S3/Topology/DescendingClosureContiguity
  - D5/S3/Topology/SubdivisionCategoricalCover
  - D5/S3/Topology/SmallPosetSubdivisionCategory
  - D5/S3/Topology/FiniteCategoricalCoverCertificate
  - D5/S3/Topology/SmallAcyclicCategoricalCovers
  - D5/S3/Topology/CrossedExtremalProfiles
  - D5/S3/Topology/RelativeDerivedContiguity
  - D5/S3/Topology/BarycentricGraphDistance
  - D5/S3/Topology/BarycentricNeighborhoodIteration
  - D5/S3/Topology/BarycentricBaseRigidity
  - D5/S3/Topology/ConnectedCategoryGraft
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Topology/mosqueraloistanaka2026stablecategory -->

# Weak and stable category of finite spaces

Question 6.3 asks whether `cat_s(X) ≤ 2 cat_w(X)`.
The stable invariant takes the minimum of the ordinary finite-space category
over all barycentric subdivisions. The weak invariant is the category of
the realization of the order complex. The paper uses unreduced category.

## Locator

Section 2 and Question 6.3 of the cited preprint give the category invariants
and the proposed inequality. Proposition 5.2 and Question 6.2 give the
height-one family and the connected realization problem. DOI
10.48550/arXiv.2609.39615.
[Preprint v1](https://arxiv.org/abs/2609.39615v1)

## Connected realizations

For a connected finite poset `X`, identify a minimal point with one of the
minima of the height-one poset `B_m` with `m ≥ 2` common maxima. The graft has
ordinary category `max(cat(X), m)`. The Lean theorem gives the exact criterion
for a categorical lower cover of each size. The principal lower sets of `B_m`
contract to the shared point while fixing it. In the lower bound, a piece
containing two maxima would contract the four-point retract whose identity is
isolated among pointwise-comparable maps.

Subdivision preserves this union and its minimal shared point. At positive
depth the subdivided `B_m` has a lower cover by the face posets of two
subdivided tree stars. Leaf pruning gives the rooted contraction required at
the common point. The same cover argument at positive depths yields stable
category `max(cat_s(X), 2)`. The classical wedge formula gives weak category
`max(cat_w(X), 2)`.

For `a ≥ 2`, take the opposite face poset of the first barycentric subdivision
of a triangulated `(a − 1)`-torus. For each face dimension, the open set of
faces meeting that dimension color contracts through the projection onto its
discrete color class. The torus cup-length gives weak category `a`, so all
three categories equal `a`. Grafting `B_c` yields every connected triple
`(a, a, c)` with `2 ≤ a ≤ c`. The Lean module proves the ordinary cover formula
used in this construction. The stable and weak formulas and the torus argument
are mathematical deductions using the subdivision and classical category
comparisons.

## A coface bound on a collapse sequence

If each lower face paired with a triangle has at most two original
triangular cofaces, a collapse sequence removing all triangles has
an edge–triangle incidence forest on its deleted faces. The analogous
proof works in any fixed pair of consecutive dimensions. The Lean theorem
extracts an indexed matching from an actual elementary collapse sequence.
An additional coface must precede the assigned one. A cycle would have
a greatest rank with two distinct predecessors.

For a two-dimensional collapse onto a tree, color the vertices of the
first barycentric subdivision according to whether the face survives
the triangle removals. The induced complexes are the subdivided tree
and the incidence forest. The corresponding neighborhoods in the
second barycentric subdivision retract by intersecting each face with
the selected vertices. Each forest component contracts in the connected
ambient complex, giving a two-piece categorical cover. The Lean
incidence result addresses the forest step.
[Subdivision and contiguity](https://arxiv.org/abs/1605.01322v2)

## Conjecture 6.1 and categorical covers

Conjecture 6.1 asks for the least size of a finite space with both category
inequalities strict. Corollary 4.2 attains twelve points. The Lean theorem
`SubdivisionCategoricalCover.hasCategoricalCover_double_subdivision`
supplies the subdivision step for the lower bound. Two categorical induced
subposets covering a finite poset give two categorical open subsets of its
second subdivision. In the first subdivision each chain meeting a chosen
set contracts through its intersection with that set. In the second
subdivision the smallest chain in each flag makes the two lower sets cover.

The computer-assisted lower bound is twelve. For a connected core of at
most eleven points, simultaneous strictness with weak category at least two
requires at least four maximal points. The corresponding Lean theorem
partitions such a core into two categorical subsets and bounds the category
of its second subdivision by two. It uses the two extrema above and below
each intermediate point in a core and the limit of four intermediate points
when there are at least three minima.

With weak category one, the nine-point theorem of Cianci and Ottina reduces
the remaining range to sizes nine through eleven. A core with at most two
maxima already has a two-cover by principal lower sets. For the rest, take
the McKay catalogue of Hasse diagrams on eight, nine and ten points and
extend each poset at one maximum. Use a lower ideal with no greatest
element, exclude all old maxima, and for each old up beat point include that
point and exclude its former least strict upper neighbor. Discard orders
with a down beat point, and use connectedness and vanishing reduced
homology over the field of two elements. The latter conditions hold for
every weakly contractible candidate. This yields 2, 10 and 93 isomorphism
classes with at least three maxima. The Lean kernel checks two explicit
lower sets and their inclusion-to-constant zigzags for every listed class.
The exhaustive enumeration uses the published catalogue and integer
computation.

Passing to cores preserves the three categories, which are additive over
components. Any component with a strict weak-to-stable inequality needs at
least nine points. For weak category one this uses Cianci and Ottina. For
weak category at least two, a core on at most eight points has a stable
two-cover by the same intermediate-point argument. Under the size bound
of eleven the other components therefore contribute equally to all three
categories.
[Conjecture 6.1 and Corollary 4.2](https://arxiv.org/html/2609.39615v1#S6)
[McKay catalogue](https://users.cecs.anu.edu.au/~bdm/data/digraphs.html)

## The extremal twelve-point spaces

The minimum in Conjecture 6.1 is attained by exactly two isomorphism
classes, the examples in Corollary 4.2 and Example 4.3. For weak
category one an exhaustive comparison of the 782 twelve-point
acyclic cores with at least three maxima leaves two orders with
ordinary category greater than two. Removing their three maxima
recovers the two nine-point cores in the paper. Both have a
categorical vertex partition and thus a two-cover after subdivision.

For weak category at least two, a strict example requires at least
four maxima. The intermediate-point count reduces the new cases
to five intermediate points between three minima and four maxima,
or four intermediate points between four minima and four maxima.
In the first case ten incidences with the maxima force a triple
sharing an upper bound, and its complementary pair shares a lower
bound. In the second case a common bound for three points suffices.
Otherwise the minimum and maximum incidences both have degree two.
The only obstruction to dividing the intermediate points into
oppositely bounded pairs is the doubled matching and complementary
four-cycle. The corresponding order and its dual admit the
categorical partition checked in Lean.

These proofs also rule out a counterexample to Question 6.3 on
at most twelve points. The weak-category-one case uses the acyclic
census. For weak category at least two, up to four maxima give
ordinary category at most four. With five or more maxima, a core on
at most twelve points has at most seven nonmaximal points, and the
structural bound gives stable category at most two.
[Conjecture 6.1 and Question 6.3](https://arxiv.org/html/2609.39615v1#S6)

The census program generates lower-mask tables directly from the
extrema profiles and exact binary homology. Its default mode covers
four through eleven points. Use `--twelve` for twelve points and
pass the resulting tables to the checker with Python 3.10 or later. The checker
enumerates categorical covers in the ambient poset and records the
two categorical vertex partitions at size twelve.
### Replaying the census

Save the C and Python blocks below as `census.c` and `covers.py`. Use
a C11 compiler and Python 3.10 or later.

```sh
cc -std=c11 -O3 census.c -o census
./census --twelve > orders.txt
python3 covers.py --classify-twelve orders.txt partitions.json
```

<details>
<summary>C enumeration</summary>

```c
/*
 * Catalogue-free census for the finite-space category bounds.
 * Compile with cc -std=c11 -O3. With no argument, replay sizes four through
 * eleven. With --twelve, replay size twelve. Output is one lower-mask table
 * per labelled acyclic presentation.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

enum { MAX_VERTICES = 12, MASKS = 1 << MAX_VERTICES, UNKNOWN_EULER = -1000 };

typedef unsigned Order[MAX_VERTICES];

static unsigned bit(int point) { return 1U << point; }
static int first(unsigned nonzero) { return __builtin_ctz(nonzero); }
static int size(unsigned mask) { return __builtin_popcount(mask); }

static void transpose(const Order lower, Order upper, int vertices) {
    memset(upper, 0, sizeof(Order));
    for (int x = 0; x < vertices; ++x)
        for (unsigned rest = lower[x]; rest; rest &= rest - 1)
            upper[first(rest)] |= bit(x);
}

static int euler(const Order lower, unsigned subset, int memo[MASKS]) {
    if (memo[subset] != UNKNOWN_EULER) return memo[subset];
    int minimal = first(subset);
    for (unsigned rest = subset; rest; rest &= rest - 1) {
        minimal = first(rest);
        if ((lower[minimal] & subset) == bit(minimal)) break;
    }
    unsigned other = subset ^ bit(minimal);
    unsigned link = 0;
    for (unsigned rest = other; rest; rest &= rest - 1)
        if (lower[first(rest)] & bit(minimal)) link |= bit(first(rest));
    return memo[subset] = euler(lower, other, memo) + 1 - euler(lower, link, memo);
}

typedef struct {
    int count[MAX_VERTICES + 2];
    unsigned by_size[MAX_VERTICES + 2][MASKS];
} Chains;

static void chains(const Order upper, Chains *faces, unsigned chain, unsigned choices) {
    for (unsigned rest = choices; rest; rest &= rest - 1) {
        int x = first(rest);
        unsigned larger = chain | bit(x);
        int rank = size(larger);
        faces->by_size[rank][faces->count[rank]++] = larger;
        chains(upper, faces, larger, choices & upper[x] & ~bit(x));
    }
}

static int boundary_rank(const Chains *faces, int rank) {
    int rows = faces->count[rank - 1];
    int blocks = (rows + 63) / 64;
    int index[MASKS];
    uint64_t pivots[rows][blocks];
    memset(pivots, 0, sizeof(pivots));
    for (int i = 0; i < rows; ++i) index[faces->by_size[rank - 1][i]] = i;
    int result = 0;
    for (int j = 0; j < faces->count[rank]; ++j) {
        uint64_t vector[blocks];
        memset(vector, 0, sizeof(vector));
        unsigned simplex = faces->by_size[rank][j];
        for (unsigned rest = simplex; rest; rest &= rest - 1) {
            int row = index[simplex ^ bit(first(rest))];
            vector[row / 64] |= UINT64_C(1) << (row % 64);
        }
        for (int block = blocks - 1; block >= 0; --block) {
            while (vector[block]) {
                int pivot = 63 - __builtin_clzll(vector[block]);
                int row = 64 * block + pivot;
                if (pivots[row][block] == 0) {
                    memcpy(pivots[row], vector, sizeof(vector));
                    ++result;
                    block = 0;
                    break;
                }
                for (int k = 0; k <= block; ++k) vector[k] ^= pivots[row][k];
            }
        }
    }
    return result;
}

static int acyclic(const Order upper, int vertices) {
    Chains faces;
    memset(faces.count, 0, sizeof(faces.count));
    chains(upper, &faces, 0, bit(vertices) - 1);
    int previous = 0;
    for (int rank = 2; faces.count[rank - 1]; ++rank) {
        int boundary = boundary_rank(&faces, rank);
        int betti = faces.count[rank - 1] - previous - boundary;
        if (betti != (rank == 2 ? 1 : 0)) return 0;
        previous = boundary;
    }
    return 1;
}

static int has_beat_point(const Order bounds, int vertices) {
    for (int x = 0; x < vertices; ++x) {
        unsigned strict = bounds[x] ^ bit(x);
        for (unsigned rest = strict; rest; rest &= rest - 1)
            if ((bounds[first(rest)] & strict) == strict) return 1;
    }
    return 0;
}

typedef struct { unsigned minima, maxima; } Profile;
typedef struct { int minimum, maximum; } Edge;

typedef struct {
    int n, minima, maxima, top_begin;
    unsigned low_mask, middle_mask;
    int profile_count;
    Profile profile[MASKS];
    Order lower, above;
    uint64_t euler_matches, acyclic_matches;
} Census;

static void check(Census *c) {
    if (has_beat_point(c->lower, c->n)) return;
    Order upper;
    transpose(c->lower, upper, c->n);
    if (has_beat_point(upper, c->n)) return;
    for (int a = 0; a < c->minima; ++a)
        if (upper[a] == bit(a)) return;
    for (int b = c->top_begin; b < c->n; ++b)
        if (c->lower[b] == bit(b)) return;
    ++c->euler_matches;
    if (!acyclic(upper, c->n)) return;
    ++c->acyclic_matches;
    for (int x = 0; x < c->n; ++x)
        printf("%u%c", c->lower[x], x + 1 == c->n ? '\n' : ' ');
}

static void choose_edges(Census *c, const Edge *edges, int edge_count, int start, int need) {
    if (need == 0) {
        check(c);
        return;
    }
    for (int i = start; i <= edge_count - need; ++i) {
        Edge e = edges[i];
        c->lower[e.maximum] |= bit(e.minimum);
        choose_edges(c, edges, edge_count, i + 1, need - 1);
        c->lower[e.maximum] ^= bit(e.minimum);
    }
}

static void finish(Census *c) {
    Edge edges[MAX_VERTICES * MAX_VERTICES];
    int edge_count = 0;
    for (int b = c->top_begin; b < c->n; ++b) {
        c->lower[b] = bit(b);
        for (int x = c->minima; x < c->top_begin; ++x)
            if (c->above[x] & bit(b - c->top_begin)) c->lower[b] |= c->lower[x];
        for (int a = 0; a < c->minima; ++a)
            if (!(c->lower[b] & bit(a))) edges[edge_count++] = (Edge){a, b};
    }
    int memo[MASKS];
    unsigned full = bit(c->n) - 1;
    for (unsigned i = 1; i <= full; ++i) memo[i] = UNKNOWN_EULER;
    memo[0] = 0;
    /* An unforced extremal relation adds exactly one edge and no triangles. */
    int missing_edges = euler(c->lower, full, memo) - 1;
    if (missing_edges >= 0 && missing_edges <= edge_count)
        choose_edges(c, edges, edge_count, 0, missing_edges);
}

static void assign(Census *c, int x, int next_profile) {
    if (x == c->top_begin) {
        finish(c);
        return;
    }
    for (int i = next_profile; i < c->profile_count; ++i) {
        Profile p = c->profile[i];
        c->above[x] = p.maxima;
        unsigned eligible = 0;
        for (int y = c->minima; y < x; ++y) {
            unsigned lower_profile = c->lower[y] & c->low_mask;
            if ((lower_profile & p.minima) == lower_profile && (p.maxima & c->above[y]) == p.maxima)
                eligible |= bit(y);
        }
        for (unsigned subset = eligible;; subset = (subset - 1) & eligible) {
            unsigned ideal_closure = subset;
            for (unsigned rest = subset; rest; rest &= rest - 1)
                ideal_closure |= c->lower[first(rest)] & c->middle_mask;
            if (ideal_closure == subset) {
                c->lower[x] = bit(x) | p.minima | subset;
                assign(c, x + 1, i);
            }
            if (!subset) break;
        }
    }
}

static void prepare(Census *c, int vertices, int minima, int maxima) {
    c->n = vertices;
    c->minima = minima;
    c->maxima = maxima;
    c->top_begin = vertices - maxima;
    c->low_mask = bit(minima) - 1;
    c->middle_mask = (bit(c->top_begin) - 1) ^ c->low_mask;
    c->profile_count = 0;
    c->euler_matches = c->acyclic_matches = 0;
    for (int x = 0; x < minima; ++x) c->lower[x] = bit(x);
    for (unsigned low = 1; low < bit(minima); ++low)
        for (unsigned high = bit(maxima) - 1; high; --high)
            if (size(low) >= 2 && size(high) >= 2)
                c->profile[c->profile_count++] = (Profile){low, high};
}

int main(int argc, char **argv) {
    int twelve = argc == 2 && strcmp(argv[1], "--twelve") == 0;
    if (argc != 1 && !twelve) {
        fprintf(stderr, "Usage: %s [--twelve]\n", argv[0]);
        return 2;
    }
    uint64_t euler_matches = 0, acyclic_matches = 0;
    for (int n = twelve ? 12 : 4; n <= (twelve ? 12 : 11); ++n) {
        int first_maxima = n < 9 ? 2 : 3;
        for (int a = 2; a + first_maxima <= n; ++a) {
            for (int b = first_maxima; a + b <= n; ++b) {
                Census census;
                prepare(&census, n, a, b);
                assign(&census, a, 0);
                euler_matches += census.euler_matches;
                acyclic_matches += census.acyclic_matches;
            }
        }
    }
    fprintf(stderr, "Euler matches: %llu, acyclic presentations: %llu\n",
            (unsigned long long)euler_matches, (unsigned long long)acyclic_matches);
    return 0;
}
```

</details>

<details>
<summary>Python cover checker</summary>

```python
"""Find and check two categorical lower sets covering each census candidate."""

from collections import Counter, defaultdict, deque
from itertools import permutations, product
import json
from pathlib import Path
import sys


def points(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def upward(lower):
    return tuple(sum(1 << j for j, column in enumerate(lower) if column >> i & 1)
                 for i in range(len(lower)))


def canonical(lower):
    upper = upward(lower)
    classes = defaultdict(list)
    for x, (below, above) in enumerate(zip(lower, upper)):
        classes[below.bit_count(), above.bit_count()].append(x)
    blocks = [permutations(group) for _, group in sorted(classes.items())]
    best = None
    for ordered_blocks in product(*blocks):
        labels = [x for block in ordered_blocks for x in block]
        encoded = tuple(sum(1 << j for j, y in enumerate(labels) if lower[x] >> y & 1)
                        for x in labels)
        if best is None or encoded < best:
            best = encoded
    return best


def contract(lower, upper, domain):
    vertices = tuple(points(domain))
    active = domain
    image = vertices
    prefix = [image]

    while active.bit_count() > 1:
        deletion = None
        for x in points(active):
            rest = active ^ (1 << x)
            below = lower[x] & rest
            above = upper[x] & rest
            targets = [y for y in points(below) if lower[y] & below == below]
            targets += [y for y in points(above) if upper[y] & above == above]
            if targets:
                deletion = x, targets[0]
                break
        if deletion is None:
            break
        x, y = deletion
        image = tuple(y if v == x else v for v in image)
        prefix.append(image)
        active ^= 1 << x

    core = tuple(points(active))
    if len(core) == 1:
        return prefix
    predecessor = [[j for j, y in enumerate(core) if x != y and lower[x] >> y & 1]
                   for x in core]
    successor = [[j for j, y in enumerate(core) if x != y and upper[x] >> y & 1]
                 for x in core]
    comparable = tuple(lo | hi for lo, hi in zip(lower, upper))
    previous = {core: None}
    queue = deque([core])
    while queue:
        state = queue.popleft()
        if len(set(state)) == 1:
            tail = []
            while state != core:
                tail.append(state)
                state = previous[state]
            index = {x: i for i, x in enumerate(core)}
            prefix += [tuple(step[index[x]] for x in image) for step in reversed(tail)]
            return prefix
        for i, x in enumerate(state):
            choices = comparable[x] ^ (1 << x)
            for j in predecessor[i]:
                choices &= upper[state[j]]
            for j in successor[i]:
                choices &= lower[state[j]]
            for y in points(choices):
                step = state[:i] + (y,) + state[i+1:]
                if step not in previous:
                    previous[step] = state
                    queue.append(step)
    return None


def check_cover(lower, pieces):
    full = (1 << len(lower)) - 1
    assert len(pieces) == 2 and pieces[0][0] | pieces[1][0] == full
    for domain, fence in pieces:
        vertices = tuple(points(domain))
        assert domain and all(lower[x] & domain == lower[x] for x in vertices)
        assert fence[0] == vertices and len(set(fence[-1])) == 1
        for step in fence:
            assert len(step) == len(vertices)
            assert all(0 <= im < len(lower) for im in step)
            for i, x in enumerate(vertices):
                for j, y in enumerate(vertices):
                    assert not (lower[y] >> x & 1) or lower[step[j]] >> step[i] & 1
        for f, g in zip(fence, fence[1:]):
            assert (all(lower[y] >> x & 1 for x, y in zip(f, g))
                    or all(lower[x] >> y & 1 for x, y in zip(f, g)))


def find_cover(lower):
    upper = upward(lower)
    maxima = [x for x, above in enumerate(upper) if above == 1 << x]
    for selected in range(1, (1 << len(maxima)) - 1, 2):
        domains = [0, 0]
        for i, x in enumerate(maxima):
            domains[selected >> i & 1] |= lower[x]
        pieces = []
        for domain in domains:
            fence = contract(lower, upper, domain)
            if fence is None:
                break
            pieces.append((domain, fence))
        if len(pieces) == 2:
            check_cover(lower, pieces)
            return pieces
    raise ValueError(f"No two-cover found for {lower}")


def stable_partition(lower):
    upper = upward(lower)
    full = (1 << len(lower)) - 1
    minima = sum(1 << x for x in points(full) if lower[x] == 1 << x)
    maxima = sum(1 << x for x in points(full) if upper[x] == 1 << x)
    middle = full ^ minima ^ maxima
    left_middle = middle
    while True:
        left = minima | left_middle
        right = maxima | (middle ^ left_middle)
        left_fence = contract(lower, upper, left)
        if left_fence is not None:
            right_fence = contract(lower, upper, right)
            if right_fence is not None:
                return [(left, left_fence), (right, right_fence)]
        if left_middle == 0:
            break
        left_middle = (left_middle - 1) & middle
    raise ValueError(f"No extrema partition found for {lower}")


def classify_twelve(input_path, output_path):
    labelled = {tuple(map(int, row.split())) for row in Path(input_path).read_text().splitlines()}
    assert labelled and all(len(order) == 12 for order in labelled)
    orders = {canonical(order) for order in labelled}
    exceptional = []
    for lower in sorted(orders):
        try:
            find_cover(lower)
        except ValueError:
            exceptional.append({"lower": lower, "parts": stable_partition(lower)})
    result = {
        "isomorphism_classes": len(orders),
        "with_ordinary_two_cover": len(orders) - len(exceptional),
        "stable_partitions": exceptional,
    }
    Path(output_path).write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print("Twelve vertices:", len(orders), "classes,", len(exceptional),
          "require a stable partition.")


if __name__ == "__main__":
    if len(sys.argv) == 4 and sys.argv[1] == "--classify-twelve":
        classify_twelve(sys.argv[2], sys.argv[3])
    elif len(sys.argv) == 3 and sys.argv[1] == "--check":
        records = json.loads(Path(sys.argv[2]).read_text())
        for row in records:
            pieces = [(domain, [tuple(step) for step in fence]) for domain, fence in row["pieces"]]
            check_cover(row["lower"], pieces)
        print("Validated", len(records), "two-cover certificates")
    else:
        orders = {canonical(tuple(map(int, line.split()))) for line in Path(sys.argv[1]).read_text().splitlines()}
        certificates = [{"lower": lower, "pieces": find_cover(lower)}
                        for lower in sorted(orders, key=lambda order: (len(order), order))]
        print("Two-cover certificates by size:", dict(sorted(Counter(map(len, orders)).items())))
        Path(sys.argv[2]).write_text(json.dumps(certificates, separators=(",", ":")) + "\n")
```

</details>

## Contiguity under subdivision

`DescendingClosureContiguity` proves finite ranked interpolation of
pointwise ordered order maps, relative to all vertices on which they agree.
For face posets, intersection with a selected vertex set gives the
descending map on its meeting-face neighborhood. The module proves the
relative contiguity chain for this map, the cover of flags by two such
neighborhoods, and preservation of contiguity classes by the induced
face-image maps.

`RelativeDerivedContiguity` constructs a complex whose simplices consist
of old base vertices and a flag of outside faces containing those old
vertices. For a finite source vertex type, full bases, and a contiguous
pair of vertex maps preserving and reflecting base membership, it proves
that the induced maps are joined by a simplicial contiguity chain on the
relative derived complexes. The common union of outside-face images
allows the exterior maps to be interpolated while the old map is fixed,
and permits one contiguous change of the old base map between those
interpolations. The retained base is full and every step respects the
base and exterior vertex sets, so the construction can be iterated.

`BarycentricGraphDistance` proves exact doubling of the extended
one-skeleton distance between two subcomplexes under ordinary
barycentric subdivision. The proof contracts alternating face walks
by choosing a vertex at each inclusion minimum. It also shows that
a full subcomplex containing a graph neighborhood of radius `D`
contains the corresponding neighborhood of radius `2D` after subdivision.
`BarycentricNeighborhoodIteration` constructs the order complex
in the same simplicial representation and proves the neighborhood
bound at every depth.

`BarycentricBaseRigidity` uses two applications of the neighborhood
bound to rule out a first move in a same-depth contiguity chain. If
the only vertex that can be adjoined to every incident maximal base
face is the original base vertex itself, that vertex remains fixed
throughout the chain. For relative cones each maximal base face has
its own exterior tip. Applied to a nontrivial strong core, this
obstructs a categorical piece containing the whole subdivided base.

This distance calculation supports a quantitative obstruction to
a uniform subdivision depth. Relative subdivisions of cones over a
twice subdivided triangulated torus can have arbitrarily long
prescribed initial stretches of constant category, with that
category equal to one more than the torus dimension. The Lean
modules verify the subdivision and distance ingredients. The cone
construction is a separate mathematical proof, and Question 6.3 on
the eventual stable category remains open.

## Rigidity for relative cones

After any positive number of derived subdivisions fixing the base of a
cone, every retained maximal base face has one strict coface and a
distinct exterior tip. A further relative step sends each unique coface
to the new tip indexed by that coface, so this incidence persists.

Suppose the maximal faces through each original base vertex intersect
in that vertex and at least two such faces meet there. The distinct tips
exclude exterior vertices from the intersection of their coface
neighborhoods. The maximal-face criterion then fixes every original base
vertex through all same-depth contiguity chains of the base inclusion.
The Lean theorem holds at every subsequent ordinary subdivision depth.
Question 6.3 also requires deciding the existence of a categorical
two-cover, whose members may meet only parts of the base.
