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
  - D5/S3/Topology/ThirteenPointStructuralCategoricalCovers
  - D5/S3/Topology/SmallSubdivisionCategoricalCovers
  - D5/S3/Topology/CrossedExtremalProfiles
  - D5/S3/Topology/RelativeDerivedContiguity
  - D5/S3/Topology/BarycentricGraphDistance
  - D5/S3/Topology/BarycentricNeighborhoodIteration
  - D5/S3/Topology/BarycentricBaseRigidity
  - D5/S3/Topology/ConnectedCategoryGraft
  - D5/S3/Topology/PathContiguity
  - D5/S3/Topology/FixedTargetGraphTermination
  - D5/S3/Topology/GraphSubdivisionIntervals
  - D5/S3/Topology/GraphSubdivisionHalves
  - D5/S3/Topology/GraphSubdivisionNullhomotopy
  - D5/S3/Topology/GraphSubdivisionPositions
  - D5/S3/Topology/GeometricGraphTermination
  - D5/S3/Topology/RankedCofaceContiguity
  - D5/S3/Topology/CofaceComparisonObstruction
  - D5/S3/Topology/CofaceTriangleCollapse
  - D5/S3/Topology/RetractionCoordinate
  - D5/S3/Topology/StableCategory/TetrahedralGraphIteration
  - D5/S3/Topology/StableCategory/TetrahedralCategoricalCover
  - D5/S3/Topology/BarycentricRealization
  - D5/S3/Topology/StableCategory/FourPieceCategoricalCover
  - D5/S3/Topology/StableCategory/DimensionFourCategoricalColour
  - D5/S3/Topology/StableCategory/LebesgueStarAssignment
  - D5/S3/Topology/StableCategory/TetrahedralOneSidedRefinement
  - D5/S3/Topology/StableCategory/TetrahedralAsymmetricIteration
  - D5/S3/Topology/StableCategory/ThreePieceCategoricalCover
  - D5/S3/Topology/StableCategory/DepthZeroElementaryExpansion
  - D5/S3/Topology/StableCategory/ExactCategoricalExtension
  - D5/S3/Topology/StableCategory/MixedSimplexChart
  - D5/S3/Topology/StableCategory/MixedSimplexAttachment
  - D5/S3/Topology/StableCategory/ShellingExactExtension
  - D5/S3/Topology/StableCategory/ProductRigidCores
  - D5/S3/Topology/StableCategory/ProductStableCover
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

## The factor-two bound for two-dimensional complexes

The stable category is at most twice the weak category when the order
complex has dimension at most two. More generally, if the inclusion
of a finite subcomplex $A$ of dimension at most two is nullhomotopic
in the realization of a finite complex $K$, after some common
ordinary subdivision depth the base is covered by two subcomplexes
categorical in the subdivided ambient complex.

In each triangle of $A$ take the tripod joining the original vertices
to its center. Together with all original vertices, these tripods
form a graph in the first subdivision. Its inclusion in the ambient
complex is nullhomotopic. One further subdivision makes the graph
full. Every nonisolated edge in this graph lies in a small triangle
in its original triangle. The small triangles chosen for different
edges are distinct, since a triangle containing two graph edges would
contradict fullness.

With the target triangulation fixed, simplicial approximation of a
nullhomotopy gives a contiguity chain from an iterated endpoint
selection on a finer subdivision of the graph to a constant. Write
$b$ for this additional source depth. In each of the chosen small
triangles replace the graph edge by a simple path joining its old
endpoints and disjoint from the triangle boundary elsewhere. At
ordinary depth $s$ the replacement can have at least $2^{b+s}$
edges. To see this, choose two disjoint interior subdivided triangles
at a fixed depth $k$, at graph distance $d>0$. Draw a simple arc in
the triangle with at least $N$ passages between these two triangles,
where $Nd\geq 2^{b+k}$. Use a sufficiently thin neighborhood and
follow the arc by a walk along fine triangle barycenters and the
barycenters of their common edges. Extend the arc parameter to the
ambient triangle. Choose disjoint closed parameter intervals that
force visits to the specified interiors. At fine depth each edge
changes the parameter by less than an interval width, so erasing
loops preserves the visits. Distance doubling shows that each
passage takes at least $2^{s-k}d$ edges. Finiteness lets the paths be
chosen at one common depth.

The replacement paths meet at the old graph vertices and preserve the
tripod incidence. Folding a chosen triangle onto its old graph edge
gives a contiguity to the identity relative to that edge. After
subdivision and restriction, the folded path maps into the subdivided
old edge. It has the same endpoints as the composite of a monotone
surjection onto the $(b+s)$-fold subdivided edge and the subdivided
endpoint selection. The two maps are contiguous through a chain
relative to their endpoints. The Lean theorem proves this interval
interpolation for finite source complexes. A maximal label among
vertices still above the pointwise minimum can be lowered one step
without violating contiguity on incident simplices. The sum of labels
strictly decreases. The relative chains glue across the graph and
then follow the subdivided nullhomotopy. Thus the replaced graph is
categorical at the same depth as its ambient target.

The complement of each tripod has three sectors, one adjacent to
each open original side. The sectors incident to one side can meet
across that side. At a different side or original vertex the
components remain separate. Consequently each complementary
component lies in the closed star of an original edge. This works
also at a free edge, an edge incident to more than two triangles,
or a maximal edge. One further subdivision makes the categorical
graph full. The induced complex on the remaining vertices lies
componentwise in subdivided closed edge stars. These stars are cones
before subdivision and their contractions persist under subdivision.
Move the resulting constant values along ambient edge paths.

Finally, a cover of the vertex set by categorical induced complexes
gives a categorical cover of the next subdivision. For a vertex
part $S$, use the flags of faces meeting $S$. Intersection with $S$
is monotone and pointwise below the inclusion. It factors through
the subdivision of the induced complex on $S$. Each flag is covered
because a vertex of its smallest face belongs to some part and
persists in the entire flag. This gives the two categorical pieces.

For a finite space of weak category one, the realization of its order
complex is contractible, so the local result applies. When the order
complex has dimension at most two, a dimension colouring of the face
poset gives at most three pieces, which suffices for weak category
at least two. The simplicial and finite-space comparisons transfer
the bound at the next subdivision. The componentwise bounds add.
[Question 6.3 and the comparison inequalities](https://arxiv.org/html/2609.39615v1#S6)
· [Simplicial approximation of homotopies](https://arxiv.org/abs/1701.07612)

## Thirteen-point cores and the first possible counterexamples

Question 6.3 holds through thirteen points. A connected space of
weak category one has a core whose order complex is mod-two acyclic.
At thirteen points a core with at most two maxima has an ordinary
two-cover. With at least three maxima the exhaustive search gives
12,282 mod-two acyclic core classes. Of these, 12,229 have an ordinary
two-cover. The other 53 have two categorical induced vertex parts.
The subdivision transfer turns each partition into a lower
two-cover of the second subdivision.

In those 53 classes the ordinary category is three in 51 cases and
four in two. All the mod-two acyclic classes in this census have
contractible realizations. A spanning tree in the order complex gives
the edge presentation of its fundamental group. Substituting a
generator that occurs exactly once in a relator eliminates that
generator and its relation. These substitutions eliminate every
generator. Integral elimination in the higher boundary matrices gives
only unit pivots, so the boundary images are saturated. The mod-two
homology test then forces zero reduced integral homology. Hurewicz
and Whitehead give contractibility. This identifies the category
triples of the 53 classes as (1,2,3) and (1,2,4).

For completeness the census orders the intermediate points by their
sets of lower and upper extrema, refining ties by a topological
ordering. It enumerates predecessor ideals within the orders admitted
by these profiles. Among all labels of the extrema, one minimizes the
sorted profile rows lexicographically. Swapping a first inverted
pair of columns in the lower or upper masks decreases this sequence.
This permits pruning by column order while preserving every
isomorphism class. Optional opposite-extrema relations never lie in
a triangle of the order complex. A cycle through an optional relation
would give nonzero mod-two first homology. Thus the optional
relations form a tree after contracting the forced components.
The Euler characteristic fixes their number, and the boundary
matrices check acyclicity. An unpruned optional-edge search gives
the same stream of 107,928 labeled presentations. Stable color
refinement followed by permutations within its classes decides
isomorphism exactly.

For weak category at least two, ordinary category at most four is
enough for Question 6.3. The double-strictness classification uses
a stronger structural comparison. Five or more maxima leave an
extremal partition into two categorical domains. With four maxima,
all but the profiles (3,4,6) and (4,4,5), in the order minima, maxima,
and middle points, also yield this partition. In these last two
profiles the catalogue of remaining incidence orders has 73 classes.
The two domains for 72 classes separate the minima from the maxima.
Adding optional comparisons from minima to maxima then preserves the
induced orders of both domains and every inequality in their
contractions. The last order is dual to the face poset of the
projective plane with K4 as its graph and its three quadrilateral
cycles as two-cells. Its weak category is three by cup-length and
dimension. Ordinary category is at most four, so it cannot have
both gaps strict.

The new Lean module checks the 53 and 72 categorical vertex
partitions and the lifting under optional opposite-extrema
comparisons. Enumeration completeness, order isomorphism,
contractibility, and the exact ordinary-category tests use the
mathematical and computational arguments above.
[Question 6.3](https://arxiv.org/html/2609.39615v1#S6)

## A four-cover through forty-one points

Every connected finite poset of at most forty-one points has a
categorical lower cover by at most four parts after its second
ordinary subdivision. Thus the factor-two conjecture in this range
can fail only for a connected component of weak category one.

Pass to a core. Let a, b, and m count its minima, maxima, and
intermediate points. At most four extrema on either side give the
result by the principal lower covers and subdivision of the dual.
Otherwise a,b ≥ 5. Every middle point has at least two minima
below it and at least two maxima above it. A minimum p and maximum
q specify two categorical blocks. The first uses all maxima and
middles above p. The second uses all minima and the remaining
middles below q. Within each block collapse the middle points
and the extrema incident to them toward the common bound. The
other extrema are isolated in the induced block and can move
independently to an ambient constant.

If the remainder has at most twelve points, two additional
categorical parts suffice. Every connected core on at most twelve
points has a two-cover at depth two. When one extrema count is
three, a popular bound sees all but at most two middle points.
With at least four extrema on the other side there is at most one
leftover. When both counts are three the leftover pair shares an
opposite bound. With at least four extrema on both sides, a common
bound for all but one middle suffices except for the four-middle
case with four extrema on each side, handled by the crossed
matching and cycle argument. The cases of at most two extrema
use the principal covers and duality. Core retractions preserve
the depth-two result. For a disconnected remainder, reuse the
two cover indices across its components and move their constants
along paths in the connected ambient poset.

To assemble the cover, for each vertex block take the flags of
chains meeting that block. Intersection with the block retracts
the chain poset onto its chains. The comparable maps induce
contiguities after subdivision. Pull back the two lower covers
of the remainder along this retraction at depth two. Every flag
is covered since the least chain of the flag meets some block.

Suppose that every choice of p and q leaves at least thirteen
middles. Greedy averaging leaves at most
$m(1-2/a)(1-2/b)$. For $s=a+b$, this is at most
$(41-s)(1-4/s)^2$. That function is below thirteen at $s=22$
and decreasing thereafter. By duality take $a\le b$, hence
$a\le10$ and $a\le b\le21-a$. Every minimum meets at most
$m-\lceil 13b/(b-2)\rceil$ middle points, or a choice of an
opposite maximum would leave fewer than thirteen. The excess
of lower incidences over $2m$ is at most
$(a-2)(41-a-b)-a(13+\lceil26/(b-2)\rceil)$.
Maximizing over the allowed values of $b$ gives
$-4,2,6,8,8,0$ for $a=5,6,7,8,9,10$. Check $b=a$ and the
breakpoints $6,7,8,9,11,15$ in range, since the expression
decreases between breakpoints.

At most four middles therefore have at least four minima
below them. With four, their lower profile sizes are four and
all other sizes are two. With three, the three profiles have
at least twelve incidences among at most ten minima. Choose
$p$ below two and $q$ above the remaining one if necessary.
With one or two, choose $p$ below the first and $q$ above the
second if necessary. The residual lower profiles now have at
most two sizes. Points of a fixed size are categorical because
comparable points have identical lower profiles. Send each
point to a chosen minimum below it and move the constants of
its comparability components to one ambient point. Thus the
residual profiles give the last two blocks.
[The finite-space category comparisons](https://arxiv.org/html/2609.39615v1#S2)

## Fourteen-point counterexample exclusion

Question 6.3 holds through fourteen points. At weak category one the
order complex of a connected core is contractible, so it is mod-two
acyclic. With at most two maxima, principal lower sets already give
a two-cover. With at least three maxima, the same profile, optional
comparison, and homology enumeration gives 2,404,458 presentations.

For 2,403,824 of these presentations there is a minimum $p$ and maximum
$q$ such that every middle point lies above $p$ or below $q$. Put
the middles above $p$ with all maxima and put the remaining middles with
all minima. The first induced domain contracts by lowering the assigned
middles and their incident maxima to $p$. Other maxima are isolated in
that domain and can move independently along ambient paths. The second
domain uses the dual contraction toward $q$.

The remaining 634 presentations give 52 isomorphism classes under
exact directed-graph isomorphism. Each class has two induced categorical
parts. The Lean checker verifies their 910 order-map changes and
transfers each partition to a categorical lower two-cover of the
second ordinary subdivision. The enumeration and isomorphism
classification are external calculations.

A separate pass deduplicates the full acyclic census by canonical
order tables and finds 206,265 classes. It constructs ordinary
two-covers for 204,596 classes and directly verifies categorical
partitions for the other 1,669. These checks confirm the bound without
using the common-extrema test to discard classes.

The four-cover above handles
components of weak category at least two. Passing to cores and adding
over connected components excludes any counterexample with fewer than
fifteen points. The unrestricted inequality remains open.
[Question 6.3](https://arxiv.org/html/2609.39615v1#S6)

## Contiguity contractions of graph maps in a fixed target

For a finite graph, choose paths from one ambient vertex to the images of the original graph
vertices. On every oriented edge, assume that triangle moves replace the
mapped edge by the concatenation through the chosen ambient vertex.
The Lean theorem `GraphSubdivisionNullhomotopy.supported_graph_map_contracts`
gives a common depth beyond which composing any selection from the original
vertex supports with the graph map yields a contiguity contraction in the
fixed target. Each old edge becomes an interval. First replace the edge maps
relative to their endpoints. Then contract the two half paths sharing its
midpoint simultaneously, including at vertices shared by several old edges.

If each graph component induces the trivial map on fundamental groups and
the vertex images lie in one ambient component, choose the vertex paths
using a spanning tree in each graph component and a path from the common
base to its root image. The classical edge-path description of the
fundamental group gives finite move witnesses for this choice.
The Lean theorem takes those witnesses as hypotheses. This is the
fixed-target step for the three-dimensional approach to Question 6.3.

For a geometric nullhomotopy there is also a direct construction.
Place the subdivided graph vertices at dyadic points on their old edges.
The pullbacks of the target vertex stars have a common Lebesgue number
on the homotopy cylinder. A fine time mesh gives contiguous consecutive
rows because the labels on each subdivided face at adjacent times all
belong to a single target face. The bottom row is contiguous to every
selection from the original supports, and the top row is constant.
The Lean theorem `GeometricGraphTermination.realized_graph_map_contracts`
uses this construction with the affine realization of a simplicial graph map.

## Coface comparisons in the four-dimensional approach

The triangle-cone construction seeks a map from a region of the ordinary
collar into one further subdivision of its triangle parameter. The
ordinary retraction is an order map. If a chain-preserving comparison
map lies pointwise above it, updating in descending face rank yields
a contiguity chain fixed wherever the maps agree. The comparison
allows the new map to reverse a comparable pair of source vertices.

A failed coface extension in a complex with face sizes at most three
has a witness of at most three prescribed comparisons when starting at
a vertex. A prescribed coface incomparable with the partial choice
forces every solution to contain their union. Each feasible such union
adds a vertex.

When the vertex labels have at most three vertices, contain their
respective vertices, and form an inclusion chain on every source face,
the source retracts by one contiguity step onto a full graph subcomplex.
An inclusion-maximal label on each triangle equals the triangle. Its
vertex has every incident face inside that triangle, so simultaneous
replacement of one such vertex per triangle gives the retraction.
Vertices whose labels have at most two elements stay fixed. The
whole-cone partition needed for the four-dimensional bound remains
open. [Question 6.3](https://arxiv.org/html/2609.39615v1#S6)

## Ordinary face cuts and flag capacity

A colour-preserving simplicial map preserves and detects membership
in the ordinary two-cut collar. Taking image flags commutes with
both cuts, even when the map identifies vertices. The union of the
retracted nested flag is exactly the part of the original support
of the selected colour. With the chamber table and its interval
charts supplied, this transports the cut data through the four old
rank colours in the three-dimensional construction. If suitable
charts are given on all source faces, an interval contiguity chain
can be interpreted in each chart. At vertices fixed during the
chain the charts need only agree at the fixed value.

The three-dimensional chamber comparison uses recursive path
coordinates on the selected old graph. A subdivision vertex
gets the sum of the least and greatest coordinates in its face.
The coordinate of the actual two-cut retraction therefore agrees
with the height computed from the tetrahedral table. On an old
edge the two possible ranks orient the interval chart. On a
singleton support the table fixes both maps at its retained vertex.
These two cases glue the contiguity chain on the whole main region.
In each extra component, adjacency preserves the two selected old
vertices of the opposite colour. Its opposite retraction lies in
the subdivided edge on those two vertices. The categorical-cover
iteration also requires the map to the fourth subdivision and its
comparison with the graph map used for termination.

The four-dimensional cone argument uses a separate chain argument
to force an interface of nonzero degree to hit every target
triangle. The ranked-fibre bound in Lean
limits the distinct coface labels that any one chain can supply
when they must come from the same fibre. A second bound applies
to an isotone whole-flag assignment whose singleton values
record the actual retracted face. A target triangle of flags
starting with the singleton of a three-vertex face forces a
source chain with sizes at least three, four, and five. The
ordinary triangle cone allows only four vertices in a source
face. The weaker comparison with only containment in the largest
assigned face remains open.

For a synchronously subdivided coarsening ($f_{s+1}=\operatorname{sd} f_s$),
there is an obstruction at every depth $s\ge4$ when the comparison is
required to preserve the full old sides and their endpoints. The source
and target subdivisions of an old side are paths of equal length, so the
comparison on that side is the identity. At the singleton flag over an
edge $A$, maximal-face containment then forces a singleton face of the
preceding target to equal $A$. The same argument allows either direction
of comparison between consecutive flags.

## One round of two-colour graph refinement

Suppose that the inclusions of two induced colour regions admit contiguity
factorizations through properly two-coloured graphs. The join of these
graphs has a proper four-rank colouring. On each main region the
tetrahedral heights give a map into four ordinary subdivisions of the
corresponding graph after only three ambient subdivisions. Each extra
component contracts through one opposite-colour carrier edge. If the
ambient one-skeleton is connected, its constant can be moved to the
image of a chosen vertex of the main parameter graph. The Lean
construction gives both refined factorizations in the same colouring
and permits any vertex selector for the final parameter subdivision.

## Weak category one in dimension at most three

Let the order complex of a nonempty finite poset have dimension at
most three and contractible realization. Some ordinary iterated chain
poset of the original poset has a categorical lower cover by two
sets. This is the weak-category-one case of Question 6.3 in that
range.

Height gives a proper four-rank colouring of every chain. The two
pairs of ranks induce bipartite graph parameters whose inclusions are
nullhomotopic by restriction of the contraction. Each refinement adds
three ambient subdivisions and four parameter subdivisions. After
enough rounds, the extra parameter subdivisions give fixed-target
contiguity contractions. The original edge carriers transport them
to the synchronously subdivided ambient complex. Taking the face
neighbourhoods that meet the two final colours gives categorical lower
sets in an ordinary iterated chain poset.

The relative theorem applies to a nonempty subcomplex with a proper
four-rank colouring and a nullhomotopic realization inclusion in a
finite ambient complex with connected one-skeleton. It gives two
subcomplexes covering an ordinary subdivision of the source. Both
inclusions contract by contiguity in the ambient at that same depth.
This allows a categorical region of dimension at most three to be
split while keeping its contractions in a higher-dimensional ambient.

## Four categorical pieces from a star assignment

Suppose a finite complex has dimension at most four and every closed
vertex star can be assigned to one of two subcomplexes with nullhomotopic
realization inclusions. The first barycentric subdivision separates
the mixed-label and five-vertex faces from the remaining faces. Each
induced region has dimension at most three. On every monochromatic flag,
the old label set is constant, including at the isolated pure top faces.
The realization map sends a flag to the weighted average of its face
barycentres. It identifies every subdivided subcomplex with the original
one and permits the supplied homotopies to glue on the open fibres of
the label sets. In a connected ambient, the two relative two-piece covers
then pull back by the face intersections at a common ordinary subdivision
depth. The Lean theorem gives four categorical lower sets in the face
poset at that depth.

For a connected complex of weak category two, the Lean theorem proves
the star assignment from the categorical open cover. In the original
coordinate metric each barycentric subdivision shrinks the mesh by at
most four fifths. Once the mesh is smaller than the Lebesgue number,
each closed vertex star lies in one categorical open. The proof
transports the two homotopies to the subcomplexes of faces carried into
the respective opens. For a finite poset with connected order-complex
realization and order-complex dimension at most four, this gives four
categorical lower sets in some ordinary iterated chain poset.

## Three-piece bound for contractible complexes

For a nullhomotopic realization inclusion of a subcomplex of dimension
at most five, the one-sided tetrahedral refinement gives a paper
proof of a relative three-piece cover. The lowest two face ranks form
a bipartite graph. Fold the other ranks to one apex when reading the
tetrahedral colouring. The graph parameter gains four levels for
every three ambient levels, and the other parameter retains the
ambient depth. Its exceptions contract through single graph edges
and enter the next parameter as isolated vertices. At the terminal
depth the graph region contracts. The remaining parameter has
dimension at most three and gives two pieces by the relative theorem.
Pulling back through the meeting-face maps gives the three-piece
cover at a single ambient depth. The Lean theorem proves the absolute
version for every finite simplicial complex of dimension at most five
with contractible realization. The relative version above remains a
paper deduction.

In dimension four the two-piece bound for contractible realization
remains open. A PL four-ball with 19 vertices and 69 maximal simplexes
admits a three-piece cover with strongly collapsible intersections
for which each pairwise union contains a domination-free ambient
retract. The retracts persist under common subdivision, so every
pairwise union remains noncategorical. This ball has another
two-piece cover obtained by redistributing parts of the original
three pieces.


## Categorical covers across one elementary expansion

Suppose the retained complex has a categorical two-cover on its
given triangulation and the expanded complex is connected. The Lean
theorem gives a categorical lower cover of size two for the face
poset after two ordinary barycentric subdivisions of the expanded
complex. For a mixed attachment, take the vertices omitted by the
old attaching facets assigned to the second piece. They form a
face in the first piece and belong to every old attaching face
exclusive to it. This face supplies the contiguity comparison for
the two new face vertices. A monochromatic attachment leaves a
separate categorical edge in the opposite first-subdivision region.

The corresponding transport of an arbitrary inherited cover
on a positive-depth subdivision is known here for a triangular
expansion by a paper argument with rooted trees and the planar dual.
In dimension four the same colouring rule can fail at every common
depth. Linked curves in the old trace can become nullhomologous in
the new colour, preventing any endpoint map that fixes the old
trace. It remains open whether a different colouring or a
contraction that moves the old trace gives a general transfer.


## Exact intersections across an attachment

Suppose the retained subcomplex is full and has a prescribed two-piece
cover. One further ordinary subdivision gives an exact categorical
extension when the attachment and one old piece are categorical
together. When the attachment and both old pieces are individually
categorical, there is an exact extension with three pieces, with the
third disjoint from the retained subdivision. More generally, if a
categorical cover by full subcomplexes contains the corresponding
prescribed old pieces, one further ordinary subdivision gives the
prescribed intersections without increasing the number of pieces.
The proofs intersect each retained face with a vertex set and compare
this order map with inclusion by a finite contiguity chain.


## Two categorical pieces across a mixed simplex attachment

Let the retained complex have two prescribed categorical pieces.
Choose a vertex of the attaching simplex and two disjoint nonempty
blocks of its other vertices. In each piece the faces inside the
simplex restrict to the corresponding horn, and each exterior face
uses only the chosen vertex and its own block among the simplex
vertices. The second subdivision has two full categorical regions
containing the prescribed pieces. A forbidden image in the chart
for one block requires a nonempty original face in that block.
Both exclusions cannot occur along a single face chain, since the
two blocks are disjoint. The retained region of each chart retracts
to the horn by adjoining the chosen singleton and deleting the top
face where needed. The comparisons fix the subdivided horn and
extend over the old piece. The full-cover extension theorem gives
exactly the prescribed old intersections at depth three.


## Exact extension across a shelling step

Suppose the retained triangulation already has a categorical
two-cover and one simplex is attached along a union of its facets.
The cover extends with both exact old intersections after three
ordinary barycentric subdivisions in the same ambient. At the second
subdivision the two induced regions need only cover vertices. In
the mixed case, use the face formed by the omitted vertices of the
facets in the second old piece. The first region can insert this
anchor into its new chains even if it lies in both prescribed pieces.
The second region cuts its chains by the second old piece. In the
monochromatic case connectedness suffices to move the constants for
the disjoint new and old components to a common vertex. A last
ordinary subdivision covers the remaining mixed flags and preserves
the prescribed intersections.

## Weak, stable, and ordinary category of a four-dimensional product

Let (P) have facets `012, 015, 023, 035, 145, 234, 345` and let
(X=F(P)\times F(P)), where (F(P)) is the poset of nonempty faces.
The realization is a PL four-ball since (P) is the boundary of an
octahedron with the relative interior of the face `124` removed.
Thus the weak category is one.

Lean gives ordinary category three. Deleting one boundary edge and its
unique triangle gives each of three categorical lower sets in the factor.
Every face is retained in at least two sets, so three corresponding
rectangles cover the product. With only two colours, the nine pairs of
exceptional triangles force a whole boundary cycle in a coordinate
slice of one colour. The three original vertices of that cycle remain
fixed under every step of a comparable order-map fence.

Lean also verifies a partition of the 484-point product core, obtained
by deleting the three up-beat boundary edges in each factor. Six
pointwise comparisons contract each colour in the product order.
Pullback along the beat retraction and the ordinary subdivision cover
theorem give two categorical lower sets after two subdivisions.
The stable category is two. The subdivided product retracts onto a coordinate slice,
and the factor is strongly minimal before
subdivision. Strong collapsibility is reflected by ordinary
barycentric subdivision by Barmak and Minian, Theorem 4.15.
This determines ((\operatorname{cat}_w,\operatorname{cat}_s,
\operatorname{cat})(X)=(1,2,3)) for this product. The general inequality
in Question 6.3 remains open.
[Question 6.3](https://arxiv.org/html/2609.39615v1#S6) ·
[Strong homotopy types, nerves and collapses](https://arxiv.org/abs/0907.2954)
