# CFMP: adjacent three-edge degree-eight clusters

## Scope

Let (N,T) be a finite, connected, orientable ideal triangulation of a compact
3-manifold whose boundary components have genus at least two. Assume every
global edge has degree exactly 8 or at least 12. Write L for the degree-eight
edges and H for the remaining edges.

For a tetrahedron sigma, let S_sigma be the set of its six local edges whose
global edge lies in L. Assume that |S_sigma|=3 and every member of S_sigma is adjacent (in the tetrahedron) to exactly two other members of S_sigma, so each packet is a three-star or three-cycle. In addition, every high local edge is opposite a low local edge and has at least two high neighbours. The separate four-cycle packet remains covered by the earlier degree-14 theorem. This is
an incidence condition on actual local edge occurrences; it does not identify
distinct global edges or impose equal lengths.

The theorem below is a new valence-eight subcase at high-edge threshold 12. The
three-star/three-cycle packet is the genuinely new local geometry. A separate
four-cycle theorem remains available at threshold 14.

## Six-variable cosine

Use the local order (12,13,14,34,24,23), with opposite pairs (1,4), (2,5),
and (3,6). Put x_i = cosh l_i and

A = 2*x1*x2*x6 + x1^2 + x2^2 + x6^2 - 1,
B = 2*x1*x3*x5 + x1^2 + x3^2 + x5^2 - 1,

P = x2*x3 + x5*x6 + x1*x2*x5 + x1*x3*x6
    - (x1^2 - 1)*x4,
phi_1 = P / sqrt(A B).

For a genuine hyper-ideal tetrahedron the dihedral angle at edge 1 is
alpha_1 = arccos(phi_1). The length-domain criterion and the formula are
Zhao, Lemma 2.2 and Proposition 2.4. On [1,2]^6, phi_1 is nondecreasing in
x2,x3,x5,x6 and nonincreasing in x4 (Zhao, Lemma 3.4; the explicit derivative
sign is formalized in the repository's mixed-coordinate comparison).

## Theorem

Under the incidence hypotheses above, the given triangulation admits a
nondegenerate hyper-ideal metric with zero cone curvature at every edge.
Consequently its face pairings give a hyperbolic metric with totally geodesic
boundary in the strict hyper-ideal sense.

## Proof

Let D be the maximum global edge degree. Set
a = 5/4 and c = 10/7. Let q_D = cos(2*pi/D), and choose

  0 < delta < min(1/3, 2*(1-q_D)/(2+q_D)),  h = 1 + delta.

Use the common global cosh-length box

  a <= x_e <= 2       (e in L),
  h <= x_e <= c       (e in H).

All coordinates lie in (1,2], hence the whole closed box is in the genuine
hyper-ideal length domain by the endpoint domain estimate on [1,2]^6.

### Degree-eight lower faces

Fix a local degree-eight edge as edge 1 and put x1=a. By monotonicity, the
smallest possible cosine occurs at the endpoint values listed below. The
entries list (x2,x3,x4,x5,x6).

  three-star:   (a,a,2,1,1)       phi_1 = 73/100
  three-cycle:  (a,1,2,1,a)       phi_1 = 8*sqrt(6)/27
  four-cycle:   (a,1,2,a,1)       phi_1 = 293/400

Each displayed number has square strictly larger than 1/2:
5329 > 5000, 384/729 > 1/2, and 85849/160000 > 1/2.
Therefore every occurrence has alpha_1 < pi/4. A degree-eight edge has eight
occurrences, so its cone angle is strictly less than 2*pi and K_e > 0.

### Degree-eight upper faces

Put x1=2. The largest possible cosine is

  three-star:   (2,2,1,c,c)       phi_1 = 709/1003
  three-cycle:  (2,c,1,c,2)       phi_1 = 11*sqrt(249)/249
  four-cycle:  (2,c,a,2,c)         phi_1 = 473/700.

Each square is strictly smaller than 1/2:
2*709^2 < 1003^2, 2*(11^2*249) < 249^2, and 2*(2753^2) < 4012^2.
Thus alpha_1 > pi/4 at every occurrence, the cone angle is strictly larger
than 2*pi, and K_e < 0.

### High-edge lower faces

For x1=h, the universal lower envelope on [1,2]^6 gives

  phi_1 >= 2*(2-h)/(h+1) > q_D.

Hence alpha_1 < 2*pi/D <= 2*pi/d(e), so the cone angle at every high edge
is strictly less than 2*pi and K_e > 0. The first strict inequality is exactly
the choice of delta above.

### High-edge upper faces

For x1=c, monotonicity and the high-occurrence condition give the endpoint bound

  phi_1 <= 5965/6972 < cos(pi/6). Since (5965/6972)^2 < 3/4 with margin 875363/48608784, every high-edge occurrence has alpha_1 > pi/6. Since d(e) >= 12, its cone angle is strictly greater than 2*pi and K_e < 0.

### Co-volume minimum

Let l_e = arccosh(x_e), and let Omega be the corresponding compact length box.
The standard co-volume identity (Luo--Yang) gives, for the global co-volume

  H(l) = sum_sigma cov_sigma(l|sigma) - 2*pi*sum_e l_e,

  partial H / partial l_e = -K_e.

At a lower face of Omega, K_e > 0, so increasing l_e decreases H. At an upper
face, K_e < 0, so decreasing l_e decreases H. Every boundary point therefore
admits an inward direction of strict decrease. A minimizer of H on Omega lies
in the interior, where all partial derivatives vanish. Thus K_e=0 for every
global edge. The common global lengths make every paired hexagonal face
isometric; zero cone curvature removes all interior edge singularities. This
is the claimed nondegenerate hyperbolic realization.

No Ricci-flow convergence theorem is used to assume existence. The only
external geometric inputs are the six-variable formula, its monotonicity and
length-domain criterion, and the co-volume gradient/convexity theorem.

## Relation to the CFMP conjecture

Costantino--Frigerio--Martelli--Petronio, Conjecture 0.8
(arXiv:math/0402339), asks for a geometric realization of an ideal
triangulation of a compact 3-manifold whose edge valences are at least six by
hyperbolic truncated (partially truncated) tetrahedra. The theorem above is a strict hyper-ideal subcase:
it does not claim the full minimum-six conjecture, arbitrary degree-eight
packets, or the partially truncated boundary cases. Zhao's 2026 theorem for
minimum valence nine does not cover the degree-eight edges here.

## References

- F. Costantino, R. Frigerio, B. Martelli, C. Petronio,
  *Triangulations of 3-manifolds, hyperbolic relative handlebodies, and Dehn
  filling*, arXiv:math/0402339, Conjecture 0.8:
  https://arxiv.org/abs/math/0402339
- X. Zhao, *Combinatorial Ricci Flows and Hyperbolic Structures on a Class of
  Compact 3-Manifolds with Boundary*, arXiv:2601.15174v2:
  https://arxiv.org/html/2601.15174v2
- F. Luo and T. Yang, *Volume and rigidity of hyperbolic polyhedral
  3-manifolds*, arXiv:1404.5365:
  https://arxiv.org/abs/1404.5365


## Explicit nonempty packet

The hypotheses occur in a genuine orientable ideal triangulation. Take 16 tetrahedra
indexed by 0,...,15, with face (t,f) opposite vertex f. Pair the following
unordered faces; the displayed permutation sends source vertices to target
vertices (the reverse pairing uses its inverse):

| source | target | permutation |
|---|---|---|
| (0,1) | (8,1) | 0123 |
| (0,2) | (4,2) | 0123 |
| (0,3) | (2,3) | 0123 |
| (1,1) | (9,1) | 0123 |
| (1,2) | (5,2) | 0123 |
| (1,3) | (3,3) | 0123 |
| (2,1) | (10,1) | 0123 |
| (2,2) | (6,2) | 0123 |
| (3,1) | (11,1) | 0123 |
| (3,2) | (7,2) | 0123 |
| (4,1) | (12,1) | 0123 |
| (4,3) | (7,3) | 0123 |
| (5,1) | (13,1) | 0123 |
| (5,3) | (6,3) | 0123 |
| (6,1) | (14,1) | 0123 |
| (7,1) | (15,1) | 0123 |
| (8,2) | (13,2) | 0123 |
| (8,3) | (11,3) | 0123 |
| (9,2) | (12,2) | 0123 |
| (9,3) | (10,3) | 0123 |
| (10,2) | (15,2) | 0123 |
| (11,2) | (14,2) | 0123 |
| (12,3) | (14,3) | 0123 |
| (13,3) | (15,3) | 0123 |
| (7,0) | (11,0) | 0132 |
| (2,0) | (6,0) | 0312 |
| (8,0) | (13,0) | 0231 |
| (9,0) | (1,0) | 0312 |
| (10,0) | (0,0) | 0132 |
| (15,0) | (4,0) | 0213 |
| (12,0) | (5,0) | 0312 |
| (14,0) | (3,0) | 0321 |

The 96 local edges fall into eight global classes. Six classes have size 8,
one has size 12 and one has size 36. A direct transitive-closure check gives
the six degree-eight classes
{0,6,12,18,24,30,36,42}, {1,7,13,19,49,55,61,67},
{2,8,26,32,50,56,74,80}, {14,20,38,44,62,68,86,92},
{25,31,37,43,73,79,85,91}, {48,54,60,66,72,78,84,90},
where local edge number is 6t+j in order (01,02,03,12,13,23).
The remaining classes have sizes 12 and 36. Every tetrahedron has local
degree-eight edges (01,02,03), a three-star. The two vertex links are connected
orientable surfaces with (F,V,chi)=(16,6,-2) and (48,10,-14), hence genera 2
and 8. Each edge link is a single circle and no edge is identified with its
reverse. Therefore this is a genuine compact orientable manifold after ideal
vertices are truncated, with one degree-eight packet type and high degrees 12
and 36.
