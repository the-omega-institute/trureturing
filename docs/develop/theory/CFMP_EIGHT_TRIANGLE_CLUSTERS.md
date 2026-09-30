# CFMP: adjacent three-edge degree-eight clusters

## Scope

Let (N,T) be a finite, connected, orientable ideal triangulation of a compact
3-manifold whose boundary components have genus at least two. Assume every
global edge has degree exactly 8 or at least 16. Write L for the degree-eight
edges and H for the remaining edges.

For a tetrahedron sigma, let S_sigma be the set of its six local edges whose
global edge lies in L. Assume that |S_sigma| is 3 or 4 and that every member of
S_sigma is adjacent (in the tetrahedron) to exactly two other members of
S_sigma. Thus a three-edge packet is one of the two incidence types (a
three-star or a three-cycle), and a four-edge packet is a four-cycle. This is
an incidence condition on actual local edge occurrences; it does not identify
distinct global edges or impose equal lengths.

The theorem below is a new valence-eight subcase. The four-cycle-only case with
a different high cap is treated separately in the repository. The new content
here is the three-star/three-cycle packet, where the two degree-eight neighbors
of a low edge are adjacent.

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
a = 5/4 and c = 4/3. Let q_D = cos(2*pi/D), and choose

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

  three-star:   (2,2,1,c,c)       phi_1 = 121/175
  three-cycle:  (2,c,1,c,2)       phi_1 = 13*sqrt(41)/123
  four-cycle:  (2,c,a,2,c)         phi_1 = 473/700.

Each square is strictly smaller than 1/2:
2*121^2 < 175^2, 2*(13^2*41) < 123^2, and 2*473^2 < 700^2.
Thus alpha_1 > pi/4 at every occurrence, the cone angle is strictly larger
than 2*pi, and K_e < 0.

### High-edge lower faces

For x1=h, the universal lower envelope on [1,2]^6 gives

  phi_1 >= 2*(2-h)/(h+1) > q_D.

Hence alpha_1 < 2*pi/D <= 2*pi/d(e), so the cone angle at every high edge
is strictly less than 2*pi and K_e > 0. The first strict inequality is exactly
the choice of delta above.

### High-edge upper faces

For x1=c, monotonicity gives the conservative endpoint bound

  phi_1 <= phi_1(c,2,2,1,2,2) = 23/25.

Moreover 23/25 < cos(pi/8). Indeed, after squaring this is
529/625 < (2+sqrt(2))/4, and sqrt(2) > 866/625 because
2 - (866/625)^2 = 31294/390625 > 0. Therefore every high-edge occurrence
has alpha_1 > pi/8. Since d(e) >= 16, its cone angle is strictly greater
than 2*pi and K_e < 0.

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
triangulation of a compact 3-manifold by hyperbolic truncated (partially
truncated) tetrahedra. The theorem above is a strict hyper-ideal subcase:
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
