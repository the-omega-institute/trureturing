# Exact all-region RT on a three-loop bouquet over F13

## Definition 1: graph, coefficient matrix, and state

Let K=F13. The graph has central vertex O, outer vertices A_j,B_j for j=0,1,2, and edges OA_j, OB_j, A_jB_j. Each outer vertex has two boundary legs, all of dimension 13. Thus the graph is planar, with seven vertices, nine internal edges, and twelve boundary legs. All edges, including boundary legs, have unit cut weight.

Write the six rows of the following matrix as a_0,b_0,a_1,b_1,a_2,b_2:

    C = [[7,4,8], [11,12,3], [11,6,5],
         [4,9,8], [4,7,12], [2,4,1]].

For lambda in K^3 and z=(z_0,z_1,z_2) in K^3, define the four boundary labels of loop j, in order, by

    (a_j lambda + z_j, a_j lambda - z_j,
     b_j lambda + z_j, b_j lambda - z_j).

The loop multiplier is 1 at every outer tensor. Define Psi to be the sum over all lambda,z of these computational-basis vectors, with identical positive amplitude 13^(-3). No variable-dependent phases are present.

## Proposition 2: local AME realization and normalization

Psi is normalized and is the normalized contraction of one AME(6,13) tensor and six AME(4,13) tensors.

Proof. At O use 13^(-3/2) times the sum over lambda of |C lambda>. At every outer vertex use 13^(-1) times the sum over u,v of |u,v,u+v,u-v>, ordered as (central wire, loop wire, boundary leg 1, boundary leg 2). Contract equal internal coordinates by Kronecker deltas. Every triple of rows of C is independent, as follows in particular from Proposition 3 below. Therefore either three-leg side uniquely determines lambda, so the central tensor is AME. The four coefficient directions u,v,u+v,u-v are pairwise independent in odd characteristic, proving the outer tensors are AME.

The internal solutions are parametrized uniquely by lambda,z. Each boundary pair recovers its central coordinate and z_j using division by 2; C has rank 3, so the full boundary labels recover lambda as well. The support has 13^6 distinct elements. Before normalization every coefficient is 13^(-15/2), whose total norm is 13^(-9/2). Normalizing gives coefficient 13^(-3), as stated. Normalized maximally-entangled edge contractions change only the common pre-normalization scalar. QED.

## Proposition 3: central direction condition

For each j set V_j=(a_j,b_j,a_j+b_j,a_j-b_j). Select, independently in each block, either no row, one row of V_j, or the pair (a_j,b_j). Whenever the total number of selected rows is three, they are independent over K.

Proof. There are 4^3=64 selections of one direction from each block and 3 times 2 times 4=24 selections of a full pair and one direction from another block. All 88 determinants are nonzero. Here is the complete determinant certificate, with residues modulo 13.

For fixed u=0,1,2,3, let D_u[v,w]=det(V_0[u],V_1[v],V_2[w]); the four matrices are

    D_0 = [[1,11,12,3], [2,1,3,1], [3,12,2,4], [12,10,9,2]],
    D_1 = [[2,8,10,7], [5,2,7,3], [7,10,4,10], [10,6,3,4]],
    D_2 = [[3,6,9,10], [7,3,10,4], [10,9,6,1], [9,3,12,6]],
    D_3 = [[12,3,2,9], [10,12,9,11], [9,2,11,7], [2,4,6,11]].

The vectors (det(a_j,b_j,V_l[u])) for u=0,1,2,3 are

    (j,l)=(0,1): [3,2,5,1];   (0,2): [2,10,12,5];
          (1,0): [11,1,12,10]; (1,2): [7,4,11,3];
          (2,0): [4,3,7,1];    (2,1): [4,6,10,11].

These identities follow by the three-by-three determinant formula. The twenty triples of original C rows occur among these selections, so C is MDS. More generally every allowed collection of E rows has rank min(3,E). For E<3, extend it to an allowed three-row collection. Extending a chosen a_j+b_j or a_j-b_j to its full block preserves its span inside span(a_j,b_j), because a_j,b_j are independent. An extension exists since the three blocks offer six total directions. For E>3, choose an allowed three-row subcollection. QED.

## Theorem 4: all-region entropy and min-cut identity

For a region R, let r_j be its number of selected legs in loop j. Define

    H_R = number of j with r_j > 0,
    H_bar = number of j with r_j < 4,
    p = number of j with 0 < r_j < 4,
    e(0)=0, e(1)=0, e(2)=1, e(3)=2, e(4)=2,
    E = sum_j e(r_j).

Then H_R+H_bar=3+p and

    rank(F_R) = H_R + min(3,E),
    rank(F_bar) = H_bar + min(3,6-E),
    S(R)/log 13 = p + min(E,6-E) = m(R).

Here F_R is the selected boundary map on the six latent coordinates (lambda,z), and m(R) is the minimum number of edges separating R from its complement. In particular the equality holds for all 4096 subsets of individual boundary legs, including disconnected, empty, and full regions.

Proof of ranks. Project the selected row space onto the three z coordinates. Each active loop contributes exactly its own z direction, so the image dimension is H_R. Its kernel consists of central-coordinate rows obtained by cancelling z separately within each loop. For r_j=0 or 1 no central row remains. For r_j=2, choosing both legs of A_j leaves a_j, both of B_j leaves b_j, and choosing one leg of each leaves a_j+b_j or a_j-b_j up to a nonzero scalar. For r_j=3, one vertex has both legs: their difference recovers z_j and their sum recovers its central row; the third leg then gives the other central row. For r_j=4 the same two-dimensional central space remains. Thus the kernel has the allowed block structure of Proposition 3 and rank min(3,E). Since e(r)+e(4-r)=2 for each r, the complementary rank formula follows.

Proof of entropy. For the uniform positive state on a d-dimensional linear support L, let a,b be the dimensions of its two coordinate projections. The kernels on the two sides have dimensions d-b and d-a. Their cosets pair bijectively into q^(a+b-d) equal-sized, disjoint rectangles in the coefficient matrix. Every rectangle is a constant rank-one block. Hence the Schmidt spectrum is flat with q^(a+b-d) nonzero coefficients, and entropy is (a+b-d)log q. This uses identical amplitudes, not only identical moduli. Applying it with d=6 gives

    S(R)/log 13
      = H_R+H_bar+min(3,E)+min(3,6-E)-6
      = p-3+min(3,E)+min(3,6-E)
      = p+min(E,6-E).

Proof of cut. Fix the central vertex side c, with c=0 the complement side. If a,b in {0,1,2} count selected legs at the two outer vertices of one loop, and alpha,beta in {0,1} are their sides, its cut cost is

    [alpha != c] + [beta != c] + [alpha != beta]
      + (a if alpha=0 else 2-a) + (b if beta=0 else 2-b).

Minimizing over alpha,beta gives, for r=a+b=0,1,2,3,4 respectively,

    c=0: 0,1,2,3,2;
    c=1: 2,3,2,1,0.

These equal e(r)+[0<r<4] and e(4-r)+[0<r<4]. With c fixed, the three outer-pair choices are independent. Therefore the full cut is min(E+p,6-E+p), which equals the entropy exponent. For the empty region H_R=E=p=0 and H_bar=3, giving ranks 0,6 and entropy 0; the full region follows by symmetry. QED.

## Mathematical context

The local AME/MDS correspondence is standard, for example Raissi et al., [arXiv:1701.03359](https://arxiv.org/abs/1701.03359). The contribution here is the explicit simultaneous central direction certificate for this fixed cyclic wiring, not a new construction of isolated AME states or a minimum field-size theorem.

The connected-region result of [HaPPY, arXiv:1503.06237](https://arxiv.org/abs/1503.06237) has additional geometric assumptions. The designated-cut optimization in [Cui et al., arXiv:1508.04644](https://arxiv.org/abs/1508.04644) does not itself supply one perfect-tensor assignment for all cuts. Random-stabilizer constructions in [Hayden et al., arXiv:1601.01694](https://arxiv.org/abs/1601.01694) and [Apel et al., arXiv:2105.12067](https://arxiv.org/abs/2105.12067) already supply large-dimension probabilistic exact-RT results. [Bao et al., arXiv:2002.05317](https://arxiv.org/abs/2002.05317) give a broader AME/GHZ hypergraph framework. The theorem above is a concrete positive-uniform F13 witness; it makes no universal-topology or gravitational-dual assertion.
