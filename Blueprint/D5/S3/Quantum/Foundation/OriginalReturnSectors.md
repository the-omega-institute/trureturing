# Original return sectors and singular tails

## Abstract

Uniform sectors and intrinsic singular-tail mass for whole original returns.

V is the original finite dimensional real space, C is its closed pointed generating cone, and u is strictly positive on every nonzero cone vector. K is the entire normalized base C intersected with u=1, P consists of all its extreme points, and effects range over the entire interval [0,u]. Every original exclusion D(p) is the image of a whole closed Euclidean unit ball under an injective affine chart of positive dimension. Dimensions may vary and may equal one. Fix any source F=D(p), any y in ri(F), and any whole injective source chart. No singleton-label, injective-label, distinguishable-frame, Pair, closed-pure-locus or common-dimension assumption is imposed.

**Theorem 1.1 (Uniform leakage for all actual returns).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalReturnSectors.whole_return_leakage`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalReturnSectors.whole_return_leakage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every delta>0 there is epsilon>0, chosen before r and t, such that pure r,t with dist(r,y)<epsilon and t in D(r) satisfy alpha_F(t)<delta. Original zero symmetry gives r in D(t). This controls the entire return face and permits repeated label fibers.

A contrary sequence supplies actual r_n tending to y, t_n in D(r_n), x_n in D(t_n) a fixed positive distance from F, and original common confirming effects e_n vanishing on all of D(t_n). Joint compactness of K, K and the full effect interval gives a common limit (t,x,e). Evaluation continuity gives e(y)=e(x)=0 and e(t)=1. The limiting label t is only asserted to belong to K.

The open source ball maps exactly onto ri(F). Nonnegativity of e on the entire source ball and its zero at an interior parameter force its restriction slope to vanish. Thus F lies in the zero face of e. This face is proper because e(t)=1. The old classification of all original proper faces and whole-ball facial rigidity identify it with F, so x belongs to F, contradicting the distance bound. No purity or uniqueness of a limiting label is used.

**Theorem 1.2 (Actual contacts around every source interior point).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalReturnSectors.source_contact_simplex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalReturnSectors.source_contact_simplex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied source chart yields an actual xi with a(xi)=y and norm(xi)<1. There are dim(a)+1 unit parameter vertices forming an affine basis, with every barycentric coordinate of xi strictly positive. Their actual images are affinely independent. The chart dimension equals the affine dimension of F, and its linear range lies in ker(u). The old chart_boundary theorem identifies the unit contacts as original pure points under the full original hypotheses.

Place a small affine simplex around xi inside the open unit ball. Every vertex differs from xi, since all its barycentric coordinates at xi are positive. Continuity along each outward ray supplies a unit-sphere point. Divide the old positive weights by their positive radial factors and normalize their sum. These weights reconstruct xi from the new sphere points. Their affine span contains xi and each old basis vertex, so it is full; the exact number of vertices gives affine independence. The construction includes segment balls and xi=0.

**Theorem 1.3 (One sector for every original normal).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalReturnSectors.uniform_return_sectors`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalReturnSectors.uniform_return_sectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are epsilon, theta and H>0 before all r,t,b. For every actual pure return r,t with r near y and affine dimension of D(t) at most dim(a), one index i works simultaneously for every original nonzero positive annihilator b of t: a nonzero slope whose direction lies in sector i satisfies norm(g_b)<=H M(b) alpha_F(t). The quantifiers are constants, all r,t, one i, all b. There is no per-normal choice of i.

The old positive_annihilator_maximum supplies a pure global maximizer x in the same D(t). Choose a nearest source point a(q), norm(q)<=1. With s=norm(g_b)>0 and w=g_b/s, the global maximum and the dual bound give s(1-inner(w,q))<=A M(b) alpha. Hence norm(q-w)^2<=2 A M(b) alpha/s, and norm(x-a(v_i))<=alpha+norm(T_F)(sqrt(2 A M(b) alpha/s)+norm(w-v_i)). No division by alpha is made; the alpha=0 case is included. Zero slope lies outside the implication.

Positive barycentric reconstruction is stable for perturbed contacts and a nearby returned point in one common affine space of dimension at most dim(a). A fixed affine left inverse of the source chart reduces the perturbation to a fixed parameter space. Invert the perturbed affine interpolation map, obtain positive coordinates, prove actual reconstruction, and use rank counting to identify the common affine space. If every sector failed, pure maximizers in the same D(t) would be close to all source contacts and reconstruct r with strictly positive weights. Since dim(a)>=1, affine independence and extremality of r contradict this. All constants are fixed before the return and normal families.

**Definition 1.4 (Orthogonal projection onto the source affine space).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalReturnSectors.sourceProjection`

*Formalization.* `D5/S3/Quantum/Foundation/OriginalReturnSectors.sourceProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In any chosen Euclidean metric on V, this is the affine orthogonal projection onto aff(F), expressed using the source center and the orthogonal projection onto U=direction(aff(F)). It fixes aff(F), maps every point into aff(F), and contracts distances to every point of aff(F).

**Definition 1.5 (Actual projected return operator).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalReturnSectors.projectedLinear`

*Formalization.* `D5/S3/Quantum/Foundation/OriginalReturnSectors.projectedLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any whole return chart c+L closedBall(d), A is proj_U composed with L, with codomain restricted to U. Its kernel J is the kernel of this actual projected operator. J is not identified with ker(L), because the original L is injective.

**Theorem 1.6 (Dimension escape and positive intrinsic singular-tail mass).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalReturnSectors.original_return_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalReturnSectors.original_return_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are fixed positive epsilon, theta, H, beta and eta, with beta<R=diam(K)/2, depending only on the source data and K, before every sequence and every return chart. These constants satisfy the full sector bound. For any actual sequence r_n tending to y, t_n in P intersected with D(r_n), and the explicit eventual common-sector condition, alpha_n tends to zero. Every supplied whole injective chart of D(t_n), and every actual coordinate z_n mapping to r_n, has norm(z_n)=1, positive dimension d_n<=dim(ker(u)), and norm(L_n)<=R. Eventually d_n>=dim(a)+1.

The same original pure maximizers give contacts near the fixed source simplex. Project them orthogonally into aff(F). A second stability result in that fixed affine space supplies one closed relative ball B_aff(F)(y,beta) contained in their convex hull and hence in the projected whole D(t_n), at every sufficiently large index. This uses reconstruction and a full affine inverse, rather than openness alone. Antipodal chart endpoints in K give the global operator bound R. Original zero symmetry and chart_boundary give the actual unit coordinates.

Write e_n=dist(r_n,y), A_n=proj_U composed with L_n and J_n=ker(A_n). Eventually e_n<beta and the projected ball supplies a radius rho=beta-e_n ball about A_n z_n inside A_n(closedBall(0,1)). Let w be the orthogonal projection of z_n onto J_n perpendicular. For w!=0, move outward from A_n w by rho, take a genuine unit-ball preimage, and use uniqueness of the orthogonal minimum-norm preimage. With norm(A_n)<=R this proves norm(w)<=1-rho/R. The w=0 branch is included. Pythagoras gives the actual finite bound norm(proj_J_n z_n)^2>=1-(1-(beta-e_n)/R)^2.

The projected relative ball gives beta norm(h)<=norm(L_n adjoint h) for every h in U, by testing its two antipodal points and using actual chart preimages. The nearest source point and both chart endpoints give norm(proj_U_perp composed with L_n)<=alpha_n. Native ordered real spectral coordinates and dimension counting then prove beta<=sigma_k(L_n) and sigma_(k+1)(L_n)<=alpha_n at every sufficiently large index. Here source sigma_k is Lean index dim(a)-1, and source sigma_(k+1) is Lean index dim(a). The fixed kept constant s_*=beta is chosen before all sequences and charts.

For v in J_n, L_n v is entirely normal to U, so beta norm(proj_T_n v)<=alpha_n norm(v), where T_n is the span of the first k ordered right singular directions. Apply this to proj_J_n z_n, use orthogonal decomposition and Cauchy-Schwarz, and include the zero-vector branch. This gives norm(proj_J_n z_n)<=norm(proj_W_n z_n)+alpha_n/beta. Combine it with the actual radial kernel margin. Put gamma=1-(1-beta/(2R))^2 and eta=gamma/4>0. Eventually dist(r_n,y)<beta/2 and alpha_n/beta<sqrt(gamma)/2, hence norm(proj_W_n z_n)^2>=eta. The unit bound supplies the upper boundedness needed for the real liminf. Thus liminf sigma_k>=s_*>0 and liminf norm(proj_W_n z_n)^2>=eta>0. No constant-dimension extraction, frame convergence or inference from shrinking physical axes is used. The private real eigenbasis leaf estimates adapt TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9, with original copyright and the existing full Apache license retained. These reusable proof ingredients carry no new-content claim.

No actual pure sequence satisfying the common-sector condition is constructed. These results do not establish local pure-limit density, existence of a common positive lift, an equivalence with fixed-test lifting, a collapse theorem or a full original-domain countermodel. They do not assume or conclude that y lies outside closure(P). Vanishing physical axis lengths alone do not imply vanishing unit-ball parameters. These are conditional mathematical results, without a physical-realization or literature-priority claim.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalReturnSectors.original_return_geometry`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalReturnSectors.projectedLinear`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalReturnSectors.sourceProjection`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalReturnSectors.source_contact_simplex`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalReturnSectors.uniform_return_sectors`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalReturnSectors.whole_return_leakage`
- Dependency: [D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts](OriginalReturnSectors/Contacts.md)
- Dependency: [D5/S3/Quantum/Foundation/OriginalReturnSectors/LinearGeometry](OriginalReturnSectors/LinearGeometry.md)
