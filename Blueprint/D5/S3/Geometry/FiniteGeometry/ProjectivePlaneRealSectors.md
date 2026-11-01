# Original-incidence real sectors and centered distances

## Abstract

Complete real incidence sectors and the exact centered-Gram positivity interval of each actual finite projective plane.

Let P and L be the original finite point and line types, with their original membership and a nondegenerate Configuration.ProjectivePlane instance. Put q=order(P,L), v=q^2+q+1 and s=sqrt(q). The existing integer incidence totals and intersection identities give N*N^T=qI+J and N^T*N=qI+J after casting to the reals. They also give N1=(q+1)1 and N^T1=(q+1)1. The order satisfies q>=2; no plane is asserted to exist at an arbitrary prescribed integer q.

**Definition 1.1 (Real order).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.orderR`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.orderR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer order of the original plane, cast to the reals.

**Definition 1.2 (Original incidence matrix).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.incidenceMatrix`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.incidenceMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N has original point rows and original line columns, with N(p,l)=1 precisely when p belongs to l.

**Definition 1.3 (Real incidence).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.toPoints`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.toPoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear map y mapped to N*y on original line coordinates.

**Definition 1.4 (Transposed real incidence).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.toLines`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.toLines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear map x mapped to N^T*x on original point coordinates.

**Definition 1.5 (Zero-sum coordinates).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.zeroSum`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.zeroSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

zeroSum(I) is the submodule of real I-coordinate vectors whose full coordinate sum is zero, including the empty index type.

**Definition 1.6 (Positive incidence singular value).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.rootOrder`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.rootOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

s=sqrt(q)>0 for the actual plane.

**Definition 1.7 (Normalized transposed incidence).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.normalizedToLines`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.normalizedToLines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On original point zero-sum coordinates, x is mapped to N^T*x/s.

**Definition 1.8 (Normalized incidence).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.normalizedToPoints`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.normalizedToPoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On original line zero-sum coordinates, y is mapped to N*y/s.

**Definition 1.9 (Equivalence of the balanced coordinate spaces).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.balancedEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.balancedEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two normalized maps are mutually inverse. Their compositions reduce to q/s^2 times the identity because the all-ones terms vanish on zero-sum vectors.

**Definition 1.10 (Finite coordinate mean).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.mean`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.mean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

mean(x)=card(I)^(-1)*sum_i x(i), with real inverse-zero convention.

**Definition 1.11 (Constant and zero-sum splitting).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.splitConstant`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.splitConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite I with nonzero cardinality, x is identified with its mean and x minus that constant mean. The inverse adds the constant coordinate back.

**Definition 1.12 (Four-sector coordinate equivalence).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S sends ((c,b),(x,y)) to (c+b+x+y, c-b+T(x-y)), where x,y belong to zeroSum(P) and T=N^T/s. This is a linear equivalence onto all original point/line coordinate pairs, with no assumed diagonalization.

**Definition 1.13 (Constant line).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorConstant`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The c coordinate alone gives (c*1,c*1).

**Definition 1.14 (Bipartition line).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorBipartition`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorBipartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The b coordinate alone gives (b*1,-b*1).

**Definition 1.15 (Positive nonconstant sector).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorPlus`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The x coordinate alone gives (x,T*x), for all original point zero-sum vectors x.

**Definition 1.16 (Negative nonconstant sector).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorMinus`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorMinus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The y coordinate alone gives (y,-T*y), for all original point zero-sum vectors y.

**Theorem 1.17 (Complete unique sector coordinates).**

$$\forall P: \operatorname{Type}, \forall L: \operatorname{Type}, [\operatorname{Membership}\left(P, L\right)], [\operatorname{Fintype}\left(P\right)], [\operatorname{Fintype}\left(L\right)], [\operatorname{ProjectivePlane}\left(P, L\right)], \forall z: ((P\to \mathbb{R}) \times (L\to \mathbb{R})), \exists! c: ((\mathbb{R} \times \mathbb{R}) \times (\operatorname{zeroSum}\left(P\right) \times \operatorname{zeroSum}\left(P\right))), \operatorname{sectorEquiv}\left(P, L, c\right) = z$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.existsUnique_sector_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original coordinate pair has exactly one four-sector coordinate vector. The normalized incidence equivalence supplies the inverse on the line zero-sum part; the means supply the two constant coordinates.

**Theorem 1.18 (Exact dimensions of the four sectors).**

$$\forall P: \operatorname{Type}, \forall L: \operatorname{Type}, [\operatorname{Membership}\left(P, L\right)], [\operatorname{Fintype}\left(P\right)], [\operatorname{Fintype}\left(L\right)], [\operatorname{ProjectivePlane}\left(P, L\right)], \operatorname{finrank}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{sectorConstant}\left(P, L\right)\right)\right) = 1 \land \left(\operatorname{finrank}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{sectorBipartition}\left(P, L\right)\right)\right) = 1 \land \left(\operatorname{finrank}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{sectorPlus}\left(P, L\right)\right)\right) = \operatorname{card}\left(P\right) - 1 \land \operatorname{finrank}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{sectorMinus}\left(P, L\right)\right)\right) = \operatorname{card}\left(P\right) - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sector_finranks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimensions of the constant, bipartition, positive and negative sectors are respectively 1, 1, v-1 and v-1. The maps into these sectors are injective. Constant/zero-sum splitting has total dimension v, so its zero-sum factor has dimension v-1.

**Definition 1.19 (Original Euclidean coordinate form).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.vertexDot`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.vertexDot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dot product is the point-coordinate dot product plus the line-coordinate dot product.

**Theorem 1.20 (Orthogonal sector formula).**

$$\forall P: \operatorname{Type}, \forall L: \operatorname{Type}, [\operatorname{Membership}\left(P, L\right)], [\operatorname{Fintype}\left(P\right)], [\operatorname{Fintype}\left(L\right)], [\operatorname{ProjectivePlane}\left(P, L\right)], \forall z: ((\mathbb{R} \times \mathbb{R}) \times (\operatorname{zeroSum}\left(P\right) \times \operatorname{zeroSum}\left(P\right))), \forall w: ((\mathbb{R} \times \mathbb{R}) \times (\operatorname{zeroSum}\left(P\right) \times \operatorname{zeroSum}\left(P\right))), \operatorname{vertexDot}\left(P, L, \operatorname{sectorEquiv}\left(P, L, z\right), \operatorname{sectorEquiv}\left(P, L, w\right)\right) = 2 \cdot \operatorname{card}\left(P\right) \cdot \left(\operatorname{fst}\left(\operatorname{fst}\left(z\right)\right) \cdot \operatorname{fst}\left(\operatorname{fst}\left(w\right)\right) + \operatorname{snd}\left(\operatorname{fst}\left(z\right)\right) \cdot \operatorname{snd}\left(\operatorname{fst}\left(w\right)\right)\right) + 2 \cdot \left(\operatorname{dotProduct}\left(\operatorname{fst}\left(\operatorname{snd}\left(z\right)\right), \operatorname{fst}\left(\operatorname{snd}\left(w\right)\right)\right) + \operatorname{dotProduct}\left(\operatorname{snd}\left(\operatorname{snd}\left(z\right)\right), \operatorname{snd}\left(\operatorname{snd}\left(w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorEquiv_dot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For z=((c,b),(x,y)) and w=((d,e),(u,t)), the dot product of S(z) and S(w) is 2v*(c*d+b*e)+2*(dot(x,u)+dot(y,t)). Thus all four sectors are mutually orthogonal. The normalized incidence equivalence preserves the zero-sum dot product.

**Definition 1.21 (Original incidence adjacency).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.adjacency`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.adjacency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A sends (x,y) to (N*y,N^T*x). Its labels and membership come from the actual plane.

**Definition 1.22 (Uniform vertex centering).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.center`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.center` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H subtracts the average of the point mean and the line mean from both coordinate vectors. The side cardinalities coincide, so this is centering over all 2v original vertices.

**Definition 1.23 (Centered two-distance Gram operator).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.gramAction`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.gramAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real delta, B=delta*H/2+(delta-1)*H*A*H/2.

**Definition 1.24 (Bipartition scalar).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.bipartitionScalar`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.bipartitionScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

beta(delta)=(q+1-q*delta)/2.

**Definition 1.25 (Positive-sector scalar).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.plusScalar`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.plusScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

alpha(delta)=((1+s)*delta-s)/2.

**Definition 1.26 (Negative-sector scalar).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.minusScalar`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.minusScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gamma(delta)=(s+(1-s)*delta)/2.

**Theorem 1.27 (Complete centered-Gram scalar action).**

$$\forall P: \operatorname{Type}, \forall L: \operatorname{Type}, [\operatorname{Membership}\left(P, L\right)], [\operatorname{Fintype}\left(P\right)], [\operatorname{Fintype}\left(L\right)], [\operatorname{ProjectivePlane}\left(P, L\right)], \forall d: \mathbb{R}, \forall z: ((\mathbb{R} \times \mathbb{R}) \times (\operatorname{zeroSum}\left(P\right) \times \operatorname{zeroSum}\left(P\right))), \operatorname{gramAction}\left(P, L, d, \operatorname{sectorEquiv}\left(P, L, z\right)\right) = \operatorname{sectorEquiv}\left(P, L, ((0, \operatorname{bipartitionScalar}\left(P, L, d\right) \cdot \operatorname{snd}\left(\operatorname{fst}\left(z\right)\right)), (\operatorname{plusScalar}\left(P, L, d\right) \cdot \operatorname{fst}\left(\operatorname{snd}\left(z\right)\right), \operatorname{minusScalar}\left(P, L, d\right) \cdot \operatorname{snd}\left(\operatorname{snd}\left(z\right)\right)))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.gramAction_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four scalar actions of B are 0, beta(delta), alpha(delta), gamma(delta), respectively. This equality holds for every real delta, including every singular value of the parameter.

**Theorem 1.28 (Positivity tests every nonconstant sector).**

$$\forall P: \operatorname{Type}, \forall L: \operatorname{Type}, [\operatorname{Membership}\left(P, L\right)], [\operatorname{Fintype}\left(P\right)], [\operatorname{Fintype}\left(L\right)], [\operatorname{ProjectivePlane}\left(P, L\right)], \forall d: \mathbb{R}, (\forall z: ((P\to \mathbb{R}) \times (L\to \mathbb{R})), 0 \le \operatorname{vertexDot}\left(P, L, z, \operatorname{gramAction}\left(P, L, d, z\right)\right)) \Leftrightarrow \left(0 \le \operatorname{bipartitionScalar}\left(P, L, d\right) \land \left(0 \le \operatorname{plusScalar}\left(P, L, d\right) \land 0 \le \operatorname{minusScalar}\left(P, L, d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.gramAction_nonnegative_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gram form is nonnegative on every original coordinate pair exactly when beta, alpha and gamma are all nonnegative. Necessity uses the actual bipartition direction and actual nonzero point zero-sum vectors. Sufficiency uses the complete orthogonal formula, with all coordinate squares nonnegative.

**Theorem 1.29 (Exact positivity interval).**

$$\forall P: \operatorname{Type}, \forall L: \operatorname{Type}, [\operatorname{Membership}\left(P, L\right)], [\operatorname{Fintype}\left(P\right)], [\operatorname{Fintype}\left(L\right)], [\operatorname{ProjectivePlane}\left(P, L\right)], \forall d: \mathbb{R}, (\forall z: ((P\to \mathbb{R}) \times (L\to \mathbb{R})), 0 \le \operatorname{vertexDot}\left(P, L, z, \operatorname{gramAction}\left(P, L, d, z\right)\right)) \Leftrightarrow \left(\frac{\operatorname{rootOrder}\left(P, L\right)}{1 + \operatorname{rootOrder}\left(P, L\right)} \le d \land d \le \frac{\operatorname{orderR}\left(P, L\right) + 1}{\operatorname{orderR}\left(P, L\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.gramAction_nonnegative_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegativity holds exactly for s/(1+s)<=delta<=(q+1)/q. The lower endpoint comes from the positive incidence sector and the upper endpoint from the bipartition sector. The negative incidence scalar is nonnegative throughout this interval.

**Definition 1.30 (Original disjoint vertex coordinates).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.vertexEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.vertexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real function on P+L is identified with its restrictions to the original points and original lines.

**Definition 1.31 (Original block adjacency matrix).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.adjacencyMatrix`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.adjacencyMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix has blocks (0,N;N^T,0).

**Definition 1.32 (Original squared two-distance assignment).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.distanceMatrix`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.distanceMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D=delta*(J-I)+(1-delta)*A. Its diagonal is zero; original incident point-line pairs have squared distance value one, and every other distinct pair has value delta.

**Definition 1.33 (The actual centering matrix).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeringMatrix`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeringMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H=I-card(P+L)^(-1)*J on all original vertices.

**Definition 1.34 (Doubly centered distance matrix).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeredGram`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeredGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B=-H*D*H/2. No positive-semidefinite or rank assumption enters this definition.

**Theorem 1.35 (Matrix and coordinate actions agree).**

$$\forall P: \operatorname{Type}, \forall L: \operatorname{Type}, [\operatorname{Membership}\left(P, L\right)], [\operatorname{Fintype}\left(P\right)], [\operatorname{Fintype}\left(L\right)], [\operatorname{ProjectivePlane}\left(P, L\right)], \forall d: \mathbb{R}, \forall f: (\operatorname{Sum}\left(P, L\right)\to \mathbb{R}), \operatorname{vertexEquiv}\left(P, L, \operatorname{mulVec}\left(\operatorname{centeredGram}\left(P, L, d\right), f\right)\right) = \operatorname{gramAction}\left(P, L, d, \operatorname{vertexEquiv}\left(P, L, f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeredGram_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the original coordinate identification, the actual doubly centered matrix acts exactly as gramAction. The all-ones term is killed by centering, and H is idempotent.

**Theorem 1.36 (Exact PSD interval for the original matrix).**

$$\forall P: \operatorname{Type}, \forall L: \operatorname{Type}, [\operatorname{Membership}\left(P, L\right)], [\operatorname{Fintype}\left(P\right)], [\operatorname{Fintype}\left(L\right)], [\operatorname{ProjectivePlane}\left(P, L\right)], \forall d: \mathbb{R}, \operatorname{PosSemidef}\left(\operatorname{centeredGram}\left(P, L, d\right)\right) \Leftrightarrow \left(\frac{\operatorname{rootOrder}\left(P, L\right)}{1 + \operatorname{rootOrder}\left(P, L\right)} \le d \land d \le \frac{\operatorname{orderR}\left(P, L\right) + 1}{\operatorname{orderR}\left(P, L\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeredGram_posSemidef_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real matrix -H*D*H/2 is positive semidefinite exactly on the stated closed interval. This result concerns the centered matrix. Exact Euclidean realization, sharp matrix rank and minimum ambient dimension require the corresponding reconstruction and rank statements; no plane existence or finite-field embedding into the reals follows from this criterion.

This is the classical real symmetric-design incidence decomposition applied to the original projective-plane labels. It does not assume the spectrum as input. Equal coordinate values and singular scalar actions remain in scope. General Euclidean distance reconstruction is the Schoenberg theory discussed in Dokmanic, Parhizkar, Ranieri and Vetterli, Euclidean Distance Matrices: Essential Theory, Algorithms and Applications, section II; the present incidence calculation supplies its specific matrix-positivity condition.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.adjacency`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.adjacencyMatrix`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.balancedEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.bipartitionScalar`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.center`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeredGram`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeredGram_action`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeredGram_posSemidef_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.centeringMatrix`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.distanceMatrix`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.existsUnique_sector_coordinates`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.gramAction`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.gramAction_nonnegative_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.gramAction_nonnegative_interval`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.gramAction_sector`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.incidenceMatrix`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.mean`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.minusScalar`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.normalizedToLines`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.normalizedToPoints`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.orderR`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.plusScalar`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.rootOrder`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorBipartition`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorConstant`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorEquiv_dot`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorMinus`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sectorPlus`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.sector_finranks`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.splitConstant`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.toLines`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.toPoints`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.vertexDot`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.vertexEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.zeroSum`
- Dependency: [D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice](ProjectivePlaneIntegerLattice.md)
