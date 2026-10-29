# Canonical two-cut occupation sewing

## Abstract

Literal two-cut occupation control for canonical lattice coefficients.

**Definition 1.1 (Two unrestricted occupations).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.Occ`

*Formalization.* `D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.Occ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each occupation is an arbitrary finitely supported natural function on Fin D.rank times Nat. Its energy weights the coordinate (i,k) by k+1; its degree counts occupation multiplicities.

For buffers A and T at least one, the finite overlap M(d,e) sums binomial(e,u) T^degree(e-u) factorialEnvelope A(d-u) over all u below both d and e. The factorial envelope is the original product of (A/(k+1)) to each multiplicity, divided by the product of multiplicity factorials. No frequency factor is inserted into the factorial coordinate metric.

The original ground-field input recurrence and Pascal's identity prove norm(wordCoeff [] m d e) <= M(d,e), uniformly in both occupations and every signed mode. The buffers bound norm(a(i)) and norm(bilinear a (unitCharge i)). Removing an occupied output coordinate x costs at most (x.2+1)d(x)/A; removing an occupied input coordinate costs at most 1/T. These comparisons keep their support conditions.

Let N(d,e)=1+level(d)+level(e). For every finite descendant word omega and every signed mode, the literal coefficient is bounded by C(omega) N(d,e)^R(omega) M(d,e). Here R is the sum of k+1 over the insertions (i,k), C([])=1, and inserting (i,k) multiplies C by A inverse plus norm(bilinear (unitCharge i) b) plus ((k+1)^k divided by T) times the sum over a of norm(G(i,a)). The constants are independent of both occupations and the mode. The two branches of the actual normal-product recurrence close this induction by their frequency-weighted occupation moments.

CanonicalTwoCutScalar uses this estimate before any grouping of the two internal occupations. The fields, translation factors and factorial coordinates are those of the imported lattice construction. The background is the lattice-field and normal-product calculus of Bakalov--Kac, Matsuo--Nagatomo and Carnahan used by the suppliers; no literature novelty, invariant BPZ form, physical unitarity, operator sewing or complete CFT is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation.Occ`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner](../Sectors/LatticeSectorIntertwiner.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/CanonicalOccupation](CanonicalOccupation.md)
