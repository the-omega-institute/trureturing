# Singer trace planes and cyclic difference sets

## Abstract

The trace-zero points in the projective plane over a prime field form a cyclic Singer difference set of size p+1. Every nonzero cyclic difference occurs exactly once. Multiplication of indices by two permutes the odd-length cycle, so its inverse image has the same cardinality and difference multiplicities.

**Theorem 1.1 (Multiplication has no proper invariant subspace).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall a : \operatorname{GaloisField}\left(p, 3\right), \forall W : \operatorname{Submodule}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right)\right), (\neg (a \in \operatorname{Set}.\operatorname{range}\left(\operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right)\right)\right))) \Rightarrow ((\forall x : \operatorname{GaloisField}\left(p, 3\right), (x \in W) \Rightarrow (a \cdot x \in W)) \Rightarrow ((W = \operatorname{Bot}.\operatorname{bot}) \lor (W = \operatorname{Top}.\operatorname{top})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/SingerTracePlane.no_proper_invariant_subspace` (`✓ std3`). ∎

*Citation.* James Singer (1938). *A theorem in finite projective geometry and some applications to number theory*. DOI: [10.1090/s0002-9947-1938-1501951-4](https://doi.org/10.1090/s0002-9947-1938-1501951-4). URL: <https://doi.org/10.1090/s0002-9947-1938-1501951-4>.

*Commentary.*

For an element outside the base field, a subspace preserved by multiplication is either zero or the whole cubic extension. The scalars preserving the subspace form a subalgebra; prime extension degree forces a non-base subalgebra to be the whole field.

**Theorem 1.2 (Distinct trace planes meet in a line).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall a : \operatorname{GaloisField}\left(p, 3\right), (\neg (a \in \operatorname{Set}.\operatorname{range}\left(\operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right)\right)\right))) \Rightarrow (\operatorname{Module}.\operatorname{finrank}\left(\operatorname{ZMod}\left(p\right), \operatorname{Subtype}\left((x: \operatorname{GaloisField}\left(p, 3\right)) \mapsto x \in \operatorname{Min}.\operatorname{min}\left((\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right)\right)).\operatorname{ker}, (\operatorname{LinearMap}.\operatorname{comp}\left(\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right)\right), \operatorname{LinearMap}.\operatorname{mulLeft}\left(\operatorname{ZMod}\left(p\right), a\right)\right)).\operatorname{ker}\right)\right)\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/SingerTracePlane.trace_plane_intersection` (`✓ std3`). ∎

*Citation.* James Singer (1938). *A theorem in finite projective geometry and some applications to number theory*. DOI: [10.1090/s0002-9947-1938-1501951-4](https://doi.org/10.1090/s0002-9947-1938-1501951-4). URL: <https://doi.org/10.1090/s0002-9947-1938-1501951-4>.

*Commentary.*

Trace is surjective, so its kernel is a plane. The kernel of x mapped to Tr(a*x) is another plane for nonzero a. If a is outside the base field, equality of these planes would make the trace kernel invariant under multiplication by a. Their sum has dimension three, and their intersection dimension one.

**Theorem 1.3 (The Singer difference-set parameters).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall \alpha : \operatorname{GaloisField}\left(p, 3\right), (\operatorname{orderOf}\left(\alpha\right) = p^{3} - 1) \Rightarrow ((\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((i: \operatorname{Fin}\left(p^{2} + p + 1\right)) \mapsto \operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{\operatorname{val}\left(i\right)}\right) = 0, \operatorname{Finset}.\operatorname{univ}\left(\operatorname{Fin}\left(p^{2} + p + 1\right)\right)\right)\right) = p + 1) \land ((\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((i: \operatorname{Fin}\left(p^{2} + p + 1\right)) \mapsto \operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{2 \cdot \operatorname{val}\left(i\right)}\right) = 0, \operatorname{Finset}.\operatorname{univ}\left(\operatorname{Fin}\left(p^{2} + p + 1\right)\right)\right)\right) = p + 1) \land ((\forall r : \operatorname{Fin}\left(p^{2} + p + 1\right), (r \ne 0) \Rightarrow (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((i: \operatorname{Fin}\left(p^{2} + p + 1\right)) \mapsto (\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{\operatorname{val}\left(i\right)}\right) = 0) \land (\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{\operatorname{val}\left(i + r\right)}\right) = 0), \operatorname{Finset}.\operatorname{univ}\left(\operatorname{Fin}\left(p^{2} + p + 1\right)\right)\right)\right) = 1)) \land ((\forall i : \operatorname{Fin}\left(p^{2} + p + 1\right), (\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{2 \cdot \operatorname{val}\left(i\right)}\right) = 0) \Leftrightarrow (\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{\operatorname{val}\left(2 \cdot i\right)}\right) = 0)) \land (\forall r : \operatorname{Fin}\left(p^{2} + p + 1\right), (r \ne 0) \Rightarrow (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((i: \operatorname{Fin}\left(p^{2} + p + 1\right)) \mapsto (\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{2 \cdot \operatorname{val}\left(i\right)}\right) = 0) \land (\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{2 \cdot \operatorname{val}\left(i + r\right)}\right) = 0), \operatorname{Finset}.\operatorname{univ}\left(\operatorname{Fin}\left(p^{2} + p + 1\right)\right)\right)\right) = 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/SingerTracePlane.result` (`✓ std3`). ∎

*Citation.* James Singer (1938). *A theorem in finite projective geometry and some applications to number theory*. DOI: [10.1090/s0002-9947-1938-1501951-4](https://doi.org/10.1090/s0002-9947-1938-1501951-4). URL: <https://doi.org/10.1090/s0002-9947-1938-1501951-4>.

*Commentary.*

Singer (1938), pages 377-385: trace-zero projective points form the cyclic (p^2+p+1,p+1,1) difference set. Primitive powers enumerate projective points. A nonzero cyclic shift corresponds to a scalar outside the base field; the unique projective point of the trace-plane intersection counts its difference multiplicity. The last two clauses identify the trace-square support with the inverse image under doubling and give the same multiplicities. Subtraction and addition in Fin(p^2+p+1) are cyclic operations; val is the canonical natural representative.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/SingerTracePlane.no_proper_invariant_subspace`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/SingerTracePlane.result`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/SingerTracePlane.trace_plane_intersection`
