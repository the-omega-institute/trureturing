# Embedding a Modular p-Group Representation through Its Invariants

## Abstract

The orbit of a linear retraction turns the modular fixed-vector theorem into an embedding and a sharp dimension bound.

**Theorem 1.1 (The retraction orbit has zero kernel).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/PGroupInvariantEmbedding.exists_injective_linearMap_invariants_rightTranslate`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/PGroupInvariantEmbedding.exists_injective_linearMap_invariants_rightTranslate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Webb (2016). *A Course in Finite Group Representation Theory*. DOI: [10.1017/CBO9781316677216](https://doi.org/10.1017/CBO9781316677216). URL: <https://www-users.cse.umn.edu/~webb/RepBook/RepBookLatex.pdf>.

*Commentary.*

Let p be prime, k any field of characteristic p, P any finite p-group, and rho a k-linear representation of P on V. There exists a k-linear map F from V to the functions P to rho.invariants such that F is injective and F(rho(g)(v))(h) equals F(v)(h times g) for all g, h and v. The field, group and vector space live in independent universes. P may be nonabelian, k may be infinite and need not be algebraically closed, and V has arbitrary dimension, including zero.

Write I for V fixed by P. Submodule.exists_isCompl chooses an ordinary vector-space complement C to I, and Submodule.projectionOnto defines a linear retraction r from V to I along C. Submodule.projectionOnto_apply_left gives r(i) equals i for i in I. No equivariance of r is assumed. LinearMap.pi assembles the orbit of r into F(v)(h) equal to r(rho(h)(v)). This construction does not divide by the order of P.

The representation convention is rho(h times g) equals rho(h) composed with rho(g). Thus F(rho(g)(v))(h) equals r(rho(h)(rho(g)(v))), which equals F(v)(h times g). This is right translation of the argument, with no commutativity hypothesis. If T_g(f)(h) equals f(h times g), then T_g composed with T_a equals T_(g times a), since both send f at h to f((h times g) times a). The stated identity therefore has the orientation of an action on the target.

Build the actual Subrepresentation K of rho whose underlying submodule is the kernel of F. The translation identity proves stability: if F(v) is zero, then for every h, F(rho(g)(v))(h) equals F(v)(h times g), hence is zero. To prove that the kernel is bottom, suppose x is a nonzero vector in it and regard x as a nonzero element of K.toSubmodule. Apply exists_nonzero_mem_invariants_of_isPGroup to K.toRepresentation with this x. It supplies a nonzero y in the kernel that is invariant for the restricted action. Subrepresentation.toRepresentation_apply_coe transports these fixed-vector equations to V, so y lies in I.

Because y lies in the kernel, evaluation of F(y) at the group identity gives r(rho(1)(y)) equals zero, hence r(y) equals zero. Because y lies in I, the retraction identity gives r(y) equals y as an element of I. Taking underlying vectors therefore forces y to be zero in K, contradicting the supplied nonzero invariant. This proves the kernel is bottom, and LinearMap.ker_eq_bot gives injectivity. The argument only invokes the nonzero fixed-vector theorem after assuming a nonzero kernel vector; it needs no nonzero-vector hypothesis on V and covers V equal to zero.

Dimension consequence: if I is finite-dimensional over k, then the finite product of copies of I indexed by P has dimension |P| times dim_k I. The injective map F first implies that V itself is finite-dimensional, and then gives dim_k V at most |P| times dim_k I. Thus finite-dimensional invariants force finite-dimensional V, although no such hypothesis occurs in the embedding theorem. In particular, if I is zero, injectivity forces V to be zero. FiniteDimensional.of_injective and LinearMap.finrank_le_finrank_of_injective give this consequence from F; Module.finrank_pi_fintype computes the target dimension. No additional named specialization is introduced.

Classical sharpness, also prose only: take the left regular representation on k[P], with basis e_a and g acting on e_a as e_(g times a). For z equal to the sum over a of c_a e_a, the coefficient at b of g acting on z is c_(g inverse times b). Invariance therefore implies c_1 equals c_g by taking b equal to g, for every g; conversely constant coefficients satisfy every fixed-vector equation. Hence the invariant space is the one-dimensional span of N equal to the sum over a of e_a. N is nonzero because its coefficient at 1 is 1, even in characteristic p when the augmentation of N, namely |P| in k, can vanish. The regular module has dimension |P|, so equality holds in the dimension bound.

The same regular example makes the orbit map explicit. Choose the retraction r(z) equal to c_1 N; it is a retraction since r(N) equals N. Then F(z)(h) equals c_(h inverse) N. Inversion permutes P, so this F is a linear bijection onto all functions P to kN. Its translation formula reads F(g acting on z)(h) equals c_(g inverse times h inverse) N equals F(z)(h times g). This coefficient calculation confirms both sharpness and the nonabelian multiplication orientation; it is a mathematical derivation in this Scribe source, not a separately checked Lean example.

This is a structural argument, rather than an enumeration, checker, numerical reduction or certified finite instance, so utility is none. The provenance is the present derivation from the invariant-vector theorem and the actual Mathlib complement, projection, product-map and subrepresentation APIs. Webb's existing Library note supports the augmentation-nilpotence input used by that prerequisite; it is not asserted to quote this exact arbitrary-dimensional embedding statement. The mechanism, dimension consequence and regular-representation calculation are classical. No novelty, exhaustive library-absence or independent-consensus claim is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/PGroupInvariantEmbedding.exists_injective_linearMap_invariants_rightTranslate`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/PGroupInvariants](PGroupInvariants.md)
