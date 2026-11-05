# Douglas factorization on Hilbert spaces

## Abstract

Actual range inclusion, bounded factorization and adjoint norm majorization for arbitrary complete real or complex Hilbert spaces, including a factor with every prescribed admissible norm bound.

The scalar k is any RCLike field. The carriers E and F are normed additive commutative groups with inner products over k and are complete. Their universe levels v and w and the scalar universe u are independent. Map(k,E,F) means ContinuousLinearMap(k,E,F), a bounded continuous k-linear map. Lin(k,E,E) means an algebraic linear endomorphism. Adjoint(T) is the Hilbert adjoint, Comp(B,C) applies C first and then B, and every map norm is the operator norm.

Range(T) is the actual linear range of T and Kernel(T) its kernel; Orthogonal(U) is the orthogonal complement. The relation Range(A) <= Range(B) is actual submodule inclusion. No closure replaces either range in a conclusion. The scalar c is real and can equal zero. No closed-range, finite-dimensional, separable, injective, surjective or nonzero-space hypothesis is imposed.

**Theorem 1.1 (norm_adjoint).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (T: \operatorname{Map}(k, E, F)), \left\lVert \operatorname{Adjoint}(T) \right\rVert = \left\lVert T \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.norm_adjoint` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

The adjoint is an isometry on bounded operators. The factorization estimate and the prescribed-bound construction use this norm identity.

**Theorem 1.2 (eq_of_mem_orthogonal_and_apply).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (B: \operatorname{Map}(k, E, F)), \forall (z1: E), \forall (z2: E), (z1 \in \operatorname{Orthogonal}(\operatorname{Kernel}(B))) \Rightarrow (z2 \in \operatorname{Orthogonal}(\operatorname{Kernel}(B))) \Rightarrow (\operatorname{B}(z1) = \operatorname{B}(z2)) \Rightarrow z1 = z2$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.eq_of_mem_orthogonal_and_apply` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

Two preimages in the orthogonal complement of the kernel with the same image are equal: their difference belongs both to the kernel and its orthogonal complement, so its squared norm vanishes. This supplies additivity, homogeneity and closed-graph uniqueness for the canonical factor.

**Theorem 1.3 (exists_mem_orthogonal_apply).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), (\operatorname{Range}(A) \leq \operatorname{Range}(B)) \Rightarrow \forall (x: E), \exists (z: E), (z \in \operatorname{Orthogonal}(\operatorname{Kernel}(B))) \land (\operatorname{B}(z) = \operatorname{A}(x))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.exists_mem_orthogonal_apply` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

For every x, actual range inclusion supplies a preimage of A x. Projecting it onto the orthogonal complement of the kernel preserves its B-image and produces the required orthogonal preimage.

**Definition 1.4 (douglasFactorFun).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), \forall (h: \operatorname{Range}(A) \leq \operatorname{Range}(B)), \forall (x: E), \operatorname{douglasFactorFun}(A, B, h, x) = \operatorname{ChooseOrthogonalPreimage}(B, \operatorname{A}(x))$$

*Formalization.* `D5/S3/HilbertOperators/DouglasLemma.douglasFactorFun` (`✓ std3`).

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

douglasFactorFun(A,B,h,x) is Classical.choose applied to exists_mem_orthogonal_apply(A,B,h,x). ChooseOrthogonalPreimage denotes that choice of a vector z in Orthogonal(Kernel(B)) with B z = A x; existence follows from h and uniqueness follows from eq_of_mem_orthogonal_and_apply. This is a noncomputable choice definition.

**Theorem 1.5 (douglasFactorFun_spec).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), \forall (h: \operatorname{Range}(A) \leq \operatorname{Range}(B)), \forall (x: E), (\operatorname{douglasFactorFun}(A, B, h, x) \in \operatorname{Orthogonal}(\operatorname{Kernel}(B))) \land (\operatorname{B}(\operatorname{douglasFactorFun}(A, B, h, x)) = \operatorname{A}(x))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.douglasFactorFun_spec` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

The chosen preimage lies in the kernel's orthogonal complement and maps under B to A x. Both conjuncts are used to establish the linear and continuous structure.

**Definition 1.6 (douglasFactorLin).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), \forall (h: \operatorname{Range}(A) \leq \operatorname{Range}(B)), (\operatorname{douglasFactorLin}(A, B, h) \in \operatorname{Lin}(k, E, E)) \land (\forall (x: E), \operatorname{douglasFactorLin}(A, B, h, x) = \operatorname{douglasFactorFun}(A, B, h, x))$$

*Formalization.* `D5/S3/HilbertOperators/DouglasLemma.douglasFactorLin` (`✓ std3`).

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

douglasFactorLin packages the chosen preimage function as a k-linear endomorphism. Addition and scalar multiplication preserve orthogonal membership and the required B-image; uniqueness proves the two linearity laws. The displayed membership specifies the linear-map type together with its underlying function.

**Theorem 1.7 (continuous_douglasFactorLin).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), \forall (h: \operatorname{Range}(A) \leq \operatorname{Range}(B)), \operatorname{Continuous}(\operatorname{douglasFactorLin}(A, B, h))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.continuous_douglasFactorLin` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

The canonical linear factor is continuous by the sequential closed graph theorem. If x_n tends to x and its images tend to z, closedness of the orthogonal complement keeps z there. Continuity of A and B and uniqueness of limits give B z = A x. Orthogonal-preimage uniqueness identifies z with the canonical image of x, closing the graph.

**Definition 1.8 (douglasFactor).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), \forall (h: \operatorname{Range}(A) \leq \operatorname{Range}(B)), (\operatorname{douglasFactor}(A, B, h) \in \operatorname{Map}(k, E, E)) \land (\forall (x: E), \operatorname{douglasFactor}(A, B, h, x) = \operatorname{douglasFactorLin}(A, B, h, x))$$

*Formalization.* `D5/S3/HilbertOperators/DouglasLemma.douglasFactor` (`✓ std3`).

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

douglasFactor is the continuous linear map whose toLinearMap is douglasFactorLin and whose continuity proof is continuous_douglasFactorLin. Thus the canonical orthogonal-preimage construction is a bounded endomorphism E to E.

**Theorem 1.9 (apply_douglasFactor).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), \forall (h: \operatorname{Range}(A) \leq \operatorname{Range}(B)), \forall (x: E), \operatorname{B}(\operatorname{douglasFactor}(A, B, h, x)) = \operatorname{A}(x)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.apply_douglasFactor` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

For each x, applying B to the bounded canonical factor recovers A x.

**Theorem 1.10 (eq_comp_douglasFactor).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), \forall (h: \operatorname{Range}(A) \leq \operatorname{Range}(B)), A = \operatorname{Comp}(B, \operatorname{douglasFactor}(A, B, h))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.eq_comp_douglasFactor` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

Extensionality turns the pointwise preimage identity into equality of bounded operators.

**Theorem 1.11 (range_le_iff_exists_factorization).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), (\operatorname{Range}(A) \leq \operatorname{Range}(B)) \iff (\exists (C: \operatorname{Map}(k, E, E)), A = \operatorname{Comp}(B, C))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.range_le_iff_exists_factorization` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

Actual range inclusion is equivalent to existence of a bounded C from E to E with A = B composed with C. The forward direction uses the continuous canonical factor; the converse uses inclusion of the range of a composition in the range of its outer map.

**Theorem 1.12 (majorization_of_factorization).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), \forall (C: \operatorname{Map}(k, E, E)), (A = \operatorname{Comp}(B, C)) \Rightarrow \forall (y: F), \left\lVert \operatorname{Apply}(\operatorname{Adjoint}(A), y) \right\rVert \leq \left\lVert C \right\rVert \cdot \left\lVert \operatorname{Apply}(\operatorname{Adjoint}(B), y) \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.majorization_of_factorization` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

Any bounded factor C gives the pointwise adjoint estimate with constant norm(C). Adjoint composition reverses the order, the operator-norm bound controls C adjoint, and norm_adjoint replaces its norm by norm(C).

**Theorem 1.13 (exists_factorization_of_majorization).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), \forall (c: \mathbb{R}), (0 \leq c) \Rightarrow (\forall (y: F), \left\lVert \operatorname{Apply}(\operatorname{Adjoint}(A), y) \right\rVert \leq c \cdot \left\lVert \operatorname{Apply}(\operatorname{Adjoint}(B), y) \right\rVert) \Rightarrow \exists (C: \operatorname{Map}(k, E, E)), (A = \operatorname{Comp}(B, C)) \land (\left\lVert C \right\rVert \leq c)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.exists_factorization_of_majorization` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

For every real c >= 0 satisfying the pointwise adjoint bound, a single bounded C realizes both A = B composed with C and norm(C) <= c. Set S to the closure of Range(Adjoint(B)). Restrict Adjoint(B) to the codomain S, obtaining a dense-range linear map e. The estimate allows Adjoint(B)y mapped to Adjoint(A)y to extend to a bounded D from S to E with norm(D) <= c. The factor is the adjoint of D composed with the orthogonal projection from E onto S. Extension equality, projection on S and adjoint composition give the factorization. The projection norm is at most one and adjoints preserve norm, giving the same prescribed bound. Closure is used only for this complete extension domain.

**Theorem 1.14 (majorization_iff_exists_factorization).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), (\exists (c: \mathbb{R}), (0 \leq c) \land (\forall (y: F), \left\lVert \operatorname{Apply}(\operatorname{Adjoint}(A), y) \right\rVert \leq c \cdot \left\lVert \operatorname{Apply}(\operatorname{Adjoint}(B), y) \right\rVert)) \iff (\exists (C: \operatorname{Map}(k, E, E)), A = \operatorname{Comp}(B, C))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.majorization_iff_exists_factorization` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

Existence of a nonnegative real majorization constant is equivalent to bounded factorization. One direction uses the prescribed-bound construction. The other uses norm(C), which is nonnegative. This equivalence retains factor existence; the separate prescribed-bound theorem states the quantitative conclusion for each given c.

**Theorem 1.15 (range_le_iff_majorization).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{InnerProductSpace}(k, F)] [\operatorname{CompleteSpace}(E)] [\operatorname{CompleteSpace}(F)] \forall (A: \operatorname{Map}(k, E, F)), \forall (B: \operatorname{Map}(k, E, F)), (\operatorname{Range}(A) \leq \operatorname{Range}(B)) \iff (\exists (c: \mathbb{R}), (0 \leq c) \land (\forall (y: F), \left\lVert \operatorname{Apply}(\operatorname{Adjoint}(A), y) \right\rVert \leq c \cdot \left\lVert \operatorname{Apply}(\operatorname{Adjoint}(B), y) \right\rVert))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DouglasLemma.range_le_iff_majorization` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Douglas lemma for bounded operators on Hilbert spaces*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/DouglasLemma.lean>.

*Commentary.*

Combining the two factorization equivalences identifies actual range inclusion with existence of a nonnegative real c satisfying the adjoint inequality for every y in F.

These statements cover zero operators and zero-dimensional, infinite-dimensional and nonseparable spaces. They assert neither an optimal-constant attainment formula nor a factorization with three distinct source and target domains, naturality, or a Hilbert C*-module analogue. The construction supplies an existence theorem, without a numerical algorithm or an empirical quantum claim.

The actual Lean supplier is the immutable facebookresearch/atlas-lean DouglasLemma source identified in the literature note. The result is classical Douglas factorization. The readable expositions by Manuilov, Moslehian and Xu and by Nayak give same-space classical statements; the arbitrary two-space RCLike formulation here is attested by the cited Lean source. The source and license attribution are recorded in that note and the Lean header.

## References

- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.apply_douglasFactor`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.continuous_douglasFactorLin`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.douglasFactor`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.douglasFactorFun`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.douglasFactorFun_spec`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.douglasFactorLin`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.eq_comp_douglasFactor`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.eq_of_mem_orthogonal_and_apply`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.exists_factorization_of_majorization`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.exists_mem_orthogonal_apply`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.majorization_iff_exists_factorization`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.majorization_of_factorization`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.norm_adjoint`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.range_le_iff_exists_factorization`
- Truth anchor: `D5/S3/HilbertOperators/DouglasLemma.range_le_iff_majorization`
