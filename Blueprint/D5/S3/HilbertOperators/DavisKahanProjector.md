# Common-gap stability of orthogonal projectors

## Abstract

Coercive Sylvester estimates and the common-gap Davis--Kahan projector bound over arbitrary complete real or complex Hilbert spaces.

The scalar k has an RCLike structure, including the real and complex fields. ContinuousLinearMap(k,E,F) denotes bounded continuous k-linear maps from E to F; LinearMap(k,E,F) denotes algebraic k-linear maps. Every norm of a continuous linear map is its operator norm; vector norms are the given Hilbert norms. Inner products use the displayed scalar k, and re takes their real part. All displayed variables and typeclass assumptions are quantified.

For a projectable submodule U, P(U) denotes U.starProjection, the orthogonal projector regarded as a bounded endomorphism of the ambient space. Orthogonal(U) is U's orthogonal complement. Comp denotes continuous-linear-map composition and agrees with multiplication of endomorphisms; the numeral one denotes the identity endomorphism. Real scalars in k-linear expressions use the canonical RCLike real embedding.

The full projector theorem allows arbitrary dimension, including zero-dimensional and infinite-dimensional ambient spaces, and zero, whole, or coincident subspaces. It assumes no equal-rank, finite-rank, simple-eigenvalue, operator-positivity, nonzero-subspace, or small-perturbation condition. The four quadratic-form bounds use the same real c and positive gap g. These are conditional form estimates; no spectral-measure or spectral-support conversion is asserted.

**Theorem 1.1 (norm_le_of_abs_re_inner_map_self_le).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(k, E)] \forall (C: \operatorname{ContinuousLinearMap}(k, E, E)), \forall (q: \mathbb{R}), ((\operatorname{IsSymmetric}(C)) \land (0 \leq q) \land (\forall (x: E), \left|\operatorname{re}(\langle C(x), x \rangle_{k})\right| \leq (q) \cdot (\left\lVert x \right\rVert^{2}))) \Rightarrow \left\lVert C \right\rVert \leq q$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DavisKahanProjector.norm_le_of_abs_re_inner_map_self_le` (`✓ std3`). ∎

*Citation.* Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5 (2026). *Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean>.

*Commentary.*

TauCeti.ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le bounds a symmetric operator by its real quadratic form. Completeness is absent. The private correction-operator estimate norm_opNorm_smul_one_sub_le uses it in the Sylvester absorption argument.

**Theorem 1.2 (le_div_of_comp_add_comp_eq_rectangular).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, F)] \forall (A: \operatorname{ContinuousLinearMap}(k, F, F)), \forall (B: \operatorname{ContinuousLinearMap}(k, E, E)), \forall (X: \operatorname{ContinuousLinearMap}(k, E, F)), \forall (Y: \operatorname{ContinuousLinearMap}(k, E, F)), \forall (N: (\operatorname{ContinuousLinearMap}(k, E, F)) \to \mathbb{R}), \forall (d: \mathbb{R}), (((\forall (f: \operatorname{ContinuousLinearMap}(k, E, F)), \forall (h: \operatorname{ContinuousLinearMap}(k, E, F)), N(f + h) \leq N(f) + N(h)) \land (\forall (a: k), \forall (f: \operatorname{ContinuousLinearMap}(k, E, F)), N((a) \cdot (f)) = (\left\lVert a \right\rVert) \cdot (N(f))) \land (\forall (C: \operatorname{ContinuousLinearMap}(k, F, F)), \forall (f: \operatorname{ContinuousLinearMap}(k, E, F)), N((C) \circ (f)) \leq (\left\lVert C \right\rVert) \cdot (N(f))) \land (\forall (f: \operatorname{ContinuousLinearMap}(k, E, F)), \forall (C: \operatorname{ContinuousLinearMap}(k, E, E)), N((f) \circ (C)) \leq (N(f)) \cdot (\left\lVert C \right\rVert))) \land (\operatorname{IsSymmetric}(A)) \land (\operatorname{IsSymmetric}(B)) \land (0 < d) \land (\forall (x: F), (d) \cdot (\left\lVert x \right\rVert^{2}) \leq \operatorname{re}(\langle A(x), x \rangle_{k})) \land (\forall (x: E), (d) \cdot (\left\lVert x \right\rVert^{2}) \leq \operatorname{re}(\langle B(x), x \rangle_{k})) \land ((A) \circ (X) + (X) \circ (B) = Y)) \Rightarrow N(X) \leq \frac{N(Y)}{(2) \cdot (d)}$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DavisKahanProjector.le_div_of_comp_add_comp_eq_rectangular` (`✓ std3`). ∎

*Citation.* Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5 (2026). *Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean>.

*Commentary.*

TauCeti.ContinuousLinearMap.le_div_of_comp_add_comp_eq_rectangular bounds an arbitrary rectangular solution of A composed with X plus X composed with B equals Y. The real-valued functional N is subadditive, exactly homogeneous in the scalar norm, and bounded under left and right multiplication by the operator norm. No definiteness, completeness, equal carrier, or nonzero-solution assumption is imposed. The zero solution is treated separately. Correction operators yield absorption by twice the positive coercivity delta.

**Theorem 1.3 (le_div_of_comp_sub_comp_eq_rectangular).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, F)] \forall (A: \operatorname{ContinuousLinearMap}(k, F, F)), \forall (B: \operatorname{ContinuousLinearMap}(k, E, E)), \forall (X: \operatorname{ContinuousLinearMap}(k, E, F)), \forall (Y: \operatorname{ContinuousLinearMap}(k, E, F)), \forall (N: (\operatorname{ContinuousLinearMap}(k, E, F)) \to \mathbb{R}), \forall (c: \mathbb{R}), \forall (g: \mathbb{R}), (((\forall (f: \operatorname{ContinuousLinearMap}(k, E, F)), \forall (h: \operatorname{ContinuousLinearMap}(k, E, F)), N(f + h) \leq N(f) + N(h)) \land (\forall (a: k), \forall (f: \operatorname{ContinuousLinearMap}(k, E, F)), N((a) \cdot (f)) = (\left\lVert a \right\rVert) \cdot (N(f))) \land (\forall (C: \operatorname{ContinuousLinearMap}(k, F, F)), \forall (f: \operatorname{ContinuousLinearMap}(k, E, F)), N((C) \circ (f)) \leq (\left\lVert C \right\rVert) \cdot (N(f))) \land (\forall (f: \operatorname{ContinuousLinearMap}(k, E, F)), \forall (C: \operatorname{ContinuousLinearMap}(k, E, E)), N((f) \circ (C)) \leq (N(f)) \cdot (\left\lVert C \right\rVert))) \land (\operatorname{IsSymmetric}(A)) \land (\operatorname{IsSymmetric}(B)) \land (0 < g) \land (\forall (x: F), (c + g) \cdot (\left\lVert x \right\rVert^{2}) \leq \operatorname{re}(\langle A(x), x \rangle_{k})) \land (\forall (x: E), \operatorname{re}(\langle B(x), x \rangle_{k}) \leq (c) \cdot (\left\lVert x \right\rVert^{2})) \land ((A) \circ (X) - (X) \circ (B) = Y)) \Rightarrow N(X) \leq \frac{N(Y)}{g}$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DavisKahanProjector.le_div_of_comp_sub_comp_eq_rectangular` (`✓ std3`). ∎

*Citation.* Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5 (2026). *Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean>.

*Commentary.*

TauCeti.ContinuousLinearMap.le_div_of_comp_sub_comp_eq_rectangular applies the preceding estimate after shifting at the midpoint c plus g divided by two. The upper bound for B is c and the lower bound for A is c plus g. All four assumptions on the rectangular functional N remain explicit.

**Theorem 1.4 (opNorm_le_div_of_comp_sub_comp_eq).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (w: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), \forall (F: \operatorname{Type}_{w}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(k, F)] \forall (A: \operatorname{ContinuousLinearMap}(k, E, E)), \forall (B: \operatorname{ContinuousLinearMap}(k, F, F)), \forall (X: \operatorname{ContinuousLinearMap}(k, F, E)), \forall (Y: \operatorname{ContinuousLinearMap}(k, F, E)), \forall (c: \mathbb{R}), \forall (g: \mathbb{R}), ((\operatorname{IsSymmetric}(A)) \land (\operatorname{IsSymmetric}(B)) \land (0 < g) \land (\forall (x: E), (c + g) \cdot (\left\lVert x \right\rVert^{2}) \leq \operatorname{re}(\langle A(x), x \rangle_{k})) \land (\forall (x: F), \operatorname{re}(\langle B(x), x \rangle_{k}) \leq (c) \cdot (\left\lVert x \right\rVert^{2})) \land ((A) \circ (X) - (X) \circ (B) = Y)) \Rightarrow \left\lVert X \right\rVert \leq \frac{\left\lVert Y \right\rVert}{g}$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DavisKahanProjector.opNorm_le_div_of_comp_sub_comp_eq` (`✓ std3`). ∎

*Citation.* Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5 (2026). *Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean>.

*Commentary.*

TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq specializes the separated rectangular estimate to the operator norm. The source and target are independently quantified normed inner-product spaces over the same k, without completeness assumptions.

**Theorem 1.5 (re_inner_reducedExtension_self).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(k, E)] \forall (R: \operatorname{LinearMap}(k, E, E)), \forall (W: \operatorname{Submodule}(k, E)), [\operatorname{HasOrthogonalProjection}(W)] \forall (q: \mathbb{R}), \forall (x: E), (\forall (x: E), (x \in W) \Rightarrow R(x) \in W) \Rightarrow \operatorname{re}(\langle R(\operatorname{P}(W)(x)) + (\operatorname{ofReal}(q)) \cdot (x - \operatorname{P}(W)(x)), x \rangle_{k}) = \operatorname{re}(\langle R(\operatorname{P}(W)(x)), \operatorname{P}(W)(x) \rangle_{k}) + (q) \cdot (\left\lVert x - \operatorname{P}(W)(x) \right\rVert^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DavisKahanProjector.re_inner_reducedExtension_self` (`✓ std3`). ∎

*Citation.* Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5 (2026). *Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean>.

*Commentary.*

TauCeti.re_inner_reducedExtension_self splits the real quadratic form of a linear map on a projectable invariant subspace and a scalar action on its orthogonal complement. The map R is algebraic, need not be bounded or symmetric, and needs invariance only on W. The private bounded-map version re_inner_bounded_reducedExtension_self applies this identity to the reduced extensions in Submodule.sinTheta_directed_coercive.

**Theorem 1.6 (norm_add_eq_max_of_block).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{CompleteSpace}(E)] \forall (P: \operatorname{ContinuousLinearMap}(k, E, E)), \forall (A: \operatorname{ContinuousLinearMap}(k, E, E)), \forall (B: \operatorname{ContinuousLinearMap}(k, E, E)), ((\operatorname{IsSelfAdjoint}(P)) \land (\operatorname{IsIdempotentElem}(P)) \land (\forall (x: E), \left\lVert P(x) \right\rVert \leq \left\lVert x \right\rVert) \land (\forall (x: E), \left\lVert (1 - P)(x) \right\rVert \leq \left\lVert x \right\rVert) \land ((A) \circ (P) = A) \land ((P) \circ (A) = A) \land ((B) \circ (P) = 0) \land ((P) \circ (B) = 0)) \Rightarrow \left\lVert A + B \right\rVert = \operatorname{max}(\left\lVert A \right\rVert, \left\lVert B \right\rVert)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DavisKahanProjector.norm_add_eq_max_of_block` (`✓ std3`). ∎

*Citation.* Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5 (2026). *Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean>.

*Commentary.*

ContinuousLinearMap.norm_add_eq_max_of_block gives the exact maximum of the norms of two complementary supported blocks. Its hypotheses include self-adjointness, idempotence, contraction of P and one minus P, and all four left/right support equations. The Pythagorean split controls the upper bound and the support equations recover both lower bounds.

**Theorem 1.7 (norm_starProjection_sub_eq_max).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{CompleteSpace}(E)] \forall (U: \operatorname{Submodule}(k, E)), \forall (V: \operatorname{Submodule}(k, E)), [\operatorname{HasOrthogonalProjection}(U)] [\operatorname{HasOrthogonalProjection}(V)] \left\lVert \operatorname{P}(U) - \operatorname{P}(V) \right\rVert = \operatorname{max}(\left\lVert (1 - \operatorname{P}(V)) \circ (\operatorname{P}(U)) \right\rVert, \left\lVert (1 - \operatorname{P}(U)) \circ (\operatorname{P}(V)) \right\rVert)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DavisKahanProjector.norm_starProjection_sub_eq_max` (`✓ std3`). ∎

*Citation.* Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5 (2026). *Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean>.

*Commentary.*

Submodule.norm_starProjection_sub_eq_max expresses the symmetric projector distance as the maximum of its two directed cross-projection norms. It uses ContinuousLinearMap.norm_add_eq_max_of_block and the C-star norm identities. It requires no rank or nonzero-subspace restriction.

**Theorem 1.8 (sinTheta_directed_coercive).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (E: \operatorname{Type}_{v}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(k, E)] [\operatorname{CompleteSpace}(E)] \forall (A: \operatorname{ContinuousLinearMap}(k, E, E)), \forall (B: \operatorname{ContinuousLinearMap}(k, E, E)), \forall (U: \operatorname{Submodule}(k, E)), \forall (V: \operatorname{Submodule}(k, E)), [\operatorname{HasOrthogonalProjection}(U)] [\operatorname{HasOrthogonalProjection}(V)] \forall (c: \mathbb{R}), \forall (g: \mathbb{R}), ((\operatorname{IsSymmetric}(A)) \land (\operatorname{IsSymmetric}(B)) \land ((\forall (x: E), (x \in U) \Rightarrow A(x) \in U) \land (\forall (x: E), (x \in \operatorname{Orthogonal}(U)) \Rightarrow A(x) \in \operatorname{Orthogonal}(U))) \land ((\forall (x: E), (x \in V) \Rightarrow B(x) \in V) \land (\forall (x: E), (x \in \operatorname{Orthogonal}(V)) \Rightarrow B(x) \in \operatorname{Orthogonal}(V))) \land (0 < g) \land (\forall (x: E), (x \in U) \Rightarrow (c + g) \cdot (\left\lVert x \right\rVert^{2}) \leq \operatorname{re}(\langle A(x), x \rangle_{k})) \land (\forall (x: E), (x \in V) \Rightarrow \operatorname{re}(\langle B(x), x \rangle_{k}) \leq (c) \cdot (\left\lVert x \right\rVert^{2}))) \Rightarrow \left\lVert (\operatorname{P}(V)) \circ (\operatorname{P}(U)) \right\rVert \leq \frac{\left\lVert B - A \right\rVert}{g}$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DavisKahanProjector.sinTheta_directed_coercive` (`✓ std3`). ∎

*Citation.* Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5 (2026). *Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean>.

*Commentary.*

Submodule.sinTheta_directed_coercive forms reduced extensions on U and V. The two operators preserve their respective subspaces and orthogonal complements. Projection commutation gives a Sylvester equation for the cross projection, and perturbation compression bounds its forcing term by the norm of B minus A. Only the lower form bound on U and the upper form bound on V are required here.

**Theorem 1.9 (opNorm_starProjection_sub_le_of_coercive).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (H: \operatorname{Type}_{v}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(k, H)] [\operatorname{CompleteSpace}(H)] \forall (A: \operatorname{ContinuousLinearMap}(k, H, H)), \forall (B: \operatorname{ContinuousLinearMap}(k, H, H)), \forall (U: \operatorname{Submodule}(k, H)), \forall (W: \operatorname{Submodule}(k, H)), [\operatorname{HasOrthogonalProjection}(U)] [\operatorname{HasOrthogonalProjection}(W)] \forall (c: \mathbb{R}), \forall (g: \mathbb{R}), ((\operatorname{IsSymmetric}(A)) \land (\operatorname{IsSymmetric}(B)) \land ((\forall (x: H), (x \in U) \Rightarrow A(x) \in U) \land (\forall (x: H), (x \in \operatorname{Orthogonal}(U)) \Rightarrow A(x) \in \operatorname{Orthogonal}(U))) \land ((\forall (x: H), (x \in W) \Rightarrow B(x) \in W) \land (\forall (x: H), (x \in \operatorname{Orthogonal}(W)) \Rightarrow B(x) \in \operatorname{Orthogonal}(W))) \land (0 < g) \land (\forall (x: H), (x \in U) \Rightarrow (c + g) \cdot (\left\lVert x \right\rVert^{2}) \leq \operatorname{re}(\langle A(x), x \rangle_{k})) \land (\forall (x: H), (x \in \operatorname{Orthogonal}(U)) \Rightarrow \operatorname{re}(\langle A(x), x \rangle_{k}) \leq (c) \cdot (\left\lVert x \right\rVert^{2})) \land (\forall (x: H), (x \in W) \Rightarrow (c + g) \cdot (\left\lVert x \right\rVert^{2}) \leq \operatorname{re}(\langle B(x), x \rangle_{k})) \land (\forall (x: H), (x \in \operatorname{Orthogonal}(W)) \Rightarrow \operatorname{re}(\langle B(x), x \rangle_{k}) \leq (c) \cdot (\left\lVert x \right\rVert^{2}))) \Rightarrow \left\lVert \operatorname{P}(U) - \operatorname{P}(W) \right\rVert \leq \frac{\left\lVert B - A \right\rVert}{g}$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/DavisKahanProjector.opNorm_starProjection_sub_le_of_coercive` (`✓ std3`). ∎

*Citation.* Jon Crall, GPT 5.6 High, Claude Fable 5, and Claude Opus 5 (2026). *Coercive Sylvester estimates and common-gap Davis--Kahan projector bounds*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean>.

*Commentary.*

Submodule.opNorm_starProjection_sub_le_of_coercive is the common-gap projector theorem. Apply Submodule.sinTheta_directed_coercive to U and the orthogonal complement of W, then to W and the orthogonal complement of U, and combine the two estimates with Submodule.norm_starProjection_sub_eq_max. The constant is one, with denominator g.

## References

- Truth anchor: `D5/S3/HilbertOperators/DavisKahanProjector.le_div_of_comp_add_comp_eq_rectangular`
- Truth anchor: `D5/S3/HilbertOperators/DavisKahanProjector.le_div_of_comp_sub_comp_eq_rectangular`
- Truth anchor: `D5/S3/HilbertOperators/DavisKahanProjector.norm_add_eq_max_of_block`
- Truth anchor: `D5/S3/HilbertOperators/DavisKahanProjector.norm_le_of_abs_re_inner_map_self_le`
- Truth anchor: `D5/S3/HilbertOperators/DavisKahanProjector.norm_starProjection_sub_eq_max`
- Truth anchor: `D5/S3/HilbertOperators/DavisKahanProjector.opNorm_le_div_of_comp_sub_comp_eq`
- Truth anchor: `D5/S3/HilbertOperators/DavisKahanProjector.opNorm_starProjection_sub_le_of_coercive`
- Truth anchor: `D5/S3/HilbertOperators/DavisKahanProjector.re_inner_reducedExtension_self`
- Truth anchor: `D5/S3/HilbertOperators/DavisKahanProjector.sinTheta_directed_coercive`
