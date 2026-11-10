# Simultaneous operator approximation

## Abstract

Simultaneous operator approximation

Every operator x in the bicommutant of a unital star subalgebra S can be approximated on any finite family of vectors: for every positive epsilon, some s in S has norm(x(v)-s(v)) less than epsilon on each vector. The one-vector case uses the projection onto the closed orbit subspace. Finite diagonal amplification yields simultaneous approximation.

**Theorem 1.1 (piLpEntry_apply).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} \{\iota : Type u_3\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [DecidableEq.\{u_3 + 1\} \iota ] (T : ContinuousLinearMap.\{u_1, u_1, max u_2 u_3, max u_2 u_3\} (RingHom.id.\{u_1\} K ) (PiLp.\{u_3, u_2\} 2 fun (x : \iota ) \mapsto H) (PiLp.\{u_3, u_2\} 2 fun (x : \iota ) \mapsto H)) (i j : \iota ) (h : H), Eq.\{u_2 + 1\} ((ContinuousLinearMap.piLpEntry.\{u_1, u_2, u_3\} T i j) h) (WithLp.ofLp.\{max u_3 u_2\} (T (PiLp.single.\{u_3, u_2\} 2 j h)) i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.piLpEntry_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The definition piLpEntry composes the single-coordinate inclusion, T, and the coordinate projection. Evaluating this composition gives the i-th coordinate of T applied to the vector supported at j; piLpEntry_apply is consequently definitional.

**Theorem 1.2 (apply_eq_sum_piLpEntry).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} \{\iota : Type u_3\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [DecidableEq.\{u_3 + 1\} \iota ] [Fintype.\{u_3\} \iota ] (T : ContinuousLinearMap.\{u_1, u_1, max u_2 u_3, max u_2 u_3\} (RingHom.id.\{u_1\} K ) (PiLp.\{u_3, u_2\} 2 fun (x : \iota ) \mapsto H) (PiLp.\{u_3, u_2\} 2 fun (x : \iota ) \mapsto H)) (w : PiLp.\{u_3, u_2\} 2 fun (x : \iota ) \mapsto H) (i : \iota ), Eq.\{u_2 + 1\} (WithLp.ofLp.\{max u_3 u_2\} (T w) i) (\sum j : \iota , (ContinuousLinearMap.piLpEntry.\{u_1, u_2, u_3\} T i j) (WithLp.ofLp.\{max u_3 u_2\} w j))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.apply_eq_sum_piLpEntry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decompose w into the finite sum of its single-coordinate vectors. Continuous linearity moves T through this sum, and piLpEntry_apply identifies each resulting i-th component with the corresponding matrix entry applied to w(j).

**Theorem 1.3 (diagStarAlgHom_apply).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} \{\iota : Type u_3\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [Fintype.\{u_3\} \iota ] [CompleteSpace.\{u_2\} H] (s : ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H) (w : PiLp.\{u_3, u_2\} 2 fun (x : \iota ) \mapsto H) (i : \iota ), Eq.\{u_2 + 1\} (WithLp.ofLp.\{max u_3 u_2\} (((PiLp.diagStarAlgHom.\{u_1, u_2, u_3\} K H \iota ) s) w) i) (s (WithLp.ofLp.\{max u_3 u_2\} w i))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.diagStarAlgHom_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

diagStarAlgHom conjugates the coordinatewise operator by PiLp.continuousLinearEquiv. Evaluating at coordinate i cancels the change of presentation and leaves s applied to w(i), so the formula follows directly from the definition.

**Theorem 1.4 (diagStarAlgHom_apply_single).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} \{\iota : Type u_3\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [Fintype.\{u_3\} \iota ] [CompleteSpace.\{u_2\} H] [DecidableEq.\{u_3 + 1\} \iota ] (s : ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H) (j : \iota ) (h : H), Eq.\{max (u_2 + 1) (u_3 + 1)\} (((PiLp.diagStarAlgHom.\{u_1, u_2, u_3\} K H \iota ) s) (PiLp.single.\{u_3, u_2\} 2 j h)) (PiLp.single.\{u_3, u_2\} 2 j (s h))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.diagStarAlgHom_apply_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use diagStarAlgHom_apply coordinatewise. At coordinate j the single vector evaluates to h, giving s(h); at every other coordinate it evaluates to zero and s maps zero to zero. Extensionality identifies the resulting vector with the single vector at j.

**Theorem 1.5 (isReducing_iff).**

$$\forall \{K : Type u_1\} \{E : Type u_2\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} E] [InnerProductSpace.\{u_1, u_2\} K E] (U : Submodule.\{u_1, u_2\} K E) (A : Module.End.\{u_1, u_2\} K E), Submodule.IsReducing.\{u_1, u_2\} U A \iff Membership.mem.\{u_2, u_2\} (Module.End.invtSubmodule.\{u_1, u_2\} A) U \land Membership.mem.\{u_2, u_2\} (Module.End.invtSubmodule.\{u_1, u_2\} A) (Submodule.orthogonal.\{u_1, u_2\} U)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.isReducing_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

IsReducing is defined as invariance of U together with invariance of its orthogonal complement. Unfolding that definition gives the equivalence; it introduces no completeness or existence-of-projection assumption.

**Theorem 1.6 (isReducing_coe_iff_commute_starProjection).**

$$\forall \{K : Type u_1\} \{E : Type u_2\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} E] [InnerProductSpace.\{u_1, u_2\} K E] \{U : Submodule.\{u_1, u_2\} K E\} [Submodule.HasOrthogonalProjection.\{u_1, u_2\} U] \{A : ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) E E\}, Submodule.IsReducing.\{u_1, u_2\} U \operatorname{coe} A \iff Commute.\{u_2\} (Submodule.starProjection.\{u_1, u_2\} U) A$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.isReducing_coe_iff_commute_starProjection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply ContinuousLinearMap.IsIdempotentElem.commute_iff to the orthogonal projection, using isIdempotentElem_starProjection. Its range is U and its kernel is the orthogonal complement by range_starProjection and ker_starProjection, so the two invariant-subspace conditions become isReducing_iff.

**Theorem 1.7 (isReducing_iff_mem_invtSubmodule_adjoint).**

$$\forall \{K : Type u_1\} \{E : Type u_2\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} E] [InnerProductSpace.\{u_1, u_2\} K E] \{U : Submodule.\{u_1, u_2\} K E\} [CompleteSpace.\{u_2\} E] [Submodule.HasOrthogonalProjection.\{u_1, u_2\} U] \{A : ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) E E\}, Submodule.IsReducing.\{u_1, u_2\} U \operatorname{coe} A \iff Membership.mem.\{u_2, u_2\} (Module.End.invtSubmodule.\{u_1, u_2\} \operatorname{coe} A) U \land Membership.mem.\{u_2, u_2\} (Module.End.invtSubmodule.\{u_1, u_2\} \operatorname{coe} (ContinuousLinearMap.adjoint.\{u_1, u_2, u_2\} A)) U$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.isReducing_iff_mem_invtSubmodule_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand isReducing_iff. The standard relation mem_invtSubmodule_adjoint_iff identifies invariance of the orthogonal complement under A with invariance of U under its adjoint. Rewriting gives the stated pair of invariance conditions under the given projection and completeness assumptions.

**Theorem 1.8 (continuous_ofPointwiseConvergenceCLM).**

$$\forall \{K 1 : Type u_1\} \{K 2 : Type u_2\} \{E : Type u_3\} \{F : Type u_4\} [NormedField.\{u_1\} K 1 ] [NormedField.\{u_2\} K 2 ] \{\sigma : RingHom.\{u_1, u_2\} K 1 K 2 \} [AddCommGroup.\{u_3\} E] [TopologicalSpace.\{u_3\} E] [Module.\{u_1, u_3\} K 1 E] [AddCommGroup.\{u_4\} F] [TopologicalSpace.\{u_4\} F] [IsTopologicalAddGroup.\{u_4\} F] [Module.\{u_2, u_4\} K 2 F] [ContinuousConstSMul.\{u_2, u_4\} K 2 F], Continuous.\{max u_3 u_4, max u_4 u_3\} fun (T : PointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} \sigma E F) \mapsto ContinuousLinearMapWOT.ofCLM.\{u_1, u_2, u_3, u_4\} T$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.continuous_ofPointwiseConvergenceCLM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use continuous_of_dual_apply_continuous for the weak operator topology. Each test coefficient is a continuous functional y applied to evaluation at x; continuous_eval_const supplies pointwise continuity and composition with y.continuous gives the required continuity of every test.

**Theorem 1.9 (isClosed_image_ofCLM_centralizer).**

$$\forall \{K : Type u_1\} \{E : Type u_2\} [NormedField.\{u_1\} K ] [AddCommGroup.\{u_2\} E] [TopologicalSpace.\{u_2\} E] [IsTopologicalAddGroup.\{u_2\} E] [Module.\{u_1, u_2\} K E] [ContinuousConstSMul.\{u_1, u_2\} K E] [SeparatingDual.\{u_1, u_2\} K E] (s : Set.\{u_2\} (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) E E)), IsClosed.\{u_2\} (Set.image.\{u_2, u_2\} ContinuousLinearMapWOT.ofCLM.\{u_1, u_1, u_2, u_2\} (Set.centralizer.\{u_2\} s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.isClosed_image_ofCLM_centralizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ContinuousLinearMapWOT.ofCLM is bijective and preserves multiplication, so its image of a centralizer is the centralizer of the image. The identity follows by testing commutation elementwise with mem_centralizer_iff and ofCLM_injective. Then isClosed_centralizer gives weak operator closedness, using the separating-dual hypotheses of the operator space.

**Theorem 1.10 (continuous_strongDual_apply_toPointwiseConvergenceCLM).**

$$\forall \{K 1 : Type u_1\} \{K : Type u_2\} \{E : Type u_3\} \{F : Type u_4\} [NormedField.\{u_1\} K 1 ] [RCLike.\{u_2\} K ] \{\sigma : RingHom.\{u_1, u_2\} K 1 K \} [AddCommGroup.\{u_3\} E] [TopologicalSpace.\{u_3\} E] [Module.\{u_1, u_3\} K 1 E] [ContinuousSMul.\{u_1, u_3\} K 1 E] [NormedAddCommGroup.\{u_4\} F] [NormedSpace.\{u_2, u_4\} K F] (\phi : StrongDual.\{u_2, max u_4 u_3\} K (PointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} \sigma E F)), Continuous.\{max u_3 u_4, u_2\} fun (A : ContinuousLinearMapWOT.\{u_1, u_2, u_3, u_4\} \sigma E F) \mapsto \phi ((ContinuousLinearMap.toPointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} K \sigma E F) (ContinuousLinearMapWOT.toCLM.\{u_1, u_2, u_3, u_4\} A))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.continuous_strongDual_apply_toPointwiseConvergenceCLM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PointwiseConvergenceCLM.exists_finset_sum_eq expresses phi as a finite sum of coefficients g(x)(A x). Each coefficient is weak-operator continuous by continuous_dual_apply, and continuous_finsetSum preserves continuity. Thus no functional is lost on passing from the strong to the weak operator topology.

**Theorem 1.11 (toPointwiseConvergenceCLM_mem_closure_image_iff).**

$$\forall \{K 1 : Type u_1\} \{K : Type u_2\} \{E : Type u_3\} \{F : Type u_4\} [NormedField.\{u_1\} K 1 ] [RCLike.\{u_2\} K ] \{\sigma : RingHom.\{u_1, u_2\} K 1 K \} [AddCommGroup.\{u_3\} E] [TopologicalSpace.\{u_3\} E] [Module.\{u_1, u_3\} K 1 E] [ContinuousSMul.\{u_1, u_3\} K 1 E] [NormedAddCommGroup.\{u_4\} F] [NormedSpace.\{u_2, u_4\} K F] [NormedSpace.\{0, u_4\} \mathbb{R} F] [IsScalarTower.\{0, u_2, u_4\} \mathbb{R} K F] \{s : Set.\{max u_4 u_3\} (ContinuousLinearMap.\{u_1, u_2, u_3, u_4\} \sigma E F)\}, Convex.\{0, max u_3 u_4\} \mathbb{R} s \to \forall \{T : ContinuousLinearMap.\{u_1, u_2, u_3, u_4\} \sigma E F\}, Membership.mem.\{max u_3 u_4, max u_3 u_4\} (closure.\{max u_3 u_4\} (Set.image.\{max u_3 u_4, max u_3 u_4\} (\operatorname{coe} (ContinuousLinearMap.toPointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} K \sigma E F)) s)) ((ContinuousLinearMap.toPointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} K \sigma E F) T) \iff Membership.mem.\{max u_4 u_3, max u_4 u_3\} (closure.\{max u_4 u_3\} (Set.image.\{max u_4 u_3, max u_4 u_3\} ContinuousLinearMapWOT.ofCLM.\{u_1, u_2, u_3, u_4\} s)) (ContinuousLinearMapWOT.ofCLM.\{u_1, u_2, u_3, u_4\} T)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.toPointwiseConvergenceCLM_mem_closure_image_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous identity continuous_ofPointwiseConvergenceCLM sends the strong closure into the weak closure. For the converse, use the linear identity e from the weak copy to the pointwise copy and the convex image of s. LinearMap.image_closure_of_convex applies because continuous_strongDual_apply_toPointwiseConvergenceCLM makes every pulled-back continuous linear functional continuous; it transfers weak closure membership to strong closure membership without asserting that e itself is continuous.

**Theorem 1.12 (closure_image_toPointwiseConvergenceCLM).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [CompleteSpace.\{u_2\} H] (S : StarSubalgebra.\{u_1, u_2\} K (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H)), Eq.\{u_2 + 1\} (closure.\{u_2\} (Set.image.\{u_2, u_2\} \operatorname{coe} (ContinuousLinearMap.toPointwiseConvergenceCLM.\{u_1, u_1, u_2, u_2\} K (RingHom.id.\{u_1\} K ) H H) \operatorname{coe} S)) (Set.image.\{u_2, u_2\} (\operatorname{coe} (ContinuousLinearMap.toPointwiseConvergenceCLM.\{u_1, u_1, u_2, u_2\} K (RingHom.id.\{u_1\} K ) H H)) (Set.centralizer.\{u_2\} (Set.centralizer.\{u_2\} \operatorname{coe} S)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.closure_image_toPointwiseConvergenceCLM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bicommutant is weak-operator closed by isClosed_image_ofCLM_centralizer, so its image is strongly closed by continuous_ofPointwiseConvergenceCLM and contains the strong closure of S. Conversely a basic strong neighborhood tests finitely many vectors; exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer supplies an element of S satisfying all these tests. This proves both inclusions.

**Theorem 1.13 (closure_image_ofCLM).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [CompleteSpace.\{u_2\} H] (S : StarSubalgebra.\{u_1, u_2\} K (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H)), Eq.\{u_2 + 1\} (closure.\{u_2\} (Set.image.\{u_2, u_2\} ContinuousLinearMapWOT.ofCLM.\{u_1, u_1, u_2, u_2\} \operatorname{coe} S)) (Set.image.\{u_2, u_2\} ContinuousLinearMapWOT.ofCLM.\{u_1, u_1, u_2, u_2\} (Set.centralizer.\{u_2\} (Set.centralizer.\{u_2\} \operatorname{coe} S)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.closure_image_ofCLM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weak closedness of the bicommutant and Set.subset_centralizer_centralizer give one inclusion. For the reverse, closure_image_toPointwiseConvergenceCLM gives strong closure membership of each bicommutant element. The continuous identity continuous_ofPointwiseConvergenceCLM carries it to the weak closure.

**Theorem 1.14 (closure_image_ofCLM_inter_selfAdjoint).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [CompleteSpace.\{u_2\} H] (S : StarSubalgebra.\{u_1, u_2\} K (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H)), Eq.\{u_2 + 1\} (closure.\{u_2\} (Set.image.\{u_2, u_2\} ContinuousLinearMapWOT.ofCLM.\{u_1, u_1, u_2, u_2\} (Inter.inter.\{u_2\} \operatorname{coe} S \operatorname{coe} (selfAdjoint.\{u_2\} (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H))))) (Set.image.\{u_2, u_2\} ContinuousLinearMapWOT.ofCLM.\{u_1, u_1, u_2, u_2\} (Inter.inter.\{u_2\} (Set.centralizer.\{u_2\} (Set.centralizer.\{u_2\} \operatorname{coe} S)) \operatorname{coe} (selfAdjoint.\{u_2\} (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.closure_image_ofCLM_inter_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A weak limit of self-adjoint elements lies in the bicommutant by closure_image_ofCLM and remains self-adjoint because the fixed set of continuous star is closed. Conversely apply the weak-operator continuous real-part map A mapped to one half times (A+star A) to weak approximation from S. It stays in S and is self-adjoint, and fixes a self-adjoint target.

**Theorem 1.15 (closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [CompleteSpace.\{u_2\} H] [NormedSpace.\{0, u_2\} \mathbb{R} H] [IsScalarTower.\{0, u_1, u_2\} \mathbb{R} K H] (S : StarSubalgebra.\{u_1, u_2\} K (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H)), Eq.\{u_2 + 1\} (closure.\{u_2\} (Set.image.\{u_2, u_2\} (\operatorname{coe} (ContinuousLinearMap.toPointwiseConvergenceCLM.\{u_1, u_1, u_2, u_2\} K (RingHom.id.\{u_1\} K ) H H)) (Inter.inter.\{u_2\} \operatorname{coe} S \operatorname{coe} (selfAdjoint.\{u_2\} (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H))))) (Set.image.\{u_2, u_2\} (\operatorname{coe} (ContinuousLinearMap.toPointwiseConvergenceCLM.\{u_1, u_1, u_2, u_2\} K (RingHom.id.\{u_1\} K ) H H)) (Inter.inter.\{u_2\} (Set.centralizer.\{u_2\} (Set.centralizer.\{u_2\} \operatorname{coe} S)) \operatorname{coe} (selfAdjoint.\{u_2\} (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The self-adjoint part of S is convex over the real numbers: it is the intersection of the real submodule underlying S with selfAdjoint.submodule. Apply Convex.toPointwiseConvergenceCLM_mem_closure_image_iff to equate its strong and weak closure memberships. Then closure_image_ofCLM_inter_selfAdjoint and injectivity of the two topology-copy maps identify the common set with the self-adjoint bicommutant.

**Theorem 1.16 (apply_mem_closure_of_mem_centralizer_centralizer).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [CompleteSpace.\{u_2\} H] (S : StarSubalgebra.\{u_1, u_2\} K (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H)) \{x : ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H\}, Membership.mem.\{u_2, u_2\} (Set.centralizer.\{u_2\} (Set.centralizer.\{u_2\} \operatorname{coe} S)) x \to \forall (v : H), Membership.mem.\{u_2, u_2\} (closure.\{u_2\} (Set.image.\{u_2, u_2\} (fun (s : ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H) \mapsto s v) \operatorname{coe} S)) (x v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.apply_mem_closure_of_mem_centralizer_centralizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be the closed submodule generated by the orbit S v. Multiplication preserves that orbit and continuity preserves its closure, so K is invariant under S and its adjoints. The reducing-subspace projection criterion puts K.starProjection in the commutant; since x is in the bicommutant, it commutes with this projection. The unit puts v in K, hence the projection fixes x v as well, proving that x v is in the orbit closure.

**Theorem 1.17 (exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer).**

$$\forall \{K : Type u_1\} \{H : Type u_2\} [RCLike.\{u_1\} K ] [NormedAddCommGroup.\{u_2\} H] [InnerProductSpace.\{u_1, u_2\} K H] [CompleteSpace.\{u_2\} H] (S : StarSubalgebra.\{u_1, u_2\} K (ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H)) \{x : ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H\}, Membership.mem.\{u_2, u_2\} (Set.centralizer.\{u_2\} (Set.centralizer.\{u_2\} \operatorname{coe} S)) x \to \forall \{\iota : Type u_3\} [Finite.\{u_3 + 1\} \iota ] (v : \iota \to H) \{\varepsilon : \mathbb{R} \}, LT.lt.\{0\} 0 \varepsilon \to \exists (s : ContinuousLinearMap.\{u_1, u_1, u_2, u_2\} (RingHom.id.\{u_1\} K ) H H), Membership.mem.\{u_2, u_2\} S s \land \forall (i : \iota ), LT.lt.\{0\} (Norm.norm.\{u_2\} (HSub.hSub.\{u_2, u_2, u_2\} (x (v i)) (s (v i)))) \varepsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pass to the finite Hilbert sum indexed by the given finite family. The helper diag_mem_centralizer_centralizer proves that the diagonal amplification of x is in the amplified bicommutant: matrix entries of a commuting operator lie in S', and x commutes with each entry. Apply apply_mem_closure_of_mem_centralizer_centralizer to the single vector of all v(i); Metric.mem_closure_iff gives an approximant, and PiLp.norm_apply_le bounds each coordinate error by its total Hilbert-sum error.

**Theorem 1.18 (toPointwiseConvergenceCLM_injective).**

$$\forall \{K 1 : Type u_1\} \{K 2 : Type u_2\} \{E : Type u_3\} \{F : Type u_4\} [NormedField.\{u_1\} K 1 ] [NormedField.\{u_2\} K 2 ] \{\sigma : RingHom.\{u_1, u_2\} K 1 K 2 \} [AddCommGroup.\{u_3\} E] [TopologicalSpace.\{u_3\} E] [Module.\{u_1, u_3\} K 1 E] [ContinuousSMul.\{u_1, u_3\} K 1 E] [AddCommGroup.\{u_4\} F] [TopologicalSpace.\{u_4\} F] [IsTopologicalAddGroup.\{u_4\} F] [Module.\{u_2, u_4\} K 2 F] [ContinuousConstSMul.\{u_2, u_4\} K 2 F], Function.Injective.\{max (u_3 + 1) (u_4 + 1), max (u_3 + 1) (u_4 + 1)\} \operatorname{coe} (ContinuousLinearMap.toPointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} K 2 \sigma E F)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.toPointwiseConvergenceCLM_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality after toPointwiseConvergenceCLM implies equality of the evaluations at every v by congrArg. ContinuousLinearMap.ext then identifies the original maps, so changing the topology copy identifies no distinct operators.

**Theorem 1.19 (exists_finset_sum_eq).**

$$\forall \{K 1 : Type u_1\} \{K : Type u_2\} \{E : Type u_3\} \{F : Type u_4\} [NormedField.\{u_1\} K 1 ] [RCLike.\{u_2\} K ] \{\sigma : RingHom.\{u_1, u_2\} K 1 K \} [AddCommGroup.\{u_3\} E] [TopologicalSpace.\{u_3\} E] [Module.\{u_1, u_3\} K 1 E] [NormedAddCommGroup.\{u_4\} F] [NormedSpace.\{u_2, u_4\} K F] (\phi : StrongDual.\{u_2, max u_4 u_3\} K (PointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} \sigma E F)), \exists (s : Finset.\{u_3\} E) (g : E \to StrongDual.\{u_2, u_4\} K F), \forall (T : PointwiseConvergenceCLM.\{u_1, u_2, u_3, u_4\} \sigma E F), Eq.\{u_2 + 1\} (\phi T) (\sum x \in s, (g x) (T x))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.exists_finset_sum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Seminorm.bound_of_continuous bounds phi by finitely many evaluations, so phi factors through the finite-coordinate linear map Phi:T mapped to (T x) on a finite set s. The norm bound makes this factor well defined on range(Phi). Module.Dual.exists_continuous_extension_of_le_seminorm extends it to all of the finite product; decomposing that extension by ContinuousLinearMap.sum_comp_single yields one continuous functional on F per coordinate and the required finite sum.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.apply_eq_sum_piLpEntry`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.apply_mem_closure_of_mem_centralizer_centralizer`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.closure_image_ofCLM`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.closure_image_ofCLM_inter_selfAdjoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.closure_image_toPointwiseConvergenceCLM`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.continuous_ofPointwiseConvergenceCLM`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.continuous_strongDual_apply_toPointwiseConvergenceCLM`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.diagStarAlgHom_apply`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.diagStarAlgHom_apply_single`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.exists_finset_sum_eq`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.isClosed_image_ofCLM_centralizer`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.isReducing_coe_iff_commute_starProjection`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.isReducing_iff`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.isReducing_iff_mem_invtSubmodule_adjoint`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.piLpEntry_apply`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.toPointwiseConvergenceCLM_injective`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/VonNeumannAlgebra/Density.toPointwiseConvergenceCLM_mem_closure_image_iff`
