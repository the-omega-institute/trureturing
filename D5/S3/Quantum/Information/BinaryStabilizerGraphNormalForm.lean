/- GID: D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/BinaryStabilizerGraphNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pauli stabilizer eigenlines are local-unitary images of binary graph amplitudes. -/

/-
Per-declaration judgement:
  complex_sign_eq_one_iff: proof_shape: bind-only; escape_witness: none.
    consumer: eigen_pair_orthogonal.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  complex_sign_val: proof_shape: bind-only; escape_witness: none.
    consumer: graph_fixed_line, StabilizerMultiEntropyCollapse.graph_replica_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  weyl: proof_shape: bind-only; escape_witness: none.
    consumer: eigen_orthogonal_iff, eigen_pair_orthogonal, generator_data, graph_fixed_line,
      graph_sign_correction, stabilizer_graph_eigen, stabilizer_graph_normal_form, stabilizer_weyl,
      tensor_clifford, tensor_weyl, unique_weyl_line_lagrangian, weyl_commute, weyl_injective,
      weyl_linear, weyl_mul, weyl_square.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  sp_bilinear: proof_shape: bind-only; escape_witness: none.
    consumer: eigen_orthogonal_iff.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  spForm: proof_shape: bind-only; escape_witness: none.
    consumer: eigen_orthogonal_iff, sp_alt, sp_nondegenerate, unique_weyl_line_lagrangian.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  sp_alt: proof_shape: bind-only; escape_witness: none.
    consumer: sp_nondegenerate, unique_weyl_line_lagrangian.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  sp_nondegenerate: proof_shape: bind-only; escape_witness: none.
    consumer: unique_weyl_line_lagrangian.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  weyl_linear: proof_shape: bind-only; escape_witness: none.
    consumer: eigen_orthogonal_iff, eigen_pair_orthogonal, generator_data, graph_sign_correction,
      stabilizer_graph_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  weyl_mul: proof_shape: bind-only; escape_witness: none.
    consumer: weyl_commute, weyl_square.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  weyl_square: proof_shape: bind-only; escape_witness: none.
    consumer: generator_data, graph_sign_correction, stabilizer_graph_normal_form, weyl_injective.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  weyl_injective: proof_shape: bind-only; escape_witness: none.
    consumer: eigen_pair_orthogonal.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  weyl_commute: proof_shape: bind-only; escape_witness: none.
    consumer: eigen_orthogonal_iff, eigen_pair_orthogonal, graph_sign_correction.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  eigen_pair_orthogonal: proof_shape: bind-only; escape_witness: none.
    consumer: eigen_orthogonal_iff, unique_weyl_line_lagrangian.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  generator_data: proof_shape: bind-only; escape_witness: none.
    consumer: eigen_orthogonal_iff, unique_weyl_line_lagrangian.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  eigen_orthogonal_iff: proof_shape: bind-only; escape_witness: none.
    consumer: unique_weyl_line_lagrangian.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  unique_weyl_line_lagrangian: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_eigen.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  wmat: proof_shape: bind-only; escape_witness: none.
    consumer: gate_wmat, pauli_wmat, stabilizer_graph_normal_form, stabilizer_weyl, tensor_clifford,
      tensor_weyl, wmat_unitary.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  tensor_mul: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_normal_form, tensor_clifford, tensor_unitary.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  tensor_one: proof_shape: bind-only; escape_witness: none.
    consumer: tensor_unitary.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  tensor_adj: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_normal_form, tensor_unitary.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  tensor_unitary: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  tensor_smul: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_weyl, tensor_clifford.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  tensor_weyl: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_normal_form, stabilizer_weyl, tensor_clifford.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  pauli_wmat: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_weyl.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  stabilizer_weyl: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_eigen.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  gate: proof_shape: bind-only; escape_witness: none.
    consumer: gate_unitary, gate_wmat, stabilizer_graph_eigen, tensor_clifford.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  wmat_unitary: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  gate_unitary: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_eigen.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  gate_wmat: proof_shape: bind-only; escape_witness: none.
    consumer: tensor_clifford.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  graphAmp: proof_shape: bind-only; escape_witness: none.
    consumer: StabilizerMultiEntropyCollapse.graph_count, StabilizerMultiEntropyCollapse.graph_norm,
      StabilizerMultiEntropyCollapse.graph_replica_form,
      StabilizerMultiEntropyCollapse.graph_scalar_norm,
      StabilizerMultiEntropyCollapse.stabilizer_replica_count, graph_fixed_line,
      graph_sign_correction, stabilizer_graph_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  graph_exponent_step: proof_shape: bind-only; escape_witness: none.
    consumer: graph_fixed_line.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  graph_fixed_line: proof_shape: bind-only; escape_witness: none.
    consumer: graph_sign_correction.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  symbolTransform: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_eigen, tensor_clifford.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  tensor_clifford: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_eigen.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  stabilizer_graph_eigen: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  graph_sign_correction: proof_shape: bind-only; escape_witness: none.
    consumer: stabilizer_graph_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  stabilizer_graph_normal_form: proof_shape: bind-only; escape_witness: none.
    consumer: StabilizerMultiEntropyCollapse.stabilizer_replica_count.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
Utility: none. The declarations give general mathematical identities and constructions;
fixed field and mode checks occur only inside parameterized proofs. No declaration
is an instance certificate, bounded enumeration result, checker or numeric reduction.
Direct frozen dependencies:
  GID: D5/S3/Quantum/Information/BinaryLagrangianGraphForm.sp.eq_1
    statement_id: sha256:12c5253668dc09888db774b33fa6859c5a970e0ee9d7fea8e2d2b341465e482e
  GID: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2._proof_1
    statement_id: sha256:603272a6c902f12a9c66e312346336a2af0f96b644ac04aa131724b394894094
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.F₂
    statement_id: sha256:e975fc48104d0cb1a40271fdfb5ec7fcfe2730a1c600ee81758d5e89253bd60f
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.result._simp_1_2
    statement_id: sha256:b6d398a580b6082cdf28a5f507b45bd399f1ae7037e5a5319384011b96fc19a3
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.result._simp_1_4
    statement_id: sha256:2eef85eac594a0afbcfd3444522525aacba24337dc294a1cf3f33407694d1fea
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.sign_one
    statement_id: sha256:3390781fef4db85cc283ca47cb98003a93fef2156bfaa5354db33575bb072789
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.sign_sum
    statement_id: sha256:cca15d93bbe8896cad48b7dfd75c8053ab080db717fab32f9ace58b5aaeec0b9
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.sign_nonzero
    statement_id: sha256:d7ca18ebff2d96e19693718a018f09f40127798210eb1de61ec401a3d5662846
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.sign_square
    statement_id: sha256:c9eaaa9aeba5c9bcec2f202017c45309146cbb04b59c5aef760c4e5083f0206d
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.sign_zero
    statement_id: sha256:6065f8df9a4b3f5f290d325893fac6a30be0a2f654742e19f7c87af97a665bc0
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign_add
    statement_id: sha256:9299cfc42d5d0ba183be190abb0eaa8f7ca19b25a002ecd815057449aad3e7ad
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign
    statement_id: sha256:815b3b55d18bbe94631f98e608ed75835a5ed6590c5cb4a958805cade90cb93d
  GID: D5/S3/Quantum/Information/BinaryLagrangianGraphForm.swapAt_involutive
    statement_id: sha256:318ab2f1a41fa4ce559fbb3ae07042ff119b4a40b9b189be8ff420a8769d7a36
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.normalExponent
    statement_id: sha256:582b0f2439e696a8856cf0d2c7099efbee950ed3b8702546f84c5b45cc7598f4
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.normal_exponent_add
    statement_id: sha256:25c15cd880920aba6f50c6998cb43db3f089545736f527745851aac167b595cf
  GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.symmetric_pairing_split
    statement_id: sha256:405a00d5a8d535dca99b1a3cdf1c32952c20c59530abd03e02173bf8f7a55b0d
  GID: D5/S3/Quantum/FiniteDimensional.QubitMatrix
    statement_id: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
  GID: D5/S3/Quantum/FiniteDimensional.qubitX
    statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
  GID: D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  GID: D5/S3/Quantum/Information/BinaryLagrangianGraphForm.lagrangian_graph_form
    statement_id: sha256:1cb9ea66caaaacf6cc8ed0ee9bede6714cc405010bd8d8f97fc35d652286ecdb
  GID: D5/S3/Quantum/Information/BinaryLagrangianGraphForm.sp
    statement_id: sha256:c75819ffa723a2d0e418784cdf96cce4f0e22e0ea5d31b161c4c27cd278b9395
  GID: D5/S3/Quantum/Information/BinaryLagrangianGraphForm.swapAt
    statement_id: sha256:2178c08684b4cb007ea35662d44cf842cb8c1341ab01195132053494ec59743c
  GID: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.StabilizedBy
    statement_id: sha256:84981833e6a3c38263d5476f28eb063fbdd1f76f4349d22a4bb67f3cb128d344
  GID: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard
    statement_id: sha256:d28d3fee83d154e42cf2331eba2ffeb942edeed66e1ff8e9221f10b0b991ddc4
  GID: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.pauliSet
    statement_id: sha256:856f9c10bdadcb60566b2de31e839e712c75cb4be32af461b413c9fdc95a1014
  GID: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2
    statement_id: sha256:ef4ae1e2fc1bec9bf605d06598d58ce332db9ba1a90facd16a497c70ae0336f7
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli
    statement_id: sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.I
    statement_id: sha256:194b87c5757c4209245572dae83ba02c7d0b8bc34b3603b0077d1f7bef8d5086
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X
    statement_id: sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y
    statement_id: sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z
    statement_id: sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.casesOn
    statement_id: sha256:c60f54d386f630c67ca7fad1dda77fd41521c115859600ec4a174714604498f2
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix
    statement_id: sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
  GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.tensorOp
    statement_id: sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
-/

import D5.S3.Quantum.Information.BinaryLagrangianGraphForm
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization

open scoped BigOperators
open D5.S3.Quantum.FiniteDimensional
open Matrix D5.S3.Quantum.Information.BinaryLagrangianGraphForm
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

noncomputable section

namespace D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm

/-- The Weyl operator `X^x Z^z` on functions on the binary configuration space. -/
private def weyl {N : ℕ} (v : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) (f : (Fin N → ZMod 2) → ℂ) :
  (Fin N → ZMod 2) → ℂ :=
  fun t => complexSign (∑ i, v.2 i * (t i + v.1 i)) * f (t + v.1)

private lemma complex_sign_eq_one_iff (a : ZMod 2) : complexSign a = 1 ↔ a = 0 := by
  simp only [complexSign, F₂]
  split_ifs with ha
  · simp [ha]
  · norm_num [ha]

lemma complex_sign_val (a : ZMod 2) : complexSign a = (-1 : ℂ) ^ a.val := by
  have ha : a = 0 ∨ a = 1 := (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) a
  rcases ha with rfl | rfl
  · change complexSign (0 : ZMod 2) = (-1 : ℂ) ^ 0
    rw [D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_zero, pow_zero]
  · change complexSign (1 : ZMod 2) = (-1 : ℂ) ^ 1
    rw [D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_one, pow_one]

private lemma sp_bilinear {N : ℕ} :
    (∀ u v w : ((Fin N → ZMod 2) × (Fin N → ZMod 2)), sp (u + v) w = sp u w + sp v w) ∧
    (∀ (a : ZMod 2) (u w : ((Fin N → ZMod 2) × (Fin N → ZMod 2))), sp (a • u) w = a • sp u w) ∧
    (∀ u v w : ((Fin N → ZMod 2) × (Fin N → ZMod 2)), sp u (v + w) = sp u v + sp u w) ∧
    (∀ (a : ZMod 2) (u w : ((Fin N → ZMod 2) × (Fin N → ZMod 2))), sp u (a • w) = a • sp u w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v w
    simp only [sp, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro a u w
    simp only [sp, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro u v w
    simp only [sp, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro a u w
    simp only [sp, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
private def spForm (N : ℕ) : LinearMap.BilinForm (ZMod 2) (((Fin N → ZMod 2) × (Fin N → ZMod 2))) :=
  LinearMap.mk₂ (ZMod 2) sp sp_bilinear.1 sp_bilinear.2.1
    sp_bilinear.2.2.1 sp_bilinear.2.2.2
private lemma sp_alt (N : ℕ) : (spForm N).IsAlt := by
  intro u
  change sp u u = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm (u.2 i) (u.1 i)]
  exact CharTwo.add_self_eq_zero _
private lemma sp_nondegenerate (N : ℕ) : (spForm N).Nondegenerate := by
  classical
  apply (sp_alt N).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro u hu
  apply Prod.ext
  · funext i
    have h := hu (0, Pi.single i 1)
    change sp u (0, Pi.single i 1) = 0 at h
    simpa [sp, Pi.single_apply, mul_ite] using h
  · funext i
    have h := hu (Pi.single i 1, 0)
    change sp u (Pi.single i 1, 0) = 0 at h
    simpa [sp, Pi.single_apply, mul_ite] using h
private lemma weyl_linear {N : ℕ} (u : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) :
    (∀ f g, weyl u (f + g) = weyl u f + weyl u g) ∧
    (∀ (a : ℂ) f, weyl u (a • f) = a • weyl u f) ∧ weyl u 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g
    funext t
    simp [weyl.eq_1, mul_add]
  · intro a f
    funext t
    simp [weyl, mul_left_comm]
  · funext t
    simp [weyl]
private lemma weyl_mul {N : ℕ} (u w : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) (f : (Fin N → ZMod 2) →
  ℂ) :
    weyl u (weyl w f) = complexSign (∑ i, u.2 i * w.1 i) • weyl (u + w) f := by
  funext t
  simp only [weyl, Pi.add_apply, Prod.fst_add, Prod.snd_add, Pi.smul_apply,
    smul_eq_mul, add_assoc]
  rw [← mul_assoc, ← mul_assoc, ← complexSign_add, ← complexSign_add]
  congr 1
  apply congrArg complexSign
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = u.2 i * w.1 i + (u.2 i + w.2 i) * (t i + (u.1 i + w.1 i)) -
        (u.2 i * w.1 i + u.2 i * w.1 i) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, sub_zero]
private lemma weyl_square {N : ℕ} (u : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) (f : (Fin N → ZMod 2)
  → ℂ) :
    weyl u (weyl u f) = complexSign (∑ i, u.1 i * u.2 i) • f := by
  rw [weyl_mul]
  have hz : u + u = 0 := by
    apply Prod.ext <;> funext i <;> exact CharTwo.add_self_eq_zero _
  have hzero : weyl (0 : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) f = f := by
    funext t
    simp [weyl, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_zero]
  rw [hz, hzero]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => mul_comm (u.2 i) (u.1 i))
private lemma weyl_injective {N : ℕ} (u : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) :
  Function.Injective (weyl u) := by
  intro f g hfg
  have h := congrArg (weyl u) hfg
  rw [weyl_square, weyl_square] at h
  exact smul_right_injective ((Fin N → ZMod 2) → ℂ) (sign_nonzero _) h
private lemma weyl_commute {N : ℕ} (u w : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) (f : (Fin N → ZMod
  2) → ℂ) :
    weyl u (weyl w f) = complexSign (sp u w) • weyl w (weyl u f) := by
  rw [weyl_mul, weyl_mul, add_comm w u, smul_smul]
  congr 1
  have h : (∑ i, w.2 i * u.1 i) = ∑ i, u.1 i * w.2 i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [sp, Finset.sum_add_distrib, h, complexSign_add]
  symm
  calc
    _ = (complexSign (∑ i, u.1 i * w.2 i) * complexSign (∑ i, u.1 i * w.2 i)) *
        complexSign (∑ i, u.2 i * w.1 i) := by ring
    _ = _ := by rw [sign_square, one_mul]
private lemma eigen_pair_orthogonal {N : ℕ} {ψ : (Fin N → ZMod 2) → ℂ} (hne : ψ ≠ 0)
    {u w : ((Fin N → ZMod 2) × (Fin N → ZMod 2))} {a b : ℂ} (hu : weyl u ψ = a • ψ) (hw : weyl w ψ =
      b • ψ) :
    sp u w = 0 := by
  have hn : weyl w (weyl u ψ) ≠ 0 := by
    intro h
    have hz : weyl u ψ = 0 :=
      weyl_injective w (h.trans (weyl_linear w).2.2.symm)
    exact hne (weyl_injective u (hz.trans (weyl_linear u).2.2.symm))
  have hc : weyl u (weyl w ψ) = weyl w (weyl u ψ) := by
    rw [hw, (weyl_linear u).2.1, hu, (weyl_linear w).2.1, hw,
      smul_smul, smul_smul, mul_comm]
  have h := weyl_commute u w ψ
  rw [hc] at h
  have hχ : (1 : ℂ) = complexSign (sp u w) :=
    smul_left_injective ℂ hn (by simpa only [one_smul] using h)
  exact (complex_sign_eq_one_iff _).mp hχ.symm
private lemma generator_data {N : ℕ} {ψ : (Fin N → ZMod 2) → ℂ} (hne : ψ ≠ 0)
    {u : ((Fin N → ZMod 2) × (Fin N → ZMod 2))} {c : ℂ} (h : c • weyl u ψ = ψ) :
    c ≠ 0 ∧ c ^ 2 = complexSign (∑ i, u.1 i * u.2 i) ∧ weyl u ψ = c⁻¹ • ψ := by
  have hc : c ≠ 0 := by
    intro hc
    exact hne (by simpa only [hc, zero_smul] using h.symm)
  have he : weyl u ψ = c⁻¹ • ψ := by
    have hh := congrArg (fun f : (Fin N → ZMod 2) → ℂ => c⁻¹ • f) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh
  have hh := congrArg (fun f : (Fin N → ZMod 2) → ℂ => c • weyl u f) h
  rw [(weyl_linear u).2.1, weyl_square] at hh
  simp only [smul_smul, h] at hh
  have hp : (c * c) * complexSign (∑ i, u.1 i * u.2 i) = 1 :=
    smul_left_injective ℂ hne (by simpa only [one_smul, mul_assoc] using hh)
  refine ⟨hc, ?_, he⟩
  calc
    c ^ 2 = ((c * c) * complexSign (∑ i, u.1 i * u.2 i)) *
        complexSign (∑ i, u.1 i * u.2 i) := by
      rw [mul_assoc, sign_square, mul_one, pow_two]
    _ = _ := by rw [hp, one_mul]
private lemma eigen_orthogonal_iff {N k : ℕ}
    (v : Fin k → ((Fin N → ZMod 2) × (Fin N → ZMod 2))) (c : Fin k → ℂ) (ψ : (Fin N → ZMod 2) → ℂ)
      (hne : ψ ≠ 0)
    (hline : ∀ w : (Fin N → ZMod 2) → ℂ,
      (∀ j, c j • weyl (v j) w = w) ↔ ∃ a : ℂ, w = a • ψ)
    (u : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) :
    (∃ a : ℂ, weyl u ψ = a • ψ) ↔
      u ∈ (spForm N).orthogonal (Submodule.span (ZMod 2) (Set.range v)) := by
  have hψ : ∀ j, c j • weyl (v j) ψ = ψ :=
    (hline ψ).mpr ⟨1, (one_smul ℂ ψ).symm⟩
  constructor
  · rintro ⟨a, ha⟩
    intro w hw
    change sp w u = 0
    refine Submodule.span_induction (p := fun w _ => sp w u = 0) ?_ ?_ ?_ ?_ hw
    · rintro w ⟨j, rfl⟩
      exact eigen_pair_orthogonal hne (generator_data hne (hψ j)).2.2 ha
    · simp [sp]
    · intro w z _ _ hw hz
      rw [sp_bilinear.1, hw, hz, add_zero]
    · intro a w _ hw
      rw [sp_bilinear.2.1, hw, smul_zero]
  · intro hu
    apply (hline (weyl u ψ)).mp
    intro j
    have hju := hu (v j) (Submodule.subset_span ⟨j, rfl⟩)
    change sp (v j) u = 0 at hju
    rw [weyl_commute, hju, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_zero, one_smul,
      ← (weyl_linear u).2.1, hψ j]

private theorem unique_weyl_line_lagrangian {N k : ℕ}
    (v : Fin k → ((Fin N → ZMod 2) × (Fin N → ZMod 2))) (c : Fin k → ℂ) (ψ : (Fin N → ZMod 2) → ℂ)
    (hne : ψ ≠ 0)
    (hline : ∀ w : (Fin N → ZMod 2) → ℂ,
      (∀ j, c j • weyl (v j) w = w) ↔ ∃ a : ℂ, w = a • ψ) :
    let L := Submodule.span (ZMod 2) (Set.range v)
    (∀ j, c j ^ 2 = complexSign (∑ i, (v j).1 i * (v j).2 i)) ∧
    (∀ u ∈ L, ∀ w ∈ L, sp u w = 0) ∧
    Module.finrank (ZMod 2) L = N ∧
    (∀ u : ((Fin N → ZMod 2) × (Fin N → ZMod 2)), (∃ a : ℂ, weyl u ψ = a • ψ) ↔ u ∈ L) := by
  classical
  let L := Submodule.span (ZMod 2) (Set.range v)
  change (∀ j, c j ^ 2 = complexSign (∑ i, (v j).1 i * (v j).2 i)) ∧
    (∀ u ∈ L, ∀ w ∈ L, sp u w = 0) ∧ Module.finrank (ZMod 2) L = N ∧
    (∀ u : ((Fin N → ZMod 2) × (Fin N → ZMod 2)), (∃ a : ℂ, weyl u ψ = a • ψ) ↔ u ∈ L)
  have hψ : ∀ j, c j • weyl (v j) ψ = ψ :=
    (hline ψ).mpr ⟨1, (one_smul ℂ ψ).symm⟩
  have hg := fun j => generator_data hne (hψ j)
  have hLO : L ≤ (spForm N).orthogonal L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact (eigen_orthogonal_iff v c ψ hne hline (v j)).mp ⟨(c j)⁻¹, (hg j).2.2⟩
  have hOO : (spForm N).orthogonal L ≤
      (spForm N).orthogonal ((spForm N).orthogonal L) := by
    intro u hu w hw
    obtain ⟨a, ha⟩ := (eigen_orthogonal_iff v c ψ hne hline w).mpr hw
    obtain ⟨b, hb⟩ := (eigen_orthogonal_iff v c ψ hne hline u).mpr hu
    exact eigen_pair_orthogonal hne ha hb
  have heq : (spForm N).orthogonal L = L := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal (B := spForm N)
      (sp_nondegenerate N) (sp_alt N).isRefl L] at hOO
    exact le_antisymm hOO hLO
  refine ⟨fun j => (hg j).2.1, ?_, ?_, ?_⟩
  · intro u hu w hw
    exact hLO hw u hu
  · have hd := LinearMap.BilinForm.finrank_add_finrank_orthogonal (B := spForm N)
      (sp_alt N).isRefl L
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot (sp_nondegenerate N), inf_bot_eq,
      finrank_bot, add_zero, heq] at hd
    have hdim : Module.finrank (ZMod 2) (((Fin N → ZMod 2) × (Fin N → ZMod 2))) = N + N := by
      simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin]
    rw [hdim] at hd
    omega
  · intro u
    rw [← heq]
    exact eigen_orthogonal_iff v c ψ hne hline u

private def wmat (a b : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun t s =>
    if id (α := ZMod 2) s = id (α := ZMod 2) t + a then complexSign (b * id (α := ZMod 2) s) else 0

private lemma tensor_mul {N : ℕ} (A B : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorOp A * tensorOp B = tensorOp (fun i => A i * B i) := by
  ext x z
  simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]
  simp_rw [D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.result._simp_1_2]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

private lemma tensor_one {N : ℕ} :
    tensorOp (fun _ : Fin N => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  classical
  ext x y
  simp only [tensorOp, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst y; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private lemma tensor_adj {N : ℕ} (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorOp A)ᴴ = tensorOp (fun i => (A i)ᴴ) := by
  ext x y
  simp [tensorOp, Matrix.conjTranspose_apply]

private lemma tensor_unitary {N : ℕ} (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i, A i ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    tensorOp A ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (tensorOp A)ᴴ * tensorOp A = 1
  rw [tensor_adj, tensor_mul]
  have he : (fun i => (A i)ᴴ * A i) = fun _ => 1 :=
    funext fun i => Matrix.mem_unitaryGroup_iff'.mp (hA i)
  rw [he]
  exact tensor_one

private lemma tensor_smul {N : ℕ} (r : Fin N → ℂ)
    (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorOp (fun i => r i • A i) = (∏ i, r i) • tensorOp A := by
  ext x y
  simp [tensorOp, Finset.prod_mul_distrib]

private lemma tensor_weyl {N : ℕ} (v : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) (f : (Fin N → ZMod 2)
  → ℂ) :
    tensorOp (fun i => wmat (v.1 i) (v.2 i)) *ᵥ f = weyl v f := by
  classical
  let T : Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ := tensorOp (fun i => wmat (v.1 i) (v.2 i))
  have entries (x y : (Fin N → ZMod 2)) : T x y =
      if y = x + v.1 then complexSign (∑ i, v.2 i * y i) else 0 := by
    change (∏ i, if id (α := ZMod 2) (y i) = id (α := ZMod 2) (x i) + v.1 i then
      complexSign (v.2 i * id (α := ZMod 2) (y i)) else 0) = _
    simp only [id]
    by_cases h : y = x + v.1
    · subst y
      simp only [Pi.add_apply, ite_true]
      exact (sign_sum Finset.univ _).symm
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  change T *ᵥ f = weyl v f
  funext t
  simp only [Matrix.mulVec, dotProduct, entries, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (t + v.1)]
  · simp [weyl]
  · intro b _ hb; simp [hb]
  · simp

private lemma pauli_wmat (p : Pauli) :
    ∃ a b : ZMod 2, ∃ r : ℂ, r ≠ 0 ∧ pauliMatrix p = r • wmat a b := by
  have binary_zero : id (α := ZMod 2) (0 : Fin 2) = (0 : ZMod 2) := rfl
  have binary_one : id (α := ZMod 2) (1 : Fin 2) = (1 : ZMod 2) := rfl
  cases p
  · refine ⟨0, 0, 1, one_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat.eq_1, binary_zero, binary_one,
      CharTwo.add_self_eq_zero, complexSign, F₂]
  · refine ⟨1, 0, 1, one_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat, binary_zero, binary_one,
        CharTwo.add_self_eq_zero, complexSign, F₂, D5.S3.Quantum.FiniteDimensional.qubitX]
  · refine ⟨1, 1, Complex.I, Complex.I_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat, binary_zero, binary_one,
        CharTwo.add_self_eq_zero, complexSign, F₂, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨0, 1, 1, one_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat, binary_zero, binary_one,
        CharTwo.add_self_eq_zero, complexSign, F₂, D5.S3.Quantum.FiniteDimensional.qubitZ]

private lemma stabilizer_weyl {N : ℕ} (ψ : (Fin N → ZMod 2) → ℂ)
    (hψ : StabilizedBy pauliSet ψ) :
    ∃ k : ℕ, ∃ v : Fin k → ((Fin N → ZMod 2) × (Fin N → ZMod 2)), ∃ c : Fin k → ℂ,
      ∀ w : (Fin N → ZMod 2) → ℂ, (∀ j, c j • weyl (v j) w = w) ↔ ∃ a : ℂ, w = a • ψ := by
  classical
  obtain ⟨_, k, O, hO, hline⟩ := hψ
  choose r hr p hp using hO
  choose a b s hs hps using fun j i => pauli_wmat (p j i)
  let v : Fin k → ((Fin N → ZMod 2) × (Fin N → ZMod 2)) := fun j => (a j, b j)
  let c : Fin k → ℂ := fun j => ∏ i, r j i * s j i
  have hop (j : Fin k) (w : (Fin N → ZMod 2) → ℂ) :
      (show Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ from tensorOp (O j)) *ᵥ w = c j • weyl (v
        j) w := by
    have he : O j = fun i => (r j i * s j i) • wmat (a j i) (b j i) := by
      funext i
      rw [hp j i, hps j i, smul_smul]
    rw [he, tensor_smul]
    change ((∏ i, r j i * s j i) •
      (show Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ from tensorOp (fun i => wmat (a j i) (b j
        i)))) *ᵥ w = _
    rw [Matrix.smul_mulVec]
    exact congrArg ((∏ i, r j i * s j i) • ·) (tensor_weyl (v j) w)
  refine ⟨k, v, c, ?_⟩
  intro w
  have hline' : (∀ j, (show Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ from tensorOp (O j)) *ᵥ w
    = w) ↔
      ∃ a : ℂ, w = a • ψ := hline w
  simpa only [hop] using hline'


private def gate (h : Bool) (d : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if d = 0 then 1 else !![1, 0; 0, Complex.I]) *
    (if h then BinaryStabilizerLocalInequivalence.hadamard else 1)

private lemma wmat_unitary (a b : ZMod 2) :
    wmat a b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have binary_zero : id (α := ZMod 2) (0 : Fin 2) = (0 : ZMod 2) := rfl
  have binary_one : id (α := ZMod 2) (1 : Fin 2) = (1 : ZMod 2) := rfl
  have cases₂ : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rw [Matrix.mem_unitaryGroup_iff]
  rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [wmat, binary_zero, binary_one, CharTwo.add_self_eq_zero, complexSign, F₂,
      Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private lemma gate_unitary (h : Bool) (d : ZMod 2) :
    gate h d ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hs : s2 ^ 2 = 1 / 2 := by
    simp only [s2]
    push_cast
    rw [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hr : (starRingEnd ℂ) s2 = s2 := by simp [s2, map_ofNat]
  have cases₂ : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rw [Matrix.mem_unitaryGroup_iff]
  cases h <;> rcases cases₂ d with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gate.eq_1, BinaryStabilizerLocalInequivalence.hadamard,
      pauliMatrix, qubitX, qubitZ, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, hr]
  all_goals ring_nf; norm_num [hs, Complex.I_sq]

set_option maxHeartbeats 1000000 in
-- The sixteen binary parameter cases expand to sixty-four matrix entry equalities.
private lemma gate_wmat (h : Bool) (d a b : ZMod 2) :
    let a' := if h then b else a
    let b' := (if h then a else b) + d * a'
    ∃ r : ℂ, r ≠ 0 ∧ gate h d * wmat a b = r • (wmat a' b' * gate h d) := by
  have binary_zero : id (α := ZMod 2) (0 : Fin 2) = (0 : ZMod 2) := rfl
  have binary_one : id (α := ZMod 2) (1 : Fin 2) = (1 : ZMod 2) := rfl
  have cases₂ : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  refine ⟨complexSign (if h then a * b else 0) *
    (if d * (if h then b else a) = 0 then 1 else Complex.I), ?_, ?_⟩
  · cases h <;> rcases cases₂ d with rfl | rfl <;>
      rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;>
      norm_num [complexSign, F₂]
  · cases h <;> rcases cases₂ d with rfl | rfl <;>
      rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [gate, wmat, BinaryStabilizerLocalInequivalence.hadamard,
        pauliMatrix, qubitX, qubitZ, Matrix.mul_apply,
        Fin.sum_univ_two, complexSign, F₂, binary_zero, binary_one, CharTwo.add_self_eq_zero] <;>
        ring_nf <;> norm_num [Complex.I_sq]


/-- The complex sign of the ordered binary quadratic exponent. -/
def graphAmp {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (x : Fin N → Fin 2) : ℂ :=
  let t : Fin N → ZMod 2 := x
  (-1 : ℂ) ^ (normalExponent Γ t).val

private lemma graph_exponent_step {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (hs : Γ.IsSymm) (hd : ∀ i, Γ i i = 0) (t : (Fin N → ZMod 2)) (i : Fin N) :
    normalExponent Γ (t + Pi.single i 1) = normalExponent Γ t + ∑ j, Γ i j * t j := by
  classical
  have h := normal_exponent_add Γ t (Pi.single i 1)
  have hp := symmetric_pairing_split Γ hs t (Pi.single i 1)
  have hz : normalExponent Γ (Pi.single i 1) = 0 := by
    unfold normalExponent
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b hb
    have hab := (Finset.mem_filter.mp hb).2
    by_cases ha : a = i
    · subst a
      simp [ne_of_gt hab]
    · simp [Pi.single_apply, ha]
  have hb : Matrix.toBilin' Γ t (Pi.single i 1) = ∑ j, Γ i j * t j := by
    simp only [Matrix.toBilin'_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq',
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.result._simp_1_4, if_true]
    exact Finset.sum_congr rfl (fun j _ => by rw [hs.apply j i, mul_comm])
  simp only [hd, zero_mul, Finset.sum_const_zero, zero_add, hb] at hp
  rw [← hp, hz, add_zero] at h
  calc
    normalExponent Γ (t + Pi.single i 1) =
        (∑ j, Γ i j * t j) + ((∑ j, Γ i j * t j) +
          normalExponent Γ (t + Pi.single i 1)) := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    _ = (∑ j, Γ i j * t j) + normalExponent Γ t :=
      congrArg (fun z => (∑ j, Γ i j * t j) + z) h.symm
    _ = normalExponent Γ t + ∑ j, Γ i j * t j := add_comm _ _

private theorem graph_fixed_line {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (hs : Γ.IsSymm) (hd : ∀ i, Γ i i = 0) (f : (Fin N → ZMod 2) → ℂ)
    (hf : ∀ i, weyl (Pi.single i 1, Γ *ᵥ Pi.single i 1) f = f) :
    f = f 0 • graphAmp Γ := by
  have cases₂ : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  classical
  let g : (Fin N → ZMod 2) → ℂ := fun t => complexSign (normalExponent Γ t) * f t
  have step (t : (Fin N → ZMod 2)) (i : Fin N) : g (t + Pi.single i 1) = g t := by
    have phase : (∑ j, (Γ *ᵥ Pi.single i 1) j *
        (t j + (Pi.single i (1 : ZMod 2) : (Fin N → ZMod 2)) j)) = ∑ j, Γ i j * t j := by
      simp only [Matrix.mulVec_single_one, Matrix.col_apply, mul_add, Finset.sum_add_distrib]
      have hz : (∑ j, Γ j i * (Pi.single i (1 : ZMod 2) : (Fin N → ZMod 2)) j) = 0 := by
        simp [Pi.single_apply, mul_ite, hd]
      rw [hz, add_zero]
      exact Finset.sum_congr rfl (fun j _ => by rw [hs.apply i j])
    have h := congrFun (hf i) t
    simp only [weyl, phase] at h
    dsimp only [g]
    rw [graph_exponent_step Γ hs hd, complexSign_add, mul_assoc, h]
  have invariant (u : (Fin N → ZMod 2)) : ∀ t : (Fin N → ZMod 2), g (t + u) = g t := by
    apply Pi.single_induction (fun u => ∀ t : (Fin N → ZMod 2), g (t + u) = g t) u
    · intro t
      simp
    · intro u v hu hv t
      rw [← add_assoc, hv, hu]
    · intro i a t
      have ha : a = 0 ∨ a = 1 := cases₂ a
      rcases ha with rfl | rfl
      · simp
      · exact step t i
  funext t
  change f t = f 0 * graphAmp Γ t
  have hconst : g t = f 0 := by
    have hz : normalExponent Γ 0 = 0 := by simp [normalExponent]
    simpa only [zero_add, g, hz,
      D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_zero, one_mul] using invariant t 0
  calc
    f t = complexSign (normalExponent Γ t) * g t := by
      dsimp only [g]
      rw [← mul_assoc, sign_square, one_mul]
    _ = f 0 * graphAmp Γ t := by
      rw [hconst]
      have hg : graphAmp Γ t = complexSign (normalExponent Γ t) :=
        (complex_sign_val _).symm
      rw [hg, mul_comm]

private def symbolTransform {N : ℕ} (H : Finset (Fin N)) (d : (Fin N → ZMod 2)) (v : ((Fin N → ZMod
  2) × (Fin N → ZMod 2))) : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) :=
  ((swapAt H v).1, (swapAt H v).2 + fun i => d i * (swapAt H v).1 i)

private lemma tensor_clifford {N : ℕ} (H : Finset (Fin N)) (d : (Fin N → ZMod 2))
    (v : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) (f : (Fin N → ZMod 2) → ℂ) :
    ∃ r : ℂ, r ≠ 0 ∧
      (show Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ from tensorOp (fun i => gate (decide (i ∈
        H)) (d i))) *ᵥ
        weyl v f = r • weyl (symbolTransform H d v)
          ((show Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ from
            tensorOp (fun i => gate (decide (i ∈ H)) (d i))) *ᵥ f) := by
  classical
  let A := fun i => gate (decide (i ∈ H)) (d i)
  let v' := symbolTransform H d v
  have localLaw (i : Fin N) : ∃ r : ℂ, r ≠ 0 ∧
      A i * wmat (v.1 i) (v.2 i) = r • (wmat (v'.1 i) (v'.2 i) * A i) := by
    have h := gate_wmat (decide (i ∈ H)) (d i) (v.1 i) (v.2 i)
    by_cases hi : i ∈ H <;> simpa [A, v', symbolTransform, swapAt, hi] using h
  choose r hr he using localLaw
  have hm : tensorOp A * tensorOp (fun i => wmat (v.1 i) (v.2 i)) =
      (∏ i, r i) • (tensorOp (fun i => wmat (v'.1 i) (v'.2 i)) * tensorOp A) := by
    rw [tensor_mul, tensor_mul]
    rw [show (fun i => A i * wmat (v.1 i) (v.2 i)) =
      (fun i => r i • (wmat (v'.1 i) (v'.2 i) * A i)) from funext he, tensor_smul]
  let G : Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ := tensorOp A
  let W : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) → Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ :=
    fun u => tensorOp (fun i => wmat (u.1 i) (u.2 i))
  have hm' : G * W v = (∏ i, r i) • (W v' * G) := hm
  have hv := congrArg (fun M : Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ => M *ᵥ f) hm'
  have hw (u : ((Fin N → ZMod 2) × (Fin N → ZMod 2))) (g : (Fin N → ZMod 2) → ℂ) : W u *ᵥ g = weyl u
    g := tensor_weyl u g
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, hw] at hv
  exact ⟨∏ i, r i, Finset.prod_ne_zero_iff.mpr (fun i _ => hr i), hv⟩

private lemma stabilizer_graph_eigen {N : ℕ} (ψ : (Fin N → ZMod 2) → ℂ)
    (hψ : StabilizedBy pauliSet ψ) :
    ∃ (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
      (Γ : Matrix (Fin N) (Fin N) (ZMod 2)),
      (∀ i, A i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧ Γ.IsSymm ∧ (∀ i, Γ i i = 0) ∧
      ∀ i, ∃ a : ℂ, weyl (Pi.single i 1, Γ *ᵥ Pi.single i 1)
        ((show Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ from tensorOp A) *ᵥ ψ) =
        a • ((show Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ from tensorOp A) *ᵥ ψ) := by
  classical
  obtain ⟨k, v, c, hline⟩ := stabilizer_weyl ψ hψ
  obtain ⟨_, hiso, hdim, heigen⟩ := unique_weyl_line_lagrangian v c ψ hψ.1 hline
  let L := Submodule.span (ZMod 2) (Set.range v)
  obtain ⟨H, d, Γ, hs, hd, hgraph⟩ := lagrangian_graph_form L hiso hdim
  let A := fun i => gate (decide (i ∈ H)) (d i)
  refine ⟨A, Γ, fun i => gate_unitary _ _, hs, hd, ?_⟩
  intro i
  let q : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) := (Pi.single i 1, Γ *ᵥ Pi.single i 1)
  let w : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) := (q.1, q.2 + fun j => d j * q.1 j)
  let u := swapAt H w
  have htu : symbolTransform H d u = q := by
    unfold symbolTransform
    rw [show swapAt H u = w from swapAt_involutive H w]
    apply Prod.ext
    · rfl
    · funext j
      change (q.2 j + d j * q.1 j) + d j * q.1 j = q.2 j
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have humem : u ∈ L := (hgraph u).mpr (by
    change (symbolTransform H d u).2 = Γ *ᵥ (symbolTransform H d u).1
    rw [htu])
  obtain ⟨a, ha⟩ := (heigen u).mpr humem
  obtain ⟨r, hr, hh⟩ := tensor_clifford H d u ψ
  rw [htu, ha, Matrix.mulVec_smul] at hh
  refine ⟨r⁻¹ * a, ?_⟩
  rw [← smul_smul, eq_inv_smul_iff₀ hr]
  exact hh.symm

private lemma graph_sign_correction {N : ℕ}
    (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (hs : Γ.IsSymm) (hd : ∀ i, Γ i i = 0)
    (φ : (Fin N → ZMod 2) → ℂ) (hne : φ ≠ 0)
    (heigen : ∀ i, ∃ a : ℂ, weyl (Pi.single i 1, Γ *ᵥ Pi.single i 1) φ = a • φ) :
    ∃ (b : (Fin N → ZMod 2)) (c : ℂ), weyl (0, b) φ = c • graphAmp Γ := by
  classical
  choose a ha using heigen
  have square (i : Fin N) : a i * a i = 1 := by
    have h := weyl_square (Pi.single i 1, Γ *ᵥ Pi.single i 1) φ
    have hz : (∑ j, (Pi.single i (1 : ZMod 2) : (Fin N → ZMod 2)) j *
        (Γ *ᵥ Pi.single i 1) j) = 0 := by
      simp [Pi.single_apply, ite_mul, hd]
    rw [ha i, (weyl_linear _).2.1, ha i, smul_smul, hz,
      D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_zero] at h
    exact smul_left_injective ℂ hne h
  let b : (Fin N → ZMod 2) := fun i => if a i = 1 then 0 else 1
  have hb (i : Fin N) : complexSign (b i) = a i := by
    rcases mul_self_eq_one_iff.mp (square i) with h | h <;> norm_num [b, h, complexSign, F₂]
  refine ⟨b, (weyl (0, b) φ) 0, graph_fixed_line Γ hs hd _ ?_⟩
  intro i
  have hsp : sp (Pi.single i 1, Γ *ᵥ Pi.single i 1) (0, b) = b i := by
    simp [sp, Pi.single_apply, ite_mul]
  rw [weyl_commute, ha i, (weyl_linear (0, b)).2.1, smul_smul,
    hsp, hb, square, one_smul]

/-- Every nonzero Pauli stabilizer eigenline is a product of local unitaries applied to a
binary graph amplitude, up to an arbitrary complex scalar. -/
theorem stabilizer_graph_normal_form {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ)
    (hψ : StabilizedBy pauliSet ψ) :
    ∃ (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (c : ℂ),
      (∀ i, U i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧ Γ.IsSymm ∧ (∀ i, Γ i i = 0) ∧
      ψ = c • (tensorOp U *ᵥ graphAmp Γ) := by
  classical
  obtain ⟨A, Γ, hA, hs, hd, heigen⟩ := stabilizer_graph_eigen ψ hψ
  let G := tensorOp A
  let φ : (Fin N → ZMod 2) → ℂ := (show Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ from G) *ᵥ ψ
  have hG : G ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := tensor_unitary A hA
  have hinv : Gᴴ * G = 1 := Matrix.mem_unitaryGroup_iff'.mp hG
  have hne : φ ≠ 0 := by
    intro hz
    have hh : Gᴴ *ᵥ (G *ᵥ ψ) = ψ := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    change (show Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ from Gᴴ) *ᵥ φ = ψ at hh
    rw [hz, Matrix.mulVec_zero] at hh
    exact hψ.1 hh.symm
  obtain ⟨b, c, hfixed⟩ := graph_sign_correction Γ hs hd φ hne heigen
  let B := fun i => wmat 0 (b i)
  let U := fun i => (A i)ᴴ * B i
  have hU (i : Fin N) : U i ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    apply (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
    · exact Unitary.star_mem (hA i)
    · exact wmat_unitary 0 (b i)
  let T : Matrix ((Fin N → ZMod 2)) ((Fin N → ZMod 2)) ℂ := tensorOp B
  let g : (Fin N → ZMod 2) → ℂ := graphAmp Γ
  have hwB : T *ᵥ g = weyl (0, b) g := tensor_weyl (0, b) g
  have hfixed' : weyl (0, b) φ = c • g := hfixed
  have hφ : φ = c • (T *ᵥ g) := by
    calc
      φ = weyl (0, b) (weyl (0, b) φ) := by
        rw [weyl_square]
        simp [D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_zero]
      _ = weyl (0, b) (c • g) := congrArg (weyl (0, b)) hfixed'
      _ = c • weyl (0, b) g := (weyl_linear _).2.1 _ _
      _ = c • (T *ᵥ g) := congrArg (c • ·) hwB.symm
  have hφ' : G *ᵥ ψ = c • (tensorOp B *ᵥ graphAmp Γ) := hφ
  refine ⟨U, Γ, c, hU, hs, hd, ?_⟩
  calc
    ψ = Gᴴ *ᵥ (G *ᵥ ψ) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = c • (tensorOp U *ᵥ graphAmp Γ) := by
      rw [hφ', Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      change c • (((tensorOp A)ᴴ * tensorOp B) *ᵥ graphAmp Γ) = _
      rw [tensor_adj, tensor_mul]


end D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
