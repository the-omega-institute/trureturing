/- GID: D5/S3/Entropy/DoubleSidedBottleneckBSC
   generality: G
   mirror-B: D5/B/S3/Entropy/DoubleSidedBottleneckBSC
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact BSC optimality for every finite channel at low correlation. -/

/-
admission_basis: open-problem-resolution (#26680; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30706
The source entropy is the frozen binaryEntropyBits expression; no entropy alias is added.
Direct frozen dependencies: declaration identities at base fcd028003080ee51fe117e1277b6f3768c12b47a.
F1: D5/S3/Divergence/ChainRule.marginal; statement_id=sha256:dceda59c3d0878b0c3f2523a44ebc1eac8e993b60b5337d514272974eafd9e18
F2: D5/S3/Divergence/ClassicalDPI.channelOutput; statement_id=sha256:bb11b45a5bb58d49bd779aa75b68940ca4390a1dc69947eb5336eed0279521e5
F3: D5/S3/Divergence/ClassicalDPI.klDivergence; statement_id=sha256:5439abc1162340dc8a960e26ac9ec0e06ba733ba3a848aa4ce21aefc7592d01e
F4: D5/S3/Divergence/ClassicalDPI.posterior; statement_id=sha256:140509554790e73238329c5ce180a67cad5e010943e52f4de445dbd5d050cfb0
F5: D5/S3/Entropy/MaxEntropy.shannonEntropy; statement_id=sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87
F6: D5/S3/Entropy/MutualInformation.mutualInformation; statement_id=sha256:f23c55736018ea5fe356eea838c35e001592a5f37f3ecfdbd0ccf944b45bf7fb
F7: D5/S3/Entropy/MutualInformationProduct.mutual_information_product_eq_zero; statement_id=sha256:fb1662e5f72b135780e9503d18aa6a2efd045eddf99bc3403804384352cd8acc
F8: D5/S3/Entropy/MutualInformationSymm.mutual_information_symm; statement_id=sha256:0fddd5288477a64573448cde5ef886f056ad4e843fd79fcc85085abc66fdfd95
F9: D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.expectedPosteriorEntropy; statement_id=sha256:ab8826faa9b59829d03b666f3a30689a5adf3778a60dfcb31ce1f4ba75b1b1c8
F10: D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.experimentJointLaw; statement_id=sha256:120c4ed051eeb8d6130aad81cd97e40f364cc5439348dcd59e069002ece58115
F11: D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.informationGain; statement_id=sha256:892ded2f9f2b8b0fa1a99c9931328df346766b195a372b52869a22a23c0bbc82
F12: D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.information_gain_eq_expected_entropy_reduction; statement_id=sha256:f9ed4f8563d80f353a2786d77108a801fdae47732beaea980ed7c33154f6c6ec
F13: D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining.hRenyi; statement_id=sha256:636915c800a5648e56b5294f58b06369992cc982bf213f54a2a480ce21cdaa80
F14: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.G; statement_id=sha256:d1ff0db76bb2dfaa6596159064f6a606f280fc28d1c49bf6c4ee450962658ff9
F15: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.bias_combining; statement_id=sha256:eef238dadb2dfd4ce9a0d4b15fdf070897e2f3ed022818652c6f1c3a598baef1
F16: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.claim; statement_id=sha256:ded331dfdefcb77a0fa5dbe2d45ab5bf7968446ef0ef8bda9ee91f45b526da35
F17: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.h; statement_id=sha256:284a16083fa547c8718507bae385b0542ebd97fc49aabbbf330bb0e75b8e75dc
F18: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.hInv; statement_id=sha256:fb70e873439c6eceb2ae437f09d7e70aebb758bc79aaf0b20ccc815ee81d6812
F19: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.hInv_h; statement_id=sha256:d5aff0666b4aaed97a04309960a4fd6d7fc87f5999865a4ca46ebe22ea955788
F20: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.inverseBias; statement_id=sha256:8365f896cd4b1b31312c1744a24b445824ff33f05c5cb0af1346a07da92f84b9
F21: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.inverseBias_anti; statement_id=sha256:27e03d50785a2f6756ac100319e342d53e1a32ae6b1364e3177487d523ade93d
F22: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.inverseBias_spec; statement_id=sha256:d75dcc8f622f4b47be37a0ff7f14a516aab2a7e9508af6a7888a67adfc56dc55
F23: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.psi; statement_id=sha256:98d07665dfc5cc8eb46c5fe709180e6272444219bdc3cac606e1fd6976e3f606
F24: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.psi_strictAntiOn; statement_id=sha256:c5e3d7a4c44bf353afbfb0d9b9cc5a66f0ef66ff79c11a6a15d0bedd8eec1b9d
F25: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.result; statement_id=sha256:39350541096004184d8e4a752e70f2a4e97a5f72d5cd0662ed71a50f035df133
F26: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.star; statement_id=sha256:502852e1de45ca3e72b52dc5c212135444ff0e0bf03a649ed22feb27a0f66056
F27: D5/S3/Entropy/Submodularity/MarkovDataProcessing.markov_of_channel; statement_id=sha256:20058f89b2ec5c4f19e9272fe12ebb03b1852225435ce570dfe7c636ecac9d7d
F28: D5/S3/Entropy/Submodularity/MarkovDataProcessing.mutual_information_le_of_markov; statement_id=sha256:bc1aae6cfaee7a13325116d25cfe364fadf4433f2c1a92c129458a5650783afa
F29: D5/S3/Entropy/Submodularity/MarkovDataProcessing.yFirstLaw; statement_id=sha256:3a9eaa59d1c60c221065f7c30c06c9405f81f571de2a78ab234f78fb309a30de
F30: D5/S3/Entropy/Submodularity/StrongSubadditivity.xyProjection; statement_id=sha256:921d1bab0e37c1918409c74ae3fe63677a151848772ae5a8449222dcaf16c945
F31: D5/S3/Entropy/Submodularity/StrongSubadditivity.xzProjection; statement_id=sha256:ad9cf98a95172d85e0406a94c9c8ed29a0137fa6bae14d85f0116b3a56de8db6
F32: D5/S3/Quantum/CloningMachine.binaryEntropyBits; statement_id=sha256:688128ab90010a81f7deda9f09bce484b31dd0c87b4be4eba0ee15f631995292
F33: D5/S3/Quantum/Information/QubitEntropyContraction.logRatio; statement_id=sha256:bb9ddc35fc615b4ef0c2ef184ee0b38420a2fea66b80854ce40df89141cdfd1e
F34: D5/S3/Quantum/Information/QubitEntropyContraction.radialEntropy; statement_id=sha256:7a1844d69160c7cdadf8d7d90c10352564fffc2c16ba40e815a355ebc8bc8ebd
F35: D5/S3/Quantum/Information/QubitEntropyContraction.radial_concave; statement_id=sha256:8026c9153902c93bfa1487395d7f93f3268e56ab78a89faa6aa82ebcb253cff0
F36: D5/S3/Quantum/Information/QubitEntropyContraction.radial_deriv; statement_id=sha256:e8867f89ff5d6dbfe903566df6ee22ac61ad20b965100eb78500fcd8a1d28307
F37: D5/S3/Quantum/Information/QubitEntropyContraction.radial_deriv2; statement_id=sha256:0d6c93f85b7e4c54a6cc869eee6cc53e301d2b85b55ae58405f8953d16d69a2a
F38: D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.pmfRealMass_sum; statement_id=sha256:e454f4ffe7f8278bdd1d7328ffaffa03673012acaec70317ba0cacde6a5b2daf
Declarations (frozen inputs above are followed through same-delivery helpers):
hbInv: proof_shape: bind-only; escape_witness: none; dependencies: F32; consumers: bscOptimal,bscOptimal_of_upper_bound,candidate_bias_interior,candidate_rate,claim,full_budget_bscOptimal,full_budget_upper,hbInv_zero,hb_inv_spec,interior_bscOptimal,result,zero_budget_bscOptimal
dsbs: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: objective_le_noiseless,outputJoint,output_joint_nonneg,output_joint_posterior
bsc: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: bscOptimal,bscOptimal_of_upper_bound,bsc_apply_formula,candidate_rate,full_budget_bscOptimal,full_budget_upper,interior_bscOptimal,objective_bsc_productValue,objective_le_noiseless,objective_noiseless_formula,output_mass_bsc,posterior_bias_bsc,rate_bsc,zero_budget_bscOptimal
mutualInformationBits: proof_shape: bind-only; escape_witness: none; dependencies: F6; consumers: objective,objective_product_formula,objective_symm,objective_zero_of_bias_zero,rate,rate_bsc,rate_posterior_formula
rate: proof_shape: bind-only; escape_witness: none; dependencies: F6; consumers: achievable,bias_zero_of_rate_nonpos,bscOptimal,bscOptimal_of_upper_bound,candidate_rate,full_budget_bscOptimal,full_budget_upper,interior_bscOptimal,rate_bsc,rate_phi,rate_posterior_formula,zero_budget_bscOptimal
outputJoint: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: objective,objective_le_noiseless,objective_product_formula,objective_symm,objective_zero_of_bias_zero,output_joint_col_sum,output_joint_nonneg,output_joint_posterior,output_joint_row_sum
objective: proof_shape: bind-only; escape_witness: none; dependencies: F6; consumers: achievable,bscOptimal,bscOptimal_of_upper_bound,full_budget_bscOptimal,full_budget_upper,interior_bscOptimal,objective_bsc_productValue,objective_le_noiseless,objective_noiseless_formula,objective_productValue,objective_product_formula,objective_symm,objective_zero_of_bias_zero,zero_budget_bscOptimal
achievable: proof_shape: bind-only; escape_witness: none; dependencies: F6; consumers: R,bscOptimal_of_upper_bound
R: proof_shape: bind-only; escape_witness: none; dependencies: F6; consumers: bscOptimal,bscOptimal_of_upper_bound
bscOptimal: proof_shape: bind-only; escape_witness: none; dependencies: F6,F32; consumers: bscOptimal_of_upper_bound,claim,full_budget_bscOptimal,interior_bscOptimal,result,zero_budget_bscOptimal
claim: proof_shape: bind-only; escape_witness: none; dependencies: F32,F6; consumers: result
posteriorBias: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: bias_zero_of_rate_nonpos,full_budget_upper,interior_bscOptimal,mass_mul_bias,objective_bsc_productValue,objective_noiseless_formula,objective_productValue,objective_product_formula,objective_symm,objective_zero_of_bias_zero,output_joint_col_sum,output_joint_posterior,output_joint_row_sum,posterior_bias_bsc,posterior_bias_centered,posterior_bias_mem,rate_phi,rate_posterior_formula,zero_budget_bscOptimal
kernel_real_sum: proof_shape: bind-only; escape_witness: none; dependencies: F38; consumers: objective_le_noiseless,output_mass_probability,posterior_bias_centered,rate_posterior_formula
output_mass_probability: proof_shape: bind-only; escape_witness: none; dependencies: F38; consumers: bias_zero_of_rate_nonpos,full_budget_upper,interior_bscOptimal,objective_le_noiseless,objective_zero_of_bias_zero,output_joint_col_sum,output_joint_row_sum,rate_posterior_formula
posterior_bias_mem: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: bias_zero_of_rate_nonpos,full_budget_upper,interior_bscOptimal
mass_mul_bias: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: output_joint_posterior,posterior_bias_bsc,posterior_bias_centered
posterior_bias_centered: proof_shape: bind-only; escape_witness: none; dependencies: F38; consumers: interior_bscOptimal,output_joint_col_sum,output_joint_row_sum
output_joint_posterior: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: objective_product_formula,objective_symm,objective_zero_of_bias_zero,output_joint_col_sum,output_joint_row_sum
output_joint_row_sum: proof_shape: bind-only; escape_witness: none; dependencies: F38; consumers: objective_product_formula
output_joint_col_sum: proof_shape: bind-only; escape_witness: none; dependencies: F38; consumers: objective_le_noiseless,objective_product_formula
objective_product_formula: proof_shape: bind-only; escape_witness: none; dependencies: F6,F3,F1,F38; consumers: objective_productValue
rate_posterior_formula: proof_shape: bind-only; escape_witness: none; dependencies: F2,F11,F6,F10,F8,F5,F4,F9,F12,F38; consumers: rate_phi
hb_binEntropy: proof_shape: bind-only; escape_witness: none; dependencies: F32; consumers: candidate_bias_interior,hbInv_zero,hb_inv_spec,phi_crossover
hb_inv_spec: proof_shape: bind-only; escape_witness: none; dependencies: F32; consumers: candidate_bias_interior,candidate_rate,full_budget_upper,hbInv_zero,interior_bscOptimal,result
bsc_apply_formula: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: objective_le_noiseless,output_mass_bsc,posterior_bias_bsc,rate_bsc
rate_bsc: proof_shape: bind-only; escape_witness: none; dependencies: F32,F6,F3,F1; consumers: candidate_rate
candidate_rate: proof_shape: bind-only; escape_witness: none; dependencies: F32,F6,F3,F1; consumers: bscOptimal_of_upper_bound,zero_budget_bscOptimal
bscOptimal_of_upper_bound: proof_shape: bind-only; escape_witness: none; dependencies: F6,F32,F3,F1; consumers: full_budget_bscOptimal,interior_bscOptimal,zero_budget_bscOptimal
phi_bias: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: phi_crossover,phi_f,rate_phi
rate_phi: proof_shape: bind-only; escape_witness: none; dependencies: F2,F11,F6,F10,F8,F5,F4,F9,F12,F38; consumers: bias_zero_of_rate_nonpos,full_budget_upper,interior_bscOptimal
phi_crossover: proof_shape: bind-only; escape_witness: none; dependencies: F32; consumers: full_budget_upper,interior_bscOptimal
output_mass_bsc: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: full_budget_upper,objective_bsc_productValue,objective_noiseless_formula,posterior_bias_bsc
posterior_bias_bsc: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: full_budget_upper,objective_bsc_productValue,objective_noiseless_formula
objective_productValue: proof_shape: bind-only; escape_witness: none; dependencies: F6,F3,F1,F38; consumers: interior_bscOptimal,objective_bsc_productValue,objective_noiseless_formula
objective_bsc_productValue: proof_shape: bind-only; escape_witness: none; dependencies: F6,F3,F1,F38; consumers: interior_bscOptimal
candidate_bias_interior: proof_shape: bind-only; escape_witness: none; dependencies: F32; consumers: interior_bscOptimal
interior_bscOptimal: proof_shape: content; escape_witness: none; dependencies: F32,F6,F3,F1,F33,F34,F36,F35,F37,F2,F11,F10,F8,F5,F4,F9,F12,F38; consumers: result
bias_zero_of_rate_nonpos: proof_shape: bind-only; escape_witness: none; dependencies: F35,F2,F11,F6,F10,F8,F5,F4,F9,F12,F38; consumers: zero_budget_bscOptimal
objective_zero_of_bias_zero: proof_shape: bind-only; escape_witness: none; dependencies: F6,F7,F38; consumers: zero_budget_bscOptimal
zero_budget_bscOptimal: proof_shape: bind-only; escape_witness: none; dependencies: F32,F6,F3,F1,F35,F2,F11,F10,F8,F5,F4,F9,F12,F7,F38; consumers: result
Boundary.combining_monotone: proof_shape: bind-only; escape_witness: none; dependencies: F14,F20,F23,F22,F21,F15,F24; consumers: Boundary.scalar_mgl
Boundary.combining_bias: proof_shape: bind-only; escape_witness: none; dependencies: F14,F23,F17,F26,F18,F19; consumers: Boundary.scalar_mgl
Boundary.phi_psi: proof_shape: bind-only; escape_witness: none; dependencies: F23,F13; consumers: Boundary.scalar_mgl
Boundary.scalar_mgl: proof_shape: bind-only; escape_witness: none; dependencies: F23,F13,F14,F16,F25,F17,F26,F18,F19,F20,F22,F21,F15,F24; consumers: full_budget_upper
phi_f: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: objective_noiseless_formula
output_joint_nonneg: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: objective_le_noiseless
objective_symm: proof_shape: bind-only; escape_witness: none; dependencies: F6,F8; consumers: full_budget_bscOptimal
noiseless: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: full_budget_upper,hbInv_zero,objective_le_noiseless,objective_noiseless_formula
objective_le_noiseless: proof_shape: bind-only; escape_witness: none; dependencies: F30,F31,F1,F29,F27,F6,F28,F8,F38; consumers: full_budget_upper
objective_noiseless_formula: proof_shape: bind-only; escape_witness: none; dependencies: F6,F3,F1,F38; consumers: full_budget_upper
hbInv_zero: proof_shape: bind-only; escape_witness: none; dependencies: F32; consumers: full_budget_upper
full_budget_upper: proof_shape: bind-only; escape_witness: none; dependencies: F32,F30,F31,F1,F29,F27,F6,F28,F8,F3,F23,F13,F14,F16,F25,F17,F26,F18,F19,F20,F22,F21,F15,F24,F2,F11,F10,F5,F4,F9,F12,F38; consumers: full_budget_bscOptimal
full_budget_bscOptimal: proof_shape: bind-only; escape_witness: none; dependencies: F6,F8,F32,F30,F31,F1,F29,F27,F28,F3,F23,F13,F14,F16,F25,F17,F26,F18,F19,F20,F22,F21,F15,F24,F2,F11,F10,F5,F4,F9,F12,F38; consumers: result
result: proof_shape: content; escape_witness: none; dependencies: F32,F6,F3,F1,F33,F34,F36,F35,F37,F2,F11,F10,F8,F5,F4,F9,F12,F30,F31,F29,F27,F28,F23,F13,F14,F16,F25,F17,F26,F18,F19,F20,F22,F21,F15,F24,F7,F38; consumers: terminal result
Definitions specify objects, not proof claims; their bind-only label claims no new theorem.
The settling result uses the posterior moment estimate and includes all budget endpoints.
-/

import D5.S3.Divergence.ChainRule
import D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining
import D5.S3.Divergence.ClassicalDPI
import D5.S3.Entropy.MaxEntropy
import D5.S3.Entropy.DoubleSidedBottleneckMoments
import D5.S3.Entropy.Observation.ExpectedPosteriorEntropyReduction
import D5.S3.Entropy.MutualInformationSymm
import D5.S3.Entropy.MutualInformation
import D5.S3.Quantum.CloningMachine
import D5.S3.Entropy.MutualInformationProduct
import D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
import D5.S3.Entropy.Submodularity.MarkovDataProcessing
import D5.S3.Entropy.Submodularity.StrongSubadditivity
import D5.S3.Observer.ProductMeasures.FinitePmfLikelihood



namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

open scoped BigOperators

noncomputable def hbInv (y : ℝ) : (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :=
  letI : Nonempty (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := ⟨⟨0, by norm_num⟩⟩
  Function.invFun (fun a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) => D5.S3.Quantum.CloningMachine.binaryEntropyBits a.val) y

noncomputable def dsbs (p : ℝ) (xy : Bool × Bool) : ℝ :=
  (if xy.1 = xy.2 then 1 - p else p) / 2

noncomputable def bsc (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) : (Bool → PMF (Fin 2)) :=
  let q : NNReal := ⟨a.val, a.property.1⟩
  have hq : q ≤ 1 := by
    change a.val ≤ 1
    linarith [a.property.2]
  fun x => (PMF.ofFintype (fun z : Bool => (↑(cond z q (1 - q)) : ENNReal))
    (by simp [hq])).map (fun z => if Bool.xor x z then (1 : Fin 2) else 0)

noncomputable def mutualInformationBits {A B : Type} [Fintype A] [Fintype B]
    (q : A × B → ℝ) : ℝ :=
  D5.S3.Entropy.MutualInformation.mutualInformation q / Real.log 2

noncomputable def rate {n : ℕ} (K : (Bool → PMF (Fin n))) : ℝ :=
  mutualInformationBits (fun xu : Bool × Fin n => (K xu.1 xu.2).toReal / 2)

noncomputable def outputJoint {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (uv : Fin n × Fin m) : ℝ :=
  ∑ x : Bool, ∑ y : Bool,
    dsbs p (x, y) * (K x uv.1).toReal * (L y uv.2).toReal

noncomputable def objective {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) : ℝ :=
  mutualInformationBits (outputJoint p K L)

noncomputable def achievable (Cu Cv p : ℝ) : Set EReal :=
  {r | ∃ (n m : ℕ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))),
    rate K ≤ Cu ∧ rate L ≤ Cv ∧ r = (objective p K L : EReal)}

noncomputable def R (Cu Cv p : ℝ) : EReal := sSup (achievable Cu Cv p)

noncomputable def bscOptimal (Cu Cv p : ℝ) : Prop :=
  rate (bsc (hbInv (1 - Cu))) ≤ Cu ∧
  rate (bsc (hbInv (1 - Cv))) ≤ Cv ∧
  R Cu Cv p =
    (objective p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv))) : EReal)

def claim : Prop :=
  ∀ Cu : ℝ, 0 ≤ Cu → Cu ≤ 1 →
    ∀ Cv : ℝ, 0 ≤ Cv → Cv ≤ 1 →
      D5.S3.Quantum.CloningMachine.binaryEntropyBits (hbInv (1 - Cu)).val = 1 - Cu ∧
      D5.S3.Quantum.CloningMachine.binaryEntropyBits (hbInv (1 - Cv)).val = 1 - Cv ∧
      ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 / 2 ∧
        ∀ p : ℝ, 0 ≤ p → p ≤ 1 / 2 → θ < p → bscOptimal Cu Cv p

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

private noncomputable def posteriorBias {n : ℕ} (K : (Bool → PMF (Fin n))) (u : Fin n) : ℝ :=
  ((K false u).toReal - (K true u).toReal) /
    ((K false u).toReal + (K true u).toReal)

private theorem kernel_real_sum {n : ℕ} (K : (Bool → PMF (Fin n))) (x : Bool) :
    ∑ u, (K x u).toReal = 1 := by
  simpa only [D5.S3.Observer.ProductMeasures.FinitePmfLikelihood.pmfRealMass] using
    (D5.S3.Observer.ProductMeasures.FinitePmfLikelihood.pmfRealMass_sum
      (Output := fun _ => Fin n) (i := 0) (K x))

private theorem output_mass_probability {n : ℕ} (K : (Bool → PMF (Fin n))) :
    (∀ u, 0 ≤ (fun w => ((K false w).toReal + (K true w).toReal) / 2) u) ∧ ∑ u, (fun w => ((K false w).toReal + (K true w).toReal) / 2) u = 1 := by
  constructor
  · intro u; exact div_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (by norm_num)
  · simp only [← Finset.sum_div, Finset.sum_add_distrib,
      kernel_real_sum]
    norm_num

private theorem posterior_bias_mem {n : ℕ} (K : (Bool → PMF (Fin n))) (u : Fin n) :
    posteriorBias K u ∈ Set.Icc (-1 : ℝ) 1 := by
  have ha : 0 ≤ (K false u).toReal := ENNReal.toReal_nonneg
  have hbHyp : 0 ≤ (K true u).toReal := ENNReal.toReal_nonneg
  by_cases hzero : (K false u).toReal + (K true u).toReal = 0
  · simp [posteriorBias, hzero]
  · have hpos : 0 < (K false u).toReal + (K true u).toReal :=
      lt_of_le_of_ne (add_nonneg ha hbHyp) (Ne.symm hzero)
    constructor
    · exact (le_div_iff₀ hpos).mpr (by linarith)
    · exact (div_le_iff₀ hpos).mpr (by linarith)

private theorem mass_mul_bias {n : ℕ} (K : (Bool → PMF (Fin n))) (u : Fin n) :
    (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * posteriorBias K u =
      ((K false u).toReal - (K true u).toReal) / 2 := by
  have ha : 0 ≤ (K false u).toReal := ENNReal.toReal_nonneg
  have hbHyp : 0 ≤ (K true u).toReal := ENNReal.toReal_nonneg
  by_cases hzero : (K false u).toReal + (K true u).toReal = 0
  · have ha0 : (K false u).toReal = 0 := by linarith
    have hb0 : (K true u).toReal = 0 := by exact (eq_zero_iff_eq_zero_of_add_eq_zero hzero).mp ha0
    simp [posteriorBias, ha0, hb0]
  · dsimp [posteriorBias]
    field_simp [hzero]

private theorem posterior_bias_centered {n : ℕ} (K : (Bool → PMF (Fin n))) :
    ∑ u, (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * posteriorBias K u = 0 := by
  simp only [mass_mul_bias, ← Finset.sum_div, Finset.sum_sub_distrib, kernel_real_sum]
  norm_num

private theorem output_joint_posterior {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (u : Fin n) (v : Fin m) :
    outputJoint p K L (u, v) = (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * (fun w => ((L false w).toReal + (L true w).toReal) / 2) v *
      (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v) := by
  have hK := mass_mul_bias K u
  have hL := mass_mul_bias L v
  calc
    outputJoint p K L (u, v) = (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * (fun w => ((L false w).toReal + (L true w).toReal) / 2) v +
        (1 - 2 * p) *
          (((K false u).toReal - (K true u).toReal) / 2) *
          (((L false v).toReal - (L true v).toReal) / 2) := by
      simp [outputJoint, dsbs]
      ring
    _ = _ := by rw [← hK, ← hL]; ring

private theorem output_joint_row_sum {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (u : Fin n) :
    ∑ v, outputJoint p K L (u, v) = (fun w => ((K false w).toReal + (K true w).toReal) / 2) u := by
  simp_rw [output_joint_posterior]
  have hf (v : Fin m) : (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * (fun w => ((L false w).toReal + (L true w).toReal) / 2) v *
      (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v) =
      (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * (fun w => ((L false w).toReal + (L true w).toReal) / 2) v +
      ((1 - 2 * p) * (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * posteriorBias K u) *
        ((fun w => ((L false w).toReal + (L true w).toReal) / 2) v * posteriorBias L v) := by ring
  simp_rw [hf]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    (output_mass_probability L).2, posterior_bias_centered L]
  ring

private theorem output_joint_col_sum {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (v : Fin m) :
    ∑ u, outputJoint p K L (u, v) = (fun w => ((L false w).toReal + (L true w).toReal) / 2) v := by
  simp_rw [output_joint_posterior]
  have hf (u : Fin n) : (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * (fun w => ((L false w).toReal + (L true w).toReal) / 2) v *
      (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v) =
      (fun w => ((L false w).toReal + (L true w).toReal) / 2) v * (fun w => ((K false w).toReal + (K true w).toReal) / 2) u +
      ((1 - 2 * p) * (fun w => ((L false w).toReal + (L true w).toReal) / 2) v * posteriorBias L v) *
        ((fun w => ((K false w).toReal + (K true w).toReal) / 2) u * posteriorBias K u) := by ring
  simp_rw [hf]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    (output_mass_probability K).2, posterior_bias_centered K]
  ring

private theorem objective_product_formula {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) :
    objective p K L =
      (∑ u, ∑ v, (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * (fun w => ((L false w).toReal + (L true w).toReal) / 2) v *
        (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v) *
        Real.log (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v)) / Real.log 2 := by
  unfold objective mutualInformationBits
    D5.S3.Entropy.MutualInformation.mutualInformation
    D5.S3.Divergence.ClassicalDPI.klDivergence
  simp only [D5.S3.Divergence.ChainRule.marginal, output_joint_row_sum,
    output_joint_col_sum, Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [output_joint_posterior]
  by_cases h : (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * (fun w => ((L false w).toReal + (L true w).toReal) / 2) v = 0
  · simp [h]
  · rw [mul_div_cancel_left₀ _ h]

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Observation.ExpectedPosteriorEntropyReduction
open D5.S3.Entropy.MutualInformationSymm

private theorem rate_posterior_formula {n : ℕ} (K : (Bool → PMF (Fin n))) :
    rate K = (∑ u, (fun w => ((K false w).toReal + (K true w).toReal) / 2) u *
      (Real.log 2 - Real.binEntropy ((1 + posteriorBias K u) / 2))) / Real.log 2 := by
  let c : Bool → Fin n → ℝ := fun x u => (K x u).toReal
  let prior : Bool → ℝ := fun _ => 1 / 2
  have hmass (u : Fin n) : channelOutput c prior u = (fun w => ((K false w).toReal + (K true w).toReal) / 2) u := by
    simp [channelOutput, prior, c]
    ring
  have hgain : informationGain c prior =
      D5.S3.Entropy.MutualInformation.mutualInformation
        (fun xu : Bool × Fin n => (K xu.1 xu.2).toReal / 2) := by
    unfold informationGain experimentJointLaw
    convert mutual_information_symm
      (fun xu : Bool × Fin n => (K xu.1 xu.2).toReal / 2) using 1
    congr 1
    funext ux
    dsimp [c, prior]
    ring
  have hprior : shannonEntropy prior = Real.log 2 := by
    calc
      _ = Real.binEntropy (2⁻¹ : ℝ) := by
        norm_num [shannonEntropy, prior, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
        <;> ring
      _ = _ := Real.binEntropy_two_inv
  have hpoint (u : Fin n) : (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * shannonEntropy (posterior c prior u) =
      (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * Real.binEntropy ((1 + posteriorBias K u) / 2) := by
    by_cases hz : (fun w => ((K false w).toReal + (K true w).toReal) / 2) u = 0
    · simp [hz]
    · have hd : (K false u).toReal + (K true u).toReal ≠ 0 := by
        intro h
        apply hz
        simp [h]
      have hfalse : posterior c prior u false = (1 + posteriorBias K u) / 2 := by
        simp only [posterior, hmass, c, prior, posteriorBias]
        field_simp [hd]
        <;> ring
      have htrue : posterior c prior u true = 1 - (1 + posteriorBias K u) / 2 := by
        simp only [posterior, hmass, c, prior, posteriorBias]
        field_simp [hd]
        <;> ring
      simp only [shannonEntropy, Fintype.sum_bool, hfalse, htrue,
        Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      ring
  have h := information_gain_eq_expected_entropy_reduction c prior
    (fun u x => mul_nonneg (by norm_num [prior]) ENNReal.toReal_nonneg)
    (fun x => kernel_real_sum K x)
  rw [hgain, hprior] at h
  unfold expectedPosteriorEntropy at h
  simp_rw [hmass, hpoint] at h
  unfold rate mutualInformationBits
  congr 1
  rw [h]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (output_mass_probability K).2, one_mul]

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

private theorem hb_binEntropy (a : ℝ) : D5.S3.Quantum.CloningMachine.binaryEntropyBits a = Real.binEntropy a / Real.log 2 := by
  simp only [D5.S3.Quantum.CloningMachine.binaryEntropyBits,
    Real.logb, Real.binEntropy, Real.log_inv]
  ring

private theorem hb_inv_spec (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    D5.S3.Quantum.CloningMachine.binaryEntropyBits (hbInv y).val = y := by
  have hc : Continuous D5.S3.Quantum.CloningMachine.binaryEntropyBits := by
    simp_rw [show D5.S3.Quantum.CloningMachine.binaryEntropyBits = fun a => Real.binEntropy a / Real.log 2 by funext a; exact hb_binEntropy a]
    exact Real.binEntropy_continuous.div_const _
  have h0 : D5.S3.Quantum.CloningMachine.binaryEntropyBits 0 = 0 := by rw [hb_binEntropy]; simp
  have h1 : D5.S3.Quantum.CloningMachine.binaryEntropyBits (1 / 2) = 1 := by
    rw [hb_binEntropy]
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
    exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hy' : y ∈ Set.Icc (D5.S3.Quantum.CloningMachine.binaryEntropyBits 0) (D5.S3.Quantum.CloningMachine.binaryEntropyBits (1 / 2)) := by rwa [h0, h1]
  obtain ⟨a, ha, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hc.continuousOn hy'
  letI : Nonempty (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := ⟨⟨0, by norm_num⟩⟩
  unfold hbInv
  exact Function.invFun_eq (f := fun a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) => D5.S3.Quantum.CloningMachine.binaryEntropyBits a.val) ⟨⟨a, ha⟩, he⟩

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

private theorem bsc_apply_formula (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) (x : Bool) (u : Fin 2) :
    (bsc a x u).toReal = if u = (if x then (1 : Fin 2) else 0) then 1 - a.val else a.val := by
  have hq : (⟨a.val, a.property.1⟩ : NNReal) ≤ 1 := by
    change a.val ≤ 1
    linarith [a.property.2]
  cases x <;> fin_cases u <;>
    simp [bsc, PMF.map_apply, tsum_fintype, Finset.sum_filter, Bool.cond_true, Bool.cond_false, hq, NNReal.coe_sub] <;>
    first | rfl | exact NNReal.coe_sub hq

private theorem rate_bsc (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) : rate (bsc a) = 1 - D5.S3.Quantum.CloningMachine.binaryEntropyBits a.val := by
  have hloga : a.val = 0 ∨ 0 < a.val := Or.imp Eq.symm id (eq_or_lt_of_le a.property.1)
  have hcomp : 0 < 1 - a.val := by linarith [a.property.2]
  unfold rate mutualInformationBits
    D5.S3.Entropy.MutualInformation.mutualInformation
    D5.S3.Divergence.ClassicalDPI.klDivergence D5.S3.Divergence.ChainRule.marginal
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two, bsc_apply_formula]
  norm_num
  have hhalf1 : a.val / 2 + (1 - a.val) / 2 = 1 / 2 := by ring
  have hhalf2 : (1 - a.val) / 2 + a.val / 2 = 1 / 2 := by ring
  simp only [hhalf1, hhalf2,
    show a.val / 2 / ((1 / 2 : ℝ) * (1 / 2)) = 2 * a.val by ring,
    show (1 - a.val) / 2 / ((1 / 2 : ℝ) * (1 / 2)) = 2 * (1 - a.val) by ring]
  rcases hloga with ha | ha
  · simp [ha, D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb]
    field_simp
    <;> ring
  · have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hcomp.ne']
    simp only [D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb]
    field_simp
    <;> ring

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

private theorem candidate_rate {C : ℝ} (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    rate (bsc (hbInv (1 - C))) = C := by
  rw [rate_bsc, hb_inv_spec (1 - C) ⟨by linarith, by linarith⟩]
  ring

private theorem bscOptimal_of_upper_bound {Cu Cv p : ℝ}
    (hCu0 : 0 ≤ Cu) (hCu1 : Cu ≤ 1) (hCv0 : 0 ≤ Cv) (hCv1 : Cv ≤ 1)
    (hupper : ∀ (n m : ℕ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))),
      rate K ≤ Cu → rate L ≤ Cv →
      objective p K L ≤ objective p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv)))) :
    bscOptimal Cu Cv p := by
  have hK := (candidate_rate hCu0 hCu1).le
  have hL := (candidate_rate hCv0 hCv1).le
  refine ⟨hK, hL, le_antisymm ?_ ?_⟩
  · apply sSup_le
    rintro r ⟨n, m, K, L, hKr, hLr, rfl⟩
    exact_mod_cast hupper n m K L hKr hLr
  · apply le_sSup
    exact ⟨2, 2, bsc (hbInv (1 - Cu)), bsc (hbInv (1 - Cv)), hK, hL, rfl⟩

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature Series
open scoped BigOperators

private theorem phi_bias (s : ℝ) :
    phi (s ^ 2) = Real.log 2 - Real.binEntropy ((1 + s) / 2) := by
  rw [phi, Real.sqrt_sq_eq_abs]
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs]
  · rw [abs_of_neg (lt_of_not_ge hs),
      show (1 + -s) / 2 = 1 - (1 + s) / 2 by ring, Real.binEntropy_one_sub]

private theorem rate_phi {n : ℕ} (K : (Bool → PMF (Fin n))) :
    rate K = dotProduct ((fun w => ((K false w).toReal + (K true w).toReal) / 2)) (fun u => phi (posteriorBias K u ^ 2)) / Real.log 2 := by
  simp only [rate_posterior_formula, dotProduct, phi_bias]

private theorem phi_crossover (a : ℝ) :
    phi ((1 - 2 * a) ^ 2) = (1 - D5.S3.Quantum.CloningMachine.binaryEntropyBits a) * Real.log 2 := by
  rw [phi_bias, show (1 + (1 - 2 * a)) / 2 = 1 - a by ring,
    Real.binEntropy_one_sub, hb_binEntropy]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

private theorem output_mass_bsc (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) (u : Fin 2) : (fun w => (((bsc a) false w).toReal + ((bsc a) true w).toReal) / 2) u = 1 / 2 := by
  fin_cases u <;> norm_num [bsc_apply_formula] <;> ring

private theorem posterior_bias_bsc (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) (u : Fin 2) :
    posteriorBias (bsc a) u = if u = 0 then 1 - 2 * a.val else -(1 - 2 * a.val) := by
  have h := mass_mul_bias (bsc a) u
  rw [output_mass_bsc] at h
  fin_cases u <;> norm_num [bsc_apply_formula] at * <;> linarith

private theorem objective_productValue {n m : ℕ} (p : ℝ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) :
    objective p K L =
      productValue (1 - 2 * p) ((fun w => ((K false w).toReal + (K true w).toReal) / 2)) (posteriorBias K) ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (posteriorBias L) /
        Real.log 2 := by
  rw [objective_product_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  dsimp [productValue, Real.negMulLog]
  ring

private theorem objective_bsc_productValue (p : ℝ) (a b : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) :
    objective p (bsc a) (bsc b) =
      productValue (1 - 2 * p) half (signed (1 - 2 * a.val)) half (signed (1 - 2 * b.val)) /
        Real.log 2 := by
  rw [objective_productValue]
  congr 1
  simp only [productValue, Fin.sum_univ_two, output_mass_bsc, posterior_bias_bsc,
    Fintype.sum_bool, half, signed]
  norm_num <;> ring_nf

private theorem candidate_bias_interior {C : ℝ} (hC0 : 0 < C) (hC1 : C < 1) :
    (1 - 2 * (hbInv (1 - C)).val) ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  let a := hbInv (1 - C)
  have ha := a.property
  have he : D5.S3.Quantum.CloningMachine.binaryEntropyBits a.val = 1 - C := hb_inv_spec _ ⟨by linarith, by linarith⟩
  have hzero : D5.S3.Quantum.CloningMachine.binaryEntropyBits (0 : ℝ) = 0 := by rw [hb_binEntropy]; simp
  have hhalf : D5.S3.Quantum.CloningMachine.binaryEntropyBits (1 / 2 : ℝ) = 1 := by
    rw [hb_binEntropy, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
    exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have ha0 : 0 < a.val := by
    by_contra h
    have hz : a.val = 0 := by linarith [ha.1]
    rw [hz, hzero] at he
    linarith
  have ha1 : a.val < 1 / 2 := by
    by_contra h
    have hz : a.val = 1 / 2 := by linarith [ha.2]
    rw [hz, hhalf] at he
    linarith
  change (1 - 2 * a.val) ^ 2 ∈ Set.Ioo (0 : ℝ) 1
  constructor
  · exact sq_pos_of_pos (by linarith)
  · nlinarith [mul_pos ha0 (sub_pos.mpr ha1)]

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature Series
open scoped BigOperators

private theorem interior_bscOptimal {Cu Cv : ℝ}
    (hCu0 : 0 < Cu) (hCu1 : Cu < 1) (hCv0 : 0 < Cv) (hCv1 : Cv < 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 / 2 ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 / 2 → θ < p → bscOptimal Cu Cv p := by
  let α := hbInv (1 - Cu)
  let β := hbInv (1 - Cv)
  let a := 1 - 2 * α.val
  let b := 1 - 2 * β.val
  let M := max (Curvature.slope (a ^ 2)) (Curvature.slope (b ^ 2))
  have ha : a ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := candidate_bias_interior hCu0 hCu1
  have hbHyp : b ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := candidate_bias_interior hCv0 hCv1
  have hM : 0 ≤ M := (slope_nonneg ha).trans (le_max_left _ _)
  have hd : 0 < 1 + 6 * M := by positivity
  let θ := 3 * M / (1 + 6 * M)
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 / 2 := by
    apply (div_lt_iff₀ hd).mpr
    linarith
  refine ⟨θ, hθ0, hθ1, ?_⟩
  intro p hp0 hp1 hθp
  have hδ0 : 0 ≤ 1 - 2 * p := by linarith
  have hδ1 : 1 - 2 * p < 1 := by linarith
  have hsmall : 1 - 2 * p ≤ 1 / (1 + 6 * M) := by
    have hh : 3 * M < p * (1 + 6 * M) := (div_lt_iff₀ hd).mp hθp
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hφa : phi (a ^ 2) = Cu * Real.log 2 := by
    dsimp [a]
    rw [phi_crossover, hb_inv_spec (1 - Cu) ⟨by linarith, by linarith⟩]
    ring
  have hφb : phi (b ^ 2) = Cv * Real.log 2 := by
    dsimp [b]
    rw [phi_crossover, hb_inv_spec (1 - Cv) ⟨by linarith, by linarith⟩]
    ring
  apply bscOptimal_of_upper_bound hCu0.le hCu1.le hCv0.le hCv1.le
  intro n m K L hK hL
  have hs (u : Fin n) : |posteriorBias K u| ≤ 1 :=
    abs_le.mpr (posterior_bias_mem K u)
  have ht (v : Fin m) : |posteriorBias L v| ≤ 1 :=
    abs_le.mpr (posterior_bias_mem L v)
  have hsc : dotProduct ((fun w => ((K false w).toReal + (K true w).toReal) / 2)) (posteriorBias K) = 0 := posterior_bias_centered K
  have htc : dotProduct ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (posteriorBias L) = 0 := posterior_bias_centered L
  have hmb : dotProduct ((fun w => ((K false w).toReal + (K true w).toReal) / 2)) (fun u => phi (posteriorBias K u ^ 2)) ≤ phi (a ^ 2) := by
    rw [rate_phi] at hK
    rw [hφa]
    exact (div_le_iff₀ hlog).mp hK
  have hnb : dotProduct ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (fun v => phi (posteriorBias L v ^ 2)) ≤ phi (b ^ 2) := by
    rw [rate_phi] at hL
    rw [hφb]
    exact (div_le_iff₀ hlog).mp hL
  have hpost := posterior_local_optimality ((fun w => ((K false w).toReal + (K true w).toReal) / 2)) (posteriorBias K)
    ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (posteriorBias L) (output_mass_probability K).1 (output_mass_probability K).2
    (output_mass_probability L).1 (output_mass_probability L).2 hs ht hsc htc
    a b ha hbHyp hmb hnb hδ0 hδ1 hsmall
  calc
    objective p K L =
        productValue (1 - 2 * p) ((fun w => ((K false w).toReal + (K true w).toReal) / 2)) (posteriorBias K) ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (posteriorBias L) /
          Real.log 2 := objective_productValue p K L
    _ ≤ productValue (1 - 2 * p) half (signed a) half (signed b) / Real.log 2 :=
      div_le_div_of_nonneg_right hpost hlog.le
    _ = objective p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv))) :=
      (objective_bsc_productValue p α β).symm

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature Series
open scoped BigOperators

private theorem bias_zero_of_rate_nonpos {n : ℕ} (K : (Bool → PMF (Fin n))) (hK : rate K ≤ 0) :
    ∀ u, (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * posteriorBias K u = 0 := by
  let p := (fun w => ((K false w).toReal + (K true w).toReal) / 2)
  let s := posteriorBias K
  have hp0 := (output_mass_probability K).1
  have hp1 := (output_mass_probability K).2
  have hx (u : Fin n) : s u ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    have hh := posterior_bias_mem K u
    exact ⟨sq_nonneg _, by dsimp [s]; nlinarith [hh.1, hh.2]⟩
  have hv : dotProduct p (fun u => s u ^ 2) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [dotProduct, smul_eq_mul] using (convex_Icc (0 : ℝ) 1).sum_mem
      (t := Finset.univ) (w := p) (z := fun u => s u ^ 2)
      (fun u _ => hp0 u) hp1 (fun u _ => hx u)
  rw [rate_phi] at hK
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbudget : dotProduct p (fun u => phi (s u ^ 2)) ≤ 0 := by
    have hh := (div_le_iff₀ hlog).mp hK
    simpa using hh
  have hj := phi_convex.map_sum_le (t := Finset.univ) (w := p) (p := fun u => s u ^ 2)
    (fun u _ => hp0 u) hp1 (fun u _ => hx u)
  simp only [smul_eq_mul] at hj
  change phi (dotProduct p (fun u => s u ^ 2)) ≤ dotProduct p (fun u => phi (s u ^ 2)) at hj
  have hphi0 : phi (0 : ℝ) = 0 := by
    simp only [phi, Real.sqrt_zero, add_zero, one_div, Real.binEntropy_two_inv, sub_self]
  have hv0 : dotProduct p (fun u => s u ^ 2) = 0 := by
    apply le_antisymm _ hv.1
    apply (phi_strictMono.le_iff_le hv (by norm_num)).mp
    rw [hphi0]
    exact hj.trans hbudget
  have hterm (u : Fin n) : p u * s u ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hp0 i) (sq_nonneg _))).mp hv0 u
      (Finset.mem_univ u)
  intro u
  change p u * s u = 0
  rcases mul_eq_zero.mp (hterm u) with h | h
  · simp [h]
  · rw [sq_eq_zero_iff] at h
    simp [h]

private theorem objective_zero_of_bias_zero {n m : ℕ} (p : ℝ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m)))
    (hzero : (∀ u, (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * posteriorBias K u = 0) ∨
      (∀ v, (fun w => ((L false w).toReal + (L true w).toReal) / 2) v * posteriorBias L v = 0)) : objective p K L = 0 := by
  have hprod : outputJoint p K L = fun uv => (fun w => ((K false w).toReal + (K true w).toReal) / 2) uv.1 * (fun w => ((L false w).toReal + (L true w).toReal) / 2) uv.2 := by
    funext uv
    rcases uv with ⟨u, v⟩
    rw [output_joint_posterior]
    calc
      _ = (fun w => ((K false w).toReal + (K true w).toReal) / 2) u * (fun w => ((L false w).toReal + (L true w).toReal) / 2) v + (1 - 2 * p) *
          ((fun w => ((K false w).toReal + (K true w).toReal) / 2) u * posteriorBias K u) * ((fun w => ((L false w).toReal + (L true w).toReal) / 2) v * posteriorBias L v) := by ring
      _ = _ := by rcases hzero with h | h <;> simp [h]
  unfold objective mutualInformationBits
  rw [hprod, D5.S3.Entropy.MutualInformationProduct.mutual_information_product_eq_zero
    ((fun w => ((K false w).toReal + (K true w).toReal) / 2)) ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (output_mass_probability K) (output_mass_probability L)]
  exact zero_div _

private theorem zero_budget_bscOptimal {Cu Cv p : ℝ}
    (hCu0 : 0 ≤ Cu) (hCu1 : Cu ≤ 1) (hCv0 : 0 ≤ Cv) (hCv1 : Cv ≤ 1)
    (hz : Cu = 0 ∨ Cv = 0) : bscOptimal Cu Cv p := by
  apply bscOptimal_of_upper_bound hCu0 hCu1 hCv0 hCv1
  intro n m K L hK hL
  rcases hz with hz | hz
  · have hzero := objective_zero_of_bias_zero p K L
      (Or.inl (bias_zero_of_rate_nonpos K (by simpa [hz] using hK)))
    have hcand := objective_zero_of_bias_zero p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv)))
      (Or.inl (bias_zero_of_rate_nonpos _ (by rw [candidate_rate hCu0 hCu1, hz])))
    rw [hzero, hcand]
  · have hzero := objective_zero_of_bias_zero p K L
      (Or.inr (bias_zero_of_rate_nonpos L (by simpa [hz] using hL)))
    have hcand := objective_zero_of_bias_zero p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv)))
      (Or.inr (bias_zero_of_rate_nonpos _ (by rw [candidate_rate hCv0 hCv1, hz])))
    rw [hzero, hcand]

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC.Boundary
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature
open D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
open scoped BigOperators

private theorem combining_monotone {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) (Real.log 2)) :
    MonotoneOn (fun x => G 1 x y) (Set.Icc (0 : ℝ) (Real.log 2)) := by
  intro x hx z hz hxz
  have hv := (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.inverseBias_spec (by norm_num : (0 : ℝ) < 1) hy).1
  have hu := (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.inverseBias_spec (by norm_num : (0 : ℝ) < 1) hx).1
  have hw := (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.inverseBias_spec (by norm_num : (0 : ℝ) < 1) hz).1
  have horder := D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.inverseBias_anti (by norm_num : (0 : ℝ) < 1) hx hz hxz
  change G 1 x y ≤ G 1 z y
  rw [D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.bias_combining, D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.bias_combining]
  apply (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.psi_strictAntiOn (by norm_num : (0 : ℝ) < 1)).antitoneOn
    ⟨mul_nonneg hv.1 hw.1, mul_le_one₀ hv.2 hw.1 hw.2⟩
    ⟨mul_nonneg hv.1 hu.1, mul_le_one₀ hv.2 hu.1 hu.2⟩
  exact mul_le_mul_of_nonneg_left horder hv.1

private theorem combining_bias {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    G 1 (psi 1 u) (psi 1 v) = psi 1 (v * u) := by
  have hpu : (1 - u) / 2 ∈ Set.Icc (0 : ℝ) (1 / 2) := by constructor <;> linarith [hu.1, hu.2]
  have hpv : (1 - v) / 2 ∈ Set.Icc (0 : ℝ) (1 / 2) := by constructor <;> linarith [hv.1, hv.2]
  change h 1 (star (hInv 1 (h 1 ((1 - u) / 2))) (hInv 1 (h 1 ((1 - v) / 2)))) =
    h 1 ((1 - v * u) / 2)
  rw [hInv_h (by norm_num : (0 : ℝ) < 1) hpu, hInv_h (by norm_num : (0 : ℝ) < 1) hpv]
  congr 1
  dsimp [D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.star, D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining.bconv]
  ring

private theorem phi_psi (s : ℝ) : phi (s ^ 2) = Real.log 2 - psi 1 |s| := by
  simp [phi, psi, h, Real.sqrt_sq_eq_abs]
  rw [← Real.binEntropy_one_sub ((1 + |s|) / 2),
    show 1 - (1 + |s|) / 2 = (1 - |s|) / 2 by ring]

private theorem scalar_mgl {B : Type*} [Fintype B] (q t : B → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) (ht : ∀ j, |t j| ≤ 1)
    {b δ : ℝ} (hbHyp : b ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hbudget : dotProduct q (fun j => phi (t j ^ 2)) ≤ phi (b ^ 2)) :
    dotProduct q (fun j => phi ((δ * t j) ^ 2)) ≤ phi ((δ * b) ^ 2) := by
  have hmem {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      psi 1 u ∈ Set.Icc (0 : ℝ) (Real.log 2) := by
    simpa [psi, h] using (show Real.binEntropy ((1 - u) / 2) ∈ Set.Icc (0 : ℝ) (Real.log 2) from
      ⟨Real.binEntropy_nonneg (by linarith [hu.2]) (by linarith [hu.1]), Real.binEntropy_le_log_two⟩)
  let x : B → ℝ := fun j => psi 1 |t j|
  let y : ℝ := psi 1 δ
  have hx (j : B) : x j ∈ Set.Icc (0 : ℝ) (Real.log 2) := hmem ⟨abs_nonneg _, ht j⟩
  have hy : y ∈ Set.Icc (0 : ℝ) (Real.log 2) := hmem hδ
  have hxbar : dotProduct q x ∈ Set.Icc (0 : ℝ) (Real.log 2) := by
    simpa only [dotProduct, smul_eq_mul] using (convex_Icc (0 : ℝ) (Real.log 2)).sum_mem
      (t := Finset.univ) (w := q) (z := x) (fun j _ => hq0 j) hq1 (fun j _ => hx j)
  obtain ⟨αhat, hhat, _, hc, _⟩ :=
    D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.result
  have hconv := hc 1 (by norm_num) hhat y hy
  have hj := hconv.map_sum_le (t := Finset.univ) (w := q) (p := x)
    (fun j _ => hq0 j) hq1 (fun j _ => hx j)
  simp only [smul_eq_mul] at hj
  change G 1 (dotProduct q x) y ≤ dotProduct q (fun j => G 1 (x j) y) at hj
  have hpoint (j : B) : x j = Real.log 2 - phi (t j ^ 2) := by
    dsimp [x]
    rw [phi_psi]
    ring
  have hbar : dotProduct q x = Real.log 2 - dotProduct q (fun j => phi (t j ^ 2)) := by
    rw [show x = (fun j => Real.log 2 - phi (t j ^ 2)) from funext hpoint,
      avg_sub, avg_const q _ hq1]
  have hbase : psi 1 b = Real.log 2 - phi (b ^ 2) := by
    rw [phi_psi, abs_of_nonneg hbHyp.1]
    ring
  have hmin : psi 1 b ≤ dotProduct q x := by rw [hbase, hbar]; linarith
  have hm := combining_monotone hy (hmem hbHyp) hxbar hmin
  have htarget : G 1 (psi 1 b) y = Real.log 2 - phi ((δ * b) ^ 2) := by
    rw [combining_bias hbHyp hδ, phi_psi, abs_of_nonneg (mul_nonneg hδ.1 hbHyp.1)]
    ring
  have hgpoint (j : B) : G 1 (x j) y = Real.log 2 - phi ((δ * t j) ^ 2) := by
    rw [combining_bias ⟨abs_nonneg _, ht j⟩ hδ, phi_psi, abs_mul, abs_of_nonneg hδ.1]
    ring
  change G 1 (psi 1 b) y ≤ G 1 (dotProduct q x) y at hm
  rw [htarget] at hm
  have hgsum : dotProduct q (fun j => G 1 (x j) y) =
      Real.log 2 - dotProduct q (fun j => phi ((δ * t j) ^ 2)) := by
    simp_rw [hgpoint]
    rw [avg_sub, avg_const q _ hq1]
  rw [hgsum] at hj
  linarith

end D5.S3.Entropy.DoubleSidedBottleneckBSC.Boundary

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature Series
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.MutualInformationSymm
open scoped BigOperators

private theorem phi_f (z : ℝ) : phi (z ^ 2) = ((-Real.negMulLog (1 + z)) + (-Real.negMulLog (1 + -z))) / 2 := by
  rw [phi_bias, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1 - (1 + z) / 2 = (1 - z) / 2 by ring]
  rw [div_eq_mul_inv, div_eq_mul_inv, Real.negMulLog_mul, Real.negMulLog_mul]
  simp only [Real.negMulLog, Real.log_inv, Real.negMulLog]
  ring

private theorem output_joint_nonneg {n m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (uv : Fin n × Fin m) :
    0 ≤ outputJoint p K L uv := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg _ ENNReal.toReal_nonneg
  apply mul_nonneg _ ENNReal.toReal_nonneg
  dsimp [dsbs]
  have hcomp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  split_ifs <;> positivity

private theorem objective_symm {n m : ℕ} (p : ℝ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) :
    objective p K L = objective p L K := by
  have heq : outputJoint p K L = fun uv => outputJoint p L K (uv.2, uv.1) := by
    funext uv
    rcases uv with ⟨u, v⟩
    rw [output_joint_posterior, output_joint_posterior]
    ring
  unfold objective mutualInformationBits
  rw [heq, mutual_information_symm]

private noncomputable def noiseless : (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := ⟨0, by norm_num⟩

private theorem objective_le_noiseless {n m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) :
    objective p K L ≤ objective p (bsc noiseless) L := by
  let j : Fin m × Fin 2 → ℝ := fun vi => outputJoint p (bsc noiseless) L (vi.2, vi.1)
  let W : Fin 2 → Fin n → ℝ := fun i u => if i = 0 then (K false u).toReal else (K true u).toReal
  let triple : Fin m × (Fin 2 × Fin n) → ℝ := fun q => j (q.1, q.2.1) * W q.2.1 q.2.2
  have hW (i : Fin 2) : ∑ u, W i u = 1 := by
    fin_cases i
    · simpa [W] using kernel_real_sum K false
    · simpa [W] using kernel_real_sum K true
  have hW0 (i : Fin 2) (u : Fin n) : 0 ≤ W i u := by
    dsimp [W]
    split_ifs <;> exact ENNReal.toReal_nonneg
  have hj0 (vi : Fin m × Fin 2) : 0 ≤ j vi := output_joint_nonneg hp0 hp1 _ _ _
  have hj1 : ∑ vi, j vi = 1 := by
    dsimp [j]
    rw [Fintype.sum_prod_type]
    simp only [output_joint_col_sum]
    exact (output_mass_probability L).2
  have hprob : (∀ q, 0 ≤ triple q) ∧ ∑ q, triple q = 1 := by
    refine ⟨fun q => mul_nonneg (hj0 _) (hW0 _ _), ?_⟩
    simp only [triple, Fintype.sum_prod_type, ← Finset.mul_sum, hW, mul_one]
    simpa only [Fintype.sum_prod_type] using hj1
  have hxy : xyProjection triple = j := by
    funext vi
    simp [xyProjection, triple, ← Finset.mul_sum, hW]
  have hxz : xzProjection triple = fun vu => outputJoint p K L (vu.2, vu.1) := by
    funext vu
    rcases vu with ⟨v, u⟩
    simp [xzProjection, triple, j, W, Fin.sum_univ_two, outputJoint, dsbs,
      bsc_apply_formula, noiseless]
    ring
  have hmarkov := markov_of_channel j W hW
  have hDPI := mutual_information_le_of_markov triple hprob hmarkov
  rw [hxy, hxz, mutual_information_symm] at hDPI
  have hjMI : D5.S3.Entropy.MutualInformation.mutualInformation j =
      D5.S3.Entropy.MutualInformation.mutualInformation (outputJoint p (bsc noiseless) L) :=
    mutual_information_symm _
  rw [hjMI] at hDPI
  exact div_le_div_of_nonneg_right hDPI (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

private theorem objective_noiseless_formula {m : ℕ} (p : ℝ) (L : (Bool → PMF (Fin m))) :
    objective p (bsc noiseless) L =
      dotProduct ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (fun v => phi (((1 - 2 * p) * posteriorBias L v) ^ 2)) / Real.log 2 := by
  rw [objective_productValue]
  congr 1
  dsimp [productValue, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fin.sum_univ_two, output_mass_bsc, posterior_bias_bsc, noiseless]
  norm_num
  rw [phi_f]
  simp only [Real.negMulLog]
  ring_nf

private theorem hbInv_zero : hbInv 0 = noiseless := by
  have he := hb_inv_spec 0 (by norm_num)
  rw [hb_binEntropy] at he
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hz : Real.binEntropy (hbInv 0).val = 0 := (div_eq_zero_iff.mp he).resolve_right hlog
  rcases Real.binEntropy_eq_zero.mp hz with hz | hz
  · exact Subtype.ext hz
  · have hh := (hbInv 0).property.2
    rw [hz] at hh
    norm_num at hh

private theorem full_budget_upper {Cv p : ℝ} (hCv0 : 0 ≤ Cv) (hCv1 : Cv ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    {n m : ℕ} (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (hL : rate L ≤ Cv) :
    objective p K L ≤ objective p (bsc (hbInv (1 - 1))) (bsc (hbInv (1 - Cv))) := by
  let β := hbInv (1 - Cv)
  let b := 1 - 2 * β.val
  have hbHyp : b ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> dsimp [b] <;> linarith [β.property.1, β.property.2]
  have hδ : 1 - 2 * p ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbudget : dotProduct ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (fun v => phi (posteriorBias L v ^ 2)) ≤ phi (b ^ 2) := by
    rw [rate_phi] at hL
    have hh := (div_le_iff₀ hlog).mp hL
    have he : phi (b ^ 2) = Cv * Real.log 2 := by
      dsimp [b]
      rw [phi_crossover, hb_inv_spec _ ⟨by linarith, by linarith⟩]
      ring
    rwa [he]
  have hmgl := Boundary.scalar_mgl ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (posteriorBias L)
    (output_mass_probability L).1 (output_mass_probability L).2
    (fun v => abs_le.mpr (posterior_bias_mem L v)) hbHyp hδ hbudget
  have hcand : objective p (bsc noiseless) (bsc β) = phi (((1 - 2 * p) * b) ^ 2) / Real.log 2 := by
    rw [objective_noiseless_formula]
    congr 1
    simp only [dotProduct, Fin.sum_univ_two, output_mass_bsc, posterior_bias_bsc]
    norm_num
    rw [show ((1 - 2 * p) * (2 * β.val - 1)) ^ 2 = ((1 - 2 * p) * b) ^ 2 by dsimp [b]; ring]
    ring
  simp only [sub_self, hbInv_zero]
  calc
    objective p K L ≤ objective p (bsc noiseless) L := objective_le_noiseless hp0 (by linarith) K L
    _ = dotProduct ((fun w => ((L false w).toReal + (L true w).toReal) / 2)) (fun v => phi (((1 - 2 * p) * posteriorBias L v) ^ 2)) / Real.log 2 :=
      objective_noiseless_formula p L
    _ ≤ phi (((1 - 2 * p) * b) ^ 2) / Real.log 2 := div_le_div_of_nonneg_right hmgl hlog.le
    _ = objective p (bsc noiseless) (bsc (hbInv (1 - Cv))) := hcand.symm

private theorem full_budget_bscOptimal {Cu Cv p : ℝ}
    (hCu0 : 0 ≤ Cu) (hCu1 : Cu ≤ 1) (hCv0 : 0 ≤ Cv) (hCv1 : Cv ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (hz : Cu = 1 ∨ Cv = 1) : bscOptimal Cu Cv p := by
  apply bscOptimal_of_upper_bound hCu0 hCu1 hCv0 hCv1
  intro n m K L hK hL
  rcases hz with hz | hz
  · subst Cu
    exact full_budget_upper hCv0 hCv1 hp0 hp1 K L hL
  · subst Cv
    rw [objective_symm p K L, objective_symm p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - 1)))]
    exact full_budget_upper hCu0 hCu1 hp0 hp1 L K hK

theorem result : claim := by
  intro Cu hCu0 hCu1 Cv hCv0 hCv1
  refine ⟨hb_inv_spec _ ⟨by linarith, by linarith⟩,
    hb_inv_spec _ ⟨by linarith, by linarith⟩, ?_⟩
  by_cases hz : Cu = 0 ∨ Cv = 0
  · exact ⟨0, le_rfl, by norm_num, fun p _ _ _ => zero_budget_bscOptimal hCu0 hCu1 hCv0 hCv1 hz⟩
  by_cases ho : Cu = 1 ∨ Cv = 1
  · exact ⟨0, le_rfl, by norm_num,
      fun p hp0 hp1 _ => full_budget_bscOptimal hCu0 hCu1 hCv0 hCv1 hp0 hp1 ho⟩
  exact interior_bscOptimal
    (lt_of_le_of_ne hCu0 (Ne.symm (not_or.mp hz).1))
    (lt_of_le_of_ne hCu1 (not_or.mp ho).1)
    (lt_of_le_of_ne hCv0 (Ne.symm (not_or.mp hz).2))
    (lt_of_le_of_ne hCv1 (not_or.mp ho).2)

end D5.S3.Entropy.DoubleSidedBottleneckBSC
