/- GID: D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.claim; result=D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.result; claim=D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.claim
   digest: Pure covariant programs cannot match the mixed program dimension. -/

/-
admission_basis: open-problem-resolution (#15518; Refuted)
IsCovariant: proof_shape: definition; escape_witness: none;
  consumers: MixedProgrammable, PureProgrammable, covariant_replacement, mixed_programmable, not_pure_programmable, replacement_covariant; Direct frozen dependencies: none
MixedProgrammable: proof_shape: definition; escape_witness: none;
  consumers: claim, mixed_programmable; Direct frozen dependencies: F1, F3, F2
PureProgrammable: proof_shape: definition; escape_witness: none;
  consumers: claim, not_pure_programmable; Direct frozen dependencies: F3, F9, F2
claim: proof_shape: definition; escape_witness: none;
  consumers: result; Direct frozen dependencies: F1, F3, F8, F9, F2
channel_linear: proof_shape: bind-only; escape_witness: none;
  consumers: covariant_replacement; Direct frozen dependencies: F3, F2
channel_trace: proof_shape: bind-only; escape_witness: none;
  consumers: channel_state; Direct frozen dependencies: F3, F7, F4, F6, F2, F5
channel_state: proof_shape: bind-only; escape_witness: none;
  consumers: covariant_replacement; Direct frozen dependencies: F1, F3, F7, F4, F6, F2, F5
half_identity_state: proof_shape: bind-only; escape_witness: none;
  consumers: covariant_replacement; Direct frozen dependencies: F1
discard_complete: proof_shape: bind-only; escape_witness: none;
  consumers: mixed_processor_channel; Direct frozen dependencies: none
mixed_processor_channel: proof_shape: bind-only; escape_witness: none;
  consumers: mixed_programmable; Direct frozen dependencies: F3, F2
mixed_processor_tensor: proof_shape: bind-only; escape_witness: none;
  consumers: mixed_programmable; Direct frozen dependencies: F3, F2
rotZ: proof_shape: definition; escape_witness: none;
  consumers: group_average, u_s, umatZ, umat_unitary; Direct frozen dependencies: none
umatZ: proof_shape: definition; escape_witness: none;
  consumers: U, group_average, u_r, u_s, umat, umatZ_mul, umat_mul, umat_unitary; Direct frozen dependencies: none
umatZ_mul: proof_shape: bind-only; escape_witness: none;
  consumers: umat_mul; Direct frozen dependencies: none
umat: proof_shape: definition; escape_witness: none;
  consumers: U, group_average, umat_mul, umat_unitary; Direct frozen dependencies: none
umat_mul: proof_shape: bind-only; escape_witness: none;
  consumers: U, group_average; Direct frozen dependencies: none
umat_unitary: proof_shape: bind-only; escape_witness: none;
  consumers: U, group_average; Direct frozen dependencies: none
U: proof_shape: definition; escape_witness: none;
  consumers: covariant_replacement, group_average, mixed_programmable, not_pure_programmable, replacement_covariant, result, u_irreducible, u_irreducible_coordinates, u_r, u_s; Direct frozen dependencies: none
u_r: proof_shape: bind-only; escape_witness: none;
  consumers: u_irreducible_coordinates; Direct frozen dependencies: none
u_s: proof_shape: bind-only; escape_witness: none;
  consumers: u_irreducible_coordinates; Direct frozen dependencies: none
u_irreducible_coordinates: proof_shape: bind-only; escape_witness: none;
  consumers: u_irreducible; Direct frozen dependencies: none
u_irreducible: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F8
replacement: proof_shape: definition; escape_witness: none;
  consumers: mixed_replacement_channel, not_pure_programmable, one_replacement_channel, plus_replacement_channel, pure_replacement_channel, replacement_covariant, zero_replacement_channel; Direct frozen dependencies: none
pure_replacement_channel: proof_shape: bind-only; escape_witness: none;
  consumers: one_replacement_channel, plus_replacement_channel, zero_replacement_channel; Direct frozen dependencies: F3, F9, F2
zero_replacement_channel: proof_shape: bind-only; escape_witness: none;
  consumers: not_pure_programmable; Direct frozen dependencies: F3, F9, F2
one_replacement_channel: proof_shape: bind-only; escape_witness: none;
  consumers: not_pure_programmable; Direct frozen dependencies: F3, F9, F2
plus_replacement_channel: proof_shape: bind-only; escape_witness: none;
  consumers: not_pure_programmable; Direct frozen dependencies: F3, F9, F2
mixed_replacement_channel: proof_shape: bind-only; escape_witness: none;
  consumers: not_pure_programmable; Direct frozen dependencies: F3, F2
dihedral_sum: proof_shape: bind-only; escape_witness: none;
  consumers: group_average; Direct frozen dependencies: none
group_average: proof_shape: bind-only; escape_witness: none;
  consumers: covariant_replacement; Direct frozen dependencies: none
covariant_replacement: proof_shape: bind-only; escape_witness: none;
  consumers: mixed_programmable; Direct frozen dependencies: F1, F3, F7, F4, F6, F2, F5
mixed_programmable: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F1, F3, F7, F4, F6, F2, F5
replacement_covariant: proof_shape: bind-only; escape_witness: none;
  consumers: not_pure_programmable; Direct frozen dependencies: none
not_pure_programmable: proof_shape: content; escape_witness: PureProgramQubitObstruction.three_pure_outputs_rigidity;
  consumers: result; Direct frozen dependencies: F3, F9, F2
  Same-delivery supporting module: PureProgramQubitObstruction.no_four_replacements
result: proof_shape: content; escape_witness: PureProgramQubitObstruction.three_pure_outputs_rigidity;
  consumers: external settlement; Direct frozen dependencies: F1, F3, F7, F4, F6, F8, F9, F2, F5
Frozen declaration identities (declaration statement_ids from the Lean report):
  F1: D5/S3/Quantum/Information/SLDSpectralEnergy.IsDensity
    statement_id: sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448
  F2: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  F3: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  F4: D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel
    statement_id: sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0
  F5: D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel
    statement_id: sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
  F6: D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap
    statement_id: sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc
  F7: D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.trace_preserving
    statement_id: sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15
  F8: D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.IrredProj
    statement_id: sha256:14e07bf7d5f38cc3c54cb5a4f2978ef88807c35b7d46558dd79a470de0d16285
  F9: D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
    statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
The channel map is the frozen MatrixMap.of_kraus K K.
finite_kraus_quantum_channel relates complete Kraus families to QuantumChannel.
The IsState convention is the frozen IsDensity predicate on Matrix;
DensityState instead has a CStarMatrix subtype carrier.
IrredProj is the frozen invariant-subspace predicate on EuclideanSpace;
WithLp.linearEquiv transports its subspaces to coordinate functions.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15645;
no_four_replacements lacks whole-family variation, sensitivity, and observational-dependence evidence.
DTR reading: DTR-Unregistered (Observe) for no_four_replacements; the designated result is exempt.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.QuantumChannels.PureProgramQubitObstruction
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound
import D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace D5.S3.Quantum.QuantumChannels.CovariantPureProgramDimensionRefutation
open D5.S3.Quantum.QuantumChannels.PureProgramQubitObstruction
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer (IrredProj)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

def IsCovariant {G : Type} [Group G] {d1 d2 : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin d1) ℂ)
    (V : G →* Matrix.unitaryGroup (Fin d2) ℂ)
    (T : Matrix (Fin d1) (Fin d1) ℂ → Matrix (Fin d2) (Fin d2) ℂ) : Prop :=
  ∀ g rho, T ((U g : Matrix _ _ ℂ) * rho * star (U g : Matrix _ _ ℂ)) =
    (V g : Matrix _ _ ℂ) * T rho * star (V g : Matrix _ _ ℂ)

def MixedProgrammable {G : Type} [Group G] {d1 d2 : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin d1) ℂ)
    (V : G →* Matrix.unitaryGroup (Fin d2) ℂ) (dP : ℕ) : Prop :=
  ∃ P : Matrix (Fin d1 × Fin dP) (Fin d1 × Fin dP) ℂ → Matrix (Fin d2) (Fin d2) ℂ,
    IsChannel P ∧ ∀ T, IsChannel T ∧ IsCovariant U V T →
      ∃ pi : Matrix (Fin dP) (Fin dP) ℂ, IsDensity pi ∧ ∀ rho, P (Matrix.kronecker rho pi) = T rho

def PureProgrammable {G : Type} [Group G] {d1 d2 : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin d1) ℂ)
    (V : G →* Matrix.unitaryGroup (Fin d2) ℂ) (dP : ℕ) : Prop :=
  ∃ P : Matrix (Fin d1 × Fin dP) (Fin d1 × Fin dP) ℂ → Matrix (Fin d2) (Fin d2) ℂ,
    IsChannel P ∧ ∀ T, IsChannel T ∧ IsCovariant U V T →
      ∃ psi : Fin dP → ℂ, star psi ⬝ᵥ psi = 1 ∧
        ∀ rho, P (Matrix.kronecker rho (rankOneDensity psi)) = T rho

def claim : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (d1 d2 : ℕ)
    (U : G →* Matrix.unitaryGroup (Fin d1) ℂ)
    (V : G →* Matrix.unitaryGroup (Fin d2) ℂ),
    IrredProj (fun g => (U g : Matrix (Fin d1) (Fin d1) ℂ)) → ∀ dP, MixedProgrammable U V dP → PureProgrammable U V dP

private lemma channel_linear {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (T : Matrix A A ℂ → Matrix B B ℂ) (hT : IsChannel T) :
    ∃ L : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ, ∀ rho, T rho = L rho := by
  obtain ⟨r,K,hK,hT⟩ := hT
  refine ⟨MatrixMap.of_kraus K K, ?_⟩
  intro rho
  simpa [MatrixMap.of_kraus] using hT rho

private lemma channel_trace {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (T : Matrix A A ℂ → Matrix B B ℂ) (hT : IsChannel T) (rho : Matrix A A ℂ) :
    (T rho).trace = rho.trace := by
  obtain ⟨r,K,hK,hT⟩ := hT
  obtain ⟨channel, hc⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel K hK
  have ht := channel.trace_preserving (CStarMatrix.ofMatrix rho)
  change Matrix.trace (CStarMatrix.ofMatrix.symm
    (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho))) = rho.trace at ht
  rw [hc] at ht
  simpa only [hT, MatrixMap.of_kraus, LinearMap.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk] using ht

private lemma channel_state {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (T : Matrix A A ℂ → Matrix B B ℂ) (hT : IsChannel T)
    (rho : Matrix A A ℂ) (hs : IsDensity rho) : IsDensity (T rho) := by
  constructor
  · obtain ⟨r,K,hK,hTk⟩ := hT
    rw [hTk]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    exact Matrix.posSemidef_sum _ (fun i hi => hs.1.mul_mul_conjTranspose_same (K i))
  · rw [channel_trace T hT rho, hs.2]

private lemma half_identity_state : IsDensity ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  constructor
  · exact Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ 1/2 by rw [RCLike.le_iff_re_im]; norm_num)
  · norm_num [Matrix.trace_smul, Matrix.trace_one]

private lemma discard_complete :
    (∑ i : Fin 2,
      ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix (Prod.mk i) id)ᴴ *
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix (Prod.mk i) id) = 1 := by
  ext a b
  rcases a with ⟨a1,a2⟩; rcases b with ⟨b1,b2⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    norm_num [Matrix.submatrix_apply, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two]

private lemma mixed_processor_channel : IsChannel (MatrixMap.of_kraus (fun i : Fin 2 => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix (Prod.mk i) id) (fun i : Fin 2 => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix (Prod.mk i) id)) := by
  refine ⟨2, (fun i : Fin 2 =>
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix (Prod.mk i) id),
    discard_complete, ?_⟩
  intro rho
  simp [MatrixMap.of_kraus]

private lemma mixed_processor_tensor (rho pi : Matrix (Fin 2) (Fin 2) ℂ) :
    (MatrixMap.of_kraus (fun i : Fin 2 => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix (Prod.mk i) id) (fun i : Fin 2 => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix (Prod.mk i) id)) (Matrix.kronecker rho pi) = rho.trace • pi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatrixMap.of_kraus, Matrix.submatrix_apply, Matrix.one_apply, Matrix.kronecker, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.trace, Matrix.diag] <;> ring


private def rotZ (k : ZMod 4) : Matrix (Fin 2) (Fin 2) ℤ :=
  match k.val with
  | 0 => 1
  | 1 => !![0,-1;1,0]
  | 2 => -1
  | _ => !![0,1;-1,0]

private def umatZ : DihedralGroup 4 → Matrix (Fin 2) (Fin 2) ℤ
  | .r k => rotZ k
  | .sr k => !![1,0;0,-1] * rotZ k

private lemma umatZ_mul : ∀ g h, umatZ (g * h) = umatZ g * umatZ h := by
  decide +kernel

private def umat (g : DihedralGroup 4) : Matrix (Fin 2) (Fin 2) ℂ := (umatZ g).map (Int.castRingHom ℂ)

private lemma umat_mul (g h : DihedralGroup 4) : umat (g * h) = umat g * umat h := by
  simp only [umat, umatZ_mul, Matrix.map_mul]

private lemma umat_unitary (g : DihedralGroup 4) : umat g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  cases g with
  | r k => fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [umat, umatZ, rotZ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose, ZMod.val]
  | sr k => fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [umat, umatZ, rotZ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose, ZMod.val]

private def U : DihedralGroup 4 →* Matrix.unitaryGroup (Fin 2) ℂ where
  toFun g := ⟨umat g, umat_unitary g⟩
  map_one' := by
    apply Subtype.ext
    change umat (1 : DihedralGroup 4) = 1
    rw [DihedralGroup.one_def]
    have hz : (0 : ZMod 4).val = 0 := by decide
    simp only [umat, umatZ, rotZ, hz]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [umat, umatZ, rotZ, ZMod.val, Matrix.map_apply]
  map_mul' g h := by
    apply Subtype.ext
    exact umat_mul g h

private lemma u_r : (U (.r 1) : Matrix (Fin 2) (Fin 2) ℂ) = (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hval : (1 : ZMod 4).val = 1 := by decide
  change (umatZ (.r 1)).map (Int.castRingHom ℂ) = (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [umatZ, rotZ, hval]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.map_apply]
private lemma u_s : (U (.sr 0) : Matrix (Fin 2) (Fin 2) ℂ) = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  change (umatZ (.sr 0)).map (Int.castRingHom ℂ) = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)
  have hz : (0 : ZMod 4).val = 0 := by decide
  simp only [umatZ, rotZ, hz, Matrix.mul_one]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [umatZ, rotZ, ZMod.val, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two]

-- Irreducibility is checked directly on invariant subspaces.
private theorem u_irreducible_coordinates : ∀ W : Submodule ℂ (Fin 2 → ℂ),
    (∀ g, ∀ v ∈ W, (U g : Matrix _ _ ℂ) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  by_cases hz : W = ⊥
  · exact Or.inl hz
  · right
    have hn : ∃ v ∈ W, v ≠ 0 := by
      by_contra he
      apply hz
      apply (Submodule.eq_bot_iff W).mpr
      intro v hv
      by_contra hv0
      exact he ⟨v,hv,hv0⟩
    obtain ⟨v,hv,hv0⟩ := hn
    have hsv := hW (.sr 0) v hv
    rw [u_s] at hsv
    have hleft : ![v 0, 0] ∈ W := by
      have hh := W.smul_mem (1/2 : ℂ) (W.add_mem hv hsv)
      convert hh using 1
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] <;> ring
    have hright : ![0, v 1] ∈ W := by
      have hh := W.smul_mem (1/2 : ℂ) (W.sub_mem hv hsv)
      convert hh using 1
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] <;> ring
    have hb : (![1,0] : Fin 2 → ℂ) ∈ W ∧ (![0,1] : Fin 2 → ℂ) ∈ W := by
      by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := by
          intro h1
          apply hv0
          ext i; fin_cases i <;> simp [h0,h1]
        have he1 : (![0,1] : Fin 2 → ℂ) ∈ W := by
          convert W.smul_mem (v 1)⁻¹ hright using 1
          ext i; fin_cases i <;> simp [h1]
        have he0 := W.neg_mem (hW (.r 1) _ he1)
        rw [u_r] at he0
        refine ⟨?_,he1⟩
        convert he0 using 1
        ext i; fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      · have he0 : (![1,0] : Fin 2 → ℂ) ∈ W := by
          convert W.smul_mem (v 0)⁻¹ hleft using 1
          ext i; fin_cases i <;> simp [h0]
        have he1 := hW (.r 1) _ he0
        rw [u_r] at he1
        refine ⟨he0,?_⟩
        convert he1 using 1
        ext i; fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    apply Submodule.eq_top_iff'.mpr
    intro x
    have he : x = (x 0) • ![1,0] + (x 1) • ![0,1] := by
      ext i; fin_cases i <;> simp
    rw [he]
    exact W.add_mem (W.smul_mem _ hb.1) (W.smul_mem _ hb.2)


private theorem u_irreducible : IrredProj (fun g => (U g : Matrix (Fin 2) (Fin 2) ℂ)) := by
  intro W hW
  let e := WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)
  have hi : ∀ g, ∀ v ∈ W.map e.toLinearMap,
      (U g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v ∈ W.map e.toLinearMap := by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨Matrix.toEuclideanLin (U g : Matrix (Fin 2) (Fin 2) ℂ) w, hW g w hw, rfl⟩
  rcases u_irreducible_coordinates (W.map e.toLinearMap) hi with hb | ht
  · exact Or.inl ((Submodule.map_eq_bot_iff (e := e)).mp hb)
  · exact Or.inr ((Submodule.map_eq_top_iff (e := e)).mp ht)

private def replacement (sigma : Matrix (Fin 2) (Fin 2) ℂ) (rho : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := rho.trace • sigma

private lemma pure_replacement_channel (v : Fin 2 → ℂ) (hv : star v ⬝ᵥ v = 1) :
    IsChannel (replacement (rankOneDensity v)) := by
  let K : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
    fun i j a => if i = a then v j else 0
  refine ⟨2,K,?_,?_⟩
  · ext a b
    have hh : star (v 0) * v 0 + star (v 1) * v 1 = 1 := by
      simpa [dotProduct,Fin.sum_univ_two] using hv
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    fin_cases a <;> fin_cases b <;>
      simp [K,Fin.sum_univ_two] <;>
      simpa only [starRingEnd_apply] using hh
  · intro rho
    change replacement (rankOneDensity v) rho = ∑ i, K i * rho * (K i)ᴴ
    ext j k
    simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
    simp [replacement,K,rankOneDensity,Matrix.sum_apply,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.vecMulVec_apply,Pi.star_apply,
      Fin.sum_univ_two,Matrix.trace,Matrix.diag]
    ring


private lemma zero_replacement_channel : IsChannel (replacement (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have he : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = rankOneDensity (![1,0] : Fin 2 → ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply]
  rw [he]
  apply pure_replacement_channel
  norm_num [dotProduct,Fin.sum_univ_two]
private lemma one_replacement_channel : IsChannel (replacement (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have he : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) = rankOneDensity (![0,1] : Fin 2 → ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply]
  rw [he]
  apply pure_replacement_channel
  norm_num [dotProduct,Fin.sum_univ_two]
private lemma plus_replacement_channel : IsChannel (replacement (fun (_ _) => (1 / 2 : ℂ))) := by
  have hsquare : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1/2 : ℂ) := by
    rw [← _root_.mul_inv_rev, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have he : (fun (_ _) => (1 / 2 : ℂ)) = rankOneDensity (![(Real.sqrt 2 : ℂ)⁻¹,(Real.sqrt 2 : ℂ)⁻¹] : Fin 2 → ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rankOneDensity,Matrix.vecMulVec_apply,hsquare]
  rw [he]
  apply pure_replacement_channel
  simp [dotProduct,Fin.sum_univ_two,hsquare]
  norm_num

private lemma mixed_replacement_channel : IsChannel (replacement ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hsquare : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1/2 : ℂ) := by
    rw [← _root_.mul_inv_rev, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  let K : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
    ![!![(Real.sqrt 2 : ℂ)⁻¹,0;0,0], !![0,(Real.sqrt 2 : ℂ)⁻¹;0,0],
      !![0,0;(Real.sqrt 2 : ℂ)⁻¹,0], !![0,0;0,(Real.sqrt 2 : ℂ)⁻¹]]
  refine ⟨4,K,?_,?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [K,Matrix.mul_apply,Fin.sum_univ_succ,hsquare]
  · intro rho
    change replacement ((1 / 2 : ℂ) • 1) rho = ∑ i, K i * rho * (K i)ᴴ
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [replacement,K,rankOneDensity,Matrix.sum_apply,Matrix.mul_apply,
        Matrix.conjTranspose_apply,Matrix.trace,Matrix.diag,
        Fin.sum_univ_succ,hsquare] <;>
      linear_combination -(rho 0 0 + rho 1 1) * hsquare


private lemma dihedral_sum (f : DihedralGroup 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ g, f g) = (∑ k : ZMod 4, f (.r k)) + (∑ k : ZMod 4, f (.sr k)) := by
  rw [← Equiv.sum_comp DihedralGroup.equivSum.symm]
  simp [Fintype.sum_sum_type, DihedralGroup.equivSum]

private theorem group_average (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    (1/8 : ℂ) • (∑ g : DihedralGroup 4, (U g : Matrix (Fin 2) (Fin 2) ℂ) * rho * star (U g : Matrix (Fin 2) (Fin 2) ℂ)) =
      (rho.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [dihedral_sum]
  change (1/8 : ℂ) •
    ((∑ k : Fin 4, (U (.r k) : Matrix (Fin 2) (Fin 2) ℂ) * rho * star (U (.r k) : Matrix (Fin 2) (Fin 2) ℂ)) +
      (∑ k : Fin 4, (U (.sr k) : Matrix (Fin 2) (Fin 2) ℂ) * rho * star (U (.sr k) : Matrix (Fin 2) (Fin 2) ℂ))) = _
  simp only [Fin.sum_univ_succ]

  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [U, umat, umatZ, rotZ, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.map_apply, ZMod.val, Matrix.vecMul, dotProduct,
      Matrix.trace, Matrix.diag, ZMod.val_one, ZMod.val_zero, ZMod.val_natCast,
      Fin.sum_univ_two] <;> ring

private theorem covariant_replacement (T : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) (hT : IsChannel T)
    (hcov : IsCovariant U (1 : DihedralGroup 4 →* Matrix.unitaryGroup (Fin 2) ℂ) T) :
    IsDensity (T ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) ∧
      ∀ rho, T rho = rho.trace • T ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨channel_state T hT _ half_identity_state, ?_⟩
  obtain ⟨L,hL⟩ := channel_linear T hT
  have hi (g : DihedralGroup 4) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
      L ((U g : Matrix (Fin 2) (Fin 2) ℂ) * rho * star (U g : Matrix (Fin 2) (Fin 2) ℂ)) = L rho := by
    simpa [hL] using hcov g rho
  intro rho
  rw [hL,hL]
  calc
    L rho = L ((1/8 : ℂ) • ∑ g : DihedralGroup 4,
      (U g : Matrix (Fin 2) (Fin 2) ℂ) * rho * star (U g : Matrix (Fin 2) (Fin 2) ℂ)) := by
      simp only [map_smul, map_sum, hi]
      norm_num [DihedralGroup.card]
      ext i j
      simp [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply]
    _ = L ((rho.trace/2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by rw [group_average]
    _ = rho.trace • L ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by simp [map_smul, smul_smul, div_eq_mul_inv]

private theorem mixed_programmable : MixedProgrammable U (1 : DihedralGroup 4 →* Matrix.unitaryGroup (Fin 2) ℂ) 2 := by
  refine ⟨(MatrixMap.of_kraus (fun i : Fin 2 => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix (Prod.mk i) id) (fun i : Fin 2 => (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix (Prod.mk i) id)), mixed_processor_channel, ?_⟩
  intro T hT
  obtain ⟨hs,hrep⟩ := covariant_replacement T hT.1 hT.2
  exact ⟨T ((1/2 : ℂ) • 1), hs, fun rho => (mixed_processor_tensor rho _).trans (hrep rho).symm⟩


private lemma replacement_covariant (sigma : Matrix (Fin 2) (Fin 2) ℂ) :
    IsCovariant U (1 : DihedralGroup 4 →* Matrix.unitaryGroup (Fin 2) ℂ)
      (replacement sigma) := by
  intro g rho
  have hu : star (U g : Matrix (Fin 2) (Fin 2) ℂ) * (U g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (U g).property
  have ht : ((U g : Matrix (Fin 2) (Fin 2) ℂ) * rho * star (U g : Matrix (Fin 2) (Fin 2) ℂ)).trace = rho.trace := by
    rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul]
  simpa [replacement,ht]

private theorem not_pure_programmable :
    ¬ PureProgrammable U (1 : DihedralGroup 4 →* Matrix.unitaryGroup (Fin 2) ℂ) 2 := by
  rintro ⟨P,hP,hprog⟩
  obtain ⟨p0,hn0,h0⟩ := hprog (replacement (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ))
    ⟨zero_replacement_channel,replacement_covariant _⟩
  obtain ⟨p1,hn1,h1⟩ := hprog (replacement (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ))
    ⟨one_replacement_channel,replacement_covariant _⟩
  obtain ⟨pp,hnp,hp⟩ := hprog (replacement (fun (_ _) => (1 / 2 : ℂ)))
    ⟨plus_replacement_channel,replacement_covariant _⟩
  obtain ⟨pm,hnm,hm⟩ := hprog (replacement ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
    ⟨mixed_replacement_channel,replacement_covariant _⟩
  apply no_four_replacements P hP (0 : Fin 2) p0 p1 pp pm
  · simpa [replacement,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
      Matrix.single, one_smul] using h0 (Matrix.single (0 : Fin 2) 0 1)
  · simpa [replacement,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
      Matrix.single, one_smul] using h1 (Matrix.single (0 : Fin 2) 0 1)
  · have h := hp (Matrix.single (0 : Fin 2) 0 1)
    have ht : (Matrix.single (0 : Fin 2) 0 (1 : ℂ)).trace = 1 := by
      norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.single]
    change P (Matrix.kronecker (Matrix.single (0 : Fin 2) 0 1) (rankOneDensity pp)) =
      (Matrix.single (0 : Fin 2) 0 (1 : ℂ)).trace •
        (fun (_ _ : Fin 2) => (1/2 : ℂ)) at h
    rw [ht, one_smul] at h
    exact h
  · simpa [replacement,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
      Matrix.single, one_smul] using hm (Matrix.single (0 : Fin 2) 0 1)

theorem result : ¬ claim := by
  intro h
  exact not_pure_programmable
    (h (DihedralGroup 4) 2 2 U 1 u_irreducible 2 mixed_programmable)


end D5.S3.Quantum.QuantumChannels.CovariantPureProgramDimensionRefutation
