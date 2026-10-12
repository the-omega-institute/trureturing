/- GID: D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/PureProgramQubitObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three pure qubit outputs obstruct a mixed fourth target. -/

/-
admission_basis: escape-witness
IsChannel: proof_shape: definition; escape_witness: none;
  consumers: MixedProgrammable, PureProgrammable, channel_linear, channel_state, channel_trace, covariant_replacement, mixed_processor_channel, mixed_programmable, mixed_replacement_channel, no_four_replacements, not_pure_programmable, one_replacement_channel, plus_replacement_channel, pure_replacement_channel, zero_replacement_channel; Direct frozen dependencies: F2, F1
gram_diag_zero: proof_shape: bind-only; escape_witness: none;
  consumers: three_pure_outputs_rigidity; Direct frozen dependencies: none
gram_diag_nonzero: proof_shape: bind-only; escape_witness: none;
  consumers: three_pure_outputs_rigidity; Direct frozen dependencies: none
gram_plus_rows: proof_shape: bind-only; escape_witness: none;
  consumers: three_pure_outputs_rigidity; Direct frozen dependencies: none
three_pure_outputs_rigidity: proof_shape: content; escape_witness: three_pure_outputs_rigidity;
  consumers: four_target_obstruction; Direct frozen dependencies: none
four_target_obstruction: proof_shape: content; escape_witness: three_pure_outputs_rigidity;
  consumers: no_four_replacements; Direct frozen dependencies: none
programMatrix: proof_shape: definition; escape_witness: none;
  consumers: kraus_pure_gram, no_four_replacements; Direct frozen dependencies: none
kraus_pure_gram: proof_shape: bind-only; escape_witness: none;
  consumers: no_four_replacements; Direct frozen dependencies: F3
no_four_replacements: proof_shape: content; escape_witness: three_pure_outputs_rigidity;
  consumers: not_pure_programmable; Direct frozen dependencies: F2, F3, F1
Frozen declaration identities (declaration statement_ids from the Lean report):
  F1: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  F2: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  F3: D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
    statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
The channel map is the frozen MatrixMap.of_kraus K K.
finite_kraus_quantum_channel states the connection from complete Kraus families to QuantumChannel;
it is not on this supporting module's dependency path.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15645;
no_four_replacements lacks whole-family variation, sensitivity, and observational-dependence evidence.
DTR reading: DTR-Unregistered (Observe) for no_four_replacements; the designated result is exempt.
-/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.PureState.PureStateHandshake
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
namespace D5.S3.Quantum.QuantumChannels.PureProgramQubitObstruction

-- General finite indices are necessary for the product-index processor.
def IsChannel {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (T : Matrix A A ℂ → Matrix B B ℂ) : Prop :=
  ∃ r : ℕ, ∃ K : Fin r → Matrix B A ℂ,
    (∑ i, (K i)ᴴ * K i) = 1 ∧ ∀ rho, T rho = MatrixMap.of_kraus K K rho






private lemma gram_diag_zero {r : ℕ} (A : Matrix (Fin 2) (Fin r) ℂ) (j : Fin 2)
    (h : (A * (A)ᴴ) j j = 0) : A j = 0 := by
  apply dotProduct_self_star_eq_zero.mp
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct] using h

private lemma gram_diag_nonzero {r : ℕ} (A : Matrix (Fin 2) (Fin r) ℂ) (j : Fin 2)
    (h : (A * (A)ᴴ) j j ≠ 0) : A j ≠ 0 := by
  intro hz
  apply h
  simp [Matrix.single, Matrix.kronecker, rankOneDensity, Matrix.mul_apply, hz]

private lemma gram_plus_rows {r : ℕ} (A : Matrix (Fin 2) (Fin r) ℂ)
    (h : (A * (A)ᴴ) = (fun (_ _) => (1 / 2 : ℂ))) : A 0 = A 1 := by
  have hz : (fun i => A 0 i - A 1 i) ⬝ᵥ star (fun i => A 0 i - A 1 i) = 0 := by
    calc
      _ = ((A * (A)ᴴ) 0 0 - (A * (A)ᴴ) 0 1) - ((A * (A)ᴴ) 1 0 - (A * (A)ᴴ) 1 1) := by
        simp only [dotProduct, Pi.star_apply, star_sub, Matrix.mul_apply,
          Matrix.conjTranspose_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
        ring
      _ = 0 := by rw [h]; norm_num []
  have hv := dotProduct_self_star_eq_zero.mp hz
  ext i
  exact sub_eq_zero.mp (congrFun hv i)

-- Three distinct rankOneDensity outputs force every image to have dependent rows.
private theorem three_pure_outputs_rigidity {r : ℕ}
    (M : (Fin 2 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin r) ℂ)
    (p0 p1 pp : Fin 2 → ℂ)
    (h0 : ((M p0) * ((M p0))ᴴ) = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) (h1 : ((M p1) * ((M p1))ᴴ) = (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ))
    (hp : ((M pp) * ((M pp))ᴴ) = (fun (_ _) => (1 / 2 : ℂ))) :
    ∀ p, ∃ c d : ℂ, (c ≠ 0 ∨ d ≠ 0) ∧
      ∀ i, c * M p 0 i = d * M p 1 i := by
  classical
  have hz0 : M p0 1 = 0 := gram_diag_zero _ 1 (by rw [h0]; rfl)
  have hz1 : M p1 0 = 0 := gram_diag_zero _ 0 (by rw [h1]; rfl)
  have hn0 : M p0 0 ≠ 0 := gram_diag_nonzero _ 0 (by rw [h0]; norm_num [])
  have hn1 : M p1 1 ≠ 0 := gram_diag_nonzero _ 1 (by rw [h1]; norm_num [])
  have hind : LinearIndependent ℂ ![p0, p1] := by
    rw [linearIndependent_fin2]
    constructor
    · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using
        (show p1 ≠ 0 from fun h => hn1 (by ext i; simp [h]))
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      intro a he
      have hm := congrArg M he
      rw [M.map_smul] at hm
      apply hn0
      ext i
      have hi := congrArg (fun A : Matrix (Fin 2) (Fin r) ℂ => A 0 i) hm
      simpa [hz1] using hi.symm
  let B := basisOfPiSpaceOfLinearIndependent hind
  have expand (p : Fin 2 → ℂ) : p = (B.repr p 0) • p0 + (B.repr p 1) • p1 := by
    have he := B.sum_repr p
    simpa [B, coe_basisOfPiSpaceOfLinearIndependent, Fin.sum_univ_two] using he.symm
  let a := B.repr pp 0
  let b := B.repr pp 1
  have hmpp : M pp = a • M p0 + b • M p1 := by rw [expand pp, map_add, map_smul, map_smul]
  have ha : a ≠ 0 := by
    intro ha
    have hr : M pp 0 = 0 := by ext i; simp [hmpp, ha, hz1]
    have hg : ((M pp) * ((M pp))ᴴ) 0 0 = 0 := by simp [Matrix.single, Matrix.kronecker, rankOneDensity, Matrix.mul_apply, hr]
    rw [hp] at hg
    norm_num [] at hg
  have hb : b ≠ 0 := by
    intro hb
    have hr : M pp 1 = 0 := by ext i; simp [hmpp, hb, hz0]
    have hg : ((M pp) * ((M pp))ᴴ) 1 1 = 0 := by simp [Matrix.single, Matrix.kronecker, rankOneDensity, Matrix.mul_apply, hr]
    rw [hp] at hg
    norm_num [] at hg
  have hab (i : Fin r) : a * M p0 0 i = b * M p1 1 i := by
    have he := congrFun (gram_plus_rows (M pp) hp) i
    simpa [hmpp, hz0, hz1] using he
  intro p
  let u := B.repr p 0
  let v := B.repr p 1
  have hmp : M p = u • M p0 + v • M p1 := by rw [expand p, map_add, map_smul, map_smul]
  by_cases hu : u = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    intro i
    simp [hmp, hu, hz1]
  · refine ⟨v * a, u * b, Or.inr (mul_ne_zero hu hb), ?_⟩
    intro i
    simp only [hmp, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have hzi0 := congrFun hz0 i
    have hzi1 := congrFun hz1 i
    simp only [Pi.zero_apply] at hzi0 hzi1
    simp only [hzi0, hzi1, mul_zero, zero_add, add_zero]
    calc
      (v * a) * (u * M p0 0 i) = (u * v) * (a * M p0 0 i) := by ring
      _ = (u * v) * (b * M p1 1 i) := by rw [hab i]
      _ = (u * b) * (v * M p1 1 i) := by ring

private theorem four_target_obstruction {r : ℕ}
    (M : (Fin 2 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin r) ℂ)
    (p0 p1 pp pm : Fin 2 → ℂ)
    (h0 : ((M p0) * ((M p0))ᴴ) = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) (h1 : ((M p1) * ((M p1))ᴴ) = (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ))
    (hp : ((M pp) * ((M pp))ᴴ) = (fun (_ _) => (1 / 2 : ℂ))) (hm : ((M pm) * ((M pm))ᴴ) = ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) : False := by
  obtain ⟨c,d,hcd,he⟩ := three_pure_outputs_rigidity M p0 p1 pp h0 h1 hp pm
  have hx : c * ((M pm) * ((M pm))ᴴ) 0 0 = d * ((M pm) * ((M pm))ᴴ) 1 0 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, he i, mul_assoc]
  have hy : c * ((M pm) * ((M pm))ᴴ) 0 1 = d * ((M pm) * ((M pm))ᴴ) 1 1 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, he i, mul_assoc]
  rw [hm] at hx hy
  norm_num [Matrix.one_apply] at hx hy
  rcases hcd with hc | hd
  · exact hc hx
  · exact hd hy


private def programMatrix {d1 r : ℕ}
    (K : Fin r → Matrix (Fin 2) (Fin d1 × Fin 2) ℂ) (x : Fin d1) :
    (Fin 2 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin r) ℂ :=
  LinearMap.pi (fun j : Fin 2 => Matrix.mulVecLin (fun i a => K i j (x, a)))

private lemma kraus_pure_gram {d1 r : ℕ}
    (K : Fin r → Matrix (Fin 2) (Fin d1 × Fin 2) ℂ) (x : Fin d1) (psi : Fin 2 → ℂ) :
    (∑ i, K i * Matrix.kronecker (Matrix.single x x 1) (rankOneDensity psi) * (K i)ᴴ) =
      ((programMatrix K x psi) * ((programMatrix K x psi))ᴴ) := by
  ext j k
  simp only [Matrix.sum_apply]
  change (∑ i, (K i * Matrix.kronecker (Matrix.single x x 1) (rankOneDensity psi) * (K i)ᴴ) j k) =
    ∑ i, (∑ a : Fin 2, K i j (x,a) * psi a) * star (∑ a : Fin 2, K i k (x,a) * psi a)
  simp [Matrix.single, Matrix.kronecker, rankOneDensity, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.single, Matrix.kroneckerMap_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Finset.sum_mul, Finset.mul_sum,
    star_sum, star_mul, mul_assoc, mul_left_comm, mul_comm, ite_and]
  apply Finset.sum_congr rfl
  intro i hi
  ring

-- The input dimension and number of Kraus operators are unrestricted.
theorem no_four_replacements {d1 : ℕ}
    (P : Matrix (Fin d1 × Fin 2) (Fin d1 × Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (hP : IsChannel P) (x : Fin d1)
    (p0 p1 pp pm : Fin 2 → ℂ)
    (h0 : P (Matrix.kronecker (Matrix.single x x 1) (rankOneDensity p0)) = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ))
    (h1 : P (Matrix.kronecker (Matrix.single x x 1) (rankOneDensity p1)) = (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ))
    (hp : P (Matrix.kronecker (Matrix.single x x 1) (rankOneDensity pp)) = (fun (_ _) => (1 / 2 : ℂ)))
    (hm : P (Matrix.kronecker (Matrix.single x x 1) (rankOneDensity pm)) = ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) : False := by
  obtain ⟨r,K,hK,hPk⟩ := hP
  apply four_target_obstruction (programMatrix K x) p0 p1 pp pm
  · simpa only [hPk, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, kraus_pure_gram] using h0
  · simpa only [hPk, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, kraus_pure_gram] using h1
  · simpa only [hPk, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, kraus_pure_gram] using hp
  · simpa only [hPk, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, kraus_pure_gram] using hm

end D5.S3.Quantum.QuantumChannels.PureProgramQubitObstruction
