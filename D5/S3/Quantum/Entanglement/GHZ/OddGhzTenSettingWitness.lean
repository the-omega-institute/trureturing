/- GID: D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The ten-setting GHZ witness bounds fidelity and GME dimension for every odd d. -/
/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#16991; Proved)
Direct frozen dependencies (declaration identities):
P: D5/S3/Fourier/FullBispectrumStability.cyclic_parseval
   statement_id: sha256:cf058fd7c3e8951e784fa974b32ec85a1ae872d65002edf997031f47f95e76f4
S: D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
   statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
T: D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.trace_rank_bound
   statement_id: sha256:f173c1c803043e2a279526218a485709d5b0ae355ee3fae50b367d417897eeb6
H: D5/S3/Weil/ZetaLinear/Sylvester.hermForm_one (Lean: RHLinalg.hermForm_one)
   statement_id: sha256:0bee6888fa3690daa127e5b383b3b8d256de079f6eee0cf979026543af837ef4
   D5/S3/Weil/ZetaLinear/Sylvester.hermForm (Lean: RHLinalg.hermForm)
   statement_id: sha256:73fe60400b35034994e7c69515b0b2e4349284066d1b1d60c2cbc066f776f399
Q: D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector
   statement_id: sha256:78fe0d4d1dc92c646a7c648e05619ae560d343eda875b00add21a0dd6a5d958a
R: D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
   statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
J: D5/S3/Quantum/Information/PartialTraceMutualInformation.density_posSemidef
   statement_id: sha256:b799be7b0c6e16bb8e03b4bcf99946d7abbc95ac0078be4a08391bec19c88bdc
K: D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.schmidtRank
The public omega, basisVec, proj and witness definitions use the literal
preregistered expressions. Proofs use ZMod.stdAddChar and Matrix.vecMulVec.
Nine labels retain multiplicity at d = 1.
The spectral Ensemble is transported from Fin (Fintype.card iota) × Fin 1
to the arbitrary finite index type. The public SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector
supplies the real-part specialization of the complex projector identity.
The I owners import Ensemble from this module. Schmidt rank uses the frozen
owner K after flattening the two-party index with finProdFinEquiv; matrix
rank is invariant under this reindexing. Generality I follows this import.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17622
weight_le_one_of_total: proof_shape: bind-only; deps: none; consumer: spectral_ensemble_nonempty, FormationBounds.Selective.conditionalEnsemble, BraunsteinGhoshSeveriniStarRefutation.Star.starEnsemble.
spectral_ensemble_nonempty: proof_shape: bind-only; deps: R; consumer: density_ensemble, BraunsteinGhoshSeveriniStarRefutation.graph_ensemble_nonempty.
All theorems have escape_witness: none. Dependencies use H/J/K/P/Q/R/S/T above.
omega_pow_character: proof_shape: bind-only; deps: none; consumer: basisVec_character.
character_orthogonality: proof_shape: bind-only; deps: none; consumer: constrained_character_sum.
tuples_sum_zero: proof_shape: bind-only; deps: none; consumer: tuples_cast_sum_zero.
basisVec_character: proof_shape: bind-only; deps: none; consumer: projector_character.
projector_character: proof_shape: bind-only; deps: none; consumer: settingOp_entry.
constrained_character_sum: proof_shape: bind-only; deps: none; consumer: constrained_fin_sum.
finEquiv_eq_z: proof_shape: bind-only; deps: none; consumer: constrained_fin_sum,z_ofResidue.
constrained_fin_sum: proof_shape: bind-only; deps: none; consumer: settingOp_entry.
settingOp_entry: proof_shape: bind-only; deps: none; consumer: settingOp_shift_entry.
tuples_cast_sum_zero: proof_shape: bind-only; deps: none; consumer: witness_entry.
shifted_quadPhase: proof_shape: bind-only; deps: none; consumer: settingOp_shift_entry.
settingOp_shift_entry: proof_shape: bind-only; deps: none; consumer: witness_entry.
diagonalOp_entry: proof_shape: bind-only; deps: none; consumer: witness_entry.
tuples_grid_sum: proof_shape: bind-only; deps: none; consumer: witness_entry.
witness_entry: proof_shape: bind-only; deps: none; consumer: witness_block_entry.
cutRank_le_d: proof_shape: bind-only; deps: K; consumer: schmidtNumberLE_d.
cutRank_eq: proof_shape: bind-only; deps: K; consumer: cutRank_le_d,cut_diagonal_bound.
density_ensemble: proof_shape: bind-only; deps: J,R,S; consumer: schmidtNumberLE_d,witness_density_bound.
schmidtNumberLE_d: proof_shape: bind-only; deps: J,K,R,S; consumer: gmeDecomposable_d.
gmeDecomposable_d: proof_shape: bind-only; deps: J,K,R,S; consumer: gmeDim_mem.
gmeDim_mem: proof_shape: bind-only; deps: J,K,R,S; consumer: gmeDim_ghz_fidelity_bound.
diagonal_trace_rank_bound: proof_shape: bind-only; deps: T; consumer: cut_diagonal_bound.
ghz_overlap: proof_shape: bind-only; deps: none; consumer: ghz_overlap_normSq.
quadratic_energy: proof_shape: bind-only; deps: H; consumer: unit_energy,blockOp_quadratic.
ghz_overlap_normSq: proof_shape: bind-only; deps: none; consumer: pure_ghz_fidelity_bound,witness_quadratic_bound.
unit_energy: proof_shape: bind-only; deps: H; consumer: cut_diagonal_bound,witness_density_bound.
cut_diagonal_bound: proof_shape: bind-only; deps: H,K,T; consumer: pure_ghz_fidelity_bound.
pure_ghz_fidelity_bound: proof_shape: bind-only; deps: H,K,T; consumer: schmidt_ghz_fidelity_bound.
quadratic_rankone: proof_shape: bind-only; deps: Q,R; consumer: schmidt_ghz_fidelity_bound,blockOp_quadratic,witness_density_bound.
quadratic_sum: proof_shape: bind-only; deps: none; consumer: schmidt_ghz_fidelity_bound,gme_ghz_fidelity_bound,quadratic_smul,witness_density_bound.
schmidt_ghz_fidelity_bound: proof_shape: bind-only; deps: H,K,Q,R,S,T; consumer: gme_ghz_fidelity_bound.
gme_ghz_fidelity_bound: proof_shape: bind-only; deps: H,K,Q,R,S,T; consumer: gmeDim_ghz_fidelity_bound.
gmeDim_ghz_fidelity_bound: proof_shape: bind-only; deps: H,J,K,Q,R,S,T; consumer: result.
signed_injective: proof_shape: bind-only; deps: none; consumer: count_le_three.
two_cancel: proof_shape: bind-only; deps: none; consumer: count_le_three.
count_le_three: proof_shape: bind-only; deps: none; consumer: grid_dft_bound.
fourier_fibre_sum: proof_shape: bind-only; deps: none; consumer: grid_dft_bound.
dft_energy: proof_shape: bind-only; deps: P; consumer: grid_dft_bound.
grid_dft_bound: proof_shape: bind-only; deps: P; consumer: block_value_bound.
block_value_bound: proof_shape: bind-only; deps: P; consumer: witness_quadratic_bound.
z_ofResidue: proof_shape: bind-only; deps: none; consumer: witness_block_entry.
block_diagonal_iff: proof_shape: bind-only; deps: none; consumer: witness_block_entry.
fourier_product: proof_shape: bind-only; deps: none; consumer: blockOp_entry.
blockOp_entry: proof_shape: bind-only; deps: none; consumer: witness_block_entry.
quadratic_smul: proof_shape: bind-only; deps: none; consumer: blockOp_quadratic.
fourierVec_overlap: proof_shape: bind-only; deps: none; consumer: blockOp_quadratic.
normSq_overlap_comm: proof_shape: bind-only; deps: none; consumer: blockOp_quadratic.
blockOp_quadratic: proof_shape: bind-only; deps: H,Q,R; consumer: witness_quadratic_blocks.
gridLabel_mul_signed: proof_shape: bind-only; deps: none; consumer: witness_block_entry.
witness_block_entry: proof_shape: bind-only; deps: none; consumer: witness_quadratic_blocks.
quadratic_reindex: proof_shape: bind-only; deps: none; consumer: witness_quadratic_blocks.
witness_quadratic_blocks: proof_shape: bind-only; deps: H,Q,R; consumer: witness_quadratic_bound.
block_energy: proof_shape: bind-only; deps: none; consumer: witness_quadratic_bound.
diagonal_block_sum: proof_shape: bind-only; deps: none; consumer: witness_quadratic_bound.
witness_quadratic_bound: proof_shape: bind-only; deps: H,P,Q,R; consumer: witness_density_bound.
witness_density_bound: proof_shape: bind-only; deps: H,J,P,Q,R,S; consumer: fidelity_lower_bound,result.
fidelity_lower_bound: proof_shape: bind-only; deps: H,J,P,Q,R,S; consumer: result.
result: proof_shape: bind-only; deps: H,J,K,P,Q,R,S,T; consumer: settling result.
-/
import D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
import D5.S3.Fourier.FullBispectrumStability
import D5.S3.Weil.ZetaLinear.Sylvester
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation
open Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (schmidtRank)
open scoped Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
/-- `ω = exp(2πi/d)`. -/
def omega (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)
/-- The basis vector `|e_l^{(j)}⟩ = d^{-1/2} Σ_m ω^{m(l+jm)} |m⟩`. -/
def basisVec (d j l : ℕ) : Fin d → ℂ :=
  fun m => (1 / Real.sqrt d : ℂ) * omega d ^ ((m : ℕ) * (l + j * (m : ℕ)))
/-- The rank-one projector `|v⟩⟨v|`. -/
def proj {d : ℕ} (v : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ := Matrix.vecMulVec v (star v)
/-- The basis-index tuples `L`, Eq. (V1). -/
def tuples (d : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (1, 1, d - 2), (d - 1, d - 1, 2), (0, 1, d - 1), (1, 0, d - 1),
    (0, d - 1, 1), (1, d - 1, 0), (d - 1, 0, 1), (d - 1, 1, 0)]
/-- The witness operator `𝒲_d`, Eq. (V2). -/
def witness (d : ℕ) : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ :=
  (3 : ℂ) • ∑ l : Fin d,
      proj (Pi.single l 1) ⊗ₖ (proj (Pi.single l 1) ⊗ₖ proj (Pi.single l 1)) +
    ((tuples d).map fun j =>
      ∑ l ∈ (Finset.univ : Finset (Fin d × Fin d × Fin d)).filter
          (fun l => ((l.1 : ℕ) + (l.2.1 : ℕ) + (l.2.2 : ℕ)) % d = 0),
        proj (basisVec d j.1 l.1) ⊗ₖ
          (proj (basisVec d j.2.1 l.2.1) ⊗ₖ proj (basisVec d j.2.2 l.2.2))).sum
/-- The GHZ vector `ghz_{3,d} = d^{-1/2} Σ_i |i⟩^{⊗3}`, Eq. (5). -/
def ghz (d : ℕ) : Fin d × Fin d × Fin d → ℂ :=
  (1 / Real.sqrt d : ℂ) • ∑ i : Fin d, (Pi.single (i, i, i) 1 : Fin d × Fin d × Fin d → ℂ)
/-- `W_d(ρ) = tr(𝒲_d ρ)`. -/
def witnessValue (d : ℕ) (ρ : DensityState (Fin d × Fin d × Fin d)) : ℝ :=
  (Matrix.trace (witness d * CStarMatrix.ofMatrix.symm ρ.1)).re
/-- `F_ghz(ρ) = ⟨ghz|ρ|ghz⟩`. -/
def ghzFidelity (d : ℕ) (ρ : DensityState (Fin d × Fin d × Fin d)) : ℝ :=
  (star (ghz d) ⬝ᵥ (CStarMatrix.ofMatrix.symm ρ.1 *ᵥ ghz d)).re
/-- Schmidt rank across the bipartition that separates party `k` from the other two. -/
def cutRank {d : ℕ} (k : Fin 3) (ψ : Fin d × Fin d × Fin d → ℂ) : ℕ :=
  schmidtRank (fun p : Fin d × Fin (d * d) =>
    let q := finProdFinEquiv.symm p.2
    match k with
    | ⟨0, _⟩ => ψ (p.1, q.1, q.2)
    | ⟨1, _⟩ => ψ (q.1, p.1, q.2)
    | ⟨_, _⟩ => ψ (q.1, q.2, p.1))
private theorem cutRank_eq {d : ℕ} (k : Fin 3) (ψ : Fin d × Fin d × Fin d → ℂ) :
    cutRank k ψ = (Matrix.of fun i (j : Fin d × Fin d) =>
      match k with
      | ⟨0, _⟩ => ψ (i, j.1, j.2)
      | ⟨1, _⟩ => ψ (j.1, i, j.2)
      | ⟨_, _⟩ => ψ (j.1, j.2, i)).rank := by
  fin_cases k <;> dsimp only [cutRank, schmidtRank]
  · exact Matrix.rank_submatrix
      (fun (i : Fin d) (j : Fin d × Fin d) => ψ (i, j.1, j.2))
      (Equiv.refl (Fin d)) finProdFinEquiv.symm
  · exact Matrix.rank_submatrix
      (fun (i : Fin d) (j : Fin d × Fin d) => ψ (j.1, i, j.2))
      (Equiv.refl (Fin d)) finProdFinEquiv.symm
  · exact Matrix.rank_submatrix
      (fun (i : Fin d) (j : Fin d × Fin d) => ψ (j.1, j.2, i))
      (Equiv.refl (Fin d)) finProdFinEquiv.symm
/-- `σ` has Schmidt number at most `r` across bipartition `k`. -/
def SchmidtNumberLE {d : ℕ} (k : Fin 3) (r : ℕ)
    (σ : DensityState (Fin d × Fin d × Fin d)) : Prop :=
  ∃ (m : ℕ) (p : Fin m → ℝ) (ψ : Fin m → Fin d × Fin d × Fin d → ℂ),
    (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i, star (ψ i) ⬝ᵥ ψ i = 1) ∧
    (∀ i, cutRank k (ψ i) ≤ r) ∧
    CStarMatrix.ofMatrix.symm σ.1 = ∑ i, ((p i : ℝ) : ℂ) • Matrix.vecMulVec (ψ i) (star (ψ i))
/-- A decomposition `ρ = Σ_{S|S̄} q_{S|S̄} σ_{S|S̄}` with every `r_{S|S̄} ≤ r`, Eq. (2). -/
def GMEDecomposable {d : ℕ} (r : ℕ) (ρ : DensityState (Fin d × Fin d × Fin d)) : Prop :=
  ∃ (q : Fin 3 → ℝ) (σ : Fin 3 → DensityState (Fin d × Fin d × Fin d)),
    (∀ k, 0 ≤ q k) ∧ ∑ k, q k = 1 ∧ (∀ k, SchmidtNumberLE k r (σ k)) ∧
    CStarMatrix.ofMatrix.symm ρ.1 = ∑ k, ((q k : ℝ) : ℂ) • CStarMatrix.ofMatrix.symm (σ k).1
/-- The GME-dimension `D_GME(ρ)`, Eq. (2). -/
def gmeDim {d : ℕ} (ρ : DensityState (Fin d × Fin d × Fin d)) : ℕ :=
  sInf {r | GMEDecomposable r ρ}
/-- (V3) and (V4) for every odd local dimension. -/
def claim : Prop :=
  ∀ d : ℕ, Odd d → ∀ ρ : DensityState (Fin d × Fin d × Fin d),
    witnessValue d ρ ≤ 3 + 9 * (gmeDim ρ : ℝ) / d ∧
      ghzFidelity d ρ ≥ (witnessValue d ρ - 3) / 9
set_option linter.unusedTactic false
private theorem omega_pow_character {d : ℕ} [NeZero d] (n : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / d)) ^ n = ZMod.stdAddChar (n : ZMod d) := by
  have hc : ZMod.stdAddChar (n : ZMod d) =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / d) := by
    simpa only [Int.cast_natCast, Int.cast_natCast] using ZMod.stdAddChar_coe (N := d) (n : ℤ)
  rw [hc, ← Complex.exp_nat_mul]
  congr 1
  ring
private theorem character_orthogonality {d : ℕ} [NeZero d] (a : ZMod d) :
    ∑ t : ZMod d, ZMod.stdAddChar (t * a) = if a = 0 then (d : ℂ) else 0 := by
  simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar d)
private theorem tuples_sum_zero {d : ℕ} (hd : Odd d) (j : ℕ × ℕ × ℕ) (hj : j ∈ tuples d) :
    (j.1 + j.2.1 + j.2.2) % d = 0 := by
  have hdpos : 0 < d := hd.pos
  by_cases h1 : d = 1
  · subst d
    exact Nat.mod_one _
  · have hd2 : 2 ≤ d := by omega
    simp only [tuples, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prod.fst, Prod.snd]
    all_goals first
      | (convert Nat.zero_mod d using 2 <;> omega)
      | (convert Nat.mod_self d using 2 <;> omega)
      | (rw [show d - 1 + (d - 1) + 2 = d + d by omega, Nat.add_mod]; simp)
private theorem basisVec_character {d : ℕ} [NeZero d] (j l : ℕ) (m : Fin d) :
    basisVec d j l m = (1 / Real.sqrt d : ℂ) *
      ZMod.stdAddChar ((m.val : ZMod d) * ((l : ZMod d) + (j : ZMod d) * (m.val : ZMod d))) := by
  rw [basisVec, omega, omega_pow_character]
  simp [ Nat.cast_mul, Nat.cast_add]
private theorem projector_character {d : ℕ} [NeZero d] (j l : ℕ) (m n : Fin d) :
    Matrix.vecMulVec (basisVec d j l) (star (basisVec d j l)) m n = (1 / d : ℂ) *
      ZMod.stdAddChar (((m.val : ZMod d) - (n.val : ZMod d)) * (l : ZMod d) + (j : ZMod d) * ((m.val : ZMod d) ^ 2 - (n.val : ZMod d) ^ 2)) := by
  have hc : (1 / Real.sqrt d : ℂ) * (1 / Real.sqrt d : ℂ) = 1 / d := by
    rw [← pow_two, one_div, inv_pow, ← Complex.ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  simp only [ Matrix.vecMulVec_apply, Pi.star_apply, basisVec_character,
    star_mul, star_div₀, star_one, Complex.star_def, Complex.conj_ofReal]
  rw [← AddChar.map_neg_eq_conj]
  calc
    _ = ((1 / Real.sqrt d : ℂ) * (1 / Real.sqrt d : ℂ)) *
        (ZMod.stdAddChar ((m.val : ZMod d) * ((l : ZMod d) + (j : ZMod d) * (m.val : ZMod d))) *
          ZMod.stdAddChar (-((n.val : ZMod d) * ((l : ZMod d) + (j : ZMod d) * (n.val : ZMod d))))) := by ring
    _ = _ := by
      rw [hc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
private theorem constrained_character_sum {d : ℕ} [NeZero d] (u v w : ZMod d) :
    (∑ l : ZMod d × ZMod d × ZMod d,
      if l.1 + l.2.1 + l.2.2 = 0 then
        ZMod.stdAddChar (l.1*u + l.2.1*v + l.2.2*w) else 0) =
      if u = w ∧ v = w then (d : ℂ)^2 else 0 := by
  classical
  have he (a b c : ZMod d) : (a+b+c = 0) ↔ c = -(a+b) := by
    exact add_eq_zero_iff_eq_neg'
  simp only [Fintype.sum_prod_type, he, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hp (a b : ZMod d) :
      ZMod.stdAddChar (a*u+b*v+(-(a+b))*w) = ZMod.stdAddChar (a*(u-w)) * ZMod.stdAddChar (b*(v-w)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hp, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [character_orthogonality, character_orthogonality]
  by_cases hu : u = w <;> by_cases hv : v = w <;> simp [hu,hv,sub_eq_zero,pow_two]
private theorem finEquiv_eq_z {d : ℕ} [NeZero d] (m : Fin d) : ZMod.finEquiv d m = (m.val : ZMod d) := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d =>
    change m = Fin.ofNat (d+1) m.val
    exact (Fin.cast_val_eq_self m).symm
private theorem constrained_fin_sum {d : ℕ} [NeZero d] (u v w : ZMod d) :
    (∑ l : Fin d × Fin d × Fin d,
      if ((l.1 : ℕ) + (l.2.1 : ℕ) + (l.2.2 : ℕ)) % d = 0 then
        ZMod.stdAddChar ((l.1.val : ZMod d)*u + (l.2.1.val : ZMod d)*v + (l.2.2.val : ZMod d)*w) else 0) =
      if u = w ∧ v = w then (d : ℂ)^2 else 0 := by
  classical
  have hc (l : Fin d × Fin d × Fin d) :
      (((l.1 : ℕ) + (l.2.1 : ℕ) + (l.2.2 : ℕ)) % d = 0) ↔
        (l.1.val : ZMod d) + (l.2.1.val : ZMod d) + (l.2.2.val : ZMod d) = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
    simp []
  simp only [hc]
  let e := (ZMod.finEquiv d).toEquiv
  let e3 := Equiv.prodCongr e (Equiv.prodCongr e e)
  rw [Fintype.sum_equiv e3 _
    (fun l : ZMod d × ZMod d × ZMod d => if l.1 + l.2.1 + l.2.2 = 0 then
      ZMod.stdAddChar (l.1*u + l.2.1*v + l.2.2*w) else 0)
    (by intro l; simp [e3,e,finEquiv_eq_z])]
  exact constrained_character_sum u v w
private def settingOp (d : ℕ) (j : ℕ × ℕ × ℕ) :
    Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ :=
  ∑ l ∈ (Finset.univ : Finset (Fin d × Fin d × Fin d)).filter
      (fun l => ((l.1 : ℕ) + (l.2.1 : ℕ) + (l.2.2 : ℕ)) % d = 0),
    Matrix.vecMulVec (basisVec d j.1 l.1) (star (basisVec d j.1 l.1)) ⊗ₖ
      (Matrix.vecMulVec (basisVec d j.2.1 l.2.1) (star (basisVec d j.2.1 l.2.1)) ⊗ₖ Matrix.vecMulVec (basisVec d j.2.2 l.2.2) (star (basisVec d j.2.2 l.2.2)))
private theorem settingOp_entry {d : ℕ} [NeZero d] (j : ℕ × ℕ × ℕ)
    (m n : Fin d × Fin d × Fin d) :
    settingOp d j m n =
      if (m.1.val : ZMod d)-(n.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d) ∧ (m.2.1.val : ZMod d)-(n.2.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d) then
        (1 / d : ℂ) * ZMod.stdAddChar ((QuadraticMap.weightedSumSquares (ZMod d) ![(j.1 : ZMod d), (j.2.1 : ZMod d), (j.2.2 : ZMod d)] ![(m.1.val : ZMod d), (m.2.1.val : ZMod d), (m.2.2.val : ZMod d)]) - (QuadraticMap.weightedSumSquares (ZMod d) ![(j.1 : ZMod d), (j.2.1 : ZMod d), (j.2.2 : ZMod d)] ![(n.1.val : ZMod d), (n.2.1.val : ZMod d), (n.2.2.val : ZMod d)])) else 0 := by
  classical
  let Q := (QuadraticMap.weightedSumSquares (ZMod d) ![(j.1 : ZMod d), (j.2.1 : ZMod d), (j.2.2 : ZMod d)] ![(m.1.val : ZMod d), (m.2.1.val : ZMod d), (m.2.2.val : ZMod d)]) - (QuadraticMap.weightedSumSquares (ZMod d) ![(j.1 : ZMod d), (j.2.1 : ZMod d), (j.2.2 : ZMod d)] ![(n.1.val : ZMod d), (n.2.1.val : ZMod d), (n.2.2.val : ZMod d)])
  let u := (m.1.val : ZMod d)-(n.1.val : ZMod d)
  let v := (m.2.1.val : ZMod d)-(n.2.1.val : ZMod d)
  let w := (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d)
  have hp (l : Fin d × Fin d × Fin d) :
      (Matrix.vecMulVec (basisVec d j.1 l.1) (star (basisVec d j.1 l.1)) ⊗ₖ
        (Matrix.vecMulVec (basisVec d j.2.1 l.2.1) (star (basisVec d j.2.1 l.2.1)) ⊗ₖ Matrix.vecMulVec (basisVec d j.2.2 l.2.2) (star (basisVec d j.2.2 l.2.2)))) m n =
      ((1/d : ℂ)^3 * ZMod.stdAddChar Q) * ZMod.stdAddChar ((l.1.val : ZMod d)*u+(l.2.1.val : ZMod d)*v+(l.2.2.val : ZMod d)*w) := by
    simp only [Matrix.kroneckerMap_apply, projector_character]
    have he : (((m.1.val : ZMod d)-(n.1.val : ZMod d))*(l.1.val : ZMod d) + (j.1 : ZMod d)*((m.1.val : ZMod d)^2-(n.1.val : ZMod d)^2)) +
        ((((m.2.1.val : ZMod d)-(n.2.1.val : ZMod d))*(l.2.1.val : ZMod d) + (j.2.1 : ZMod d)*((m.2.1.val : ZMod d)^2-(n.2.1.val : ZMod d)^2)) +
        (((m.2.2.val : ZMod d)-(n.2.2.val : ZMod d))*(l.2.2.val : ZMod d) + (j.2.2 : ZMod d)*((m.2.2.val : ZMod d)^2-(n.2.2.val : ZMod d)^2))) =
        Q + ((l.1.val : ZMod d)*u+(l.2.1.val : ZMod d)*v+(l.2.2.val : ZMod d)*w) := by
      simp only [Q, u, v, w, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three]
      dsimp
      ring
    calc
      _ = (1/d : ℂ)^3 * ZMod.stdAddChar (
        (((m.1.val : ZMod d)-(n.1.val : ZMod d))*(l.1.val : ZMod d) + (j.1 : ZMod d)*((m.1.val : ZMod d)^2-(n.1.val : ZMod d)^2)) +
        ((((m.2.1.val : ZMod d)-(n.2.1.val : ZMod d))*(l.2.1.val : ZMod d) + (j.2.1 : ZMod d)*((m.2.1.val : ZMod d)^2-(n.2.1.val : ZMod d)^2)) +
        (((m.2.2.val : ZMod d)-(n.2.2.val : ZMod d))*(l.2.2.val : ZMod d) + (j.2.2 : ZMod d)*((m.2.2.val : ZMod d)^2-(n.2.2.val : ZMod d)^2)))) := by
          simp only [AddChar.map_add_eq_mul]; ring
      _ = _ := by rw [he, AddChar.map_add_eq_mul]; ring
  rw [settingOp]
  simp only [Matrix.sum_apply, Finset.sum_filter, hp]
  have hs : (∑ l : Fin d × Fin d × Fin d,
      if ((l.1 : ℕ)+(l.2.1 : ℕ)+(l.2.2 : ℕ)) % d = 0 then
        ((1/d : ℂ)^3 * ZMod.stdAddChar Q) * ZMod.stdAddChar ((l.1.val : ZMod d)*u+(l.2.1.val : ZMod d)*v+(l.2.2.val : ZMod d)*w) else 0) =
      ((1/d : ℂ)^3 * ZMod.stdAddChar Q) * ∑ l : Fin d × Fin d × Fin d,
        if ((l.1 : ℕ)+(l.2.1 : ℕ)+(l.2.2 : ℕ)) % d = 0 then
          ZMod.stdAddChar ((l.1.val : ZMod d)*u+(l.2.1.val : ZMod d)*v+(l.2.2.val : ZMod d)*w) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> simp
  rw [hs, constrained_fin_sum]
  change _ = if u = w ∧ v = w then (1/d : ℂ)*ZMod.stdAddChar Q else 0
  split_ifs <;> simp
  field_simp
private theorem tuples_cast_sum_zero {d : ℕ} (hd : Odd d) (j : ℕ × ℕ × ℕ)
    (hj : j ∈ tuples d) : (j.1 : ZMod d)+j.2.1+j.2.2 = 0 := by
  have h := (Nat.dvd_iff_mod_eq_zero).mpr (tuples_sum_zero hd j hj)
  simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff _ d).mpr h
private theorem shifted_quadPhase {d : ℕ} (j : ℕ × ℕ × ℕ)
    (hj : (j.1 : ZMod d)+j.2.1+j.2.2 = 0)
    (m n : Fin d × Fin d × Fin d)
    (hm : (m.1.val : ZMod d)-(n.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d) ∧ (m.2.1.val : ZMod d)-(n.2.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d)) :
    (QuadraticMap.weightedSumSquares (ZMod d) ![(j.1 : ZMod d), (j.2.1 : ZMod d), (j.2.2 : ZMod d)] ![(m.1.val : ZMod d), (m.2.1.val : ZMod d), (m.2.2.val : ZMod d)]) - (QuadraticMap.weightedSumSquares (ZMod d) ![(j.1 : ZMod d), (j.2.1 : ZMod d), (j.2.2 : ZMod d)] ![(n.1.val : ZMod d), (n.2.1.val : ZMod d), (n.2.2.val : ZMod d)]) =
      2*((m.2.2.val : ZMod d)-(n.2.2.val : ZMod d))*((j.1 : ZMod d)*((n.1.val : ZMod d)-(n.2.2.val : ZMod d))+
        (j.2.1 : ZMod d)*((n.2.1.val : ZMod d)-(n.2.2.val : ZMod d))) := by
  have h1 : (m.1.val : ZMod d) = (n.1.val : ZMod d)+((m.2.2.val : ZMod d)-(n.2.2.val : ZMod d)) := by simpa only [add_comm] using (eq_add_of_sub_eq hm.1)
  have h2 : (m.2.1.val : ZMod d) = (n.2.1.val : ZMod d)+((m.2.2.val : ZMod d)-(n.2.2.val : ZMod d)) := by simpa only [add_comm] using (eq_add_of_sub_eq hm.2)
  simp only [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three]
  dsimp
  rw [h1,h2]
  linear_combination (((m.2.2.val : ZMod d))^2-((n.2.2.val : ZMod d))^2)*hj
private theorem settingOp_shift_entry {d : ℕ} [NeZero d] (j : ℕ × ℕ × ℕ)
    (hj : (j.1 : ZMod d)+j.2.1+j.2.2 = 0)
    (m n : Fin d × Fin d × Fin d) :
    settingOp d j m n =
      if (m.1.val : ZMod d)-(n.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d) ∧ (m.2.1.val : ZMod d)-(n.2.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d) then
        (1 / d : ℂ) * ZMod.stdAddChar (2*((m.2.2.val : ZMod d)-(n.2.2.val : ZMod d))*
          ((j.1 : ZMod d)*((n.1.val : ZMod d)-(n.2.2.val : ZMod d))+(j.2.1 : ZMod d)*((n.2.1.val : ZMod d)-(n.2.2.val : ZMod d)))) else 0 := by
  rw [settingOp_entry]
  split_ifs with h
  · rw [shifted_quadPhase j hj m n h]
  · rfl
private def diagonalOp (d : ℕ) :
    Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ :=
  ∑ l : Fin d, Matrix.vecMulVec (Pi.single l (1 : ℂ)) (star (Pi.single l (1 : ℂ))) ⊗ₖ
    (Matrix.vecMulVec (Pi.single l (1 : ℂ)) (star (Pi.single l (1 : ℂ))) ⊗ₖ Matrix.vecMulVec (Pi.single l (1 : ℂ)) (star (Pi.single l (1 : ℂ))))
private theorem diagonalOp_entry {d : ℕ} (m n : Fin d × Fin d × Fin d) :
    diagonalOp d m n = if m = n ∧ m.1 = m.2.1 ∧ m.2.1 = m.2.2 then 1 else 0 := by
  classical
  have ht (l : Fin d) :
      (Matrix.vecMulVec (Pi.single l (1 : ℂ)) (star (Pi.single l (1 : ℂ))) ⊗ₖ (Matrix.vecMulVec (Pi.single l (1 : ℂ)) (star (Pi.single l (1 : ℂ))) ⊗ₖ Matrix.vecMulVec (Pi.single l (1 : ℂ)) (star (Pi.single l (1 : ℂ))))) m n =
        if m = (l,l,l) ∧ n = (l,l,l) then 1 else 0 := by
    simp only [Pi.star_single, star_one, ← Matrix.single_eq_single_vecMulVec_single,
      Matrix.single_kronecker_single, one_mul, Matrix.single_apply, eq_comm]
  simp only [diagonalOp, Matrix.sum_apply, ht]
  by_cases h : m = n ∧ m.1 = m.2.1 ∧ m.2.1 = m.2.2
  · rcases h with ⟨rfl,h1,h2⟩
    have hm : m = (m.1,m.1,m.1) := by ext <;> simp_all
    rw [hm]
    simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro l _
    rw [if_neg]
    intro hh
    apply h
    simp_all
private def signed {d : ℕ} (x : ZMod d) : Fin 3 → ZMod d := ![-x, 0, x]
private theorem tuples_grid_sum {d : ℕ} (hd : Odd d) (f : ZMod d → ZMod d → ℂ) :
    ((tuples d).map (fun j => f (j.1 : ZMod d) (j.2.1 : ZMod d))).sum =
      ∑ a : Fin 3, ∑ b : Fin 3, f ((signed (1 : ZMod d)) a) ((signed (1 : ZMod d)) b) := by
  have hd1 : 1 ≤ d := hd.pos
  have hc : ((d-1 : ℕ) : ZMod d) = -1 := by
    rw [Nat.cast_sub hd1, ZMod.natCast_self, Nat.cast_one, zero_sub]
  simp only [tuples, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.cast_zero, Nat.cast_one, hc, signed, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num <;> ring
private theorem witness_entry {d : ℕ} [NeZero d] (hd : Odd d) (m n : Fin d × Fin d × Fin d) :
    witness d m n =
      (if m = n ∧ m.1 = m.2.1 ∧ m.2.1 = m.2.2 then 3 else 0) +
      (if (m.1.val : ZMod d)-(n.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d) ∧ (m.2.1.val : ZMod d)-(n.2.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d) then
        (1 / d : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          ZMod.stdAddChar (2*((m.2.2.val : ZMod d)-(n.2.2.val : ZMod d))*
            ((signed (1 : ZMod d)) a*((n.1.val : ZMod d)-(n.2.2.val : ZMod d))+(signed (1 : ZMod d)) b*((n.2.1.val : ZMod d)-(n.2.2.val : ZMod d)))) else 0) := by
  classical
  have hw : witness d = (3 : ℂ) • diagonalOp d + ((tuples d).map (settingOp d)).sum := rfl
  rw [hw]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, diagonalOp_entry]
  congr 1
  · split_ifs <;> simp
  · have hm : (((tuples d).map (settingOp d)).sum) m n =
        ((tuples d).map (fun j => settingOp d j m n)).sum := by
      exact Complex.ext rfl rfl
    rw [hm]
    have he : ((tuples d).map (fun j => settingOp d j m n)) =
      (tuples d).map (fun j =>
        if (m.1.val : ZMod d)-(n.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d) ∧ (m.2.1.val : ZMod d)-(n.2.1.val : ZMod d) = (m.2.2.val : ZMod d)-(n.2.2.val : ZMod d) then
          (1/d : ℂ)*ZMod.stdAddChar (2*((m.2.2.val : ZMod d)-(n.2.2.val : ZMod d))*
            ((j.1 : ZMod d)*((n.1.val : ZMod d)-(n.2.2.val : ZMod d))+(j.2.1 : ZMod d)*((n.2.1.val : ZMod d)-(n.2.2.val : ZMod d)))) else 0) := by
      apply List.map_congr_left
      intro j hj
      exact settingOp_shift_entry j (tuples_cast_sum_zero hd j hj) m n
    rw [he]
    split_ifs
    · rw [List.sum_map_mul_left]
      congr 1
      exact tuples_grid_sum hd (fun a b => ZMod.stdAddChar (2*((m.2.2.val : ZMod d)-(n.2.2.val : ZMod d))*
        (a*((n.1.val : ZMod d)-(n.2.2.val : ZMod d))+b*((n.2.1.val : ZMod d)-(n.2.2.val : ZMod d)))))
    · simp
end D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
namespace D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
open scoped MatrixOrder ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
private theorem cutRank_le_d {d : ℕ} (k : Fin 3) (ψ : Fin d × Fin d × Fin d → ℂ) :
    cutRank k ψ ≤ d := by
  rw [cutRank_eq]
  exact (Matrix.rank_le_card_height _).trans (by simp)
structure Ensemble {p q : ℕ} (ρ : (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)) where
  N : ℕ
  weight : Fin N → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  le_one : ∀ i, weight i ≤ 1
  total : ∑ i, weight i = 1
  psi : Fin N → ((Fin p × Fin q) → ℂ)
  unit : ∀ i, ∑ x, ‖psi i x‖ ^ 2 = 1
  average : ∑ i, (weight i : ℂ) • rankOneDensity (psi i) = ρ
theorem weight_le_one_of_total {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℝ) (nonneg : ∀ i, 0 ≤ weight i) (total : ∑ i, weight i = 1)
    (i : ι) : weight i ≤ 1 := by
  rw [← total]
  exact Finset.single_le_sum (fun j _ => nonneg j) (Finset.mem_univ i)
theorem spectral_ensemble_nonempty {p q : ℕ} (ρ : (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ))
    (hρ : ρ.PosSemidef) (ht : ρ.trace=1) : Nonempty (Ensemble ρ) := by
  classical
  let e := Fintype.equivFin ((Fin p × Fin q))
  let U := hρ.1.eigenvectorUnitary
  have total : ∑ v, hρ.1.eigenvalues v = 1 := by
    have hh := congrArg Complex.re hρ.1.trace_eq_sum_eigenvalues
    simpa [ht,Complex.re_sum] using hh.symm
  have unit (v : (Fin p × Fin q)) : ∑ x, ‖U x v‖^2 = 1 := by
    change ∑ x, ‖(hρ.1.eigenvectorBasis v) x‖^2 = 1
    rw [← EuclideanSpace.norm_sq_eq,hρ.1.eigenvectorBasis.orthonormal.norm_eq_one]
    norm_num
  have average : ∑ v, (hρ.1.eigenvalues v : ℂ) • rankOneDensity (fun x => U x v) = ρ := by
    apply Eq.trans (b := Unitary.conjStarAlgAut ℂ _ hρ.1.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hρ.1.eigenvalues))) ?_ hρ.1.spectral_theorem.symm
    ext x y
    simp [Unitary.conjStarAlgAut_apply,Matrix.mul_apply,Matrix.diagonal,rankOneDensity,
      Matrix.vecMulVec_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,U]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨{
    N := Fintype.card ((Fin p × Fin q))
    weight := fun i => hρ.1.eigenvalues (e.symm i)
    nonneg := fun i => hρ.eigenvalues_nonneg _
    le_one := fun i => weight_le_one_of_total _ (fun v => hρ.eigenvalues_nonneg v) total (e.symm i)
    total := ?_
    psi := fun i x => U x (e.symm i)
    unit := fun i => unit _
    average := ?_
  }⟩
  · rw [Equiv.sum_comp e.symm]; exact total
  · exact (Equiv.sum_comp e.symm
      (fun v => (hρ.1.eigenvalues v : ℂ) • rankOneDensity (fun x => U x v))).trans average
private theorem density_ensemble {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityState ι) :
    ∃ (m : ℕ) (p : Fin m → ℝ) (ψ : Fin m → ι → ℂ),
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i, star (ψ i) ⬝ᵥ ψ i = 1) ∧
      CStarMatrix.ofMatrix.symm ρ.1 =
        ∑ i, (p i : ℂ) • Matrix.vecMulVec (ψ i) (star (ψ i)) := by
  classical
  let e : (Fin (Fintype.card ι) × Fin 1) ≃ ι :=
    (Equiv.prodUnique (Fin (Fintype.card ι)) (Fin 1)).trans (Fintype.equivFin ι).symm
  let A := CStarMatrix.ofMatrix.symm ρ.1
  have hp : A.PosSemidef :=
    D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef ρ
  let B := A.submatrix e e
  have ht : B.trace = 1 := by
    change (∑ j, A (e j) (e j)) = 1
    exact (e.sum_comp (fun j => A j j)).trans ρ.2.2
  obtain ⟨v⟩ := spectral_ensemble_nonempty B (hp.submatrix e) ht
  refine ⟨v.N, v.weight, fun i j => v.psi i (e.symm j), v.nonneg, v.total, ?_, ?_⟩
  · intro i
    have hn : (∑ j : ι, ‖v.psi i (e.symm j)‖ ^ 2) = 1 :=
      (e.symm.sum_comp (fun j => ‖v.psi i j‖ ^ 2)).trans (v.unit i)
    change (∑ j : ι, star (v.psi i (e.symm j)) * v.psi i (e.symm j)) = 1
    simp_rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [← Complex.ofReal_sum, hn]
    rfl
  · ext j k
    have h := congrArg (fun M => M (e.symm j) (e.symm k)) v.average
    simpa only [B, rankOneDensity, Matrix.submatrix_apply, Equiv.apply_symm_apply,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Pi.star_apply] using h.symm
private theorem schmidtNumberLE_d {d : ℕ} (k : Fin 3)
    (ρ : DensityState (Fin d × Fin d × Fin d)) : SchmidtNumberLE k d ρ := by
  obtain ⟨m,p,ψ,hp,hs,hu,hav⟩ := density_ensemble ρ
  exact ⟨m,p,ψ,hp,hs,hu,fun i => cutRank_le_d k (ψ i),hav⟩
private theorem gmeDecomposable_d {d : ℕ}
    (ρ : DensityState (Fin d × Fin d × Fin d)) : GMEDecomposable d ρ := by
  refine ⟨fun k => if k = 0 then 1 else 0, fun _ => ρ, ?_, ?_,
    fun k => schmidtNumberLE_d k ρ, ?_⟩
  · intro k
    change (0 : ℝ) ≤ if k = 0 then 1 else 0
    split_ifs <;> norm_num
  · simp
  · simp
private theorem gmeDim_mem {d : ℕ} (ρ : DensityState (Fin d × Fin d × Fin d)) :
    GMEDecomposable (gmeDim ρ) ρ := by
  exact Nat.sInf_mem (s := {r | GMEDecomposable r ρ}) ⟨d, gmeDecomposable_d ρ⟩
private theorem diagonal_trace_rank_bound {d : ℕ} (A : Matrix (Fin d) (Fin d × Fin d) ℂ) :
    Complex.normSq (∑ i, A i (i,i)) ≤
      (A.rank : ℝ) * ∑ i, ∑ j, Complex.normSq (A i j) := by
  classical
  let S := LinearMap.range A.mulVecLin
  let b := Module.finBasis ℂ S
  let col (j : Fin d × Fin d) : S := ⟨fun i => A i j, by
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]⟩
  let U : Matrix (Fin (Module.finrank ℂ S)) (Fin d) ℂ :=
    fun s i => star ((b s : Fin d → ℂ) i)
  let W : Matrix (Fin (Module.finrank ℂ S)) (Fin d) ℂ :=
    fun s i => b.repr (col (i,i)) s
  have hUW : Uᴴ * W = fun i j => A i (j,j) := by
    ext i j
    have he := congrArg (fun v : S => (v : Fin d → ℂ) i) (b.sum_repr (col (j,j)))
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, W,
      star_star, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm] using he
  have hh := D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.trace_rank_bound (Module.finrank ℂ S) d U W
  rw [hUW] at hh
  change Complex.normSq (∑ i, A i (i,i)) ≤
    (A.rank : ℝ) * ∑ i, ∑ j, Complex.normSq (A i (j,j)) at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun j _ => Finset.single_le_sum (f := fun k => Complex.normSq (A i (j,k)))
    (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
private theorem ghz_overlap {d : ℕ} (ψ : Fin d × Fin d × Fin d → ℂ) :
    star (ghz d) ⬝ᵥ ψ = (1 / Real.sqrt d : ℂ) * ∑ i, ψ (i,i,i) := by
  classical
  simp [ghz, star_smul, star_sum, smul_dotProduct, sum_dotProduct,
    Pi.star_single, single_dotProduct]
private theorem quadratic_energy {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    (star g ⬝ᵥ g).re = ∑ i, Complex.normSq (g i) := by
  classical
  simpa only [RHLinalg.hermForm, Matrix.one_mulVec, RCLike.re_to_complex,
    Complex.normSq_eq_norm_sq] using RHLinalg.hermForm_one g
private theorem ghz_overlap_normSq {d : ℕ} (v : Fin d × Fin d × Fin d → ℂ) :
    Complex.normSq (star (ghz d) ⬝ᵥ v) = (1/(d : ℝ))*Complex.normSq (∑ i, v (i,i,i)) := by
  rw [ghz_overlap, Complex.normSq_mul]
  have hn : Complex.normSq (1 / Real.sqrt d : ℂ) = 1 / (d : ℝ) := by
    simp only [one_div, Complex.normSq_inv, Complex.normSq_ofReal]
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [hn]
private theorem unit_energy {ι : Type*} [Fintype ι] (ψ : ι → ℂ)
    (hu : star ψ ⬝ᵥ ψ = 1) : ∑ i, Complex.normSq (ψ i) = 1 := by
  simpa only [hu, Complex.one_re] using (quadratic_energy ψ).symm
private theorem cut_diagonal_bound {d : ℕ} (k : Fin 3)
    (ψ : Fin d × Fin d × Fin d → ℂ) (hu : star ψ ⬝ᵥ ψ = 1) :
    Complex.normSq (∑ i, ψ (i,i,i)) ≤ cutRank k ψ := by
  rw [cutRank_eq]
  have he := unit_energy ψ hu
  rw [Fintype.sum_prod_type] at he
  simp only [Fintype.sum_prod_type] at he
  fin_cases k
  · have h := diagonal_trace_rank_bound (fun i p => ψ (i,p.1,p.2))
    simp only [Fintype.sum_prod_type, he, mul_one] at h
    convert h using 1 <;> rfl
  · have h := diagonal_trace_rank_bound (fun i p => ψ (p.1,i,p.2))
    have he' : (∑ i, ∑ j, ∑ l, Complex.normSq (ψ (j,i,l))) = 1 := by
      rw [Finset.sum_comm]; exact he
    simp only [Fintype.sum_prod_type, he', mul_one] at h
    convert h using 1 <;> rfl
  · have h := diagonal_trace_rank_bound (fun i p => ψ (p.1,p.2,i))
    have he' : (∑ i, ∑ j, ∑ l, Complex.normSq (ψ (j,l,i))) = 1 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (f := fun i l => Complex.normSq (ψ (_,l,i)))]
      exact he
    simp only [Fintype.sum_prod_type, he', mul_one] at h
    convert h using 1 <;> rfl
private theorem pure_ghz_fidelity_bound {d r : ℕ} (k : Fin 3)
    (ψ : Fin d × Fin d × Fin d → ℂ) (hu : star ψ ⬝ᵥ ψ = 1)
    (hr : cutRank k ψ ≤ r) : Complex.normSq (star (ghz d) ⬝ᵥ ψ) ≤ (r : ℝ) / d := by
  have hdiag : Complex.normSq (∑ i, ψ (i,i,i)) ≤ (r : ℝ) :=
    (cut_diagonal_bound k ψ hu).trans (by exact_mod_cast hr)
  rw [ghz_overlap_normSq]
  calc
    _ ≤ (1/(d : ℝ)) * r := mul_le_mul_of_nonneg_left hdiag (by positivity)
    _ = _ := by ring
private theorem quadratic_rankone {ι : Type*} [Fintype ι] (g ψ : ι → ℂ) :
    (star g ⬝ᵥ (Matrix.vecMulVec ψ (star ψ) *ᵥ g)).re =
      Complex.normSq (star g ⬝ᵥ ψ) := by
  simpa only [rankOneDensity, Complex.ofReal_re] using
    congrArg Complex.re (D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector g ψ)
private theorem quadratic_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → ℂ) (p : κ → ℝ) (A : κ → Matrix ι ι ℂ) :
    (star g ⬝ᵥ ((∑ i, (p i : ℂ) • A i) *ᵥ g)).re =
      ∑ i, p i * (star g ⬝ᵥ (A i *ᵥ g)).re := by
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
private theorem schmidt_ghz_fidelity_bound {d r : ℕ} (k : Fin 3)
    (ρ : DensityState (Fin d × Fin d × Fin d)) (hr : SchmidtNumberLE k r ρ) :
    ghzFidelity d ρ ≤ (r : ℝ) / d := by
  obtain ⟨m,p,ψ,hp,hs,hu,hc,he⟩ := hr
  rw [ghzFidelity, he, quadratic_sum]
  simp only [quadratic_rankone]
  calc
    _ ≤ ∑ i, p i * ((r : ℝ) / d) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (pure_ghz_fidelity_bound k (ψ i) (hu i) (hc i)) (hp i)
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
private theorem gme_ghz_fidelity_bound {d r : ℕ}
    (ρ : DensityState (Fin d × Fin d × Fin d)) (hr : GMEDecomposable r ρ) :
    ghzFidelity d ρ ≤ (r : ℝ) / d := by
  obtain ⟨q,σ,hq,hs,hc,he⟩ := hr
  rw [ghzFidelity, he, quadratic_sum]
  calc
    _ ≤ ∑ k, q k * ((r : ℝ) / d) := Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (schmidt_ghz_fidelity_bound k (σ k) (hc k)) (hq k)
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]
private theorem gmeDim_ghz_fidelity_bound {d : ℕ}
    (ρ : DensityState (Fin d × Fin d × Fin d)) :
    ghzFidelity d ρ ≤ (gmeDim ρ : ℝ) / d :=
  gme_ghz_fidelity_bound ρ (gmeDim_mem ρ)
end D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
open Finset
set_option linter.unusedTactic false
namespace D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
noncomputable section
private theorem signed_injective {d : ℕ} (hd : Odd d) {x : ZMod d} (hx : x ≠ 0) :
    Function.Injective (signed x) := by
  have hn := ZMod.ne_neg_self hd hx
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [signed, eq_comm]
private theorem two_cancel {d : ℕ} (hd : Odd d) {x y : ZMod d} (h : 2*x = 2*y) : x = y := by
  exact ((ZMod.isUnit_iff_coprime 2 d).mpr hd.coprime_two_left).mul_left_cancel h
private theorem count_le_three {d : ℕ} (hd : Odd d) (x y s : ZMod d)
    (hxy : x ≠ 0 ∨ y ≠ 0) : (Multiset.countP (fun a : Fin 3 × Fin 3 => 2 * (signed x a.1 + signed y a.2) = s) (Finset.univ : Finset (Fin 3 × Fin 3)).val) ≤ 3 := by
  classical
  let S := (univ : Finset (Fin 3 × Fin 3)).filter
    (fun a => 2 * (signed x a.1 + signed y a.2) = s)
  rw [Multiset.countP_eq_card_filter]
  change S.card ≤ 3
  rcases hxy with hx | hy
  · have hi : (S : Set (Fin 3 × Fin 3)).InjOn Prod.snd := by
      intro a ha b hb hab
      apply Prod.ext _ hab
      apply signed_injective hd hx
      have h := two_cancel hd ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
      simpa only [hab, add_left_inj] using h
    simpa using (card_le_card_of_injOn (t := (univ : Finset (Fin 3))) Prod.snd (by simp [Set.MapsTo]) hi)
  · have hi : (S : Set (Fin 3 × Fin 3)).InjOn Prod.fst := by
      intro a ha b hb hab
      apply Prod.ext hab
      apply signed_injective hd hy
      have h := two_cancel hd ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
      simpa only [hab, add_right_inj] using h
    simpa using (card_le_card_of_injOn (t := (univ : Finset (Fin 3))) Prod.fst (by simp [Set.MapsTo]) hi)
end
noncomputable section
private def freq {d : ℕ} (x y : ZMod d) (p : Fin 3 × Fin 3) : ZMod d :=
  2*(signed x p.1 + signed y p.2)
private theorem fourier_fibre_sum {d : ℕ} [NeZero d] (x y : ZMod d) (f : ZMod d → ℝ) :
    (∑ p : Fin 3 × Fin 3, f (freq x y p)) = ∑ s : ZMod d, ((Multiset.countP (fun a : Fin 3 × Fin 3 => 2 * (signed x a.1 + signed y a.2) = s) (Finset.univ : Finset (Fin 3 × Fin 3)).val) : ℝ) * f s := by
  classical
  simpa only [Multiset.countP_eq_card_filter, freq, Finset.sum_const, nsmul_eq_mul, Finset.card_def, Finset.filter_val] using
    (Finset.sum_fiberwise' Finset.univ (freq x y) f).symm
private theorem dft_energy {d : ℕ} [NeZero d] (f : ZMod d → ℂ) :
    ∑ s, Complex.normSq (ZMod.dft f s) = (d : ℝ) * ∑ t, Complex.normSq (f t) := by
  have h := D5.S3.Fourier.FullBispectrumStability.cyclic_parseval f
  rw [Fintype.expect_eq_sum_div_card, ZMod.card] at h
  simp only [← Complex.normSq_eq_norm_sq] at h
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  exact (eq_div_iff hd).mp h |>.symm.trans (mul_comm _ _)
private theorem grid_dft_bound {d : ℕ} [NeZero d] (hd : Odd d) (x y : ZMod d)
    (hxy : x ≠ 0 ∨ y ≠ 0) (f : ZMod d → ℂ) :
    (∑ p : Fin 3 × Fin 3, Complex.normSq (ZMod.dft f (freq x y p))) ≤
      3*(d : ℝ) * ∑ t, Complex.normSq (f t) := by
  rw [fourier_fibre_sum x y (fun s => Complex.normSq (ZMod.dft f s))]
  calc
    _ ≤ ∑ s : ZMod d, 3 * Complex.normSq (ZMod.dft f s) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right
        (by exact_mod_cast count_le_three hd x y s hxy) (Complex.normSq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, dft_energy]; ring
private def blockValue {d : ℕ} [NeZero d] (x y : ZMod d) (f : ZMod d → ℂ) : ℝ :=
  (if x = 0 ∧ y = 0 then 3 else 0) * ∑ t, Complex.normSq (f t) +
    (1 / (d : ℝ)) * ∑ p : Fin 3 × Fin 3, Complex.normSq (ZMod.dft f (freq x y p))
private theorem block_value_bound {d : ℕ} [NeZero d] (hd : Odd d) (x y : ZMod d) (f : ZMod d → ℂ) :
    blockValue x y f ≤ 3 * ∑ t, Complex.normSq (f t) +
      (if x = 0 ∧ y = 0 then 9/(d : ℝ)*Complex.normSq (∑ t, f t) else 0) := by
  classical
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  by_cases hxy : x = 0 ∧ y = 0
  · rcases hxy with ⟨rfl,rfl⟩
    simp [blockValue, freq, signed, ZMod.dft_apply_zero, Fin.sum_univ_succ,
      Fintype.sum_prod_type, Fin.forall_fin_succ]
    ring_nf
    exact le_rfl
  · have hn : x ≠ 0 ∨ y ≠ 0 := by
      exact Decidable.not_and_iff_or_not.mp hxy
    have h := mul_le_mul_of_nonneg_left (grid_dft_bound hd x y hn f)
      (show 0 ≤ 1/(d : ℝ) by positivity)
    simp only [blockValue, if_neg hxy, zero_mul, zero_add, add_zero]
    have he (a : ℝ) : 1/(d : ℝ)*(3*(d : ℝ)*a) = 3*a := by
      field_simp
    simpa only [he] using h
end
end D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
namespace D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
noncomputable section
private theorem z_ofResidue {d : ℕ} [NeZero d] (x : ZMod d) : ((((ZMod.finEquiv d).symm x) : ℕ) : ZMod d) = x := by
  rw [← finEquiv_eq_z]
  exact (ZMod.finEquiv d).apply_symm_apply x
private def blockEquiv (d : ℕ) [NeZero d] :
    (ZMod d × ZMod d × ZMod d) ≃ (Fin d × Fin d × Fin d) :=
  (Equiv.prodAssoc (ZMod d) (ZMod d) (ZMod d)).symm |>.trans
    (Equiv.prodCongrLeft (fun t : ZMod d =>
      Equiv.prodCongr (Equiv.addRight t) (Equiv.addRight t))) |>.trans
    (Equiv.prodAssoc (ZMod d) (ZMod d) (ZMod d)) |>.trans
    (Equiv.prodCongr (ZMod.finEquiv d).symm.toEquiv
      (Equiv.prodCongr (ZMod.finEquiv d).symm.toEquiv (ZMod.finEquiv d).symm.toEquiv))
private theorem block_diagonal_iff {d : ℕ} [NeZero d] (p : ZMod d × ZMod d × ZMod d) :
    ((blockEquiv d p).1 = (blockEquiv d p).2.1 ∧
      (blockEquiv d p).2.1 = (blockEquiv d p).2.2) ↔ p.1 = 0 ∧ p.2.1 = 0 := by
  have he (x y : ZMod d) : (ZMod.finEquiv d).symm x = (ZMod.finEquiv d).symm y ↔ x = y :=
    (ZMod.finEquiv d).symm.injective.eq_iff
  simp only [blockEquiv, Equiv.trans_apply, Equiv.prodCongrLeft_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, Equiv.prodAssoc_symm_apply,
    Equiv.coe_addRight, Prod.map_apply, Prod.fst, Prod.snd, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, he]
  constructor
  · intro h
    constructor
    · linear_combination h.1 + h.2
    · linear_combination h.2
  · rintro ⟨h1,h2⟩
    simp [h1,h2]
private theorem fourier_product {d : ℕ} [NeZero d] (s t u : ZMod d) :
    (fun s t => ZMod.stdAddChar (t*s)) s t * star ((fun s t => ZMod.stdAddChar (t*s)) s u) = ZMod.stdAddChar ((t-u)*s) := by
  rw [ RCLike.star_def, ← AddChar.map_neg_eq_conj,
    ← AddChar.map_add_eq_mul]
  congr 1
  ring
private def blockOp {d : ℕ} [NeZero d] (x y : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  ((if x=0 ∧ y=0 then 3 else 0 : ℝ) : ℂ) • 1 +
    ((1/(d : ℝ) : ℝ) : ℂ) • ∑ p : Fin 3 × Fin 3,
      Matrix.vecMulVec ((fun s t => ZMod.stdAddChar (t*s)) (freq x y p)) (star ((fun s t => ZMod.stdAddChar (t*s)) (freq x y p)))
private theorem blockOp_entry {d : ℕ} [NeZero d] (x y t u : ZMod d) :
    blockOp x y t u =
      ((if x=0 ∧ y=0 then 3 else 0 : ℝ) : ℂ) * (if t=u then 1 else 0) +
        (1/d : ℂ) * ∑ p : Fin 3 × Fin 3, ZMod.stdAddChar ((t-u)*freq x y p) := by
  classical
  simp only [blockOp, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, Matrix.one_apply, fourier_product]
  simp
private theorem quadratic_smul {ι : Type*} [Fintype ι] (g : ι → ℂ) (r : ℝ) (A : Matrix ι ι ℂ) :
    (star g ⬝ᵥ (((r : ℂ) • A) *ᵥ g)).re = r * (star g ⬝ᵥ (A *ᵥ g)).re := by
  simpa only [Fintype.sum_unique] using
    quadratic_sum (κ := Unit) g (fun _ => r) (fun _ => A)
private theorem fourierVec_overlap {d : ℕ} [NeZero d] (f : ZMod d → ℂ) (s : ZMod d) :
    star ((fun s t => ZMod.stdAddChar (t*s)) s) ⬝ᵥ f = ZMod.dft f s := by
  simpa only [dotProduct, Pi.star_apply, RCLike.star_def,
    ← AddChar.map_neg_eq_conj, smul_eq_mul] using (ZMod.dft_apply f s).symm
private theorem normSq_overlap_comm {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    Complex.normSq (star f ⬝ᵥ g) = Complex.normSq (star g ⬝ᵥ f) := by
  rw [star_dotProduct f g, RCLike.star_def, Complex.normSq_conj]
private theorem blockOp_quadratic {d : ℕ} [NeZero d] (x y : ZMod d) (f : ZMod d → ℂ) :
    (star f ⬝ᵥ (blockOp x y *ᵥ f)).re = blockValue x y f := by
  classical
  simp only [blockOp, Matrix.add_mulVec, dotProduct_add, Complex.add_re,
    quadratic_smul, Matrix.one_mulVec, quadratic_energy]
  congr 1
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum,
    quadratic_rankone, normSq_overlap_comm f, fourierVec_overlap, blockValue]
private theorem gridLabel_mul_signed {d : ℕ} (x : ZMod d) (a : Fin 3) :
    (signed (1 : ZMod d)) a * x = signed x a := by
  fin_cases a <;> simp [signed]
private theorem witness_block_entry {d : ℕ} [NeZero d] (hd : Odd d)
    (p q : ZMod d × ZMod d × ZMod d) :
    witness d (blockEquiv d p) (blockEquiv d q) =
      if p.1=q.1 ∧ p.2.1=q.2.1 then blockOp p.1 p.2.1 p.2.2 q.2.2 else 0 := by
  classical
  have hb : ((((blockEquiv d p).1 : ℕ) : ZMod d)-(((blockEquiv d q).1 : ℕ) : ZMod d) =
        (((blockEquiv d p).2.2 : ℕ) : ZMod d)-(((blockEquiv d q).2.2 : ℕ) : ZMod d) ∧
      (((blockEquiv d p).2.1 : ℕ) : ZMod d)-(((blockEquiv d q).2.1 : ℕ) : ZMod d) =
        (((blockEquiv d p).2.2 : ℕ) : ZMod d)-(((blockEquiv d q).2.2 : ℕ) : ZMod d)) ↔
        p.1=q.1 ∧ p.2.1=q.2.1 := by
    simp only [blockEquiv, Equiv.trans_apply, Equiv.prodCongrLeft_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, Equiv.prodAssoc_symm_apply,
    Equiv.coe_addRight, Prod.map_apply, Prod.fst, Prod.snd, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, z_ofResidue]
    constructor
    · intro h
      constructor
      · linear_combination h.1
      · linear_combination h.2
    · rintro ⟨h1,h2⟩
      simp [h1,h2]
  rw [witness_entry hd]
  simp only [(blockEquiv d).injective.eq_iff, block_diagonal_iff, hb]
  by_cases h : p.1=q.1 ∧ p.2.1=q.2.1
  · rcases p with ⟨x,y,t⟩
    rcases q with ⟨x',y',u⟩
    simp only [Prod.fst,Prod.snd] at h
    obtain ⟨hx,hy⟩ := h
    subst x'
    subst y'
    simp only [Prod.fst,Prod.snd,eq_self_iff_true,and_self,if_true]
    rw [blockOp_entry]
    simp only [blockEquiv, Equiv.trans_apply, Equiv.prodCongrLeft_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, Equiv.prodAssoc_symm_apply,
    Equiv.coe_addRight, Prod.map_apply, Prod.fst, Prod.snd, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, z_ofResidue, add_sub_cancel_right,
      Prod.mk.injEq, and_self, true_and, freq, Fintype.sum_prod_type,
      gridLabel_mul_signed]
    have hc (a b : Fin 3) :
        2*(t-u)*(signed x a+signed y b) =
          (t-u)*(2*(signed x a+signed y b)) := by ring
    simp only [hc]
    by_cases hxy : x=0 ∧ y=0 <;> by_cases htu : t=u <;> simp [hxy,htu]
  · rw [if_neg h,if_neg h]
    have hpq : p ≠ q := by intro he; apply h; simp [he]
    simp [hpq]
private theorem quadratic_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (v : ι → ℂ) (A : Matrix ι ι ℂ) :
    star v ⬝ᵥ (A *ᵥ v) = star (v ∘ e) ⬝ᵥ (A.submatrix e e *ᵥ (v ∘ e)) := by
  classical
  rw [Matrix.submatrix_mulVec_equiv]
  simpa only [Function.comp_def, Equiv.apply_symm_apply, Pi.star_def] using
    (comp_equiv_dotProduct_comp_equiv (star v) (A *ᵥ v) e).symm
private theorem witness_quadratic_blocks {d : ℕ} [NeZero d] (hd : Odd d)
    (v : Fin d × Fin d × Fin d → ℂ) :
    (star v ⬝ᵥ (witness d *ᵥ v)).re =
      ∑ x : ZMod d, ∑ y : ZMod d,
        blockValue x y (fun t => v (blockEquiv d (x,y,t))) := by
  classical
  rw [quadratic_reindex (blockEquiv d)]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Function.comp_apply,
    Matrix.submatrix_apply, witness_block_entry hd, Fintype.sum_prod_type,
    Prod.fst,Prod.snd]
  simp only [ite_and, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.re_sum] using
    blockOp_quadratic x y (fun t => v (blockEquiv d (x,y,t)))
private theorem block_energy {d : ℕ} [NeZero d] (v : Fin d × Fin d × Fin d → ℂ) :
    (∑ x : ZMod d, ∑ y : ZMod d, ∑ t : ZMod d,
      Complex.normSq (v (blockEquiv d (x,y,t)))) = ∑ m, Complex.normSq (v m) := by
  simpa only [Fintype.sum_prod_type] using
    (blockEquiv d).sum_comp (fun m => Complex.normSq (v m))
private theorem diagonal_block_sum {d : ℕ} [NeZero d] (v : Fin d × Fin d × Fin d → ℂ) :
    (∑ t : ZMod d, v (blockEquiv d (0,0,t))) = ∑ i : Fin d, v (i,i,i) := by
  simp only [blockEquiv, Equiv.trans_apply, Equiv.prodCongrLeft_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, Equiv.prodAssoc_symm_apply,
    Equiv.coe_addRight, Prod.map_apply, Prod.fst, Prod.snd, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, zero_add]
  convert (ZMod.finEquiv d).symm.toEquiv.sum_comp (fun i => v (i,i,i)) using 1 <;> rfl
private theorem witness_quadratic_bound {d : ℕ} [NeZero d] (hd : Odd d)
    (v : Fin d × Fin d × Fin d → ℂ) :
    (star v ⬝ᵥ (witness d *ᵥ v)).re ≤
      9*Complex.normSq (star (ghz d) ⬝ᵥ v)+3*∑ m,Complex.normSq (v m) := by
  classical
  rw [witness_quadratic_blocks hd]
  calc
    _ ≤ ∑ x : ZMod d, ∑ y : ZMod d,
        (3 * ∑ t, Complex.normSq (v (blockEquiv d (x,y,t))) +
          if x=0 ∧ y=0 then 9/(d : ℝ)*Complex.normSq (∑ t, v (blockEquiv d (x,y,t))) else 0) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        block_value_bound hd x y (fun t => v (blockEquiv d (x,y,t)))
    _ = _ := by
      simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel,
        Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        ← Finset.mul_sum, block_energy, diagonal_block_sum, ghz_overlap_normSq]
      ring
private theorem witness_density_bound {d : ℕ} [NeZero d] (hd : Odd d)
    (ρ : DensityState (Fin d × Fin d × Fin d)) :
    witnessValue d ρ ≤ 9*ghzFidelity d ρ+3 := by
  classical
  obtain ⟨m,p,ψ,hp,hs,hu,he⟩ := density_ensemble ρ
  have hw : witnessValue d ρ =
      ∑ i, p i * (star (ψ i) ⬝ᵥ (witness d *ᵥ ψ i)).re := by
    rw [witnessValue,he]
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, smul_eq_mul,
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, dotProduct_comm]
  have hf : ghzFidelity d ρ =
      ∑ i, p i * Complex.normSq (star (ghz d) ⬝ᵥ ψ i) := by
    rw [ghzFidelity,he,quadratic_sum]
    simp only [quadratic_rankone]
  rw [hw]
  calc
    _ ≤ ∑ i, p i * (9*Complex.normSq (star (ghz d) ⬝ᵥ ψ i)+3) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hp i)
      simpa only [unit_energy (ψ i) (hu i), mul_one] using witness_quadratic_bound hd (ψ i)
    _ = _ := by
      rw [hf]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
private theorem fidelity_lower_bound {d : ℕ} [NeZero d] (hd : Odd d)
    (ρ : DensityState (Fin d × Fin d × Fin d)) :
    ghzFidelity d ρ ≥ (witnessValue d ρ-3)/9 := by
  linarith [witness_density_bound hd ρ]
theorem result : claim := by
  intro d hd ρ
  letI : NeZero d := ⟨Nat.ne_of_gt hd.pos⟩
  have hW := witness_density_bound hd ρ
  have hF := gmeDim_ghz_fidelity_bound ρ
  constructor
  · rw [mul_div_assoc]
    linarith
  · exact fidelity_lower_bound hd ρ
end
end D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
