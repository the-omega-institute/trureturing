/- GID: D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.claim; result=D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.result; claim=D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.claim
   digest: A qubit measure-and-prepare channel refutes coherence domination. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#20020; Refuted)
  Direct frozen dependencies: F1, F6, F5, F2, F3, F4

Frozen declaration identities (each hash is a declaration statement_id):
F1: D5/S3/Quantum/Foundation/FiniteKrausChannel.MatrixMap
  Lean name: D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
  statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
F2: D5/S3/Quantum/Foundation/FiniteKrausChannel.IsCompletelyPositive
  Lean name: D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive
  statement_id: sha256:31bd68fc3c839750d1a8ac1474555b08fcd9579b1627c81db36a58f3172e1252
F3: D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus
  Lean name: D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
  statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
F4: D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus_isCompletelyPositive
  Lean name: D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive
  statement_id: sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f
F5: D5/S3/Quantum/Matrix/SpectralPower.mpow_two
  Lean name: D5.S3.Quantum.Matrix.SpectralPower.mpow_two
  statement_id: sha256:268ba73aab733cd496eb67ed52f5cbf866a6e4fed3856e0912a62124adca7ac5
F6: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.projectiveReadout
  Lean name: D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projectiveReadout
  statement_id: sha256:b3edc6179afd66a2e1084490dabd42950a8bf7721c01cdb7fd20a874df2c8d50

Private helper declarations:
phi_tp: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F1
phi_kraus: proof_shape: bind-only; escape_witness: none;
  consumers: phi_cp; Direct frozen dependencies: F3, F1
phi_cp: proof_shape: bind-only; escape_witness: none;
  consumers: choi_hermitian, result; Direct frozen dependencies: F2, F3, F1, F4
scalar_mpow: proof_shape: bind-only; escape_witness: none;
  consumers: renyi_scalar; Direct frozen dependencies: none
renyi_scalar: proof_shape: bind-only; escape_witness: none;
  consumers: renyi_sigma, choi_div; Direct frozen dependencies: F5
sigma_hermitian: proof_shape: bind-only; escape_witness: none;
  consumers: renyi_sigma; Direct frozen dependencies: none
sigma_trace_square: proof_shape: bind-only; escape_witness: none;
  consumers: renyi_sigma; Direct frozen dependencies: none
renyi_sigma: proof_shape: bind-only; escape_witness: none;
  consumers: input_div; Direct frozen dependencies: F5
choi_hermitian: proof_shape: bind-only; escape_witness: none;
  consumers: choi_div; Direct frozen dependencies: F2, F3, F1, F4
choi_square: proof_shape: bind-only; escape_witness: none;
  consumers: choi_div; Direct frozen dependencies: F1
choi_div: proof_shape: bind-only; escape_witness: none;
  consumers: coherence_upper; Direct frozen dependencies: F1, F2, F3, F4, F5
phi_dephase: proof_shape: bind-only; escape_witness: none;
  consumers: input_div; Direct frozen dependencies: F1, F6
sigma_dephase: proof_shape: bind-only; escape_witness: none;
  consumers: input_div; Direct frozen dependencies: F6
state_entries: proof_shape: bind-only; escape_witness: none;
  consumers: output_formula, input_div_le; Direct frozen dependencies: none
output_formula: proof_shape: bind-only; escape_witness: none;
  consumers: input_div; Direct frozen dependencies: F1
input_div: proof_shape: bind-only; escape_witness: none;
  consumers: input_div_le, rho0_div; Direct frozen dependencies: F1, F6, F5
input_div_le: proof_shape: bind-only; escape_witness: none;
  consumers: commutativity_lower; Direct frozen dependencies: F1, F6, F5
rho0_state: proof_shape: bind-only; escape_witness: none;
  consumers: rho0_div, commutativity_lower; Direct frozen dependencies: none
rho0_div: proof_shape: bind-only; escape_witness: none;
  consumers: commutativity_lower; Direct frozen dependencies: F1, F6, F5
commutativity_lower: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F1, F6, F5
quarter_state: proof_shape: bind-only; escape_witness: none;
  consumers: coherence_upper; Direct frozen dependencies: none
renyi_lower: proof_shape: bind-only; escape_witness: none;
  consumers: coherence_upper; Direct frozen dependencies: none
coherence_upper: proof_shape: bind-only; escape_witness: none;
  consumers: result; Direct frozen dependencies: F1, F2, F3, F4, F5

The source formulas inline spectral powers, density conditions, diagonal readout and
normalized Choi entries; proofs use the existing owners through these correspondences.
Choi Hermiticity follows from complete positivity through Choi's theorem.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

namespace D5.S3.Quantum.QuantumChannels.FanWuFeiChannelCoherenceDomination

open _root_.Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (IsCompletelyPositive)

/-- Eqs. (1)–(2), with z = 1 and real matrix powers defined by cfc. -/
noncomputable def renyiDiv {c : Type} [Fintype c] [DecidableEq c]
    (α : ℝ) (ρ σ : Matrix c c ℂ) : ℝ :=
  ((RCLike.re (cfc (fun x : ℝ => x ^ ((1 - α) / 2)) σ *
    cfc (fun x : ℝ => x ^ α) ρ * cfc (fun x : ℝ => x ^ ((1 - α) / 2)) σ).trace) ^
    (1 / α) - 1) / (α - 1)

/-- Eq. (7) at `z = 1`: `C_{α,1}(φ)`, the infimum of `D_{α,1}(M_φ, σ)` over incoherent states `σ` on `A × B`. -/
noncomputable def coherence {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (α : ℝ) (φ : MatrixMap a b ℂ) : ℝ :=
  sInf {r | ∃ σ : Matrix (a × b) (a × b) ℂ, (σ.PosSemidef ∧ σ.trace = 1) ∧ diagonal (fun i => σ i i) = σ ∧ r = renyiDiv α (fun p q => (Fintype.card a : ℂ)⁻¹ *
      φ (single p.1 q.1 1) p.2 q.2) σ}

/-- Eq. (10) at `z = 1`: `C̃_{α,1}(φ) = sup_ρ D_{α,1}(φ(Δρ), Δ(φρ))`. -/
noncomputable def commutativityCoherence {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (α : ℝ) (φ : MatrixMap a b ℂ) : ℝ :=
  sSup {r | ∃ ρ : Matrix a a ℂ, (ρ.PosSemidef ∧ ρ.trace = 1) ∧ r = renyiDiv α (φ (diagonal (fun i => ρ i i))) (diagonal (fun i => φ ρ i i))}

/-- The conjecture of Section 3: `C_{α,1}(φ) ≥ C̃_{α,1}(φ)` for every channel and every `α ∈ (0, 1) ∪ (1, 2]`. -/
def claim : Prop :=
  ∀ (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (φ : MatrixMap a b ℂ),
    IsCompletelyPositive φ → (∀ x, (φ x).trace = x.trace) →
      ∀ α : ℝ, (0 < α ∧ α < 1) ∨ (1 < α ∧ α ≤ 2) → commutativityCoherence α φ ≤ coherence α φ


open _root_.Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (IsCompletelyPositive)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (projectiveReadout)
noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

private def phi : MatrixMap (Fin 2) (Fin 2) ℂ where
  toFun x := x 0 0 • (fun t : ℝ => (!![1/2, (t:ℂ)/2; (t:ℂ)/2, 1/2] : Matrix (Fin 2) (Fin 2) ℂ)) (3/4) + x 1 1 • (fun t : ℝ => (!![1/2, (t:ℂ)/2; (t:ℂ)/2, 1/2] : Matrix (Fin 2) (Fin 2) ℂ)) (1/2)
  map_add' x y := by simp only [Matrix.add_apply, add_smul]; abel
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, smul_add, smul_smul] <;> ring

private theorem phi_tp (x : Matrix (Fin 2) (Fin 2) ℂ) : (phi x).trace = x.trace := by
  simp [trace, phi, Fin.sum_univ_two, Matrix.smul_apply]
  ring

private def K (k : Fin 16) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if j = (if k.val < 8 then 0 else 1) then
    if i = 0 then 1/4 else if k.val < 7 ∨ (8 ≤ k.val ∧ k.val < 14) then 1/4 else -1/4
    else 0

private theorem phi_kraus : of_kraus K K = phi := by
  ext x i j
  fin_cases i <;> fin_cases j <;>
    simp [of_kraus, K, phi, Matrix.mul_apply, conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.single, map_ofNat] <;> norm_num <;> ring

private theorem phi_cp : IsCompletelyPositive phi := by
  rw [← phi_kraus]
  exact of_kraus_isCompletelyPositive K

private theorem scalar_mpow {n : Type} [Fintype n] [DecidableEq n] (q p : ℝ) :
    cfc (fun x : ℝ => x ^ p) (q • (1 : Matrix n n ℂ)) = (q ^ p) • (1 : Matrix n n ℂ) := by
  simp only [← Algebra.algebraMap_eq_smul_one, cfc_algebraMap]

private theorem renyi_scalar {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (q : ℝ) (hq : 0 ≤ q) :
    renyiDiv 2 A (q • (1 : Matrix n n ℂ)) =
      Real.sqrt (q⁻¹ * (A * A).trace.re) - 1 := by
  have hp : (q ^ (-(1/2:ℝ))) ^ 2 = q⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
    norm_num [Real.rpow_neg_one]
  simp only [renyiDiv]
  norm_num only [show (1-(2:ℝ))/2 = -1/2 by norm_num, show (2:ℝ)-1 = 1 by norm_num, div_one]
  rw [show cfc (fun x : ℝ => x ^ (2:ℝ)) A = A * A from
    D5.S3.Quantum.Matrix.SpectralPower.mpow_two hA, scalar_mpow]
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul, ← pow_two,
    hp, trace_smul]
  simp only [RCLike.smul_re, smul_eq_mul, ← Real.sqrt_eq_rpow]
  rfl

private theorem sigma_hermitian (t : ℝ) : ((fun t : ℝ => (!![1/2, (t:ℂ)/2; (t:ℂ)/2, 1/2] : Matrix (Fin 2) (Fin 2) ℂ)) t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [map_ofNat]

private theorem sigma_trace_square (t : ℝ) :
    (((fun t : ℝ => (!![1/2, (t:ℂ)/2; (t:ℂ)/2, 1/2] : Matrix (Fin 2) (Fin 2) ℂ)) t * (fun t : ℝ => (!![1/2, (t:ℂ)/2; (t:ℂ)/2, 1/2] : Matrix (Fin 2) (Fin 2) ℂ)) t).trace).re = (1 + t^2)/2 := by
  simp [Matrix.mul_apply, trace, Fin.sum_univ_two, Complex.mul_re]
  ring

private theorem renyi_sigma (t : ℝ) :
    renyiDiv 2 ((fun t : ℝ => (!![1/2, (t:ℂ)/2; (t:ℂ)/2, 1/2] : Matrix (Fin 2) (Fin 2) ℂ)) t) ((1/2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      Real.sqrt (1+t^2) - 1 := by
  rw [renyi_scalar (sigma_hermitian t) (1/2) (by norm_num), sigma_trace_square]
  congr 2
  norm_num
  ring

private theorem choi_hermitian : (((Fintype.card (Fin 2) : ℂ)⁻¹ • Matrix.reindex (Equiv.prodComm (Fin 2) (Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2)) (choi_matrix phi))).IsHermitian := by
  have h := ((choi_PSD_iff_CP_map phi).mp phi_cp).isHermitian
  exact (h.reindex (Equiv.prodComm (Fin 2) (Fin 2))).smul (by norm_num [IsSelfAdjoint])

private theorem choi_square : ((((Fintype.card (Fin 2) : ℂ)⁻¹ • Matrix.reindex (Equiv.prodComm (Fin 2) (Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2)) (choi_matrix phi)) * ((Fintype.card (Fin 2) : ℂ)⁻¹ • Matrix.reindex (Equiv.prodComm (Fin 2) (Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2)) (choi_matrix phi))).trace).re = 45/128 := by
  norm_num [choi_matrix, Matrix.reindex, phi, Matrix.single, Matrix.mul_apply, trace,
    Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem choi_div :
    renyiDiv 2 (((Fintype.card (Fin 2) : ℂ)⁻¹ • Matrix.reindex (Equiv.prodComm (Fin 2) (Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2)) (choi_matrix phi))) ((1/4:ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) =
      Real.sqrt (45/32) - 1 := by
  rw [renyi_scalar choi_hermitian (1/4) (by norm_num), choi_square]
  norm_num
private theorem phi_dephase (x : Matrix (Fin 2) (Fin 2) ℂ) : phi (projectiveReadout x) = phi x := by
  ext i j
  simp [phi, projectiveReadout]

private theorem sigma_dephase (t : ℝ) :
    projectiveReadout ((fun t : ℝ => (!![1/2, (t:ℂ)/2; (t:ℂ)/2, 1/2] : Matrix (Fin 2) (Fin 2) ℂ)) t) = (1/2:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [projectiveReadout, Matrix.one_apply]

private theorem state_entries {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hρ : (ρ.PosSemidef ∧ ρ.trace = 1)) :
    ρ 0 0 = (ρ 0 0).re ∧ ρ 1 1 = ((1 - (ρ 0 0).re : ℝ) : ℂ) ∧
    0 ≤ (ρ 0 0).re ∧ (ρ 0 0).re ≤ 1 := by
  have h0 := Complex.nonneg_iff.mp (hρ.1.diag_nonneg (i := 0))
  have h1 := Complex.nonneg_iff.mp (hρ.1.diag_nonneg (i := 1))
  have ht : ρ 0 0 + ρ 1 1 = 1 := by
    simpa [trace, Fin.sum_univ_two] using hρ.2
  have htr := congrArg Complex.re ht
  simp only [Complex.add_re, Complex.one_re] at htr
  refine ⟨?_, ?_, h0.1, ?_⟩
  · apply Complex.ext <;> simp [h0.2.symm]
  · apply Complex.ext
    · simp only [Complex.ofReal_re]
      linarith
    · simp [h1.2.symm]
  · linarith [h1.1]

private theorem output_formula {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hρ : (ρ.PosSemidef ∧ ρ.trace = 1)) :
    phi ρ = (fun t : ℝ => (!![1/2, (t:ℂ)/2; (t:ℂ)/2, 1/2] : Matrix (Fin 2) (Fin 2) ℂ)) (1/2 + (ρ 0 0).re / 4) := by
  obtain ⟨h0,h1,_,_⟩ := state_entries hρ
  generalize (ρ 0 0).re = p at *
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phi, h0, h1, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_sub] <;> ring

private theorem input_div {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hρ : (ρ.PosSemidef ∧ ρ.trace = 1)) :
    renyiDiv 2 (phi (projectiveReadout ρ)) (projectiveReadout (phi ρ)) =
      Real.sqrt (1+(1/2+(ρ 0 0).re/4)^2) - 1 := by
  rw [phi_dephase, output_formula hρ, sigma_dephase, renyi_sigma]

private theorem input_div_le {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hρ : (ρ.PosSemidef ∧ ρ.trace = 1)) :
    renyiDiv 2 (phi (projectiveReadout ρ)) (projectiveReadout (phi ρ)) ≤ 1/4 := by
  rw [input_div hρ]
  have hp := (state_entries hρ).2.2
  have ht : 0 ≤ 1/2+(ρ 0 0).re/4 ∧ 1/2+(ρ 0 0).re/4 ≤ (3/4:ℝ) := by
    constructor <;> linarith [hp.1,hp.2]
  have hs : 1+(1/2+(ρ 0 0).re/4)^2 ≤ (25/16:ℝ) := by
    nlinarith [sq_nonneg (3/4-(1/2+(ρ 0 0).re/4))]
  have h := Real.sqrt_le_sqrt hs
  norm_num at h
  linarith

private def rho0 : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1,0]

private theorem rho0_state : (rho0.PosSemidef ∧ rho0.trace = 1) := by
  constructor
  · apply posSemidef_diagonal_iff.mpr
    norm_num
  · norm_num [rho0, trace, Fin.sum_univ_two]

private theorem rho0_div : renyiDiv 2 (phi (projectiveReadout rho0)) (projectiveReadout (phi rho0)) = 1/4 := by
  rw [input_div rho0_state]
  norm_num [rho0]

private theorem commutativity_lower : (1/4:ℝ) ≤ commutativityCoherence 2 phi := by
  apply le_csSup
  · refine ⟨1/4, ?_⟩
    rintro r ⟨ρ,hρ,rfl⟩
    exact input_div_le hρ
  · exact ⟨rho0,rho0_state,rho0_div.symm⟩

private theorem quarter_state :
    (((1/4:ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)).PosSemidef ∧
      ((1/4:ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)).trace = 1) := by
  constructor
  · exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (by norm_num : (0:ℝ) ≤ 1/4)
  · norm_num [trace_smul]

private theorem renyi_lower {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    -1 ≤ renyiDiv 2 A B := by
  unfold renyiDiv
  norm_num only [show (2:ℝ)-1=1 by norm_num, div_one]
  rw [← Real.sqrt_eq_rpow]
  rw [le_sub_iff_add_le, neg_add_cancel]
  exact Real.sqrt_nonneg _

private theorem coherence_upper : coherence 2 phi ≤ Real.sqrt (45/32)-1 := by
  rw [← choi_div]
  apply csInf_le
  · refine ⟨-1, ?_⟩
    rintro r ⟨σ,_,_,rfl⟩
    exact renyi_lower _ _
  · refine ⟨_,quarter_state,?_,rfl⟩
    ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [projectiveReadout, Matrix.one_apply]

theorem result : ¬ claim := by
  intro h
  have hd := h (Fin 2) (Fin 2) phi phi_cp phi_tp 2 (Or.inr ⟨by norm_num, by norm_num⟩)
  have hlt : Real.sqrt (45/32:ℝ)-1 < 1/4 := by
    have : Real.sqrt (45/32:ℝ) < 5/4 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith
  linarith [coherence_upper, commutativity_lower]


end
end D5.S3.Quantum.QuantumChannels.FanWuFeiChannelCoherenceDomination
