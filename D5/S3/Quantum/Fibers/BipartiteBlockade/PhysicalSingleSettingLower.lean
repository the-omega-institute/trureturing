/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/PhysicalSingleSettingLower
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/PhysicalSingleSettingLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced diagonal blockade perturbations lift to physical single-setting ambiguities by coherent edge flow. -/

import D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator
import D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual
import D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode
import D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Matrix MatrixOrder ComplexOrder symmDiff Classical

namespace D5.S3.Quantum.Fibers.BipartiteBlockade

open D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary
open private signedBoundary_range_eq_totalMassZero from
  D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary
open D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual
open private pureConfiguration pureConfiguration_density pureConfiguration_occupation
  pureConfiguration_blockade expectation_affine from
  D5.S3.Quantum.Fibers.BipartiteBlockade.BornFiveMode

variable {V : Type*} [Fintype V] [DecidableEq V]

private def singletonState (G : SimpleGraph V) (v : V) : Configuration G :=
  ⟨{v}, by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact G.irrefl⟩

private theorem singletonState_injective (G : SimpleGraph V) :
    Function.Injective (singletonState G) := by
  intro u v h
  have hh := congrArg Subtype.val h
  exact Finset.singleton_injective hh

private def coherentEdge (G : SimpleGraph V) (a b : V) (r : ℝ) :
    Matrix (Configuration G) (Configuration G) ℂ :=
  Matrix.single (singletonState G a) (singletonState G b) (r : ℂ) +
    Matrix.single (singletonState G b) (singletonState G a) (r : ℂ)

private theorem coherentEdge_hermitian (G : SimpleGraph V) (a b : V) (r : ℝ) :
    (coherentEdge G a b r).IsHermitian := by
  simp only [Matrix.IsHermitian, coherentEdge, Matrix.conjTranspose_add,
    Matrix.conjTranspose_single, Complex.star_def, map_ofNat]
  simp [add_comm]

private theorem coherentEdge_trace (G : SimpleGraph V) (a b : V) (hab : a ≠ b) (r : ℝ) :
    Matrix.trace (coherentEdge G a b r) = 0 := by
  have hne := (singletonState_injective G).ne hab
  simp [coherentEdge, Matrix.trace_add, hne, hne.symm]

private theorem coherentEdge_diagonal (G : SimpleGraph V) (a b : V)
    (hab : a ≠ b) (r : ℝ) (f : Configuration G → ℂ) :
    Matrix.trace (coherentEdge G a b r * Matrix.diagonal f) = 0 := by
  have hne := (singletonState_injective G).ne hab
  simp [coherentEdge, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul,
    Matrix.diagonal_apply, hne, hne.symm]

private theorem singleton_symmDiff_pair (a b : V) (hab : a ≠ b) :
    ({a} : Finset V) ∆ {a,b} = {b} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all

private theorem exchange_singletons (G : SimpleGraph V) (u v a b : V)
    (huv : u ≠ v) (hab : a ≠ b) :
    exchange G u v (singletonState G a) (singletonState G b) =
      if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then 1 else 0 := by
  have hequiv : ({a} : Finset V) ∆ {u,v} = {b} ↔
      (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
    constructor
    · intro h
      have hauv : a = u ∨ a = v := by
        by_contra hn
        push Not at hn
        have ha : a ∈ ({a} : Finset V) ∆ {u,v} := by
          simp [Finset.mem_symmDiff, hn.1, hn.2]
        rw [h] at ha
        exact hab (Finset.mem_singleton.mp ha)
      rcases hauv with hau | hav
      · subst a
        left
        refine ⟨rfl, ?_⟩
        rw [singleton_symmDiff_pair u v huv] at h
        exact (Finset.singleton_injective h).symm
      · subst a
        right
        refine ⟨rfl, ?_⟩
        have hp : ({u,v} : Finset V) = {v,u} := by ext x; simp [or_comm]
        rw [hp, singleton_symmDiff_pair v u huv.symm] at h
        exact (Finset.singleton_injective h).symm
    · rintro (⟨hau,hbv⟩ | ⟨hav,hbu⟩)
      · subst a; subst b
        exact singleton_symmDiff_pair u v huv
      · subst a; subst b
        have hp : ({u,v} : Finset V) = {v,u} := by ext x; simp [or_comm]
        rw [hp]
        exact singleton_symmDiff_pair v u huv.symm
  simp only [exchange, singletonState, hequiv]

private theorem coherentEdge_exchange (G : SimpleGraph V) (u v a b : V)
    (huv : u ≠ v) (hab : a ≠ b) (r : ℝ) :
    Matrix.trace (coherentEdge G a b r * exchange G u v) =
      (2 * r : ℂ) * if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then 1 else 0 := by
  rw [coherentEdge, Matrix.add_mul, Matrix.trace_add]
  simp only [Matrix.trace_single_mul, smul_eq_mul,
    exchange_singletons G u v a b huv hab,
    exchange_singletons G u v b a huv hab.symm]
  by_cases h : (a = u ∧ b = v) ∨ (a = v ∧ b = u)
  · have h' : (b = u ∧ a = v) ∨ (b = v ∧ a = u) := by tauto
    simp [h, h'] <;> ring
  · have h' : ¬((b = u ∧ a = v) ∨ (b = v ∧ a = u)) := by tauto
    simp [h, h']

private theorem coherentEdge_acceleration (G : SimpleGraph V) (Ω : V → ℝ)
    (a b : V) (hab : G.Adj a b) (r : ℝ) (v : V) :
    Matrix.trace (coherentEdge G a b r *
      ⁅hamiltonian G (fun x => (Ω x : ℂ)),
        ⁅hamiltonian G (fun x => (Ω x : ℂ)), number G v⁆⁆) =
      (2 * r * Ω a * Ω b : ℂ) *
        ((if v = a then 1 else 0) + (if v = b then 1 else 0)) := by
  have habne : a ≠ b := G.ne_of_adj hab
  rw [general_double_commutator, Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_smul, Matrix.trace_smul]
  simp only [number, blockade]
  rw [coherentEdge_diagonal G a b habne r, coherentEdge_diagonal G a b habne r]
  simp only [smul_zero, sub_zero, zero_add]
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [mul_ite, mul_zero, apply_ite Matrix.trace, Matrix.trace_zero]
  have heach : ∀ u : V,
      (if G.Adj u v then Matrix.trace
        (coherentEdge G a b r * (((Ω u : ℂ) * Ω v) • exchange G u v)) else 0) =
      if G.Adj u v then ((Ω u : ℂ) * Ω v) * (2 * r : ℂ) *
        (if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then 1 else 0) else 0 := by
    intro u
    by_cases huv : G.Adj u v
    · simp only [if_pos huv]
      rw [Matrix.mul_smul, Matrix.trace_smul,
        coherentEdge_exchange G u v a b (G.ne_of_adj huv) habne]
      simp only [smul_eq_mul, mul_assoc]
    · simp [huv]
  simp_rw [heach]
  by_cases hva : v = a
  · subst v
    rw [Finset.sum_eq_single b]
    · simp [habne, habne.symm, hab.symm] <;> ring
    · intro x _ hxb
      simp [habne.symm, Ne.symm hxb]
    · simp
  · by_cases hvb : v = b
    · subst v
      rw [Finset.sum_eq_single a]
      · simp [habne, habne.symm, hab] <;> ring
      · intro x _ hxa
        simp [habne, Ne.symm hxa]
      · simp
    · simp [hva, hvb, Ne.symm hva, Ne.symm hvb]

private def referenceOrientation (G : SimpleGraph V) : Orientation G :=
  fun e => ⟨e.val.out, Sym2.mk_fst_out_snd_out e.val⟩

private theorem oriented_adjacent (G : SimpleGraph V) (o : Orientation G) (e : ↥G.edgeSet) :
    G.Adj (o e).1.1 (o e).1.2 := by
  apply G.mem_edgeSet.mp
  rw [(o e).2]
  exact e.property

private theorem unsigned_flow_exists (G : SimpleGraph V) (connected : G.Connected)
    (color : V → Bool) (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (o : Orientation G) (s : V → ℝ)
    (balanced : ∑ v, (if color v then 1 else -1) * s v = 0) :
    ∃ t : ↥G.edgeSet → ℝ, ∀ v,
      (∑ e, t e * ((if v = (o e).1.1 then 1 else 0) +
        (if v = (o e).1.2 then 1 else 0))) = s v := by
  let χ : V → ℝ := fun v => if color v then 1 else -1
  let x : V → ℝ := fun v => χ v * s v
  have hx : x ∈ totalMassZero := balanced
  rw [← signedBoundary_range_eq_totalMassZero connected o] at hx
  obtain ⟨f, hf⟩ := hx
  refine ⟨fun e => f e * χ (o e).1.2, fun v => ?_⟩
  have hsq : χ v * χ v = 1 := by dsimp [χ]; split <;> norm_num
  have hedge : ∀ e : ↥G.edgeSet,
      χ v * edgeVector o e v = χ (o e).1.2 *
        ((if v = (o e).1.1 then 1 else 0) + (if v = (o e).1.2 then 1 else 0)) := by
    intro e
    have hproper := proper _ _ (oriented_adjacent G o e)
    have hne : (o e).1.1 ≠ (o e).1.2 := G.ne_of_adj (oriented_adjacent G o e)
    have hsign : χ (o e).1.1 = -χ (o e).1.2 := by
      dsimp [χ]
      cases ha : color (o e).1.1 <;> cases hb : color (o e).1.2 <;>
        simp_all
    by_cases ha : v = (o e).1.1
    · subst v
      simp [edgeVector,
        D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity.signedIncidence,
        hne, hne.symm, hsign]
    · by_cases hb : v = (o e).1.2
      · subst v
        simp [edgeVector,
          D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity.signedIncidence,
          hne, hne.symm]
      · simp [edgeVector,
          D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity.signedIncidence,
          ha, hb]
  have hv := congrFun hf v
  have hv' := congrArg (fun z : ℝ => χ v * z) hv
  change χ v * (∑ e, f e * edgeVector o e v) = χ v * (χ v * s v) at hv'
  rw [← mul_assoc, hsq, one_mul, Finset.mul_sum] at hv'
  rw [← hv']
  apply Finset.sum_congr rfl
  intro e _
  rw [mul_left_comm, hedge]
  ring

private theorem norm_shift_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℂ) (hermitian : R.IsHermitian) :
    (‖CStarMatrix.ofMatrix R‖ • (1 : Matrix n n ℂ) + R).PosSemidef := by
  let B := CStarMatrix.ofMatrix R
  have hself : IsSelfAdjoint B := congrArg CStarMatrix.ofMatrix hermitian
  have lower := IsSelfAdjoint.neg_algebraMap_norm_le_self (a := B) (ha := hself)
  have positive : 0 ≤ (algebraMap ℝ (CStarMatrix n n ℂ)) ‖B‖ + B := by
    exact neg_le_iff_add_nonneg'.mp lower
  have raw : CStarMatrix.ofMatrix.symm
      ((algebraMap ℝ (CStarMatrix n n ℂ)) ‖B‖ + B) =
      ‖CStarMatrix.ofMatrix R‖ • (1 : Matrix n n ℂ) + R := by
    ext i j
    simp [B, CStarMatrix.algebraMap_apply, Matrix.one_apply, Complex.real_smul]
  rw [← Matrix.nonneg_iff_posSemidef]
  have mapped := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm positive
  change 0 ≤ CStarMatrix.ofMatrix.symm
    ((algebraMap ℝ (CStarMatrix n n ℂ)) ‖B‖ + B) at mapped
  rwa [raw] at mapped

private theorem small_centered_density_perturbations
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (R : Matrix n n ℂ) (hermitian : R.IsHermitian)
    (traceless : Matrix.trace R = 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t| < η →
      (((Fintype.card n : ℝ)⁻¹) • (1 : Matrix n n ℂ) + t • R).PosDef ∧
      Matrix.trace (((Fintype.card n : ℝ)⁻¹) • (1 : Matrix n n ℂ) + t • R) = 1 := by
  let c : ℝ := (Fintype.card n : ℝ)⁻¹
  let B := CStarMatrix.ofMatrix R
  have hc : 0 < c := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hden : 0 < 2 * (‖B‖ + 1) := by positivity
  refine ⟨c / (2 * (‖B‖ + 1)), div_pos hc hden, fun t ht => ?_⟩
  have hb : ‖CStarMatrix.ofMatrix (t • R)‖ = |t| * ‖B‖ := by
    change ‖(t : ℂ) • B‖ = |t| * ‖B‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hbound : ‖CStarMatrix.ofMatrix (t • R)‖ < c := by
    rw [hb]
    have hprod := (lt_div_iff₀ hden).mp ht
    have hnonneg : 0 ≤ |t| := abs_nonneg t
    have hnorm : 0 ≤ ‖B‖ := norm_nonneg B
    nlinarith
  have hs := norm_shift_posSemidef (t • R) (hermitian.smul (by rfl : IsSelfAdjoint t))
  have hgap : 0 < c - ‖CStarMatrix.ofMatrix (t • R)‖ := sub_pos.mpr hbound
  have hp := (Matrix.PosDef.one.smul hgap).add_posSemidef hs
  have heq : (c - ‖CStarMatrix.ofMatrix (t • R)‖) • (1 : Matrix n n ℂ) +
      (‖CStarMatrix.ofMatrix (t • R)‖ • (1 : Matrix n n ℂ) + t • R) =
      c • (1 : Matrix n n ℂ) + t • R := by module
  refine ⟨?_, ?_⟩
  · rw [heq] at hp
    exact hp
  · simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, traceless,
      smul_zero, add_zero, smul_eq_mul]
    have hcard : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact inv_mul_cancel₀ hcard

private theorem physical_pair_of_direction {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (R : Matrix n n ℂ) (hermitian : R.IsHermitian)
    (traceless : Matrix.trace R = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ σ : Matrix n n ℂ,
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      σ.PosSemidef ∧ Matrix.trace σ = 1 ∧ ρ - σ = (2 * ε) • R := by
  obtain ⟨η, hη, hsmall⟩ := small_centered_density_perturbations R hermitian traceless
  let ε : ℝ := η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hlt : |ε| < η := by rw [abs_of_pos hε]; dsimp [ε]; linarith
  have hltNeg : |-ε| < η := by simpa only [abs_neg] using hlt
  have hplus := hsmall ε hlt
  have hminus := hsmall (-ε) hltNeg
  refine ⟨ε, hε,
    ((Fintype.card n : ℝ)⁻¹) • (1 : Matrix n n ℂ) + ε • R,
    ((Fintype.card n : ℝ)⁻¹) • (1 : Matrix n n ℂ) + (-ε) • R,
    hplus.1.posSemidef, hplus.2, hminus.1.posSemidef, hminus.2, ?_⟩
  module

private def diagonalDirection (G : SimpleGraph V) (δ : Configuration G → ℝ) :
    Matrix (Configuration G) (Configuration G) ℂ := Matrix.diagonal (fun S => (δ S : ℂ))

private theorem diagonal_number (G : SimpleGraph V) (δ : Configuration G → ℝ)
    (zeroMean : ∀ v, ∑ S, δ S * (if v ∈ S.val then 1 else 0) = 0) (v : V) :
    Matrix.trace (diagonalDirection G δ * number G v) = 0 := by
  unfold diagonalDirection number
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (zeroMean v)
  push_cast at h
  simpa only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h

private theorem diagonal_blockade (G : SimpleGraph V) (δ : Configuration G → ℝ) (v : V) :
    Matrix.trace (diagonalDirection G δ * blockade G v) = (blockMoment G δ v : ℂ) := by
  unfold diagonalDirection blockade blockMoment
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  push_cast
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero]

private theorem diagonal_exchange (G : SimpleGraph V) (δ : Configuration G → ℝ)
    (u v : V) :
    Matrix.trace (diagonalDirection G δ * exchange G u v) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro S _
  rw [Matrix.diag_apply, diagonalDirection, Matrix.diagonal_mul]
  have hne : S.val ∆ {u,v} ≠ S.val := by
    intro h
    have hh : S.val ∆ {u,v} = S.val ∆ (∅ : Finset V) := by simpa using h
    have hp : ({u,v} : Finset V) = ∅ := symmDiff_right_inj.mp hh
    have hu : u ∈ ({u,v} : Finset V) := by simp
    rw [hp] at hu
    exact Finset.notMem_empty u hu
  simp [exchange, hne]

private theorem diagonal_acceleration (G : SimpleGraph V) (Ω : V → ℝ)
    (δ : Configuration G → ℝ)
    (zeroMean : ∀ v, ∑ S, δ S * (if v ∈ S.val then 1 else 0) = 0) (v : V) :
    Matrix.trace (diagonalDirection G δ *
      ⁅hamiltonian G (fun x => (Ω x : ℂ)),
        ⁅hamiltonian G (fun x => (Ω x : ℂ)), number G v⁆⁆) =
      (-2 * (Ω v)^2 * blockMoment G δ v : ℂ) := by
  rw [general_double_commutator, Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_smul, Matrix.trace_smul, diagonal_number G δ zeroMean v,
    diagonal_blockade G δ v]
  have hexchange : Matrix.trace (diagonalDirection G δ *
      ∑ u, if G.Adj u v then ((Ω u : ℂ) * Ω v) • exchange G u v else 0) = 0 := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro u _
    split_ifs with hadj
    · rw [Matrix.mul_smul, Matrix.trace_smul,
        diagonal_exchange G δ u v]
      simp
    · simp
  rw [hexchange]
  simp only [smul_eq_mul, mul_zero, zero_sub, add_zero]
  push_cast
  ring

/-- A nonlinear neighborhood admits physical states with identical occupations
and different empty-neighborhood probabilities. -/
theorem physical_zero_setting_lower (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (v : V) (large : 2 ≤ (G.neighborFinset v).card) :
    ∃ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      (∀ x, occupationMean G ρ x = occupationMean G σ x) ∧
      blockadeMean G ρ v ≠ blockadeMean G σ v := by
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp large
  have hvu : G.Adj v u := by simpa using hu
  have hvw : G.Adj v w := by simpa using hw
  have hind : ¬ G.Adj u w := by
    intro hadj
    have hl := proper v u hvu
    have hr := proper v w hvw
    have he := proper u w hadj
    cases hc : color v <;> cases hu : color u <;> cases hw : color w <;> simp_all
  let empty : Configuration G := ⟨∅, by simp⟩
  let left : Configuration G := ⟨{u}, by simp [G.irrefl]⟩
  let right : Configuration G := ⟨{w}, by simp [G.irrefl]⟩
  let both : Configuration G := ⟨{u,w}, by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact G.irrefl
    · exact hind
    · exact fun h => hind h.symm
    · exact G.irrefl⟩
  let ρ := (1 / 2 : ℝ) • (pureConfiguration G empty + pureConfiguration G both)
  let σ := (1 / 2 : ℝ) • (pureConfiguration G left + pureConfiguration G right)
  have hd (S T : Configuration G) :
      ((1 / 2 : ℝ) • (pureConfiguration G S + pureConfiguration G T)).PosSemidef ∧
      Matrix.trace ((1 / 2 : ℝ) • (pureConfiguration G S + pureConfiguration G T)) = 1 := by
    refine ⟨((pureConfiguration_density G S).1.add
      (pureConfiguration_density G T).1).smul (by norm_num), ?_⟩
    simp [Matrix.trace_smul, Matrix.trace_add, (pureConfiguration_density G S).2,
      (pureConfiguration_density G T).2]
    norm_num
  refine ⟨ρ, σ, (hd empty both).1, (hd empty both).2,
    (hd left right).1, (hd left right).2, ?_, ?_⟩
  · intro x
    rw [(expectation_affine G _ _ x).1, (expectation_affine G _ _ x).1]
    simp only [pureConfiguration_occupation]
    by_cases hx : x = u <;> by_cases hw : x = w
    · exact (huw (hx.symm.trans hw)).elim
    · simp [empty, left, right, both, hx, hw, huw]
    · simp [empty, left, right, both, hx, hw, huw.symm]
    · simp [empty, left, right, both, hx, hw]
  · have he : clear G v empty := by simp [clear, empty]
    have hl : ¬ clear G v left := by
      intro h
      exact h u (by simp [left]) hvu
    have hr : ¬ clear G v right := by
      intro h
      exact h w (by simp [right]) hvw
    have hb : ¬ clear G v both := by
      intro h
      exact h u (by simp [both]) hvu
    change blockadeMean G ((1 / 2 : ℝ) • _) v ≠
      blockadeMean G ((1 / 2 : ℝ) • _) v
    rw [(expectation_affine G _ _ v).2, (expectation_affine G _ _ v).2]
    simp [pureConfiguration_blockade, he, hl, hr, hb]

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.physical_zero_setting_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physical_zero_setting_lower

private theorem coherent_lift_of_balanced_diagonal
    (G : SimpleGraph V) (connected : G.Connected) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0) (δ : Configuration G → ℝ)
    (zeroTrace : (∑ S, δ S) = 0)
    (zeroMean : ∀ v, ∑ S, δ S * (if v ∈ S.val then 1 else 0) = 0)
    (balanced : (∑ v, (if color v then 1 else -1) * (Ω v)^2 *
      blockMoment G δ v) = 0) :
    ∃ R : Matrix (Configuration G) (Configuration G) ℂ,
      R.IsHermitian ∧ Matrix.trace R = 0 ∧
      (∀ v, Matrix.trace (R * number G v) = 0) ∧
      (∀ v, Matrix.trace (R *
        ⁅hamiltonian G (fun x => (Ω x : ℂ)),
          ⁅hamiltonian G (fun x => (Ω x : ℂ)), number G v⁆⁆) = 0) ∧
      (∀ v, Matrix.trace (R * blockade G v) = (blockMoment G δ v : ℂ)) := by
  let o := referenceOrientation G
  obtain ⟨t, ht⟩ := unsigned_flow_exists G connected color proper o
    (fun v => (Ω v)^2 * blockMoment G δ v) (by simpa only [mul_assoc] using balanced)
  let C : ↥G.edgeSet → Matrix (Configuration G) (Configuration G) ℂ := fun e =>
    coherentEdge G (o e).1.1 (o e).1.2
      (t e / (Ω (o e).1.1 * Ω (o e).1.2))
  let R := diagonalDirection G δ + ∑ e, C e
  have hne (e : ↥G.edgeSet) : (o e).1.1 ≠ (o e).1.2 :=
    G.ne_of_adj (oriented_adjacent G o e)
  have hR : R.IsHermitian := by
    apply Matrix.IsHermitian.add
    · apply Matrix.isHermitian_diagonal_of_self_adjoint
      ext S
      simp
    · change (∑ e, C e)ᴴ = ∑ e, C e
      rw [Matrix.conjTranspose_sum]
      apply Finset.sum_congr rfl
      intro e _
      exact (coherentEdge_hermitian G _ _ _).eq
  have htrace : Matrix.trace R = 0 := by
    have hd : (∑ S, (δ S : ℂ)) = 0 := by exact_mod_cast zeroTrace
    have hc (e : ↥G.edgeSet) : Matrix.trace (C e) = 0 :=
      coherentEdge_trace G _ _ (hne e) _
    simp [R, Matrix.trace_add, Matrix.trace_sum, diagonalDirection, hd, hc]
  have R_diagonal (f : Configuration G → ℂ) :
      Matrix.trace (R * Matrix.diagonal f) =
        Matrix.trace (diagonalDirection G δ * Matrix.diagonal f) := by
    dsimp only [R]
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.sum_mul, Matrix.trace_sum]
    have hc (e : ↥G.edgeSet) : Matrix.trace (C e * Matrix.diagonal f) = 0 :=
      coherentEdge_diagonal G _ _ (hne e) _ f
    simp [hc]
  have R_number (v : V) : Matrix.trace (R * number G v) = 0 := by
    rw [number, R_diagonal]
    exact diagonal_number G δ zeroMean v
  have R_blockade (v : V) :
      Matrix.trace (R * blockade G v) = (blockMoment G δ v : ℂ) := by
    rw [blockade, R_diagonal]
    exact diagonal_blockade G δ v
  have R_acceleration (v : V) :
      Matrix.trace (R *
        ⁅hamiltonian G (fun x => (Ω x : ℂ)),
          ⁅hamiltonian G (fun x => (Ω x : ℂ)), number G v⁆⁆) = 0 := by
    dsimp only [R]
    rw [Matrix.add_mul, Matrix.trace_add,
      diagonal_acceleration G Ω δ zeroMean v, Matrix.sum_mul, Matrix.trace_sum]
    have hc (e : ↥G.edgeSet) :
        Matrix.trace (C e *
          ⁅hamiltonian G (fun x => (Ω x : ℂ)),
            ⁅hamiltonian G (fun x => (Ω x : ℂ)), number G v⁆⁆) =
          (2 : ℂ) * ((t e : ℂ) *
            ((if v = (o e).1.1 then 1 else 0) +
              (if v = (o e).1.2 then 1 else 0))) := by
      rw [coherentEdge_acceleration G Ω _ _ (oriented_adjacent G o e)]
      push_cast
      field_simp [nonzero (o e).1.1, nonzero (o e).1.2]
    simp_rw [hc]
    rw [← Finset.mul_sum]
    have htC := congrArg (fun z : ℝ => (z : ℂ)) (ht v)
    push_cast at htC
    have castIf (p : Prop) [Decidable p] :
        Complex.ofReal (if p then (1 : ℝ) else 0) = if p then 1 else 0 := by
      by_cases hp : p <;> simp [hp]
    simp only [castIf] at htC
    rw [htC]
    push_cast
    ring
  exact ⟨R, hR, htrace, R_number, R_acceleration, R_blockade⟩

/-- Every positive drive on a connected bipartite graph with two distinct
nonlinear neighborhoods has two physical states with identical one-setting
data and different blockade readouts. -/
theorem physical_single_setting_lower
    (G : SimpleGraph V) (connected : G.Connected) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0) (u w : V)
    (largeU : 2 ≤ (G.neighborFinset u).card)
    (largeW : 2 ≤ (G.neighborFinset w).card)
    (distinct : G.neighborFinset u ≠ G.neighborFinset w) :
    ∃ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      (∀ v, Matrix.trace (ρ * number G v) = Matrix.trace (σ * number G v)) ∧
      (∀ v, Matrix.trace (ρ *
          ⁅hamiltonian G (fun x => (Ω x : ℂ)),
            ⁅hamiltonian G (fun x => (Ω x : ℂ)), number G v⁆⁆) =
        Matrix.trace (σ *
          ⁅hamiltonian G (fun x => (Ω x : ℂ)),
            ⁅hamiltonian G (fun x => (Ω x : ℂ)), number G v⁆⁆)) ∧
      ∃ v, (Matrix.trace (ρ * blockade G v)).re ≠
        (Matrix.trace (σ * blockade G v)).re := by
  obtain ⟨δ, zeroTrace, zeroMean, balanced, bNonzero⟩ :=
    diagonal_residual_of_distinct_neighborhoods G color proper Ω nonzero u w
      largeU largeW distinct
  obtain ⟨R, hR, htrace, R_number, R_acceleration, R_blockade⟩ :=
    coherent_lift_of_balanced_diagonal G connected color proper Ω nonzero δ
      zeroTrace zeroMean balanced
  letI : Nonempty (Configuration G) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨ε, hε, ρ, σ, hρ, trρ, hσ, trσ, hdifference⟩ :=
    physical_pair_of_direction R hR htrace
  have difference (E : Matrix (Configuration G) (Configuration G) ℂ) :
      Matrix.trace (ρ * E) - Matrix.trace (σ * E) =
        ((2 * ε : ℝ) : ℂ) * Matrix.trace (R * E) := by
    have hh := congrArg (fun M => Matrix.trace (M * E)) hdifference
    simpa [Matrix.sub_mul, Matrix.trace_sub, smul_mul_assoc,
      Matrix.trace_smul, smul_eq_mul] using hh
  refine ⟨ρ, σ, hρ, trρ, hσ, trσ, ?_, ?_, ?_⟩
  · intro v
    apply sub_eq_zero.mp
    rw [difference, R_number]
    simp
  · intro v
    apply sub_eq_zero.mp
    rw [difference, R_acceleration]
    simp
  · obtain ⟨v, hv⟩ := bNonzero
    refine ⟨v, ?_⟩
    intro heq
    have hh := congrArg Complex.re (difference (blockade G v))
    rw [R_blockade] at hh
    have hz : (2 * ε) * blockMoment G δ v = 0 := by
      have hreal :
          ((((2 * ε : ℝ) : ℂ) * (blockMoment G δ v : ℂ))).re =
            (2 * ε) * blockMoment G δ v := by simp
      rw [Complex.sub_re, heq, sub_self, hreal] at hh
      exact hh.symm
    exact mul_ne_zero (by positivity) hv hz

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.physical_single_setting_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physical_single_setting_lower

end D5.S3.Quantum.Fibers.BipartiteBlockade
