/- GID: D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pure-target quantum Cerny complexity of constant words grows linearly. -/

import D5.S3.Quantum.QuantumChannels.QuantumCernyThueMorseRefutation
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace D5.S3.Quantum.QuantumChannels.QuantumCernyPureTargetRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (IsPure pureState)
open D5.S3.Quantum.QuantumChannels.QuantumCernyThueMorseRefutation
  (applyWord reachable Synchronizing UniqueShortestSync)
open Matrix Module
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder

/-- An instance with a unique shortest word and pure common output. -/
def HasPureInstance (d : ℕ) (w : List (Fin 2)) : Prop :=
  ∃ (A : Fin 2 → QuantumChannel (Fin d) (Fin d)) (ρ₀ P : DensityState (Fin d)),
    UniqueShortestSync A ρ₀ w ∧ IsPure P ∧
      ∀ ρ ∈ reachable A ρ₀, applyWord A w ρ = P

/-- The least dimension of a pure-output instance. -/
def qcPure (w : List (Fin 2)) : ℕ := sInf {d | HasPureInstance d w}

/-- The general square-root saving asked for in item 5. -/
def claim : Prop := ∃ C : ℝ, ∃ m₀ : ℕ, ∀ w : List (Fin 2),
  m₀ ≤ w.length → (qcPure w : ℝ) ≤ C * Real.sqrt w.length

private def basisState {d : ℕ} (j : Fin d) : DensityState (Fin d) :=
  pureState (Pi.single j 1) (by simp [dotProduct, Pi.single_apply])

private theorem basisState_value {d : ℕ} (j : Fin d) :
    (basisState j).1 = CStarMatrix.ofMatrix (Matrix.single j j 1) := by
  apply CStarMatrix.ext
  intro i k
  by_cases hi : j = i <;> by_cases hk : j = k <;>
    simp [basisState, pureState, Matrix.vecMulVec, Matrix.single, Pi.single_apply, hi, hk, eq_comm]

private theorem basisState_injective {d : ℕ} : Function.Injective (@basisState d) := by
  intro i j h
  have hh := congrArg (fun ρ : DensityState (Fin d) => ρ.1 i i) h
  simp only [basisState_value, CStarMatrix.ofMatrix_apply, Matrix.single_apply] at hh
  by_contra hn
  simp [Ne.symm hn] at hh

private def down {m : ℕ} (j : Fin (m + 1)) : Fin (m + 1) :=
  ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩

/-- The reset-and-shift channel sends each basis density to its predecessor. -/
private theorem shift_channel (m : ℕ) :
    ∃ Φ : QuantumChannel (Fin (m+1)) (Fin (m+1)),
      ∀ j, Φ.mapState (basisState j) = basisState (down j) := by
  let K : Fin (m+1) → Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
    fun j => Matrix.single (down j) j 1
  have hK : (∑ j, (K j).conjTranspose * K j) = 1 := by
    simp only [K, Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same,
      one_mul]
    exact Matrix.sum_single_one
  obtain ⟨Φ, hΦ⟩ := finite_kraus_quantum_channel K hK
  refine ⟨Φ, fun j => Subtype.ext ?_⟩
  rw [QuantumChannel.mapState_value, basisState_value, basisState_value]
  have h := hΦ (Matrix.single j j 1)
  apply CStarMatrix.ofMatrix.symm.injective
  rw [h]
  simp only [K, Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single,
    one_mul, mul_one]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

private theorem identity_channel (d : ℕ) :
    ∃ Φ : QuantumChannel (Fin d) (Fin d), ∀ ρ, Φ.mapState ρ = ρ := by
  obtain ⟨Φ, hΦ⟩ := finite_kraus_quantum_channel
    (fun _ : Unit => (1 : Matrix (Fin d) (Fin d) ℂ)) (by simp)
  refine ⟨Φ, fun ρ => Subtype.ext ?_⟩
  apply CStarMatrix.ofMatrix.symm.injective
  simpa using hΦ (CStarMatrix.ofMatrix.symm ρ.1)

/-- Every constant word has a pure-target realization in dimension one more than its length. -/
theorem constant_word_realization (m : ℕ) : HasPureInstance (m+1) (List.replicate m 0) := by
  obtain ⟨Φ, hΦ⟩ := shift_channel m
  obtain ⟨I, hI⟩ := identity_channel (m+1)
  let A : Fin 2 → QuantumChannel (Fin (m+1)) (Fin (m+1)) :=
    fun a => if a = 0 then Φ else I
  have hstep (a : Fin 2) (j : Fin (m+1)) :
      (A a).mapState (basisState j) =
        basisState ⟨j.val - (if a = 0 then 1 else 0),
          (Nat.sub_le _ _).trans_lt j.isLt⟩ := by
    by_cases ha : a = 0
    · simpa [A, ha, down] using hΦ j
    · simpa [A, ha] using hI (basisState j)
  have hword (u : List (Fin 2)) (j : Fin (m+1)) :
      applyWord A u (basisState j) =
        basisState ⟨j.val - u.count 0, (Nat.sub_le _ _).trans_lt j.isLt⟩ := by
    induction u generalizing j with
    | nil => simp [applyWord]
    | cons a u ih =>
      rw [applyWord, hstep, ih]
      congr 1
      apply Fin.ext
      by_cases ha : a = 0 <;> simp [ha, Nat.sub_sub, Nat.add_comm]
  let top : Fin (m+1) := ⟨m, by omega⟩
  let bottom : Fin (m+1) := ⟨0, by omega⟩
  have hreach (j : Fin (m+1)) : basisState j ∈ reachable A (basisState top) := by
    refine ⟨List.replicate (m-j.val) 0, ?_⟩
    change applyWord A (List.replicate (m-j.val) 0) (basisState top) = basisState j
    rw [hword]
    congr 1
    apply Fin.ext
    simp only [List.count_replicate, beq_self_eq_true, ↓reduceIte]
    dsimp [top]
    omega
  have hsync (u : List (Fin 2)) :
      Synchronizing A (basisState top) u ↔ m ≤ u.count 0 := by
    constructor
    · rintro ⟨P, hP⟩
      have heq := (hP _ (hreach top)).trans (hP _ (hreach bottom)).symm
      rw [hword, hword] at heq
      have hv := congrArg Fin.val (basisState_injective heq)
      dsimp [top, bottom] at hv
      omega
    · intro hu
      refine ⟨basisState bottom, ?_⟩
      rintro ρ ⟨v, rfl⟩
      change applyWord A u (applyWord A v (basisState top)) = basisState bottom
      rw [hword, hword]
      congr 1
      apply Fin.ext
      dsimp [bottom, top]
      omega
  refine ⟨A, basisState top, basisState bottom, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (hsync _).mpr (by simp)
  · intro u hu hne h
    have hz := (hsync u).mp h
    have heq : u = List.replicate u.length 0 := by
      apply List.eq_replicate_of_mem
      intro a ha
      by_contra han
      have hc := List.count_lt_length_iff.mpr ⟨a, ha, han⟩
      simp only [List.length_replicate] at hu
      omega
    apply hne
    rw [heq]
    congr 1
    have hc := List.count_le_length (a := (0 : Fin 2)) (l := u)
    simp only [List.length_replicate] at hu
    omega
  · exact ⟨Pi.single bottom 1, rfl⟩
  · rintro ρ ⟨v, rfl⟩
    change applyWord A (List.replicate m 0) (applyWord A v (basisState top)) = basisState bottom
    rw [hword, hword]
    congr 1
    apply Fin.ext
    simp [bottom, top]

private abbrev Mat (d : ℕ) := CStarMatrix (Fin d) (Fin d) ℂ

private def outer {d : ℕ} (v : Fin d → ℂ) : Mat d :=
  CStarMatrix.ofMatrix (vecMulVec (star v) v)

private def rowMap {d : ℕ} (i₀ : Fin d) : (Fin d → ℂ) →ₗ[ℂ] Mat d where
  toFun v := CStarMatrix.ofMatrix (fun i j => if i = i₀ then v j else 0)
  map_add' v w := by
    ext i j
    change (if i = i₀ then v j + w j else 0) =
      (if i = i₀ then v j else 0) + (if i = i₀ then w j else 0)
    by_cases h : i = i₀ <;> simp [h]
  map_smul' c v := by
    ext i j
    change (if i = i₀ then c * v j else 0) =
      c * (if i = i₀ then v j else 0)
    by_cases h : i = i₀ <;> simp [h]

private theorem rowMap_square {d : ℕ} (i₀ : Fin d) (v : Fin d → ℂ) :
    star (rowMap i₀ v) * rowMap i₀ v = outer v := by
  apply CStarMatrix.ext
  intro i j
  change (∑ k : Fin d, star (if k = i₀ then v i else 0) *
    (if k = i₀ then v j else 0)) = star (v i) * v j
  simp

private def functionalKernel {d : ℕ} (i₀ : Fin d) (f : Mat d →ₚ[ℂ] ℂ) :
    Submodule ℂ (Fin d → ℂ) where
  carrier := {v | ‖f.toPreGNS (rowMap i₀ v)‖ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change ‖f.toPreGNS (rowMap i₀ (v + w))‖ = 0
    rw [map_add, map_add]
    apply le_antisymm _ (norm_nonneg _)
    exact (norm_add_le _ _).trans (by rw [hv, hw, add_zero])
  smul_mem' := by
    intro c v hv
    change ‖f.toPreGNS (rowMap i₀ (c • v))‖ = 0
    rw [map_smul, map_smul, norm_smul, hv, mul_zero]

private theorem mem_functionalKernel {d : ℕ} (i₀ : Fin d)
    (f : Mat d →ₚ[ℂ] ℂ) (v : Fin d → ℂ) :
    v ∈ functionalKernel i₀ f ↔ f (outer v) = 0 := by
  change ‖f.toPreGNS (rowMap i₀ v)‖ = 0 ↔ _
  have hs := f.preGNS_norm_sq (f.toPreGNS (rowMap i₀ v))
  rw [PositiveLinearMap.ofPreGNS_toPreGNS, rowMap_square] at hs
  constructor
  · intro h
    simpa [h] using hs.symm
  · intro h
    have : (‖f.toPreGNS (rowMap i₀ v)‖ : ℂ) ^ 2 = 0 := by
      simpa [h] using hs
    exact_mod_cast (sq_eq_zero_iff.mp this)

private theorem outer_nonneg {d : ℕ} (v : Fin d → ℂ) : 0 ≤ outer v :=
  map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    (Matrix.posSemidef_vecMulVec_star_self v).nonneg

private theorem functional_zero_decomposition {d n : ℕ} (i₀ : Fin d)
    (f : Mat d →ₚ[ℂ] ℂ) (v : Fin n → Fin d → ℂ) :
    f (∑ i, outer (v i)) = 0 ↔ ∀ i, v i ∈ functionalKernel i₀ f := by
  rw [map_sum]
  simp only [mem_functionalKernel]
  simpa using (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ) (fun i _ => map_nonneg f (outer_nonneg (v i))))

private theorem functional_zero_transfer {d : ℕ} (i₀ : Fin d)
    (f g : Mat d →ₚ[ℂ] ℂ) (h : functionalKernel i₀ f = functionalKernel i₀ g)
    (X : Mat d) (hX : 0 ≤ X) : f X = 0 ↔ g X = 0 := by
  have hXM : (CStarMatrix.ofMatrix.symm X).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hX)
  obtain ⟨n, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hXM
  have hdecomp : X = ∑ i, outer (star (v i)) := by
    have ht := congrArg CStarMatrix.ofMatrixStarAlgEquiv hv
    rw [map_sum] at ht
    change X = ∑ i, CStarMatrix.ofMatrix (vecMulVec (v i) (star (v i))) at ht
    simpa only [outer, star_star] using ht
  rw [hdecomp, functional_zero_decomposition i₀, functional_zero_decomposition i₀, h]

private def positiveIterate {d : ℕ} (L : Mat d →ₚ[ℂ] Mat d) : ℕ → Mat d →ₚ[ℂ] Mat d
  | 0 => PositiveLinearMap.id ℂ (Mat d)
  | n + 1 => (positiveIterate L n).comp L

private theorem positiveIterate_succ {d : ℕ} (L : Mat d →ₚ[ℂ] Mat d)
    (n : ℕ) (X : Mat d) : positiveIterate L (n + 1) X = L (positiveIterate L n X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih (L X)

private theorem positive_absorption_dimension {d : ℕ} (i₀ : Fin d)
    (L : Mat d →ₚ[ℂ] Mat d) (P : Mat d) (f : Mat d →ₚ[ℂ] ℂ)
    (hfix : L P = P) (hfp : f P = 0)
    (hdetect : ∀ X : Mat d, 0 ≤ X → f X = 0 → X = Matrix.trace X • P)
    (v : Fin d → ℂ) (hv : v ≠ 0) (hvp : outer v = P)
    (m : ℕ) (hm : 0 < m) (X : Mat d) (hX : 0 ≤ X)
    (hmX : f (positiveIterate L m X) = 0)
    (hprev : f (positiveIterate L (m - 1) X) ≠ 0) : m + 1 ≤ d := by
  let F : ℕ → Mat d →ₚ[ℂ] ℂ := fun j => f.comp (positiveIterate L j)
  let H : ℕ → Submodule ℂ (Fin d → ℂ) := fun j => functionalKernel i₀ (F j)
  have hF (j : ℕ) (Y : Mat d) : F (j + 1) Y = F j (L Y) := rfl
  have hmono (j : ℕ) : H j ≤ H (j + 1) := by
    intro u hu
    rw [mem_functionalKernel] at hu ⊢
    change f (positiveIterate L (j + 1) (outer u)) = 0
    have hpos := map_nonneg (positiveIterate L j) (outer_nonneg u)
    have hscalar := hdetect _ hpos hu
    rw [positiveIterate_succ, hscalar, map_smul, hfix, map_smul, hfp, smul_zero]
  have hstable (j : ℕ) (hj : H j = H (j + 1)) : H (j + 1) = H (j + 2) := by
    apply Submodule.ext
    intro u
    simp only [H, mem_functionalKernel]
    rw [hF, show j + 2 = (j + 1) + 1 by omega, hF]
    exact functional_zero_transfer i₀ (F j) (F (j + 1)) hj
      (L (outer u)) (map_nonneg L (outer_nonneg u))
  have hlast : H (m - 1) ≠ H m := by
    intro heq
    have hzero := functional_zero_transfer i₀ (F (m - 1)) (F m) heq X hX
    exact hprev (hzero.mpr hmX)
  have hall (j : ℕ) (hj : j < m) : H j ≠ H (j + 1) := by
    intro heq
    have hpersist : ∀ k, H (j + k) = H (j + k + 1) := by
      intro k
      induction k with
      | zero => simpa using heq
      | succ k ih => simpa [Nat.add_assoc] using hstable (j + k) ih
    have := hpersist (m - 1 - j)
    have hindex : j + (m - 1 - j) = m - 1 := by omega
    rw [hindex, show m - 1 + 1 = m by omega] at this
    exact hlast this
  have hpos₀ : 1 ≤ finrank ℂ (H 0) := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    have hbot : H 0 = ⊥ := Submodule.finrank_eq_zero.mp hz
    have hvH : v ∈ H 0 := by
      rw [mem_functionalKernel]
      change f (outer v) = 0
      rw [hvp, hfp]
    rw [hbot, Submodule.mem_bot] at hvH
    exact hv hvH
  have hgrowth : ∀ j, j ≤ m → j + 1 ≤ finrank ℂ (H j) := by
    intro j
    induction j with
    | zero => intro _; exact hpos₀
    | succ j ih =>
      intro hj
      have hrank := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (hmono j) (hall j (by omega)))
      have := ih (by omega)
      omega
  have hbound := Submodule.finrank_le (H m)
  have hambient : finrank ℂ (Fin d → ℂ) = d := by simp
  rw [hambient] at hbound
  exact (hgrowth m le_rfl).trans hbound

private theorem pure_density_detector {d : ℕ} (P : DensityState (Fin d)) (hp : IsPure P) :
    Matrix.trace ((1-P.1)*P.1*star (1-P.1)) = 0 ∧
      ∀ (X : CStarMatrix (Fin d) (Fin d) ℂ), 0 ≤ X →
        Matrix.trace ((1-P.1)*X*star (1-P.1)) = 0 → X = Matrix.trace X • P.1 := by
  obtain ⟨ψ, hψ⟩ := hp
  let p : Matrix (Fin d) (Fin d) ℂ := Matrix.vecMulVec ψ (star ψ)
  have ht : Matrix.trace p = 1 := by
    have h := P.2.2
    rw [hψ] at h
    exact h
  have hunit : star ψ ⬝ᵥ ψ = 1 := by
    simpa only [p, Matrix.trace_vecMulVec, dotProduct_comm] using ht
  have hps : p.conjTranspose = p := by simp [p]
  have hpp : p*p = p := by
    simp [p, Matrix.vecMulVec_mul_vecMulVec, hunit]
  let q : Matrix (Fin d) (Fin d) ℂ := 1-p
  have hqs : q.conjTranspose = q := by simp [q, hps]
  constructor
  · rw [hψ]
    change Matrix.trace (q*p*q.conjTranspose) = 0
    simp [q, Matrix.sub_mul, hpp]
  · intro X hX hz
    let x : Matrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix.symm X
    have hx : 0 ≤ x := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hX
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
    have hBx : x = B.conjTranspose * B := hB
    have hz' : Matrix.trace (q*x*q.conjTranspose) = 0 := by
      rw [hψ] at hz
      exact hz
    have hBQ : B*q = 0 := by
      apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
      simpa only [Matrix.conjTranspose_mul, hqs, Matrix.mul_assoc, hBx] using hz'
    have hxq : x*q = 0 := by rw [hBx, Matrix.mul_assoc, hBQ, mul_zero]
    have hxs : x.conjTranspose = x := (Matrix.nonneg_iff_posSemidef.mp hx).isHermitian.eq
    have hqx : q*x = 0 := by
      have hh := congrArg Matrix.conjTranspose hxq
      simpa only [Matrix.conjTranspose_mul, hqs, hxs, Matrix.conjTranspose_zero] using hh
    have hxp : x*p = x := by
      have : x-x*p = 0 := by simpa only [q, Matrix.mul_sub, mul_one] using hxq
      exact (sub_eq_zero.mp this).symm
    have hpx : p*x = x := by
      have : x-p*x = 0 := by simpa only [q, Matrix.sub_mul, one_mul] using hqx
      exact (sub_eq_zero.mp this).symm
    let c := ((star ψ) ᵥ* x) ⬝ᵥ ψ
    have hscalar : x = c • p := by
      calc x = p*x*p := by rw [hpx, hxp]
        _ = c • p := by
          dsimp only [p]
          rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
    have hc : Matrix.trace x = c := by rw [hscalar, Matrix.trace_smul, ht, smul_eq_mul, mul_one]
    rw [hψ]
    change x = Matrix.trace x • p
    rw [hc]
    exact hscalar

private theorem pure_constant_word_dimension_of_detector (d m : ℕ)
    (A : Fin 2 → QuantumChannel (Fin d) (Fin d))
    (ρ₀ P : DensityState (Fin d))
    (hunique : UniqueShortestSync A ρ₀ (List.replicate m 0)) (hpure : IsPure P)
    (hout : ∀ ρ ∈ reachable A ρ₀, applyWord A (List.replicate m 0) ρ = P)
    (hdet : Matrix.trace ((1 - P.1) * P.1 * star (1 - P.1)) = 0 ∧
      ∀ X : Mat d, 0 ≤ X →
        Matrix.trace ((1 - P.1) * X * star (1 - P.1)) = 0 →
        X = Matrix.trace X • P.1) : m + 1 ≤ d := by
  obtain ⟨ψ, hψ⟩ := hpure
  have hψunit : star ψ ⬝ᵥ ψ = 1 := by
    have := P.2.2
    rw [hψ] at this
    change trace (vecMulVec ψ (star ψ)) = 1 at this
    simpa only [trace_vecMulVec, dotProduct_comm] using this
  have hψne : ψ ≠ 0 := by
    intro hz
    simp [hz] at hψunit
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin d, ψ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hψne (funext h)
  by_cases hm : m = 0
  · subst m
    exact Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt i₀.isLt)
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let L : Mat d →ₚ[ℂ] Mat d := PositiveLinearMap.ofClass (A 0).toCompletelyPositiveMap
  have hval (j : ℕ) (ρ : DensityState (Fin d)) :
      positiveIterate L j ρ.1 = (applyWord A (List.replicate j 0) ρ).1 := by
    induction j generalizing ρ with
    | zero => rfl
    | succ j ih => exact ih ((A 0).mapState ρ)
  have hreach₀ : ρ₀ ∈ reachable A ρ₀ := ⟨[], rfl⟩
  have hreach₁ : (A 0).mapState ρ₀ ∈ reachable A ρ₀ := ⟨[0], rfl⟩
  have hfix : L P.1 = P.1 := by
    have hP := congrArg Subtype.val (hout ρ₀ hreach₀)
    have hLP := congrArg Subtype.val (hout ((A 0).mapState ρ₀) hreach₁)
    rw [← hval m ρ₀] at hP
    rw [← hval m ((A 0).mapState ρ₀)] at hLP
    calc L P.1 = L (positiveIterate L m ρ₀.1) := congrArg L hP.symm
      _ = positiveIterate L (m + 1) ρ₀.1 := (positiveIterate_succ L m _).symm
      _ = P.1 := hLP
  let fL : Mat d →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin d) ℂ ℂ).comp
      (CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.toLinearMap.comp
        ((LinearMap.mulRight ℂ (star (1 - P.1))).comp
          (LinearMap.mulLeft ℂ (1 - P.1))))
  let f : Mat d →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ fL (by
    intro X hX
    exact (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
        (star_right_conjugate_nonneg hX (1 - P.1)))).trace_nonneg)
  have hshort : ¬ Synchronizing A ρ₀ (List.replicate (m - 1) 0) := by
    have hlen : (List.replicate (m-1) (0 : Fin 2)).length ≤
        (List.replicate m (0 : Fin 2)).length := by simp
    have hne : List.replicate (m-1) (0 : Fin 2) ≠ List.replicate m 0 := by
      intro heq
      have := congrArg List.length heq
      simp only [List.length_replicate] at this
      omega
    exact hunique.2 _ hlen hne
  obtain ⟨ρ, hρ, hprev⟩ : ∃ ρ ∈ reachable A ρ₀,
      f (positiveIterate L (m - 1) ρ.1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hshort
    refine ⟨P, ?_⟩
    intro ρ hρ
    apply Subtype.ext
    have hpos := map_nonneg (positiveIterate L (m - 1)) ρ.2.1
    have heq := hdet.2 _ hpos (h ρ hρ)
    rw [hval] at heq
    simpa using heq
  apply positive_absorption_dimension i₀ L P.1 f hfix (hdet.1)
    (hdet.2) (star ψ) (star_ne_zero.mpr hψne) (by simpa [outer] using hψ.symm)
    m hmpos ρ.1 ρ.2.1 _ hprev
  rw [hval, hout ρ hρ]
  exact hdet.1

/-- A unary unique shortest synchronizing word with pure output requires one more
state-space dimension than its length. -/
theorem pure_constant_word_dimension (d m : ℕ)
    (A : Fin 2 → QuantumChannel (Fin d) (Fin d))
    (ρ₀ P : DensityState (Fin d))
    (hunique : UniqueShortestSync A ρ₀ (List.replicate m 0)) (hpure : IsPure P)
    (hout : ∀ ρ ∈ reachable A ρ₀, applyWord A (List.replicate m 0) ρ = P) :
    m + 1 ≤ d :=
  pure_constant_word_dimension_of_detector d m A ρ₀ P hunique hpure hout
    (pure_density_detector P hpure)

/-- The pure-target complexity of the constant word of length m is exactly m+1. -/
theorem constant_word_complexity (m : ℕ) : qcPure (List.replicate m 0) = m+1 := by
  have hin : HasPureInstance (qcPure (List.replicate m 0)) (List.replicate m 0) :=
    Nat.sInf_mem (s := {d | HasPureInstance d (List.replicate m 0)})
      ⟨m+1, constant_word_realization m⟩
  apply le_antisymm
  · exact csInf_le' (constant_word_realization m)
  · obtain ⟨A, ρ₀, P, hunique, hpure, hout⟩ := hin
    exact pure_constant_word_dimension _ m A ρ₀ P hunique hpure hout

/-- No uniform square-root saving holds for pure-target quantum Cerny complexity. -/
theorem result : ¬ claim := by
  rintro ⟨C, m₀, hC⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (max (C^2) (max (m₀ : ℝ) 1))
  have hmC : C^2 < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hmm₀ : (m₀ : ℝ) < m := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hm
  have hm₀ : m₀ ≤ m := by exact_mod_cast le_of_lt hmm₀
  have hmpos : 0 < (m : ℝ) := by
    have : (1 : ℝ) < m := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hm
    linarith
  have hs := Real.sq_sqrt (le_of_lt hmpos)
  have hspos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  have hCs : C < Real.sqrt (m : ℝ) := by nlinarith [Real.sqrt_nonneg (m : ℝ)]
  have hmul := mul_lt_mul_of_pos_right hCs hspos
  have hb := hC (List.replicate m 0) (by simpa using hm₀)
  rw [constant_word_complexity] at hb
  simp only [List.length_replicate, Nat.cast_add, Nat.cast_one] at hb
  nlinarith

end D5.S3.Quantum.QuantumChannels.QuantumCernyPureTargetRefutation
