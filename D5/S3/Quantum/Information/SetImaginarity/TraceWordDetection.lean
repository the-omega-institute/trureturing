/- GID: D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SetImaginarity/TraceWordDetection
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.claim; result=D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.result; claim=D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.claim
   digest: Four positive definite states have real trace words of every length but no common real basis. -/

import D5.S3.Quantum.Information.SetImaginarity.PrintedConjecture
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.LinearCombination

namespace D5.S3.Quantum.Information.SetImaginarity.TraceWordDetection

open Matrix
open PrintedConjecture (CommonRealBasis traceWord)
open scoped ComplexOrder Matrix

noncomputable section

/-- The all-word sufficiency implication in dimension four, using two pairs of basis vectors. -/
def claim : Prop :=
  ∀ ρ : Fin 4 → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ,
    Function.Injective ρ → (∀ j, (ρ j).PosSemidef ∧ (ρ j).trace = 1) →
    (∀ (k : ℕ) (w : Fin k → Fin 4), (traceWord ρ w).im = 0) →
    CommonRealBasis ρ

private abbrev Block := Matrix (Fin 2) (Fin 2) ℂ
private abbrev Index := Fin 2 ⊕ Fin 2
private abbrev Mat := Matrix Index Index ℂ

local notation "bar" => (starRingEnd ℂ).mapMatrix

private def X : Block := !![0, 1; 1, 0]
private def Z : Block := !![1, 0; 0, -1]
private def J : Block := !![0, 1; -1, 0]

private def generator : Fin 4 → Mat :=
  ![fromBlocks 1 0 0 (-1),
    fromBlocks 0 1 1 0,
    fromBlocks 0 (-Complex.I • X) (Complex.I • X) 0,
    fromBlocks 0 (-Complex.I • Z) (Complex.I • Z) 0]

private def states (j : Fin 4) : Mat :=
  (1 / 4 : ℂ) • 1 + (1 / 8 : ℂ) • generator j

private def Q : Mat := fromBlocks J 0 0 J

private theorem generator_adjoint (j : Fin 4) : (generator j)ᴴ = generator j := by
  fin_cases j <;> rw [show generator _ = _ from rfl, fromBlocks_conjTranspose] <;>
    simp only [fromBlocks_inj] <;>
    norm_num [X, Z, Matrix.ext_iff, Fin.forall_fin_two, Complex.star_def]

private theorem generator_sq (j : Fin 4) : generator j * generator j = 1 := by
  rw [← fromBlocks_one (l := Fin 2) (m := Fin 2) (α := ℂ)]
  fin_cases j <;>
    simp only [generator, Matrix.cons_val_zero, Matrix.cons_val_succ, fromBlocks_multiply,
      fromBlocks_inj] <;>
    norm_num [X, Z, Matrix.ext_iff, Fin.forall_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, Complex.I_mul_I]

private theorem generator_trace (j : Fin 4) : (generator j).trace = 0 := by
  fin_cases j <;>
    norm_num [generator, trace, diag, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply]

private theorem states_injective : Function.Injective states := by
  intro i j hij
  have h := congrArg (fun A : Mat =>
    (A (Sum.inl 0) (Sum.inl 0), A (Sum.inl 0) (Sum.inr 0), A (Sum.inl 0) (Sum.inr 1))) hij
  fin_cases i <;> fin_cases j <;>
    norm_num [states, generator, X, Z, Matrix.one_apply] at h ⊢ <;>
    simp_all [Complex.ext_iff]

private theorem states_posDef (j : Fin 4) : (states j).PosDef := by
  let H : Mat := 1 + generator j
  have hH : Hᴴ * H = (2 : ℂ) • (1 + generator j) := by
    simp [H, generator_adjoint, generator_sq, add_mul, mul_add, two_smul]
    abel
  have hgram : states j = (1 / 8 : ℂ) • 1 + (1 / 16 : ℂ) • (Hᴴ * H) := by
    rw [hH, smul_smul]
    norm_num [states, smul_add, ← add_smul]
  rw [hgram]
  apply PosDef.add_posSemidef
  · exact PosDef.one.smul (show (0 : ℂ) < 1 / 8 by
      exact_mod_cast (show (0 : ℝ) < 1 / 8 by norm_num))
  · exact (posSemidef_conjTranspose_mul_self H).smul (show (0 : ℂ) ≤ 1 / 16 by
      exact_mod_cast (show (0 : ℝ) ≤ 1 / 16 by norm_num))

private theorem states_trace (j : Fin 4) : (states j).trace = 1 := by
  norm_num [states, trace_add, trace_smul, trace_one, generator_trace, Fintype.card_sum]

private theorem affine_intertwine_iff (g C : Mat) :
    ((1 / 4 : ℂ) • 1 + (1 / 8 : ℂ) • g) * C =
      C * bar ((1 / 4 : ℂ) • 1 + (1 / 8 : ℂ) • g) ↔
    g * C = C * bar g := by
  have map_scale (a : ℂ) (A : Mat) :
      bar (a • A) = (starRingEnd ℂ a) • bar A := by
    exact Matrix.map_smul' _ _ _ (map_mul _)
  simp only [map_add, map_one, map_scale, map_div₀, map_natCast, add_mul, mul_add, smul_mul,
    Matrix.mul_smul, one_mul, mul_one, add_right_inj]
  exact (smul_right_injective (div_ne_zero one_ne_zero (by norm_num : (8 : ℂ) ≠ 0))).eq_iff

private theorem Q_right_inverse : Q * (-Q) = 1 := by
  rw [← fromBlocks_one (l := Fin 2) (m := Fin 2) (α := ℂ)]
  simp only [Q, ← fromBlocks_neg, fromBlocks_multiply, fromBlocks_inj, neg_zero, zero_mul,
    mul_zero, add_zero, zero_add, and_true, true_and]
  norm_num [J, Matrix.ext_iff, Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply]

private theorem Q_skew : Qᵀ = -Q := by
  rw [Q, fromBlocks_transpose, ← fromBlocks_neg]
  norm_num [J, Matrix.ext_iff, Fin.forall_fin_two]

private theorem Q_intertwines (j : Fin 4) : generator j * Q = Q * bar (generator j) := by
  fin_cases j <;>
    simp only [generator, Matrix.cons_val_zero, Matrix.cons_val_succ, RingHom.mapMatrix_apply,
      Q, fromBlocks_map, fromBlocks_multiply, fromBlocks_inj] <;>
    norm_num [X, Z, J, Matrix.ext_iff, Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Complex.star_def]

private theorem all_words_real (k : ℕ) (w : Fin k → Fin 4) : (traceWord states w).im = 0 := by
  have intertwines (word : List (Fin 4)) :
      (word.map states).prod * Q = Q * bar (word.map states).prod := by
    induction word with
    | nil => simp
    | cons j word ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, mul_assoc, ih]
      rw [← mul_assoc, (affine_intertwine_iff (generator j) Q).mpr (Q_intertwines j),
        mul_assoc]
  let W : Mat := (List.ofFn fun t => states (w t)).prod
  have h := intertwines (List.ofFn w)
  rw [List.map_ofFn] at h
  change W * Q = Q * bar W at h
  have htrace : (bar W).trace = W.trace := calc
    (bar W).trace = trace ((-Q) * (Q * bar W)) := by
      have hleft : (-Q) * Q = 1 := by
        simpa only [neg_mul, mul_neg] using Q_right_inverse
      rw [← mul_assoc, hleft, one_mul]
    _ = trace ((-Q) * (W * Q)) := by rw [h]
    _ = W.trace := by rw [← mul_assoc, trace_mul_comm, ← mul_assoc, Q_right_inverse, one_mul]
  change W.trace.im = 0
  have him := congrArg Complex.im
    ((AddMonoidHom.map_trace (starRingEnd ℂ) W).trans htrace)
  exact CharZero.neg_eq_self_iff.mp (by simpa [Complex.star_def] using him)

private theorem intertwiner_form (C : Mat)
    (h : ∀ j, generator j * C = C * bar (generator j)) :
    ∃ b : ℂ, C = b • Q := by
  let A := C.toBlocks₁₁
  let B := C.toBlocks₁₂
  let D := C.toBlocks₂₁
  let E := C.toBlocks₂₂
  have hblocks : fromBlocks A B D E = C := fromBlocks_toBlocks C
  have h₁ := h 0
  have h₂ := h 1
  have h₃ := h 2
  have h₄ := h 3
  have h₁bar : bar (generator 0) = generator 0 := by
    change bar (fromBlocks (1 : Block) 0 0 (-1)) = _
    simp [RingHom.mapMatrix_apply, fromBlocks_map, Matrix.map_one, Matrix.map_zero,
      Matrix.map_neg]
  have h₂bar : bar (generator 1) = generator 1 := by
    change bar (fromBlocks (0 : Block) 1 1 0) = _
    simp [RingHom.mapMatrix_apply, fromBlocks_map, Matrix.map_one, Matrix.map_zero, generator]
  have h₃bar : bar (generator 2) = -(generator 2) := by
    change (fromBlocks ((0 : Block)) (-Complex.I • X) (Complex.I • X) 0).map
      (starRingEnd ℂ) = _
    rw [fromBlocks_map, generator, Matrix.cons_val_succ, Matrix.cons_val_succ,
      Matrix.cons_val_zero, ← fromBlocks_neg]
    simp only [fromBlocks_inj]
    norm_num [X, Matrix.ext_iff, Fin.forall_fin_two, Complex.star_def]
  have h₄bar : bar (generator 3) = -(generator 3) := by
    change (fromBlocks ((0 : Block)) (-Complex.I • Z) (Complex.I • Z) 0).map
      (starRingEnd ℂ) = _
    rw [fromBlocks_map, generator, Matrix.cons_val_succ, Matrix.cons_val_succ,
      Matrix.cons_val_succ, Matrix.cons_val_zero, ← fromBlocks_neg]
    simp only [fromBlocks_inj]
    norm_num [Z, Matrix.ext_iff, Fin.forall_fin_two, Complex.star_def]
  rw [h₁bar, ← hblocks] at h₁
  rw [h₂bar, ← hblocks] at h₂
  have hb : B = -B := by
    simpa [generator, fromBlocks_multiply] using congrArg Matrix.toBlocks₁₂ h₁
  have hd : -D = D := by
    simpa [generator, fromBlocks_multiply] using congrArg Matrix.toBlocks₂₁ h₁
  have hB : B = 0 := CharZero.neg_eq_self_iff.mp hb.symm
  have hD : D = 0 := CharZero.neg_eq_self_iff.mp hd
  have hE : E = A := by
    simpa [generator, fromBlocks_multiply] using congrArg Matrix.toBlocks₁₂ h₂
  have hdiag : fromBlocks A 0 0 A = C := by simpa [hB, hD, hE] using hblocks
  rw [h₃bar, ← hdiag] at h₃
  rw [h₄bar, ← hdiag] at h₄
  have cancel_I (P : Block) (hp : (-Complex.I : ℂ) • (P * A) = (-Complex.I : ℂ) • -(A * P)) :
      P * A = -(A * P) :=
    smul_right_injective (neg_ne_zero.mpr Complex.I_ne_zero) hp
  have hx : X * A = -(A * X) := by
    apply cancel_I
    simpa [generator, ← fromBlocks_neg, fromBlocks_multiply, smul_mul, Matrix.mul_smul,
      smul_neg, neg_smul] using congrArg Matrix.toBlocks₁₂ h₃
  have hz : Z * A = -(A * Z) := by
    apply cancel_I
    simpa [generator, ← fromBlocks_neg, fromBlocks_multiply, smul_mul, Matrix.mul_smul,
      smul_neg, neg_smul] using congrArg Matrix.toBlocks₁₂ h₄
  have ha₀ : A 0 0 = 0 := by
    have he := congrArg (fun M : Block => M 0 0) hz
    simp [Z, mul_apply, Fin.sum_univ_two] at he
    exact CharZero.neg_eq_self_iff.mp he.symm
  have ha₁ : A 1 1 = 0 := by
    have he := congrArg (fun M : Block => M 1 1) hz
    simp [Z, mul_apply, Fin.sum_univ_two] at he
    exact CharZero.neg_eq_self_iff.mp he
  have ha₂ : A 1 0 = -(A 0 1) := by
    simpa [X, mul_apply, Fin.sum_univ_two] using congrArg (fun M : Block => M 0 0) hx
  have ha : A = A 0 1 • J := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, ha₀, ha₁, ha₂]
  refine ⟨A 0 1, ?_⟩
  rw [Q, fromBlocks_smul, smul_zero, smul_zero, ← ha, hdiag]

private theorem no_common_basis : ¬ CommonRealBasis states := by
  rintro ⟨U, hreal⟩
  let V : Mat := U
  let C : Mat := Vᴴ * bar V
  have hV : Vᴴ * V = 1 := UnitaryGroup.star_mul_self U
  have hVt : (bar V)ᴴ = Vᵀ := by
    ext i j
    simp [V, RingHom.mapMatrix_apply]
  have hVtV : Vᵀ * bar V = 1 := by
    rw [← hVt]
    exact UnitaryGroup.star_mul_self (UnitaryGroup.map_star U)
  have hCsymm : Cᵀ = C := by
    rw [show Vᴴ = (bar V)ᵀ from rfl]
    simp [C, transpose_mul, conjTranspose, RingHom.mapMatrix_apply]
  have hC (j : Fin 4) : generator j * C = C * bar (generator j) := by
    have hj : bar (V * states j * Vᴴ) = V * states j * Vᴴ := by
      ext i l
      apply Complex.ext <;> simp [RingHom.mapMatrix_apply, Complex.star_def, V, hreal]
    have hVbar : bar Vᴴ = Vᵀ := by
      ext i l
      simp [RingHom.mapMatrix_apply]
    simp only [map_mul, hVbar] at hj
    apply (affine_intertwine_iff (generator j) C).mp
    change states j * C = C * bar (states j)
    calc
      states j * C = Vᴴ * (V * states j * Vᴴ) * bar V := by
        simp only [C, ← mul_assoc, hV, one_mul]
      _ = Vᴴ * (bar V * bar (states j) * Vᵀ) * bar V := by rw [hj]
      _ = C * bar (states j) := by
        simp only [C, mul_assoc, hVtV, mul_one]
  obtain ⟨b, hb⟩ := intertwiner_form C hC
  have hzero : C = 0 := by
    have hneg : -C = C := calc
      -C = Cᵀ := by rw [hb, transpose_smul, Q_skew, smul_neg]
      _ = C := hCsymm
    exact CharZero.neg_eq_self_iff.mp hneg
  have hunit : C ∈ unitaryGroup Index ℂ := (U⁻¹ * UnitaryGroup.map_star U).property
  have hOne : C * star C = 1 := mem_unitaryGroup_iff.mp hunit
  rw [hzero, zero_mul] at hOne
  exact zero_ne_one hOne

/-- Four distinct density operators can have real traces for all words and no common real basis. -/
theorem result : ¬ claim := by
  intro h
  exact no_common_basis
    (h states states_injective (fun j => ⟨(states_posDef j).posSemidef, states_trace j⟩)
      all_words_real)

end

end D5.S3.Quantum.Information.SetImaginarity.TraceWordDetection
