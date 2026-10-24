/- GID: D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.claim; result=D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.result; claim=D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.claim
   digest: A four-party eight-level pure state has only zero-volume fills and is not biseparable. -/

import D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation

/-! A pure four-qudit counterexample to the genuine requirement for entropic tetrahedra. -/

noncomputable section
set_option linter.style.longLine false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EntropicFill.QuditTetrahedronGenuineRefutation

open scoped BigOperators
open D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation (entropy entropy_diagonal)

/-- The one-party reduced density matrix in the computational basis. -/
def rho1 {d : ℕ} (ψ : (Fin 4 → Fin d) → ℂ) (i : Fin 4) :
    Matrix (Fin d) (Fin d) ℂ := fun a a' =>
  ∑ x : Fin 4 → Fin d, if x i = a then
    ψ x * star (ψ (Function.update x i a')) else 0

/-- The two-party reduced density matrix; its uses have distinct parties. -/
def rho2 {d : ℕ} (ψ : (Fin 4 → Fin d) → ℂ) (i j : Fin 4) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := fun a a' =>
  ∑ x : Fin 4 → Fin d, if x i = a.1 ∧ x j = a.2 then
    ψ x * star (ψ (Function.update (Function.update x i a'.1) j a'.2)) else 0

/-- Base-two spectral von Neumann entropy, with the frozen natural-log entropy. -/
def entropy2 {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) : ℝ :=
  entropy ρ / Real.log 2

/-- Factorization across a nonempty proper cut of the four parties. -/
def Biseparable {d : ℕ} (ψ : (Fin 4 → Fin d) → ℂ) : Prop :=
  ∃ X : Finset (Fin 4), X.Nonempty ∧ Xᶜ.Nonempty ∧
    ∃ φ χ : (Fin 4 → Fin d) → ℂ,
      (∀ x y, (∀ i ∈ X, x i = y i) → φ x = φ y) ∧
      (∀ x y, (∀ i ∉ X, x i = y i) → χ x = χ y) ∧
      ∀ x, ψ x = φ x * χ x

/-- The six coordinates are AB, AC, AD, BC, BD, CD, in that order. -/
def AdmissibleFill {d : ℕ} (ψ : (Fin 4 → Fin d) → ℂ)
    (σ : Fin 6 → ℝ) (ell : ℝ) : Prop :=
  (∀ k, 0 ≤ σ k) ∧
  σ 0 + σ 1 + σ 2 = entropy2 (rho1 ψ 0) ∧
  σ 0 + σ 3 + σ 4 = entropy2 (rho1 ψ 1) ∧
  σ 1 + σ 3 + σ 5 = entropy2 (rho1 ψ 2) ∧
  σ 2 + σ 4 + σ 5 = entropy2 (rho1 ψ 3) ∧
  -Real.sqrt (σ 0 * σ 5) + Real.sqrt (σ 1 * σ 4) + Real.sqrt (σ 2 * σ 3) =
    ell * entropy2 (rho2 ψ 0 1) ∧
  Real.sqrt (σ 0 * σ 5) - Real.sqrt (σ 1 * σ 4) + Real.sqrt (σ 2 * σ 3) =
    ell * entropy2 (rho2 ψ 0 2) ∧
  Real.sqrt (σ 0 * σ 5) + Real.sqrt (σ 1 * σ 4) - Real.sqrt (σ 2 * σ 3) =
    ell * entropy2 (rho2 ψ 0 3)

/-- The source volume, including its surface-area factor and all four radical factors. -/
def volume (σ : Fin 6 → ℝ) : ℝ :=
  let p := Real.sqrt (σ 0 * σ 5)
  let q := Real.sqrt (σ 1 * σ 4)
  let r := Real.sqrt (σ 2 * σ 3)
  Real.sqrt 2 / 3 * Real.sqrt (2 * ∑ k, σ k) *
    Real.rpow ((p + q + r) * (-p + q + r) * (p - q + r) * (p + q - r)) (1 / 4)

/-- Vanishing of every admissible fill of a unit pure state implies biseparability. -/
def claim : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ ψ : (Fin 4 → Fin d) → ℂ,
    (∑ x, ‖ψ x‖ ^ 2 = 1) →
    (∃ σ ell, AdmissibleFill ψ σ ell) →
    (∀ σ ell, AdmissibleFill ψ σ ell → volume σ = 0) → Biseparable ψ

private def supported (x : Fin 4 → Fin 8) : Prop :=
  (x 0).val = 4 * (x 1).val + 2 * (x 2).val + (x 3).val ∧
    (x 1).val < 2 ∧ (x 2).val < 2 ∧ (x 3).val < 2

private def psi (x : Fin 4 → Fin 8) : ℂ := by
  classical
  exact if supported x then ((Real.sqrt 8)⁻¹ : ℝ) else 0

private def label (t : Fin 8) : Fin 4 → Fin 8 :=
  ![t, ⟨t.val / 4, by omega⟩, ⟨t.val / 2 % 2, by omega⟩, ⟨t.val % 2, by omega⟩]

private theorem label_supported (t : Fin 8) : supported (label t) := by
  dsimp [supported, label]
  omega

private theorem label_reconstruct (x : Fin 4 → Fin 8) (hx : supported x) :
    label (x 0) = x := by
  dsimp [supported] at hx
  funext i
  fin_cases i <;> apply Fin.ext <;> simp [label] <;> omega

open Classical in
private theorem sum_supported {α : Type*} [AddCommMonoid α]
    (f : (Fin 4 → Fin 8) → α) :
    (∑ x, if supported x then f x else 0) = ∑ t : Fin 8, f (label t) := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun t _ => label t) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact label_supported t
  · intro t _ u _ h
    simpa [label] using congrFun h 0
  · intro x hx
    exact ⟨x 0, Finset.mem_univ _, label_reconstruct x (Finset.mem_filter.mp hx).2⟩

private theorem supported_update (x : Fin 4 → Fin 8) (hx : supported x)
    (i : Fin 4) (a : Fin 8) : supported (Function.update x i a) ↔ a = x i := by
  constructor
  · intro hy
    dsimp [supported] at hx hy
    fin_cases i <;> apply Fin.ext <;>
      norm_num [Function.update_apply] at hy ⊢ <;> omega
  · rintro rfl
    simpa only [Function.update_eq_self] using hx

private theorem normalized : ∑ x, ‖psi x‖ ^ 2 = 1 := by
  classical
  calc
    _ = ∑ x, if supported x then (1 / 8 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : supported x
      · simp only [psi, ite_eq_left hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        rw [inv_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      · simp [psi, hx]
    _ = ∑ _t : Fin 8, (1 / 8 : ℝ) := sum_supported (fun _ => (1 / 8 : ℝ))
    _ = 1 := by norm_num

private theorem marginal_entries (i : Fin 4) (a b : Fin 8) :
    rho1 psi i a b =
      ∑ t : Fin 8, if label t i = a ∧ b = a then (1 / 8 : ℂ) else 0 := by
  classical
  have hsq : ((Real.sqrt 8 : ℂ)⁻¹) ^ 2 = (1 / 8 : ℂ) := by
    calc
      _ = (((Real.sqrt 8)⁻¹ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      _ = ((1 / 8 : ℝ) : ℂ) := congrArg (fun r : ℝ => (r : ℂ)) (by
        rw [inv_pow, Real.sq_sqrt (by norm_num)]
        norm_num)
      _ = _ := by norm_num
  unfold rho1
  trans ∑ x, if supported x then
    (if x i = a ∧ b = a then (1 / 8 : ℂ) else 0) else 0
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hs : supported x
    · have hu := supported_update x hs i b
      by_cases ha : x i = a
      · by_cases hb : b = a
        · have hup : supported (Function.update x i a) :=
            (supported_update x hs i a).mpr ha.symm
          simp [psi, hs, hup, ha, hb, ← pow_two, hsq]
        · simp [psi, hs, hu, ha, hb]
      · simp [ha]
    · simp [psi, hs]
  · exact sum_supported _

private theorem marginal_A : rho1 psi 0 = Matrix.diagonal (fun _ => (1 / 8 : ℂ)) := by
  ext a b
  by_cases hab : b = a
  · subst b
    simp [marginal_entries, label]
  · simp [marginal_entries, hab, Ne.symm hab]

private theorem marginal_leaf (i : Fin 4) (hi : i ≠ 0) :
    rho1 psi i = Matrix.diagonal (fun a => if a.val < 2 then (1 / 2 : ℂ) else 0) := by
  ext a b
  rw [marginal_entries]
  by_cases hab : b = a
  · subst b
    rw [Matrix.diagonal_apply_eq]
    simp only [and_true]
    fin_cases i
    · exact (hi rfl).elim
    all_goals fin_cases a <;> norm_num [label, Fin.sum_univ_succ]
  · simp [hab, Ne.symm hab]

private theorem entropies :
    entropy2 (rho1 psi 0) = 3 ∧ entropy2 (rho1 psi 1) = 1 ∧
    entropy2 (rho1 psi 2) = 1 ∧ entropy2 (rho1 psi 3) = 1 := by
  have hlog : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hne : Real.log (2 : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hA : entropy2 (rho1 psi 0) = 3 := by
    rw [marginal_A, entropy2]
    rw [show (1 / 8 : ℂ) = ((1 / 8 : ℝ) : ℂ) by norm_num, entropy_diagonal]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply (div_eq_iff hne).mpr
    norm_num [Real.negMulLog, Real.log_div, hlog]
    <;> ring
  have hL (i : Fin 4) (hi : i ≠ 0) : entropy2 (rho1 psi i) = 1 := by
    rw [marginal_leaf i hi, entropy2]
    let w : Fin 8 → ℝ := fun a => if a.val < 2 then 1 / 2 else 0
    have hdiag : (fun a : Fin 8 => if a.val < 2 then (1 / 2 : ℂ) else 0) =
        (fun a => (w a : ℂ)) := by
      funext a
      dsimp [w]
      split_ifs <;> norm_num
    rw [hdiag, entropy_diagonal]
    apply (div_eq_iff hne).mpr
    norm_num [w, Fin.sum_univ_succ, Real.negMulLog, Real.log_div]
    <;> ring
  exact ⟨hA, hL 1 (by decide), hL 2 (by decide), hL 3 (by decide)⟩

private theorem forced_fill (σ : Fin 6 → ℝ) (ell : ℝ) (h : AdmissibleFill psi σ ell) :
    σ = ![1, 1, 1, 0, 0, 0] := by
  rcases h with ⟨hn, hA, hB, hC, hD, _⟩
  rcases entropies with ⟨eA, eB, eC, eD⟩
  rw [eA] at hA
  rw [eB] at hB
  rw [eC] at hC
  rw [eD] at hD
  funext k
  fin_cases k <;> simp <;> linarith [hn 3, hn 4, hn 5]

private theorem exists_fill : ∃ σ ell, AdmissibleFill psi σ ell := by
  rcases entropies with ⟨eA, eB, eC, eD⟩
  refine ⟨![1, 1, 1, 0, 0, 0], 0, ?_⟩
  constructor
  · intro k
    fin_cases k <;> norm_num
  · norm_num [eA, eB, eC, eD]

private theorem all_volume_zero (σ : Fin 6 → ℝ) (ell : ℝ)
    (h : AdmissibleFill psi σ ell) : volume σ = 0 := by
  sorry

private theorem not_biseparable : ¬ Biseparable psi := by
  sorry

theorem result : ¬ claim := by
  intro h
  exact not_biseparable (h 8 (by norm_num) psi normalized exists_fill all_volume_zero)

end D5.S3.Quantum.Entanglement.EntropicFill.QuditTetrahedronGenuineRefutation
