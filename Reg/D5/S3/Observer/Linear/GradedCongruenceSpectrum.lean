import D5.S3.Observer.Linear.GradedCongruenceSpectrum
import Reg.Support.DependentFamily
import Mathlib.Algebra.Order.Star.Real

open _root_.D5.S3.Observer.Linear
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Observer.Linear.GradedCongruenceSpectrum

structure Parameters where
  n : ℕ
  H : ℝ → Matrix (Fin n) (Fin n) ℝ
  H₀ : Matrix (Fin n) (Fin n) ℝ
  w : Fin n → ℕ
  hw : Monotone w
  hH : Filter.Tendsto H (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds H₀)
  hH₀ : H₀.PosDef
  hGpos : ∀ T, 0 < T →
    (Matrix.diagonal (fun i : Fin n => T ^ w i * Real.sqrt T) * H T *
      Matrix.diagonal (fun i : Fin n => T ^ w i * Real.sqrt T)).PosDef

abbrev signature : Signature where
  Params := Parameters
  State := fun p => {T : ℝ // 0 < T} × Fin p.n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p s =>
      (p.hGpos s.1.1 s.1.2).isHermitian.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin p.n)).symm s.2))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Parameters,
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ T i (hT : 0 < T), T < δ →
        c * T ^ (2 * p.w i + 1) ≤
            R.readout () p (⟨⟨T, hT⟩, i⟩) ∧
        R.readout () p (⟨⟨T, hT⟩, i⟩) ≤ C * T ^ (2 * p.w i + 1)

theorem actual_law : arena.Law actual := by
  intro p
  obtain ⟨c, C, δ, hc, hC, hδ, hb⟩ :=
    graded_congruence_spectrum p.H p.H₀ p.w p.hw p.hH p.hH₀ p.hGpos
  refine ⟨c, C, δ, hc, hC, hδ, ?_⟩
  intro T i hT hTδ
  simpa [actual, realize] using hb T i hT hTδ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Parameters := {
    n := 1
    H := fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)
    H₀ := (1 : Matrix (Fin 1) (Fin 1) ℝ)
    w := fun _ => 0
    hw := by intro a b hab; rfl
    hH := by
      simpa using (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1))
    hH₀ := Matrix.PosDef.one
    hGpos := by
      intro T hT
      let d : Fin 1 → ℝ := fun _ => T ^ (0 : ℕ) * Real.sqrt T
      have hd : ∀ i : Fin 1, 0 < d i ^ 2 := by
        intro i
        simp [d, Real.sq_sqrt (le_of_lt hT), hT]
      have heq :
          (Matrix.diagonal d * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
            Matrix.diagonal d) = Matrix.diagonal (fun i => d i ^ 2) := by
        simp only [← Matrix.diagonal_one, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        dsimp [d]
        ring
      rw [heq]
      exact Matrix.posDef_diagonal_iff.mpr hd
  }
  obtain ⟨c, _, δ, hc, _, hδ, hb⟩ := h p
  have hsmall : (0 : ℝ) < min δ 1 := lt_min hδ zero_lt_one
  have hbound := (hb (min δ 1 / 2) 0 (by positivity) (by
    have : min δ 1 ≤ δ := min_le_left _ _
    nlinarith [hsmall])).1
  have hnonpos : rejected.readout () p (⟨⟨min δ 1 / 2, by positivity⟩, 0⟩) = 0 := rfl
  rw [hnonpos] at hbound
  have hpow : 0 < (min δ 1 / 2 : ℝ) ^ (2 * p.w 0 + 1) := by positivity
  have hprod : 0 < c * (min δ 1 / 2 : ℝ) ^ (2 * p.w 0 + 1) :=
    mul_pos hc hpow
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  let p : Parameters := {
    n := 1
    H := fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)
    H₀ := (1 : Matrix (Fin 1) (Fin 1) ℝ)
    w := fun _ => 0
    hw := by intro a b hab; rfl
    hH := by
      simpa using (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1))
    hH₀ := Matrix.PosDef.one
    hGpos := by
      intro T hT
      let d : Fin 1 → ℝ := fun _ => T ^ (0 : ℕ) * Real.sqrt T
      have hd : ∀ i : Fin 1, 0 < d i ^ 2 := by
        intro i
        simp [d, Real.sq_sqrt (le_of_lt hT), hT]
      have heq :
          (Matrix.diagonal d * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
            Matrix.diagonal d) = Matrix.diagonal (fun i => d i ^ 2) := by
        simp only [← Matrix.diagonal_one, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        dsimp [d]
        ring
      rw [heq]
      exact Matrix.posDef_diagonal_iff.mpr hd
  }
  refine ⟨p,
    ⟨⟨1, by norm_num⟩, 0⟩, ⟨⟨4, by norm_num⟩, 0⟩, ?_⟩
  intro hEq
  let A1 : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.diagonal (fun i : Fin 1 => (1 : ℝ) ^ p.w i * Real.sqrt 1) *
      p.H 1 * Matrix.diagonal (fun i : Fin 1 => (1 : ℝ) ^ p.w i * Real.sqrt 1)
  let A4 : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.diagonal (fun i : Fin 1 => (4 : ℝ) ^ p.w i * Real.sqrt 4) *
      p.H 4 * Matrix.diagonal (fun i : Fin 1 => (4 : ℝ) ^ p.w i * Real.sqrt 4)
  have hpos1 : A1.PosDef := by
    simpa [A1] using p.hGpos 1 (by norm_num)
  have hpos4 : A4.PosDef := by
    simpa [A4] using p.hGpos 4 (by norm_num)
  let hH1 := hpos1.isHermitian
  let hH4 := hpos4.isHermitian
  have hEq' :
      (hH1.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin 1)).symm 0)) =
      (hH4.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin 1)).symm 0)) := by
    change hH1.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin 1)).symm 0) =
      hH4.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin 1)).symm 0) at hEq
    exact hEq
  have htrace1 := hH1.trace_eq_sum_eigenvalues
  have htrace4 := hH4.trace_eq_sum_eigenvalues
  have hcoord1 :
      (hH1.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin 1)).symm 0)) =
      hH1.eigenvalues 0 := by
    simp only [Matrix.IsHermitian.eigenvalues]
    apply congrArg _
    apply Fin.ext
    have hc : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
    have hl := ((Fin.castOrderIso (Fintype.card_fin 1)).symm 0).isLt
    have hr :=
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 1)))).symm 0).isLt
    omega
  have hcoord4 :
      (hH4.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin 1)).symm 0)) =
      hH4.eigenvalues 0 := by
    simp only [Matrix.IsHermitian.eigenvalues]
    apply congrArg _
    apply Fin.ext
    have hc : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
    have hl := ((Fin.castOrderIso (Fintype.card_fin 1)).symm 0).isLt
    have hr :=
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 1)))).symm 0).isLt
    omega
  rw [hcoord1, hcoord4] at hEq'
  have hA1 : A1.trace = (1 : ℝ) := by
    norm_num [A1, p, Matrix.trace, Matrix.diagonal, Matrix.mul_apply,
      Fin.sum_univ_one, Real.sq_sqrt]
  have hA4 : A4.trace = (4 : ℝ) := by
    norm_num [A4, p, Matrix.trace, Matrix.diagonal, Matrix.mul_apply,
      Fin.sum_univ_one, Real.sq_sqrt]
  rw [hA1] at htrace1
  rw [hA4] at htrace4
  norm_num [Fin.sum_univ_one] at htrace1 htrace4
  linarith [htrace1, htrace4, hEq']

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem graded_congruence_spectrum in arena
  readout via (realize signature
    (fun _ p s =>
      (p.hGpos s.1.1 s.1.2).isHermitian.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin p.n)).symm s.2))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Linear.GradedCongruenceSpectrum
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Observer.Linear.GradedCongruenceSpectrum
