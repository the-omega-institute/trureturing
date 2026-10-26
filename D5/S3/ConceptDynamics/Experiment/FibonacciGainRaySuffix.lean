/- GID: D5/S3/ConceptDynamics/Experiment/FibonacciGainRaySuffix
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/FibonacciGainRaySuffix
   mirror-E: none(waiver:exact-symbolic-acquisition-obstruction)
   anchors: []
   utility: none
   digest: Universal collinearity annihilates the identical-row family on short suffixes. -/

import D5.S3.ConceptDynamics.Experiment.SelfCalibratingRulings
import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Exact linear gain-ray obstruction for native chronological Fibonacci words. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Matrix
open Matrix

namespace D5.S3.ConceptDynamics.Experiment.FibonacciGainRaySuffix

private abbrev RW := Arith.FibonacciAtomic.SelfCalibratingRawWords.word

/-- The normalized identical-row source, with its original real parameter. -/
def source (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1-θ, θ; 1-θ, θ]

/-- A whole polynomial in ordinary ascending coefficient coordinates. -/
def gain {m : ℕ} (β : Fin m → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin m, β j * t ^ (j : ℕ)

/-- Each prefix is read immediately at its original clock, including clock zero. -/
def reads {m N : ℕ} (w : List Bool) (θ : ℝ) (β : Fin m → ℝ) (δ : ℝ) : Fin N → ℝ :=
  fun i => gain β (i : ℕ) *
    SelfCalibratingRulings.observe (SelfCalibratingRulings.matrix (w.take i)) (source θ) + δ

private def rows (w : List Bool) : Fin 2 → ℝ :=
  SelfCalibratingRulings.matrix w *ᵥ (fun _ => 1)

private lemma matrix_append (p q : List Bool) :
    SelfCalibratingRulings.matrix (p ++ q) =
      SelfCalibratingRulings.matrix q * SelfCalibratingRulings.matrix p := by
  have h := (Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound p).2.2.2.1 q
  ext i j
  have h' := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A i j) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h'
  change ((RW (p ++ q) i j : ℤ) : ℝ) = _
  simpa [SelfCalibratingRulings.matrix, Matrix.mul_apply, Fin.sum_univ_two] using
    congrArg (fun z : ℤ => (z : ℝ)) h'

private lemma rows_snoc (w : List Bool) (a : Bool) :
    rows (w ++ [a]) = if a then ![rows w 1, rows w 0]
      else ![rows w 1, rows w 0 + rows w 1] := by
  rw [rows, matrix_append, ← Matrix.mulVec_mulVec]
  change SelfCalibratingRulings.matrix [a] *ᵥ rows w = _
  cases a <;> ext i <;> fin_cases i <;>
    simp [SelfCalibratingRulings.matrix, Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma rows_invariant (w : List Bool) :
    (∀ i, 0 < rows w i) ∧
    (false ∉ w → rows w = fun _ => 1) ∧
    (false ∈ w → rows w 0 ≠ rows w 1) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp [rows, SelfCalibratingRulings.matrix,
      Arith.FibonacciAtomic.SelfCalibratingRawWords.word]
  | append_singleton w a ih =>
    rcases ih with ⟨hp, hj, hm⟩
    rw [rows_snoc]
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton,
        or_true, not_true_eq_false, false_implies, true_implies]
      refine ⟨?_, trivial, ?_⟩
      · intro i; fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        · exact hp 1
        · exact add_pos (hp 0) (hp 1)
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith [hp 0]
    · simp only [↓reduceIte, List.mem_append, List.mem_singleton, Bool.false_eq_true,
        or_false]
      refine ⟨?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        · exact hp 1
        · exact hp 0
      · intro h
        rw [hj h]
        ext i; fin_cases i <;> rfl
      · intro h
        simpa using (hm h).symm

private lemma observe_rows (w : List Bool) (θ : ℝ) :
    SelfCalibratingRulings.observe (SelfCalibratingRulings.matrix w) (source θ) =
      rows w 0 + θ * (rows w 1 - rows w 0) := by
  simp [SelfCalibratingRulings.observe, source, rows, Matrix.trace,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

private lemma affine_scalar {m : ℕ} (hm : 2 ≤ m)
    (L : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ)
    (h : ∀ β : Fin m → ℝ, β ≠ 0 → ∀ δ : ℝ,
      ∃ s : ℝ, L *ᵥ β + δ • v = s • β) :
    v = 0 ∧ ∃ a : ℝ, L = a • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  classical
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have hv : v = 0 := by
    ext j
    obtain ⟨k, hkj⟩ := exists_ne j
    let β : Fin m → ℝ := Pi.single k 1
    have hβ : β ≠ 0 := by
      intro hz
      have := congrFun hz k
      simp [β] at this
    obtain ⟨s, hs⟩ := h β hβ 0
    obtain ⟨t, ht⟩ := h β hβ 1
    have hs' := congrFun hs j
    have ht' := congrFun ht j
    simp [β, hkj.symm] at hs' ht'
    change v j = 0
    linarith
  refine ⟨hv, ?_⟩
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := Matrix.toLin' L) (fun β => by
      by_cases hb : β = 0
      · simp only [hb, map_zero]
        intro hi
        exact (hi.ne_zero 0) rfl
      · obtain ⟨s, hs⟩ := h β hb 0
        simp only [zero_smul, add_zero] at hs
        rw [LinearIndependent.pair_iff' hb]
        push Not
        exact ⟨s, by simpa using hs.symm⟩)
  refine ⟨a, ?_⟩
  apply Matrix.toLin'.injective
  calc
    Matrix.toLin' L = a • (1 : Module.End ℝ (Fin m → ℝ)) := ha
    _ = Matrix.toLin' (a • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
      ext β j
      simp

private def evaluation (m N : ℕ) : Matrix (Fin N) (Fin m) ℝ :=
  fun i j => (i : ℝ) ^ (j : ℕ)

private def weighted {m N : ℕ} (C : Matrix (Fin m) (Fin N) ℝ)
    (a : Fin N → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  C * Matrix.diagonal a * evaluation m N

private lemma weighted_apply {m N : ℕ} (C : Matrix (Fin m) (Fin N) ℝ)
    (a : Fin N → ℝ) (j k : Fin m) :
    weighted C a j k = ∑ i : Fin N, C j i * a i * (i : ℝ) ^ (k : ℕ) := by
  change ∑ i : Fin N, (C * Matrix.diagonal a) j i * (i : ℝ) ^ (k : ℕ) = _
  simp only [Matrix.mul_diagonal]

private lemma readout_matrix {m N : ℕ} (w : List Bool)
    (C : Matrix (Fin m) (Fin N) ℝ) (θ : ℝ) (β : Fin m → ℝ) (δ : ℝ) :
    C *ᵥ reads w θ β δ =
      weighted C (fun i : Fin N => rows (w.take i) 0 +
        θ * (rows (w.take i) 1 - rows (w.take i) 0)) *ᵥ β +
      δ • (C *ᵥ (fun _ => 1)) := by
  have he : reads w θ β δ =
      (Matrix.diagonal (fun i : Fin N => rows (w.take i) 0 +
        θ * (rows (w.take i) 1 - rows (w.take i) 0)) * evaluation m N) *ᵥ β +
      δ • (fun _ => 1) := by
    ext i
    simp [reads, gain, observe_rows, evaluation, Matrix.mulVec, dotProduct,
      Finset.mul_sum, mul_comm, mul_assoc]
  rw [he, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  simp only [weighted, Matrix.mul_assoc]

private lemma scalar_pencil {m N : ℕ} (hm : 2 ≤ m) (w : List Bool)
    (C : Matrix (Fin m) (Fin N) ℝ)
    (h : ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ β : Fin m → ℝ, β ≠ 0 → ∀ δ : ℝ,
      ∃ s : ℝ, C *ᵥ reads w θ β δ = s • β) :
    C *ᵥ (fun _ => 1) = 0 ∧ ∃ a b : ℝ,
      weighted C (fun i : Fin N => rows (w.take i) 0) = a • 1 ∧
      weighted C (fun i : Fin N => rows (w.take i) 1 - rows (w.take i) 0) = b • 1 := by
  have hs (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) :=
    affine_scalar hm _ _ (fun β hb δ => by
      obtain ⟨s, hs⟩ := h θ h0 h1 β hb δ
      exact ⟨s, by rwa [readout_matrix] at hs⟩)
  obtain ⟨hv, a, ha⟩ := hs (1/3) (by norm_num) (by norm_num)
  obtain ⟨_, b, hb⟩ := hs (2/3) (by norm_num) (by norm_num)
  refine ⟨hv, 2*a-b, 3*(b-a), ?_, ?_⟩
  all_goals
    ext j k
    have hlin (θ : ℝ) :
        weighted C (fun i : Fin N => rows (w.take i) 0 +
          θ * (rows (w.take i) 1 - rows (w.take i) 0)) j k =
        weighted C (fun i : Fin N => rows (w.take i) 0) j k +
          θ * weighted C (fun i : Fin N => rows (w.take i) 1 - rows (w.take i) 0) j k := by
      simp only [weighted_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h1 := congrArg (fun A : Matrix (Fin m) (Fin m) ℝ => A j k) ha
    have h2 := congrArg (fun A : Matrix (Fin m) (Fin m) ℝ => A j k) hb
    rw [hlin] at h1 h2
    simp only [Matrix.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linarith

private lemma weighted_support {m N : ℕ} (C : Matrix (Fin m) (Fin N) ℝ)
    (b : Fin N → ℝ) (hcard : Fintype.card {i : Fin N // b i ≠ 0} < m)
    (a : ℝ) (ha : weighted C b = a • 1) :
    a = 0 ∧ ∀ j i, b i ≠ 0 → C j i = 0 := by
  classical
  let S := {i : Fin N // b i ≠ 0}
  have hr : (weighted C b).rank ≤ Fintype.card S := by
    calc
      (weighted C b).rank ≤ (C * Matrix.diagonal b).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (Matrix.diagonal b).rank := Matrix.rank_mul_le_right _ _
      _ = Fintype.card S := Matrix.rank_diagonal b
  have hz : a = 0 := by
    by_contra hn
    have hmem : a ∈ nonZeroDivisors ℝ := mem_nonZeroDivisors_iff_ne_zero.mpr hn
    rw [ha, Matrix.rank_smul_of_mem_nonZeroDivisors _ hmem,
      Matrix.rank_one, Fintype.card_fin] at hr
    change m ≤ Fintype.card {i : Fin N // b i ≠ 0} at hr
    omega
  have hzero : weighted C b = 0 := by simpa [hz] using ha
  refine ⟨hz, ?_⟩
  let e := Fintype.equivFin S
  let nodes : Fin (Fintype.card S) → ℝ := fun k => ((e.symm k).val : ℝ)
  have hn : Function.Injective nodes := by
    intro k l hkl
    apply e.symm.injective
    apply Subtype.ext
    apply Fin.ext
    exact Nat.cast_injective hkl
  have sum_support (f : Fin N → ℝ) (hf : ∀ i, b i = 0 → f i = 0) :
      ∑ i : S, f i.val = ∑ i : Fin N, f i := by
    have ht := Fintype.sum_subtype_add_sum_subtype (fun i : Fin N => b i ≠ 0) f
    have hcomp : ∑ i : {i : Fin N // ¬ b i ≠ 0}, f i.val = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact hf i.val (not_not.mp i.property)
    simpa only [hcomp, add_zero] using ht
  intro j i hbi
  let amplitudes : Fin (Fintype.card S) → ℝ :=
    fun k => C j (e.symm k).val * b (e.symm k).val
  have hmoment :
      Analytic.GoldenTomography.FiniteVandermondeTomography.finiteMomentReadout nodes amplitudes =
        Analytic.GoldenTomography.FiniteVandermondeTomography.finiteMomentReadout nodes 0 := by
    ext k
    rw [Analytic.GoldenTomography.FiniteVandermondeTomography.finite_moment_readout_apply,
      Analytic.GoldenTomography.FiniteVandermondeTomography.finite_moment_readout_apply]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    change (∑ l, C j (e.symm l).val * b (e.symm l).val *
      ((e.symm l).val : ℝ) ^ (k : ℕ)) = 0
    rw [e.symm.sum_comp (fun l : S => C j l.val * b l.val * (l.val : ℝ) ^ (k : ℕ)),
      sum_support (fun l => C j l * b l * (l : ℝ) ^ (k : ℕ))
        (by intro l hl; simp [hl])]
    have hentry := congrArg (fun A : Matrix (Fin m) (Fin m) ℝ =>
      A j ⟨k.val, lt_trans k.isLt hcard⟩) hzero
    simpa only [weighted_apply, Matrix.zero_apply] using hentry
  have hamp := Analytic.GoldenTomography.FiniteVandermondeTomography.finite_moment_readout_injective
    hn hmoment
  have hval := congrFun hamp (e ⟨i, hbi⟩)
  have hprod : C j i * b i = 0 := by simpa [amplitudes] using hval
  exact (mul_eq_zero.mp hprod).resolve_right hbi

private lemma support_card_bound {m N : ℕ} (w : List Bool)
    (regime : false ∉ w ∨ ∃ n : ℕ, ∃ p q : List Bool,
      w = p ++ false :: q ∧ false ∉ p ∧ n = p.length + 1 ∧ N - n < m)
    (hm : 0 < m) :
    Fintype.card {i : Fin N // rows (w.take i) 1 - rows (w.take i) 0 ≠ 0} < m := by
  classical
  let b : Fin N → ℝ := fun i => rows (w.take i) 1 - rows (w.take i) 0
  change Fintype.card {i : Fin N // b i ≠ 0} < m
  have pure (v : List Bool) (hv : false ∉ v) (i : ℕ) :
      rows (v.take i) = fun _ => 1 :=
    (rows_invariant _).2.1 (fun hh => hv ((List.take_sublist i v).subset hh))
  rcases regime with hpure | ⟨n, p, q, rfl, hp, rfl, hshort⟩
  · have hb : ∀ i, b i = 0 := by
      intro i
      dsimp [b]
      rw [pure _ hpure]
      simp
    have he : IsEmpty {i : Fin N // b i ≠ 0} :=
      ⟨fun i => i.property (hb i.val)⟩
    haveI := he
    simpa using hm
  · have before (i : Fin N) (hi : i.val < p.length + 1) : b i = 0 := by
      dsimp [b]
      rw [List.take_append_of_le_length (by omega : i.val ≤ p.length), pure _ hp]
      simp
    let S := {i : Fin N // b i ≠ 0}
    let f : S → Fin (N - (p.length + 1)) := fun i =>
      ⟨i.val.val - (p.length + 1), by
        have hn : p.length + 1 ≤ i.val.val := by
          by_contra hlt
          exact i.property (before i.val (by omega))
        have := i.val.isLt
        omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      have hi : p.length + 1 ≤ i.val.val := by
        by_contra hlt
        exact i.property (before i.val (by omega))
      have hj : p.length + 1 ≤ j.val.val := by
        by_contra hlt
        exact j.property (before j.val (by omega))
      have he := congrArg Fin.val hij
      apply Subtype.ext
      apply Fin.ext
      dsimp [f] at he
      omega
    have hc := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hc
    exact lt_of_le_of_lt hc hshort

/-- A fixed linear map that is collinear throughout the original identical-row
family vanishes throughout that same family, for pure swaps or a short first-M suffix. -/
theorem short_suffix_annihilates
    (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (w : List Bool) (hw : w.length = N - 1)
    (C : Matrix (Fin (d + 1)) (Fin N) ℝ)
    (regime : false ∉ w ∨ ∃ n : ℕ, ∃ p q : List Bool,
      w = p ++ false :: q ∧ false ∉ p ∧ n = p.length + 1 ∧ N - n < d + 1)
    (h : ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ β : Fin (d + 1) → ℝ, β ≠ 0 → ∀ δ : ℝ,
      ∃ s : ℝ, C *ᵥ reads w θ β δ = s • β) :
    ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ β : Fin (d + 1) → ℝ, β ≠ 0 → ∀ δ : ℝ,
      C *ᵥ reads w θ β δ = 0 := by
  classical
  have hclock : w.length + 1 = N := by omega
  let u : Fin N → ℝ := fun i => rows (w.take i) 0
  let b : Fin N → ℝ := fun i => rows (w.take i) 1 - rows (w.take i) 0
  have hcard : Fintype.card {i : Fin N // b i ≠ 0} < d + 1 :=
    support_card_bound w regime (by omega)
  obtain ⟨hv, a, c, ha, hc⟩ := scalar_pencil (by omega : 2 ≤ d + 1) w C h
  change weighted C u = a • 1 at ha
  change weighted C b = c • 1 at hc
  obtain ⟨hc0, hcolumns⟩ := weighted_support C b hcard c hc
  have hu (i : Fin N) (hi : b i = 0) : u i = 1 := by
    have hp : false ∉ w.take i := by
      intro hh
      have hneq := (rows_invariant (w.take i)).2.2 hh
      apply hneq
      dsimp [b] at hi
      linarith
    have he := (rows_invariant (w.take i)).2.1 hp
    exact congrFun he 0
  have hterm (j : Fin (d + 1)) (i : Fin N) : C j i * u i = C j i := by
    by_cases hi : b i = 0
    · rw [hu i hi, mul_one]
    · rw [hcolumns j i hi]
      simp
  let j₀ : Fin (d + 1) := ⟨0, by omega⟩
  have ha0 : a = 0 := by
    have he := congrArg (fun A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => A j₀ j₀) ha
    simp only [weighted_apply, Matrix.smul_apply, smul_eq_mul] at he
    have hsum : (∑ i : Fin N, C j₀ i * u i * (i : ℝ) ^ (j₀ : ℕ)) = 0 := by
      simp only [j₀, pow_zero, mul_one, hterm]
      have hh := congrFun hv j₀
      simpa only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] using hh
    rw [hsum] at he
    simpa [j₀] using he.symm
  have hU : weighted C u = 0 := by simpa [ha0] using ha
  have hB : weighted C b = 0 := by simpa [hc0] using hc
  intro θ _ _ β _ δ
  rw [readout_matrix, hv, smul_zero, add_zero]
  have hmat : weighted C (fun i : Fin N => u i + θ * b i) = 0 := by
    ext j k
    have he : weighted C (fun i : Fin N => u i + θ * b i) j k =
        weighted C u j k + θ * weighted C b j k := by
      simp only [weighted_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, hU, hB]
    simp
  change weighted C (fun i : Fin N => u i + θ * b i) *ᵥ β = 0
  rw [hmat, Matrix.zero_mulVec]

#print axioms short_suffix_annihilates

end D5.S3.ConceptDynamics.Experiment.FibonacciGainRaySuffix
