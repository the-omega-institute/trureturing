/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGramClassification
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGramClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact dimension criteria for a positive scalar column Gram of a width-three tensor sum. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGram
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeThreeRectangularBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification

open QuantumMaxFlowBound (flow rank_le_QMaxFlow QMaxFlow_le_QMinCut)
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit (coordinateMatrix coordinate_gram)

/-- Dimension criteria for the empty source, two enlarging factors, and the two
orientations with a shrinking factor. -/
def ScalarGramAdmissible (a b c d : ℕ) : Prop :=
  b = 0 ∨ c = 0 ∨ (b ≤ a ∧ c ≤ d) ∨
    (a < b ∧
      ((2 * b ≤ 3 * a ∧ 3 * c ≤ 2 * d) ∨
        (3 * a < 2 * b ∧ b ≤ 2 * a ∧ 2 * c ≤ d) ∨
        (2 * a < b ∧ b ≤ 3 * a ∧ 3 * c ≤ d))) ∨
    (d < c ∧
      ((2 * c ≤ 3 * d ∧ 3 * b ≤ 2 * a) ∨
        (3 * d < 2 * c ∧ c ≤ 2 * d ∧ 2 * b ≤ a) ∨
        (2 * d < c ∧ c ≤ 3 * d ∧ 3 * b ≤ a)))

private theorem block_gram {a b c d k : ℕ} (hk : k ≤ 3)
    (hb : b ≤ k * a) (hd : k * c ≤ d) (lam : ℝ) (hlam : 0 < lam) :
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      (flow M N)ᴴ * flow M N = (lam : ℂ) • 1 := by
  let left : Fin b ↪ Fin k × Fin a :=
    (Fin.castLEEmb hb).trans finProdFinEquiv.symm.toEmbedding
  let right : Fin k × Fin c ↪ Fin d :=
    finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hd)
  let route : (Fin b × Fin c) ↪ (Fin a × Fin d) :=
    ⟨fun p => ((left p.1).2, right ((left p.1).1, p.2)), by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have hr := right.injective (congrArg Prod.snd h)
      have hl := left.injective (Prod.ext (congrArg Prod.fst hr) (congrArg Prod.fst h))
      exact Prod.ext hl (congrArg Prod.snd hr)⟩
  let M : Fin 3 → Matrix (Fin a) (Fin b) ℂ :=
    fun r i j => if r.val = (left j).1.val ∧ i = (left j).2 then 1 else 0
  let N : Fin 3 → Matrix (Fin d) (Fin c) ℂ :=
    fun r i j => if h : r.val < k then
      if right (⟨r.val, h⟩, j) = i then 1 else 0
    else 0
  have hroute : flow M N = coordinateMatrix route := by
    ext i j
    let r : Fin 3 := Fin.castLE hk (left j.1).1
    change (∑ t : Fin 3, M t i.1 j.1 * N t i.2 j.2) =
      if route j = i then 1 else 0
    rw [Finset.sum_eq_single r]
    · have hr : r.val < k := (left j.1).1.isLt
      have hcoord : (⟨r.val, hr⟩ : Fin k) = (left j.1).1 := Fin.ext rfl
      by_cases hleft : i.1 = (left j.1).2 <;>
        by_cases hright : right ((left j.1).1, j.2) = i.2 <;>
        simp [M, N, route, r, hcoord, Prod.ext_iff, hleft, eq_comm, hright]
    · intro t _ ht
      have hval : t.val ≠ (left j.1).1.val := fun h => ht (Fin.ext h)
      simp [M, hval]
    · simp
  refine ⟨fun r => (Real.sqrt lam : ℂ) • M r, N, ?_⟩
  have hscale : flow (fun r => (Real.sqrt lam : ℂ) • M r) N =
      (Real.sqrt lam : ℂ) • flow M N := by
    simp only [flow, Matrix.smul_kronecker, Finset.smul_sum]
  have hsquare : (Real.sqrt lam : ℂ) * (Real.sqrt lam : ℂ) = (lam : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hlam.le
  rw [hscale, hroute, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, coordinate_gram]
  simp only [Complex.star_def, Complex.conj_ofReal, hsquare]

private theorem swap_gram {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (z : ℂ)
    (h : (flow M N)ᴴ * flow M N = z • 1) :
    (flow N M)ᴴ * flow N M = z • 1 := by
  let rows := Equiv.prodComm (Fin d) (Fin a)
  let cols := Equiv.prodComm (Fin c) (Fin b)
  have heq : flow N M = (flow M N).submatrix rows cols := by
    ext i j
    change (∑ r : Fin 3, N r i.1 j.1 * M r i.2 j.2) =
      ∑ r : Fin 3, M r i.2 j.2 * N r i.1 j.1
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [heq, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ cols rows cols, h]
  ext i j
  simp [Matrix.submatrix, Matrix.one_apply, cols]

private theorem shrinking_left_bounds {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) {lam : ℝ} (hlam : 0 < lam)
    (hab : a < b) (hc : 0 < c)
    (h : (flow M N)ᴴ * flow M N = (lam : ℂ) • 1) :
    (2 * b ≤ 3 * a ∧ 3 * c ≤ 2 * d) ∨
      (3 * a < 2 * b ∧ b ≤ 2 * a ∧ 2 * c ≤ d) ∨
      (2 * a < b ∧ b ≤ 3 * a ∧ 3 * c ≤ d) := by
  by_cases hfirst : 2 * b ≤ 3 * a
  · exact Or.inl ⟨hfirst,
      NativeThreeRectangularBound.native_three_rectangular_bound M N lam hlam hab h⟩
  by_cases hsecond : b ≤ 2 * a
  · exact Or.inr (Or.inl ⟨by omega, hsecond,
      NativeRectangularBound.bound M N lam hlam (by omega) h⟩)
  have hr := (Matrix.rank_mul_le_right (flow M N)ᴴ (flow M N)).trans
    ((rank_le_QMaxFlow M N).trans (QMaxFlow_le_QMinCut a b c d))
  have hnonzero : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)
  rw [h, Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_iff_ne_zero.mpr hnonzero),
    Matrix.rank_one, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hr
  have hwidth : b * c ≤ (3 * a) * c := hr.trans (min_le_left _ _)
  exact Or.inr (Or.inr ⟨by omega, Nat.le_of_mul_le_mul_right hwidth hc,
    RestrictedFlatSpectrum.obstruction M N hc (by omega) lam hlam h⟩)

private theorem shrinking_left_construct {a b c d : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (h : (2 * b ≤ 3 * a ∧ 3 * c ≤ 2 * d) ∨
      (3 * a < 2 * b ∧ b ≤ 2 * a ∧ 2 * c ≤ d) ∨
      (2 * a < b ∧ b ≤ 3 * a ∧ 3 * c ≤ d)) :
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      (flow M N)ᴴ * flow M N = (lam : ℂ) • 1 := by
  rcases h with ⟨hb, hd⟩ | ⟨_, hb, hd⟩ | ⟨_, hb, hd⟩
  · exact NativeScalarGram.native_scalar_gram_exists a b c d hb hd lam hlam
  · exact block_gram (k := 2) (by decide) hb hd lam hlam
  · exact block_gram (k := 3) (by decide) hb hd lam hlam

private theorem empty_gram {a b c d : ℕ} [IsEmpty (Fin b × Fin c)] (lam : ℝ) :
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      (flow M N)ᴴ * flow M N = (lam : ℂ) • 1 :=
  ⟨0, 0, Subsingleton.elim _ _⟩

/-- The natural dimension conditions characterize every specified positive scalar column Gram. -/
theorem native_scalar_gram_iff (a b c d : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    (∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      (∑ r, kronecker (M r) (N r))ᴴ *
        (∑ r, kronecker (M r) (N r)) =
          (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)) ↔
      ScalarGramAdmissible a b c d := by
  change (∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      (flow M N)ᴴ * flow M N = (lam : ℂ) • 1) ↔ ScalarGramAdmissible a b c d
  constructor
  · rintro ⟨M, N, h⟩
    unfold ScalarGramAdmissible
    by_cases hb : b = 0
    · exact Or.inl hb
    by_cases hc : c = 0
    · exact Or.inr (Or.inl hc)
    by_cases hab : a < b
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hab, shrinking_left_bounds M N hlam hab (Nat.pos_of_ne_zero hc) h⟩)))
    by_cases hdc : d < c
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hdc, shrinking_left_bounds N M hlam hdc (Nat.pos_of_ne_zero hb) (swap_gram M N _ h)⟩)))
    exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · rintro (hb | hc | ⟨hb, hc⟩ | ⟨_, h⟩ | ⟨_, h⟩)
    · subst b
      exact empty_gram lam
    · subst c
      exact empty_gram lam
    · exact block_gram (k := 1) (by decide) (by simpa using hb) (by simpa using hc) lam hlam
    · exact shrinking_left_construct lam hlam h
    · obtain ⟨N, M, hgram⟩ := shrinking_left_construct lam hlam h
      exact ⟨M, N, swap_gram N M _ hgram⟩

example : (0 : ℝ) < 1 := by norm_num

example : Fin 3 → Matrix (Fin 2) (Fin 4) ℂ := 0

example : ScalarGramAdmissible 0 5 0 0 := Or.inr (Or.inl rfl)

end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGramClassification
