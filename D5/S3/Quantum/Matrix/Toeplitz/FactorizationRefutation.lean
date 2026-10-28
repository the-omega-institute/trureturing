/- GID: D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.claim; result=D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.result; claim=D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.claim
   digest: A common field obstructs uniformly short Toeplitz products modulo left units. -/

import D5.S3.Combinatorics.Matroids.LinearRado
import D5.S3.Weil.TestFunctions.LiCurvatureCriterion
import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Common fields of definition and graph row spaces for ordinary Toeplitz products. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Cardinal IntermediateField
open scoped BigOperators IntermediateField.algebraAdjoinAdjoin

namespace D5.S3.Quantum.Matrix.Toeplitz.FactorizationRefutation

/-- Equality on every pair of adjacent entries of an ordinary diagonal. -/
def IsOrdinaryToeplitz {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (i j : Fin n) (hi : i.val + 1 < n) (hj : j.val + 1 < n),
    T i j = T ⟨i.val + 1, hi⟩ ⟨j.val + 1, hj⟩

/-- The dimension-uniform single-left-multiplier assertion in Conjecture 5.1. -/
def claim : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
    ∀ M : Matrix (Fin n) (Fin n) ℂ,
      ∃ (P : Matrix (Fin n) (Fin n) ℂ)
        (T : Fin C → Matrix (Fin n) (Fin n) ℂ),
        IsUnit P ∧ (∀ k, IsOrdinaryToeplitz (T k)) ∧
          M = P * (List.ofFn T).prod

private lemma exists_independent (ι : Type) [Finite ι] :
    ∃ x : ι → ℂ, AlgebraicIndependent ℚ x := by
  classical
  have huncount : ¬ #ℂ ≤ ℵ₀ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum.not_ge
  have hna : ¬ Algebra.IsAlgebraic ℚ ℂ := by
    intro h
    let := h
    apply huncount
    exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ ℂ).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ ℂ
  have : Nonempty s := hs.nonempty_iff_transcendental.mpr
    (Algebra.transcendental_iff_not_isAlgebraic.mpr hna)
  have hcard : ℵ₀ ≤ #s := by
    by_contra h
    have hsmall : #s ≤ ℵ₀ := (lt_of_not_ge h).le
    have heq : #ℂ = max (max #ℚ #s) ℵ₀ := by
      simpa only [Cardinal.lift_id] using hs.lift_cardinalMk_eq_max_lift
    exact huncount (heq.trans_le (max_le (max_le Cardinal.mk_le_aleph0 hsmall) le_rfl))
  obtain ⟨f⟩ : Nonempty (ι ↪ s) := Cardinal.lift_mk_le'.mp (by
    simpa only [Cardinal.lift_id] using (Cardinal.mk_lt_aleph0 (α := ι)).le.trans hcard)
  exact ⟨fun i => (f i : ℂ), hs.1.comp f f.injective⟩

private lemma generated_field_trdeg {ι : Type} [Fintype ι] (g : ι → ℂ) :
    Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range g)) ≤ (Fintype.card ι : Cardinal) := by
  classical
  let K := IntermediateField.adjoin ℚ (Set.range g)
  let gK : ι → K := fun i => ⟨g i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  let J := IntermediateField.adjoin ℚ (Set.range gK)
  have hJ : J = ⊤ := by
    apply (IntermediateField.lift_injective K)
    change IntermediateField.lift (IntermediateField.adjoin ℚ (Set.range gK)) =
      IntermediateField.lift (⊤ : IntermediateField ℚ K)
    rw [IntermediateField.lift_adjoin]
    have himage : Subtype.val '' Set.range gK = Set.range g := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨gK i, ⟨i, rfl⟩, rfl⟩
    rw [himage]
    ext x
    simp only [K, IntermediateField.lift, IntermediateField.mem_map,
      IntermediateField.mem_top, true_and]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩
  let A := Algebra.adjoin ℚ (Set.range gK)
  let : Algebra.IsAlgebraic A K := ⟨fun x => by
    let y : J := ⟨x, by rw [hJ]; trivial⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := A) y).algHom
      (IsScalarTower.toAlgHom A J K)⟩
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ (Set.range gK)).trans
    (by simpa only [Cardinal.mk_fintype] using (Cardinal.mk_range_le (f := gK)))

private lemma entry_eq_boundary {n : ℕ} (hn : 0 < n)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : IsOrdinaryToeplitz T) (i j : Fin n) :
    T i j = if h : j.val ≤ i.val then
      T ⟨i.val - j.val, by omega⟩ ⟨0, hn⟩
    else T ⟨0, hn⟩ ⟨j.val - i.val, by omega⟩ := by
  obtain ⟨a, ha⟩ := i
  obtain ⟨b, hb⟩ := j
  induction a generalizing b with
  | zero =>
    by_cases h : b = 0
    · subst b; simp
    · simp [h]
  | succ a ih =>
    cases b with
    | zero => simp
    | succ b =>
      have he := hT ⟨a, by omega⟩ ⟨b, by omega⟩ ha hb
      rw [← he, ih (by omega) b (by omega)]
      simp only [Fin.val_mk, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

private lemma toeplitz_representation {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (hT : IsOrdinaryToeplitz T) :
    ∃ c : ℤ → ℂ,
      T = D5.S3.Weil.TestFunctions.LiCurvatureCriterion.toeplitzMatrix c N := by
  classical
  let c : ℤ → ℂ := fun d =>
    if h : d.toNat < N + 1 ∧ (-d).toNat < N + 1 then
      T ⟨d.toNat, h.1⟩ ⟨(-d).toNat, h.2⟩ else 0
  refine ⟨c, ?_⟩
  ext i j
  change T i j = c ((i.val : ℤ) - (j.val : ℤ))
  have hb : ((i.val : ℤ) - (j.val : ℤ)).toNat < N + 1 ∧
      (-((i.val : ℤ) - (j.val : ℤ))).toNat < N + 1 := by
    constructor <;> omega
  dsimp only [c]
  rw [dite_eq_left hb, entry_eq_boundary (by omega) T hT i j]
  split_ifs <;> congr 1 <;> apply Fin.ext <;> dsimp <;> omega

private lemma product_field {n C : ℕ} (hn : 0 < n)
    (T : Fin C → Matrix (Fin n) (Fin n) ℂ) (hT : ∀ k, IsOrdinaryToeplitz (T k)) :
    ∃ g : Fin C × Fin (2 * n - 1) → ℂ,
      ∀ i j, (List.ofFn T).prod i j ∈ IntermediateField.adjoin ℚ (Set.range g) := by
  classical
  cases n with
  | zero => omega
  | succ N =>
    choose c hc using fun k => toeplitz_representation (T k) (hT k)
    let g : Fin C × Fin (2 * (N + 1) - 1) → ℂ :=
      fun p => c p.1 ((p.2.val : ℤ) - N)
    let K := IntermediateField.adjoin ℚ (Set.range g)
    have ht (k : Fin C) (i j : Fin (N + 1)) : T k i j ∈ K := by
      rw [hc k]
      change c k ((i.val : ℤ) - j.val) ∈ K
      let d : Fin (2 * (N + 1) - 1) := ⟨i.val + N - j.val, by omega⟩
      apply IntermediateField.subset_adjoin ℚ _
      refine ⟨(k, d), ?_⟩
      dsimp [g, d]
      congr 1
      omega
    have hp : ∀ L : List (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ),
        (∀ A ∈ L, ∀ i j, A i j ∈ K) → ∀ i j, L.prod i j ∈ K := by
      intro L
      induction L with
      | nil =>
        intro _ i j
        simp only [List.prod_nil, Matrix.one_apply]
        split_ifs
        · exact K.one_mem
        · exact K.zero_mem
      | cons A L ih =>
        intro h i j
        simp only [List.prod_cons, Matrix.mul_apply]
        exact K.sum_mem fun k _ => K.mul_mem (h A (by simp) i k)
          (ih (fun B hB => h B (by simp [hB])) k j)
    refine ⟨g, hp _ ?_⟩
    intro A hA
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hA
    exact ht k

private def graphMatrix (r : ℕ) (X : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin (r + r)) (Fin (r + r)) ℂ :=
  (Matrix.fromBlocks 1 X 0 0).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

private lemma graph_mul_blocks (r : ℕ) (X : Matrix (Fin r) (Fin r) ℂ)
    (Q : Matrix (Fin (r + r)) (Fin (r + r)) ℂ) :
    (Q * graphMatrix r X).submatrix id (Fin.natAdd r) =
      (Q * graphMatrix r X).submatrix id (Fin.castAdd r) * X := by
  classical
  have hl (i : Fin (r + r)) (j : Fin r) :
      (Q * graphMatrix r X) i (Fin.castAdd r j) = Q i (Fin.castAdd r j) := by
    simp [Matrix.mul_apply, Fin.sum_univ_add, graphMatrix, Matrix.submatrix_apply,
      Matrix.one_apply, -Fin.natAdd_eq_addNat]
  ext i j
  change (Q * graphMatrix r X) i (Fin.natAdd r j) =
    ∑ k, (Q * graphMatrix r X) i (Fin.castAdd r k) * X k j
  simp_rw [hl]
  simp [Matrix.mul_apply, Fin.sum_univ_add, graphMatrix, Matrix.submatrix_apply,
      Matrix.one_apply, -Fin.natAdd_eq_addNat]

private lemma graph_coordinates_mem {r : ℕ} (X : Matrix (Fin r) (Fin r) ℂ)
    (P N : Matrix (Fin (r + r)) (Fin (r + r)) ℂ) (hP : IsUnit P)
    (hM : graphMatrix r X = P * N) (K : IntermediateField ℚ ℂ)
    (hN : ∀ i j, N i j ∈ K) : ∀ i j, X i j ∈ K := by
  classical
  let L : Fin r → Fin (r + r) := Fin.castAdd r
  let R : Fin r → Fin (r + r) := Fin.natAdd r
  have hleft : P.submatrix L id * N.submatrix id L = 1 := by
    have hm := Matrix.submatrix_mul_equiv P N L (Equiv.refl _) L
    change P.submatrix L id * N.submatrix id L = (P * N).submatrix L L at hm
    rw [hm, ← hM]
    ext i j
    simp [graphMatrix, L, Matrix.submatrix_apply]
  have hspan : Submodule.span ℂ (Set.range (N.submatrix id L).row) = ⊤ := by
    rw [← range_vecMulLinear, LinearMap.range_eq_top]
    intro u
    refine ⟨u ᵥ* P.submatrix L id, ?_⟩
    change (u ᵥ* P.submatrix L id) ᵥ* N.submatrix id L = u
    rw [Matrix.vecMul_vecMul, hleft, Matrix.vecMul_one]
  obtain ⟨f, _, hdet⟩ :=
    D5.S3.Combinatorics.Matroids.LinearRado.exists_nonsingular_rows (N.submatrix id L) hspan
  have hNM : N = P⁻¹ * graphMatrix r X := by
    rw [hM, Matrix.nonsing_inv_mul_cancel_left P N (P.isUnit_iff_isUnit_det.mp hP)]
  have hgraph : N.submatrix id R = N.submatrix id L * X := by
    simpa only [← hNM] using graph_mul_blocks r X P⁻¹
  let A : Matrix (Fin r) (Fin r) K := fun i j => ⟨N (f i) (L j), hN _ _⟩
  let B : Matrix (Fin r) (Fin r) K := fun i j => ⟨N (f i) (R j), hN _ _⟩
  let φ : K →+* ℂ := algebraMap K ℂ
  have hAdet : A.det ≠ 0 := by
    intro hz
    apply hdet
    change (A.map φ).det = 0
    have hm := φ.map_det A
    change φ A.det = (A.map φ).det at hm
    rw [← hm, hz, map_zero]
  have hAB : B.map φ = A.map φ * X := by
    ext i j
    exact congrFun (congrFun hgraph (f i)) j
  let Y := A⁻¹ * B
  have hY : Y.map φ = X := by
    apply ((Matrix.isUnit_iff_isUnit_det (A.map φ)).mpr
      (isUnit_iff_ne_zero.mpr (show (A.map φ).det ≠ 0 from hdet))).mul_left_cancel
    calc
      A.map φ * Y.map φ = (A * Y).map φ := Matrix.map_mul.symm
      _ = B.map φ := by
        dsimp only [Y]
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hAdet),
          Matrix.one_mul]
      _ = A.map φ * X := hAB
  intro i j
  rw [← hY]
  exact (Y i j).property

/-- No positive dimension-independent Toeplitz length works with one invertible left factor. -/
theorem result : ¬ claim := by
  classical
  rintro ⟨C, hC, hall⟩
  let r := 4 * C
  have hr : 0 < r + r := by dsimp [r]; omega
  obtain ⟨x, hx⟩ := exists_independent (Fin r × Fin r)
  let X : Matrix (Fin r) (Fin r) ℂ := fun i j => x (i, j)
  obtain ⟨P, T, hP, hT, hM⟩ := hall (r + r) hr (graphMatrix r X)
  obtain ⟨g, hg⟩ := product_field hr T hT
  let K := IntermediateField.adjoin ℚ (Set.range g)
  have hX : ∀ i j, X i j ∈ K :=
    graph_coordinates_mem X P (List.ofFn T).prod hP hM K hg
  let xK : Fin r × Fin r → K := fun p => ⟨x p, hX p.1 p.2⟩
  have hi : AlgebraicIndependent ℚ xK :=
    (K.val.algebraicIndependent_iff Subtype.val_injective).mp hx
  have hlow : (r * r : Cardinal) ≤ Algebra.trdeg ℚ K := by
    simpa only [Cardinal.mk_prod, Cardinal.mk_fin, Cardinal.lift_id] using hi.cardinalMk_le_trdeg
  have hup := generated_field_trdeg g
  simp only [Fintype.card_prod, Fintype.card_fin] at hup
  have hn : r * r ≤ C * (2 * (r + r) - 1) := by
    exact_mod_cast hlow.trans hup
  have he : 2 * (r + r) - 1 + 1 = 4 * r := by omega
  have hgap : C * (2 * (r + r) - 1) + C = r * r := by
    calc
      _ = C * (2 * (r + r) - 1 + 1) := by ring
      _ = C * (4 * r) := by rw [he]
      _ = r * r := by dsimp [r]; ring
  omega

#check graphMatrix
#check claim
#check result
#print axioms result

end D5.S3.Quantum.Matrix.Toeplitz.FactorizationRefutation
