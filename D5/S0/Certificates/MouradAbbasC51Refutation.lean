/- GID: D5/S0/Certificates/MouradAbbasC51Refutation
   generality: G
   mirror-B: D5/B/S0/Certificates/MouradAbbasC51Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/MouradAbbasC51Refutation.claim; result=D5/S0/Certificates/MouradAbbasC51Refutation.result; claim=D5/S0/Certificates/MouradAbbasC51Refutation.claim
   digest: Positive-trace uniform blocks refute Mourad–Abbas Conjecture 5.1. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#21726; Refuted)
  Direct frozen dependencies: none.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The source uses real matrices, ordinary similarity, the full symmetric
polytope's extreme points, and closed segments. Matrix and doublyStochastic
are used directly rather than introducing aliases. The source definitions
needed by claim retain their defining expressions.
positive_edge_rows_equal: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: projection_support_mass, uniform_projection, partition_coordinates.
projection_support_mass: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: uniform_projection.
uniform_projection: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: similar_family_rigidity.
partition_coordinates: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: similar_family_rigidity.
block_projection_properties: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: family_properties, similar_family_rigidity.
family_scalar_bounds: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: family_properties, similar_family_rigidity, family_exclusion, family_trace_slice.
family_properties: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: family_isDS, family_exclusion, family_trace_slice.
similar_family_rigidity: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: family_isDS.
family_permutation: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: family_isDS.
family_isDS: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: result.
four_cycle_not_extreme: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: segment_exclusion.
segment_exclusion: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: family_exclusion.
family_exclusion: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: result.
family_trace_slice: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: result.
All helper classifications expand same-module dependencies and stop at
pinned Mathlib. No independent mathematical-content admission is asserted.
-/

import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Extreme

namespace D5.S0.Certificates.MouradAbbasC51Refutation


/-- The symmetric elements Δ_n^s of the full doubly stochastic polytope. -/
def DeltaSymm (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A ∈ (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)) ∧ A.IsSymm}

/-- The trace-a slice Δ_n^s(a). -/
def traceSlice (n : ℕ) (a : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A ∈ DeltaSymm n ∧ Matrix.trace A = a}

/-- C_n is used only at n ≥ 2 in claim. -/
noncomputable def C (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else 1 / ((n : ℝ) - 1)

/-- B = Pᵀ A P for a permutation matrix P. -/
def IsPermutationallySimilar {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    B = (σ.permMatrix ℝ).transpose * A * σ.permMatrix ℝ

/-- IsConj on the matrix monoid is ordinary similarity by an invertible real matrix. -/
def IsDS {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A ∈ DeltaSymm n ∧
    ∀ B : Matrix (Fin n) (Fin n) ℝ, B ∈ DeltaSymm n → IsConj A B → IsPermutationallySimilar A B

/-- Conjecture 5.1: every DS matrix in a positive-trace slice lies on a listed segment. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ a : ℝ, 0 < a → a ≤ (n : ℝ) →
      ∀ A : Matrix (Fin n) (Fin n) ℝ, A ∈ traceSlice n a → IsDS A →
        (A ∈ segment ℝ (1 : Matrix (Fin n) (Fin n) ℝ) (C n) ∨
          ∃ P : Matrix (Fin n) (Fin n) ℝ, P ∈ (DeltaSymm n).extremePoints ℝ ∧
            (A ∈ segment ℝ (1 : Matrix (Fin n) (Fin n) ℝ) P ∨ A ∈ segment ℝ (C n) P))

end D5.S0.Certificates.MouradAbbasC51Refutation

namespace D5.S0.Certificates.MouradAbbasC51Refutation
open Finset Matrix
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

private theorem positive_edge_rows_equal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℝ) (hE : E ∈ doublyStochastic ℝ ι)
    (hid : E * E = E) {i j : ι} (hij : 0 < E i j) : E i = E j := by
  have hrow := (mem_doublyStochastic_iff_sum.mp hE).2.1
  have hcol := (mem_doublyStochastic_iff_sum.mp hE).2.2
  have hmul (i k : ι) : ∑ j, E i j * E j k = E i k := congrFun (congrFun hid i) k
  have hvar (i k : ι) :
      ∑ j, E i j * (E j k - E i k)^2 =
        (∑ j, E i j * (E j k)^2) - (E i k)^2 := by
    calc
      _ = (∑ j, E i j * (E j k)^2) -
          2 * E i k * (∑ j, E i j * E j k) +
          (E i k)^2 * (∑ j, E i j) := by
        simp_rw [sub_sq, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
        congr 1
        · congr 1
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
        · rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
      _ = _ := by rw [hmul, hrow]; ring
  have htotal (k : ι) : ∑ i, ∑ j, E i j * (E j k - E i k)^2 = 0 := by
    simp_rw [hvar, sum_sub_distrib]
    rw [sum_comm]
    simp_rw [← sum_mul, hcol, one_mul]
    exact sub_self _
  funext k
  have hz := (sum_eq_zero_iff_of_nonneg (fun i _ =>
    sum_nonneg (fun j _ => mul_nonneg (hE.1 i j) (sq_nonneg _)))).mp (htotal k)
  have hz' := (sum_eq_zero_iff_of_nonneg (fun j _ =>
    mul_nonneg (hE.1 i j) (sq_nonneg _))).mp (hz i (mem_univ _)) j (mem_univ _)
  have hs : (E j k - E i k)^2 = 0 := (mul_eq_zero.mp hz').resolve_left (ne_of_gt hij)
  have : E j k - E i k = 0 := sq_eq_zero_iff.mp hs
  linarith


private theorem projection_support_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℝ) (hE : E ∈ doublyStochastic ℝ ι)
    (hsymm : E.IsSymm) (hid : E * E = E) (i : ι) :
    ((univ.filter fun j => 0 < E i j).card : ℝ) * E i i = 1 := by
  classical
  calc
    _ = ∑ j ∈ univ.filter (fun j => 0 < E i j), E i i := by simp
    _ = ∑ j, E i j := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j _
      split_ifs with h
      · have he := congrFun (positive_edge_rows_equal E hE hid h) i
        have hs : E j i = E i j := hsymm.apply i j
        linarith
      · exact (le_antisymm (not_lt.mp h) (hE.1 i j)).symm
    _ = 1 := sum_row_of_mem_doublyStochastic hE i

private theorem uniform_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℝ) (hE : E ∈ doublyStochastic ℝ ι)
    (hsymm : E.IsSymm) (hid : E * E = E) (hpos : ∀ i, 0 < E i i)
    (k : ℕ) (hk : 0 < k) (lam : ℝ) (hlam : lam < 0)
    (hsize : 1 + (k : ℝ) * lam < 0)
    (hdiag : ∀ i, 0 ≤ lam + (1-lam) * E i i)
    (htrace : (k : ℝ) * Matrix.trace E = Fintype.card ι) :
    (∀ i, (univ.filter fun j => 0 < E i j).card = k) ∧
    (∀ i j, E i j = if 0 < E i j then 1 / (k : ℝ) else 0) := by
  classical
  let m : ι → ℕ := fun i => (univ.filter fun j => 0 < E i j).card
  have hmass (i : ι) : (m i : ℝ) * E i i = 1 :=
    projection_support_mass E hE hsymm hid i
  have hmle (i : ι) : m i ≤ k := by
    by_contra h
    have hm : (k : ℝ) + 1 ≤ (m i : ℝ) := by exact_mod_cast (show k+1 ≤ m i by omega)
    have hmp : 0 ≤ (m i : ℝ) := Nat.cast_nonneg _
    have hd := hdiag i
    have hp := hpos i
    have he := hmass i
    have hx : (m i : ℝ) * (lam + (1-lam) * E i i) = (m i : ℝ)*lam + 1-lam := by
      calc
        _ = (m i : ℝ)*lam + (1-lam)*((m i : ℝ)*E i i) := by ring
        _ = _ := by rw [he]; ring
    have hn := mul_nonneg hmp hd
    rw [hx] at hn
    have hn' := mul_le_mul_of_nonpos_right hm hlam.le
    nlinarith
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hdle (i : ι) : 1 ≤ (k : ℝ) * E i i := by
    have hc : (m i : ℝ) ≤ k := by exact Nat.cast_le.mpr (hmle i)
    nlinarith [mul_le_mul_of_nonneg_right hc (hpos i).le, hmass i]
  have hsum : ∑ i, ((k : ℝ) * E i i - 1) = 0 := by
    rw [sum_sub_distrib, ← mul_sum]
    simpa [Matrix.trace, Matrix.diag] using sub_eq_zero.mpr htrace
  have hdeq (i : ι) : (k : ℝ)*E i i = 1 := by
    have := (sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hdle j))).mp hsum i (mem_univ i)
    linarith
  constructor
  · intro i
    change m i = k
    have := hdeq i
    have := hmass i
    have : (m i : ℝ) = (k : ℝ) := by nlinarith [hpos i]
    exact_mod_cast this
  · intro i j
    split_ifs with h
    · have he := congrFun (positive_edge_rows_equal E hE hid h) i
      have hs : E j i = E i j := hsymm.apply i j
      have hd := hdeq i
      apply (eq_div_iff (ne_of_gt hkpos)).mpr
      nlinarith
    · exact le_antisymm (not_lt.mp h) (hE.1 i j)


private theorem partition_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℝ) (hE : E ∈ doublyStochastic ℝ ι)
    (hid : E * E = E) (hpos : ∀ i, 0 < E i i)
    (k r : ℕ) (hk : 0 < k) (hn : Fintype.card ι = r*k)
    (hcard : ∀ i, (univ.filter fun j => 0 < E i j).card = k) :
    ∃ e : ι ≃ Fin r × Fin k, ∀ i j, (e i).1 = (e j).1 ↔ 0 < E i j := by
  classical
  let s : Setoid ι := ⟨fun i j => E i = E j, ⟨fun _ => rfl, fun h => h.symm, fun h g => h.trans g⟩⟩
  let q : ι → Quotient s := Quotient.mk s
  letI : Fintype (Quotient s) := Fintype.ofFinite _
  have hrel (i j : ι) : q i = q j ↔ 0 < E i j := by
    constructor
    · intro h
      have he : E i = E j := Quotient.exact h
      simpa only [congrFun he j] using hpos j
    · intro h
      exact Quotient.sound (positive_edge_rows_equal E hE hid h)
  have hc (c : Quotient s) : Fintype.card {i // q i = c} = k := by
    induction c using Quotient.inductionOn with
    | h i =>
      rw [Fintype.card_subtype]
      convert hcard i using 1
      congr 1
      ext j
      simp only [mem_filter, mem_univ, true_and]
      rw [eq_comm, hrel]
  let e0 : ι ≃ Quotient s × Fin k :=
    (Equiv.sigmaFiberEquiv q).symm.trans
      (Equiv.sigmaEquivProdOfEquiv fun c => Fintype.equivFinOfCardEq (hc c))
  have he0 (i : ι) : (e0 i).1 = q i := rfl
  have hqc : Fintype.card (Quotient s) = r := by
    have h := Fintype.card_congr e0
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.eq_of_mul_eq_mul_right hk (h.symm.trans hn)
  let eqc := Fintype.equivFinOfCardEq hqc
  refine ⟨e0.trans (Equiv.prodCongr eqc (Equiv.refl _)), ?_⟩
  intro i j
  change eqc (e0 i).1 = eqc (e0 j).1 ↔ _
  rw [eqc.injective.eq_iff, he0, he0, hrel]


private noncomputable def blockProjection {ι : Type*} (k r : ℕ) (e : ι ≃ Fin r × Fin k) : Matrix ι ι ℝ :=
  (Matrix.blockDiagonal (fun _ : Fin r => fun _ _ : Fin k => (1 / (k : ℝ)))).submatrix
    (Prod.swap ∘ e) (Prod.swap ∘ e)

private theorem block_projection_properties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k r : ℕ) (hk : 0 < k) (e : ι ≃ Fin r × Fin k) :
    blockProjection k r e ∈ doublyStochastic ℝ ι ∧
    (blockProjection k r e).IsSymm ∧
    blockProjection k r e * blockProjection k r e = blockProjection k r e ∧
    Matrix.trace (blockProjection k r e) = (r : ℝ) := by
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
  have hr (i : ι) : ∑ j, blockProjection k r e i j = 1 := by
    rw [← e.symm.sum_comp]
    simp only [blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, Equiv.apply_symm_apply, Fintype.sum_prod_type]
    have hi (a : Fin r) : (∑ b : Fin k, if (e i).1 = a then 1/(k : ℝ) else 0) =
        if (e i).1 = a then 1 else 0 := by
      split_ifs <;> simp [Finset.sum_const, hkne]
    simp_rw [hi]
    simp
  have hs : (blockProjection k r e).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, eq_comm]
  refine ⟨mem_doublyStochastic_iff_sum.mpr ⟨?_, hr, ?_⟩, hs, ?_, ?_⟩
  · intro i j
    simp only [blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap]
    split_ifs <;> positivity
  · intro j
    convert hr j using 1
    apply sum_congr rfl
    intro i _
    exact hs.apply j i
  · ext i j
    change (∑ l, blockProjection k r e i l * blockProjection k r e l j) = _
    calc
      _ = ∑ l, blockProjection k r e i l * blockProjection k r e i j := by
        apply sum_congr rfl
        intro l _
        by_cases h : (e i).1 = (e l).1
        · simp only [blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, ← h]
        · simp [blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, h]
      _ = _ := by rw [← sum_mul, hr, one_mul]
  · have hc : Fintype.card ι = r*k := by simpa using Fintype.card_congr e
    simp [Matrix.trace, Matrix.diag, blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, hc, Nat.cast_mul, hkne]

private noncomputable def familyLambda (k : ℕ) (t : ℝ) : ℝ := ((k : ℝ)*t-1)/((k : ℝ)-1)

private noncomputable def familyMatrix {ι : Type*} [DecidableEq ι]
    (k r : ℕ) (e : ι ≃ Fin r × Fin k) (t : ℝ) : Matrix ι ι ℝ :=
  familyLambda k t • 1 + (1-familyLambda k t) • blockProjection k r e

private theorem family_scalar_bounds (k : ℕ) (hk : 4 ≤ k) (t : ℝ)
    (ht : 0 < t) (htu : t < 1/(k : ℝ)^2) :
    familyLambda k t < 0 ∧ 0 < 1-familyLambda k t ∧
    1+(k : ℝ)*familyLambda k t < 0 ∧
    familyLambda k t + (1-familyLambda k t)/(k : ℝ) = t ∧
    (1-familyLambda k t)/(k : ℝ) = (1-t)/((k : ℝ)-1) ∧ t < 1 := by
  have hk4 : (4 : ℝ) ≤ k := by exact Nat.ofNat_le_cast.mpr hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkm : (0 : ℝ) < (k : ℝ)-1 := by linarith
  have ht' : t * (k : ℝ)^2 < 1 := (lt_div_iff₀ (sq_pos_of_pos hk0)).mp htu
  have htl : t < 1 := by nlinarith
  have hlam : familyLambda k t < 0 := by
    rw [familyLambda, div_lt_iff₀ hkm]
    nlinarith
  have heq : familyLambda k t * ((k : ℝ)-1) = (k : ℝ)*t-1 := by
    exact div_mul_cancel₀ _ (ne_of_gt hkm)
  refine ⟨hlam, by linarith, ?_, ?_, ?_, htl⟩
  · nlinarith
  · have hcan : (1-familyLambda k t)/(k : ℝ) * (k : ℝ) = 1-familyLambda k t :=
      div_mul_cancel₀ _ (ne_of_gt hk0)
    nlinarith
  · apply (div_eq_div_iff (ne_of_gt hk0) (ne_of_gt hkm)).mpr
    nlinarith

private theorem family_properties {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k r : ℕ) (hk : 4 ≤ k) (e : ι ≃ Fin r × Fin k)
    (t : ℝ) (ht : 0 < t) (htu : t < 1/(k : ℝ)^2) :
    familyMatrix k r e t ∈ doublyStochastic ℝ ι ∧
    (familyMatrix k r e t).IsSymm ∧
    (∀ i, familyMatrix k r e t i i = t) := by
  classical
  obtain ⟨hE, hsE, hidE, htrE⟩ := block_projection_properties k r (by omega) e
  obtain ⟨hlam, hscale, hsize, hdiag, hoff, ht1⟩ := family_scalar_bounds k hk t ht htu
  have hd (i : ι) : familyMatrix k r e t i i = t := by
    simpa [familyMatrix, blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, div_eq_mul_inv, mul_comm] using hdiag
  have hs : (familyMatrix k r e t).IsSymm := by
    exact (Matrix.isSymm_one.smul (familyLambda k t)).add (hsE.smul (1-familyLambda k t))
  refine ⟨mem_doublyStochastic_iff_sum.mpr ⟨?_, ?_, ?_⟩, hs, hd⟩
  · intro i j
    by_cases h : i = j
    · subst j; exact (hd i).symm ▸ ht.le
    · simp only [familyMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_ne h, mul_zero, zero_add]
      exact mul_nonneg hscale.le (hE.1 i j)
  · intro i
    simp only [familyMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      sum_add_distrib, ← mul_sum]
    simp [Matrix.one_apply, sum_row_of_mem_doublyStochastic hE i]
  · intro j
    have hr : ∑ i, familyMatrix k r e t j i = 1 := by
      simp only [familyMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        sum_add_distrib, ← mul_sum]
      simp [Matrix.one_apply, sum_row_of_mem_doublyStochastic hE j]
    convert hr using 1
    apply sum_congr rfl
    intro i _
    exact hs.apply j i


private theorem similar_family_rigidity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k r : ℕ) (hk : 4 ≤ k) (e : ι ≃ Fin r × Fin k)
    (t : ℝ) (ht : 0 < t) (htu : t < 1/(k : ℝ)^2)
    (B : Matrix ι ι ℝ) (hB : B ∈ doublyStochastic ℝ ι) (hsB : B.IsSymm)
    (hsim : IsConj (familyMatrix k r e t) B) :
    ∃ f : ι ≃ Fin r × Fin k, B = familyMatrix k r f t := by
  classical
  let lam := familyLambda k t
  let E := (1-lam)⁻¹ • (B-lam • (1 : Matrix ι ι ℝ))
  obtain ⟨hlam, hscale, hsize, hdiag, hoff, ht1⟩ := family_scalar_bounds k hk t ht htu
  change lam < 0 at hlam
  change 0 < 1-lam at hscale
  change 1+(k : ℝ)*lam < 0 at hsize
  have hsn : 1-lam ≠ 0 := ne_of_gt hscale
  obtain ⟨hEA, hsEA, hidEA, htrEA⟩ := block_projection_properties k r (by omega) e
  rcases hsim with ⟨u, hu⟩
  have hbconj : B = (u : Matrix ι ι ℝ) * familyMatrix k r e t * (↑(u⁻¹) : Matrix ι ι ℝ) := by
    calc
      _ = B * ((↑u : Matrix ι ι ℝ) * (↑(u⁻¹) : Matrix ι ι ℝ)) := by simp
      _ = B * (↑u : Matrix ι ι ℝ) * (↑(u⁻¹) : Matrix ι ι ℝ) := by rw [mul_assoc]
      _ = _ := by rw [← hu]
  have heconj : E = (u : Matrix ι ι ℝ) * blockProjection k r e * (↑(u⁻¹) : Matrix ι ι ℝ) := by
    dsimp [E]
    rw [hbconj]
    simp [familyMatrix, lam, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc,
      inv_smul_smul₀ (ne_of_gt hscale)]
  have heid : E * E = E := by
    rw [heconj]
    calc
      _ = (u : Matrix ι ι ℝ) * (blockProjection k r e * blockProjection k r e) * (↑(u⁻¹) : Matrix ι ι ℝ) := by
        simp [mul_assoc]
      _ = _ := by rw [hidEA]
  have hetrace : Matrix.trace E = r := by
    rw [heconj, Matrix.trace_units_conj, htrEA]
  have heapply (i j : ι) : E i j = (B i j-lam*(1 : Matrix ι ι ℝ) i j)/(1-lam) := by
    simp [E, div_eq_mul_inv, mul_comm]
  have hediag (i : ι) : E i i = (B i i-lam)/(1-lam) := by simp [heapply]
  have hepos (i : ι) : 0 < E i i := by
    rw [hediag]
    exact div_pos (by linarith [hB.1 i i]) hscale
  have hesymm : E.IsSymm := by
    exact (hsB.sub (Matrix.isSymm_one.smul lam)).smul ((1-lam)⁻¹)
  have herow (i : ι) : ∑ j, E i j = 1 := by
    simp_rw [heapply, div_eq_mul_inv, sub_mul, sum_sub_distrib, ← sum_mul, ← mul_sum]
    rw [sum_row_of_mem_doublyStochastic hB i]
    simp [Matrix.one_apply, hsn] <;> field_simp <;> ring
  have heDS : E ∈ doublyStochastic ℝ ι := by
    refine mem_doublyStochastic_iff_sum.mpr ⟨?_, herow, ?_⟩
    · intro i j
      by_cases h : i = j
      · subst j; exact (hepos i).le
      · rw [heapply, Matrix.one_apply_ne h, mul_zero, sub_zero]
        exact div_nonneg (hB.1 i j) hscale.le
    · intro j
      convert herow j using 1
      apply sum_congr rfl
      intro i _
      exact hesymm.apply j i
  have henonneg (i : ι) : 0 ≤ lam+(1-lam)*E i i := by
    rw [hediag, mul_div_cancel₀ _ hsn]
    linarith [hB.1 i i]
  have hn : Fintype.card ι = r*k := by simpa using Fintype.card_congr e
  have hecount : (k : ℝ) * Matrix.trace E = Fintype.card ι := by
    rw [hetrace, hn, Nat.cast_mul]; ring
  obtain ⟨hcard, hentry⟩ := uniform_projection E heDS hesymm heid hepos k (by omega) lam hlam hsize henonneg hecount
  obtain ⟨f, hf⟩ := partition_coordinates E heDS heid hepos k r (by omega) hn hcard
  have hef : E = blockProjection k r f := by
    ext i j
    rw [hentry]
    simp only [blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, hf]
  refine ⟨f, ?_⟩
  ext i j
  have hij := congrFun (congrFun hef i) j
  rw [heapply] at hij
  have hij' := (div_eq_iff hsn).mp hij
  simp only [familyMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  change B i j = lam*(1 : Matrix ι ι ℝ) i j + (1-lam)*blockProjection k r f i j
  nlinarith


private theorem family_permutation {n k r : ℕ}
    (e f : Fin n ≃ Fin r × Fin k) (t : ℝ) :
    IsPermutationallySimilar (familyMatrix k r e t) (familyMatrix k r f t) := by
  let σ : Equiv.Perm (Fin n) := e.trans f.symm
  refine ⟨σ, ?_⟩
  change familyMatrix k r f t =
    σ.toPEquiv.toMatrix.transpose * familyMatrix k r e t * σ.toPEquiv.toMatrix
  rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [familyMatrix, blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, Matrix.submatrix_apply, Matrix.one_apply, σ,
    Equiv.apply_eq_iff_eq]

private theorem family_isDS (k r : ℕ) (hk : 4 ≤ k)
    (e : Fin (r*k) ≃ Fin r × Fin k) (t : ℝ)
    (ht : 0 < t) (htu : t < 1/(k : ℝ)^2) :
    IsDS (familyMatrix k r e t) := by
  obtain ⟨hA, hsA, hdiag⟩ := family_properties k r hk e t ht htu
  refine ⟨⟨hA, hsA⟩, ?_⟩
  intro B hB hs
  obtain ⟨f, hf⟩ := similar_family_rigidity k r hk e t ht htu B hB.1 hB.2 hs
  rw [hf]
  exact family_permutation e f t

private theorem four_cycle_not_extreme {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ DeltaSymm n) (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (w : ℝ) (hw : 0 < w)
    (h1 : M a b = w) (h2 : M b c = w) (h3 : M c d = w) (h4 : M d a = w) :
    M ∉ (DeltaSymm n).extremePoints ℝ := by
  classical
  let u : Fin n → ℝ := Pi.single a 1 - Pi.single c 1
  let v : Fin n → ℝ := Pi.single b 1 - Pi.single d 1
  let H : Matrix (Fin n) (Fin n) ℝ := (w/2) • (vecMulVec u v + vecMulVec v u)
  have hsu : ∑ i, u i = 0 := by simp [u, sum_sub_distrib]
  have hsv : ∑ i, v i = 0 := by simp [v, sum_sub_distrib]
  have hsH : H.IsSymm := by
    dsimp only [H]
    apply Matrix.IsSymm.smul
    simpa only [Matrix.transpose_vecMulVec] using Matrix.isSymm_add_transpose_self (vecMulVec u v)
  have hrH (i : Fin n) : ∑ j, H i j = 0 := by
    simp [H, vecMulVec, mul_add, sum_add_distrib, ← mul_sum, hsu, hsv]
  have hcH (j : Fin n) : ∑ i, H i j = 0 := by
    convert hrH j using 1
    apply sum_congr rfl
    intro i _
    exact hsH.apply j i
  have hba : M b a = w := (hM.2.apply a b).trans h1
  have hcb : M c b = w := (hM.2.apply b c).trans h2
  have hdc : M d c = w := (hM.2.apply c d).trans h3
  have had' : M a d = w := (hM.2.apply d a).trans h4
  have hnn (i j : Fin n) : 0 ≤ M i j + H i j ∧ 0 ≤ M i j - H i j := by
    have h0 := hM.1.1 i j
    have hi : i=a ∨ i=b ∨ i=c ∨ i=d ∨ (i≠a ∧ i≠b ∧ i≠c ∧ i≠d) := by tauto
    have hj : j=a ∨ j=b ∨ j=c ∨ j=d ∨ (j≠a ∧ j≠b ∧ j≠c ∧ j≠d) := by tauto
    clear hcH hrH hsH hsu hsv
    simp only [H, u, v, vecMulVec, Matrix.smul_apply, Matrix.add_apply,
      Matrix.of_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply]
    clear H u v
    rcases hi with rfl | rfl | rfl | rfl | ⟨hia, hib, hic, hid⟩ <;>
      rcases hj with rfl | rfl | rfl | rfl | ⟨hja, hjb, hjc, hjd⟩ <;>
      simp_all [eq_comm] <;> (try constructor) <;> linarith
  have hp : M + H ∈ DeltaSymm n := by
    refine ⟨mem_doublyStochastic_iff_sum.mpr ⟨fun i j => (hnn i j).1, ?_, ?_⟩, ?_⟩
    · intro i
      simp only [Matrix.add_apply, sum_add_distrib]
      rw [sum_row_of_mem_doublyStochastic hM.1 i, hrH, add_zero]
    · intro j
      simp only [Matrix.add_apply, sum_add_distrib]
      rw [sum_col_of_mem_doublyStochastic hM.1 j, hcH, add_zero]
    · exact hM.2.add hsH
  have hm : M - H ∈ DeltaSymm n := by
    refine ⟨mem_doublyStochastic_iff_sum.mpr ⟨fun i j => (hnn i j).2, ?_, ?_⟩, ?_⟩
    · intro i
      simp only [Matrix.sub_apply, sum_sub_distrib]
      rw [sum_row_of_mem_doublyStochastic hM.1 i, hrH, sub_zero]
    · intro j
      simp only [Matrix.sub_apply, sum_sub_distrib]
      rw [sum_col_of_mem_doublyStochastic hM.1 j, hcH, sub_zero]
    · exact hM.2.sub hsH
  intro hext
  have he := hext.2 hp hm (mem_openSegment_add_sub (𝕜 := ℝ) M H)
  have hab' := congrFun (congrFun he a) b
  have hH : H a b = w/2 := by simp [H,u,v,vecMulVec,Pi.single_apply,hab,hac,had,hbc,hbd,hcd,Ne.symm,eq_comm]
  change M a b + H a b = M a b at hab'
  rw [hH] at hab'
  linarith


private theorem segment_exclusion {n : ℕ} (hn : 2 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ DeltaSymm n) (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (w : ℝ) (hw : 0 < w)
    (h1 : M a b = w) (h2 : M b c = w) (h3 : M c d = w) (h4 : M d a = w)
    (x y : Fin n) (hxy : x ≠ y) (hz : M x y = 0) :
    M ∉ segment ℝ (1 : Matrix (Fin n) (Fin n) ℝ) (C n) ∧
    ∀ P ∈ (DeltaSymm n).extremePoints ℝ,
      M ∉ segment ℝ (1 : Matrix (Fin n) (Fin n) ℝ) P ∧ M ∉ segment ℝ (C n) P := by
  have hn' : (0 : ℝ) < (n : ℝ)-1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hCpos : 0 < ((n : ℝ)-1)⁻¹ := inv_pos.mpr hn'
  have hnot := four_cycle_not_extreme M hM a b c d hab hac had hbc hbd hcd w hw h1 h2 h3 h4
  constructor
  · rintro ⟨u,v,hu,hv,huv,he⟩
    have hexy := congrFun (congrFun he x) y
    have heab := congrFun (congrFun he a) b
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, C, hxy, hz] at hexy
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, C, hab, h1] at heab
    rcases hexy with hv0 | hn0
    · rw [hv0] at heab; linarith
    · linarith
  · intro P hext
    have hP : P ∈ DeltaSymm n := hext.1
    constructor
    · rintro ⟨u,v,hu,hv,huv,he⟩
      have hev (i j : Fin n) (hij : i≠j) : v * P i j = M i j := by
        have h := congrFun (congrFun he i) j
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hij] using h
      have hvp : 0 < v := by
        have hvab := hev a b hab
        rw [h1] at hvab
        nlinarith [hP.1.1 a b]
      have hpedge (i j : Fin n) (hij : i≠j) (hijw : M i j=w) : P i j = w/v := by
        apply (eq_div_iff (ne_of_gt hvp)).mpr
        nlinarith [hev i j hij]
      exact (four_cycle_not_extreme P hP a b c d hab hac had hbc hbd hcd
        (w/v) (div_pos hw hvp)
        (hpedge a b hab h1) (hpedge b c hbc h2) (hpedge c d hcd h3)
        (hpedge d a had.symm h4)) hext
    · rintro ⟨u,v,hu,hv,huv,he⟩
      have hexy := congrFun (congrFun he x) y
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, C, hxy, hz] at hexy
      have hzv : 0 ≤ v * P x y := mul_nonneg hv (hP.1.1 x y)
      have hu0 : u=0 := by
        by_contra h
        have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm h)
        have hprod := mul_pos hup hCpos
        linarith
      have hv1 : v=1 := by linarith
      have hp : P=M := by simpa [hu0,hv1] using he
      exact hnot (hp ▸ hext)


private theorem family_exclusion (k r : ℕ) (hk : 4 ≤ k) (hr : 2 ≤ r)
    (e : Fin (r*k) ≃ Fin r × Fin k) (t : ℝ)
    (ht : 0 < t) (htu : t < 1/(k : ℝ)^2) :
    familyMatrix k r e t ∉ segment ℝ (1 : Matrix (Fin (r*k)) (Fin (r*k)) ℝ) (C (r*k)) ∧
    ∀ P ∈ (DeltaSymm (r*k)).extremePoints ℝ,
      familyMatrix k r e t ∉ segment ℝ (1 : Matrix (Fin (r*k)) (Fin (r*k)) ℝ) P ∧
      familyMatrix k r e t ∉ segment ℝ (C (r*k)) P := by
  classical
  obtain ⟨hA, hsA, hdiag⟩ := family_properties k r hk e t ht htu
  obtain ⟨hlam, hscale, hsize, hdiagt, hoff, ht1⟩ := family_scalar_bounds k hk t ht htu
  let v : Fin 4 → Fin (r*k) := fun i => e.symm (⟨0, by omega⟩, i.castLE hk)
  have hv : Function.Injective v := by
    intro i j h
    apply Fin.ext
    have hvv := congrArg (fun x => ((e x).2).val) h
    simpa [v] using hvv
  let w := (1-familyLambda k t)/(k : ℝ)
  have hw : 0 < w := div_pos hscale (by exact_mod_cast (show 0 < k by omega))
  have hedge (i j : Fin 4) (hij : i≠j) : familyMatrix k r e t (v i) (v j) = w := by
    have hne : v i ≠ v j := hv.ne hij
    simp [familyMatrix, blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, Matrix.one_apply_ne hne, v, w, div_eq_mul_inv]
  let x : Fin (r*k) := e.symm (⟨0, by omega⟩, ⟨0, by omega⟩)
  let y : Fin (r*k) := e.symm (⟨1, by omega⟩, ⟨0, by omega⟩)
  have hxy : x≠y := by
    intro h
    have := congrArg (fun i => ((e i).1).val) h
    norm_num [x,y] at this
  have hz : familyMatrix k r e t x y = 0 := by
    simp [familyMatrix, blockProjection, Matrix.blockDiagonal, Matrix.submatrix, Matrix.of_apply, Function.comp_apply, Prod.swap, Matrix.one_apply_ne hxy, x, y]
  exact segment_exclusion (by nlinarith) (familyMatrix k r e t) ⟨hA,hsA⟩
    (v 0) (v 1) (v 2) (v 3)
    (hv.ne (by decide)) (hv.ne (by decide)) (hv.ne (by decide))
    (hv.ne (by decide)) (hv.ne (by decide)) (hv.ne (by decide)) w hw
    (hedge 0 1 (by decide)) (hedge 1 2 (by decide))
    (hedge 2 3 (by decide)) (hedge 3 0 (by decide)) x y hxy hz

private theorem family_trace_slice (k r : ℕ) (hk : 4 ≤ k) (hr : 2 ≤ r)
    (e : Fin (r*k) ≃ Fin r × Fin k) (t : ℝ)
    (ht : 0 < t) (htu : t < 1/(k : ℝ)^2) :
    familyMatrix k r e t ∈ traceSlice (r*k) ((r*k : ℕ)*t) ∧
    0 < (r*k : ℕ)*t ∧ (r*k : ℕ)*t ≤ (r*k : ℕ) := by
  obtain ⟨hA, hsA, hd⟩ := family_properties k r hk e t ht htu
  have htr : Matrix.trace (familyMatrix k r e t) = (r*k : ℕ)*t := by
    simp only [Matrix.trace, Matrix.diag, hd]
    simp [sum_const]
  have hnpos : (0 : ℝ) < (r*k : ℕ) := by
    exact_mod_cast (Nat.mul_pos (show 0 < r by omega) (show 0 < k by omega))
  have ht1 := (family_scalar_bounds k hk t ht htu).2.2.2.2.2
  exact ⟨⟨⟨hA,hsA⟩,htr⟩,mul_pos hnpos ht,by nlinarith⟩

theorem result : ¬ claim := by
  intro hclaim
  let e : Fin (2*4) ≃ Fin 2 × Fin 4 := finProdFinEquiv.symm
  let A : Matrix (Fin (2*4)) (Fin (2*4)) ℝ := familyMatrix 4 2 e (1/40)
  have ht : (0 : ℝ) < 1/40 := by norm_num
  have htu : (1/40 : ℝ) < 1/(4 : ℝ)^2 := by norm_num
  have hDS : IsDS A := family_isDS 4 2 (by omega) e (1/40) ht htu
  have hsl := family_trace_slice 4 2 (by omega) (by omega) e (1/40) ht htu
  have hslice : A ∈ traceSlice (2*4) (1/5) := by
    convert hsl.1 using 1; norm_num
  have hex := family_exclusion 4 2 (by omega) (by omega) e (1/40) ht htu
  rcases hclaim (2*4) (by omega) (1/5) (by norm_num) (by norm_num) A hslice hDS with h | ⟨P,hP,h | h⟩
  · exact hex.1 h
  · exact (hex.2 P hP).1 h
  · exact (hex.2 P hP).2 h

end D5.S0.Certificates.MouradAbbasC51Refutation
