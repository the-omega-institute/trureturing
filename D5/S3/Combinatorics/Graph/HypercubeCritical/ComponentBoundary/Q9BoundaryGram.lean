/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Integral Gram matrices and square determinants for the signed nine-cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Integral boundary identities for the fixed Huang signing of the nine-cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryGram

open scoped BigOperators Matrix
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj flip_flip)
open D5.S3.Combinatorics.Graph.Hypercube
open private intCoeff intCoeff_cast intA intA_square intCoeff_zero_of_same_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private intCoeff_zero_of_not_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private huangMatrix_symmetric cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

open private paritySide parity_union parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

/-- Huang's integral signed adjacency after switching by a vertex sign function. -/
noncomputable def switchedMatrix (s : Q 9 → ℤ) : Matrix (Q 9) (Q 9) ℤ :=
  fun x y => s x * intCoeff x y * s y

private theorem switchedMatrix_transpose (s : Q 9 → ℤ) : (switchedMatrix s)ᵀ =
    switchedMatrix s := by
  ext x y
  have h : intCoeff x y = intCoeff y x := by
    apply Int.cast_injective (α := ℝ)
    rw [intCoeff_cast, intCoeff_cast, huangMatrix_symmetric]
  change s y * intCoeff y x * s x = s x * intCoeff x y * s y
  rw [h]
  ring

private theorem switchedMatrix_square (s : Q 9 → ℤ) (hs : ∀ x, s x * s x = 1) :
    switchedMatrix s * switchedMatrix s = (9 : ℤ) • (1 : Matrix (Q 9) (Q 9) ℤ) := by
  classical
  let H : Matrix (Q 9) (Q 9) ℤ := intCoeff
  have hH : H * H = (9 : ℤ) • (1 : Matrix (Q 9) (Q 9) ℤ) := by
    apply Matrix.ext_of_mulVec_single
    intro y
    rw [← Matrix.mulVec_mulVec]
    change intA (intA (Pi.single y 1)) = _
    rw [intA_square, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  ext x y
  calc
    (switchedMatrix s * switchedMatrix s) x y = s x * (H * H) x y * s y := by
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, switchedMatrix]
      apply Finset.sum_congr rfl
      intro z _
      change (s x * H x z * s z) * (s z * H z y * s y) =
        s x * (H x z * H z y) * s y
      calc
        _ = (s z * s z) * (s x * (H x z * H z y) * s y) := by ring
        _ = _ := by rw [hs, one_mul]
    _ = _ := by
      rw [hH]
      by_cases h : x = y
      · subst y
        simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        rw [mul_comm (s x) 9, mul_assoc, hs, mul_one]
      · simp [h]

/-- The selected columns on the parity opposite to the retained rows. -/
abbrev Interior (S : Finset (Q 9)) (b : Bool) :=
  {y : {x : Q 9 // cubeParity x ≠ b} // y.1 ∈ S}

/-- All exterior columns on the parity opposite to the retained rows. -/
abbrev Exterior (S : Finset (Q 9)) (b : Bool) :=
  {y : {x : Q 9 // cubeParity x ≠ b} // y.1 ∉ S}

/-- Keep any injectively indexed subset of rows of one parity, and split all opposite
columns between the selected vertices and their complement. The exterior Gram is the
defect of the interior Gram. When the exterior is square, the determinant of that
defect is the square of the determinant of the actual signed exterior block. -/
theorem reduced_boundary_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Q 9)) (b : Bool) (r : ι ↪ Q 9) (hr : ∀ i, cubeParity (r i) = b)
    (s : Q 9 → ℤ) (hs : ∀ x, s x * s x = 1) :
    let H := switchedMatrix s
    let M := H.submatrix r (fun y : Interior S b => y.1.1)
    let K := H.submatrix r (fun y : Exterior S b => y.1.1)
    K * Kᵀ = (9 : ℤ) • 1 - M * Mᵀ ∧
      ∀ e : ι ≃ Exterior S b,
        ((9 : ℤ) • 1 - M * Mᵀ).det = (K.submatrix id e).det ^ 2 := by
  classical
  dsimp only
  let H := switchedMatrix s
  let M := H.submatrix r (fun y : Interior S b => y.1.1)
  let K := H.submatrix r (fun y : Exterior S b => y.1.1)
  let W := H.submatrix r (fun y : {x : Q 9 // cubeParity x ≠ b} => y.1)
  have hW : W * Wᵀ = (9 : ℤ) • 1 := by
    ext i j
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x : Q 9 => cubeParity x ≠ b)
      (fun x => H (r i) x * H (r j) x)
    have hzero : (∑ x : {x : Q 9 // ¬ cubeParity x ≠ b},
        H (r i) x.1 * H (r j) x.1) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      have hparity := (hr i).trans (not_ne_iff.mp x.property).symm
      simp [H, switchedMatrix, intCoeff_zero_of_same_parity _ _ hparity]
    rw [hzero, add_zero] at hsplit
    have hfull : H * Hᵀ = (9 : ℤ) • 1 := by
      rw [switchedMatrix_transpose s, switchedMatrix_square s hs]
    trans (H * Hᵀ) (r i) (r j)
    · exact hsplit
    · rw [hfull]
      simp [Matrix.one_apply, r.injective.eq_iff]
  have hadd : M * Mᵀ + K * Kᵀ = W * Wᵀ := by
    ext i j
    exact Fintype.sum_subtype_add_sum_subtype (fun y : {x : Q 9 // cubeParity x ≠ b} => y.1 ∈ S)
      (fun x => H (r i) x.1 * H (r j) x.1)
  have hGram : K * Kᵀ = (9 : ℤ) • 1 - M * Mᵀ :=
    eq_sub_of_add_eq (by simpa only [add_comm, hW] using hadd)
  change K * Kᵀ = _ ∧ _
  refine ⟨hGram, fun e => ?_⟩
  have hreindex : K.submatrix id e * (K.submatrix id e)ᵀ = K * Kᵀ := by
    exact Matrix.submatrix_mul_transpose_submatrix e K
  rw [← hGram, ← hreindex, Matrix.det_mul, Matrix.det_transpose, pow_two]

open Classical in
/-- A balanced signed induced support has an unsigned interior biadjacency block,
with the same integral Gram factor on the true exterior of the support. -/
theorem balanced_boundary_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Q 9)) (b : Bool) (r : ι ↪ Q 9) (hr : ∀ i, cubeParity (r i) = b)
    (hS : ∀ i, r i ∈ S) (hb : IsBalanced S) :
    let M : Matrix ι (Interior S b) ℤ :=
      fun i y => if (hypercube 9).Adj (r i) y.1.1 then 1 else 0
    ∃ s : Q 9 → ℤ, (∀ x, s x * s x = 1) ∧
      let K := (switchedMatrix s).submatrix r (fun y : Exterior S b => y.1.1)
      K * Kᵀ = (9 : ℤ) • 1 - M * Mᵀ ∧
        ∀ e : ι ≃ Exterior S b,
          ((9 : ℤ) • 1 - M * Mᵀ).det = (K.submatrix id e).det ^ 2 := by
  classical
  obtain ⟨σ, hσ⟩ := hb
  let s : Q 9 → ℤ := fun x => if σ x = 1 then 1 else -1
  have hs : ∀ x, s x * s x = 1 := by
    intro x
    dsimp [s]
    split <;> norm_num
  have hcast (x : Q 9) (hx : x ∈ S) : (s x : ℝ) = σ x := by
    rcases hσ.1 x hx with hx | hx <;> norm_num [s, hx]
  dsimp only
  refine ⟨s, hs, ?_⟩
  have hM : (switchedMatrix s).submatrix r (fun y : Interior S b => y.1.1) =
      (fun i y => if (hypercube 9).Adj (r i) y.1.1 then 1 else 0) := by
    ext i y
    simp only [Matrix.submatrix_apply]
    split_ifs with hadj
    · have hsign : intCoeff (r i) y.1.1 = s (r i) * s y.1.1 := by
        apply Int.cast_injective (α := ℝ)
        rw [intCoeff_cast, Int.cast_mul, hcast _ (hS i), hcast _ y.property]
        exact hσ.2 _ (hS i) _ y.property hadj
      change s (r i) * intCoeff (r i) y.1.1 * s y.1.1 = 1
      calc
        _ = (s (r i) * s (r i)) * (s y.1.1 * s y.1.1) := by rw [hsign]; ring
        _ = 1 := by rw [hs, hs, one_mul]
    · simp [switchedMatrix, intCoeff_zero_of_not_adj _ _ hadj]
  simpa only [hM] using reduced_boundary_factorization S b r hr s hs

open Classical in
private theorem regular_parity_card (S : Finset (Q 9)) (b : Bool) {d : ℕ} (hd : 0 < d)
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree d) :
    2 * (paritySide S b).card = S.card := by
  classical
  have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq (parity_bipartite S)
  simp only [hr.degree_eq, Finset.sum_const, smul_eq_mul] at hs
  have heq : (paritySide S false).card = (paritySide S true).card :=
    Nat.eq_of_mul_eq_mul_right hd hs
  have hcardS : Fintype.card (S : Set (Q 9)) = S.card := by simp
  have hu := congrArg Finset.card (parity_union S)
  rw [Finset.card_union_of_disjoint (by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact Bool.false_ne_true ((Finset.mem_filter.mp hz).2.symm.trans
      (Finset.mem_filter.mp hz').2)), Finset.card_univ, hcardS] at hu
  cases b <;> omega

private theorem interior_card (S : Finset (Q 9)) (b : Bool) :
    Fintype.card (Interior S b) = (paritySide S (!b)).card := by
  let e : Interior S b ≃ ↥(paritySide S (!b)) :=
    { toFun := fun y => ⟨⟨y.1.1, y.property⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          have h := y.1.property
          cases b <;> cases hy : cubeParity y.1.1 <;> simp_all⟩⟩
      invFun := fun y => ⟨⟨y.1.1, by
        have h := (Finset.mem_filter.mp y.property).2
        cases b <;> cases hy : cubeParity y.1.1 <;> simp_all⟩, y.1.property⟩
      left_inv := fun y => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext (Subtype.ext rfl) }
  rw [Fintype.card_congr e, Fintype.card_coe]

private theorem cube_opposite_card (b : Bool) :
    Fintype.card {x : Q 9 // cubeParity x ≠ b} = 256 := by
  let e : {x : Q 9 // cubeParity x ≠ b} ≃ {x : Q 9 // ¬ cubeParity x ≠ b} :=
    { toFun := fun x => ⟨flip x.1 0, by
        have h := x.property
        have hf := cubeParity_ne_of_adj (flip_adj x.1 0)
        cases b <;> cases hx : cubeParity x.1 <;> cases hy : cubeParity (flip x.1 0) <;>
          simp_all⟩
      invFun := fun x => ⟨flip x.1 0, by
        have h := not_ne_iff.mp x.property
        exact fun h' => cubeParity_ne_of_adj (flip_adj x.1 0) (h.trans h'.symm)⟩
      left_inv := fun x => Subtype.ext (flip_flip x.1 0)
      right_inv := fun x => Subtype.ext (flip_flip x.1 0) }
  have he := Fintype.card_congr e
  have hc := Fintype.card_subtype_compl (fun x : Q 9 => cubeParity x ≠ b)
  have hfull : Fintype.card (Q 9) = 512 := by simp
  rw [hfull] at hc
  omega

/-- The row indices obtained by deleting two vertices from the chosen parity side. -/
abbrev ReducedRows (S : Finset (Q 9)) (b : Bool) (c d : (S : Set (Q 9))) :=
  ↥(((paritySide S b).erase c).erase d)

open Classical in
/-- On a balanced cubic induced support of size 258, two distinct deletions on
one parity leave an actual square integral boundary factor of order 127. -/
theorem cubic_reduced_boundary_factorization (S : Finset (Q 9)) (b : Bool)
    (hcard : S.card = 258)
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced S)
    (c d : (S : Set (Q 9))) (hc : cubeParity c.1 = b) (hd : cubeParity d.1 = b) (hne : d ≠ c) :
    let M : Matrix (ReducedRows S b c d) (Interior S b) ℤ :=
      fun i y => if (hypercube 9).Adj i.1.1 y.1.1 then 1 else 0
    ∃ (s : Q 9 → ℤ) (e : ReducedRows S b c d ≃ Exterior S b),
      (∀ x, s x * s x = 1) ∧ Fintype.card (Exterior S b) = 127 ∧
      let Z := (switchedMatrix s).submatrix
        (fun i : ReducedRows S b c d => i.1.1) (fun i => (e i).1.1)
      Z * Zᵀ = (9 : ℤ) • 1 - M * Mᵀ ∧
        ((9 : ℤ) • 1 - M * Mᵀ).det = Z.det ^ 2 := by
  classical
  dsimp only
  let r : ReducedRows S b c d ↪ Q 9 :=
    ⟨fun i => i.1.1, fun _ _ h => Subtype.ext (Subtype.ext h)⟩
  have hrb (i : ReducedRows S b c d) : cubeParity (r i) = b :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase i.property))).2
  have hC : c ∈ paritySide S b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have hD : d ∈ (paritySide S b).erase c :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩
  have hrows : Fintype.card (ReducedRows S b c d) = 127 := by
    change Fintype.card ↥(((paritySide S b).erase c).erase d) = 127
    rw [Fintype.card_coe, Finset.card_erase_of_mem hD, Finset.card_erase_of_mem hC]
    have h := regular_parity_card S b (d := 3) (by decide) hr
    omega
  have hout : Fintype.card (Exterior S b) = 127 := by
    rw [Fintype.card_subtype_compl (fun y : {x : Q 9 // cubeParity x ≠ b} => y.1 ∈ S),
      cube_opposite_card, interior_card]
    have h := regular_parity_card S (!b) (d := 3) (by decide) hr
    omega
  let e := Fintype.equivOfCardEq (hrows.trans hout.symm)
  obtain ⟨s, hs, hGram, hdet⟩ :=
    balanced_boundary_factorization S b r hrb (fun i => i.1.property) hb
  refine ⟨s, e, hs, hout, ?_, hdet e⟩
  exact (Matrix.submatrix_mul_transpose_submatrix e
    ((switchedMatrix s).submatrix r (fun y : Exterior S b => y.1.1))).trans hGram

open Classical in
private theorem degree_of_no_exterior_neighbors (C S : Finset (Q 9))
    (hsub : C ⊆ S) (x : (C : Set (Q 9)))
    (h : ∀ y ∈ S, (hypercube 9).Adj x.1 y → y ∈ C) :
    ((hypercube 9).induce (S : Set (Q 9))).degree ⟨x.1, hsub x.property⟩ =
      ((hypercube 9).induce (C : Set (Q 9))).degree x := by
  let f := (hypercube 9).induceHomOfLE
    (s := (C : Set (Q 9))) (s' := (S : Set (Q 9))) (fun _ hx => hsub hx)
  apply SimpleGraph.Embedding.degree_eq_of_neighborSet_subset_range (f := f) (v := x)
  intro y hy
  exact ⟨⟨y.1, h y.1 y.property hy⟩, Subtype.ext rfl⟩

set_option maxHeartbeats 650000 in
-- Elaborating the reduced row matrices unfolds several nested subtype coercions.
open Classical in
/-- The separated balanced cubic 72- and 186-vertex supports have an integral
boundary factor of order 127 after deleting one row from each support. -/
theorem separated_cubic_boundary_factorization (C D : Finset (Q 9)) (b : Bool)
    (hC : C.card = 72) (hD : D.card = 186) (hdisj : Disjoint C D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (c : (C : Set (Q 9))) (d : (D : Set (Q 9)))
    (hc : cubeParity c.1 = b) (hd : cubeParity d.1 = b) :
    let S := C ∪ D
    let cS : (S : Set (Q 9)) := ⟨c.1, Finset.mem_union_left _ c.property⟩
    let dS : (S : Set (Q 9)) := ⟨d.1, Finset.mem_union_right _ d.property⟩
    let M : Matrix (ReducedRows S b cS dS) (Interior S b) ℤ :=
      fun i y => if (hypercube 9).Adj i.1.1 y.1.1 then 1 else 0
    ∃ (s : Q 9 → ℤ) (e : ReducedRows S b cS dS ≃ Exterior S b),
      (∀ x, s x * s x = 1) ∧ Fintype.card (Exterior S b) = 127 ∧
      let Z := (switchedMatrix s).submatrix
        (fun i : ReducedRows S b cS dS => i.1.1) (fun i => (e i).1.1)
      Z * Zᵀ = (9 : ℤ) • 1 - M * Mᵀ ∧
        ((9 : ℤ) • 1 - M * Mᵀ).det = Z.det ^ 2 := by
  classical
  have hc' (x : Q 9) (hx : x ∈ D) : x ∉ C :=
    fun hxC => Finset.disjoint_left.mp hdisj hxC hx
  have hr : ((hypercube 9).induce ((C ∪ D : Finset (Q 9)) : Set (Q 9))).IsRegularOfDegree 3 := by
    intro x
    rcases Finset.mem_union.mp x.property with hx | hx
    · have hn (y : Q 9) (hy : y ∈ C ∪ D) (ha : (hypercube 9).Adj x.1 y) : y ∈ C :=
        (Finset.mem_union.mp hy).resolve_right (fun hyD => hsep _ hx _ hyD ha)
      exact (degree_of_no_exterior_neighbors C (C ∪ D)
        (fun _ hy => Finset.mem_union_left _ hy) ⟨x.1, hx⟩ hn).trans (hrC ⟨x.1, hx⟩)
    · have hn (y : Q 9) (hy : y ∈ C ∪ D) (ha : (hypercube 9).Adj x.1 y) : y ∈ D :=
        (Finset.mem_union.mp hy).resolve_left (fun hyC => hsep _ hyC _ hx ha.symm)
      exact (degree_of_no_exterior_neighbors D (C ∪ D)
        (fun _ hy => Finset.mem_union_right _ hy) ⟨x.1, hx⟩ hn).trans (hrD ⟨x.1, hx⟩)
  obtain ⟨σC, hσC⟩ := hbC
  obtain ⟨σD, hσD⟩ := hbD
  have hb : IsBalanced (C ∪ D) := by
    let σ : Q 9 → ℝ := fun x => if x ∈ C then σC x else σD x
    refine ⟨σ, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · simpa only [σ, ite_eq_left hx] using hσC.1 x hx
      · simpa only [σ, ite_eq_right (hc' x hx)] using hσD.1 x hx
    · intro x hx y hy ha
      rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
      · simpa only [σ, ite_eq_left hx, ite_eq_left hy] using hσC.2 x hx y hy ha
      · exact (hsep x hx y hy ha).elim
      · exact (hsep y hy x hx ha.symm).elim
      · simpa only [σ, ite_eq_right (hc' x hx), ite_eq_right (hc' y hy)] using hσD.2 x hx y hy ha
  have hsize : (C ∪ D).card = 258 := by
    rw [Finset.card_union_of_disjoint hdisj, hC, hD]
  let cS : ((C ∪ D : Finset (Q 9)) : Set (Q 9)) :=
    ⟨c.1, Finset.mem_union_left _ c.property⟩
  let dS : ((C ∪ D : Finset (Q 9)) : Set (Q 9)) :=
    ⟨d.1, Finset.mem_union_right _ d.property⟩
  have hne : dS ≠ cS := by
    intro heq
    have hdc : d.1 = c.1 := congrArg Subtype.val heq
    exact hc' d.1 d.property (hdc.symm ▸ c.property)
  exact cubic_reduced_boundary_factorization (C ∪ D) b hsize hr hb cS dS hc hd hne

#print axioms reduced_boundary_factorization
#print axioms balanced_boundary_factorization
#print axioms cubic_reduced_boundary_factorization
#print axioms separated_cubic_boundary_factorization

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryGram
