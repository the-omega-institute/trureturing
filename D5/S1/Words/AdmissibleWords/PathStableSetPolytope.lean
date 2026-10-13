/- GID: D5/S1/Words/AdmissibleWords/PathStableSetPolytope
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/PathStableSetPolytope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The convex hull of admissible binary path words equals the bounded edge polytope. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount

set_option autoImplicit false
noncomputable section
namespace D5.S1.Words.AdmissibleWords.PathStableSetPolytope
open D5.S1.Words.AdmissibleWords.AdmissibleCount

/-- The real occupancy vector of a binary word. -/
def occupancy {n : ℕ} (w : Fin n → Bool) : Fin n → ℝ := fun i => if w i then 1 else 0

/-- Occupancy vectors of words with no adjacent occupied positions. -/
def vertices (n : ℕ) : Set (Fin n → ℝ) := occupancy '' {w | Adm n w}

/-- Coordinate bounds and the exclusion inequality on every edge of a finite path. -/
def polytope (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    ∀ i j, i.val + 1 = j.val → x i + x j ≤ 1}

private theorem adm_edge {n : ℕ} {w : Fin n → Bool} (hw : Adm n w)
    (i j : Fin n) (hij : i.val + 1 = j.val) : ¬ (w i = true ∧ w j = true) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases n with
    | zero => have hi := i.isLt; have hj := j.isLt; omega
    | succ n =>
      revert hij
      refine Fin.cases (fun hij => ?_) (fun k hij => ?_) i
      · have hj : j = 1 := Fin.ext (by simpa using hij.symm)
        simpa [hj] using hw.1
      · revert hij
        refine Fin.cases (fun hij => ?_) (fun l hij => ?_) j
        · simp only [Fin.val_zero, Fin.val_succ] at hij; omega
        · exact ih hw.2 k l (by simpa using hij)

private theorem vertex_mem_polytope {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ vertices n) : x ∈ polytope n := by
  obtain ⟨w, hw, rfl⟩ := hx
  constructor
  · intro i; cases h : w i <;> simp [occupancy, h]
  · intro i j hij
    have h := adm_edge hw i j hij
    cases hi : w i <;> cases hj : w j <;> simp_all [occupancy]

private theorem convex_polytope (n : ℕ) : Convex ℝ (polytope n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i ∧ a * x i + b * y i ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg ha (hx.1 i).1) (mul_nonneg hb (hy.1 i).1)
    · nlinarith [(hx.1 i).2, (hy.1 i).2]
  · intro i j hij
    change a * x i + b * y i + (a * x j + b * y j) ≤ 1
    nlinarith [mul_nonneg ha (sub_nonneg.mpr (hx.2 i j hij)),
      mul_nonneg hb (sub_nonneg.mpr (hy.2 i j hij))]

private theorem lift_hull {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ))
    (hv : ∀ x ∈ vertices n, f x ∈ vertices m)
    (hf : ∀ x y (a b : ℝ), a + b = 1 → f (a • x + b • y) = a • f x + b • f y)
    {y : Fin n → ℝ} (hy : y ∈ convexHull ℝ (vertices n)) :
    f y ∈ convexHull ℝ (vertices m) := by
  apply convexHull_min (t := {y | f y ∈ convexHull ℝ (vertices m)}) ?_ ?_ hy
  · intro x hx; exact subset_convexHull ℝ _ (hv x hx)
  · intro x hx z hz a b ha hb hab
    change f (a • x + b • z) ∈ convexHull ℝ (vertices m)
    rw [hf x z a b hab]
    exact convex_convexHull ℝ _ hx hz ha hb hab

private theorem zero_lift {n : ℕ} {y : Fin n → ℝ}
    (hy : y ∈ convexHull ℝ (vertices n)) :
    Fin.cons 0 y ∈ convexHull ℝ (vertices (n + 1)) := by
  apply lift_hull (fun y => Fin.cons 0 y) ?_ ?_ hy
  · rintro x ⟨w, hw, rfl⟩
    refine ⟨Fin.cons false w, (adm_cons_false n w).mpr hw, ?_⟩
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [occupancy]
  · intro x z a b hab
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem complement_lift {n : ℕ} {y : Fin (n + 1) → ℝ}
    (hy : y ∈ convexHull ℝ (vertices (n + 1))) :
    Fin.cons (1 - y 0) y ∈ convexHull ℝ (vertices (n + 2)) := by
  apply lift_hull (fun y => Fin.cons (1 - y 0) y) ?_ ?_ hy
  · rintro x ⟨w, hw, rfl⟩
    refine ⟨Fin.cons (!(w 0)) w, ?_, ?_⟩
    · change Adm (n + 2) _
      rw [adm_two_iff]
      constructor
      · simp
      · simpa only [Fin.tail_cons] using (show Adm (n + 1) w from hw)
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · cases h : w 0 <;> simp [occupancy, h]
      · simp [occupancy]
  · intro x z a b hab
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · simp

private theorem polytope_mem_hull (n : ℕ) {x : Fin n → ℝ}
    (hx : x ∈ polytope n) : x ∈ convexHull ℝ (vertices n) := by
  induction n with
  | zero =>
    apply subset_convexHull ℝ _
    exact ⟨fun _ => false, trivial, funext fun i => Fin.elim0 i⟩
  | succ n ih =>
    have ht : Fin.tail x ∈ polytope n := by
      exact ⟨fun i => hx.1 i.succ, fun i j hij => hx.2 i.succ j.succ (by simpa using hij)⟩
    have h0 := zero_lift (ih ht)
    cases n with
    | zero =>
      have h1 : Fin.cons 1 (Fin.tail x) ∈ convexHull ℝ (vertices 1) := by
        apply subset_convexHull ℝ _
        refine ⟨fun _ => true, trivial, ?_⟩
        funext i; refine Fin.cases ?_ (fun j => Fin.elim0 j) i
        simp [occupancy]
      have h := convex_convexHull ℝ _ h1 h0 (hx.1 0).1
        (sub_nonneg.mpr (hx.1 0).2) (by ring : x 0 + (1 - x 0) = 1)
      convert h using 1
      funext i; refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      simp
    | succ n =>
      have h1 := complement_lift (ih ht)
      have he : x 0 + x 1 ≤ 1 := hx.2 0 1 rfl
      by_cases hz : 1 - x 1 = 0
      · have hx0 : x 0 = 0 := by linarith [(hx.1 0).1]
        simpa only [← hx0, Fin.cons_self_tail] using h0
      · have hd : 0 < 1 - x 1 := lt_of_le_of_ne (sub_nonneg.mpr (hx.1 1).2) (Ne.symm hz)
        let t := x 0 / (1 - x 1)
        have ht0 : 0 ≤ t := div_nonneg (hx.1 0).1 hd.le
        have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
        have h := convex_convexHull ℝ _ h1 h0 ht0 (sub_nonneg.mpr ht1)
          (by ring : t + (1 - t) = 1)
        convert h using 1
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Pi.add_apply, Pi.smul_apply, Fin.cons_zero, smul_eq_mul,
            Fin.tail, Fin.succ_zero_eq_one, mul_zero, add_zero]
          exact (div_mul_cancel₀ (x 0) hz).symm
        · simp only [Pi.add_apply, Pi.smul_apply, Fin.cons_succ, smul_eq_mul, Fin.tail]
          ring

/-- Every bounded fractional occupancy of a finite path is a convex mixture of admissible words.
The result includes the empty path and the one-coordinate interval. -/
theorem convexHull_vertices (n : ℕ) : convexHull ℝ (vertices n) = polytope n := by
  exact Set.Subset.antisymm (convexHull_min (fun _ hx => vertex_mem_polytope hx) (convex_polytope n))
    (fun _ hx => polytope_mem_hull n hx)

/-- In three coordinates the edge inequalities describe a pyramid with square base
`{(u,0,v) | u,v ∈ [0,1]}` and apex `(0,1,0)`. -/
theorem convexHull_three_pyramid :
    convexHull ℝ (vertices 3) =
      {x : Fin 3 → ℝ | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 ≤ 1 ∧ x 1 + x 2 ≤ 1} ∧
    ∀ x : Fin 3 → ℝ, x ∈ convexHull ℝ (vertices 3) ↔
      ∃ t u v : ℝ, t ∈ Set.Icc 0 1 ∧ u ∈ Set.Icc 0 1 ∧ v ∈ Set.Icc 0 1 ∧
        x = (1 - t) • ![u, 0, v] + t • ![0, 1, 0] := by
  have hthree : polytope 3 =
      {x : Fin 3 → ℝ | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 ≤ 1 ∧ x 1 + x 2 ≤ 1} := by
    ext x
    constructor
    · intro hx
      exact ⟨fun i => (hx.1 i).1, hx.2 0 1 rfl, hx.2 1 2 rfl⟩
    · rintro ⟨h0, h01, h12⟩
      constructor
      · intro i
        refine ⟨h0 i, ?_⟩
        have hzero := h0 0
        have hone := h0 1
        have htwo := h0 2
        fin_cases i <;> dsimp <;> linarith
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
  have heq := (convexHull_vertices 3).trans hthree
  refine ⟨heq, ?_⟩
  intro x
  rw [heq]
  constructor
  · rintro ⟨h0, h01, h12⟩
    have ht : x 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨h0 1, by linarith [h0 0]⟩
    by_cases hone : x 1 = 1
    · have hx0 : x 0 = 0 := by linarith [h0 0]
      have hx2 : x 2 = 0 := by linarith [h0 2]
      refine ⟨1, 0, 0, ⟨by norm_num, le_rfl⟩, ⟨le_rfl, by norm_num⟩,
        ⟨le_rfl, by norm_num⟩, ?_⟩
      funext i
      fin_cases i <;> simp [hx0, hx2, hone]
    · have hd : 0 < 1 - x 1 := by rcases ht with ⟨_, ht⟩; exact sub_pos.mpr (lt_of_le_of_ne ht hone)
      refine ⟨x 1, x 0 / (1 - x 1), x 2 / (1 - x 1), ht,
        ⟨div_nonneg (h0 0) hd.le, (div_le_one hd).mpr (by linarith)⟩,
        ⟨div_nonneg (h0 2) hd.le, (div_le_one hd).mpr (by linarith)⟩, ?_⟩
      funext i
      fin_cases i <;> simp <;> field_simp
  · rintro ⟨t, u, v, ht, hu, hv, rfl⟩
    have hn : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · change 0 ≤ (1 - t) * u + t * 0
        nlinarith [mul_nonneg hn hu.1]
      · change 0 ≤ (1 - t) * 0 + t * 1
        linarith [ht.1]
      · change 0 ≤ (1 - t) * v + t * 0
        nlinarith [mul_nonneg hn hv.1]
    · change (1 - t) * u + t * 0 + ((1 - t) * 0 + t * 1) ≤ 1
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hu.2)]
    · change (1 - t) * 0 + t * 1 + ((1 - t) * v + t * 0) ≤ 1
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hv.2)]

#print axioms convexHull_three_pyramid
#print axioms convexHull_vertices
end D5.S1.Words.AdmissibleWords.PathStableSetPolytope
