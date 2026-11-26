/- GID: D5/S3/Analytic/Probability/ThreeBitCubeConditionalMeans
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/ThreeBitCubeConditionalMeans
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Antitone weighted conditional means on positive fibers of the three-bit cube give nonpositive centered sums on all upper sets. -/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

set_option autoImplicit false

namespace D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans

/-- The three-coordinate binary product with its pointwise order. -/
abbrev Cube := Fin 3 → Fin 2

private def single (i : Fin 3) : Cube := fun j => if j = i then 1 else 0
private def double (i : Fin 3) : Cube := fun j => if j = i then 0 else 1
private def majority (x : Cube) : Prop := 2 ≤ ∑ i : Fin 3, (x i).val
private instance (x : Cube) : Decidable (majority x) := inferInstanceAs (Decidable (_ ≤ _))

-- These finite propositions concern only the eight vertices and the coordinatewise order.
private theorem cube_vertices :
    ∀ x : Cube, x = (fun _ => 0) ∨ x = (fun _ => 1) ∨
      (∃ i, x = single i) ∨ (∃ i, x = double i) := by decide

private theorem single_le_iff (i : Fin 3) (x : Cube) :
    single i ≤ x ↔ x i = 1 := by revert i x; decide

private theorem le_double_iff (i : Fin 3) (x : Cube) :
    x ≤ double i ↔ x i = 0 := by revert i x; decide

private theorem bit_cases : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide

private def faceCorners (i j : Fin 3) (x y : Cube) : Prop :=
  (∀ z : Cube, z i = x i → z j = 0 → z ≤ x) ∧
  (∀ z : Cube, z i = y i → z j = 1 → y ≤ z)

private instance (i j : Fin 3) (x y : Cube) : Decidable (faceCorners i j x y) := by
  unfold faceCorners
  infer_instance

private theorem opposite_face_vertices :
    ∀ (i : Fin 3) (x y : Cube), x i = y i → ¬ x ≤ y → ¬ y ≤ x →
      ∃ j : Fin 3, j ≠ i ∧ x j = 0 ∧ y j = 1 ∧ faceCorners i j x y := by decide

private theorem opposite_majority_vertices :
    ∀ x y : Cube, ¬ majority x → majority y → ¬ x ≤ y →
      ∃ j i : Fin 3, x = single j ∧ y = double j ∧ single i ≤ y ∧ x ≤ double i := by decide

private theorem majority_exchange :
    ∀ (i : Fin 3) (z : Cube),
      majority z ↔ (z i = 1 ∧ z ≠ single i) ∨ z = double i := by decide

private theorem majority_vertices :
    ∀ x : Cube, majority x ↔ x = (fun _ => 1) ∨ ∃ i, x = double i := by decide

private theorem cube_bounds : ∀ x : Cube, (fun _ => 0) ≤ x ∧ x ≤ (fun _ => 1) := by decide

private theorem exchange_vertices (i : Fin 3) :
    single i i = 1 ∧ double i i = 0 := by simp [single, double]

open scoped Classical
noncomputable section

/-- The inverse image of the specified tuple under restriction to the selected coordinates. -/
def fiber (T : Finset (Fin 3)) (a : T → Fin 2) : Set Cube :=
  {x | (fun i : T => x i) = a}

/-- The real probability mass of a coordinate fiber. -/
def fiberMass (p : PMF Cube) (T : Finset (Fin 3)) (a : T → Fin 2) : ℝ :=
  ∑ x ∈ (fiber T a).toFinset, (p x).toReal

/-- The conditional weighted mean on a positive-mass coordinate fiber. -/
def fiberMean (p : PMF Cube) (h : Cube → ℝ) (T : Finset (Fin 3)) (a : T → Fin 2) : ℝ :=
  (∑ x ∈ (fiber T a).toFinset, (p x).toReal * h x) / fiberMass p T a

private abbrev AntitoneMeans (p : PMF Cube) (h : Cube → ℝ) :=
  ∀ (T : Finset (Fin 3)) (a b : T → Fin 2), a ≤ b →
    0 < fiberMass p T a → 0 < fiberMass p T b → fiberMean p h T b ≤ fiberMean p h T a

private def mean (p : PMF Cube) (h : Cube → ℝ) : ℝ :=
  ∑ x, (p x).toReal * h x

private def centered (p : PMF Cube) (h : Cube → ℝ) (x : Cube) : ℝ :=
  (p x).toReal * (h x - mean p h)

private def regionSum (s : Cube → ℝ) (U : Set Cube) : ℝ :=
  ∑ x ∈ U.toFinset, s x

private theorem regionSum_univ (s : Cube → ℝ) :
    regionSum s Set.univ = ∑ x, s x := by simp [regionSum]

private theorem regionSum_singleton (s : Cube → ℝ) (x : Cube) :
    regionSum s {x} = s x := by simp [regionSum]

private theorem regionSum_indicator (s : Cube → ℝ) (A : Set Cube) :
    regionSum s A = ∑ x, if x ∈ A then s x else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp

private theorem regionSum_union (s : Cube → ℝ) {A B : Set Cube} (hd : Disjoint A B) :
    regionSum s (A ∪ B) = regionSum s A + regionSum s B := by
  simp only [regionSum_indicator, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B
  · exact (Set.disjoint_left.mp hd ha hb).elim
  all_goals simp [ha, hb]

private theorem regionSum_split (s : Cube → ℝ) (A U : Set Cube) :
    regionSum s (A ∩ U) + regionSum s (A \ U) = regionSum s A := by
  have hdisj : Disjoint (A ∩ U) (A \ U) := Set.disjoint_left.mpr fun _ h₁ h₂ =>
    h₂.2 h₁.2
  have hunion : (A ∩ U) ∪ (A \ U) = A := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  rw [← regionSum_union s hdisj, hunion]

private theorem exists_pos_of_regionSum_pos {s : Cube → ℝ} {U : Set Cube}
    (hs : 0 < regionSum s U) : ∃ x ∈ U, 0 < s x := by
  by_contra! hn
  exact hs.not_ge (Finset.sum_nonpos fun x hx => hn x (Set.mem_toFinset.mp hx))

private theorem exists_neg_of_regionSum_neg {s : Cube → ℝ} {U : Set Cube}
    (hs : regionSum s U < 0) : ∃ x ∈ U, s x < 0 := by
  by_contra! hn
  exact hs.not_ge (Finset.sum_nonneg fun x hx => hn x (Set.mem_toFinset.mp hx))

private theorem centered_total (p : PMF Cube) (h : Cube → ℝ) :
    regionSum (centered p h) Set.univ = 0 := by
  have hp : ∑ x, p x = 1 := by
    simpa only [tsum_fintype] using p.tsum_coe
  have hw : ∑ x, (p x).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x), hp, ENNReal.toReal_one]
  rw [regionSum_univ]
  simp only [centered, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul,
    mean, sub_self]

private theorem centered_fiber {p : PMF Cube} {h : Cube → ℝ} {T : Finset (Fin 3)}
    {a : T → Fin 2} :
    regionSum (centered p h) (fiber T a) =
      fiberMass p T a * (fiberMean p h T a - mean p h) := by
  have hsum :
      regionSum (centered p h) (fiber T a) =
        (∑ x ∈ (fiber T a).toFinset, (p x).toReal * h x) - fiberMass p T a * mean p h := by
    simp only [regionSum, centered, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, fiberMass]
  rw [hsum, mul_sub]
  have hn : ∀ x ∈ (fiber T a).toFinset, 0 ≤ (p x).toReal := fun _ _ => ENNReal.toReal_nonneg
  by_cases hm : fiberMass p T a = 0
  · have hzero : ∀ x ∈ (fiber T a).toFinset, (p x).toReal = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hn).mp hm
    rw [hm, zero_mul, zero_mul, sub_zero, sub_zero]
    exact Finset.sum_eq_zero fun x hx => by rw [hzero x hx, zero_mul]
  · rw [fiberMean, mul_div_cancel₀ _ hm]

-- Strict centered signs force both masses to be positive, so the endpoints can be compared.
private theorem no_opposite_fibers {p : PMF Cube} {h : Cube → ℝ} (hr : AntitoneMeans p h)
    {T : Finset (Fin 3)} {a b : T → Fin 2} (hab : a ≤ b)
    (ha : regionSum (centered p h) (fiber T a) < 0)
    (hb : 0 < regionSum (centered p h) (fiber T b)) : False := by
  rw [centered_fiber] at ha hb
  have hm (t : T → Fin 2) : 0 ≤ fiberMass p T t :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hma : 0 < fiberMass p T a := (hm a).lt_of_ne' fun hzero => by simp [hzero] at ha
  have hmb : 0 < fiberMass p T b := (hm b).lt_of_ne' fun hzero => by simp [hzero] at hb
  have hmean := hr T a b hab hma hmb
  have hlow : fiberMean p h T a - mean p h < 0 := by
    by_contra! hnonneg
    exact ha.not_ge (mul_nonneg (hma.le) hnonneg)
  have hhigh : 0 < fiberMean p h T b - mean p h := by
    by_contra! hnonpos
    exact hb.not_ge (mul_nonpos_of_nonneg_of_nonpos (hmb.le) hnonpos)
  linarith only [hmean, hlow, hhigh]

private def restrict (T : Finset (Fin 3)) (x : Cube) : T → Fin 2 :=
  fun i => x i

private theorem mem_fiber_restrict {T : Finset (Fin 3)} {x z : Cube} :
    z ∈ fiber T (restrict T x) ↔ ∀ i ∈ T, z i = x i := by
  change ((fun i : T => z i) = fun i : T => x i) ↔ _
  rw [funext_iff]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.property⟩

private theorem no_opposite_points {p : PMF Cube} {h : Cube → ℝ} (hr : AntitoneMeans p h)
    {x y : Cube} (hxy : x ≤ y) (hx : centered p h x < 0) (hy : 0 < centered p h y) : False := by
  have hf (z : Cube) : fiber Finset.univ (restrict Finset.univ z) = {z} := by
    ext q
    simp only [mem_fiber_restrict, Finset.mem_univ, true_implies, Set.mem_singleton_iff]
    exact funext_iff.symm
  have hle : restrict Finset.univ x ≤ restrict Finset.univ y := fun i => hxy i
  apply no_opposite_fibers hr hle
  · rwa [hf, regionSum_singleton]
  · rwa [hf, regionSum_singleton]

private def face (i : Fin 3) (b : Fin 2) : Set Cube := {x | x i = b}

private theorem fiber_single (i : Fin 3) (b : Fin 2) :
    fiber {i} (fun _ => b) = face i b := by
  ext z
  change ((fun j : (↑({i} : Finset (Fin 3))) => z j) = fun _ => b) ↔ z i = b
  rw [funext_iff]
  constructor
  · intro hz
    exact hz ⟨i, by simp⟩
  · intro hz j
    have hji : (j : Fin 3) = i := Finset.mem_singleton.mp j.property
    exact (congrArg z hji).trans hz

private theorem face_totals {p : PMF Cube} {h : Cube → ℝ} (i : Fin 3) :
    regionSum (centered p h) (face i 1) + regionSum (centered p h) (face i 0) = 0 := by
  have hcomp : (Set.univ : Set Cube) \ face i 1 = face i 0 := by
    ext x
    change (x ∈ (Set.univ : Set Cube) ∧ x i ≠ 1) ↔ x i = 0
    simp only [Set.mem_univ, true_and]
    rcases bit_cases (x i) with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hsplit := regionSum_split (centered p h) Set.univ (face i 1)
  rwa [Set.univ_inter, hcomp, centered_total] at hsplit

private theorem upper_face_nonpos {p : PMF Cube} {h : Cube → ℝ} (hr : AntitoneMeans p h)
    (i : Fin 3) : regionSum (centered p h) (face i 1) ≤ 0 := by
  by_contra! hp
  have hn : regionSum (centered p h) (face i 0) < 0 := by
    linarith only [hp, face_totals (p := p) (h := h) i]
  apply no_opposite_fibers hr (T := {i}) (a := fun _ => 0) (b := fun _ => 1)
  · intro j
    exact (by decide : (0 : Fin 2) ≤ 1)
  · rwa [fiber_single]
  · rwa [fiber_single]

private theorem mem_pair_fiber {i j : Fin 3} {x z : Cube} :
    z ∈ fiber {i, j} (restrict {i, j} x) ↔ z i = x i ∧ z j = x j := by
  rw [mem_fiber_restrict]
  constructor
  · intro hz
    exact ⟨hz i (by simp), hz j (by simp)⟩
  · rintro ⟨hi, hj⟩ k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · rwa [Finset.mem_singleton.mp hk]

-- Two incomparable corners of a face force its upper trace to be a coordinate slice.
private theorem no_opposite_face_parts {p : PMF Cube} {h : Cube → ℝ} (hr : AntitoneMeans p h)
    {U : Set Cube} (hU : IsUpperSet U) (i : Fin 3) (b : Fin 2)
    (hneg : regionSum (centered p h) (face i b \ U) < 0)
    (hpos : 0 < regionSum (centered p h) (face i b ∩ U)) : False := by
  obtain ⟨x, hx, hsx⟩ := exists_neg_of_regionSum_neg hneg
  obtain ⟨y, hy, hsy⟩ := exists_pos_of_regionSum_pos hpos
  have hxi : x i = b := hx.1
  have hyi : y i = b := hy.1
  have hxy : x i = y i := hxi.trans hyi.symm
  have hnxy : ¬ x ≤ y := fun hle => no_opposite_points hr hle hsx hsy
  have hnyx : ¬ y ≤ x := fun hle => hx.2 (hU hle hy.2)
  obtain ⟨j, _, hxj, hyj, corners⟩ := opposite_face_vertices i x y hxy hnxy hnyx
  change (∀ z : Cube, z i = x i → z j = 0 → z ≤ x) ∧
    (∀ z : Cube, z i = y i → z j = 1 → y ≤ z) at corners
  have hlower : fiber {i, j} (restrict {i, j} x) = face i b \ U := by
    ext z
    rw [mem_pair_fiber, hxi, hxj]
    change (z i = b ∧ z j = 0) ↔ z i = b ∧ z ∉ U
    refine and_congr_right fun hzi => ⟨?_, ?_⟩
    · intro hzj hzU
      exact hx.2 (hU (corners.1 z (hzi.trans hxi.symm) hzj) hzU)
    · intro hzU
      rcases bit_cases (z j) with hzj | hzj
      · exact hzj
      · exact (hzU (hU (corners.2 z (hzi.trans hyi.symm) hzj) hy.2)).elim
  have hupper : fiber {i, j} (restrict {i, j} y) = face i b ∩ U := by
    ext z
    rw [mem_pair_fiber, hyi, hyj]
    change (z i = b ∧ z j = 1) ↔ z i = b ∧ z ∈ U
    refine and_congr_right fun hzi => ⟨?_, ?_⟩
    · intro hzj
      exact hU (corners.2 z (hzi.trans hyi.symm) hzj) hy.2
    · intro hzU
      rcases bit_cases (z j) with hzj | hzj
      · exact (hx.2 (hU (corners.1 z (hzi.trans hxi.symm) hzj) hzU)).elim
      · exact hzj
  have hle : restrict {i, j} x ≤ restrict {i, j} y := by
    intro k
    change x k ≤ y k
    rcases Finset.mem_insert.mp k.property with hk | hk
    · rw [hk, hxy]
    · rw [Finset.mem_singleton.mp hk, hxj, hyj]
      decide
  exact no_opposite_fibers hr hle (by rwa [hlower]) (by rwa [hupper])

-- Majority is an upper coordinate face with one singleton exchanged for a doubleton.
private theorem majority_nonpos {p : PMF Cube} {h : Cube → ℝ} (hr : AntitoneMeans p h) :
    regionSum (centered p h) {x | majority x} ≤ 0 := by
  let M : Set Cube := {x | majority x}
  change regionSum (centered p h) M ≤ 0
  by_contra! hpos
  have hsplit := regionSum_split (centered p h) Set.univ M
  rw [Set.univ_inter, centered_total] at hsplit
  have hneg : regionSum (centered p h) (Set.univ \ M) < 0 := by linarith
  obtain ⟨x, hx, hsx⟩ := exists_neg_of_regionSum_neg hneg
  obtain ⟨y, hy, hsy⟩ := exists_pos_of_regionSum_pos hpos
  have hnotle : ¬ x ≤ y := fun hle => no_opposite_points hr hle hsx hsy
  obtain ⟨_, i, _, _, hsingle, hdouble⟩ := opposite_majority_vertices x y hx.2 hy hnotle
  have hremoved : 0 ≤ centered p h (single i) := by
    by_contra! hn
    exact no_opposite_points hr hsingle hn hsy
  have hadded : centered p h (double i) ≤ 0 := by
    by_contra! hp
    exact no_opposite_points hr hdouble hsx hp
  have hexchange : M = (face i 1 \ {single i}) ∪ {double i} := by
    ext z
    change majority z ↔ (z i = 1 ∧ z ≠ single i) ∨ z = double i
    exact majority_exchange i z
  have hd : Disjoint (face i 1 \ {single i}) ({double i} : Set Cube) := by
    apply Set.disjoint_left.mpr
    intro z hz heq
    rw [Set.mem_singleton_iff] at heq
    have hzi : z i = 1 := hz.1
    rw [heq, (exchange_vertices i).2] at hzi
    exact (by decide : (0 : Fin 2) ≠ 1) hzi
  have hkeep : face i 1 ∩ ({single i} : Set Cube) = {single i} := by
    apply Set.inter_eq_right.mpr
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    show z i = 1
    rw [hz, (exchange_vertices i).1]
  have hface := regionSum_split (centered p h) (face i 1) {single i}
  rw [hkeep, regionSum_singleton] at hface
  rw [hexchange, regionSum_union (centered p h) hd, regionSum_singleton] at hpos
  linarith only [hpos, hface, hremoved, hadded, upper_face_nonpos hr i]

/-- Antitone means on comparable positive coordinate fibers of a three-bit law
give a nonpositive globally centered sum on every upper set. -/
theorem centered_sum_nonpos_of_antitone_fiber_means (p : PMF (Fin 3 → Fin 2))
    (h : (Fin 3 → Fin 2) → ℝ)
    (hreg : ∀ (T : Finset (Fin 3)) (a b : T → Fin 2), a ≤ b →
      0 < fiberMass p T a → 0 < fiberMass p T b → fiberMean p h T b ≤ fiberMean p h T a)
    (U : Set (Fin 3 → Fin 2)) (hU : IsUpperSet U) :
    ∑ x ∈ U.toFinset, (p x).toReal * (h x - ∑ y, (p y).toReal * h y) ≤ 0 := by
  change regionSum (centered p h) U ≤ 0
  by_cases hcontained : ∃ i : Fin 3, U ⊆ face i 1
  · obtain ⟨i, hi⟩ := hcontained
    by_contra! hp
    have htrace : face i 1 ∩ U = U := Set.inter_eq_right.mpr hi
    have hsplit := regionSum_split (centered p h) (face i 1) U
    rw [htrace] at hsplit
    have hn : regionSum (centered p h) (face i 1 \ U) < 0 := by
      linarith only [hp, hsplit, upper_face_nonpos hreg i]
    exact no_opposite_face_parts hreg hU i 1 hn (htrace.symm ▸ hp)
  by_cases hcontains : ∃ i : Fin 3, face i 1 ⊆ U
  · obtain ⟨i, hi⟩ := hcontains
    by_contra! hp
    have hcomp : (Set.univ : Set Cube) \ U = face i 0 \ U := by
      ext x
      change (x ∈ (Set.univ : Set Cube) ∧ x ∉ U) ↔ x i = 0 ∧ x ∉ U
      refine ⟨fun hx => ⟨?_, hx.2⟩, fun hx => ⟨Set.mem_univ _, hx.2⟩⟩
      rcases bit_cases (x i) with hz | ho
      · exact hz
      · exact (hx.2 (hi ho)).elim
    have hsplit := regionSum_split (centered p h) Set.univ U
    rw [Set.univ_inter, hcomp, centered_total] at hsplit
    have hn : regionSum (centered p h) (face i 0 \ U) < 0 := by linarith
    have htrace := regionSum_split (centered p h) (face i 0) U
    have htotal := face_totals (p := p) (h := h) i
    have hpos : 0 < regionSum (centered p h) (face i 0 ∩ U) := by
      linarith only [hn, htrace, htotal, upper_face_nonpos hreg i]
    exact no_opposite_face_parts hreg hU i 0 hn hpos
  -- With neither face reduction applicable, all singletons are out and all doubletons are in.
  have hbottom : (fun _ => 0) ∉ U := fun hx =>
    hcontains ⟨0, fun z _ => hU (cube_bounds z).1 hx⟩
  have htop : (fun _ => 1) ∈ U := by
    by_contra ht
    exact hcontained ⟨0, fun z hz => (ht (hU (cube_bounds z).2 hz)).elim⟩
  have hsingle (i : Fin 3) : single i ∉ U := fun hi =>
    hcontains ⟨i, fun z hz => hU ((single_le_iff i z).mpr hz) hi⟩
  have hdouble (i : Fin 3) : double i ∈ U := by
    by_contra hi
    apply hcontained
    refine ⟨i, fun z hz => ?_⟩
    rcases bit_cases (z i) with hzero | hone
    · exact (hi (hU ((le_double_iff i z).mpr hzero) hz)).elim
    · exact hone
  have hmajority : U = {x | majority x} := by
    ext z
    change z ∈ U ↔ majority z
    rw [majority_vertices]
    constructor
    · intro hz
      rcases cube_vertices z with hzero | hone | ⟨i, hi⟩ | ⟨i, hi⟩
      · exact (hbottom (hzero ▸ hz)).elim
      · exact Or.inl hone
      · exact (hsingle i (hi ▸ hz)).elim
      · exact Or.inr ⟨i, hi⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact htop
      · exact hdouble i
  rw [hmajority]
  exact majority_nonpos hreg

end

end D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans
