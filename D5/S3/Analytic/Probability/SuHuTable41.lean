/- GID: D5/S3/Analytic/Probability/SuHuTable41
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/SuHuTable41
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=bounded-enumeration; basis=terminal=gid:D5/S3/Analytic/Probability/SuHuTable41.table_attainment
   digest: A strictly positive full-NRD ternary law with positive covariance on disjoint events. -/

import D5.S3.Analytic.Probability.FiniteNegativeRegression
import Mathlib.Tactic.NormNum

/-! Su and Hu, arXiv:2609.23313v1, Table 4.1 and Proposition 4.2. -/

set_option autoImplicit false

open Finset hiding expect
open scoped ENNReal

namespace D5.S3.Analytic.Probability.SuHuTable41

open FiniteNegativeRegression

/-- The four ternary coordinates in the published table. -/
abbrev State := Fin 4 → Fin 3

/-- Table 4.1 in lexicographic order within each pair of coordinates. -/
def table : Fin 9 → Fin 9 → ℕ :=
  ![![1, 93, 959, 93, 1708, 397, 959, 397, 209],
    ![93, 572, 1783, 572, 2247, 450, 1783, 450, 238],
    ![959, 1783, 3918, 1783, 5065, 857, 3918, 857, 439],
    ![93, 572, 1783, 572, 2247, 450, 1783, 450, 238],
    ![1708, 2247, 5065, 2247, 8193, 1275, 5065, 1275, 659],
    ![397, 450, 857, 450, 1275, 187, 857, 187, 93],
    ![959, 1783, 3918, 1783, 5065, 857, 3918, 857, 439],
    ![397, 450, 857, 450, 1275, 187, 857, 187, 93],
    ![209, 238, 439, 238, 659, 93, 439, 93, 1]]

private def pairIndex (a b : Fin 3) : Fin 9 :=
  ⟨3 * a.val + b.val, by omega⟩

/-- The integer entry for a full coordinate tuple. -/
def weight (x : State) : ℕ := table (pairIndex (x 0) (x 1)) (pairIndex (x 2) (x 3))

private theorem weight_sum : ∑ x : State, weight x = 99999 := by decide
set_option maxHeartbeats 3000000 in
private theorem weight_pos : ∀ x : State, 0 < weight x := by decide

/-- The weights of Table 4.1 divided by their total. -/
noncomputable def tablePMF : PMF State := PMF.ofFintype (fun x => (weight x : ℝ≥0∞) / 99999) (by
  rw [← ENNReal.sum_div, ← Nat.cast_sum, weight_sum]
  exact ENNReal.div_self (by norm_num) (by norm_num))

private theorem table_real (x : State) : (tablePMF x).toReal = (weight x : ℝ) / 99999 := by
  simp [tablePMF, ENNReal.toReal_div]

private def Left : Finset (Fin 4) := {0, 1}
private def Right : Finset (Fin 4) := {2, 3}

private def leftEvent (x : State) : Prop := 1 ≤ x 0 ∧ 1 ≤ x 1
private def rightEvent (x : State) : Prop := 1 ≤ x 2 ∧ 1 ≤ x 3

private instance (x : State) : Decidable (leftEvent x) := inferInstanceAs (Decidable (_ ∧ _))
private instance (x : State) : Decidable (rightEvent x) := inferInstanceAs (Decidable (_ ∧ _))

private def leftTest (a : (i : Left) → Fin 3) : ℝ :=
  if 1 ≤ a ⟨0, by decide⟩ ∧ 1 ≤ a ⟨1, by decide⟩ then 1 else 0

private def rightTest (a : (i : Right) → Fin 3) : ℝ :=
  if 1 ≤ a ⟨2, by decide⟩ ∧ 1 ≤ a ⟨3, by decide⟩ then 1 else 0

private theorem test_mono {β : Type*} [Preorder β] (f g : β → Fin 3)
    (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun x => if 1 ≤ f x ∧ 1 ≤ g x then (1 : ℝ) else 0) := by
  intro a b hab
  by_cases h : 1 ≤ f a ∧ 1 ≤ g a
  · simp [h, h.1.trans (hf hab), h.2.trans (hg hab)]
  · by_cases h' : 1 ≤ f b ∧ 1 ≤ g b <;> simp [h, h']

private theorem event_expect (P : State → Prop) [DecidablePred P] :
    expect tablePMF (fun x => if P x then 1 else 0) =
      ((∑ x : State, if P x then weight x else 0 : ℕ) : ℝ) / 99999 := by
  rw [expect, Nat.cast_sum, Finset.sum_div]
  apply sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [table_real, hx]

private theorem eleft : ∑ x : State, (if leftEvent x then weight x else 0) = 39649 := by decide
private theorem eright : ∑ x : State, (if rightEvent x then weight x else 0) = 39649 := by decide
private theorem eboth :
    ∑ x : State, (if leftEvent x ∧ rightEvent x then weight x else 0) = 15732 := by decide

private theorem table_cov : cov tablePMF (leftTest ∘ project Left) (rightTest ∘ project Right) =
    1141067 / 9999800001 := by
  have hl : expect tablePMF (leftTest ∘ project Left) = (39649 : ℝ) / 99999 := by
    change expect tablePMF (fun x => if leftEvent x then 1 else 0) = _
    rw [event_expect, eleft]
    norm_num
  have hr : expect tablePMF (rightTest ∘ project Right) = (39649 : ℝ) / 99999 := by
    change expect tablePMF (fun x => if rightEvent x then 1 else 0) = _
    rw [event_expect, eright]
    norm_num
  have hb : expect tablePMF (fun x => leftTest (project Left x) * rightTest (project Right x)) =
      (15732 : ℝ) / 99999 := by
    have he : (fun x => leftTest (project Left x) * rightTest (project Right x)) =
        (fun x => if leftEvent x ∧ rightEvent x then (1 : ℝ) else 0) := by
      funext x
      change (if leftEvent x then (1 : ℝ) else 0) * (if rightEvent x then 1 else 0) = _
      by_cases h : leftEvent x <;> by_cases h' : rightEvent x <;> simp [h, h']
    rw [he, event_expect, eboth]
    norm_num
  rw [cov, hl, hr]
  change expect tablePMF (fun x => leftTest (project Left x) * rightTest (project Right x)) -
      (39649 : ℝ) / 99999 * (39649 / 99999) = _
  rw [hb]
  norm_num

/-- Table 4.1 is strictly positive and has the stated positive covariance on disjoint upper events. -/
theorem table_positive_covariance :
    (∀ x : State, 0 < tablePMF x) ∧
      ∃ (I J : Finset (Fin 4)), Disjoint I J ∧
        ∃ (f : (I → Fin 3) → ℝ) (g : (J → Fin 3) → ℝ),
          Monotone f ∧ Monotone g ∧ cov tablePMF (f ∘ project I) (g ∘ project J) =
            1141067 / 9999800001 ∧ 0 < cov tablePMF (f ∘ project I) (g ∘ project J) := by
  refine ⟨?_, Left, Right, by decide, leftTest, rightTest, ?_, ?_, table_cov, ?_⟩
  · intro x
    have h : 0 < (tablePMF x).toReal := by
      rw [table_real]
      exact div_pos (Nat.cast_pos.mpr (weight_pos x)) (by norm_num)
    exact (ENNReal.toReal_pos_iff.mp h).1
  · exact test_mono _ _ (fun _ _ hab => hab _) (fun _ _ hab => hab _)
  · exact test_mono _ _ (fun _ _ hab => hab _) (fun _ _ hab => hab _)
  · rw [table_cov]
    norm_num

private def decode (k : Fin 81) : State := fun i =>
  ⟨k.val / 3 ^ i.val % 3, Nat.mod_lt _ (by decide)⟩

private def encode (x : State) : Fin 81 :=
  ⟨(x 0).val + 3 * (x 1).val + 9 * (x 2).val + 27 * (x 3).val, by omega⟩

set_option maxHeartbeats 3000000 in
private theorem decode_encode : ∀ x, decode (encode x) = x := by decide

private theorem encode_decode : ∀ k, encode (decode k) = k := by decide

private def stateEquiv : Fin 81 ≃ State where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

private def mask (J : Finset (Fin 4)) (x : State) : State :=
  fun i => if i ∈ J then x i else 0

private def comp (J : Finset (Fin 4)) : Finset (Fin 4) := univ \ J

private def indices : List (Fin 81) := List.finRange 81

private def keys (J : Finset (Fin 4)) : List (Fin 81) :=
  indices.filter fun k => encode (mask J (decode k)) == k

private def below (a b : Fin 81) : Bool :=
  (List.finRange 4).all (fun i => decide (decode a i ≤ decode b i))

private theorem below_iff {a b : Fin 81} : below a b = true ↔ decode a ≤ decode b := by
  simp [below, List.all_eq_true, Pi.le_def]

private def upperLists (xs : List (Fin 81)) : List (List (Fin 81)) :=
  match xs with
  | [] => [[]]
  | x :: tail =>
    let rest := upperLists tail
    (rest.filter fun u => u.all fun y => !(below y x)) ++
      (rest.filter fun u => tail.all fun y => !below x y || u.contains y).map (x :: ·)

private theorem upperLists_complete (xs : List (Fin 81)) (P : Fin 81 → Bool)
    (h : ∀ a b, below a b = true → P a = true → P b = true) :
    xs.filter P ∈ upperLists xs := by
  induction xs with
  | nil => simp [upperLists]
  | cons x tail ih =>
    cases hx : P x
    · simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte, upperLists]
      apply List.mem_append_left
      refine List.mem_filter.mpr ⟨ih, List.all_eq_true.mpr ?_⟩
      intro y hy
      simp only [Bool.not_eq_true']
      cases hle : below y x
      · rfl
      · have hn := h y x hle (List.mem_filter.mp hy).2
        simp [hx] at hn
    · simp only [List.filter_cons, hx, ↓reduceIte, upperLists]
      apply List.mem_append_right
      refine List.mem_map.mpr ⟨tail.filter P, List.mem_filter.mpr ⟨ih, ?_⟩, rfl⟩
      apply List.all_eq_true.mpr
      intro y hy
      cases hle : below x y
      · simp
      · simp [List.mem_filter.mpr ⟨hy, h x y hle hx⟩]

private def rows (J : Finset (Fin 4)) (a : Fin 81) : List (Fin 81 × ℕ) :=
  (indices.filter fun k => encode (mask J (decode k)) == a).map fun k =>
    (encode (mask (comp J) (decode k)), weight (decode k))

private def total (r : List (Fin 81 × ℕ)) : ℕ := (r.map Prod.snd).sum

private def upperWeight (U : List (Fin 81)) (r : List (Fin 81 × ℕ)) : ℕ :=
  (r.map fun (k,n) => if U.contains k then n else 0).sum

private def checkRows (J : Finset (Fin 4)) : Bool :=
  let rs := (keys J).map fun a => (a, rows J a)
  let us := upperLists (keys (comp J))
  rs.all fun (a, ra) =>
    rs.all fun (b, rb) =>
      if a != b && below a b then
        let ma := total ra
        let mb := total rb
        us.all fun u => decide (upperWeight u rb * ma ≤ upperWeight u ra * mb)
      else true

private def maskOf (k : Fin 16) : Finset (Fin 4) :=
  univ.filter fun i => k.val.testBit i.val

private theorem maskOf_surj : Function.Surjective maskOf := by decide

private theorem mem_keys (J : Finset (Fin 4)) (x : State) :
    encode (mask J x) ∈ keys J := by
  apply List.mem_filter.mpr
  refine ⟨by simp [indices], ?_⟩
  rw [decode_encode]
  have h : mask J (mask J x) = mask J x := by
    funext i
    by_cases hi : i ∈ J <;> simp [mask, hi]
  simp [h]

private theorem rows_mem (J : Finset (Fin 4)) (a : Fin 81) (ha : a ∈ keys J) :
    (a, rows J a) ∈ (keys J).map (fun b => (b, rows J b)) :=
  List.mem_map.mpr ⟨a, ha, rfl⟩

private theorem readCheck {J : Finset (Fin 4)} (h : checkRows J = true)
    {a b : Fin 81} (ha : a ∈ keys J) (hb : b ∈ keys J) (hle : below a b = true)
    {u : List (Fin 81)} (hu : u ∈ upperLists (keys (comp J))) :
    upperWeight u (rows J b) * total (rows J a) ≤
      upperWeight u (rows J a) * total (rows J b) := by
  by_cases he : a = b
  · simp [he]
  unfold checkRows at h
  have h1 := (List.all_eq_true.mp h) _ (rows_mem J a ha)
  have h2 := (List.all_eq_true.mp h1) _ (rows_mem J b hb)
  simp [he, hle] at h2
  exact h2 _ hu

private def place (J : Finset (Fin 4)) (a : J → Fin 3) : State :=
  fun i => if h : i ∈ J then a ⟨i, h⟩ else 0

private theorem mask_eq_place (J : Finset (Fin 4)) (x : State) (a : J → Fin 3) :
    mask J x = place J a ↔ project J x = a := by
  constructor
  · intro h
    funext i
    simpa [mask, place, i.property, project] using congrFun h i
  · intro h
    funext i
    by_cases hi : i ∈ J
    · simpa [mask, place, hi, project] using congrFun h ⟨i, hi⟩
    · simp [mask, place, hi]

private theorem place_mono (J : Finset (Fin 4)) : Monotone (place J) := by
  intro a b h i
  by_cases hi : i ∈ J
  · simpa [place, hi] using h ⟨i, hi⟩
  · simp [place, hi]

private theorem place_key (J : Finset (Fin 4)) (a : J → Fin 3) :
    encode (place J a) ∈ keys J := by
  have h : mask J (place J a) = place J a := by
    funext i
    by_cases hi : i ∈ J <;> simp [mask, place, hi]
  rw [← h]
  exact mem_keys _ _

private theorem check_keys_le (J : Finset (Fin 4)) {a b : J → Fin 3} (hab : a ≤ b) :
    below (encode (place J a)) (encode (place J b)) = true := by
  apply below_iff.mpr
  rw [decode_encode, decode_encode]
  exact place_mono J hab

private theorem cut_sum {α : Type*} (xs : List α) (P : α → Bool) (f : α → ℕ) :
    ((xs.filter P).map f).sum = (xs.map (fun x => if P x then f x else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : P x <;> simp [hx, ih]

private theorem sum_indices (f : State → ℕ) :
    (indices.map (f ∘ decode)).sum = ∑ x : State, f x := by
  rw [indices, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  exact Fintype.sum_equiv stateEquiv (f ∘ decode) f (fun _ => rfl)

private theorem total_rows (J : Finset (Fin 4)) (a : J → Fin 3) :
    total (rows J (encode (place J a))) =
      ∑ x : State, if project J x = a then weight x else 0 := by
  unfold total rows
  rw [List.map_map, cut_sum]
  rw [← sum_indices]
  congr 1
  apply List.map_congr_left
  intro k _
  have he :
      (encode (mask J (decode k)) == encode (place J a)) = true ↔ project J (decode k) = a := by
    rw [beq_iff_eq]
    exact stateEquiv.symm.injective.eq_iff.trans (mask_eq_place J (decode k) a)
  simp only [Function.comp_apply]
  by_cases h : project J (decode k) = a
  · rw [ite_eq_left (he.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hh => h (he.mp hh)), ite_eq_right h]

open scoped Classical in
private theorem upper_rows {I J : Finset (Fin 4)} (hd : Disjoint I J)
    (U : Set (I → Fin 3)) (a : J → Fin 3) :
    let P : Fin 81 → Bool := fun k => decide (project I (decode k) ∈ U)
    let u := (keys (comp J)).filter P
    upperWeight u (rows J (encode (place J a))) =
      ∑ x : State, if project J x = a ∧ project I x ∈ U then weight x else 0 := by
  intro P u
  unfold upperWeight rows
  rw [List.map_map, cut_sum]
  rw [← sum_indices]
  congr 1
  apply List.map_congr_left
  intro k _
  have he :
      (encode (mask J (decode k)) == encode (place J a)) = true ↔ project J (decode k) = a := by
    rw [beq_iff_eq]
    exact stateEquiv.symm.injective.eq_iff.trans (mask_eq_place J (decode k) a)
  have hproj (x : State) : project I (mask (comp J) x) = project I x := by
    funext i
    have hi : (i : Fin 4) ∈ comp J := by
      simp only [comp, mem_sdiff, mem_univ, true_and]
      exact fun hj => Finset.disjoint_left.mp hd i.property hj
    simp [project, mask, hi]
  have hk : u.contains (encode (mask (comp J) (decode k))) = true ↔
      project I (decode k) ∈ U := by
    rw [List.contains_iff_mem, List.mem_filter]
    refine and_iff_right_of_imp (fun _ => mem_keys _ _) |>.trans ?_
    simp [P, decode_encode, hproj]
  simp only [Function.comp_apply]
  by_cases h : project J (decode k) = a
  · rw [ite_eq_left (he.mpr h)]
    by_cases hh : project I (decode k) ∈ U
    · rw [ite_eq_left (hk.mpr hh), ite_eq_left ⟨h, hh⟩]
    · rw [ite_eq_right (fun h' => hh (hk.mp h')), ite_eq_right (fun h' => hh h'.2)]
  · rw [ite_eq_right (fun hh => h (he.mp hh))]
    simp [h]

open scoped Classical in
private theorem table_upper (hcheck : ∀ J : Finset (Fin 4), J ≠ ∅ → checkRows J = true)
    (I J : Finset (Fin 4)) (hd : Disjoint I J) (U : Set (I → Fin 3)) (hU : IsUpperSet U)
    (a b : J → Fin 3) (hab : a ≤ b)
    (ha : 0 < mass tablePMF (project J) a) (hb : 0 < mass tablePMF (project J) b) :
    cond tablePMF (project J) b (event U ∘ project I) ≤
      cond tablePMF (project J) a (event U ∘ project I) := by
  by_cases hJ : J = ∅
  · have he : a = b := by
      funext i
      exact False.elim (by simpa [hJ] using i.property)
    rw [he]
  let P : Fin 81 → Bool := fun k => decide (project I (decode k) ∈ U)
  let u := (keys (comp J)).filter P
  have hu : u ∈ upperLists (keys (comp J)) := by
    apply upperLists_complete
    intro c d hcd hc
    apply decide_eq_true
    exact hU (fun i => below_iff.mp hcd i) (of_decide_eq_true hc)
  have hcode := readCheck (hcheck J hJ) (place_key J a) (place_key J b)
    (check_keys_le J hab) hu
  rw [total_rows, total_rows, upper_rows hd U b, upper_rows hd U a] at hcode
  let M (c : J → Fin 3) := ∑ x : State, if project J x = c then weight x else 0
  let N (c : J → Fin 3) := ∑ x : State, if project J x = c ∧ project I x ∈ U then weight x else 0
  change N b * M a ≤ N a * M b at hcode
  have hm (c : J → Fin 3) : mass tablePMF (project J) c = (M c : ℝ) / 99999 := by
    rw [mass, fiberSum, sum_filter]
    simp only [M, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, sum_div]
    apply sum_congr rfl
    intro x _
    by_cases hx : project J x = c <;> simp [hx, table_real]
  have hn (c : J → Fin 3) :
      fiberSum (project J) c (fun x => (tablePMF x).toReal * (event U ∘ project I) x) =
        (N c : ℝ) / 99999 := by
    rw [fiberSum, sum_filter]
    simp only [N, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, sum_div]
    apply sum_congr rfl
    intro x _
    by_cases hx : project J x = c <;> by_cases hy : project I x ∈ U <;>
      simp [event, hx, hy, table_real]
  simp only [FiniteNegativeRegression.cond, hm, hn]
  rw [hm] at ha hb
  apply (div_le_div_iff₀ hb ha).mpr
  have hh : (N b : ℝ) * (M a : ℝ) ≤ (N a : ℝ) * (M b : ℝ) := by exact_mod_cast hcode
  calc
    (N b : ℝ) / 99999 * ((M a : ℝ) / 99999) =
        ((N b : ℝ) * (M a : ℝ)) / (99999 * 99999) := by ring
    _ ≤ ((N a : ℝ) * (M b : ℝ)) / (99999 * 99999) :=
      div_le_div_of_nonneg_right hh (by norm_num)
    _ = (N a : ℝ) / 99999 * ((M b : ℝ) / 99999) := by ring


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask1 : checkRows (maskOf 1) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask2 : checkRows (maskOf 2) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask3 : checkRows (maskOf 3) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask4 : checkRows (maskOf 4) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask5 : checkRows (maskOf 5) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask6 : checkRows (maskOf 6) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask7 : checkRows (maskOf 7) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask8 : checkRows (maskOf 8) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask9 : checkRows (maskOf 9) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask10 : checkRows (maskOf 10) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask11 : checkRows (maskOf 11) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask12 : checkRows (maskOf 12) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask13 : checkRows (maskOf 13) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask14 : checkRows (maskOf 14) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem checkMask15 : checkRows (maskOf 15) = true := by decide +kernel

private theorem check_all (J : Finset (Fin 4)) (hJ : J ≠ ∅) : checkRows J = true := by
  obtain ⟨k, rfl⟩ := maskOf_surj J
  fin_cases k
  · exact (hJ (by decide)).elim
  · exact checkMask1
  · exact checkMask2
  · exact checkMask3
  · exact checkMask4
  · exact checkMask5
  · exact checkMask6
  · exact checkMask7
  · exact checkMask8
  · exact checkMask9
  · exact checkMask10
  · exact checkMask11
  · exact checkMask12
  · exact checkMask13
  · exact checkMask14
  · exact checkMask15

/-- The literal normalized law satisfies full negative regression. -/
private theorem table_fullNRD : FullNRD tablePMF := by
  apply fullNRD_of_upper
  intro I J hd U hU a b hab ha hb
  have he : @Pi.instFintype (Fin 4) (fun _ => Fin 3)
      (fun a b => Classical.propDecidable (a = b)) _ _ = (inferInstance : Fintype State) :=
    Subsingleton.elim _ _
  rw [he] at ha hb ⊢
  exact table_upper check_all I J hd U hU a b hab ha hb


private theorem table_support_size : marginalProduct tablePMF = 81 := by
  classical
  have hs (i : Fin 4) : (tablePMF.map (fun x => x i)).support = Set.univ := by
    ext a
    refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨fun _ => a, (PMF.mem_support_iff _ _).mpr
      (ne_of_gt (table_positive_covariance.1 (fun _ => a))), rfl⟩
  unfold marginalProduct
  calc
    _ = ∏ _i : Fin 4, (3 : ℕ) := by
      apply prod_congr rfl
      intro i _
      rw [hs]
      simp
    _ = 81 := by decide

/-- Table 4.1 attains the threshold with full support and violates negative association. -/
theorem table_attainment :
    (∀ x : State, 0 < tablePMF x) ∧ marginalProduct tablePMF = 81 ∧
      FullNRD tablePMF ∧ ¬ NA tablePMF := by
  obtain ⟨hpos, I, J, hd, f, g, hf, hg, _, hc⟩ := table_positive_covariance
  refine ⟨hpos, table_support_size, table_fullNRD, fun h => ?_⟩
  have hc' := h I J hd f g hf hg
  have he : @Pi.instFintype (Fin 4) (fun _ => Fin 3)
      (fun a b => Classical.propDecidable (a = b)) _ _ = (inferInstance : Fintype State) :=
    Subsingleton.elim _ _
  rw [he] at hc'
  exact (not_lt_of_ge hc') hc

end D5.S3.Analytic.Probability.SuHuTable41
