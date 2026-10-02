/- GID: D5/S3/Arith/FibonacciAtomic/ScalarSoftmaxTreeObstruction
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ScalarSoftmaxTreeObstruction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Scalar bilinear trees with affine softmax heads have uniform three-class risk floors. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.Arith.FibonacciAtomic.TreeMessageRealization
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ScalarSoftmaxTreeObstruction

open LiteralWindowEnd (Window first last)
open TreeMessageRealization (Full leaves Implementation evaluate)

open scoped BigOperators

/-- Three initial windows and an arbitrary tail. Positions start at zero. -/
abbrev Word (m : ℕ) := FirstRejectionCutCapacity.Word (m + 2)

/-- The first two rejecting seams receive labels one and two; all later
rejections, terminal failures and acceptance receive label zero. -/
noncomputable def coarse {m : ℕ} (w : Word m) : Fin 3 := by
  classical
  exact if FirstRejectionCutCapacity.task w =
      ((⟨0, by omega⟩ : Fin (m + 3)) : FirstRejectionCutCapacity.Label (m + 2)) then 1
    else if FirstRejectionCutCapacity.task w =
      ((⟨1, by omega⟩ : Fin (m + 3)) : FirstRejectionCutCapacity.Label (m + 2)) then 2
    else 0

/-- All messages live in the real line. A zero-dimensional message embeds as
the constant zero coordinate. Each merger is separately linear on the whole
ambient real line and has no additional input or affine constant. -/
def scalarImplementation {m : ℕ} (f : Fin (m + 3) → Window → ℝ)
    (B : TreeMessageRealization.Tree (Fin (m + 3)) → TreeMessageRealization.Tree (Fin (m + 3)) → ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) :
    Implementation (fun _ : Fin (m + 3) => Window) where
  Message := fun _ => ℝ
  empty := 0
  encode := fun i _ _ => f i
  combine := fun l r x y => B l r x y

def logit (u v : Fin 3 → ℝ) (z : ℝ) (y : Fin 3) : ℝ := u y * z + v y

noncomputable def maxima (u v : Fin 3 → ℝ) (z : ℝ) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun y => ∀ j, logit u v z j ≤ logit u v z y)

def LegalChoice (choose : Finset (Fin 3) → Fin 3) : Prop :=
  ∀ S, S.Nonempty → choose S ∈ S

noncomputable def prediction (u v : Fin 3 → ℝ)
    (choose : Finset (Fin 3) → Fin 3) (z : ℝ) : Fin 3 := choose (maxima u v z)

noncomputable def probability (u v : Fin 3 → ℝ) (z : ℝ) (y : Fin 3) : ℝ :=
  Real.exp (logit u v z y) / ∑ j, Real.exp (logit u v z j)

noncomputable def errorRisk {m : ℕ} (z : Word m → ℝ) (u v : Fin 3 → ℝ)
    (choose : Finset (Fin 3) → Fin 3) : ℝ := by
  classical
  exact 𝔼 w, if prediction u v choose (z w) = coarse w then (0 : ℝ) else 1

noncomputable def squareRisk {m : ℕ} (z : Word m → ℝ) (u v : Fin 3 → ℝ) : ℝ := by
  classical
  exact 𝔼 w, ∑ y, (probability u v (z w) y - if coarse w = y then 1 else 0) ^ 2

noncomputable def logRisk {m : ℕ} (z : Word m → ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  𝔼 w, -Real.log (probability u v (z w) (coarse w))

-- The decision-fiber geometry and uniform averaging share one proof scope.
set_option maxHeartbeats 1600000 in
/-- Uniform risk floors for every fully labelled scalar bilinear tree. The
parameter m is the number of windows after the first three, so n=m+3. -/
theorem result (m : ℕ) (t : TreeMessageRealization.Tree (Fin (m + 3))) (ht : Full t)
    (hall : leaves t = Finset.univ) (f : Fin (m + 3) → Window → ℝ)
    (B : TreeMessageRealization.Tree (Fin (m + 3)) → TreeMessageRealization.Tree (Fin (m + 3)) → ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)
    (u v : Fin 3 → ℝ) :
    (∀ choose, LegalChoice choose →
      (1 / 125 : ℝ) ≤ errorRisk (evaluate (scalarImplementation f B) t) u v choose) ∧
    (1 / 250 : ℝ) ≤ squareRisk (evaluate (scalarImplementation f B) t) u v ∧
    Real.log 2 / 125 ≤ logRisk (evaluate (scalarImplementation f B) t) u v := by
  classical
  letI : Nonempty Window := ⟨.zero⟩
  have scalar (A : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) (x y : ℝ) :
      A x y = A 1 1 * x * y := by
    calc
      A x y = A (x • (1 : ℝ)) (y • (1 : ℝ)) := by simp
      _ = x • (y • A 1 1) := by rw [LinearMap.map_smul₂, LinearMap.map_smul]
      _ = A 1 1 * x * y := by simp only [smul_eq_mul]; ring
  have factorize (s : TreeMessageRealization.Tree (Fin (m + 3))) (hs : Full s) :
      ∃ κ : ℝ, ∀ w : Word m,
        evaluate (scalarImplementation f B) s w = κ * ∏ i ∈ leaves s, f i (w i) := by
    letI : DecidableEq (Fin (m + 3)) := Classical.decEq _
    induction s with
    | nil => simp [Full] at hs
    | node a l r hl hr =>
      cases a with
      | some i => exact ⟨1, by intro w; simp [evaluate, scalarImplementation, leaves]⟩
      | none =>
        obtain ⟨κl, hκl⟩ := hl hs.1
        obtain ⟨κr, hκr⟩ := hr hs.2.1
        refine ⟨B l r 1 1 * κl * κr, ?_⟩
        intro w
        change B l r (evaluate (scalarImplementation f B) l w)
          (evaluate (scalarImplementation f B) r w) =
          B l r 1 1 * κl * κr * ∏ i ∈ leaves (.node none l r), f i (w i)
        rw [hκl, hκr]
        rw [scalar (B l r) (κl * ∏ i ∈ leaves l, f i (w i))
          (κr * ∏ i ∈ leaves r, f i (w i))]
        rw [show leaves (.node none l r) = leaves l ∪ leaves r by rfl,
          Finset.prod_union hs.2.2]
        ring
  obtain ⟨κ, hκ⟩ := factorize t ht
  have maxima_nonempty (a : ℝ) : (maxima u v a).Nonempty := by
    obtain ⟨y, _, hy⟩ := Finset.exists_max_image Finset.univ (logit u v a)
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
    exact ⟨y, by simp [maxima, hy]⟩
  have winner (choose : Finset (Fin 3) → Fin 3) (hc : LegalChoice choose)
      (a : ℝ) : ∀ j, logit u v a j ≤ logit u v a (prediction u v choose a) := by
    have h := hc _ (maxima_nonempty a)
    simpa [maxima, prediction] using h
  have interval (choose : Finset (Fin 3) → Fin 3) (hc : LegalChoice choose)
      (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (y : Fin 3)
      (ha : prediction u v choose a = y) (hc' : prediction u v choose c = y) :
      prediction u v choose b = y := by
    rcases hab.eq_or_lt with rfl | hab
    · exact ha
    rcases hbc.eq_or_lt with rfl | hbc
    · exact hc'
    have hya := winner choose hc a
    have hyc := winner choose hc c
    rw [ha] at hya
    rw [hc'] at hyc
    have mid (j : Fin 3) : logit u v b j ≤ logit u v b y := by
      have hja := hya j
      have hjc := hyc j
      dsimp [logit] at *
      by_cases hu : u j ≤ u y
      · nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hab.le)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hu))
          (sub_nonneg.mpr hbc.le)]
    have persistent (j : Fin 3) (hj : j ∈ maxima u v b) :
        j ∈ maxima u v a ∧ j ∈ maxima u v c := by
      have hj' : ∀ i, logit u v b i ≤ logit u v b j := by simpa [maxima] using hj
      have he : logit u v b j = logit u v b y := le_antisymm (mid j) (hj' y)
      have hu : u j = u y := by
        have hja := hya j
        have hjc := hyc j
        dsimp [logit] at *
        rcases lt_trichotomy (u j) (u y) with hu | hu | hu
        · nlinarith [mul_pos (sub_pos.mpr hu) (sub_pos.mpr hab)]
        · exact hu
        · nlinarith [mul_pos (sub_pos.mpr hu) (sub_pos.mpr hbc)]
      have hv : v j = v y := by dsimp [logit] at he; rw [hu] at he; linarith
      constructor
      · simp only [maxima, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i
        simpa only [logit, hu, hv] using hya i
      · simp only [maxima, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i
        simpa only [logit, hu, hv] using hyc i
    have converse (j : Fin 3) (hja : j ∈ maxima u v a)
        (hjc : j ∈ maxima u v c) : j ∈ maxima u v b := by
      have hja' : ∀ i, logit u v a i ≤ logit u v a j := by simpa [maxima] using hja
      have hjc' : ∀ i, logit u v c i ≤ logit u v c j := by simpa [maxima] using hjc
      have heq : logit u v b j = logit u v b y := by
        have hea := le_antisymm (hya j) (hja' y)
        have hec := le_antisymm (hyc j) (hjc' y)
        dsimp [logit] at *
        have huu : u j = u y := by
          rcases lt_trichotomy (u j) (u y) with hu | hu | hu
          · nlinarith only [hea, hec, mul_pos (sub_pos.mpr hu) (sub_pos.mpr (hab.trans hbc))]
          · exact hu
          · nlinarith only [hea, hec, mul_pos (sub_pos.mpr hu) (sub_pos.mpr (hab.trans hbc))]
        have hvv : v j = v y := by rw [huu] at hea; linarith only [hea]
        simp only [huu, hvv]
      simp only [maxima, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      rw [heq]
      exact mid i
    have hyb : y ∈ maxima u v b := by simp [maxima, mid]
    let j := prediction u v choose b
    have hjb : j ∈ maxima u v b := hc _ (maxima_nonempty b)
    by_contra hjy
    have hset : maxima u v a = maxima u v b ∨ maxima u v c = maxima u v b := by
      by_contra hn
      push Not at hn
      obtain ⟨p, hpa, hpb⟩ := Finset.exists_of_ssubset
        (Finset.ssubset_iff_subset_ne.mpr ⟨fun q hq => (persistent q hq).1, Ne.symm hn.1⟩)
      obtain ⟨q, hqc, hqb⟩ := Finset.exists_of_ssubset
        (Finset.ssubset_iff_subset_ne.mpr ⟨fun q hq => (persistent q hq).2, Ne.symm hn.2⟩)
      have hpj : p ≠ j := fun h => hpb (h ▸ hjb)
      have hpy : p ≠ y := fun h => hpb (h ▸ hyb)
      have hqj : q ≠ j := fun h => hqb (h ▸ hjb)
      have hqy : q ≠ y := fun h => hqb (h ▸ hyb)
      have hpq : p = q := by
        have hjy' : j.val ≠ y.val := fun h => hjy (Fin.ext h)
        simp only [ne_eq, Fin.ext_iff] at hpj hpy hqj hqy
        apply Fin.ext
        omega
      exact hpb (converse p hpa (hpq ▸ hqc))
    rcases hset with hset | hset
    · exact hjy (by simpa [j, prediction, hset] using ha)
    · exact hjy (by simpa [j, prediction, hset] using hc')
  have separated (d : ℝ → Fin 3)
      (hd : ∀ a b c y, a ≤ b → b ≤ c → d a = y → d c = y → d b = y)
      (a b c e : ℝ) (y z : Fin 3) (hyz : y ≠ z)
      (ha : d a = y) (hb : d b = y) (hc : d c = z) (he : d e = z) :
      (a < c ∧ a < e ∧ b < c ∧ b < e) ∨
      (c < a ∧ c < b ∧ e < a ∧ e < b) := by
    have orient (a b c e : ℝ) (y z : Fin 3) (hyz : y ≠ z)
        (ha : d a = y) (hb : d b = y) (hc : d c = z) (he : d e = z)
        (hac : a < c) : a < c ∧ a < e ∧ b < c ∧ b < e := by
      have hbc : b < c := by
        by_contra hn
        exact hyz ((hd a c b y hac.le (le_of_not_gt hn) ha hb).symm.trans hc)
      have hae : a < e := by
        by_contra hn
        exact hyz (ha.symm.trans (hd e a c z (le_of_not_gt hn) hac.le he hc))
      have hbe : b < e := by
        by_contra hn
        exact hyz ((hd a e b y hae.le (le_of_not_gt hn) ha hb).symm.trans he)
      exact ⟨hac, hae, hbc, hbe⟩
    rcases lt_trichotomy a c with hac | hac | hac
    · exact Or.inl (orient a b c e y z hyz ha hb hc he hac)
    · exact False.elim (hyz (ha.symm.trans (hac ▸ hc)))
    · exact Or.inr (orient c e a b z y (Ne.symm hyz) hc he ha hb hac)
  have scaled_interval (choose : Finset (Fin 3) → Fin 3) (hc : LegalChoice choose)
      (r a b c : ℝ) (y : Fin 3) (hab : a ≤ b) (hbc : b ≤ c)
      (ha : prediction u v choose (r * a) = y)
      (hc' : prediction u v choose (r * c) = y) :
      prediction u v choose (r * b) = y := by
    by_cases hr : 0 ≤ r
    · exact interval choose hc _ _ _ (mul_le_mul_of_nonneg_left hab hr)
        (mul_le_mul_of_nonneg_left hbc hr) y ha hc'
    · exact interval choose hc _ _ _ (mul_le_mul_of_nonpos_left hbc (le_of_not_ge hr))
        (mul_le_mul_of_nonpos_left hab (le_of_not_ge hr)) y hc' ha
  have crossing (choose : Finset (Fin 3) → Fin 3) (hc : LegalChoice choose)
      (x : Bool → Bool → ℝ) (s r : ℝ)
      (rows : ∀ a b, prediction u v choose (s * x a b) = if a then 1 else 0)
      (cols : ∀ a b, prediction u v choose (r * x a b) = if b then 2 else 0) : False := by
    have hrow := separated (fun z => prediction u v choose (s * z))
      (fun a b c y hab hbc ha hc' => scaled_interval choose hc s a b c y hab hbc ha hc')
      (x false false) (x false true) (x true false) (x true true) 0 1 (by decide)
      (rows false false) (rows false true) (rows true false) (rows true true)
    have hcol := separated (fun z => prediction u v choose (r * z))
      (fun a b c y hab hbc ha hc' => scaled_interval choose hc r a b c y hab hbc ha hc')
      (x false false) (x true false) (x false true) (x true true) 0 2 (by decide)
      (cols false false) (cols true false) (cols false true) (cols true true)
    rcases hrow with ⟨hr1, hr2, hr3, hr4⟩ | ⟨hr1, hr2, hr3, hr4⟩ <;>
      rcases hcol with ⟨hc1, hc2, hc3, hc4⟩ | ⟨hc1, hc2, hc3, hc4⟩ <;> linarith
  let p0 : Fin (m + 3) := ⟨0, by omega⟩
  let p1 : Fin (m + 3) := ⟨1, by omega⟩
  let p2 : Fin (m + 3) := ⟨2, by omega⟩
  have label0 (w : Word m) :
      FirstRejectionCutCapacity.task w = (p0 : FirstRejectionCutCapacity.Label (m + 2)) ↔
        FirstRejectionCutCapacity.bad w p0 := by
    constructor
    · intro h
      obtain ⟨i, hi, hip⟩ := (FirstRejectionCutCapacity.task_le_iff w p0).mp h.le
      have hip' : i.val ≤ 0 := hip
      have he : i = p0 := by apply Fin.ext; change i.val = 0; omega
      simpa only [he] using hi
    · intro h
      exact le_antisymm ((FirstRejectionCutCapacity.task_le_iff w p0).mpr ⟨p0, h, le_rfl⟩)
        (show (⊥ : FirstRejectionCutCapacity.Label (m + 2)) ≤ _ from bot_le)
  have label1 (w : Word m) :
      FirstRejectionCutCapacity.task w = (p1 : FirstRejectionCutCapacity.Label (m + 2)) ↔
        ¬ FirstRejectionCutCapacity.bad w p0 ∧ FirstRejectionCutCapacity.bad w p1 := by
    constructor
    · intro h
      constructor
      · intro h0
        have he := (label0 w).mpr h0
        rw [h] at he
        have he' := WithTop.coe_injective he
        have := congrArg Fin.val he'
        change (1 : ℕ) = 0 at this
        omega
      · obtain ⟨i, hi, hip⟩ := FirstRejectionCutCapacity.task_le_iff w p1 |>.mp (le_of_eq h)
        have hval : i.val = 0 ∨ i.val = 1 := by
          have hip' : i.val ≤ 1 := hip
          omega
        rcases hval with hv | hv
        · have he : i = p0 := Fin.ext hv
          have he0 := (label0 w).mpr (by simpa [he] using hi)
          rw [h] at he0
          have := congrArg Fin.val (WithTop.coe_injective he0)
          change (1 : ℕ) = 0 at this
          omega
        · simpa [show i = p1 from Fin.ext hv] using hi
    · rintro ⟨h0, h1⟩
      have hle := FirstRejectionCutCapacity.task_le_iff w p1 |>.mpr ⟨p1, h1, le_rfl⟩
      apply le_antisymm hle
      by_contra hn
      have hlt : FirstRejectionCutCapacity.task w <
          (p1 : FirstRejectionCutCapacity.Label (m + 2)) := lt_of_not_ge hn
      obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      rw [← hj] at hlt
      have hj0 : j = p0 := by
        have hh := WithTop.coe_lt_coe.mp hlt
        apply Fin.ext
        have hh' : j.val < 1 := hh
        change j.val = 0
        omega
      exact h0 ((label0 w).mp (hj.symm.trans (congrArg (fun i : Fin (m + 3) => (i : FirstRejectionCutCapacity.Label (m + 2))) hj0)))
  have coarse_formula (w : Word m) : coarse w =
      if last (w p0) = true ∧ first (w p1) = true then 1
      else if last (w p1) = true ∧ first (w p2) = true then 2 else 0 := by
    have b0 : FirstRejectionCutCapacity.bad w p0 ↔ last (w p0) = true ∧ first (w p1) = true := by
      simp [FirstRejectionCutCapacity.bad, p0, p1, show 0 < m + 2 by omega]
    have b1 : FirstRejectionCutCapacity.bad w p1 ↔ last (w p1) = true ∧ first (w p2) = true := by
      simp [FirstRejectionCutCapacity.bad, p1, p2, show 1 < m + 2 by omega]
    unfold coarse
    have h0eq : FirstRejectionCutCapacity.task w =
        ((⟨0, by omega⟩ : Fin (m + 3)) : FirstRejectionCutCapacity.Label (m + 2)) ↔
        last (w p0) = true ∧ first (w p1) = true := (label0 w).trans b0
    have h1eq : FirstRejectionCutCapacity.task w =
        ((⟨1, by omega⟩ : Fin (m + 3)) : FirstRejectionCutCapacity.Label (m + 2)) ↔
        ¬ (last (w p0) = true ∧ first (w p1) = true) ∧
        (last (w p1) = true ∧ first (w p2) = true) := (label1 w).trans (b0.not.and b1)
    simp only [h0eq, h1eq]
    by_cases h0 : last (w p0) = true ∧ first (w p1) = true <;>
      by_cases h1 : last (w p1) = true ∧ first (w p2) = true <;> simp only [h0, h1,
        not_true_eq_false, not_false_eq_true, true_and, false_and, ↓reduceIte]
  let join (a b c : Window) (τ : Fin m → Window) : Word m :=
    Fin.cons a (Fin.cons b (Fin.cons c τ))
  let wa (a : Bool) : Window := if a then .high else .zero
  let wb (b : Bool) : Window := if b then .high else .low
  let wc (c : Bool) : Window := if c then .low else .zero
  have e0 : p0 = (0 : Fin (m + 3)) := by
    apply Fin.ext; simp only [p0, Fin.val_mk, Fin.val_zero]
  have e1 : p1 = (0 : Fin (m + 2)).succ := by
    apply Fin.ext; simp only [p1, Fin.val_mk, Fin.val_succ, Fin.val_zero]
  have e2 : p2 = (0 : Fin (m + 1)).succ.succ := by
    apply Fin.ext; simp only [p2, Fin.val_mk, Fin.val_succ, Fin.val_zero]
  have table (a b c : Bool) (τ : Fin m → Window) :
      coarse (join (wa a) (wb b) (wc c) τ) = if b then (if c then 2 else 0) else (if a then 1 else 0) := by
    rw [coarse_formula]
    cases a <;> cases b <;> cases c <;>
      simp only [join, e0, e1, e2,
        Fin.cons_zero, Fin.cons_succ, wa, wb, wc, Bool.false_eq_true, if_false, if_true,
        first, last, not_false_eq_true, and_self, false_and, true_and]
  have score (a b c : Window) (τ : Fin m → Window) :
      evaluate (scalarImplementation f B) t (join a b c τ) =
        (κ * ∏ i : Fin m, f i.succ.succ.succ (τ i)) * f p1 b * (f p0 a * f p2 c) := by
    rw [hκ, hall, e0, e1, e2]
    simp only [Fin.prod_univ_succ, join, Fin.cons_zero, Fin.cons_succ]
    ring_nf
    rfl
  have eight (choose : Finset (Fin 3) → Fin 3) (hc : LegalChoice choose)
      (τ : Fin m → Window) : ∃ a b c : Bool,
      prediction u v choose (evaluate (scalarImplementation f B) t (join (wa a) (wb b) (wc c) τ)) ≠
        coarse (join (wa a) (wb b) (wc c) τ) := by
    by_contra hn
    push Not at hn
    apply crossing choose hc (fun a c => f p0 (wa a) * f p2 (wc c))
      ((κ * ∏ i : Fin m, f i.succ.succ.succ (τ i)) * f p1 (wb false))
      ((κ * ∏ i : Fin m, f i.succ.succ.succ (τ i)) * f p1 (wb true))
    · intro a c
      simpa only [score, table, Bool.false_eq_true, if_false] using hn a false c
    · intro a c
      simpa only [score, table, if_true] using hn a true c
  have cons_mean (q : ℕ) (g : (Fin (q + 1) → Window) → ℝ) :
      (𝔼 w, g w) = 𝔼 a : Window, 𝔼 τ : Fin q → Window, g (Fin.cons a τ) := by
    calc
      (𝔼 w, g w) = 𝔼 x : Window × (Fin q → Window), g (Fin.cons x.1 x.2) :=
        (Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (q + 1) => Window))
          (fun x => g (Fin.cons x.1 x.2)) g (by intro x; rfl)).symm
      _ = _ := by
        simpa only [Finset.univ_product_univ] using
          Finset.expect_product (Finset.univ : Finset Window)
            (Finset.univ : Finset (Fin q → Window)) (fun x => g (Fin.cons x.1 x.2))
  have split_mean (g : Word m → ℝ) :
      (𝔼 w, g w) = 𝔼 τ : Fin m → Window,
        𝔼 a : Window, 𝔼 b : Window, 𝔼 c : Window, g (join a b c τ) := by
    rw [cons_mean (m + 2)]
    simp_rw [cons_mean (m + 1), cons_mean m]
    simp_rw [Finset.expect_comm (Finset.univ : Finset Window)
      (Finset.univ : Finset (Fin m → Window))]
    rfl
  have floor (choose : Finset (Fin 3) → Fin 3) (hc : LegalChoice choose)
      (loss : Word m → ℝ) (η : ℝ) (hn : ∀ w, 0 ≤ loss w)
      (hl : ∀ w, prediction u v choose (evaluate (scalarImplementation f B) t w) ≠ coarse w →
        η ≤ loss w) : η / 125 ≤ 𝔼 w, loss w := by
    have fibre (τ : Fin m → Window) : η ≤
        ∑ a : Window, ∑ b : Window, ∑ c : Window, loss (join a b c τ) := by
      obtain ⟨a, b, c, h⟩ := eight choose hc τ
      calc
        η ≤ loss (join (wa a) (wb b) (wc c) τ) := hl _ h
        _ ≤ ∑ c : Window, loss (join (wa a) (wb b) c τ) :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun c : Window => loss (join (wa a) (wb b) c τ))
            (fun c _ => hn _) (Finset.mem_univ (wc c))
        _ ≤ ∑ b : Window, ∑ c : Window, loss (join (wa a) b c τ) :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun b : Window => ∑ c : Window, loss (join (wa a) b c τ))
            (fun b _ => Finset.sum_nonneg (fun c _ => hn _)) (Finset.mem_univ (wb b))
        _ ≤ _ := Finset.single_le_sum (s := Finset.univ)
          (f := fun a : Window => ∑ b : Window, ∑ c : Window, loss (join a b c τ))
          (fun a _ => Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun c _ => hn _)))
          (Finset.mem_univ (wa a))
    have prefix_mean (τ : Fin m → Window) : η / 125 ≤
        𝔼 a : Window, 𝔼 b : Window, 𝔼 c : Window, loss (join a b c τ) := by
      have hw : Fintype.card Window = 5 := by decide
      simp only [Fintype.expect_eq_sum_div_card, hw, Nat.cast_ofNat]
      simp only [← Finset.sum_div, div_div]
      have h := fibre τ
      norm_num
      linarith only [h]
    rw [split_mean]
    calc
      η / 125 = 𝔼 _τ : Fin m → Window, η / 125 := (Fintype.expect_const _).symm
      _ ≤ _ := Finset.expect_le_expect (fun τ _ => prefix_mean τ)
  have denominator_pos (z : ℝ) : 0 < ∑ j, Real.exp (logit u v z j) := by
    exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have prob_pos (z : ℝ) (y : Fin 3) : 0 < probability u v z y :=
    div_pos (Real.exp_pos _) (denominator_pos z)
  have prob_sum (z : ℝ) : ∑ y, probability u v z y = 1 := by
    simp only [probability, ← Finset.sum_div]
    exact div_self (ne_of_gt (denominator_pos z))
  have prob_le_one (z : ℝ) (y : Fin 3) : probability u v z y ≤ 1 := by
    apply (div_le_one (denominator_pos z)).mpr
    exact Finset.single_le_sum (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ y)
  have log_nonneg (z : ℝ) (y : Fin 3) : 0 ≤ -Real.log (probability u v z y) :=
    neg_nonneg.mpr (Real.log_nonpos (prob_pos z y).le (prob_le_one z y))
  have error_losses (choose : Finset (Fin 3) → Fin 3) (hc : LegalChoice choose)
      (z : ℝ) (y : Fin 3) (he : prediction u v choose z ≠ y) :
      (1 / 2 : ℝ) ≤ ∑ i, (probability u v z i - if y = i then 1 else 0) ^ 2 ∧
      Real.log 2 ≤ -Real.log (probability u v z y) := by
    let j := prediction u v choose z
    have hjy : j ≠ y := he
    have horder : probability u v z y ≤ probability u v z j := by
      apply div_le_div_of_nonneg_right _ (denominator_pos z).le
      exact Real.exp_le_exp.mpr (winner choose hc z y)
    have pair : probability u v z y + probability u v z j ≤ 1 := by
      calc
        _ = ∑ i ∈ ({y, j} : Finset (Fin 3)), probability u v z i := by
          simp [Ne.symm hjy]
        _ ≤ ∑ i, probability u v z i := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun i _ _ => (prob_pos z i).le)
        _ = 1 := prob_sum z
    have half : probability u v z y ≤ 1 / 2 := by linarith only [pair, horder]
    constructor
    · have square_pair : (probability u v z y - 1) ^ 2 + probability u v z j ^ 2 ≤
          ∑ i, (probability u v z i - if y = i then 1 else 0) ^ 2 := by
        calc
          _ = ∑ i ∈ ({y, j} : Finset (Fin 3)),
              (probability u v z i - if y = i then 1 else 0) ^ 2 := by
            simp [Ne.symm hjy]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => sq_nonneg _)
      have py := (prob_pos z y).le
      have pj := (prob_pos z j).le
      nlinarith only [square_pair, horder, py, pj, sq_nonneg (probability u v z y - 1 / 2)]
    · have hlog := Real.log_le_log (prob_pos z y) half
      have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hhalf] at hlog
      linarith only [hlog]
  let choose : Finset (Fin 3) → Fin 3 := fun S => if h : S.Nonempty then S.min' h else 0
  have choose_legal : LegalChoice choose := by
    intro S hS
    simp only [choose, dif_pos hS]
    exact Finset.min'_mem S hS
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    unfold errorRisk
    apply floor c hc _ 1
    · intro w
      split_ifs <;> norm_num
    · intro w h
      simp only [if_neg h, le_refl]
  · unfold squareRisk
    have h := floor choose choose_legal
      (fun w => ∑ y, (probability u v (evaluate (scalarImplementation f B) t w) y -
        if coarse w = y then 1 else 0) ^ 2) (1 / 2)
      (fun w => Finset.sum_nonneg (fun y _ => sq_nonneg _))
      (fun w he => (error_losses choose choose_legal _ _ he).1)
    norm_num at h
    exact h
  · unfold logRisk
    exact floor choose choose_legal _ (Real.log 2)
      (fun w => log_nonneg _ _) (fun w he => (error_losses choose choose_legal _ _ he).2)

end D5.S3.Arith.FibonacciAtomic.ScalarSoftmaxTreeObstruction
