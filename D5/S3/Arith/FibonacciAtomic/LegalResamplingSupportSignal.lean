/- GID: D5/S3/Arith/FibonacciAtomic/LegalResamplingSupportSignal
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LegalResamplingSupportSignal
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Positive-End resampling detects effective support. -/

import D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.LegalResamplingSupportSignal

open LiteralWindowEnd (Window first last nonzero)
open LegalPriorityTeacher (Input Roles Legal gate teacher legal_iff)
open scoped BigOperators

/-- The source keeps all positions and requires a nonzero terminal window. -/
def Positive {n : ℕ} (x : Input n) : Prop :=
  Legal x ∧ ∀ j : Fin n, j.val + 1 = n → nonzero (x j) = true

def source (n : ℕ) : Finset (Input n) := by
  letI (x : Input n) : Decidable (Legal x) :=
    decidable_of_iff (LiteralWindowEnd.run (some (false, false)) (List.ofFn x) ≠ none)
      (by simpa only [Legal, not_not] using
        ((LiteralWindowEnd.execution false false (List.ofFn x)).2).not)
  letI (x : Input n) : Decidable (Positive x) := inferInstanceAs
    (Decidable (Legal x ∧ ∀ j : Fin n, j.val + 1 = n → nonzero (x j) = true))
  exact Finset.univ.filter Positive

/-- Absent adjacent gates contribute no support coordinates. -/
def support {n : ℕ} (t : Roles n) : Finset (Fin n) :=
  (if t.p.val + 1 < t.q.val then {t.p, t.q} else ∅) ∪
    (if t.q.val + 1 < t.r.val then {t.q, t.r} else ∅)

/-- A completion agrees with the original word at every external position. -/
def fiber {n : ℕ} (I : Finset (Fin n)) (x : Input n) : Finset (Input n) :=
  (source n).filter (fun y => ∀ j, j ∉ I → y j = x j)

/-- Both averages are exact rational averages over the actual finite source. -/
def signal {n : ℕ} (t : Roles n) (I : Finset (Fin n)) : ℚ :=
  (∑ x ∈ source n,
    (∑ y ∈ fiber I x, if teacher t x ≠ teacher t y then (1 : ℚ) else 0) /
      (fiber I x).card) / (source n).card

set_option maxHeartbeats 4000000 in
-- Finite averaging identities and the four guard-repair cases are checked together.
theorem result {n : ℕ} (_hn : 4 ≤ n) (t : Roles n) (I : Finset (Fin n)) :
    (I ∩ support t = ∅ → signal t I = 0) ∧
    ((I ∩ support t).Nonempty → (2 / 3125 : ℚ) ≤ signal t I) := by
  classical
  have mem_source (x : Input n) : x ∈ source n ↔ Positive x := by simp [source]
  have mem_fiber (J : Finset (Fin n)) (x y : Input n) :
      y ∈ fiber J x ↔ Positive y ∧ ∀ j, j ∉ J → y j = x j := by
    simp [fiber, source]
  have self_mem (J : Finset (Fin n)) (x : Input n) (hx : x ∈ source n) :
      x ∈ fiber J x := (mem_fiber J x x).2 ⟨(mem_source x).1 hx, by simp⟩
  have fiber_eq (J : Finset (Fin n)) (x y : Input n) (hy : y ∈ fiber J x) :
      fiber J y = fiber J x := by
    ext z
    simp only [mem_fiber]
    obtain ⟨_, he⟩ := (mem_fiber J x y).1 hy
    constructor <;> rintro ⟨hz, h⟩ <;> refine ⟨hz, ?_⟩
    · intro j hj; exact (h j hj).trans (he j hj)
    · intro j hj; exact (h j hj).trans (he j hj).symm
  have adjacent_gate (x : Input n) (hx : Legal x) (a b : Fin n)
      (hab : a < b) (hn : ¬ a.val + 1 < b.val) : gate x a b = false := by
    have hseam := (legal_iff x).1 hx a b (by change a.val < b.val at hab; omega)
    exact Bool.eq_false_iff.mpr (by simpa [gate] using hseam)
  have response_eq (x y : Input n) (hx : Legal x) (hy : Legal y)
      (he : ∀ j ∈ support t, x j = y j) : teacher t x = teacher t y := by
    have ha : gate x t.p t.q = gate y t.p t.q := by
      by_cases h : t.p.val + 1 < t.q.val
      · have hp : t.p ∈ support t := by simp [support, h]
        have hq : t.q ∈ support t := by simp [support, h]
        simp only [gate, he t.p hp, he t.q hq]
      · rw [adjacent_gate x hx _ _ t.pq h, adjacent_gate y hy _ _ t.pq h]
    have hb : gate x t.q t.r = gate y t.q t.r := by
      by_cases h : t.q.val + 1 < t.r.val
      · have hq : t.q ∈ support t := by simp [support, h]
        have hr : t.r ∈ support t := by simp [support, h]
        simp only [gate, he t.q hq, he t.r hr]
      · rw [adjacent_gate x hx _ _ t.qr h, adjacent_gate y hy _ _ t.qr h]
    simp only [teacher, ha, hb]
  let L := source n
  let K (J : Finset (Fin n)) (x y : Input n) : ℚ :=
    if y ∈ fiber J x then 1 / (fiber J x).card else 0
  let avg (J : Finset (Fin n)) (f : Input n → ℚ) (x : Input n) : ℚ :=
    ∑ y ∈ L, K J x y * f y
  have fiber_sub (J : Finset (Fin n)) (x : Input n) : fiber J x ⊆ L := by
    intro y hy
    exact (mem_source y).2 ((mem_fiber J x y).1 hy).1
  have member_symm (J : Finset (Fin n)) (x y : Input n)
      (hx : x ∈ L) (hy : y ∈ L) : y ∈ fiber J x ↔ x ∈ fiber J y := by
    simp only [mem_fiber, (mem_source x).1 hx, (mem_source y).1 hy, true_and]
    exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
  have kernel_symm (J : Finset (Fin n)) (x y : Input n)
      (hx : x ∈ L) (hy : y ∈ L) : K J x y = K J y x := by
    by_cases h : y ∈ fiber J x
    · have h' := (member_symm J x y hx hy).1 h
      simp only [K, if_pos h, if_pos h', fiber_eq J x y h]
    · have h' : x ∉ fiber J y := fun h' => h ((member_symm J x y hx hy).2 h')
      simp only [K, if_neg h, if_neg h']
  have kernel_mass (J : Finset (Fin n)) (x : Input n) (hx : x ∈ L) :
      ∑ y ∈ L, K J x y = 1 := by
    have hpos : (0 : ℚ) < (fiber J x).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨x, self_mem J x hx⟩
    change (∑ y ∈ L, if y ∈ fiber J x then (1 : ℚ) / (fiber J x).card else 0) = 1
    rw [← Finset.sum_filter]
    have he : L.filter (fun y => y ∈ fiber J x) = fiber J x := by
      ext y; simp only [Finset.mem_filter]; exact and_iff_right_of_imp (fun hy => fiber_sub J x hy)
    rw [he, Finset.sum_const]
    simp only [nsmul_eq_mul]
    exact mul_one_div_cancel hpos.ne'
  have avg_eq (J : Finset (Fin n)) (f : Input n → ℚ) (x y : Input n)
      (hy : y ∈ fiber J x) : avg J f y = avg J f x := by
    unfold avg K
    rw [fiber_eq J x y hy]
  have avg_const (J : Finset (Fin n)) (f : Input n → ℚ)
      (hf : ∀ x ∈ L, ∀ y ∈ fiber J x, f y = f x) (x : Input n) (hx : x ∈ L) :
      avg J f x = f x := by
    calc
      _ = ∑ y ∈ L, K J x y * f x := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hm : y ∈ fiber J x
        · rw [hf x hx y hm]
        · simp [K, hm]
      _ = f x := by rw [← Finset.sum_mul, kernel_mass J x hx, one_mul]
  have adjoint (J : Finset (Fin n)) (f g : Input n → ℚ) :
      (∑ x ∈ L, f x * avg J g x) = ∑ x ∈ L, g x * avg J f x := by
    simp only [avg, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [kernel_symm J y x hy hx]
    ring
  have orthogonal (J : Finset (Fin n)) (f h : Input n → ℚ)
      (hh : ∀ x ∈ L, ∀ y ∈ fiber J x, h y = h x) :
      (∑ x ∈ L, f x * h x) = ∑ x ∈ L, avg J f x * h x := by
    calc
      _ = ∑ x ∈ L, f x * avg J h x := by
        apply Finset.sum_congr rfl; intro x hx; rw [avg_const J h hh x hx]
      _ = ∑ x ∈ L, h x * avg J f x := adjoint J f h
      _ = _ := by apply Finset.sum_congr rfl; intro x _; ring
  have avg_fiber_const (J : Finset (Fin n)) (f : Input n → ℚ) :
      ∀ x ∈ L, ∀ y ∈ fiber J x, avg J f y = avg J f x := by
    intro x _ y hy; exact avg_eq J f x y hy
  have square_projection (J : Finset (Fin n)) (f : Input n → ℚ) :
      (∑ x ∈ L, f x * avg J f x) = ∑ x ∈ L, (avg J f x)^2 := by
    simpa only [pow_two] using orthogonal J f (avg J f) (avg_fiber_const J f)
  have error_formula (J : Finset (Fin n)) (f : Input n → ℚ) :
      (∑ x ∈ L, (f x - avg J f x)^2) =
        (∑ x ∈ L, (f x)^2) - ∑ x ∈ L, f x * avg J f x := by
    have he : (∑ x ∈ L, (f x - avg J f x)^2) =
        (∑ x ∈ L, (f x)^2) - 2 * (∑ x ∈ L, f x * avg J f x) +
          ∑ x ∈ L, (avg J f x)^2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _; ring
    rw [he, ← square_projection J f]; ring
  have error_mono (J H : Finset (Fin n)) (hJH : J ⊆ H) (f : Input n → ℚ) :
      (∑ x ∈ L, (f x - avg J f x)^2) ≤ ∑ x ∈ L, (f x - avg H f x)^2 := by
    have hh : ∀ x ∈ L, ∀ y ∈ fiber J x, avg H f y = avg H f x := by
      intro x _ y hy
      apply avg_eq H f x y
      obtain ⟨hp, he⟩ := (mem_fiber J x y).1 hy
      exact (mem_fiber H x y).2 ⟨hp, fun j hj => he j (fun h => hj (hJH h))⟩
    have cross := orthogonal J f (avg H f) hh
    have hn : 0 ≤ ∑ x ∈ L, (avg J f x - avg H f x)^2 :=
      Finset.sum_nonneg (fun x _ => sq_nonneg _)
    have he : (∑ x ∈ L, (avg J f x - avg H f x)^2) =
        (∑ x ∈ L, (avg J f x)^2) - 2 * (∑ x ∈ L, avg J f x * avg H f x) +
          ∑ x ∈ L, (avg H f x)^2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _; ring
    rw [error_formula J f, error_formula H f]
    rw [he, ← square_projection J f, ← square_projection H f, ← cross] at hn
    linarith only [hn]
  let U (c : Fin 3) (x : Input n) : ℚ := if teacher t x = c then 1 else 0
  have indicator_identity (x y : Input n) :
      (if teacher t x ≠ teacher t y then (1 : ℚ) else 0) =
        ∑ c : Fin 3, U c x * (U c x - U c y) := by
    dsimp [U]
    generalize teacher t x = a, teacher t y = b
    fin_cases a <;> fin_cases b <;> norm_num [Fin.sum_univ_succ]
  have signal_error (J : Finset (Fin n)) : signal t J =
      (∑ c : Fin 3, ∑ x ∈ L, (U c x - avg J (U c) x)^2) / L.card := by
    have hk (x : Input n) :
        (∑ y ∈ fiber J x, if teacher t x ≠ teacher t y then (1 : ℚ) else 0) /
          (fiber J x).card =
        ∑ y ∈ L, K J x y * (if teacher t x ≠ teacher t y then (1 : ℚ) else 0) := by
      rw [Finset.sum_div]
      simp only [K, ite_mul, zero_mul, one_div_mul_eq_div]
      rw [← Finset.sum_filter]
      have hf : L.filter (fun y => y ∈ fiber J x) = fiber J x := by
        ext y
        simp only [Finset.mem_filter]
        exact and_iff_right_of_imp (fun hy => fiber_sub J x hy)
      rw [hf]
    unfold signal
    change (∑ x ∈ L, _) / _ = _
    congr 1
    simp_rw [hk, indicator_identity, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := L) (t := (Finset.univ : Finset (Fin 3)))]
    apply Finset.sum_congr rfl
    intro c _
    rw [error_formula]
    have hstep : ∀ x ∈ L,
        (∑ y ∈ L, K J x y * (U c x * (U c x - U c y))) =
          (U c x)^2 - U c x * avg J (U c) x := by
      intro x hx
      calc
        _ = (U c x)^2 * (∑ y ∈ L, K J x y) - U c x * avg J (U c) x := by
          simp only [avg, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro y _; ring
        _ = _ := by rw [kernel_mass J x hx, mul_one]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hstep
  have signal_mono (J H : Finset (Fin n)) (hJH : J ⊆ H) : signal t J ≤ signal t H := by
    rw [signal_error J, signal_error H]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum (fun c _ => error_mono J H hJH (U c))
  have insert_positive (x : Input n) (hx : Positive x) (j : Fin n) (w : Window)
      (hw : nonzero w = true)
      (hl : first w = true → ∀ a : Fin n, a.val + 1 = j.val → last (x a) = false)
      (hh : last w = true → ∀ b : Fin n, j.val + 1 = b.val → first (x b) = false) :
      Positive (Function.update x j w) := by
    constructor
    · apply (legal_iff _).2
      intro a b hab hbad
      by_cases ha : a = j
      · subst a
        have hb : b ≠ j := by intro he; subst b; omega
        have hw' : last w = true := by simpa using hbad.1
        have hf := hh hw' b hab
        simpa [Function.update_of_ne hb, hf] using hbad.2
      · by_cases hb : b = j
        · subst b
          have hw' : first w = true := by simpa using hbad.2
          have hf := hl hw' a hab
          simpa [Function.update_of_ne ha, hf] using hbad.1
        · exact (legal_iff x).1 hx.1 a b hab (by simpa [ha, hb] using hbad)
    · intro a ha
      by_cases he : a = j
      · simpa [he] using hw
      · simpa [he] using hx.2 a ha
  have neutral_positive (x : Input n) (hx : Positive x) (j : Fin n) :
      Positive (Function.update x j .middle) :=
    insert_positive x hx j .middle rfl (by simp [first]) (by simp [last])
  have singleton_card (i : Fin n) (x : Input n) : (fiber {i} x).card ≤ 5 := by
    have hinj : Set.InjOn (fun y : Input n => y i) (fiber {i} x) := by
      intro y hy z hz he
      funext j
      by_cases hj : j = i
      · simpa [hj] using he
      · exact (((mem_fiber {i} x y).1 hy).2 j (by simpa)).trans
          (((mem_fiber {i} x z).1 hz).2 j (by simpa)).symm
    have hcard := Finset.card_le_card_of_injOn (fun y : Input n => y i)
      (s := fiber {i} x) (t := Finset.univ) (by simp [Set.MapsTo]) hinj
    have hw : (Finset.univ : Finset Window).card = 5 := by decide
    exact hw ▸ hcard
  have background (mode side : Bool) (u v : Fin n)
      (hu : u = if mode then t.p else t.q)
      (hv : v = if mode then t.q else t.r)
      (gap : u.val + 1 < v.val) :
      let i := if side then u else v
      ∃ B : Finset (Input n), B ⊆ L ∧ L.card ≤ 125 * B.card ∧
        ∀ x ∈ B, ∃ y ∈ fiber {i} x, teacher t x ≠ teacher t y := by
    let i := if side then u else v
    let other := if side then v else u
    let g : Fin n := ⟨u.val + 1, by omega⟩
    let h : Fin n := ⟨v.val - 1, by omega⟩
    let w : Window := if side then .low else .high
    let repair (x : Input n) : Input n :=
      Function.update (Function.update (Function.update x g .middle) h .middle) other w
    let B := L.filter (fun x => x g = .middle ∧ x h = .middle ∧ x other = w)
    have distinct : g ≠ u ∧ g ≠ v ∧ h ≠ u ∧ h ≠ v ∧ u ≠ v := by
      simp only [ne_eq, Fin.ext_iff]
      dsimp [g, h]
      omega
    have guards (x : Input n) : repair x g = .middle ∧ repair x h = .middle ∧
        repair x other = w := by
      have go : g ≠ other := by
        cases side <;> simp only [other, Bool.false_eq_true, ↓reduceIte]
        · exact distinct.1
        · exact distinct.2.1
      have ho : h ≠ other := by
        cases side <;> simp only [other, Bool.false_eq_true, ↓reduceIte]
        · exact distinct.2.2.1
        · exact distinct.2.2.2.1
      simp [repair, go, ho, Function.update_apply]
    have force_positive (x : Input n) (hx : Positive x)
        (hg : x g = .middle) (hh : x h = .middle)
        (j : Fin n) (hj : j = u ∨ j = v) (b : Window) (hnz : nonzero b = true)
        (hb : (j = u → first b = false) ∧ (j = v → last b = false)) :
        Positive (Function.update x j b) := by
      apply insert_positive x hx j b hnz
      · intro hon a ha
        rcases hj with rfl | rfl
        · rw [hb.1 rfl] at hon; contradiction
        · have he : a = h := Fin.ext (by dsimp [h]; omega)
          simp [he, hh, last]
      · intro hon a ha
        rcases hj with rfl | rfl
        · have he : a = g := Fin.ext (by dsimp [g]; omega)
          simp [he, hg, first]
        · rw [hb.2 rfl] at hon; contradiction
    have repaired_positive (x : Input n) (hx : Positive x) : Positive (repair x) := by
      let z := Function.update (Function.update x g .middle) h .middle
      have hz := neutral_positive _ (neutral_positive x hx g) h
      apply force_positive z hz
      · dsimp [z]; by_cases he : g = h <;> simp [he]
      · simp [z]
      · cases side <;> simp [other]
      · cases side <;> rfl
      · cases side <;> simp [other, w, first, last, distinct.2.2.2.2, distinct.2.2.2.2.symm]
    have repair_mem (x : Input n) (hx : x ∈ L) : repair x ∈ B := by
      exact Finset.mem_filter.mpr ⟨(mem_source _).2
        (repaired_positive x ((mem_source x).1 hx)), guards x⟩
    let encode (x : {x // x ∈ L}) : {y // y ∈ B} × (Fin 3 → Window) :=
      (⟨repair x.val, repair_mem x.val x.property⟩, ![x.val g, x.val h, x.val other])
    have hinj : Function.Injective encode := by
      intro x y he
      apply Subtype.ext
      funext j
      have hr : repair x.val = repair y.val := congrArg (fun z => z.1.val) he
      have hm : ![x.val g, x.val h, x.val other] = ![y.val g, y.val h, y.val other] :=
        congrArg Prod.snd he
      by_cases hjg : j = g
      · simpa [hjg] using congrFun hm 0
      · by_cases hjh : j = h
        · simpa [hjh] using congrFun hm 1
        · by_cases hjo : j = other
          · simpa [hjo] using congrFun hm 2
          · simpa [repair, hjg, hjh, hjo] using congrFun hr j
    have count : L.card ≤ 125 * B.card := by
      have hc := Fintype.card_le_of_injective encode hinj
      simpa [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun,
        show Fintype.card Window = 5 from by decide, mul_comm] using hc
    refine ⟨B, Finset.filter_subset _ _, count, ?_⟩
    intro x hx
    obtain ⟨hxL, hxg, hxh, hxo⟩ := Finset.mem_filter.mp hx
    have hp := (mem_source x).1 hxL
    let on : Window := if side then .high else .low
    let yes := Function.update x i on
    let no := Function.update x i .middle
    have hi : i = u ∨ i = v := by cases side <;> simp [i]
    have yes_pos : Positive yes := by
      apply force_positive x hp hxg hxh i hi on
      · cases side <;> rfl
      · cases side <;> simp [i, on, first, last, distinct.2.2.2.2, distinct.2.2.2.2.symm]
    have no_pos : Positive no := neutral_positive x hp i
    have yes_mem : yes ∈ fiber {i} x :=
      (mem_fiber {i} x yes).2 ⟨yes_pos, by
        intro j hj
        exact Function.update_of_ne (by simpa using hj) on x⟩
    have no_mem : no ∈ fiber {i} x :=
      (mem_fiber {i} x no).2 ⟨no_pos, by
        intro j hj
        exact Function.update_of_ne (by simpa using hj) .middle x⟩
    have difference : teacher t yes ≠ teacher t no := by
      have hpq : t.p ≠ t.q := ne_of_lt t.pq
      have hqr : t.q ≠ t.r := ne_of_lt t.qr
      cases mode <;> cases side <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at hu hv <;> subst u <;> subst v <;>
        simp only [other, w, Bool.false_eq_true, ↓reduceIte] at hxo ⊢ <;>
        simp [yes, no, i, on, teacher, gate, first, last, hpq, hpq.symm, hqr, hqr.symm, hxo]
    by_cases he : teacher t x = teacher t yes
    · exact ⟨no, no_mem, fun h => difference (he.symm.trans h)⟩
    · exact ⟨yes, yes_mem, he⟩
  constructor
  · intro hI
    unfold signal
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro x hx
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro y hy
    have hxy := response_eq x y ((mem_source x).1 hx).1 ((mem_fiber I x y).1 hy).1.1
      (by
        intro j hj
        have hjI : j ∉ I := by
          intro hij
          have : j ∈ I ∩ support t := Finset.mem_inter.mpr ⟨hij, hj⟩
          simp [hI] at this
        exact (((mem_fiber I x y).1 hy).2 j hjI).symm)
    simp [hxy]
  · intro hI
    obtain ⟨i, hi⟩ := hI
    obtain ⟨hiI, hiS⟩ := Finset.mem_inter.mp hi
    have select : ∃ mode side : Bool,
        let u := if mode then t.p else t.q
        let v := if mode then t.q else t.r
        u.val + 1 < v.val ∧ i = if side then u else v := by
      simp only [support, Finset.mem_union] at hiS
      rcases hiS with ha | hb
      · split_ifs at ha with h
        · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact ⟨true, true, h, rfl⟩
          · exact ⟨true, false, h, rfl⟩
        · simp at ha
      · split_ifs at hb with h
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl
          · exact ⟨false, true, h, rfl⟩
          · exact ⟨false, false, h, rfl⟩
        · simp at hb
    obtain ⟨mode, side, gap, he⟩ := select
    obtain ⟨B, hBL, hcount, hwitness⟩ := background mode side _ _ rfl rfl gap
    rw [← he] at hwitness
    have row_bound (x : Input n) (hx : x ∈ B) :
        (1 / 5 : ℚ) ≤ (∑ y ∈ fiber {i} x,
          if teacher t x ≠ teacher t y then (1 : ℚ) else 0) / (fiber {i} x).card := by
      obtain ⟨y, hy, hd⟩ := hwitness x hx
      have hpos : (0 : ℚ) < (fiber {i} x).card := by
        exact_mod_cast Finset.card_pos.mpr ⟨y, hy⟩
      have hsize : ((fiber {i} x).card : ℚ) ≤ 5 := by exact_mod_cast singleton_card i x
      have hone : (1 : ℚ) ≤ ∑ z ∈ fiber {i} x,
          if teacher t x ≠ teacher t z then (1 : ℚ) else 0 := by
        calc
          _ = if teacher t x ≠ teacher t y then (1 : ℚ) else 0 := by simp [hd]
          _ ≤ _ := Finset.single_le_sum
            (f := fun z => if teacher t x ≠ teacher t z then (1 : ℚ) else 0)
            (fun z _ => by split_ifs <;> norm_num) hy
      exact (le_div_iff₀ hpos).2 (by nlinarith only [hsize, hone])
    have singleton_bound : (2 / 3125 : ℚ) ≤ signal t {i} := by
      let row (x : Input n) : ℚ :=
        (∑ y ∈ fiber {i} x, if teacher t x ≠ teacher t y then (1 : ℚ) else 0) /
          (fiber {i} x).card
      have hnpos : (0 : ℚ) < L.card := by
        have hm : (fun _ : Fin n => Window.middle) ∈ L := by
          apply (mem_source _).2
          constructor
          · apply (legal_iff _).2; simp [last]
          · intro _ _; rfl
        exact_mod_cast Finset.card_pos.mpr ⟨_, hm⟩
      have hsum : (B.card : ℚ) / 5 ≤ ∑ x ∈ L, row x := by
        calc
          _ = ∑ x ∈ B, (1 / 5 : ℚ) := by
            simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
          _ ≤ ∑ x ∈ B, row x := Finset.sum_le_sum (fun x hx => row_bound x hx)
          _ ≤ ∑ x ∈ L, row x := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hBL
            intro x _ _
            apply div_nonneg _ (Nat.cast_nonneg _)
            apply Finset.sum_nonneg
            intro y _
            exact ite_nonneg (by norm_num) (by norm_num)
      have hc : (L.card : ℚ) ≤ 125 * (B.card : ℚ) := by exact_mod_cast hcount
      change (2 / 3125 : ℚ) ≤ (∑ x ∈ L, row x) / L.card
      apply (le_div_iff₀ hnpos).2
      nlinarith only [hsum, hc]
    exact singleton_bound.trans (signal_mono {i} I (by simpa))

end D5.S3.Arith.FibonacciAtomic.LegalResamplingSupportSignal
