/- GID: D5 / S3 / Combinatorics / Graph / Chordal / ChordalBanachLimitTwo
   generality: G
   mirror - B: D5 / B / S3 / Combinatorics / Graph / Chordal / ChordalBanachLimitTwo
   mirror - E: none(waiver:evidence - not - specified - by - formal - manifest)
   anchors: []
   utility: kind = certified - instance; basis = refutes = gid:D5 / S3 / Combinatorics / Graph / Chordal / ChordalBanachLimitTwo.subtwo_banach_chordal_claim; result = D5 / S3 / Combinatorics / Graph / Chordal / ChordalBanachLimitTwo.not_subtwo_banach_chordal; claim = D5 / S3 / Combinatorics / Graph / Chordal / ChordalBanachLimitTwo.subtwo_banach_chordal_claim
   digest: Averaging block potentials and summing periodic residuals give the exact Banach limit for path powers. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Banach reconstruction on path powers

Block - head potentials give an upper bound after averaging over the offsets.
For the lower bound, the coordinates of the gain record samples at the right
endpoints of width-length edges and their sums over consecutive-edge windows.
-/

namespace SimpleGraph.BanachPathPower

open Finset
open scoped BigOperators

/-- The power of the finite path, with width k. -/
def pathPower (n k : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ i.val ≤ j.val + k ∧ j.val ≤ i.val + k
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩


private theorem cycle_chord_not_edge {V : Type*} {G : SimpleGraph V} {z : V}
    {c : G.Walk z z} (hc : c.IsCycle) (hn : 4 ≤ c.length) :
    s(c.snd, c.penultimate) ∉ c.edges := by
  intro he
  obtain ⟨i, hi, hei⟩ := (Walk.mk_mem_edges_iff_exists c).mp he
  have hi' : i + 1 ≤ c.length := by omega
  have hinj := hc.getVert_injOn
  have identify {a b : ℕ} (ha : 1 ≤ a) (hal : a ≤ c.length)
      (hb : 1 ≤ b) (hbl : b ≤ c.length) (h : c.getVert a = c.getVert b) : a = b :=
    hinj (show a ∈ {t : ℕ | 1 ≤ t ∧ t ≤ c.length} from ⟨ha, hal⟩)
      (show b ∈ {t : ℕ | 1 ≤ t ∧ t ≤ c.length} from ⟨hb, hbl⟩) h
  obtain ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ := Sym2.eq_iff.mp hei.symm
  · by_cases h0 : i = 0
    · subst i
      have e₁' : c.getVert 1 = c.getVert c.length :=
        e₁.trans (c.getVert_zero.trans c.getVert_length.symm)
      clear e₁
      have := identify (by omega) (by omega) (by omega) le_rfl e₁'
      omega
    · have := identify (by omega) (by omega) (by omega) (by omega) e₁
      have := identify (by omega) (by omega) (by omega) hi' e₂
      omega
  · have h := identify (by omega) (by omega) (by omega) hi' e₁
    have hi0 : i = 0 := by omega
    subst i
    have e₂' : c.getVert (c.length - 1) = c.getVert c.length :=
      e₂.trans (c.getVert_zero.trans c.getVert_length.symm)
    clear e₂
    have := identify (by omega) (by omega) (by omega) le_rfl e₂'
    omega

/-- The two cycle neighbours of a least index are at distance at most the width. -/
private theorem pathPower_isChordal (n k : ℕ) : (pathPower n k).IsChordal := by
  classical
  intro v c hc hlen
  obtain ⟨z, hz, hzmin⟩ :=
    Finset.exists_min_image c.support.toFinset Fin.val ⟨v, by simp⟩
  have hzs : z ∈ c.support := by simpa using hz
  let d := c.rotate z hzs
  have hd : d.IsCycle := hc.rotate hzs
  have he := c.rotate_edges z hzs
  have hsupp (w : Fin n) (hw : w ∈ d.support) : w ∈ c.support := by
    rw [← Walk.cons_tail_support] at hw
    rcases List.mem_cons.mp hw with rfl | hh
    · exact hzs
    · exact List.mem_of_mem_tail ((c.support_rotate z hzs).mem_iff.mp hh)
  have hx := hsupp d.snd (d.getVert_mem_support 1)
  have hy := hsupp d.penultimate (d.getVert_mem_support (d.length - 1))
  have hxz := hzmin d.snd (by simpa using hx)
  have hyz := hzmin d.penultimate (by simpa using hy)
  have hzx := (d.adj_snd hd.not_nil).2.2
  have hzy := (d.adj_penultimate hd.not_nil).symm.2.2
  refine ⟨d.snd, d.penultimate, hx, hy, ⟨hd.snd_ne_penultimate, by omega, by omega⟩, ?_⟩
  intro hmem
  exact cycle_chord_not_edge hd (by simpa [d] using hlen) (he.mem_iff.mpr hmem)

private theorem close {n k : ℕ} {i j : Fin n}
    (h : i.val ≤ j.val) (h' : j.val ≤ i.val + k) :
    i = j ∨ (pathPower n k).Adj i j := by
  by_cases he : i = j
  · exact .inl he
  · exact .inr ⟨he, by omega, h'⟩

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

private def head (k s m : ℕ) : ℕ := k * m - s

private def spine (n k s : ℕ) (g : Fin n → Fin n → E) : ℕ → E
  | 0 => 0
  | m + 1 => spine n k s g m +
      if ha : head k s m < n then
        if hb : head k s (m + 1) < n then g ⟨head k s m, ha⟩ ⟨head k s (m + 1), hb⟩
        else 0
      else 0

private def blockHead {n : ℕ} (k s : ℕ) (v : Fin n) : Fin n :=
  ⟨head k s ((v.val + s) / k), by
    have := Nat.mul_div_le (v.val + s) k
    dsimp [head]
    omega⟩

/-- Integrate on the clamped block heads, then along each block star. -/
private def offsetPotential {n : ℕ} (k s : ℕ) (g : Fin n → Fin n → E) (v : Fin n) : E :=
  spine n k s g ((v.val + s) / k) + g (blockHead k s v) v

private theorem diagonal {n : ℕ} (g : Fin n → Fin n → E)
    (hskew : ∀ i j, g j i = -g i j) (i : Fin n) : g i i = 0 := by
  have h : (2 : ℝ) • g i i = 0 := by
    rw [two_smul]
    calc
      _ = g i i + (-g i i) := congrArg (g i i + ·) (hskew i i)
      _ = 0 := add_neg_cancel _
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

private theorem triangle {n k : ℕ} (g : Fin n → Fin n → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hskew : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
      (pathPower n k).Adj i l → ‖g i j + g j l - g i l‖ ≤ ε)
    {a b c : Fin n} (hab : a = b ∨ (pathPower n k).Adj a b)
    (hbc : b = c ∨ (pathPower n k).Adj b c)
    (hac : a = c ∨ (pathPower n k).Adj a c) :
    ‖g a b + g b c - g a c‖ ≤ ε := by
  rcases hab with rfl | hab
  · simpa [diagonal g hskew] using hε
  rcases hbc with rfl | hbc
  · simpa [diagonal g hskew] using hε
  rcases hac with rfl | hac
  · simpa [diagonal g hskew, hskew b a] using hε
  exact htri a b c hab hbc hac

/-- Each endpoint pays one triangle unless its shifted residue is zero.
The first block head is clamped to zero, so clamping can only remove a payment. -/
private theorem offset_potential_error {n k : ℕ} (hk : 0 < k) (s : ℕ) (hs : s < k)
    (g : Fin n → Fin n → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hskew : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
      (pathPower n k).Adj i l → ‖g i j + g j l - g i l‖ ≤ ε)
    (u v : Fin n) (huv : (pathPower n k).Adj u v) :
    ‖g u v - (offsetPotential k s g v - offsetPotential k s g u)‖ ≤
      ε * ((if (u.val + s) % k = 0 then 0 else 1) +
           (if (v.val + s) % k = 0 then 0 else 1)) := by
  have hd := diagonal g hskew
  have ht {a b c : Fin n} := triangle g ε hε hskew htri (a := a) (b := b) (c := c)
  have forward (u v : Fin n) (huv : (pathPower n k).Adj u v) (hu : u.val < v.val) :
      ‖g u v - (offsetPotential k s g v - offsetPotential k s g u)‖ ≤
        ε * ((if (u.val + s) % k = 0 then 0 else 1) +
             (if (v.val + s) % k = 0 then 0 else 1)) := by
    let a := (u.val + s) / k
    let b := (v.val + s) / k
    let x := blockHead k s u
    let y := blockHead k s v
    have eu := Nat.mod_add_div (u.val + s) k
    have ev := Nat.mod_add_div (v.val + s) k
    change (u.val + s) % k + k * a = u.val + s at eu
    change (v.val + s) % k + k * b = v.val + s at ev
    have ru := Nat.mod_lt (u.val + s) hk
    have rv := Nat.mod_lt (v.val + s) hk
    have ex : x.val = k * a - s := rfl
    have ey : y.val = k * b - s := rfl
    have hx : x.val ≤ u.val := by omega
    have hy : y.val ≤ v.val := by omega
    have hxu : u.val ≤ x.val + k := by omega
    have hyv : v.val ≤ y.val + k := by omega
    have hxa := close hx hxu
    have hyb := close hy hyv
    have hu0 (h : (u.val + s) % k = 0) : x = u := Fin.ext (by omega)
    have hv0 (h : (v.val + s) % k = 0) : y = v := Fin.ext (by omega)
    have hab : a ≤ b := Nat.div_le_div_right (by omega)
    have hab' : b ≤ a + 1 := by
      dsimp [a,b]
      have := Nat.div_le_div_right (c := k) (show v.val + s ≤ (u.val + s) + k by
        have := huv.2.2; omega)
      simpa [Nat.add_div_right _ hk] using this
    by_cases he : a = b
    · have hxy : x = y := Fin.ext (by
        dsimp [x,y,blockHead,head]
        rw [show (u.val + s) / k = (v.val + s) / k from he])
      have hv : (v.val + s) % k ≠ 0 := by
        intro hz
        have := congrArg Fin.val (hv0 hz)
        have := congrArg Fin.val hxy
        omega
      change ‖g u v - ((spine n k s g b + g y v) - (spine n k s g a + g x u))‖ ≤ _
      rw [he, hxy, ite_eq_right hv]
      by_cases hz : (u.val + s) % k = 0
      · rw [ite_eq_left hz, ← hxy, hu0 hz, hd]
        simpa using hε
      · rw [ite_eq_right hz]
        have H := ht (hxy ▸ hxa) (.inr huv) hyb
        calc
          _ = ‖g y u + g u v - g y v‖ := by congr 1; abel
          _ ≤ ε := H
          _ ≤ ε * (1 + 1) := by linarith
    · have hb : b = a + 1 := by omega
      have ek : k * b = k * a + k := by rw [hb,Nat.mul_succ]
      rw [ek] at ev
      have ey' : y.val = k * a + k - s := by rw [ey,hb,Nat.mul_succ]
      have hxy := close (k:=k) (i:=x) (j:=y) (by omega) (by omega)
      have huy := close (k:=k) (i:=u) (j:=y) (by omega) (by omega)
      have hQ : spine n k s g b = spine n k s g a + g x y := by
        rw [hb,spine]
        have h₁ : head k s a < n := x.isLt
        have h₂ : head k s (a + 1) < n := by
          have hylt : head k s b < n := y.isLt
          rw [hb] at hylt
          exact hylt
        simp only [dite_eq_left h₁,dite_eq_left h₂]
        congr 1
        congr 1
        apply Fin.ext
        change head k s (a + 1) = head k s b
        rw [hb]
      have h₁ : ‖g x u + g u y - g x y‖ ≤ ε * (if (u.val + s) % k = 0 then 0 else 1) := by
        split_ifs with hz
        · rw [hu0 hz,hd]; simp
        · simpa using ht hxa huy hxy
      have h₂ : ‖g u y + g y v - g u v‖ ≤ ε * (if (v.val + s) % k = 0 then 0 else 1) := by
        split_ifs with hz
        · rw [hv0 hz,hd]; simp
        · simpa using ht huy hyb (.inr huv)
      change ‖g u v - ((spine n k s g b + g y v) - (spine n k s g a + g x u))‖ ≤ _
      rw [hQ]
      calc
        _ = ‖(g x u + g u y - g x y) - (g u y + g y v - g u v)‖ := by congr 1; abel
        _ ≤ ‖g x u + g u y - g x y‖ + ‖g u y + g y v - g u v‖ := norm_sub_le _ _
        _ ≤ _ := by nlinarith [h₁,h₂]
  rcases lt_trichotomy u.val v.val with h | h | h
  · exact forward u v huv h
  · exact (huv.1 (Fin.ext h)).elim
  · have H := forward v u huv.symm h
    rw [hskew u v] at H
    have he : g u v - (offsetPotential k s g v - offsetPotential k s g u) =
        -(-g u v - (offsetPotential k s g u - offsetPotential k s g v)) := by abel
    rw [he,norm_neg]
    simpa [add_comm] using H

private theorem mark_sum {k : ℕ} (hk : 0 < k) (v : ℕ) :
    (∑ s : Fin k, (if (v + s.val) % k = 0 then (0:ℝ) else 1)) = (k:ℝ) - 1 := by
  classical
  let : NeZero k := ⟨by omega⟩
  let x : Fin k := ⟨v % k,Nat.mod_lt v hk⟩
  have he (s : Fin k) : (v + s.val) % k = 0 ↔ s = -x := by
    have hr : (v + s.val) % k = (x + s).val := by
      simp [Fin.val_add,x,Nat.add_mod]
    rw [hr]
    change (x + s).val = (0 : Fin k).val ↔ _
    rw [Fin.val_inj]
    simpa [add_comm] using (add_eq_zero_iff_eq_neg : s + x = 0 ↔ s = -x)
  simp_rw [he]
  simp [Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem,
    Nat.cast_sub (show 1 ≤ k by omega)]

/-- Averaging all offsets gives the coefficient two minus two over width in every real
seminormed space; completeness is unnecessary. -/
theorem pathPower_banach_upper_bound (n k : ℕ) (hk : 0 < k)
    (g : Fin n → Fin n → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hskew : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
      (pathPower n k).Adj i l → ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : Fin n → E, ∀ i j, (pathPower n k).Adj i j →
      ‖g i j - (φ j - φ i)‖ ≤ (2 - 2 / (k:ℝ)) * ε := by
  classical
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  let φ := fun v : Fin n => (k:ℝ)⁻¹ • ∑ s : Fin k, offsetPotential k s.val g v
  refine ⟨φ,fun u v huv => ?_⟩
  have he : g u v - (φ v - φ u) = (k:ℝ)⁻¹ •
      ∑ s : Fin k, (g u v - (offsetPotential k s.val g v - offsetPotential k s.val g u)) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ,smul_sub,smul_smul,inv_mul_cancel₀ hkR.ne',one_smul,φ]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hkR)]
  have H := calc
    ‖∑ s : Fin k, (g u v - (offsetPotential k s.val g v - offsetPotential k s.val g u))‖
        ≤ ∑ s : Fin k, ‖g u v -
          (offsetPotential k s.val g v - offsetPotential k s.val g u)‖ := norm_sum_le _ _
    _ ≤ ∑ s : Fin k, ε * ((if (u.val + s.val) % k = 0 then 0 else 1) +
        (if (v.val + s.val) % k = 0 then 0 else 1)) :=
      Finset.sum_le_sum fun s _ => offset_potential_error hk s.val s.isLt g ε hε hskew htri u v huv
    _ = ε * ((k:ℝ) - 1 + ((k:ℝ) - 1)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,mark_sum hk,mark_sum hk]
  calc
    _ ≤ (k:ℝ)⁻¹ * (ε * ((k:ℝ) - 1 + ((k:ℝ) - 1))) :=
      mul_le_mul_of_nonneg_left H (le_of_lt (inv_pos.mpr hkR))
    _ = _ := by field_simp; ring


section

private def residueMark (k a w : ℕ) : ℝ :=
  if a % k = w % k then 1 else 0

private def centered (k a w : ℕ) : ℝ :=
  residueMark k a w - 1 / (k : ℝ)

private theorem nearby_eq_of_mod {k a b : ℕ}
    (hab : a ≤ b) (hgap : b < a + k) (h : a % k = b % k) : a = b := by
  have hd : k ∣ b - a := Nat.ModEq.dvd' h
  by_contra hn
  have := Nat.le_of_dvd (by omega : 0 < b - a) hd
  omega

private theorem mark_sum_eq (k a : ℕ) (S : Finset ℕ)
    (hinj : Set.InjOn (· % k) ↑S) :
    (∑ w ∈ S, residueMark k a w) = if ∃ w ∈ S, w % k = a % k then 1 else 0 := by
  classical
  split
  next h =>
    obtain ⟨w, hw, he⟩ := h
    rw [sum_eq_single_of_mem w hw]
    · simp [residueMark, he]
    · intro v hv hne
      have hnot : a % k ≠ v % k := fun hh => hne (hinj hv hw (hh.symm.trans he.symm))
      simp [residueMark, hnot]
  next h =>
    exact sum_eq_zero fun w hw => ite_eq_right (fun hh => h ⟨w, hw, hh.symm⟩)

private theorem interval_injOn (u k : ℕ) : Set.InjOn (· % k) ↑(Ico u (u + k)) := by
  intro a ha b hb he
  obtain ⟨ha₁, ha₂⟩ := mem_Ico.mp ha
  obtain ⟨hb₁, hb₂⟩ := mem_Ico.mp hb
  rcases le_total a b with h | h
  · exact nearby_eq_of_mod h (by omega) he
  · exact (nearby_eq_of_mod h (by omega) he.symm).symm

private theorem centered_period {k : ℕ} (hk : 0 < k) (a u : ℕ) :
    (∑ w ∈ Ico u (u + k), centered k a w) = 0 := by
  classical
  have hhit : ∃ w ∈ Ico u (u + k), w % k = a % k := by
    let x := (a % k + k - u % k) % k
    have hx : x < k := Nat.mod_lt _ hk
    refine ⟨u + x, mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    have hu := Nat.mod_lt u hk
    have ha := Nat.mod_lt a hk
    have he : u % k + (a % k + k - u % k) = a % k + k := by omega
    calc
      (u + x) % k = (u % k + (a % k + k - u % k)) % k := by
        rw [Nat.add_mod u x]
        simp only [x, Nat.mod_mod, Nat.add_mod_mod]
      _ = a % k := by rw [he, Nat.add_mod_right, Nat.mod_mod]
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [centered, sum_sub_distrib, mark_sum_eq k a _ (interval_injOn u k),
    ite_eq_left hhit, sum_const, nsmul_eq_mul, Nat.card_Ico, Nat.add_sub_cancel_left]
  field_simp
  <;> ring

private theorem centered_period_left {k : ℕ} (hk : 0 < k) (w u : ℕ) :
    (∑ a ∈ Ico u (u + k), centered k a w) = 0 := by
  convert centered_period hk w u using 1
  apply sum_congr rfl
  intro a ha
  simp [centered, residueMark, eq_comm]

private theorem centered_partial {k u : ℕ} (hk : 0 < k) (a : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Ico u (u + k)) :
    |∑ w ∈ S, centered k a w| ≤ 1 := by
  classical
  have hinj : Set.InjOn (· % k) ↑S := (interval_injOn u k).mono hS
  have hc : (S.card : ℝ) ≤ k := by
    exact_mod_cast (card_le_card hS).trans_eq (by simp [Nat.card_Ico])
  have hk' : (0 : ℝ) < k := by positivity
  have hdiv : (S.card : ℝ) * (1 / k) ≤ 1 := by
    rw [mul_one_div, div_le_iff₀ hk']
    simpa using hc
  simp only [centered, sum_sub_distrib, sum_const, nsmul_eq_mul, mark_sum_eq k a S hinj]
  have hn : 0 ≤ (S.card : ℝ) * (1 / k) := by positivity
  split <;> rw [abs_le] <;> constructor <;> linarith

private theorem centered_difference_partial {k u : ℕ} (a b : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Ico u (u + k)) :
    |∑ w ∈ S, (centered k a w - centered k b w)| ≤ 1 := by
  classical
  have hinj : Set.InjOn (· % k) ↑S := (interval_injOn u k).mono hS
  simp only [centered, sum_sub_distrib, mark_sum_eq k a S hinj, mark_sum_eq k b S hinj]
  split <;> split <;> ring_nf <;> norm_num

private def sampleWindow (n k u : ℕ) : Finset ℕ :=
  (Ico u (u + k)).filter fun w => k ≤ w ∧ w < n

private theorem mem_sampleWindow {n k u w : ℕ} :
    w ∈ sampleWindow n k u ↔ u ≤ w ∧ w < u + k ∧ k ≤ w ∧ w < n := by
  simp [sampleWindow, and_assoc]

private theorem sampleWindow_eq {n k u : ℕ} (hu : k ≤ u) (hn : u + k ≤ n) :
    sampleWindow n k u = Ico u (u + k) := by
  ext w
  rw [mem_sampleWindow, mem_Ico]
  omega

private def readSample {n : ℕ} (x : Fin n → ℝ) (w : ℕ) : ℝ :=
  if h : w < n then x ⟨w, h⟩ else 0

private def samples (n k : ℕ) : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) where
  carrier := {x |
    (∀ w : Fin n, w.val < k → x.1 w = 0) ∧
    (∀ u : Fin n, x.2 u = ∑ w ∈ sampleWindow n k u, readSample x.1 w) ∧
    (∀ u : Fin n, k ≤ u.val → u.val + k ≤ n → x.2 u = 0)}
  zero_mem' := by
    simp [readSample]
  add_mem' := by
    rintro x y ⟨hx, hxs, hxf⟩ ⟨hy, hys, hyf⟩
    refine ⟨fun w hw => by simp [hx w hw, hy w hw], fun u => ?_, fun u hu hn => ?_⟩
    · change x.2 u + y.2 u = _
      rw [hxs, hys, ← sum_add_distrib]
      apply sum_congr rfl
      intro w hw
      simp [readSample, (mem_sampleWindow.mp hw).2.2.2]
    · change x.2 u + y.2 u = 0
      rw [hxf u hu hn, hyf u hu hn, add_zero]
  smul_mem' := by
    rintro c x ⟨hx, hxs, hxf⟩
    refine ⟨fun w hw => by simp [hx w hw], fun u => ?_, fun u hu hn => ?_⟩
    · change c * x.2 u = _
      rw [hxs, mul_sum]
      apply sum_congr rfl
      intro w hw
      simp [readSample, (mem_sampleWindow.mp hw).2.2.2]
    · change c * x.2 u = 0
      rw [hxf u hu hn, mul_zero]

private def pack {n k : ℕ} (f : ℕ → ℝ)
    (hf : ∀ u, k ≤ u → u + k ≤ n → ∑ w ∈ Ico u (u + k), f w = 0) :
    samples n k :=
  ⟨(fun w => if k ≤ w.val then f w else 0,
    fun u => ∑ w ∈ sampleWindow n k u, f w), by
    refine ⟨fun w hw => ite_eq_right (not_le.mpr hw), fun u => ?_, fun u hu hn => ?_⟩
    · change (∑ w ∈ sampleWindow n k u, f w) =
        ∑ w ∈ sampleWindow n k u, readSample (fun v => if k ≤ v.val then f v else 0) w
      apply sum_congr rfl
      intro w hw
      have hm := mem_sampleWindow.mp hw
      simp [readSample, hm.2.2.1, hm.2.2.2]
    · simpa only [sampleWindow_eq hu hn] using hf u hu hn⟩

private theorem sample_le_norm {n k : ℕ} (x : samples n k) (w : Fin n) :
    |x.val.1 w| ≤ ‖x‖ := by
  exact (norm_le_pi_norm (f := x.val.1) w).trans (le_max_left _ _)

private theorem window_le_norm {n k : ℕ} (x : samples n k) (u : Fin n) :
    |x.val.2 u| ≤ ‖x‖ := by
  exact (norm_le_pi_norm (f := x.val.2) u).trans (le_max_right _ _)

private theorem sample_norm_le {n k : ℕ} {x : samples n k} {M : ℝ} (hM : 0 ≤ M)
    (h₁ : ∀ w : Fin n, |x.val.1 w| ≤ M) (h₂ : ∀ u : Fin n, |x.val.2 u| ≤ M) : ‖x‖ ≤ M :=
  max_le ((pi_norm_le_iff_of_nonneg hM).mpr h₁)
    ((pi_norm_le_iff_of_nonneg hM).mpr h₂)

/-- The increasing - edge gain in consecutive-edge gauge. Open intervals count
exactly the interior marks of a short edge. -/
private def profile (k i j w : ℕ) : ℝ :=
  if i + k = j then 2 * centered k j w else -∑ a ∈ Ioo i j, centered k a w

private theorem profile_period {k : ℕ} (hk : 0 < k) (i j u : ℕ) :
    (∑ w ∈ Ico u (u + k), profile k i j w) = 0 := by
  classical
  by_cases h : i + k = j
  · simp [profile, h, ← mul_sum, centered_period hk]
  · simp only [profile, ite_eq_right h, sum_neg_distrib]
    rw [sum_comm]
    simp [centered_period hk]

private theorem profile_consecutive (k u w : ℕ) :
    profile k u (u + 1) w = 0 := by
  have hI : Ioo u (u + 1) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    have := mem_Ioo.mp ha
    omega
  by_cases hk : k = 1
  · subst k
    simp [profile, centered, residueMark, Nat.mod_one]
  · simp [profile, hk, hI]

private theorem inner_sum {i j l : ℕ} (hij : i < j) (hjl : j < l) (f : ℕ → ℝ) :
    (∑ a ∈ Ioo i l, f a) = (∑ a ∈ Ioo i j, f a) + (∑ a ∈ Ioo j l, f a) + f j := by
  classical
  have hs : Ioo i l = insert j (Ioo i j ∪ Ioo j l) := by
    ext x
    simp only [mem_Ioo, mem_insert, mem_union]
    omega
  have hnot : j ∉ Ioo i j ∪ Ioo j l := by simp
  have hd : Disjoint (Ioo i j) (Ioo j l) := by
    refine Finset.disjoint_left.mpr fun a h₁ h₂ => ?_
    have := (mem_Ioo.mp h₁).2
    have := (mem_Ioo.mp h₂).1
    omega
  rw [hs, sum_insert hnot, sum_union hd]
  abel

private theorem inner_period {k : ℕ} (hk : 0 < k) (i w : ℕ) :
    (∑ a ∈ Ioo i (i + k), centered k a w) = -centered k (i + k) w := by
  have hs : Ico (i + 1) (i + 1 + k) = insert (i + k) (Ioo i (i + k)) := by
    ext a
    simp only [mem_Ico, mem_insert, mem_Ioo]
    omega
  have h := centered_period_left hk w (i + 1)
  rw [hs, sum_insert (by simp)] at h
  linarith

private theorem profile_defect {k i j l : ℕ} (hij : i < j) (hjl : j < l) (hil : l ≤ i + k)
    (w : ℕ) :
    profile k i j w + profile k j l w - profile k i l w =
      if i + k = l then centered k j w - centered k l w else centered k j w := by
  have ha : i + k ≠ j := by omega
  have hb : j + k ≠ l := by omega
  have hs := inner_sum hij hjl (fun a => centered k a w)
  by_cases hc : i + k = l
  · have hk : 0 < k := by omega
    have hp := inner_period hk i w
    rw [hc] at hp
    simp only [profile, ite_eq_right ha, ite_eq_right hb, ite_eq_left hc]
    linarith
  · simp only [profile, ite_eq_right ha, ite_eq_right hb, ite_eq_right hc]
    linarith

private def orientedGain {n k : ℕ} (hk : 0 < k) (i j : Fin n) : samples n k :=
  if i.val < j.val then pack (profile k i j) (fun u _ _ => profile_period hk i j u)
  else if j.val < i.val then -pack (profile k j i) (fun u _ _ => profile_period hk j i u)
  else 0

private theorem orientedGain_skew {n k : ℕ} (hk : 0 < k) (i j : Fin n) :
    orientedGain hk j i = -orientedGain hk i j := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [orientedGain, h, not_lt.mpr h.le]
  · simp [orientedGain, h]
  · simp [orientedGain, h, not_lt.mpr h.le]

private theorem sorted_flat {n k : ℕ} (hk : 0 < k) {i j l : Fin n}
    (hij : i.val < j.val) (hjl : j.val < l.val) (hil : l.val ≤ i.val + k) :
    ‖orientedGain hk i j + orientedGain hk j l - orientedGain hk i l‖ ≤ 1 := by
  let D := fun w => profile k i j w + profile k j l w - profile k i l w
  have hD {u : ℕ} (S : Finset ℕ) (hS : S ⊆ Ico u (u + k)) :
      |∑ w ∈ S, D w| ≤ 1 := by
    simp only [D, profile_defect hij hjl hil]
    by_cases h : i.val + k = l.val
    · simp only [ite_eq_left h]
      exact centered_difference_partial j l S hS
    · simp only [ite_eq_right h]
      exact centered_partial hk j S hS
  simp only [orientedGain, ite_eq_left hij, ite_eq_left hjl, ite_eq_left (hij.trans hjl)]
  apply sample_norm_le zero_le_one
  · intro w
    change |(if k ≤ w.val then profile k i j w else 0) +
      (if k ≤ w.val then profile k j l w else 0) -
      (if k ≤ w.val then profile k i l w else 0)| ≤ 1
    by_cases hw : k ≤ w.val
    · have hsub : ({w.val} : Finset ℕ) ⊆ Ico w.val (w.val + k) := by
        simp [mem_Ico, hk]
      simpa only [ite_eq_left hw, sum_singleton, D] using hD {w.val} hsub
    · simp [hw]
  · intro u
    change |(∑ w ∈ sampleWindow n k u, profile k i j w) +
      (∑ w ∈ sampleWindow n k u, profile k j l w) -
      (∑ w ∈ sampleWindow n k u, profile k i l w)| ≤ 1
    rw [← sum_add_distrib, ← sum_sub_distrib]
    exact hD _ (filter_subset _ _)

private theorem all_flat {n k : ℕ} (hk : 0 < k) {i j l : Fin n}
    (hne₁ : i ≠ j) (hne₂ : j ≠ l) (hne₃ : i ≠ l)
    (h₁ : i.val ≤ j.val + k) (h₂ : j.val ≤ i.val + k)
    (h₃ : j.val ≤ l.val + k) (h₄ : l.val ≤ j.val + k)
    (h₅ : i.val ≤ l.val + k) (h₆ : l.val ≤ i.val + k) :
    ‖orientedGain hk i j + orientedGain hk j l - orientedGain hk i l‖ ≤ 1 := by
  have neq₁ : i.val ≠ j.val := fun h => hne₁ (Fin.ext h)
  have neq₂ : j.val ≠ l.val := fun h => hne₂ (Fin.ext h)
  have neq₃ : i.val ≠ l.val := fun h => hne₃ (Fin.ext h)
  have swap {a b c : Fin n} (h : a.val < b.val) (h' : b.val < c.val)
      (hadj : c.val ≤ a.val + k) :
      let g := orientedGain hk
      ‖g a b + g b c - g a c‖ ≤ 1 ∧ ‖g a c + g c b - g a b‖ ≤ 1 ∧
      ‖g b a + g a c - g b c‖ ≤ 1 ∧ ‖g b c + g c a - g b a‖ ≤ 1 ∧
      ‖g c a + g a b - g c b‖ ≤ 1 ∧ ‖g c b + g b a - g c a‖ ≤ 1 := by
    dsimp only
    have hs := sorted_flat hk h h' hadj
    rw [orientedGain_skew hk a b, orientedGain_skew hk a c, orientedGain_skew hk b c]
    refine ⟨hs, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      first
      | convert hs using 1 <;> congr 1 <;> abel <;> done
      | have hn : ‖-(orientedGain hk a b + orientedGain hk b c -
            orientedGain hk a c)‖ ≤ 1 := by simpa only [norm_neg] using hs
        convert hn using 1 <;> congr 1 <;> abel
  by_cases hij : i.val < j.val
  · by_cases hjl : j.val < l.val
    · exact (swap hij hjl h₆).1
    · by_cases hil : i.val < l.val
      · exact (swap hil (by omega) h₂).2.1
      · exact (swap (by omega : l.val < i.val) hij h₃).2.2.2.1
  · by_cases hil : i.val < l.val
    · exact (swap (by omega : j.val < i.val) hil h₄).2.2.1
    · by_cases hjl : j.val < l.val
      · exact (swap hjl (by omega : l.val < i.val) h₁).2.2.2.2.1
      · exact (swap (by omega : l.val < j.val) (by omega : j.val < i.val) h₅).2.2.2.2.2

private def stepResidual {n k : ℕ} (φ : Fin n → samples n k) (u : ℕ) :
    samples n k :=
  if hu : u < n then -(φ ⟨u, hu⟩ - φ ⟨u - 1, by omega⟩) else 0

private theorem stepResidual_eq {n k : ℕ} (hk : 0 < k) (φ : Fin n → samples n k)
    {u : ℕ} (hu : u < n) (hu₀ : 0 < u) :
    stepResidual φ u =
      orientedGain hk ⟨u - 1, by omega⟩ ⟨u, hu⟩ - (φ ⟨u, hu⟩ - φ ⟨u - 1, by omega⟩) := by
  have h : u - 1 < u := by omega
  have hp (w : ℕ) : profile k (u - 1) u w = 0 := by
    have he : u - 1 + 1 = u := by omega
    simpa only [he] using profile_consecutive k (u - 1) w
  have hz : (pack (n := n) (k := k) (profile k (u - 1) u)
      (fun t _ _ => profile_period hk (u - 1) u t)) = 0 := by
    apply Subtype.ext
    exact Prod.ext (funext fun w => by simp [pack, hp]) (funext fun w => by simp [pack, hp])
  simpa only [stepResidual, dite_eq_left hu, orientedGain, ite_eq_left h, hz, zero_sub]

private theorem window_double_sum (n k : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ v ∈ Ico k n, ∑ u ∈ Ico (v - k + 1) (v + 1), f u v) =
      ∑ u ∈ Ico 1 n, ∑ v ∈ sampleWindow n k u, f u v := by
  have hr (v : ℕ) (hv : v ∈ Ico k n) :
      Ico (v - k + 1) (v + 1) = (Ico 1 n).filter (fun u => u ≤ v ∧ v < u + k) := by
    ext u
    have := mem_Ico.mp hv
    simp only [mem_Ico, mem_filter]
    omega
  have hc (u : ℕ) :
      sampleWindow n k u = (Ico k n).filter (fun v => u ≤ v ∧ v < u + k) := by
    ext v
    simp only [mem_sampleWindow, mem_filter, mem_Ico]
    omega
  calc
    _ = ∑ v ∈ Ico k n, ∑ u ∈ Ico 1 n, if u ≤ v ∧ v < u + k then f u v else 0 := by
      apply sum_congr rfl
      intro v hv
      rw [hr v hv, sum_filter]
    _ = ∑ u ∈ Ico 1 n, ∑ v ∈ Ico k n, if u ≤ v ∧ v < u + k then f u v else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro u _
      rw [hc, sum_filter]

private theorem trace_identity {n k : ℕ} (hk : 0 < k) (φ : Fin n → samples n k)
    {v : ℕ} (hv : v ∈ Ico k n) :
    let hvn := (mem_Ico.mp hv).2
    let l : Fin n := ⟨v - k, by omega⟩
    let r : Fin n := ⟨v, hvn⟩
    (orientedGain hk l r - (φ r - φ l)).val.1 r -
      (∑ u ∈ Ico (v - k + 1) (v + 1), readSample (stepResidual φ u).val.1 v) =
      2 - 2 / (k : ℝ) := by
  have hvk := (mem_Ico.mp hv).1
  have hvn := (mem_Ico.mp hv).2
  dsimp only
  let r : Fin n := ⟨v, hvn⟩
  let F := fun u => readSample (fun x => (φ x).val.1 r) u
  have hsum :
      (∑ u ∈ Ico (v - k + 1) (v + 1), readSample (stepResidual φ u).val.1 v) =
        F (v - k) - F v := calc
    _ = ∑ u ∈ Ico (v - k + 1) (v + 1), (F (u - 1) - F u) := by
      apply sum_congr rfl
      intro u hu
      have h := mem_Ico.mp hu
      have hun : u < n := by omega
      simp [F, stepResidual, readSample, r, hvn, hun, show u - 1 < n by omega]
    _ = F (v - k) - F v := by
      have hshift : Ico (v - k + 1) (v + 1) = (Ico (v - k) v).map (addRightEmbedding 1) := by
        ext u
        simp only [mem_Ico, mem_map]
        constructor
        · intro hu
          exact ⟨u - 1, ⟨by omega, by omega⟩, by
            change u - 1 + 1 = u
            omega⟩
        · rintro ⟨a, ha, rfl⟩
          change v - k + 1 ≤ a + 1 ∧ a + 1 < v + 1
          omega
      rw [hshift, sum_map]
      simp only [addRightEmbedding_apply, Nat.add_sub_cancel]
      have ht := Finset.sum_Ico_sub (f := F) (by omega : v - k ≤ v)
      calc
        _ = ∑ x ∈ Ico (v - k) v, -(F (x + 1) - F x) :=
          sum_congr rfl fun x _ => (neg_sub _ _).symm
        _ = _ := by rw [sum_neg_distrib, ht, neg_sub]
  rw [hsum]
  have hlt : v - k < v := by omega
  have he : v - k + k = v := by omega
  simp only [orientedGain, Fin.val_mk, ite_eq_left hlt]
  change (if k ≤ v then profile k (v - k) v v else 0) -
    ((φ r).val.1 r - (φ ⟨v - k, by omega⟩).val.1 r) - (F (v - k) - F v) = _
  simp [F, readSample, r, hvn, show v - k < n by omega, hvk, profile, he, centered, residueMark]
  <;> ring

private theorem boundary_card_le {n k : ℕ} (hn : k + 1 ≤ n) :
    ((Ico 1 n).filter fun u => ¬(k ≤ u ∧ u + k ≤ n)).card ≤ 2 * (k - 1) := by
  have hsub : (Ico 1 n).filter (fun u => ¬(k ≤ u ∧ u + k ≤ n)) ⊆
      Ico 1 k ∪ Ico (n - k + 1) n := by
    intro u hu
    simp only [mem_filter, mem_Ico, mem_union] at *
    omega
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  simp only [Nat.card_Ico]
  omega

private theorem residual_trace_bound {n k : ℕ} (hk : 0 < k) (hn : k + 1 ≤ n)
    (φ : Fin n → samples n k) {M : ℝ} (hM : 0 ≤ M)
    (hstep : ∀ u ∈ Ico 1 n, ‖stepResidual φ u‖ ≤ M)
    (hwide : ∀ v (hv : v ∈ Ico k n),
      let l : Fin n := ⟨v - k, by have := (mem_Ico.mp hv).2; omega⟩
      let r : Fin n := ⟨v, (mem_Ico.mp hv).2⟩
      ‖orientedGain hk l r - (φ r - φ l)‖ < M) :
    ((n : ℝ) - k) * (2 - 2 / (k : ℝ)) < ((n : ℝ) + k - 2) * M := by
  let long := fun v => if hv : v ∈ Ico k n then
    let l : Fin n := ⟨v - k, by have := (mem_Ico.mp hv).2; omega⟩
    let r : Fin n := ⟨v, (mem_Ico.mp hv).2⟩
    (orientedGain hk l r - (φ r - φ l)).val.1 r else 0
  let A := fun u => ∑ v ∈ sampleWindow n k u, readSample (stepResidual φ u).val.1 v
  let boundary := (Ico 1 n).filter fun u => ¬(k ≤ u ∧ u + k ≤ n)
  have htrace :
      (∑ v ∈ Ico k n, long v) - (∑ u ∈ Ico 1 n, A u) =
        ((n : ℝ) - k) * (2 - 2 / (k : ℝ)) := by
    unfold A
    rw [← window_double_sum, ← sum_sub_distrib]
    calc
      _ = ∑ _v ∈ Ico k n, (2 - 2 / (k : ℝ)) := by
        apply sum_congr rfl
        intro v hv
        simpa only [long, dite_eq_left hv] using trace_identity hk φ hv
      _ = _ := by
        simp [Nat.card_Ico, Nat.cast_sub (by omega : k ≤ n)]
        ring
  have hlong : (∑ v ∈ Ico k n, long v) < ((n : ℝ) - k) * M := by
    have hne : (Ico k n).Nonempty := ⟨k, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    calc
      _ < ∑ _v ∈ Ico k n, M := by
        apply sum_lt_sum_of_nonempty hne
        intro v hv
        simp only [long, dite_eq_left hv]
        exact (le_abs_self _).trans_lt ((sample_le_norm _ _).trans_lt (hwide v hv))
      _ = _ := by simp [Nat.card_Ico, Nat.cast_sub (by omega : k ≤ n)]
  have hA (u : ℕ) (hu : u ∈ Ico 1 n) :
      A u = (stepResidual φ u).val.2 ⟨u, (mem_Ico.mp hu).2⟩ :=
    ((stepResidual φ u).property.2.1 (⟨u, (mem_Ico.mp hu).2⟩ : Fin n)).symm
  have hAz (u : ℕ) (hu : u ∈ Ico 1 n) (hh : k ≤ u ∧ u + k ≤ n) : A u = 0 :=
    (hA u hu).trans ((stepResidual φ u).property.2.2 _ hh.1 hh.2)
  have hsmall : -(∑ u ∈ Ico 1 n, A u) ≤ 2 * ((k : ℝ) - 1) * M := by
    rw [← sum_neg_distrib]
    have hs : (∑ u ∈ boundary, -A u) = ∑ u ∈ Ico 1 n, -A u := by
      apply sum_subset (filter_subset _ _)
      intro u hu hn'
      have hh : k ≤ u ∧ u + k ≤ n := by
        by_contra h
        exact hn' (mem_filter.mpr ⟨hu, h⟩)
      simp [hAz u hu hh]
    rw [← hs]
    calc
      _ ≤ ∑ _u ∈ boundary, M := by
        apply sum_le_sum
        intro u hu
        have hu' : u ∈ Ico 1 n := (mem_filter.mp hu).1
        rw [hA u hu']
        exact (neg_le_abs _).trans ((window_le_norm _ _).trans (hstep u hu'))
      _ = (boundary.card : ℝ) * M := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hM
        have hc : boundary.card ≤ 2 * (k - 1) := boundary_card_le hn
        have hcR : (boundary.card : ℝ) ≤ ↑(2 * (k - 1) : ℕ) := Nat.cast_le.mpr hc
        push_cast [Nat.cast_sub (by omega : 1 ≤ k)] at hcR
        exact hcR
  linarith

/-- The trace of the width-length residuals, corrected by the boundary windows,
forces an edge with the stated error for every potential. -/
theorem pathPower_banach_lower_bound (n k : ℕ) (hk : 1 ≤ k) (hn : k + 1 ≤ n) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
      (_ : CompleteSpace E) (_ : FiniteDimensional ℝ E) (g : Fin n → Fin n → E),
      (∀ i j, g j i = -g i j) ∧
      (∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
        (pathPower n k).Adj i l → ‖g i j + g j l - g i l‖ ≤ 1) ∧
      ∀ φ : Fin n → E, ∃ i j, (pathPower n k).Adj i j ∧
        ((n : ℝ) - k) / ((n : ℝ) + k - 2) * (2 - 2 / (k : ℝ)) ≤ ‖g i j - (φ j - φ i)‖ := by
  have hk' : 0 < k := hk
  refine ⟨samples n k, inferInstance, inferInstance, inferInstance, inferInstance,
    orientedGain hk', orientedGain_skew hk', ?_, ?_⟩
  · intro i j l hij hjl hil
    exact all_flat hk' hij.1 hjl.1 hil.1 hij.2.1 hij.2.2 hjl.2.1 hjl.2.2 hil.2.1 hil.2.2
  · intro φ
    let M := ((n : ℝ) - k) / ((n : ℝ) + k - 2) * (2 - 2 / (k : ℝ))
    change ∃ i j, (pathPower n k).Adj i j ∧ M ≤ _
    by_contra! h
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hnR : (k : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hden : 0 < (n : ℝ) + k - 2 := by linarith
    have hcoef : 0 ≤ (2 : ℝ) - 2 / k := by
      have hd := (div_le_iff₀ (by positivity : (0 : ℝ) < k)).mpr (show (2 : ℝ) ≤ 2 * k by linarith)
      linarith
    have hM : 0 ≤ M := mul_nonneg (div_nonneg (by linarith) hden.le) hcoef
    have hs (u : ℕ) (hu : u ∈ Ico 1 n) : ‖stepResidual φ u‖ ≤ M := by
      have hm := mem_Ico.mp hu
      rw [stepResidual_eq hk' φ hm.2 (by omega)]
      apply (h _ _ ?_).le
      change (⟨u - 1, _⟩ : Fin n) ≠ ⟨u, _⟩ ∧ u - 1 ≤ u + k ∧ u ≤ u - 1 + k
      refine ⟨fun he => ?_, by omega, by omega⟩
      have := congrArg Fin.val he
      simp at this
      omega
    have hw (v : ℕ) (hv : v ∈ Ico k n) :
        let l : Fin n := ⟨v - k, by have := (mem_Ico.mp hv).2; omega⟩
        let r : Fin n := ⟨v, (mem_Ico.mp hv).2⟩
        ‖orientedGain hk' l r - (φ r - φ l)‖ < M := by
      have hm := mem_Ico.mp hv
      dsimp only
      apply h
      change (⟨v - k, _⟩ : Fin n) ≠ ⟨v, _⟩ ∧ v - k ≤ v + k ∧ v ≤ v - k + k
      refine ⟨fun he => ?_, by omega, by omega⟩
      have := congrArg Fin.val he
      simp at this
      omega
    have hh := residual_trace_bound hk' hn φ hM hs hw
    have he : ((n : ℝ) + k - 2) * M = ((n : ℝ) - k) * (2 - 2 / (k : ℝ)) := by
      dsimp [M]
      field_simp
    exact (lt_irrefl _) (he ▸ hh)

open Filter Topology

private def reconstructs (n k : ℕ) (C : ℝ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : Fin n → Fin n → E),
    (∀ i j, g j i = -g i j) →
    (∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
      (pathPower n k).Adj i l → ‖g i j + g j l - g i l‖ ≤ 1) →
    ∃ φ : Fin n → E, ∀ i j, (pathPower n k).Adj i j → ‖g i j - (φ j - φ i)‖ ≤ C

/-- The infimum of nonnegative uniform error bounds at triangle defect one
for gains in real Banach spaces. -/
def banachCoefficient (n k : ℕ) : ℝ :=
  sInf {C | 0 ≤ C ∧ reconstructs n k C}

private theorem path_coefficient_upper {n k : ℕ} (hk : 1 ≤ k) :
    banachCoefficient n k ≤ 2 - 2 / (k : ℝ) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoef : 0 ≤ (2 : ℝ) - 2 / k := by
    have hd := (div_le_iff₀ (by positivity : (0 : ℝ) < k)).mpr
      (show (2 : ℝ) ≤ 2 * k by linarith)
    linarith
  apply csInf_le ⟨0, fun _ h => h.1⟩
  refine ⟨hcoef, ?_⟩
  intro E _ _ _ g hg hf
  simpa only [mul_one] using pathPower_banach_upper_bound n k (show 0 < k from hk) g 1 zero_le_one hg hf

private theorem path_coefficient_lower {n k : ℕ} (hk : 1 ≤ k) (hn : k + 1 ≤ n) :
    ((n : ℝ) - k) / ((n : ℝ) + k - 2) * (2 - 2 / (k : ℝ)) ≤ banachCoefficient n k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let B : ℝ := 2 - 2 / (k : ℝ)
  have hB : 0 ≤ B := by
    have hd := (div_le_iff₀ (by positivity : (0 : ℝ) < k)).mpr
      (show (2 : ℝ) ≤ 2 * k by linarith)
    dsimp [B]
    linarith
  apply le_csInf
  · refine ⟨B, hB, ?_⟩
    intro E _ _ _ g hg hf
    simpa only [mul_one, B] using pathPower_banach_upper_bound n k (show 0 < k from hk) g 1 zero_le_one hg hf
  · intro C hC
    obtain ⟨E, hE, hSpace, hComplete, _, g, hg, hf, hL⟩ :=
      pathPower_banach_lower_bound n k hk hn
    letI := hE
    letI := hSpace
    letI := hComplete
    obtain ⟨φ, hφ⟩ := hC.2 E g hg hf
    obtain ⟨i,j,hij,hR⟩ := hL φ
    exact hR.trans (hφ i j hij)

private theorem lower_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => ((n : ℝ) - k) / ((n : ℝ) + k - 2) * (2 - 2 / (k : ℝ)))
      atTop (𝓝 (2 - 2 / (k : ℝ))) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + k - 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_atTop.mp (tendsto_natCast_atTop_atTop (R := ℝ))) (b + 2)] with n hn
    have hk₀ : (0 : ℝ) ≤ k := by positivity
    linarith
  have ht : Tendsto (fun n : ℕ => (1 - (2 * (k - 1 : ℝ)) / ((n : ℝ) + k - 2)) *
      (2 - 2 / (k : ℝ))) atTop (𝓝 (2 - 2 / (k : ℝ))) := by
    simpa only [sub_zero, one_mul] using
      ((hden.const_div_atTop (2 * (k - 1 : ℝ))).const_sub 1).mul_const (2 - 2 / (k : ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (n : ℝ) + k - 2 := by linarith
  field_simp
  <;> ring

/-- For every positive width, the Banach reconstruction coefficients converge
to two minus two over the width as the number of vertices grows. -/
theorem pathPower_banach_limit_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n => banachCoefficient n k) atTop (𝓝 (2 - 2 / (k : ℝ))) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (lower_tendsto k hk) tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn using path_coefficient_lower hk hn
  · exact Eventually.of_forall fun n => path_coefficient_upper (n := n) hk

/-- A real Banach reconstruction bound strictly below two for all finite
chordal graphs and all nonnegative triangle error tolerances. -/
def subtwo_banach_chordal_claim : Prop :=
  ∃ C < (2 : ℝ),
    ∀ (V : Type) [Finite V] (G : SimpleGraph V), G.IsChordal →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (g : V → V → E) (ε : ℝ), 0 ≤ ε →
      (∀ i j, g j i = -g i j) →
      (∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l → ‖g i j + g j l - g i l‖ ≤ ε) →
      ∃ φ : V → E, ∀ i j, G.Adj i j → ‖g i j - (φ j - φ i)‖ ≤ C * ε

/-- Width and length can be chosen so that the trace bound exceeds any
proposed coefficient strictly below two. -/
theorem not_subtwo_banach_chordal : ¬ subtwo_banach_chordal_claim := by
  rintro ⟨C, hC, h⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (2 / (2 - C)))
  have hkR : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk₁ : 1 ≤ k := by exact_mod_cast hkR.le
  have hkc : 2 / (2 - C) < (k : ℝ) := (le_max_right _ _).trans_lt hk
  have hgap := (div_lt_iff₀ (by linarith : 0 < 2 - C)).mp hkc
  have hsmall := (div_lt_iff₀ (by linarith : (0 : ℝ) < k)).mpr
    (show (2 : ℝ) < (2 - C) * k by linarith only [hgap])
  have htarget : C < 2 - 2 / (k : ℝ) := by linarith
  have he := (lower_tendsto k hk₁).eventually (lt_mem_nhds htarget)
  obtain ⟨n, hl, hn⟩ := (he.and (eventually_ge_atTop (k + 1))).exists
  obtain ⟨E, hE, hSpace, hComplete, _, g, hg, hf, hL⟩ :=
    pathPower_banach_lower_bound n k hk₁ hn
  letI := hE
  letI := hSpace
  letI := hComplete
  obtain ⟨φ, hφ⟩ := h (Fin n) (pathPower n k) (pathPower_isChordal n k) E g 1 zero_le_one hg hf
  obtain ⟨i,j,hij,hR⟩ := hL φ
  exact (not_lt_of_ge (by simpa only [mul_one] using hφ i j hij)) (hl.trans_le hR)


example : ∃ g : Fin 3 → Fin 3 → ℝ,
    (∀ i j, g j i = -g i j) ∧
    (∀ i j l, (pathPower 3 2).Adj i j → (pathPower 3 2).Adj j l →
      (pathPower 3 2).Adj i l → ‖g i j + g j l - g i l‖ ≤ 0) :=
  ⟨fun _ _ => 0, by simp, by simp⟩

example : (pathPower 3 2).Adj (0 : Fin 3) 2 := by
  change (0 : Fin 3) ≠ 2 ∧ (0 : ℕ) ≤ 2 + 2 ∧ (2 : ℕ) ≤ 0 + 2
  decide

#print axioms pathPower_banach_upper_bound
#print axioms pathPower_banach_lower_bound
#print axioms pathPower_banach_limit_tendsto
#print axioms not_subtwo_banach_chordal

end
end
end SimpleGraph.BanachPathPower
