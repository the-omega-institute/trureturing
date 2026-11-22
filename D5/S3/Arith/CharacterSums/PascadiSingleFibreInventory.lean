/- GID: D5/S3/Arith/CharacterSums/PascadiSingleFibreInventory
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiSingleFibreInventory
   mirror-E: none(waiver:open-short-frequency-concentration)
   anchors: []
   utility: none
   digest: A smooth cubic fibre has a shortest-vector count and few short directions. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Sqrt
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A four-coordinate integer frequency box and its actual lower stationary equation. -/

namespace D5.S3.Arith.CharacterSums.PascadiSingleFibreInventory

open Finset
open scoped BigOperators

private def kernelReading {p : ℕ} (α β : ZMod p) (v : ℤ × ℤ) : ZMod p :=
  α * (v.1 : ZMod p) + β * (v.2 : ZMod p)

private def supLength (v : ℤ × ℤ) : ℕ := max v.1.natAbs v.2.natAbs

private theorem grid_difference_short {p : ℕ} [Fact p.Prime] (α β : ZMod p) :
    ∃ v : ℤ × ℤ, v ≠ 0 ∧ kernelReading α β v = 0 ∧ supLength v ≤ p.sqrt := by
  classical
  let G := Fin (p.sqrt + 1) × Fin (p.sqrt + 1)
  let f : G → ZMod p := fun x => α * (x.1.val : ZMod p) + β * (x.2.val : ZMod p)
  have hn : ¬ Function.Injective f := by
    intro hi
    have hc := Fintype.card_le_of_injective f hi
    have ht := Nat.lt_succ_sqrt p
    simp only [G, Fintype.card_prod, Fintype.card_fin, ZMod.card] at hc
    exact (not_le_of_gt ht) hc
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hn
  let v : ℤ × ℤ := ((x.1.val : ℤ) - (y.1.val : ℤ), (x.2.val : ℤ) - (y.2.val : ℤ))
  have hb (a b : Fin (p.sqrt+1)) : ((a.val : ℤ) - (b.val : ℤ)).natAbs ≤ p.sqrt := by
    have ha := a.isLt
    have hb := b.isLt
    by_cases h : (b.val : ℤ) ≤ a.val
    · have he := Int.natAbs_of_nonneg (sub_nonneg.mpr h)
      omega
    · rw [← Int.natAbs_neg, neg_sub]
      have he := Int.natAbs_of_nonneg (a := (b.val : ℤ) - a.val) (by omega)
      omega
  refine ⟨v, ?_, ?_, max_le (hb _ _) (hb _ _)⟩
  · intro hv
    apply hne
    have h₁ := congrArg Prod.fst hv
    have h₂ := congrArg Prod.snd hv
    change (x.1.val : ℤ) - y.1.val = 0 at h₁
    change (x.2.val : ℤ) - y.2.val = 0 at h₂
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · dsimp [kernelReading, v]
    push_cast
    rw [mul_sub, mul_sub, sub_add_sub_comm]
    exact sub_eq_zero.mpr hxy

private theorem exists_shortest_primitive {p : ℕ} [Fact p.Prime] (α β : ZMod p) :
    ∃ v : ℤ × ℤ, v ≠ 0 ∧ kernelReading α β v = 0 ∧ IsCoprime v.1 v.2 ∧
      supLength v ≤ p.sqrt ∧
      ∀ w : ℤ × ℤ, w ≠ 0 → kernelReading α β w = 0 →
        supLength v ≤ supLength w := by
  classical
  let Q (n : ℕ) : Prop :=
    ∃ v : ℤ × ℤ, v ≠ 0 ∧ kernelReading α β v = 0 ∧ supLength v = n
  obtain ⟨v₀, hv₀, hk₀, hb₀⟩ := grid_difference_short α β
  have hQ : ∃ n, Q n := ⟨_, v₀, hv₀, hk₀, rfl⟩
  obtain ⟨v, hv, hk, hlen⟩ := Nat.find_spec hQ
  have hmin (w : ℤ × ℤ) (hw : w ≠ 0) (hwk : kernelReading α β w = 0) :
      supLength v ≤ supLength w := by
    rw [hlen]
    exact Nat.find_min' hQ (show Q (supLength w) from ⟨w, hw, hwk, rfl⟩)
  have hb := (hmin _ hv₀ hk₀).trans hb₀
  refine ⟨v, hv, hk, ?_, hb, hmin⟩
  let g := Int.gcd v.1 v.2
  have hgpos : 0 < g := by
    by_contra! h
    have hz : g = 0 := Nat.eq_zero_of_le_zero h
    apply hv
    have h₁ := Int.gcd_dvd_left v.1 v.2
    have h₂ := Int.gcd_dvd_right v.1 v.2
    change (g : ℤ) ∣ v.1 at h₁
    change (g : ℤ) ∣ v.2 at h₂
    rw [hz] at h₁ h₂
    exact Prod.ext (by simpa using h₁) (by simpa using h₂)
  have hgle : g ≤ supLength v := by
    by_cases h : v.1 = 0
    · have hv₂ : v.2 ≠ 0 := fun H => hv (Prod.ext h H)
      have hd := Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_right v.1 v.2)
      have hg : g ∣ v.2.natAbs := by simpa [g] using hd
      exact (Nat.le_of_dvd (by simpa using hv₂) hg).trans (le_max_right _ _)
    · have hd := Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_left v.1 v.2)
      have hg : g ∣ v.1.natAbs := by simpa [g] using hd
      exact (Nat.le_of_dvd (by simpa using h) hg).trans (le_max_left _ _)
  have hglt : g < p := (hgle.trans hb).trans_lt (Nat.sqrt_lt_self (Fact.out : p.Prime).one_lt)
  have hgF : (g : ZMod p) ≠ 0 := fun h =>
    (Nat.ne_of_gt hgpos) (Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff g p).mp h) hglt)
  obtain ⟨a, ha⟩ := Int.gcd_dvd_left v.1 v.2
  obtain ⟨b, hb'⟩ := Int.gcd_dvd_right v.1 v.2
  let w : ℤ × ℤ := (a,b)
  change v.1 = (g : ℤ) * a at ha
  change v.2 = (g : ℤ) * b at hb'
  have hw : w ≠ 0 := by
    intro H
    have h₁ := congrArg Prod.fst H
    have h₂ := congrArg Prod.snd H
    change a = 0 at h₁
    change b = 0 at h₂
    apply hv
    exact Prod.ext (by simp [ha,h₁]) (by simp [hb',h₂])
  have hwk : kernelReading α β w = 0 := by
    unfold kernelReading at hk ⊢
    rw [ha, hb'] at hk
    push_cast at hk
    apply (mul_eq_zero.mp ?_).resolve_left hgF
    change (g : ZMod p) * (α * (a : ZMod p) + β * (b : ZMod p)) = 0
    rw [mul_add]
    simpa only [mul_left_comm (g : ZMod p)] using hk
  have hmul : supLength v = g * supLength w := by
    change max v.1.natAbs v.2.natAbs = g * max a.natAbs b.natAbs
    rw [ha, hb', Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, mul_max]
  have hwpos : 0 < supLength w := by
    by_contra! h
    have H : max w.1.natAbs w.2.natAbs = 0 := Nat.eq_zero_of_le_zero h
    apply hw
    have h₁ : w.1.natAbs = 0 := Nat.eq_zero_of_le_zero ((le_max_left _ _).trans H.le)
    have h₂ : w.2.natAbs = 0 := Nat.eq_zero_of_le_zero ((le_max_right _ _).trans H.le)
    exact Prod.ext (by simpa using h₁) (by simpa using h₂)
  have hg1 : g = 1 := by
    have hm := hmin w hw hwk
    rw [hmul] at hm
    by_contra H
    have hg2 : 1 < g := by omega
    have hh := Nat.mul_lt_mul_of_pos_right hg2 hwpos
    omega
  exact Int.isCoprime_iff_gcd_eq_one.mpr hg1



private def squaredLength (v : ℤ × ℤ) : ℕ := v.1.natAbs ^ 2 + v.2.natAbs ^ 2

private lemma squaredLength_cast (v : ℤ × ℤ) :
    (squaredLength v : ℝ) = (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by
  simp only [squaredLength, Nat.cast_add, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]

private lemma sup_le_euclidean_sq (v : ℤ × ℤ) : supLength v ^ 2 ≤ squaredLength v := by
  rw [supLength, squaredLength]
  rcases le_total v.1.natAbs v.2.natAbs with h|h
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left h]
    omega

private lemma euclidean_sq_le_sup (v : ℤ × ℤ) : squaredLength v ≤ 2 * supLength v ^ 2 := by
  have h1 : v.1.natAbs ^ 2 ≤ supLength v ^ 2 :=
    Nat.pow_le_pow_left (le_max_left _ _) _
  have h2 : v.2.natAbs ^ 2 ≤ supLength v ^ 2 :=
    Nat.pow_le_pow_left (le_max_right _ _) _
  rw [squaredLength]
  omega

private lemma supLength_pos {v : ℤ × ℤ} (hv : v ≠ 0) : 0 < supLength v := by
  by_contra! h
  apply hv
  have h1 : v.1.natAbs ≤ supLength v := le_max_left _ _
  have h2 : v.2.natAbs ≤ supLength v := le_max_right _ _
  exact Prod.ext (show v.1 = (0 : ℤ) by omega) (show v.2 = (0 : ℤ) by omega)

private theorem exists_kernel_sq {p : ℕ} [Fact p.Prime] (α β : ZMod p) :
    ∃ n, ∃ v : ℤ × ℤ, v ≠ 0 ∧ kernelReading α β v = 0 ∧ squaredLength v = n := by
  obtain ⟨v, hv, hk, _⟩ := grid_difference_short α β
  exact ⟨squaredLength v, v, hv, hk, rfl⟩

/-- The usual Euclidean shortest nonzero length in the actual congruence kernel. -/
noncomputable def euclideanMinimum {p : ℕ} [Fact p.Prime] (α β : ZMod p) : ℝ := by
  classical
  exact Real.sqrt (Nat.find (exists_kernel_sq α β) : ℝ)

private lemma minimum_attained {p : ℕ} [Fact p.Prime] (α β : ZMod p) :
    ∃ v : ℤ × ℤ, v ≠ 0 ∧ kernelReading α β v = 0 ∧
      euclideanMinimum α β = Real.sqrt ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2) := by
  classical
  obtain ⟨v, hv, hker, hsq⟩ := Nat.find_spec (exists_kernel_sq α β)
  exact ⟨v, hv, hker, by rw [← squaredLength_cast, hsq, euclideanMinimum]⟩

private lemma minimum_le_length {p : ℕ} [Fact p.Prime] {α β : ZMod p} {v : ℤ × ℤ}
    (hv : v ≠ 0) (hker : kernelReading α β v = 0) :
    euclideanMinimum α β ≤ Real.sqrt (squaredLength v : ℝ) := by
  classical
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.find_min' (exists_kernel_sq α β) ⟨v, hv, hker, rfl⟩

private lemma sup_le_sqrt_squared (v : ℤ × ℤ) :
    (supLength v : ℝ) ≤ Real.sqrt (squaredLength v : ℝ) := by
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  exact_mod_cast sup_le_euclidean_sq v

private lemma minimum_compare {p : ℕ} [Fact p.Prime] {α β : ZMod p} {v : ℤ × ℤ}
    (hv : v ≠ 0) (hvker : kernelReading α β v = 0) (hvs : supLength v ≤ p.sqrt)
    (hmin : ∀ w, w ≠ 0 → kernelReading α β w = 0 → supLength v ≤ supLength w) :
    0 < euclideanMinimum α β ∧ euclideanMinimum α β ≤ 2 * (supLength v : ℝ) ∧
      euclideanMinimum α β ^ 2 ≤ 2 * (p : ℝ) := by
  obtain ⟨w, hw, hwker, he⟩ := minimum_attained α β
  have hv0 : 0 < (supLength v : ℝ) := by exact_mod_cast supLength_pos hv
  have hlo : (supLength v : ℝ) ≤ euclideanMinimum α β := by
    rw [he, ← squaredLength_cast]
    exact (show (supLength v : ℝ) ≤ (supLength w : ℝ) by exact_mod_cast hmin w hw hwker).trans
      (sup_le_sqrt_squared w)
  have hup := minimum_le_length hv hvker
  have hs : (squaredLength v : ℝ) ≤ 2 * (supLength v : ℝ) ^ 2 := by
    exact_mod_cast euclidean_sq_le_sup v
  have hh : Real.sqrt (squaredLength v : ℝ) ≤ 2 * (supLength v : ℝ) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg (supLength v : ℝ)]
  have hsqrt : (supLength v : ℝ) ^ 2 ≤ (p : ℝ) := by
    exact_mod_cast (Nat.pow_le_pow_left hvs 2).trans (Nat.sqrt_le' p)
  have hsq : euclideanMinimum α β ^ 2 ≤ (squaredLength v : ℝ) := by
    calc
      _ ≤ (Real.sqrt (squaredLength v : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (hv0.le.trans hlo) hup 2
      _ = _ := Real.sq_sqrt (by positivity)
  exact ⟨hv0.trans_le hlo, hup.trans hh, by linarith⟩

private def latticeDet (v x : ℤ × ℤ) : ℤ := v.1 * x.2 - v.2 * x.1

private theorem latticeDet_modEq {p : ℕ} [Fact p.Prime] {α β : ZMod p}
    (hproj : α ≠ 0 ∨ β ≠ 0) (v x y : ℤ × ℤ)
    (hv : α * (v.1 : ZMod p) + β * (v.2 : ZMod p) = 0)
    (hxy : α * (x.1 : ZMod p) + β * (x.2 : ZMod p) =
      α * (y.1 : ZMod p) + β * (y.2 : ZMod p)) :
    latticeDet v x ≡ latticeDet v y [ZMOD (p : ℤ)] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  have h : α * ((x.1 : ZMod p) - y.1) + β * ((x.2 : ZMod p) - y.2) = 0 := by
    linear_combination hxy
  have hd : α * ((latticeDet v x : ZMod p) - (latticeDet v y : ZMod p)) = 0 := by
    simp only [latticeDet, Int.cast_sub, Int.cast_mul]
    linear_combination ((x.2 : ZMod p) - y.2) * hv - (v.2 : ZMod p) * h
  have he : β * ((latticeDet v x : ZMod p) - (latticeDet v y : ZMod p)) = 0 := by
    simp only [latticeDet, Int.cast_sub, Int.cast_mul]
    linear_combination (v.1 : ZMod p) * h - ((x.1 : ZMod p) - y.1) * hv
  rcases hproj with ha | hb
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left ha)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hb)

private theorem latticeDet_span (v x y : ℤ × ℤ) (H : ℕ)
    (hx : |x.1 - y.1| ≤ (H : ℤ)) (hy : |x.2 - y.2| ≤ (H : ℤ)) :
    |latticeDet v x - latticeDet v y| ≤ (2 * H * max v.1.natAbs v.2.natAbs : ℕ) := by
  have e : latticeDet v x - latticeDet v y =
      v.1 * (x.2 - y.2) + (-v.2) * (x.1 - y.1) := by dsimp [latticeDet]; ring
  have h₁ : |v.1| ≤ (max v.1.natAbs v.2.natAbs : ℕ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast le_max_left v.1.natAbs v.2.natAbs
  have h₂ : |v.2| ≤ (max v.1.natAbs v.2.natAbs : ℕ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast le_max_right v.1.natAbs v.2.natAbs
  rw [e]
  calc
    _ ≤ |v.1 * (x.2 - y.2)| + |(-v.2) * (x.1 - y.1)| := abs_add_le _ _
    _ ≤ (max v.1.natAbs v.2.natAbs : ℕ) * (H : ℤ) +
        (max v.1.natAbs v.2.natAbs : ℕ) * (H : ℤ) := by
          simp only [abs_mul, abs_neg]
          exact add_le_add (mul_le_mul h₁ hy (abs_nonneg _) (by positivity))
            (mul_le_mul h₂ hx (abs_nonneg _) (by positivity))
    _ = _ := by push_cast; ring

private theorem latticeDet_eq_displacement (v x y : ℤ × ℤ)
    (hprim : Int.gcd v.1 v.2 = 1) (hdet : latticeDet v x = latticeDet v y) :
    ∃ k : ℤ, x.1 - y.1 = k * v.1 ∧ x.2 - y.2 = k * v.2 := by
  have hg := Int.gcd_eq_gcd_ab v.1 v.2
  rw [hprim, Nat.cast_one] at hg
  let k := v.1.gcdA v.2 * (x.1 - y.1) + v.1.gcdB v.2 * (x.2 - y.2)
  refine ⟨k, ?_, ?_⟩ <;> dsimp [k]
  · dsimp [latticeDet] at hdet
    linear_combination (x.1 - y.1) * hg - v.1.gcdB v.2 * hdet
  · dsimp [latticeDet] at hdet
    linear_combination (x.2 - y.2) * hg + v.1.gcdA v.2 * hdet

private theorem row_code_toNat {a m b : ℤ} (hm : 0 < m)
    (hab : a ≤ b) : (a / m).toNat ≤ (b / m).toNat :=
  Int.toNat_le_toNat (Int.ediv_le_ediv hm hab)

private theorem row_code_inj {a b t m : ℤ} (hm : 0 ≤ m)
    (ha : t ≤ a) (hb : t ≤ b) (hmod : a ≡ b [ZMOD m])
    (hcode : ((a - t) / m).toNat = ((b - t) / m).toNat) : a = b := by
  have ha' := Int.ediv_nonneg (show 0 ≤ a - t by omega) hm
  have hb' := Int.ediv_nonneg (show 0 ≤ b - t by omega) hm
  have h : (a - t) / m = (b - t) / m := by omega
  have hs : a - t ≡ b - t [ZMOD m] := hmod.sub (Int.ModEq.refl t)
  have h' := (Int.modEq_iff_eq_of_div_eq h).mp hs
  omega

private theorem translated_lattice_rows_card {p : ℕ} [Fact p.Prime]
    {α β c : ZMod p} (hproj : α ≠ 0 ∨ β ≠ 0)
    (v : ℤ × ℤ) (hprim : Int.gcd v.1 v.2 = 1)
    (hv : α * (v.1 : ZMod p) + β * (v.2 : ZMod p) = 0)
    (T : Finset (ℤ × ℤ)) (L M : ℤ) (H : ℕ)
    (hbox : ∀ x ∈ T, L ≤ x.1 ∧ x.1 ≤ L + H ∧ M ≤ x.2 ∧ x.2 ≤ M + H)
    (hres : ∀ x ∈ T, α * (x.1 : ZMod p) + β * (x.2 : ZMod p) = c) :
    let ell := max v.1.natAbs v.2.natAbs
    T.card ≤ (1 + (2 * H * ell) / p) * (1 + H / ell) := by
  classical
  dsimp only
  let ell := max v.1.natAbs v.2.natAbs
  change T.card ≤ (1 + (2 * H * ell) / p) * (1 + H / ell)
  have hp : 0 < (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hell : 0 < (ell : ℤ) := by
    by_contra h
    have h₁ := le_max_left v.1.natAbs v.2.natAbs
    have h₂ := le_max_right v.1.natAbs v.2.natAbs
    have hnell : ¬ 0 < ell := by exact_mod_cast h
    dsimp [ell] at hnell
    have e₁ : v.1 = 0 := by omega
    have e₂ : v.2 = 0 := by omega
    simp [e₁, e₂] at hprim
  by_cases hn : T.Nonempty
  · let D := (T.image (latticeDet v)).min' (hn.image _)
    have hm (x : ℤ × ℤ) (hx : x ∈ T) : D ≤ latticeDet v x :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)
    obtain ⟨x₀, hx₀, he₀⟩ : ∃ x₀ ∈ T, latticeDet v x₀ = D :=
      Finset.mem_image.mp (Finset.min'_mem _ (hn.image _))
    have hd (x : ℤ × ℤ) (hx : x ∈ T) : latticeDet v x - D ≤ (2 * H * ell : ℕ) := by
      obtain ⟨u₁, u₂, u₃, u₄⟩ := hbox x hx
      obtain ⟨v₁, v₂, v₃, v₄⟩ := hbox x₀ hx₀
      have hh := latticeDet_span v x x₀ H (abs_le.mpr ⟨by omega, by omega⟩)
        (abs_le.mpr ⟨by omega, by omega⟩)
      rw [he₀] at hh
      exact (le_abs_self _).trans hh
    let first (x : ℤ × ℤ) := ((latticeDet v x - D) / p).toNat
    have hf (x : ℤ × ℤ) (hx : x ∈ T) : first x < 1 + (2 * H * ell) / p := by
      have hh := row_code_toNat hp (hd x hx)
      rw [← Int.natCast_ediv, Int.toNat_natCast] at hh
      change first x ≤ _ at hh
      omega
    have hf_inj (x : ℤ × ℤ) (hx : x ∈ T) (y : ℤ × ℤ) (hy : y ∈ T)
        (hxy : first x = first y) : latticeDet v x = latticeDet v y :=
      row_code_inj hp.le (hm x hx) (hm y hy)
        (latticeDet_modEq hproj v x y hv ((hres x hx).trans (hres y hy).symm)) hxy
    let coord (x : ℤ × ℤ) := if v.2.natAbs ≤ v.1.natAbs then x.1 else x.2
    let lo : ℤ := if v.2.natAbs ≤ v.1.natAbs then L else M
    have hc (x : ℤ × ℤ) (hx : x ∈ T) : lo ≤ coord x ∧ coord x ≤ lo + H := by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hbox x hx
      by_cases h : v.2.natAbs ≤ v.1.natAbs <;> simp [coord, lo, *]
    let code (x : ℤ × ℤ) := (first x, ((coord x - lo) / ell).toNat)
    rw [← Finset.card_range (n := 1 + (2 * H * ell) / p),
      ← Finset.card_range (n := 1 + H / ell), ← Finset.card_product]
    apply Finset.card_le_card_of_injOn code
    · intro x hx
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_range.mpr (hf x hx), Finset.mem_range.mpr ?_⟩
      obtain ⟨h₁, h₂⟩ := hc x hx
      have hh := row_code_toNat hell
        (show coord x - lo ≤ (H : ℤ) by omega)
      rw [← Int.natCast_ediv, Int.toNat_natCast] at hh
      dsimp [code]
      omega
    · intro x hx y hy hxy
      have e := hf_inj x hx y hy (congrArg Prod.fst hxy)
      obtain ⟨k, hk₁, hk₂⟩ := latticeDet_eq_displacement v x y hprim e
      have hu : coord x = coord y := by
        apply row_code_inj hell.le (hc x hx).1 (hc y hy).1 _ (congrArg Prod.snd hxy)
        apply Int.modEq_iff_dvd.mpr
        by_cases h : v.2.natAbs ≤ v.1.natAbs
        · simp only [coord, ite_eq_left h, ell, max_eq_left h]
          have hdv : (v.1.natAbs : ℤ) ∣ v.1 := Int.natAbs_dvd_natAbs.mp (by simp)
          rw [show y.1 - x.1 = -k * v.1 by linear_combination -hk₁]
          exact dvd_mul_of_dvd_right hdv _
        · simp only [coord, ite_eq_right h, ell, max_eq_right (Nat.le_of_not_ge h)]
          have hdv : (v.2.natAbs : ℤ) ∣ v.2 := Int.natAbs_dvd_natAbs.mp (by simp)
          rw [show y.2 - x.2 = -k * v.2 by linear_combination -hk₂]
          exact dvd_mul_of_dvd_right hdv _
      have hk : k = 0 := by
        by_cases h : v.2.natAbs ≤ v.1.natAbs
        · simp only [coord, ite_eq_left h] at hu
          have hv₁ : v.1 ≠ 0 := by
            intro hv₀
            have he : ell = v.1.natAbs := max_eq_left h
            simp [he, hv₀] at hell
          exact (mul_eq_zero.mp (show k * v.1 = 0 by omega)).resolve_right hv₁
        · simp only [coord, ite_eq_right h] at hu
          have hv₂ : v.2 ≠ 0 := by
            intro hv₀
            have he : ell = v.2.natAbs := max_eq_right (Nat.le_of_not_ge h)
            simp [he, hv₀] at hell
          exact (mul_eq_zero.mp (show k * v.2 = 0 by omega)).resolve_right hv₂
      rw [hk, zero_mul] at hk₁ hk₂
      exact Prod.ext (sub_eq_zero.mp hk₁) (sub_eq_zero.mp hk₂)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]
private def projectiveReading {p : ℕ} (d : Option (ZMod p)) (v : ℤ × ℤ) : ZMod p :=
  match d with
  | none => (v.2 : ZMod p)
  | some t => (v.1 : ZMod p) + t * (v.2 : ZMod p)

private theorem int_eq_zero_of_short_cast_eq_zero {p : ℕ} (a : ℤ) (ha : a.natAbs < p)
    (hz : (a : ZMod p) = 0) : a = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)
  simpa using ha

private theorem unique_projective_kernel {p : ℕ} [Fact p.Prime]
    {d e : Option (ZMod p)} {v : ℤ × ℤ}
    (hv : ¬ (v.1 = 0 ∧ v.2 = 0))
    (hshort : max v.1.natAbs v.2.natAbs < p)
    (hd : projectiveReading d v = 0) (he : projectiveReading e v = 0) : d = e := by
  have hn : ¬ ((v.1 : ZMod p) = 0 ∧ (v.2 : ZMod p) = 0) := by
    rintro ⟨hx, hy⟩
    exact hv ⟨int_eq_zero_of_short_cast_eq_zero v.1 ((le_max_left _ _).trans_lt hshort) hx,
      int_eq_zero_of_short_cast_eq_zero v.2 ((le_max_right _ _).trans_lt hshort) hy⟩
  cases d with
  | none =>
    cases e with
    | none => rfl
    | some e =>
      change (v.2 : ZMod p) = 0 at hd
      change (v.1 : ZMod p) + e * (v.2 : ZMod p) = 0 at he
      simp only [hd, mul_zero, add_zero] at he
      exact (hn ⟨he, hd⟩).elim
  | some d =>
    cases e with
    | none =>
      change (v.1 : ZMod p) + d * (v.2 : ZMod p) = 0 at hd
      change (v.2 : ZMod p) = 0 at he
      simp only [he, mul_zero, add_zero] at hd
      exact (hn ⟨hd, he⟩).elim
    | some e =>
      change (v.1 : ZMod p) + d * (v.2 : ZMod p) = 0 at hd
      change (v.1 : ZMod p) + e * (v.2 : ZMod p) = 0 at he
      have hy : (v.2 : ZMod p) ≠ 0 := by
        intro hy
        simp only [hy, mul_zero, add_zero] at hd
        exact hn ⟨hd, hy⟩
      exact congrArg some (mul_right_cancel₀ hy (add_left_cancel (hd.trans he.symm)))

private theorem short_projective_directions_card {p B : ℕ} [Fact p.Prime]
    (hB : B ≤ p) (T : Finset (Option (ZMod p)))
    (hT : ∀ d ∈ T, ∃ v : ℤ × ℤ, ¬ (v.1 = 0 ∧ v.2 = 0) ∧
      max v.1.natAbs v.2.natAbs < B ∧ projectiveReading d v = 0) :
    T.card ≤ (2 * B - 1) ^ 2 := by
  classical
  let f (d : Option (ZMod p)) : ℤ × ℤ := if hd : d ∈ T then (hT d hd).choose else (0, 0)
  have hspec (d : Option (ZMod p)) (hd : d ∈ T) :
      ¬ ((f d).1 = 0 ∧ (f d).2 = 0) ∧
        max (f d).1.natAbs (f d).2.natAbs < B ∧ projectiveReading d (f d) = 0 := by
    simpa only [f, dite_eq_left hd] using (hT d hd).choose_spec
  let I := Finset.Icc (1 - (B : ℤ)) ((B : ℤ) - 1)
  have hm : Set.MapsTo f T (I ×ˢ I : Finset (ℤ × ℤ)) := by
    intro d hd
    have hd' : d ∈ T := hd
    have hl := (le_max_left _ _).trans_lt (hspec d hd').2.1
    have hr := (le_max_right _ _).trans_lt (hspec d hd').2.1
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (by omega),
      Finset.mem_Icc.mpr (by omega)⟩
  have hi : Set.InjOn f T := by
    intro d hd e he hv
    have hd' : d ∈ T := hd
    have he' : e ∈ T := he
    obtain ⟨hn, hb, hk⟩ := hspec d hd'
    exact unique_projective_kernel hn (hb.trans_le hB) hk (hv ▸ (hspec e he').2.2)
  have hI : I.card = 2 * B - 1 := by
    dsimp only [I]
    rw [Int.card_Icc]
    omega
  calc
    T.card ≤ (I ×ˢ I).card := Finset.card_le_card_of_injOn f hm hi
    _ = (2 * B - 1) ^ 2 := by rw [Finset.card_product, hI, pow_two]

private theorem short_projective_directions_real {p : ℕ} [Fact p.Prime] {R : ℝ}
    (hR : 1 ≤ R) (hRp : R ≤ (p : ℝ)) (T : Finset (Option (ZMod p)))
    (hT : ∀ d ∈ T, ∃ v : ℤ × ℤ, ¬ (v.1 = 0 ∧ v.2 = 0) ∧
      ((max v.1.natAbs v.2.natAbs : ℕ) : ℝ) < R ∧ projectiveReading d v = 0) :
    (T.card : ℝ) ≤ 9 * R ^ 2 := by
  let B := Nat.ceil R
  have hB : B ≤ p := Nat.ceil_le.mpr hRp
  have hC : T.card ≤ (2 * B - 1) ^ 2 := by
    apply short_projective_directions_card hB T
    intro d hd
    obtain ⟨v, hv, hs, hk⟩ := hT d hd
    exact ⟨v, hv, Nat.lt_ceil.mpr hs, hk⟩
  have hpos : 0 < B := Nat.lt_ceil.mpr (by simpa using (zero_lt_one.trans_le hR))
  have hsub : ((2 * B - 1 : ℕ) : ℝ) = 2 * (B : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hle : 2 * (B : ℝ) - 1 ≤ 3 * R := by
    have hceil : (B : ℝ) < R + 1 := Nat.ceil_lt_add_one (zero_le_one.trans hR)
    linarith
  have hnonneg : 0 ≤ ((2 * B - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : (((2 * B - 1 : ℕ) : ℝ)) ^ 2 ≤ (3 * R) ^ 2 :=
    pow_le_pow_left₀ hnonneg (hsub.symm ▸ hle) 2
  have hCast : (T.card : ℝ) ≤ (((2 * B - 1 : ℕ) : ℝ)) ^ 2 := by exact_mod_cast hC
  exact hCast.trans (hsq.trans (le_of_eq (by ring)))


private lemma shape_bound {p H L m : ℝ} (hp : 0 < p) (hH : 1 ≤ H) (hL : 0 < L)
    (hm : 0 < m) (hLsq : L ^ 2 ≤ p) (hcomp : m ≤ 2 * L) :
    (H + 1) ^ 2 * ((1 + 2 * H * L / p) * (1 + H / L)) ≤
      8 * (H ^ 4 / p) + 24 * (H ^ 3 / m) + 4 * H ^ 2 := by
  have hH0 : 0 ≤ H := by linarith
  have hrows : H * L / p ≤ H / L := by
    apply (div_le_div_iff₀ hp hL).2
    nlinarith [mul_nonneg hH0 (sub_nonneg.mpr hLsq)]
  have hcomp' : H ^ 3 / L ≤ 2 * (H ^ 3 / m) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hL hm).2
    nlinarith [mul_nonneg (show 0 ≤ H ^ 3 by positivity) (sub_nonneg.mpr hcomp)]
  have hsq : (H + 1) ^ 2 ≤ 4 * H ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 3 * H + 1 by positivity)
      (show 0 ≤ H-1 from sub_nonneg.mpr hH)]
  have he : (1 + 2 * H * L / p) * (1 + H / L) = 1 + H / L + 2 * (H * L / p) + 2 * (H ^ 2 / p) := by
    field_simp
    ring
  calc
    _ ≤ (4 * H ^ 2) * ((1 + 2 * H * L / p) * (1 + H / L)) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ (4 * H ^ 2) * (1 + 3 * (H / L) + 2 * (H ^ 2 / p)) := by
      rw [he]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = 8 * (H ^ 4 / p) + 12 * (H ^ 3 / L) + 4 * H ^ 2 := by ring
    _ ≤ _ := by linarith

private lemma volume_bound {p H m : ℝ} (hp : 0 < p) (hH : 1 ≤ H)
    (hm : 0 < m) (hmsq : m ^ 2 ≤ 2 * p) (hlong : p / H ≤ m) :
    8 * (H ^ 4 / p) + 24 * (H ^ 3 / m) + 4 * H ^ 2 ≤ 40 * (H ^ 4 / p) := by
  have hH0 : 0 < H := by linarith
  have hpm : p ≤ m * H := (div_le_iff₀ hH0).1 hlong
  have hlong' : H ^ 3 / m ≤ H ^ 4 / p := by
    apply (div_le_div_iff₀ hm hp).2
    nlinarith [mul_nonneg (show 0 ≤ H ^ 3 by positivity) (sub_nonneg.mpr hpm)]
  have hp2 : p ≤ 2 * H ^ 2 := by
    have h1 : p * p ≤ (m * H) * (m * H) :=
      mul_le_mul hpm hpm hp.le (by positivity)
    have h2 : (m * H) * (m * H) ≤ 2 * p * H ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ H ^ 2 by positivity) (sub_nonneg.mpr hmsq)]
    have h3 := h1.trans h2
    apply le_of_mul_le_mul_right (a := p) _ hp
    nlinarith
  have hlast : H ^ 2 ≤ 2 * (H ^ 4 / p) := by
     have hh : H ^ 2 ≤ (2 * H ^ 4) / p := by
      apply (le_div_iff₀ hp).2
      nlinarith [mul_nonneg (show 0 ≤ H ^ 2 by positivity) (sub_nonneg.mpr hp2)]
     simpa only [mul_div_assoc] using hh
  linarith

variable {p : ℕ}

/-- The two lower partial gradients of xy(h-x-y). -/
def cubicGradient (h : ZMod p) (z : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (z.2 * (h - 2 * z.1 - z.2), z.1 * (h - z.1 - 2 * z.2))

private def square (L : ℤ × ℤ) (H : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc L.1 (L.1 + H)).product (Finset.Icc L.2 (L.2 + H))

private lemma card_square (L : ℤ × ℤ) (H : ℕ) : (square L H).card = (H + 1) ^ 2 := by
  have hcard : (square L H).card =
      (Finset.Icc L.1 (L.1 + H)).card * (Finset.Icc L.2 (L.2 + H)).card :=
    Finset.card_product _ _
  rw [hcard, Int.card_Icc, Int.card_Icc, pow_two]
  rw [show L.1 + (H : ℤ) + 1 - L.1 = H + 1 by omega,
    show L.2 + (H : ℤ) + 1 - L.2 = H + 1 by omega]
  norm_cast

/-- Literal integer frequencies of side H with lower dual reading parallel to the cubic gradient. -/
def stationaryFiber (H : ℕ) (L₁ L₂ : ℤ × ℤ) (α β h : ZMod p)
    (z : ZMod p × ZMod p) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((square L₁ H).product (square L₂ H)).filter fun f =>
    kernelReading α β f.1 * (cubicGradient h z).2 =
      kernelReading α β f.2 * (cubicGradient h z).1

private lemma product_slice_card {R S : Type}
    (A : Finset R) (B : Finset S) (F : Finset (R × S)) (N : ℕ)
    (hF : F ⊆ A.product B)
    (hN : ∀ r ∈ A, ∃ U : Finset S, (∀ s, (r, s) ∈ F → s ∈ U) ∧ U.card ≤ N) :
    F.card ≤ A.card * N := by
  classical
  have hproj : ∀ z ∈ F, z.1 ∈ A :=
    fun z hz => (Finset.mem_product.mp (hF hz)).1
  rw [Finset.card_eq_sum_card_fiberwise hproj]
  calc
    _ ≤ ∑ _r ∈ A, N := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨U, hU, hbound⟩ := hN r hr
      apply le_trans _ hbound
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hz, hrz⟩
        exact hU z.2 (show (r, z.2) ∈ F by simpa only [← hrz, Prod.eta] using hz)
      · intro z hz w hw hwz
        exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm) hwz
    _ = A.card * N := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

private lemma stationary_card_of_rows [Fact p.Prime] (H : ℕ) (L₁ L₂ : ℤ × ℤ)
    (α β h : ZMod p) (z : ZMod p × ZMod p) (hgrad : cubicGradient h z ≠ 0)
    (N : ℕ) (hrows : ∀ (L : ℤ × ℤ) (r : ZMod p),
      ((square L H).filter fun w => kernelReading α β w = r).card ≤ N) :
    (stationaryFiber H L₁ L₂ α β h z).card ≤ (H + 1) ^ 2 * N := by
  classical
  let F := stationaryFiber H L₁ L₂ α β h z
  let g := cubicGradient h z
  by_cases hg : g.1 = 0
  · have hg₂ : g.2 ≠ 0 := fun hz => hgrad (Prod.ext hg hz)
    let e : ((ℤ × ℤ) × (ℤ × ℤ)) ↪ ((ℤ × ℤ) × (ℤ × ℤ)) :=
      ⟨Prod.swap, Prod.swap_injective⟩
    change F.card ≤ _
    rw [← (Finset.card_map (s := F) e), ← card_square L₂ H]
    apply product_slice_card (square L₂ H) (square L₁ H) (F.map e) N
    · intro q hq
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hq
      obtain ⟨hw₁, hw₂⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hw).1
      exact Finset.mem_product.mpr ⟨hw₂, hw₁⟩
    · intro r hr
      refine ⟨(square L₁ H).filter fun w => kernelReading α β w = 0, ?_, hrows L₁ 0⟩
      intro s hs
      have hmem : (s,r) ∈ F := by
        obtain ⟨w, hw, he⟩ := Finset.mem_map.mp hs
        have hw' : w = (s,r) := e.injective he
        rwa [hw'] at hw
      obtain ⟨hpair, hread⟩ := Finset.mem_filter.mp hmem
      change kernelReading α β s * g.2 = kernelReading α β r * g.1 at hread
      rw [hg, mul_zero] at hread
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_product.mp hpair).1, (mul_eq_zero.mp hread).resolve_right hg₂⟩
  · rw [← card_square L₁ H]
    apply product_slice_card (square L₁ H) (square L₂ H) F N
    · exact Finset.filter_subset _ _
    · intro r hr
      let t := kernelReading α β r * g.2 / g.1
      refine ⟨(square L₂ H).filter fun w => kernelReading α β w = t, ?_, hrows L₂ t⟩
      intro s hs
      obtain ⟨hpair, hread⟩ := Finset.mem_filter.mp hs
      refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hpair).2, ?_⟩
      exact (eq_div_iff hg).2 hread.symm


/-- The nonzero normalized projective pivot, with the vertical line represented by none. -/
def pivotCoefficients (d : Option (ZMod p)) : ZMod p × ZMod p :=
  match d with
  | none => (0, 1)
  | some t => (1, t)

private lemma pivot_reading (d : Option (ZMod p)) (v : ℤ × ℤ) :
    projectiveReading d v =
      kernelReading (pivotCoefficients d).1 (pivotCoefficients d).2 v := by
  cases d <;> simp [projectiveReading, kernelReading, pivotCoefficients]

/-- Width, actual smooth fixed-sum cubic point, and translated literal box corners. -/
structure StationarySlice where
  p : ℕ
  prime : p.Prime
  H : ℕ
  width_pos : 1 ≤ H
  width_lt : H < p
  firstCorner : ℤ × ℤ
  secondCorner : ℤ × ℤ
  h : ZMod p
  point : ZMod p × ZMod p
  smooth : cubicGradient h point ≠ 0

/-- The actual number of integer frequency quadruples satisfying stationarity. -/
def stationaryCount (R : StationarySlice) (d : ZMod R.p × ZMod R.p) : ℕ :=
  (stationaryFiber R.H R.firstCorner R.secondCorner d.1 d.2 R.h R.point).card

/-- Euclidean shortest length of the reduced index-p congruence kernel. -/
noncomputable def directionMinimum (R : StationarySlice) (d : ZMod R.p × ZMod R.p) : ℝ := by
  let : Fact R.p.Prime := ⟨R.prime⟩
  exact euclideanMinimum d.1 d.2

/-- All normalized directions with Euclidean minimum below the physical threshold p/H. -/
noncomputable def shortDirections (R : StationarySlice) : Finset (Option (ZMod R.p)) := by
  classical
  let : Fact R.p.Prime := ⟨R.prime⟩
  exact Finset.univ.filter fun d => directionMinimum R (pivotCoefficients d) < (R.p : ℝ) / R.H

private lemma cast_div_le (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hb)).2
  exact_mod_cast Nat.div_mul_le_self a b

/-- A literal stationary count, its volume case, and the short directions. -/
theorem single_fibre_inventory (R : StationarySlice) (d : ZMod R.p × ZMod R.p)
    (hproj : d.1 ≠ 0 ∨ d.2 ≠ 0) :
    (stationaryCount R d : ℝ) ≤
      8 * ((R.H : ℝ) ^ 4 / R.p) + 24 * ((R.H : ℝ) ^ 3 / directionMinimum R d) +
        4 * (R.H : ℝ) ^ 2 ∧
    ((R.p : ℝ) / R.H ≤ directionMinimum R d →
      (stationaryCount R d : ℝ) ≤ 40 * ((R.H : ℝ) ^ 4 / R.p)) ∧
    ((shortDirections R).card : ℝ) ≤ 9 * ((R.p : ℝ) / R.H) ^ 2 := by
  classical
  let : Fact R.p.Prime := ⟨R.prime⟩
  let α := d.1
  let β := d.2
  let H := R.H
  let p := R.p
  let m := directionMinimum R d
  obtain ⟨v, hv, hvker, hprim, hvp, hvmin⟩ := exists_shortest_primitive α β
  let ell := supLength v
  have hel : 0 < ell := supLength_pos hv
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast R.prime.pos
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast R.width_pos
  have hH0 : (0 : ℝ) < H := by linarith
  obtain ⟨hm, hcomp, hmsq⟩ := minimum_compare hv hvker hvp hvmin
  change 0 < m at hm
  change m ≤ 2 * (ell : ℝ) at hcomp
  change m ^ 2 ≤ 2 * (p : ℝ) at hmsq
  let N : ℕ := (1 + (2 * H * ell) / p) * (1 + H / ell)
  have hrows (L : ℤ × ℤ) (r : ZMod p) :
      ((square L H).filter fun w => kernelReading α β w = r).card ≤ N := by
    let T := (square L H).filter fun w => kernelReading α β w = r
    have hbox : ∀ x ∈ T,
        L.1 ≤ x.1 ∧ x.1 ≤ L.1 + H ∧ L.2 ≤ x.2 ∧ x.2 ≤ L.2 + H := by
      intro x hx
      have hs : x ∈ square L H := (Finset.mem_filter.mp hx).1
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hs
      exact ⟨(Finset.mem_Icc.mp h1).1, (Finset.mem_Icc.mp h1).2,
        (Finset.mem_Icc.mp h2).1, (Finset.mem_Icc.mp h2).2⟩
    exact translated_lattice_rows_card hproj v
      (Int.isCoprime_iff_gcd_eq_one.mp hprim) hvker T L.1 L.2 H hbox
      (fun x hx => (Finset.mem_filter.mp hx).2)
  have hc : stationaryCount R d ≤ (H + 1) ^ 2 * N :=
    stationary_card_of_rows H R.firstCorner R.secondCorner α β R.h R.point R.smooth N hrows
  have hf1 : (((2 * H * ell) / p : ℕ) : ℝ) ≤ 2 * (H : ℝ) * ell / p := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using cast_div_le (2 * H * ell) p R.prime.pos
  have hf2 := cast_div_le H ell hel
  have hb : (N : ℝ) ≤ (1 + 2 * (H : ℝ) * ell / p) * (1 + (H : ℝ) / ell) := by
    dsimp only [N]
    push_cast
    exact mul_le_mul (by linarith only [hf1]) (by linarith only [hf2])
      (by positivity) (by positivity)
  have hcards : (stationaryCount R d : ℝ) ≤ ((H : ℝ) + 1) ^ 2 * (N : ℝ) := by
    exact_mod_cast hc
  have hl : 0 < (ell : ℝ) := by exact_mod_cast hel
  have hlsq : (ell : ℝ) ^ 2 ≤ (p : ℝ) := by
    exact_mod_cast (Nat.pow_le_pow_left hvp 2).trans (Nat.sqrt_le' p)
  have primary : (stationaryCount R d : ℝ) ≤
      8 * ((H : ℝ) ^ 4 / p) + 24 * ((H : ℝ) ^ 3 / m) + 4 * (H : ℝ) ^ 2 :=
    hcards.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans
      (shape_bound hp0 hH hl hm hlsq hcomp))
  refine ⟨primary, fun hlong => primary.trans (volume_bound hp0 hH hm hmsq hlong), ?_⟩
  apply short_projective_directions_real
  · apply (le_div_iff₀ hH0).2
    simpa only [one_mul] using (show (H : ℝ) ≤ p by exact_mod_cast R.width_lt.le)
  · apply div_le_self hp0.le hH
  · intro t ht
    have hshort : directionMinimum R (pivotCoefficients t) < (p : ℝ) / H :=
      (Finset.mem_filter.mp ht).2
    obtain ⟨w, hw, hwker, hreal⟩ :=
      minimum_attained (pivotCoefficients t).1 (pivotCoefficients t).2
    refine ⟨w, fun ⟨h1, h2⟩ => hw (Prod.ext h1 h2), ?_, ?_⟩
    · calc
        (supLength w : ℝ) ≤ Real.sqrt (squaredLength w : ℝ) := sup_le_sqrt_squared w
        _ = directionMinimum R (pivotCoefficients t) := by
          rw [squaredLength_cast]
          exact hreal.symm
        _ < (p : ℝ) / H := hshort
    · rw [pivot_reading]
      exact hwker

#print axioms single_fibre_inventory

end D5.S3.Arith.CharacterSums.PascadiSingleFibreInventory
