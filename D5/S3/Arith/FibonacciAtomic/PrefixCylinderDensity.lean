/- GID: D5/S3/Arith/FibonacciAtomic/PrefixCylinderDensity
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PrefixCylinderDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Fixed canonical Fibonacci prefixes have bounded counting error and positive natural density. -/

import Mathlib
import D5.S1.Deficit.Displacement.GoldenSubstStartSharpness
import D5.S1.Digit.GoldenZeckendorfLanguage

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PrefixCylinderDensity

open D5.S0.Conventions D5.S1.Deficit.ZeckendorfDisplacementReading
open Filter Topology
open GoldenDesubstitutionZeckendorf
open D5.S1.Words.Powers

/-- The occupied indices of a prefix are descending Fibonacci indices, starting at two.
The length includes any high zero digits. -/
def LegalPrefix (m : ℕ) (w : List ℕ) : Prop :=
  w.IsZeckendorfRep ∧ ∀ k ∈ w, k < m + 2

/-- A final occupied digit forces one additional zero before the free tail. -/
def seamDepth (m : ℕ) (w : List ℕ) : ℕ :=
  m + if m + 1 ∈ w then 1 else 0

/-- Canonical integers whose occupied indices below the prefix boundary are exactly `w`. -/
def cylinder (m : ℕ) (w : List ℕ) : Set ℕ :=
  {n | (wdigits n).filter (fun k => k < m + 2) = w}

/-- The number of cylinder members strictly below a real cutoff; it is zero at nonpositive cutoffs. -/
noncomputable def counting (m : ℕ) (w : List ℕ) (X : ℝ) : ℕ :=
  {n : ℕ | n ∈ cylinder m w ∧ (n : ℝ) < X}.ncard

-- The result includes both canonical tail reconstruction and the real counting estimate.
set_option maxHeartbeats 800000 in
/-- Every legal fixed prefix has a bounded counting discrepancy, its natural density,
and the density ratio of every legal extension. Occupied indices encode low-first binary digits. -/
theorem result (m : ℕ) (w : List ℕ) (hw : LegalPrefix m w) :
    (StrictMono (fun t => (w.map Nat.fib).sum +
      displacementDecode^[seamDepth m w] t) ∧
      Set.range (fun t => (w.map Nat.fib).sum +
        displacementDecode^[seamDepth m w] t) = cylinder m w) ∧
    (∃ C : ℝ, ∀ X : ℝ, 0 ≤ X →
      |(counting m w X : ℝ) - (Real.goldenRatio ^ seamDepth m w)⁻¹ * X| ≤ C) ∧
    Tendsto (fun X : ℝ => (counting m w X : ℝ) / X)
      atTop (𝓝 ((Real.goldenRatio ^ seamDepth m w)⁻¹)) ∧
    (∀ (m' : ℕ) (w' : List ℕ), LegalPrefix m' w' → m ≤ m' →
      w'.filter (fun k => k < m + 2) = w →
      Tendsto (fun X : ℝ => (counting m' w' X : ℝ) / (counting m w X : ℝ))
        atTop (𝓝 (Real.goldenRatio ^
          ((seamDepth m w : ℤ) - (seamDepth m' w' : ℤ))))) := by
  classical
  let φ := Real.goldenRatio
  have hp : 0 < φ := Real.goldenRatio_pos
  have h1 : 1 < φ := Real.one_lt_goldenRatio
  letI : IsTrans ℕ (fun a b => b + 2 ≤ a) := ⟨by intros; omega⟩
  have canonical_iff (l : List ℕ) : l.IsZeckendorfRep ↔
      l.Pairwise (fun a b => b + 2 ≤ a) ∧ ∀ k ∈ l, 2 ≤ k := by
    simp only [List.IsZeckendorfRep, List.isChain_iff_pairwise,
      List.pairwise_append, List.pairwise_singleton, List.mem_singleton,
      true_and, forall_eq, Nat.zero_add]
  have canonical_shift (l : List ℕ) (hl : l.IsZeckendorfRep) (d : ℕ) :
      (l.map (fun k => k + d)).IsZeckendorfRep := by
    rw [canonical_iff, List.pairwise_map]
    obtain ⟨hpair, hmin⟩ := (canonical_iff l).mp hl
    refine ⟨hpair.imp (by intros; omega), ?_⟩
    intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    have := hmin j hj
    omega
  have shift_digits (n : ℕ) :
      wdigits (displacementDecode n) = (wdigits n).map (fun k => k + 1) := by
    rw [← golden_subst_start_eq_displacement_decode]
    exact golden_subst_start_wdigits n
  have iterate_digits (d n : ℕ) :
      wdigits (displacementDecode^[d] n) = (wdigits n).map (fun k => k + d) := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Function.iterate_succ_apply', shift_digits, ih, List.map_map]
      simp [Function.comp_def, Nat.add_assoc]
  have shift_bounds (n : ℕ) : |(displacementDecode n : ℝ) - φ * n| ≤ 1 := by
    obtain ⟨hlo, hhi⟩ := GoldenSubstStartSharpness.golden_subst_start_error_window n
    rw [golden_subst_start_eq_displacement_decode] at hlo hhi
    have hi0 : 0 ≤ φ⁻¹ := inv_nonneg.mpr hp.le
    have hi1 : φ⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ h1).le
    have hs : φ⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hi0 hi1
    exact abs_le.mpr ⟨(neg_le_neg hs).trans hlo, hhi.trans hi1⟩
  have shift_mono : StrictMono displacementDecode := by
    intro a b hab
    simpa only [golden_subst_start_eq_displacement_decode] using goldenSubstStart_strictMono hab
  have iterate_bounds (d n : ℕ) :
      |(displacementDecode^[d] n : ℝ) - φ ^ d * n| ≤ (d : ℝ) * φ ^ d := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Function.iterate_succ_apply']
      have hd : 1 ≤ φ ^ d := one_le_pow₀ h1.le
      have hb := shift_bounds (displacementDecode^[d] n)
      have ht := abs_add_le
        ((displacementDecode (displacementDecode^[d] n) : ℝ) -
          φ * (displacementDecode^[d] n : ℝ))
        (φ * ((displacementDecode^[d] n : ℝ) - φ ^ d * n))
      have he : (displacementDecode (displacementDecode^[d] n) : ℝ) -
          φ ^ (d + 1) * n =
          ((displacementDecode (displacementDecode^[d] n) : ℝ) -
            φ * (displacementDecode^[d] n : ℝ)) +
          φ * ((displacementDecode^[d] n : ℝ) - φ ^ d * n) := by
        rw [pow_succ]; ring
      rw [he]
      rw [abs_mul, abs_of_pos hp] at ht
      have hm := mul_le_mul_of_nonneg_left ih hp.le
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith
  have parametrization (m : ℕ) (w : List ℕ) (hw : LegalPrefix m w) :
      StrictMono (fun t => (w.map Nat.fib).sum + displacementDecode^[seamDepth m w] t) ∧
      Set.range (fun t => (w.map Nat.fib).sum + displacementDecode^[seamDepth m w] t) =
        cylinder m w := by
    let h := seamDepth m w
    have hge : m ≤ h := by simp [h, seamDepth]
    have wbound (k : ℕ) (hk : k ∈ w) : k ≤ h := by
      have hb := hw.2 k hk
      dsimp [h, seamDepth]
      split_ifs with he
      · omega
      · have hn : k ≠ m + 1 := by intro e; exact he (e ▸ hk)
        omega
    have hm : StrictMono (fun t => (w.map Nat.fib).sum + displacementDecode^[h] t) :=
      fun a b hab => Nat.add_lt_add_left ((shift_mono.iterate h) hab) _
    refine ⟨hm, ?_⟩
    ext n
    constructor
    · rintro ⟨t, rfl⟩
      let tail := (wdigits t).map (fun k => k + h)
      have htail := canonical_shift _ (wdigits_isCanonical t) h
      have hc : (tail ++ w).IsZeckendorfRep := by
        rw [canonical_iff, List.pairwise_append]
        refine ⟨⟨(canonical_iff tail).mp htail |>.1,
          (canonical_iff w).mp hw.1 |>.1, ?_⟩, ?_⟩
        · intro a ha b hb
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
          have := (canonical_iff _).mp (wdigits_isCanonical t) |>.2 k hk
          have := wbound b hb
          omega
        · intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact (canonical_iff tail).mp htail |>.2 k hk
          · exact (canonical_iff w).mp hw.1 |>.2 k hk
      have hv : ((tail ++ w).map Nat.fib).sum =
          (w.map Nat.fib).sum + displacementDecode^[h] t := by
        rw [List.map_append, List.sum_append]
        have hd := decode_wdigits (displacementDecode^[h] t)
        rw [iterate_digits] at hd
        dsimp [tail]
        omega
      have hdigits := (wdigits_unique hc hv).symm
      change (wdigits _).filter (fun k => k < m + 2) = w
      rw [hdigits, List.filter_append]
      have ht : tail.filter (fun k => k < m + 2) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
        have := (canonical_iff _).mp (wdigits_isCanonical t) |>.2 k hk
        simp only [decide_eq_true_eq]
        omega
      rw [ht, List.nil_append]
      exact List.filter_eq_self.mpr (by intro k hk; exact decide_eq_true (hw.2 k hk))
    · intro hn
      change (wdigits n).filter (fun k => k < m + 2) = w at hn
      have low : (wdigits n).filter (fun k => k < h + 2) = w := by
        rw [← hn]
        apply List.filter_congr
        intro k hk
        congr 1
        apply propext
        by_cases he : m + 1 ∈ w
        · have hlast : m + 1 ∈ wdigits n := by
            rw [← hn] at he
            exact (List.mem_filter.mp he).1
          have hnot : m + 2 ∉ wdigits n := by
            intro hbad
            exact D5.S1.Digit.GoldenZeckendorfLanguage.canonical_indices_not_adjacent
              (wdigits n) (wdigits_isCanonical n) (m + 1) ⟨hlast, by simpa [Nat.add_assoc] using hbad⟩
          have hkne : k ≠ m + 2 := by intro e; exact hnot (e ▸ hk)
          simp [h, seamDepth, he]
          omega
        · simp [h, seamDepth, he]
      let tail := (wdigits n).filter (fun k => h + 2 ≤ k)
      have htail : tail.IsZeckendorfRep := by
        rw [canonical_iff]
        have hc := (canonical_iff _).mp (wdigits_isCanonical n)
        exact ⟨hc.1.filter _, fun k hk => hc.2 k (List.mem_filter.mp hk).1⟩
      have tbound (k : ℕ) (hk : k ∈ tail) : h + 2 ≤ k :=
        of_decide_eq_true (List.mem_filter.mp hk).2
      let down := tail.map (fun k => k - h)
      have hdown : down.IsZeckendorfRep := by
        rw [canonical_iff, List.pairwise_map]
        refine ⟨((canonical_iff _).mp htail).1.imp_of_mem ?_, ?_⟩
        · intro a b ha hb hab
          have := tbound a ha
          have := tbound b hb
          omega
        · intro k hk
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
          have := tbound a ha
          omega
      let t := (down.map Nat.fib).sum
      have hdt : wdigits t = down := (wdigits_unique hdown rfl).symm
      have restored : wdigits (displacementDecode^[h] t) = tail := by
        rw [iterate_digits, hdt]
        dsimp [down]
        rw [List.map_map]
        convert List.map_id tail using 1
        apply List.map_congr_left
        intro k hk
        dsimp [Function.comp_def]
        exact Nat.sub_add_cancel (by have := tbound k hk; omega)
      have hperm : (tail ++ w).Perm (wdigits n) := by
        have hh := List.filter_append_perm (fun k => decide (h + 2 ≤ k)) (wdigits n)
        have he : (wdigits n).filter (fun k => !decide (h + 2 ≤ k)) = w := by
          rw [← low]
          apply List.filter_congr
          intro k hk
          by_cases hh : h + 2 ≤ k <;> simp [hh, show (k < h + 2) ↔ ¬ h + 2 ≤ k by omega]
        simpa only [he] using hh
      have hv := (hperm.map Nat.fib).sum_eq
      rw [List.map_append, List.sum_append, decode_wdigits] at hv
      have ht := decode_wdigits (displacementDecode^[h] t)
      rw [restored] at ht
      refine ⟨t, ?_⟩
      change (w.map Nat.fib).sum + displacementDecode^[h] t = n
      omega
  have estimate (m : ℕ) (w : List ℕ) (hw : LegalPrefix m w) :
      ∃ C : ℝ, ∀ X : ℝ, 0 ≤ X →
        |(counting m w X : ℝ) - (φ ^ seamDepth m w)⁻¹ * X| ≤ C := by
    let h := seamDepth m w
    let V := (w.map Nat.fib).sum
    let f := fun t => V + displacementDecode^[h] t
    let A := φ ^ h
    let B := (h : ℝ) * A
    have hA : 0 < A := pow_pos hp h
    have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hA.le
    have hV : 0 ≤ (V : ℝ) := Nat.cast_nonneg _
    obtain ⟨hm, hr⟩ := parametrization m w hw
    change StrictMono f at hm
    change Set.range f = cylinder m w at hr
    have error (t : ℕ) : |(f t : ℝ) - ((V : ℝ) + A * t)| ≤ B := by
      simpa [f, A, B, Nat.cast_add] using iterate_bounds h t
    let C := ((V : ℝ) + B) / A + 1
    refine ⟨C, ?_⟩
    intro X hX
    have hex : ∃ t : ℕ, X ≤ (f t : ℝ) := by
      refine ⟨⌈X⌉₊, (Nat.le_ceil X).trans ?_⟩
      exact_mod_cast hm.id_le ⌈X⌉₊
    let k := Nat.find hex
    have hk : X ≤ (f k : ℝ) := Nat.find_spec hex
    have cut : {t : ℕ | (f t : ℝ) < X} = Set.Iio k := by
      ext t
      constructor
      · intro ht
        by_contra h
        have hkt : k ≤ t := le_of_not_gt h
        have hft : (f k : ℝ) ≤ f t := by exact_mod_cast hm.monotone hkt
        exact (not_lt_of_ge (hk.trans hft)) ht
      · intro ht
        exact lt_of_not_ge (Nat.find_min hex ht)
    have image : {n : ℕ | n ∈ cylinder m w ∧ (n : ℝ) < X} = f '' Set.Iio k := by
      ext n
      constructor
      · rintro ⟨hn, hx⟩
        rw [← hr] at hn
        obtain ⟨t, rfl⟩ := hn
        exact ⟨t, by rw [← cut]; exact hx, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        refine ⟨hr ▸ Set.mem_range_self t, ?_⟩
        rw [← cut] at ht
        exact ht
    have count_eq : counting m w X = k := by
      rw [counting, image, Set.ncard_image_of_injective _ hm.injective, Set.ncard_Iio_nat]
    rw [count_eq]
    change |(k : ℝ) - A⁻¹ * X| ≤ C
    have hAC : A * C = (V : ℝ) + B + A := by
      dsimp [C]
      field_simp
    have hAX : A * (A⁻¹ * X) = X := by field_simp
    have e₁ := (abs_le.mp (error k)).2
    have e₂ : A * (k : ℝ) ≤ X + B + A := by
      by_cases hk0 : k = 0
      · simp only [hk0, Nat.cast_zero, mul_zero]
        positivity
      · have hprev : (f (k - 1) : ℝ) < X := lt_of_not_ge
          (Nat.find_min hex (show k - 1 < k by omega))
        have eb := (abs_le.mp (error (k - 1))).1
        have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hcast] at eb
        nlinarith
    rw [abs_le]
    constructor
    · apply le_of_mul_le_mul_left (a := A) _ hA
      nlinarith
    · apply le_of_mul_le_mul_left (a := A) _ hA
      nlinarith
  have density (m : ℕ) (w : List ℕ) (hw : LegalPrefix m w) :
      Tendsto (fun X : ℝ => (counting m w X : ℝ) / X)
        atTop (𝓝 ((φ ^ seamDepth m w)⁻¹)) := by
    obtain ⟨C, hC⟩ := estimate m w hw
    let d := (φ ^ seamDepth m w)⁻¹
    have hz : Tendsto (fun X : ℝ =>
        |(counting m w X : ℝ) / X - d|) atTop (𝓝 0) := by
      apply squeeze_zero' (g := fun X : ℝ => C / X)
        (Filter.Eventually.of_forall (fun X => abs_nonneg _))
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        have hb := hC X hX.le
        have he : (counting m w X : ℝ) / X - d =
            ((counting m w X : ℝ) - d * X) / X := by field_simp
        rw [he, abs_div, abs_of_pos hX]
        exact (div_le_div_of_nonneg_right hb hX.le)
      · exact tendsto_const_nhds.div_atTop tendsto_id
    have ht := ((tendsto_zero_iff_abs_tendsto_zero _).mpr hz).add_const d
    simpa only [sub_add_cancel, zero_add] using ht
  refine ⟨parametrization m w hw, estimate m w hw, density m w hw, ?_⟩
  intro m' w' hw' hmm hrestrict
  have hd := density m w hw
  have hd' := density m' w' hw'
  have hden : (φ ^ seamDepth m w)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (pow_pos hp _))
  have hratio := hd'.div hd hden
  have he : (φ ^ seamDepth m' w')⁻¹ / (φ ^ seamDepth m w)⁻¹ =
      φ ^ ((seamDepth m w : ℤ) - (seamDepth m' w' : ℤ)) := by
    rw [zpow_sub₀ (ne_of_gt hp)]
    simp only [zpow_natCast]
    field_simp
  rw [he] at hratio
  apply hratio.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with X hX
  exact div_div_div_cancel_right₀ hX _ _


end D5.S3.Arith.FibonacciAtomic.PrefixCylinderDensity
