/- GID: D5/S3/ConceptDynamics/Experiment/SelfCalibratingFibers
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/SelfCalibratingFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entire positive shear fibers determine the exact signed continuation capacity. -/

import D5.S3.ConceptDynamics.Experiment.SelfCalibratingRulings
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix

namespace D5.S3.ConceptDynamics.Experiment.SelfCalibratingFibers
open SelfCalibratingRulings
noncomputable section

/-- True selects the actual upper shear; false selects the actual lower shear. -/
def endpoint (upper : Bool) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if upper then !![1, (k : ℝ); 0, 1] else !![1, 0; (k : ℝ), 1]

/-- The full positive source fiber, without its two excluded endpoints. -/
def fiber (upper : Bool) (x z s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if upper then !![x - s, s * (x - s) / z; z, s]
  else !![x - s, z; s * (x - s) / z, s]

/-- A scalar third read at the selected cumulative matrix. -/
def third (upper : Bool) (x z : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) : ℝ :=
  observe B (fiber upper x z s)

/-- Stable recovery from a selected increasing coordinate; lower shears use p=x-s. -/
def recover (upper : Bool) (x z a tau : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let K := x+a*z
  let p := 2*z*(tau-z)/(K+Real.sqrt (K^2-4*z*(tau-z)))
  fiber upper x z (if upper then p else x-p)

/-- The chosen shortest chronological continuation of the actual branch. -/
def continuation (upper : Bool) (x z : ℝ) (k : ℕ) : List Bool :=
  Arith.FibonacciAtomic.SelfCalibratingRawWords.alt (!upper)
    (2 * (⌈x/z⌉₊ - k - (if upper then 1 else 0)) + 1)

/-- The exponent of the selected final cumulative matrix. -/
def finalLevel (upper : Bool) (x z : ℝ) (k : ℕ) : ℕ :=
  max k (⌈x/z⌉₊ - (if upper then 1 else 0))

/-- A causal three-read policy retaining the entire first-read-selected prefixWord. -/
def optimalPolicy (direction : ℝ → Bool) (exponent : ℝ → ℕ)
    (prefixWord : ℝ → List Bool) : History → Sum Query Label
  | [] => .inl ([], [])
  | [a] => .inl ([], prefixWord a.2)
  | [a,b] => .inl (prefixWord a.2,
      continuation (direction a.2) a.2 ((b.2-a.2)/(exponent a.2)) (exponent a.2))
  | [a,b,c] =>
      let upper := direction a.2
      let z := (b.2-a.2)/(exponent a.2)
      let N := finalLevel upper a.2 z (exponent a.2)
      .inr (recover upper a.2 z ((N : ℝ)+(if upper then 1 else 0)) c.2, [])
  | _ => .inr (0, [])

set_option maxHeartbeats 2000000 in
/-- The exact full-fiber criterion includes the open-interval equality boundary,
and the raw signed bound limits every literal continuation in both directions. -/
theorem full_fiber_and_signed_capacity
    (upper : Bool) (x z : ℝ) (hx : 0 < x) (hz : 0 < z)
    (k : ℕ) (hk : 0 < k) (w : List Bool) :
    (∀ (P : History → Sum Query Label), OriginalValid P →
      ∃ (paidWord : List Bool) (j : ℕ) (direction : Bool),
        P [⟨([],[]),x⟩] = .inl ([],paidWord) ∧ 0 < j ∧
          matrix paidWord = endpoint direction j) ∧
    (∀ R : Source, ∃ c l : Fin 2 → ℝ,
      (∀ i, 0 < c i) ∧ (∀ i, 0 < l i) ∧ R.val = Matrix.vecMulVec c l ∧
      ∀ word : List Bool, observe (matrix word) R.val = l ⬝ᵥ (matrix word *ᵥ c)) ∧
    (∀ R : Source,
      (Matrix.trace R.val = x ∧ observe (endpoint upper k) R.val = x + k * z) ↔
      ∃ s ∈ Set.Ioo 0 x, R.val = fiber upper x z s) ∧
    (∀ s ∈ Set.Ioo 0 x,
      (∀ i j, 0 < fiber upper x z s i j) ∧
      fiber upper x z s 0 0 * fiber upper x z s 1 1 =
        fiber upper x z s 0 1 * fiber upper x z s 1 0) ∧
    (let B := matrix w * endpoint upper k
     let e := if upper then B 1 0 else B 0 1
     let D := B 1 1 - B 0 0
     Set.InjOn (third upper x z B) (Set.Ioo 0 x) ↔
       0 < e ∧ e * (x / z) ≤ |D|) ∧
    (Set.InjOn (third upper x z (matrix w * endpoint upper k)) (Set.Ioo 0 x) →
      1 ≤ w.length ∧
      (if upper then x / z ≤ (k : ℝ) + ((w.length + 1) / 2 : ℕ)
       else x / z ≤ (k : ℝ) + ((w.length + 1) / 2 : ℕ) - 1) ∧
      2 * (⌈x / z⌉₊ - k - (if upper then 1 else 0)) + 1 ≤ w.length) ∧
    (∃ v : List Bool,
      v.length = 2 * (⌈x / z⌉₊ - k - (if upper then 1 else 0)) + 1 ∧
      Set.InjOn (third upper x z (matrix v * endpoint upper k)) (Set.Ioo 0 x)) ∧
    (∀ (P : History → Sum Query Label), OriginalValid P → ∀ paidWord : List Bool,
      matrix paidWord = endpoint upper k →
      P [⟨([], []), x⟩] = .inl ([], paidWord) →
      ∃ v : List Bool,
        P [⟨([], []), x⟩, ⟨([], paidWord), x+k*z⟩] = .inl (paidWord, v) ∧
        Set.InjOn (third upper x z (matrix v * endpoint upper k)) (Set.Ioo 0 x) ∧
        (∀ (R : Source), Matrix.trace R.val = x →
          observe (endpoint upper k) R.val = x+k*z →
          ∀ (n : ℕ) (tr : History) (out : Label),
          PassivePolicyNormalization.execute SelfCalibratingRulings.read P n [] R = some (tr,out) →
          paidWord.length + (2*(⌈x/z⌉₊-k-(if upper then 1 else 0))+1) ≤ actualCost tr out)) ∧
    (∀ a : ℝ, x/z ≤ a →
      let f := fun p : ℝ => z+a*p+p*(x-p)/z
      let K := x+a*z
      f '' Set.Ioo 0 x = Set.Ioo z (z+a*x) ∧
      ∀ p ∈ Set.Ioo 0 x,
        0 < K^2-4*z*(f p-z) ∧
        Real.sqrt (K^2-4*z*(f p-z)) = K-2*p ∧
        x < K-p ∧
        2*z*(f p-z)/(K+Real.sqrt (K^2-4*z*(f p-z))) = p ∧
        recover upper x z a (f p) = fiber upper x z (if upper then p else x-p)) ∧
    (let N := finalLevel upper x z k
     let v := continuation upper x z k
     let a : ℝ := (N : ℝ)+(if upper then 1 else 0)
     matrix v * endpoint upper k = matrix [!upper] * endpoint upper N ∧
     matrix v * endpoint upper k =
       (if upper then !![0, 1; 1, (N : ℝ)+1] else !![(N : ℝ), 1; 1, 0]) ∧
     x/z ≤ a ∧
     (third upper x z (matrix v * endpoint upper k)) '' Set.Ioo 0 x =
       Set.Ioo z (z+a*x) ∧
     ∀ s ∈ Set.Ioo 0 x,
       third upper x z (matrix v * endpoint upper k) s =
         z+a*(if upper then s else x-s)+(if upper then s else x-s)*
           (x-(if upper then s else x-s))/z ∧
       recover upper x z a (third upper x z (matrix v * endpoint upper k) s) =
         fiber upper x z s) ∧
    (∀ (direction : ℝ → Bool) (exponent : ℝ → ℕ) (prefixWord : ℝ → List Bool),
      (∀ X : ℝ, 0 < X → 0 < exponent X ∧
        matrix (prefixWord X) = endpoint (direction X) (exponent X)) →
      OriginalValid (optimalPolicy direction exponent prefixWord) ∧
      ∀ R : Source,
        let X := Matrix.trace R.val
        let paid := prefixWord X
        let K := exponent X
        let upper := direction X
        let Y := observe (matrix paid) R.val
        let Z := (Y-X)/(K : ℝ)
        let v := continuation upper X Z K
        let tau := SelfCalibratingRulings.read (paid,v) R
        let tr : History := [⟨([],[]),X⟩, ⟨([],paid),Y⟩, ⟨(paid,v),tau⟩]
        PassivePolicyNormalization.execute SelfCalibratingRulings.read
          (optimalPolicy direction exponent prefixWord) 4 [] R = some (tr,(R.val,[])) ∧
        actualCost tr (R.val,[]) = paid.length +
          (2*(⌈X/Z⌉₊-K-(if upper then 1 else 0))+1) ∧
        matrix (paid++v) = matrix [!upper] * endpoint upper (finalLevel upper X Z K)) ∧
    (∀ paid : List Bool, matrix paid = endpoint upper k → 2*k ≤ paid.length) ∧
    (∃ paid : List Bool, matrix paid = endpoint upper k ∧ paid.length = 2*k) ∧
    (((2*k + (2*(⌈x/z⌉₊-k-(if upper then 1 else 0))+1) : ℕ) : ℤ) =
      if upper then max (2*(k : ℤ)+1) (2*⌈x/z⌉-1)
      else max (2*(k : ℤ)+1) (2*⌈x/z⌉+1)) := by
  have zn : z ≠ 0 := ne_of_gt hz
  have scalar (t₀ D e : ℝ) (he : 0 ≤ e) (he0 : e = 0 → D = 0) :
      Set.InjOn (fun s : ℝ => t₀ + D * s + (e / z) * s * (x - s)) (Set.Ioo 0 x) ↔
        0 < e ∧ e * (x / z) ≤ |D| := by
    by_cases he₀ : e = 0
    · subst e
      have hd : D = 0 := he0 rfl
      simp only [hd, zero_mul, zero_div, add_zero]
      constructor
      · intro hi
        have hh := hi (show x / 3 ∈ Set.Ioo 0 x from ⟨by positivity, by linarith⟩)
          (show 2 * x / 3 ∈ Set.Ioo 0 x from ⟨by positivity, by linarith⟩) rfl
        linarith
      · rintro ⟨h, _⟩; exact False.elim (lt_irrefl _ h)
    have hep : 0 < e := lt_of_le_of_ne he (Ne.symm he₀)
    let a := e / z
    have ha : 0 < a := div_pos hep hz
    have diff (u v : ℝ) :
        (t₀ + D * v + a * v * (x - v)) -
          (t₀ + D * u + a * u * (x - u)) = (v - u) * (D + a * (x - u - v)) := by ring
    constructor
    · intro hi
      refine ⟨hep, ?_⟩
      by_contra h
      have hD : |D| < a * x := by dsimp [a]; simpa [div_mul_eq_mul_div, mul_div_assoc] using lt_of_not_ge h
      have bounds := abs_lt.mp hD
      let vtx := (x + D / a) / 2
      have hv₀ : 0 < vtx := by
        have hb : -x < D / a := (lt_div_iff₀ ha).2 (by nlinarith [bounds.1])
        dsimp [vtx]; linarith
      have hv₁ : vtx < x := by dsimp [vtx]; rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]; have : D / a < x := (div_lt_iff₀ ha).2 (by nlinarith [bounds.2]); linarith
      let eps := min vtx (x - vtx) / 2
      have hp : 0 < eps := by dsimp [eps]; exact half_pos (lt_min hv₀ (sub_pos.mpr hv₁))
      have hp₀ : eps < vtx := by dsimp [eps]; have := min_le_left vtx (x-vtx); linarith
      have hp₁ : eps < x - vtx := by dsimp [eps]; have := min_le_right vtx (x-vtx); linarith
      have hu : vtx - eps ∈ Set.Ioo 0 x := ⟨by linarith, by linarith⟩
      have hv : vtx + eps ∈ Set.Ioo 0 x := ⟨by linarith, by linarith⟩
      have heq : t₀ + D * (vtx - eps) + a * (vtx - eps) * (x - (vtx - eps)) =
          t₀ + D * (vtx + eps) + a * (vtx + eps) * (x - (vtx + eps)) := by
        dsimp [vtx]; field_simp [ne_of_gt ha] <;> ring
      have hh := hi hu hv heq
      linarith
    · rintro ⟨_, hD⟩ u hu v hv heq
      have bound : a * x ≤ |D| := by dsimp [a]; simpa [div_mul_eq_mul_div, mul_div_assoc] using hD
      change t₀ + D * u + a * u * (x-u) = t₀ + D * v + a * v * (x-v) at heq
      have hdiff : (v - u) * (D + a * (x - u - v)) = 0 := by
        rw [← diff]; change _ - _ = 0; rw [heq]; ring
      rcases mul_eq_zero.mp hdiff with h | h
      · linarith
      · have hstrict : |a * (x-u-v)| < a*x := by
          rw [abs_mul, abs_of_pos ha]
          apply mul_lt_mul_of_pos_left _ ha
          exact abs_lt.mpr ⟨by linarith [hu.2,hv.2], by linarith [hu.1,hv.1]⟩
        have hab : |D| = |a * (x-u-v)| := by
          have : D = -(a * (x-u-v)) := by linarith
          rw [this, abs_neg]
        rw [hab] at bound
        linarith
  have charAll : ∀ (upper : Bool) (x z : ℝ), 0 < x → 0 < z →
      ∀ k : ℕ, 0 < k → ∀ R : Source,
      (Matrix.trace R.val = x ∧ observe (endpoint upper k) R.val = x + k * z) ↔
      ∃ s ∈ Set.Ioo 0 x, R.val = fiber upper x z s := by
    intro upper x z hx hz k hk R
    have zn : z ≠ 0 := ne_of_gt hz
    have hp := R.property.1 0 0
    have hs := R.property.1 1 1
    have hrank := R.property.2
    have kp : 0 < (k : ℝ) := by exact_mod_cast hk
    constructor
    · rintro ⟨ht, hy⟩
      have htrace : R.val 0 0 + R.val 1 1 = x := by
        simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using ht
      refine ⟨R.val 1 1, ⟨hs, by linarith⟩, ?_⟩
      cases upper
      · have he : R.val 0 1 = z := by
          simp [observe, endpoint, Matrix.trace, Matrix.diag, Matrix.mul_apply,
            Fin.sum_univ_two] at hy
          nlinarith [htrace]
        ext i j; fin_cases i <;> fin_cases j <;> simp [fiber]
        · linarith
        · exact he
        · rw [eq_div_iff zn]; rw [he] at hrank; nlinarith [hrank, htrace]
      · have he : R.val 1 0 = z := by
          simp [observe, endpoint, Matrix.trace, Matrix.diag, Matrix.mul_apply,
            Fin.sum_univ_two] at hy
          nlinarith [htrace]
        ext i j; fin_cases i <;> fin_cases j <;> simp [fiber]
        · linarith
        · rw [eq_div_iff zn]; rw [he] at hrank; nlinarith [hrank, htrace]
        · exact he
    · rintro ⟨s, _, he⟩
      rw [he]
      cases upper <;> constructor <;>
        simp [fiber, endpoint, observe, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Fin.sum_univ_two] <;> ring
  have characterization := charAll upper x z hx hz k hk
  have positive : ∀ s ∈ Set.Ioo 0 x,
      (∀ i j, 0 < fiber upper x z s i j) ∧
      fiber upper x z s 0 0 * fiber upper x z s 1 1 =
        fiber upper x z s 0 1 * fiber upper x z s 1 0 := by
    intro s hs
    obtain ⟨hs₀, hs₁⟩ := hs
    have hquad : 0 < s*x-s^2 := by nlinarith [mul_pos hs₀ (sub_pos.mpr hs₁)]
    cases upper <;> constructor
    all_goals first
      | (solve | simp [fiber, hs₀, hs₁, hz, hquad])
      | (simp [fiber]; field_simp [zn] <;> ring)
  have raw (w : List Bool) :
      (let B := matrix w * endpoint upper k
       let e := if upper then B 1 0 else B 0 1
       let D := B 1 1-B 0 0
       Set.InjOn (third upper x z B) (Set.Ioo 0 x) ↔ 0<e ∧ e*(x/z)≤|D|) ∧
      (Set.InjOn (third upper x z (matrix w * endpoint upper k)) (Set.Ioo 0 x) →
        1 ≤ w.length ∧
        (if upper then x/z ≤ (k:ℝ)+((w.length+1)/2:ℕ)
         else x/z ≤ (k:ℝ)+((w.length+1)/2:ℕ)-1) ∧
        2*(⌈x/z⌉₊-k-(if upper then 1 else 0))+1 ≤ w.length) := by
    let W := matrix w
    let B := W * endpoint upper k
    let e := if upper then B 1 0 else B 0 1
    let delta := W 1 1 - W 0 0
    let D := B 1 1 - B 0 0
    let eW := if upper then W 1 0 else W 0 1
    have heq : e = eW := by
      cases upper <;> simp [e, eW, B, endpoint, Matrix.mul_apply, Fin.sum_univ_two]
    have hD : D = delta + (if upper then (k : ℝ) else -(k : ℝ)) * e := by
      cases upper <;> simp [D, delta, B, endpoint, Matrix.mul_apply, Fin.sum_univ_two, e] <;> ring
    have packet := Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound w
    have hn : ∀ i j, 0 ≤ W i j := by
      intro i j
      change 0 ≤ (Arith.FibonacciAtomic.SelfCalibratingRawWords.word w i j : ℝ)
      exact_mod_cast packet.2.1 i j
    have he : 0 ≤ e := by rw [heq]; cases upper <;> exact hn _ _
    have bounds : -(((w.length - 1) / 2 : ℕ) : ℝ) * e ≤ delta ∧
        delta ≤ (((w.length + 1) / 2 : ℕ) : ℝ) * e := by
      rw [heq]
      cases upper
      · have h := packet.1 0 1 (by decide)
        constructor
        · dsimp [delta, eW, W, matrix]; exact_mod_cast h.1
        · dsimp [delta, eW, W, matrix]
          have hc : ((Arith.FibonacciAtomic.SelfCalibratingRawWords.word w 1 1 -
              Arith.FibonacciAtomic.SelfCalibratingRawWords.word w 0 0 : ℤ) : ℝ) ≤
              (((((w.length + 1) / 2 : ℕ) : ℤ) *
                Arith.FibonacciAtomic.SelfCalibratingRawWords.word w 0 1 : ℤ) : ℝ) :=
            Int.cast_le.mpr h.2
          simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hc
      · have h := packet.1 1 0 (by decide)
        constructor
        · dsimp [delta, eW, W, matrix]; exact_mod_cast h.1
        · dsimp [delta, eW, W, matrix]
          have hc : ((Arith.FibonacciAtomic.SelfCalibratingRawWords.word w 1 1 -
              Arith.FibonacciAtomic.SelfCalibratingRawWords.word w 0 0 : ℤ) : ℝ) ≤
              (((((w.length + 1) / 2 : ℕ) : ℤ) *
                Arith.FibonacciAtomic.SelfCalibratingRawWords.word w 1 0 : ℤ) : ℝ) :=
            Int.cast_le.mpr h.2
          simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hc
    have he0 : e = 0 → D = 0 := by
      intro hz₀
      have hd : delta = 0 := by rw [hz₀] at bounds; nlinarith [bounds.1,bounds.2]
      rw [hD, hd, hz₀]; ring
    let t₀ := B 0 0 * x + (if upper then B 0 1 else B 1 0) * z
    have formula : third upper x z B = fun s => t₀ + D * s + (e / z) * s * (x - s) := by
      funext s
      cases upper <;>
        simp [third, fiber, observe, t₀, D, e, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have criterion : Set.InjOn (third upper x z B) (Set.Ioo 0 x) ↔
        0 < e ∧ e * (x / z) ≤ |D| := by
      rw [formula]; exact scalar t₀ D e he he0
    have lower : Set.InjOn (third upper x z B) (Set.Ioo 0 x) →
        1 ≤ w.length ∧
        (if upper then x/z ≤ (k:ℝ) + ((w.length+1)/2:ℕ)
         else x/z ≤ (k:ℝ) + ((w.length+1)/2:ℕ)-1) := by
      intro hi
      obtain ⟨hep, hcap⟩ := criterion.mp hi
      have len : 1 ≤ w.length := by
        by_contra h
        have hw : w = [] := List.length_eq_zero_iff.mp (by omega)
        subst w
        cases upper <;> norm_num [e, B, W, matrix,
          Arith.FibonacciAtomic.SelfCalibratingRawWords.word, endpoint, Matrix.mul_apply,
          Fin.sum_univ_two] at hep
      have hL : (w.length - 1) / 2 + 1 = (w.length + 1) / 2 := by omega
      have hLr : (((w.length - 1) / 2 : ℕ) : ℝ) + 1 =
          (((w.length + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hL
      have kr : 1 ≤ (k : ℝ) := by exact_mod_cast hk
      refine ⟨len, ?_⟩
      cases upper
      · have cap : |D| ≤ ((k : ℝ) + ((w.length + 1) / 2 : ℕ) - 1) * e := by
          apply abs_le.mpr
          simp only [Bool.false_eq_true, if_false] at hD
          constructor <;> nlinarith [bounds.1,bounds.2]
        change x / z ≤ (k : ℝ) + ((w.length + 1) / 2 : ℕ) - 1
        apply le_of_mul_le_mul_right _ hep
        nlinarith
      · have cap : |D| ≤ ((k : ℝ) + ((w.length + 1) / 2 : ℕ)) * e := by
          apply abs_le.mpr
          simp only [if_true] at hD
          constructor <;> nlinarith [bounds.1,bounds.2]
        change x / z ≤ (k : ℝ) + ((w.length + 1) / 2 : ℕ)
        apply le_of_mul_le_mul_right _ hep
        nlinarith
    refine ⟨criterion, ?_⟩
    · intro hi
      obtain ⟨len, cap⟩ := lower hi
      refine ⟨len, cap, ?_⟩
      cases upper
      · have hm : ⌈x / z⌉₊ ≤ k + (w.length+1)/2 - 1 := by
          apply Nat.ceil_le.mpr
          rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
          exact cap
        simp only [Bool.false_eq_true, if_false, Nat.sub_zero]
        omega
      · have hm : ⌈x / z⌉₊ ≤ k + (w.length+1)/2 := by
          apply Nat.ceil_le.mpr
          simpa only [Nat.cast_add, if_true] using cap
        simp only [if_true]
        omega
  have inverseAll : ∀ (upper : Bool) (x z : ℝ), 0 < x → 0 < z →
      ∀ a : ℝ, x/z ≤ a →
      let f := fun p : ℝ => z+a*p+p*(x-p)/z
      let K := x+a*z
      f '' Set.Ioo 0 x = Set.Ioo z (z+a*x) ∧
      ∀ p ∈ Set.Ioo 0 x,
        0 < K^2-4*z*(f p-z) ∧
        Real.sqrt (K^2-4*z*(f p-z)) = K-2*p ∧
        x < K-p ∧
        2*z*(f p-z)/(K+Real.sqrt (K^2-4*z*(f p-z))) = p ∧
        recover upper x z a (f p) = fiber upper x z (if upper then p else x-p) := by
    intro upper x z hx hz a ha
    have zn : z ≠ 0 := ne_of_gt hz
    let f := fun p : ℝ => z+a*p+p*(x-p)/z
    let K := x+a*z
    have hax : x ≤ a*z := (div_le_iff₀ hz).mp ha
    have hK : 2*x ≤ K := by dsimp [K]; linarith
    have fzero : f 0 = z := by dsimp [f]; ring
    have fx : f x = z+a*x := by dsimp [f]; ring
    have eqn (p : ℝ) : z*(f p-z) = p*(K-p) := by
      dsimp [f,K]; field_simp [zn] <;> ring
    have range (p : ℝ) (hp : p ∈ Set.Ioo 0 x) : f p ∈ Set.Ioo z (z+a*x) := by
      have hl : 0 < p*(K-p) := mul_pos hp.1 (by linarith [hp.2])
      have hu : 0 < (x-p)*(K-x-p) := mul_pos (sub_pos.mpr hp.2) (by linarith [hp.2])
      have he := eqn p
      constructor <;> nlinarith
    have image : f '' Set.Ioo 0 x = Set.Ioo z (z+a*x) := by
      apply Set.Subset.antisymm
      · rintro t ⟨p,hp,rfl⟩; exact range p hp
      · have cf : ContinuousOn f (Set.Icc 0 x) := by
          apply Continuous.continuousOn
          dsimp [f]; fun_prop
        simpa only [fzero,fx] using intermediate_value_Ioo (le_of_lt hx) cf
    refine ⟨image,?_⟩
    intro p hp
    have hkp : 0 < K-2*p := by linarith [hp.2]
    have discr : K^2-4*z*(f p-z) = (K-2*p)^2 := by nlinarith [eqn p]
    have root : Real.sqrt (K^2-4*z*(f p-z)) = K-2*p := by
      rw [discr, Real.sqrt_sq (le_of_lt hkp)]
    have inverse : 2*z*(f p-z)/(K+Real.sqrt (K^2-4*z*(f p-z))) = p := by
      rw [root]
      have den : K+(K-2*p) ≠ 0 := ne_of_gt (by linarith : 0 < K+(K-2*p))
      apply (div_eq_iff den).mpr
      nlinarith [eqn p]
    refine ⟨by rw [discr]; positivity,root,by linarith [hp.2],inverse,?_⟩
    dsimp only [recover]
    change fiber upper x z (if upper then 2*z*(f p-z)/(K+Real.sqrt (K^2-4*z*(f p-z)))
      else x-2*z*(f p-z)/(K+Real.sqrt (K^2-4*z*(f p-z)))) = _
    rw [inverse]
  have compose (p q : List Bool) : matrix (p++q) = matrix q * matrix p := by
    have hw := (Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound p).2.2.2.1 q
    ext i j
    simp [matrix, hw, Matrix.mul_apply, Fin.sum_univ_two]
  have alen : ∀ a n, (Arith.FibonacciAtomic.SelfCalibratingRawWords.alt a n).length = n := by
    intro a n
    induction n generalizing a with
    | zero => rfl
    | succ n ih => simp [Arith.FibonacciAtomic.SelfCalibratingRawWords.alt, ih]
  have attaining : ∀ (upper : Bool) (X Z : ℝ), 0 < X → 0 < Z →
      ∀ k : ℕ, 0 < k →
      let N := finalLevel upper X Z k
      let v := continuation upper X Z k
      let a : ℝ := (N : ℝ)+(if upper then 1 else 0)
      v.length = 2*(⌈X/Z⌉₊-k-(if upper then 1 else 0))+1 ∧
      matrix v * endpoint upper k = matrix [!upper] * endpoint upper N ∧
      matrix v * endpoint upper k =
        (if upper then !![0, 1; 1, (N : ℝ)+1] else !![(N : ℝ), 1; 1, 0]) ∧
      X/Z ≤ a ∧
      (third upper X Z (matrix v * endpoint upper k)) '' Set.Ioo 0 X =
        Set.Ioo Z (Z+a*X) ∧
      ∀ s ∈ Set.Ioo 0 X,
        third upper X Z (matrix v * endpoint upper k) s =
          Z+a*(if upper then s else X-s)+(if upper then s else X-s)*
            (X-(if upper then s else X-s))/Z ∧
        recover upper X Z a (third upper X Z (matrix v * endpoint upper k) s) =
          fiber upper X Z s := by
    intro upper X Z hX hZ k hk
    let d := ⌈X/Z⌉₊-k-(if upper then 1 else 0)
    let N := finalLevel upper X Z k
    let v := continuation upper X Z k
    let a : ℝ := (N : ℝ)+(if upper then 1 else 0)
    have hN : N = k+d := by
      dsimp [N,finalLevel,d]
      cases upper <;> simp only [Bool.false_eq_true,if_false,if_true,Nat.sub_zero] <;> omega
    have hNr : (N : ℝ) = (k : ℝ)+(d : ℝ) := by exact_mod_cast hN
    have hcap : X/Z ≤ a := by
      have hm : ⌈X/Z⌉₊ ≤ N+(if upper then 1 else 0) := by
        dsimp [N,finalLevel]
        cases upper <;> simp only [Bool.false_eq_true,if_false,if_true,Nat.sub_zero] <;> omega
      have hr : (⌈X/Z⌉₊ : ℝ) ≤ ((N+(if upper then 1 else 0) : ℕ) : ℝ) := by
        exact_mod_cast hm
      apply (Nat.le_ceil (X/Z)).trans
      cases upper <;> simpa [a] using hr
    have odds := (Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound
      []).2.2.2.2.2.1 d
    have hv : matrix v =
        (if upper then !![0,1;1,(d : ℝ)+1] else !![(d : ℝ),1;1,0]) := by
      dsimp [v,continuation]
      change (Arith.FibonacciAtomic.SelfCalibratingRawWords.word
        (Arith.FibonacciAtomic.SelfCalibratingRawWords.alt (!upper) (2*d+1))).map
          (fun n : ℤ => (n : ℝ)) = _
      cases upper
      · simp only [Bool.not_false]
        rw [odds.2]
        ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.map_apply]
      · simp only [Bool.not_true]
        rw [odds.1]
        ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.map_apply]
    have endeq : matrix v * endpoint upper k =
        (if upper then !![0,1;1,(N : ℝ)+1] else !![(N : ℝ),1;1,0]) := by
      rw [hv]
      cases upper <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [endpoint,Matrix.mul_apply,Fin.sum_univ_two,hNr] <;> ring
    have cumulative : matrix v * endpoint upper k = matrix [!upper] * endpoint upper N := by
      rw [endeq]
      cases upper <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [matrix,Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
          Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
          Arith.FibonacciAtomic.GraftAffineClosure.matrixM,endpoint,
          Matrix.mul_apply,Fin.sum_univ_two]
    let f := fun p : ℝ => Z+a*p+p*(X-p)/Z
    have form (s : ℝ) : third upper X Z (matrix v * endpoint upper k) s =
        f (if upper then s else X-s) := by
      rw [endeq]
      cases upper <;>
        simp [third,observe,fiber,f,a,Matrix.trace,Matrix.diag,
          Matrix.mul_apply,Fin.sum_univ_two] <;> ring
    have inverse := inverseAll upper X Z hX hZ a hcap
    have image : (third upper X Z (matrix v * endpoint upper k)) '' Set.Ioo 0 X =
        Set.Ioo Z (Z+a*X) := by
      rw [← inverse.1]
      apply Set.Subset.antisymm
      · rintro t ⟨s,hs,rfl⟩
        rw [form]
        refine ⟨if upper then s else X-s, ?_, rfl⟩
        cases upper <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
          constructor <;> linarith [hs.1,hs.2]
      · rintro t ⟨p,hp,rfl⟩
        refine ⟨if upper then p else X-p, ?_, ?_⟩
        · cases upper <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
            constructor <;> linarith [hp.1,hp.2]
        · rw [form]
          cases upper <;> simp [f]
    refine ⟨alen _ _, cumulative, endeq, hcap, image, ?_⟩
    intro s hs
    have hp : (if upper then s else X-s) ∈ Set.Ioo 0 X := by
      cases upper <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
        constructor <;> linarith [hs.1,hs.2]
    refine ⟨form s, ?_⟩
    rw [form]
    have he := (inverse.2 _ hp).2.2.2.2
    cases upper <;> simpa [f,a,N] using he
  have shortestPrefix : ∀ paid : List Bool,
      matrix paid = endpoint upper k → 2*k ≤ paid.length := by
    intro paid hpaid
    have he : Arith.FibonacciAtomic.SelfCalibratingRawWords.word paid =
        (if upper then !![1,(k : ℤ);0,1] else !![1,0;(k : ℤ),1]) := by
      ext i j
      have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B i j) hpaid
      cases upper <;> fin_cases i <;> fin_cases j <;>
        simp [matrix,endpoint] at h ⊢ <;> exact_mod_cast h
    exact (Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound
      paid).2.2.2.2.2.2 upper k hk he
  have shortestWitness : ∃ paid : List Bool,
      matrix paid = endpoint upper k ∧ paid.length = 2*k := by
    let paid := Arith.FibonacciAtomic.SelfCalibratingRawWords.alt (!upper) (2*k)
    have ev := (Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound
      []).2.2.2.2.1 k
    refine ⟨paid,?_,alen _ _⟩
    change (Arith.FibonacciAtomic.SelfCalibratingRawWords.word
      (Arith.FibonacciAtomic.SelfCalibratingRawWords.alt (!upper) (2*k))).map
        (fun n : ℤ => (n : ℝ)) = _
    cases upper
    · simp only [Bool.not_false]
      rw [ev.2]
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [endpoint,Matrix.map_apply]
    · simp only [Bool.not_true]
      rw [ev.1]
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [endpoint,Matrix.map_apply]
  have optimized : ((2*k + (2*(⌈x/z⌉₊-k-(if upper then 1 else 0))+1) : ℕ) : ℤ) =
      (if upper then max (2*(k : ℤ)+1) (2*⌈x/z⌉-1)
       else max (2*(k : ℤ)+1) (2*⌈x/z⌉+1)) := by
    have hceil := Int.natCast_ceil_eq_ceil (le_of_lt (div_pos hx hz))
    cases upper <;> simp only [Bool.false_eq_true,if_false,if_true,Nat.sub_zero]
    all_goals rw [← hceil]; omega
  have globalPolicy : ∀ (direction : ℝ → Bool) (exponent : ℝ → ℕ)
      (prefixWord : ℝ → List Bool),
      (∀ X : ℝ, 0 < X → 0 < exponent X ∧
        matrix (prefixWord X) = endpoint (direction X) (exponent X)) →
      OriginalValid (optimalPolicy direction exponent prefixWord) ∧
      ∀ R : Source,
        let X := Matrix.trace R.val
        let paid := prefixWord X
        let K := exponent X
        let upper := direction X
        let Y := observe (matrix paid) R.val
        let Z := (Y-X)/(K : ℝ)
        let v := continuation upper X Z K
        let tau := SelfCalibratingRulings.read (paid,v) R
        let tr : History := [⟨([],[]),X⟩, ⟨([],paid),Y⟩, ⟨(paid,v),tau⟩]
        PassivePolicyNormalization.execute SelfCalibratingRulings.read
          (optimalPolicy direction exponent prefixWord) 4 [] R = some (tr,(R.val,[])) ∧
        actualCost tr (R.val,[]) = paid.length +
          (2*(⌈X/Z⌉₊-K-(if upper then 1 else 0))+1) ∧
        matrix (paid++v) = matrix [!upper] * endpoint upper (finalLevel upper X Z K) := by
    intro direction exponent prefixWord hlegal
    let P := optimalPolicy direction exponent prefixWord
    have data (R : Source) :
        let X := Matrix.trace R.val
        let paid := prefixWord X
        let K := exponent X
        let upper := direction X
        let Y := observe (matrix paid) R.val
        let Z := (Y-X)/(K : ℝ)
        let v := continuation upper X Z K
        let tau := SelfCalibratingRulings.read (paid,v) R
        let tr : History := [⟨([],[]),X⟩, ⟨([],paid),Y⟩, ⟨(paid,v),tau⟩]
        (PassivePolicyNormalization.execute SelfCalibratingRulings.read P 4 [] R =
          some (tr,(R.val,[])) ∧
        actualCost tr (R.val,[]) = paid.length +
          (2*(⌈X/Z⌉₊-K-(if upper then 1 else 0))+1) ∧
        matrix (paid++v) = matrix [!upper] * endpoint upper (finalLevel upper X Z K)) ∧
        Chronological [] tr := by
      let X := Matrix.trace R.val
      let paid := prefixWord X
      let K := exponent X
      let upper := direction X
      let Y := observe (matrix paid) R.val
      let Z := (Y-X)/(K : ℝ)
      let v := continuation upper X Z K
      let tau := SelfCalibratingRulings.read (paid,v) R
      let tr : History := [⟨([],[]),X⟩, ⟨([],paid),Y⟩, ⟨(paid,v),tau⟩]
      have hX : 0 < X := by
        dsimp [X]
        simpa [Matrix.trace,Matrix.diag,Fin.sum_univ_two] using
          add_pos (R.property.1 0 0) (R.property.1 1 1)
      have hk : 0 < K := (hlegal X hX).1
      have hpaid : matrix paid = endpoint upper K := (hlegal X hX).2
      have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
      have hzform : Z = if upper then R.val 1 0 else R.val 0 1 := by
        dsimp only [Z,Y]
        rw [hpaid]
        dsimp only [X]
        cases upper <;>
          simp [observe,endpoint,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]
        all_goals field_simp [hKr] <;> ring
      have hZ : 0 < Z := by
        rw [hzform]
        cases upper <;> exact R.property.1 _ _
      have hY : Y = X+(K : ℝ)*Z := by
        dsimp only [Z]
        field_simp [hKr] <;> ring
      obtain ⟨s,hs,hR⟩ := (charAll upper X Z hX hZ K hk R).mp
        ⟨rfl,by rw [← hpaid]; exact hY⟩
      have ha := attaining upper X Z hX hZ K hk
      have hthird : tau = third upper X Z (matrix v * endpoint upper K) s := by
        dsimp only [tau,SelfCalibratingRulings.read]
        rw [compose,hpaid,hR]
        rfl
      have hrecover : recover upper X Z
          ((finalLevel upper X Z K : ℝ)+(if upper then 1 else 0)) tau = R.val := by
        rw [hthird]
        exact ((ha.2.2.2.2.2 s hs).2).trans hR.symm
      have empty : matrix [] = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;>
          norm_num [matrix,Arith.FibonacciAtomic.SelfCalibratingRawWords.word]
      have hfirst : SelfCalibratingRulings.read ([],[]) R = X := by
        simp [SelfCalibratingRulings.read,observe,empty,X]
      have hsecond : SelfCalibratingRulings.read ([],paid) R = Y := by
        simp [SelfCalibratingRulings.read,Y]
      have run : PassivePolicyNormalization.execute SelfCalibratingRulings.read P 4 [] R =
          some (tr,(R.val,[])) := by
        simp only [PassivePolicyNormalization.execute,P,optimalPolicy,hfirst,List.nil_append,
          hsecond,List.cons_append,Option.map_some]
        change some (tr,(recover upper X Z
          ((finalLevel upper X Z K : ℝ)+(if upper then 1 else 0)) tau,[])) = _
        rw [hrecover]
      refine ⟨⟨run,?_,?_⟩,?_⟩
      · change actualCost tr (R.val,[]) = _
        simp only [tr,actualCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
          List.length_nil,Nat.zero_add,Nat.add_zero]
        rw [ha.1]
      · change matrix (paid++v) = matrix [!upper] *
          endpoint upper (finalLevel upper X Z K)
        exact (compose paid v).trans
          ((congrArg (fun A => matrix v * A) hpaid).trans ha.2.1)
      · simp [tr,Chronological]
    constructor
    · refine ⟨rfl,?_⟩
      intro R
      let X := Matrix.trace R.val
      let paid := prefixWord X
      let K := exponent X
      let upper := direction X
      let Y := observe (matrix paid) R.val
      let Z := (Y-X)/(K : ℝ)
      let v := continuation upper X Z K
      let tau := SelfCalibratingRulings.read (paid,v) R
      let tr : History := [⟨([],[]),X⟩, ⟨([],paid),Y⟩, ⟨(paid,v),tau⟩]
      exact ⟨4,tr,(R.val,[]),(data R).1.1,(data R).2,by simp [tr],rfl⟩
    · intro R
      exact (data R).1
  refine ⟨?_, ?_, characterization, positive, (raw w).1, (raw w).2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hp
    obtain ⟨paid,j,hsel,hj,hend⟩ := (second_query_shear P hp x hx).1
    rcases hend with hu | hv
    · exact ⟨paid,j,true,hsel,hj,by simpa [endpoint] using hu⟩
    · exact ⟨paid,j,false,hsel,hj,by simpa [endpoint] using hv⟩
  · have hp : OriginalValid (optimalPolicy (fun _ => true) (fun _ => 1)
        (fun _ => Arith.FibonacciAtomic.SelfCalibratingRawWords.alt false 2)) := by
      apply (globalPolicy _ _ _ ?_).1
      intro X hX
      constructor
      · omega
      · ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [matrix,endpoint,Arith.FibonacciAtomic.SelfCalibratingRawWords.alt,
            Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
            Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
            Arith.FibonacciAtomic.GraftAffineClosure.matrixM,Matrix.mul_apply,
            Fin.sum_univ_two]
    exact (second_query_shear _ hp x hx).2

  · let d := ⌈x / z⌉₊ - k - (if upper then 1 else 0)
    let v := Arith.FibonacciAtomic.SelfCalibratingRawWords.alt (!upper) (2*d+1)
    have alen : ∀ a n, (Arith.FibonacciAtomic.SelfCalibratingRawWords.alt a n).length = n := by
      intro a n
      induction n generalizing a with
      | zero => rfl
      | succ n ih => simp [Arith.FibonacciAtomic.SelfCalibratingRawWords.alt, ih]
    refine ⟨v, alen _ _, ?_⟩
    have odds := (Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound
      []).2.2.2.2.2.1 d
    have hm : x/z ≤ (⌈x/z⌉₊ : ℝ) := Nat.le_ceil _
    have dk : (⌈x/z⌉₊ : ℝ) ≤ (k:ℝ) + (d:ℝ) + (if upper then 1 else 0) := by
      have hi : ⌈x/z⌉₊ ≤ k+d+(if upper then 1 else 0) := by
        dsimp only [d]
        cases upper <;> simp only [Bool.false_eq_true, if_false, if_true, Nat.sub_zero] <;> omega
      exact_mod_cast hi
    have hn : 0 ≤ (k:ℝ) + (d:ℝ) := by positivity
    cases upper
    · have hv : matrix v = !![(d:ℝ), 1; 1, 0] := by
        change (Arith.FibonacciAtomic.SelfCalibratingRawWords.word
          (Arith.FibonacciAtomic.SelfCalibratingRawWords.alt true (2*d+1))).map
            (fun z : ℤ => (z:ℝ)) = _
        rw [odds.2]
        ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.map_apply]
      have hf : third false x z (matrix v * endpoint false k) =
          fun s => ((k:ℝ)+(d:ℝ))*x+z + (-((k:ℝ)+(d:ℝ)))*s + (1/z)*s*(x-s) := by
        funext s; rw [hv]
        simp [third, observe, fiber, endpoint, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two] <;> ring
      rw [hf]
      apply (scalar _ _ 1 (by norm_num) (by norm_num)).mpr
      refine ⟨by norm_num, ?_⟩
      simp only [abs_neg, abs_of_nonneg hn, one_mul]
      simpa using hm.trans dk
    · have hv : matrix v = !![0, 1; 1, (d:ℝ)+1] := by
        change (Arith.FibonacciAtomic.SelfCalibratingRawWords.word
          (Arith.FibonacciAtomic.SelfCalibratingRawWords.alt false (2*d+1))).map
            (fun z : ℤ => (z:ℝ)) = _
        rw [odds.1]
        ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.map_apply]
      have hf : third true x z (matrix v * endpoint true k) =
          fun s => z + ((k:ℝ)+(d:ℝ)+1)*s + (1/z)*s*(x-s) := by
        funext s; rw [hv]
        simp [third, observe, fiber, endpoint, Matrix.trace, Matrix.diag,
          Matrix.mul_apply, Fin.sum_univ_two] <;> ring
      rw [hf]
      apply (scalar _ _ 1 (by norm_num) (by norm_num)).mpr
      refine ⟨by norm_num, ?_⟩
      rw [one_mul, abs_of_nonneg (by linarith : 0 ≤ (k:ℝ)+(d:ℝ)+1)]
      exact hm.trans dk

  · intro P hp paidWord hpaid hsel
    let h₂ : History := [⟨([], []), x⟩, ⟨([], paidWord), x+k*z⟩]
    have truncate : ∀ n : ℕ, ∀ (h : History) (R : Source) (tr : History) (out : Label)
        (m : ℕ), PassivePolicyNormalization.execute SelfCalibratingRulings.read P n h R = some (tr, out) →
        tr.length < m → PassivePolicyNormalization.execute SelfCalibratingRulings.read P m h R = some (tr, out) := by
      intro n
      induction n with
      | zero => intro h R tr out m hr; simp [PassivePolicyNormalization.execute] at hr
      | succ n ih =>
        intro h R tr out m hr hm
        cases m with
        | zero => omega
        | succ m =>
          cases hP : P h with
          | inr out' =>
            simp only [PassivePolicyNormalization.execute, hP, Option.some.injEq,
              Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            simp [PassivePolicyNormalization.execute, hP]
          | inl q =>
            simp only [PassivePolicyNormalization.execute, hP, Option.map_eq_some_iff] at hr
            obtain ⟨⟨s, out'⟩, hs, he⟩ := hr
            cases he
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hm
            simp only [PassivePolicyNormalization.execute, hP]
            rw [ih _ _ _ _ _ hs hm]
            rfl
    have run₄ (R : Source) : ∃ tr out,
        PassivePolicyNormalization.execute SelfCalibratingRulings.read P 4 [] R = some (tr, out) ∧
        Chronological [] tr ∧ out.1 = R.val := by
      obtain ⟨n,tr,out,hr,hc,hn,he⟩ := hp.2 R
      exact ⟨tr,out,truncate _ _ _ _ _ _ hr (by omega),hc,he⟩
    have correct (R : Source) (tr : History) (out : Label)
        (hr : PassivePolicyNormalization.execute SelfCalibratingRulings.read P 4 [] R = some (tr,out)) : out.1 = R.val := by
      obtain ⟨s,out',hs,_,he⟩ := run₄ R
      rw [hr] at hs
      exact (Prod.mk.inj (Option.some.inj hs)).2 ▸ he
    let src (s : ℝ) (hs : s ∈ Set.Ioo 0 x) : Source := ⟨fiber upper x z s, positive s hs⟩
    have sourceReads (s : ℝ) (hs : s ∈ Set.Ioo 0 x) :
        Matrix.trace (src s hs).val = x ∧
          observe (endpoint upper k) (src s hs).val = x+k*z :=
      (characterization _).mpr ⟨s,hs,rfl⟩
    have empty : matrix [] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [matrix, Arith.FibonacciAtomic.SelfCalibratingRawWords.word]
    have first (R : Source) : SelfCalibratingRulings.read ([],[]) R = Matrix.trace R.val := by
      simp [SelfCalibratingRulings.read,observe,empty]
    have second (R : Source) : SelfCalibratingRulings.read ([],paidWord) R = observe (endpoint upper k) R.val := by
      simp [SelfCalibratingRulings.read,hpaid]
    have compose (p q : List Bool) : matrix (p++q) = matrix q * matrix p := by
      have hw := (Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound p).2.2.2.1 q
      ext i j
      simp [matrix, hw, Matrix.mul_apply, Fin.sum_univ_two]
    let R₀ := src (x/3) (by constructor <;> linarith : x/3 ∈ Set.Ioo 0 x)
    let R₁ := src (2*x/3) (by constructor <;> linarith : 2*x/3 ∈ Set.Ioo 0 x)
    have hx₀ := (sourceReads (x/3) (by constructor <;> linarith)).1
    have hy₀ := (sourceReads (x/3) (by constructor <;> linarith)).2
    have hx₁ := (sourceReads (2*x/3) (by constructor <;> linarith)).1
    have hy₁ := (sourceReads (2*x/3) (by constructor <;> linarith)).2
    change Matrix.trace R₀.val = x at hx₀
    change observe (endpoint upper k) R₀.val = x+k*z at hy₀
    change Matrix.trace R₁.val = x at hx₁
    change observe (endpoint upper k) R₁.val = x+k*z at hy₁
    have different : R₀ ≠ R₁ := by
      intro he
      have he' := congrArg (fun R : Source => R.val 1 1) he
      change fiber upper x z (x/3) 1 1 = fiber upper x z (2*x/3) 1 1 at he'
      cases upper <;> simp [fiber] at he' <;> linarith
    cases hP₂ : P h₂ with
    | inr out =>
      dsimp only [h₂] at hP₂
      have runs (R : Source) (hRx : Matrix.trace R.val = x)
          (hRy : observe (endpoint upper k) R.val = x+k*z) :
          PassivePolicyNormalization.execute SelfCalibratingRulings.read P 4 [] R = some (h₂,out) := by
        simp [PassivePolicyNormalization.execute,hp.1,first,second,hRx,hRy,hsel,hP₂,h₂]
      exact False.elim (different (Subtype.ext
        ((correct R₀ h₂ out (runs R₀ hx₀ hy₀)).symm.trans
          (correct R₁ h₂ out (runs R₁ hx₁ hy₁)))))
    | inl q =>
      dsimp only [h₂] at hP₂
      have before : q.1 = paidWord := by
        obtain ⟨tr,out,hr,hc,_⟩ := run₄ R₀
        simp only [PassivePolicyNormalization.execute,hp.1,first,second,hx₀,hy₀,
          List.nil_append,hsel,hP₂] at hr
        obtain ⟨⟨t,l⟩,ht,he⟩ := Option.map_eq_some_iff.mp hr
        cases he
        obtain ⟨⟨t',l'⟩,ht',he'⟩ := Option.map_eq_some_iff.mp ht
        cases he'
        simp only [List.cons_append,List.nil_append,hP₂] at ht'
        obtain ⟨⟨t'',l''⟩,_,he''⟩ := Option.map_eq_some_iff.mp ht'
        cases he''
        simpa only [Chronological,List.nil_append] using hc.2.2.1
      have qeq : q = (paidWord,q.2) := Prod.ext before rfl
      rw [qeq] at hP₂
      have injective : Set.InjOn (third upper x z (matrix q.2*endpoint upper k)) (Set.Ioo 0 x) := by
        intro u hu v hv heq
        let U := src u hu
        let V := src v hv
        have hU := sourceReads u hu
        have hV := sourceReads v hv
        change Matrix.trace U.val = x ∧ observe (endpoint upper k) U.val = x+k*z at hU
        change Matrix.trace V.val = x ∧ observe (endpoint upper k) V.val = x+k*z at hV
        have thirdRead (s : ℝ) (hs : s ∈ Set.Ioo 0 x) :
            SelfCalibratingRulings.read (paidWord,q.2) (src s hs) = third upper x z (matrix q.2*endpoint upper k) s := by
          simp only [SelfCalibratingRulings.read,compose,hpaid,third,src]
        have hread : SelfCalibratingRulings.read (paidWord,q.2) U = SelfCalibratingRulings.read (paidWord,q.2) V := by
          rw [thirdRead u hu,thirdRead v hv]; exact heq
        let h₃ := h₂ ++ [⟨(paidWord,q.2),SelfCalibratingRulings.read (paidWord,q.2) U⟩]
        obtain ⟨tr,out,hr,_,_⟩ := run₄ U
        cases hP₃ : P h₃ with
        | inl q' =>
          dsimp only [h₃,h₂] at hP₃
          simp only [List.cons_append,List.nil_append] at hP₃
          simp [PassivePolicyNormalization.execute,hp.1,first,second,hU.1,hU.2,hsel,hP₂,hP₃] at hr
        | inr out =>
          dsimp only [h₃,h₂] at hP₃
          simp only [List.cons_append,List.nil_append] at hP₃
          have runs (R : Source) (hRx : Matrix.trace R.val = x)
              (hRy : observe (endpoint upper k) R.val = x+k*z)
              (ht : SelfCalibratingRulings.read (paidWord,q.2) R = SelfCalibratingRulings.read (paidWord,q.2) U) :
              PassivePolicyNormalization.execute SelfCalibratingRulings.read P 4 [] R = some (h₃,out) := by
            simp [PassivePolicyNormalization.execute,hp.1,first,second,hRx,hRy,
              ht,hsel,hP₂,hP₃,h₃,h₂]
          have he := (correct U h₃ out (runs U hU.1 hU.2 rfl)).symm.trans
            (correct V h₃ out (runs V hV.1 hV.2 hread.symm))
          have he' := congrArg (fun R : Matrix (Fin 2) (Fin 2) ℝ => R 1 1) he
          change fiber upper x z u 1 1 = fiber upper x z v 1 1 at he'
          cases upper <;> simpa [fiber] using he'
      have lengthBound := ((raw q.2).2 injective).2.2
      refine ⟨q.2,congrArg Sum.inl qeq,injective,?_⟩
      intro R hRx hRy n tr out hr
      let h₃ : History := h₂ ++ [⟨(paidWord,q.2),SelfCalibratingRulings.read (paidWord,q.2) R⟩]
      have stopped : ∃ label, P h₃ = .inr label := by
        obtain ⟨t,l,ht,_,_⟩ := run₄ R
        cases hP₃ : P h₃ with
        | inr label => exact ⟨label,rfl⟩
        | inl q' =>
          dsimp only [h₃,h₂] at hP₃
          simp only [List.cons_append,List.nil_append] at hP₃
          simp [PassivePolicyNormalization.execute,hp.1,first,second,hRx,hRy,hsel,hP₂,hP₃] at ht
      obtain ⟨label,hP₃⟩ := stopped
      dsimp only [h₃,h₂] at hP₃
      simp only [List.cons_append,List.nil_append] at hP₃
      cases n with
      | zero => simp [PassivePolicyNormalization.execute] at hr
      | succ n =>
        cases n with
        | zero => simp [PassivePolicyNormalization.execute,hp.1] at hr
        | succ n =>
          cases n with
          | zero => simp [PassivePolicyNormalization.execute,hp.1,first,hRx,hsel] at hr
          | succ n =>
            cases n with
            | zero =>
              simp [PassivePolicyNormalization.execute,hp.1,first,second,hRx,hRy,hsel,hP₂] at hr
            | succ n =>
              simp [PassivePolicyNormalization.execute,hp.1,first,second,hRx,hRy,
                hsel,hP₂,hP₃] at hr
              obtain ⟨rfl,rfl⟩ := hr
              simp [actualCost]
              omega

  · exact inverseAll upper x z hx hz
  · exact (attaining upper x z hx hz k hk).2
  · exact globalPolicy
  · exact shortestPrefix
  · exact shortestWitness
  · exact optimized

#print axioms full_fiber_and_signed_capacity

end
end D5.S3.ConceptDynamics.Experiment.SelfCalibratingFibers
