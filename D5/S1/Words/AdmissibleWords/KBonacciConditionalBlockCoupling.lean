/- GID: D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Exterior-conditioned legal-word completions and their zero-reset coupling. -/

import D5.S1.Words.ClosedRunStarts
import D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval
import D5.S0.Tower.DBonacci.TerminalSampling
import Mathlib.Tactic

/-! Actual finite conditional fibers retain every fixed exterior and prefix bit. -/

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling

open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.TerminalSampling
open D5.S1.Words.ClosedRunStarts
open scoped BigOperators ENNReal NNReal Classical

private theorem legal_iff (k n : ℕ) (hk : 0 < k) (w : Fin n → Bool) :
    DBonacciAdmissible k n w ↔ ∀ s, ¬ TrueBlock w s k :=
  D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval.scanner_iff_literal k n hk w

theorem legal_delete {k n : ℕ} (hk : 0 < k) (w : Fin n → Bool)
    (hw : DBonacciAdmissible k n w) (i : Fin n) :
    DBonacciAdmissible k n (Function.update w i false) := by
  classical
  apply (legal_iff k n hk _).mpr
  intro s h
  apply (legal_iff k n hk w).mp hw s
  refine ⟨h.1, ?_⟩
  intro j hj hj'
  have hb := h.2 j hj hj'
  by_cases he : j = i
  · simp [he] at hb
  · simpa [Function.update_of_ne he] using hb

/-- Full legal words agreeing with every fixed coordinate. Taking the fixed set
to be the full block exterior together with a sampled prefix retains both ends. -/
def completions (k n : ℕ) (fixed : Finset (Fin n)) (exterior : Fin n → Bool) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun w => DBonacciAdmissible k n w ∧
    ∀ i ∈ fixed, w i = exterior i

/-- The exact uniform conditional law on the nonempty full-exterior fiber. -/
def completionLaw {k n : ℕ} (fixed : Finset (Fin n)) (exterior : Fin n → Bool)
    (h : (completions k n fixed exterior).Nonempty) : PMF (Fin n → Bool) := by
  letI : Nonempty {w // w ∈ completions k n fixed exterior} :=
    ⟨⟨h.choose, h.choose_spec⟩⟩
  exact (uniformPmf {w // w ∈ completions k n fixed exterior}).map Subtype.val

theorem completionLaw_apply {k n : ℕ} (fixed : Finset (Fin n))
    (exterior w : Fin n → Bool) (h : (completions k n fixed exterior).Nonempty) :
    completionLaw fixed exterior h w =
      if w ∈ completions k n fixed exterior then
        ((completions k n fixed exterior).card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  simp only [completionLaw, PMF.map_apply, uniformPmf, PMF.ofFintype_apply]
  by_cases hw : w ∈ completions k n fixed exterior
  · rw [tsum_eq_single (⟨w, hw⟩ : {w // w ∈ completions k n fixed exterior})]
    · simp [hw, Fintype.card_coe]
    · intro b hb
      have : w ≠ b.val := fun he => hb (Subtype.ext he.symm)
      simp [this]
  · have hz : ∀ b : {w // w ∈ completions k n fixed exterior}, w ≠ b.val := by
      intro b he
      exact hw (he ▸ b.property)
    simp [hz, hw]

theorem completion_nonempty {k n : ℕ} (fixed : Finset (Fin n))
    (exterior : Fin n → Bool) (h : DBonacciAdmissible k n exterior) :
    (completions k n fixed exterior).Nonempty := by
  classical
  exact ⟨exterior, by simp [completions, h]⟩

theorem zero_completion_injection {k n : ℕ} (hk : 0 < k)
    (fixed : Finset (Fin n)) (exterior : Fin n → Bool) (i : Fin n) (hi : i ∉ fixed) :
    ((completions k n fixed exterior).filter fun w => w i = true).card ≤
      ((completions k n fixed exterior).filter fun w => w i = false).card := by
  classical
  let f : {w // w ∈ (completions k n fixed exterior).filter fun w => w i = true} →
      {w // w ∈ (completions k n fixed exterior).filter fun w => w i = false} :=
    fun w => ⟨Function.update w.val i false, by
      obtain ⟨hw, hbit⟩ := Finset.mem_filter.mp w.property
      obtain ⟨hlegal, hfixed⟩ := (Finset.mem_filter.mp hw).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, completions]
      refine ⟨⟨legal_delete hk w.val hlegal i, ?_⟩, by simp⟩
      intro j hj
      have hji : j ≠ i := by intro he; exact hi (he ▸ hj)
      simpa [Function.update_of_ne hji] using hfixed j hj⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      exact (Finset.mem_filter.mp a.property).2.trans
        (Finset.mem_filter.mp b.property).2.symm
    · have he' := congrArg (fun w => w.val j) he
      simpa [f, Function.update_of_ne hji] using he'
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

private theorem completion_bit_probability {k n : ℕ} (fixed : Finset (Fin n))
    (exterior : Fin n → Bool) (h : (completions k n fixed exterior).Nonempty)
    (i : Fin n) (b : Bool) :
    ((completionLaw fixed exterior h).map (fun w => w i)) b =
      (((completions k n fixed exterior).filter fun w => w i = b).card : ℝ≥0∞) /
        (completions k n fixed exterior).card := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp_rw [completionLaw_apply]
  have he : ∀ w : Fin n → Bool,
      (if b = w i then
        if w ∈ completions k n fixed exterior then
          ((completions k n fixed exterior).card : ℝ≥0∞)⁻¹ else 0
        else 0) =
      if w ∈ (completions k n fixed exterior).filter (fun w => w i = b) then
        ((completions k n fixed exterior).card : ℝ≥0∞)⁻¹ else 0 := by
    intro w
    by_cases hw : w ∈ completions k n fixed exterior <;>
      by_cases hb : w i = b <;> simp [hw, hb, eq_comm]
  simp_rw [he]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun w =>
      w ∈ (completions k n fixed exterior).filter (fun w => w i = b)) =
      (completions k n fixed exterior).filter (fun w => w i = b) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hf]
  simp [div_eq_mul_inv]

private theorem conditional_zero_half {k n : ℕ} (hk : 0 < k)
    (fixed : Finset (Fin n)) (exterior : Fin n → Bool)
    (h : (completions k n fixed exterior).Nonempty) (i : Fin n) (hi : i ∉ fixed) :
    (1 / 2 : ℝ≥0∞) ≤ ((completionLaw fixed exterior h).map (fun w => w i)) false := by
  classical
  rw [completion_bit_probability]
  have hinj := zero_completion_injection hk fixed exterior i hi
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := completions k n fixed exterior) (fun w => w i = false)
  have htotal : (completions k n fixed exterior).card ≤
      2 * ((completions k n fixed exterior).filter fun w => w i = false).card := by
    have hnot : ((completions k n fixed exterior).filter fun w => ¬ w i = false) =
        ((completions k n fixed exterior).filter fun w => w i = true) := by
      ext w
      simp
    rw [hnot] at hsplit
    omega
  have hpos : 0 < (completions k n fixed exterior).card := h.card_pos
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by exact_mod_cast (Nat.ne_of_gt hpos)))
    (Or.inl (ENNReal.natCast_ne_top _))).mpr
  have hc : ((completions k n fixed exterior).card : ℝ≥0∞) ≤
      2 * (((completions k n fixed exterior).filter fun w => w i = false).card : ℝ≥0∞) := by
    exact_mod_cast htotal
  calc
    (1 / 2 : ℝ≥0∞) * (completions k n fixed exterior).card ≤
        (1 / 2 : ℝ≥0∞) * (2 *
          (((completions k n fixed exterior).filter fun w => w i = false).card : ℝ≥0∞)) :=
      by gcongr
    _ = _ := by
      rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

private def orderedBitMass (a b : ℝ≥0) (bits : Bool × Bool) : ℝ≥0 :=
  match bits with
  | (false, false) => a
  | (false, true) => 0
  | (true, false) => b - a
  | (true, true) => 1 - b

private def orderedBitCoupling (a b : ℝ≥0) (hab : a ≤ b) (hb : b ≤ 1) :
    PMF (Bool × Bool) :=
  PMF.ofFintype (fun bits => (orderedBitMass a b bits : ℝ≥0∞)) (by
    have hs : ∑ bits : Bool × Bool, orderedBitMass a b bits = 1 := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, orderedBitMass, add_zero, zero_add]
      rw [add_assoc, tsub_add_cancel_of_le hab, tsub_add_cancel_of_le hb]
    exact_mod_cast hs)

private theorem orderedBitCoupling_marginals (a b : ℝ≥0) (hab : a ≤ b) (hb : b ≤ 1) :
    ((orderedBitCoupling a b hab hb).map Prod.fst) false = a ∧
      ((orderedBitCoupling a b hab hb).map Prod.snd) false = b ∧
      orderedBitCoupling a b hab hb (false, false) = a := by
  classical
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    orderedBitCoupling, PMF.ofFintype_apply, orderedBitMass, Prod.fst, Prod.snd,
    Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, ite_false, ite_true,
    ENNReal.coe_zero, add_zero, zero_add, true_and, eq_self_iff_true]
  norm_cast
  exact ⟨tsub_add_cancel_of_le hab, trivial⟩

private theorem bool_pmf_ext (p q : PMF Bool) (h : p false = q false) : p = q := by
  apply PMF.ext
  intro b
  cases b with
  | false => exact h
  | true =>
      have hp : p false + p true = 1 := by
        simpa [tsum_fintype, Fintype.sum_bool, add_comm] using p.tsum_coe
      have hq : q false + q true = 1 := by
        simpa [tsum_fintype, Fintype.sum_bool, add_comm] using q.tsum_coe
      apply (ENNReal.add_right_inj (p.apply_ne_top false)).mp
      rw [h] at hp ⊢
      exact hp.trans hq.symm

private theorem zero_toNNReal_le_one (p : PMF Bool) : (p false).toNNReal ≤ 1 := by
  exact_mod_cast (ENNReal.coe_toNNReal (p.apply_ne_top false)) ▸ p.coe_le_one false

/-- The finite shared-threshold coupling of the next two conditional bits. -/
def bitCoupling (p q : PMF Bool) : PMF (Bool × Bool) :=
  if h : (p false).toNNReal ≤ (q false).toNNReal then
    orderedBitCoupling _ _ h (zero_toNNReal_le_one q)
  else
    (orderedBitCoupling _ _ (le_of_not_ge h) (zero_toNNReal_le_one p)).map Prod.swap

private theorem bitCoupling_laws (p q : PMF Bool) :
    (bitCoupling p q).map Prod.fst = p ∧
      (bitCoupling p q).map Prod.snd = q ∧
      bitCoupling p q (false, false) = min (p false) (q false) := by
  classical
  unfold bitCoupling
  split_ifs with h
  · have hs := orderedBitCoupling_marginals _ _ h (zero_toNNReal_le_one q)
    have hp := ENNReal.coe_toNNReal (p.apply_ne_top false)
    have hq := ENNReal.coe_toNNReal (q.apply_ne_top false)
    refine ⟨bool_pmf_ext _ _ (hs.1.trans hp),
      bool_pmf_ext _ _ (hs.2.1.trans hq), ?_⟩
    rw [hs.2.2, hp, min_eq_left]
    rw [← hp, ← hq]
    exact_mod_cast h
  · have hs := orderedBitCoupling_marginals _ _ (le_of_not_ge h)
      (zero_toNNReal_le_one p)
    have hp := ENNReal.coe_toNNReal (p.apply_ne_top false)
    have hq := ENNReal.coe_toNNReal (q.apply_ne_top false)
    refine ⟨bool_pmf_ext _ _ ?_, bool_pmf_ext _ _ ?_, ?_⟩
    · rw [PMF.map_comp]
      exact hs.2.1.trans hp
    · rw [PMF.map_comp]
      exact hs.1.trans hq
    · have hm : ∀ r : PMF (Bool × Bool),
          r.map Prod.swap (false, false) = r (false, false) := by
        intro r
        simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
      rw [hm, hs.2.2, hq, min_eq_right]
      rw [← hp, ← hq]
      exact_mod_cast le_of_not_ge h

/-- For two arbitrary nonempty legal exterior-and-prefix fibers, the actual next
conditional bits admit exact marginal pushforwards and a common zero of mass at
least one half. Neither conditional probability is an assumed parameter. -/
theorem conditional_step_coupling {k n : ℕ} (hk : 0 < k)
    (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty) (i : Fin n) (hi : i ∉ fixed) :
    let p := (completionLaw fixed x hx).map (fun w => w i)
    let q := (completionLaw fixed y hy).map (fun w => w i)
    (bitCoupling p q).map Prod.fst = p ∧
      (bitCoupling p q).map Prod.snd = q ∧
      (1 / 2 : ℝ≥0∞) ≤ bitCoupling p q (false, false) := by
  dsimp only
  have h := bitCoupling_laws
    ((completionLaw fixed x hx).map (fun w => w i))
    ((completionLaw fixed y hy).map (fun w => w i))
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2]
  exact le_min (conditional_zero_half hk fixed x hx i hi)
    (conditional_zero_half hk fixed y hy i hi)

/-- A zero screens every earlier bit from the later legal-completion constraint.
The prefix on each side is an actual legal word, and the later bits are identical. -/
theorem zero_screening {k n : ℕ} (hk : 0 < k) (x y : Fin n → Bool)
    (hx : DBonacciAdmissible k n x) (hy : DBonacciAdmissible k n y)
    (z : Fin n) (hxz : x z = false) (hyz : y z = false)
    (tail : Fin n → Bool) :
    DBonacciAdmissible k n (fun i => if i.val ≤ z.val then x i else tail i) ↔
      DBonacciAdmissible k n (fun i => if i.val ≤ z.val then y i else tail i) := by
  have transfer (a b : Fin n → Bool) (hb : DBonacciAdmissible k n b)
      (hbz : b z = false) (hlegal : DBonacciAdmissible k n
        (fun i => if i.val ≤ z.val then a i else tail i)) :
      DBonacciAdmissible k n (fun i => if i.val ≤ z.val then b i else tail i) := by
    apply (legal_iff k n hk _).mpr
    intro s h
    by_cases hleft : s + k ≤ z.val + 1
    · apply (legal_iff k n hk b).mp hb s
      refine ⟨h.1, ?_⟩
      intro j hj hj'
      have hle : j.val ≤ z.val := by omega
      simpa [hle] using h.2 j hj hj'
    · by_cases hright : z.val < s
      · apply (legal_iff k n hk _).mp hlegal s
        refine ⟨h.1, ?_⟩
        intro j hj hj'
        have hle : ¬ j.val ≤ z.val := by omega
        simpa [hle] using h.2 j hj hj'
      · have hz := h.2 z (by omega) (by omega)
        simp [hbz] at hz
  exact ⟨transfer x y hy hyz, transfer y x hx hxz⟩

/-- Replace only the prefix through the reset site, retaining the whole suffix. -/
def resetMap {n : ℕ} (z : Fin n) (history w : Fin n → Bool) : Fin n → Bool :=
  fun i => if i.val ≤ z.val then history i else w i

/-- Sample one full conditional completion and retain its suffix in both outputs. -/
def resetCoupling {k n : ℕ} (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (h : (completions k n fixed x).Nonempty) (z : Fin n) :
    PMF ((Fin n → Bool) × (Fin n → Bool)) :=
  (completionLaw fixed x h).map (fun w => (w, resetMap z y w))

private def resetFiberEquiv {k n : ℕ} (hk : 0 < k)
    (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (hx : DBonacciAdmissible k n x) (hy : DBonacciAdmissible k n y)
    (z : Fin n) (hxz : x z = false) (hyz : y z = false)
    (leftFixed : ∀ i : Fin n, i.val ≤ z.val → i ∈ fixed)
    (farSame : ∀ i ∈ fixed, z.val < i.val → x i = y i) :
    {w // w ∈ completions k n fixed x} ≃ {w // w ∈ completions k n fixed y} := by
  classical
  have transfer (a b : Fin n → Bool) (ha : DBonacciAdmissible k n a)
      (hb : DBonacciAdmissible k n b) (haz : a z = false) (hbz : b z = false)
      (hsame : ∀ i ∈ fixed, z.val < i.val → a i = b i)
      (w : Fin n → Bool) (hw : w ∈ completions k n fixed a) :
      resetMap z b w ∈ completions k n fixed b := by
    obtain ⟨hlegal, hfixed⟩ := (Finset.mem_filter.mp hw).2
    have he : resetMap z a w = w := by
      funext i
      by_cases hi : i.val ≤ z.val
      · simp [resetMap, hi, hfixed i (leftFixed i hi)]
      · simp [resetMap, hi]
    have hreset := (zero_screening hk a b ha hb z haz hbz w).mp
      (by change DBonacciAdmissible k n (resetMap z a w); rwa [he])
    simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hreset, ?_⟩
    intro i hi
    by_cases hleft : i.val ≤ z.val
    · simp [resetMap, hleft]
    · simp [resetMap, hleft, hfixed i hi, hsame i hi (by omega)]
  refine
    { toFun := fun w => ⟨resetMap z y w.val,
        transfer x y hx hy hxz hyz farSame w.val w.property⟩
      invFun := fun w => ⟨resetMap z x w.val,
        transfer y x hy hx hyz hxz (fun i hi hz => (farSame i hi hz).symm) w.val w.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    apply Subtype.ext
    funext i
    have hf := (Finset.mem_filter.mp w.property).2.2
    by_cases hi : i.val ≤ z.val
    · simp [resetMap, hi, hf i (leftFixed i hi)]
    · simp [resetMap, hi]
  · intro w
    apply Subtype.ext
    funext i
    have hf := (Finset.mem_filter.mp w.property).2.2
    by_cases hi : i.val ≤ z.val
    · simp [resetMap, hi, hf i (leftFixed i hi)]
    · simp [resetMap, hi]

/-- Once both prefixes end in zero, replacing the fixed prefix transports the
actual conditional uniform laws exactly; every later coordinate is unchanged. -/
theorem reset_law_transport {k n : ℕ} (hk : 0 < k)
    (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (hx : DBonacciAdmissible k n x) (hy : DBonacciAdmissible k n y)
    (z : Fin n) (hxz : x z = false) (hyz : y z = false)
    (leftFixed : ∀ i : Fin n, i.val ≤ z.val → i ∈ fixed)
    (farSame : ∀ i ∈ fixed, z.val < i.val → x i = y i) :
    (completionLaw fixed x (completion_nonempty fixed x hx)).map (resetMap z y) =
        completionLaw fixed y (completion_nonempty fixed y hy) ∧
      (∀ w : Fin n → Bool, ∀ i : Fin n, z.val < i.val → resetMap z y w i = w i) ∧
      ((resetCoupling fixed x y (completion_nonempty fixed x hx) z).map Prod.fst =
        completionLaw fixed x (completion_nonempty fixed x hx) ∧
       (resetCoupling fixed x y (completion_nonempty fixed x hx) z).map Prod.snd =
        completionLaw fixed y (completion_nonempty fixed y hy)) := by
  classical
  let e := resetFiberEquiv hk fixed x y hx hy z hxz hyz leftFixed farSame
  letI : Nonempty {w // w ∈ completions k n fixed x} :=
    ⟨⟨x, by simp [completions, hx]⟩⟩
  letI : Nonempty {w // w ∈ completions k n fixed y} :=
    ⟨⟨y, by simp [completions, hy]⟩⟩
  have hu : (uniformPmf {w // w ∈ completions k n fixed x}).map e =
      uniformPmf {w // w ∈ completions k n fixed y} := by
    apply PMF.ext
    intro w
    simp only [PMF.map_apply, uniformPmf, PMF.ofFintype_apply, ← e.symm_apply_eq]
    simp [Fintype.card_congr e]
  have ht : (completionLaw fixed x (completion_nonempty fixed x hx)).map (resetMap z y) =
      completionLaw fixed y (completion_nonempty fixed y hy) := by
    change ((uniformPmf {w // w ∈ completions k n fixed x}).map Subtype.val).map
      (resetMap z y) = (uniformPmf {w // w ∈ completions k n fixed y}).map Subtype.val
    rw [← hu, PMF.map_comp, PMF.map_comp]
    rfl
  refine ⟨ht, ?_, ?_⟩
  · intro w i hi
    simp [resetMap, show ¬ i.val ≤ z.val by omega]
  · constructor
    · change ((completionLaw fixed x _).map (fun w => (w, resetMap z y w))).map
        Prod.fst = _
      rw [PMF.map_comp]
      exact PMF.map_id _
    · change ((completionLaw fixed x _).map (fun w => (w, resetMap z y w))).map
        Prod.snd = _
      rw [PMF.map_comp]
      exact ht

theorem refined_completions {k n : ℕ} (fixed : Finset (Fin n))
    (x : Fin n → Bool) (i : Fin n) (hi : i ∉ fixed) (b : Bool) :
    completions k n (insert i fixed) (Function.update x i b) =
      (completions k n fixed x).filter (fun w => w i = b) := by
  classical
  ext w
  simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, hf⟩
    refine ⟨⟨hw, ?_⟩, by simpa using hf i (by simp)⟩
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hi hj
    simpa [Function.update_of_ne hji] using hf j (Finset.mem_insert_of_mem hj)
  · rintro ⟨⟨hw, hf⟩, hb⟩
    refine ⟨hw, ?_⟩
    intro j hjfixed
    rcases Finset.mem_insert.mp hjfixed with hji | hj
    · subst j
      simpa using hb
    · have hji : j ≠ i := fun he => hi (he ▸ hj)
      simpa [Function.update_of_ne hji] using hf j hj

/-- The actual conditional law after revealing one more bit. The fallback is
used only at bits of zero marginal mass. -/
def nextCompletionLaw {k n : ℕ} (fixed : Finset (Fin n)) (x : Fin n → Bool)
    (hx : (completions k n fixed x).Nonempty) (i : Fin n) (b : Bool) :
    PMF (Fin n → Bool) :=
  if h : (completions k n (insert i fixed) (Function.update x i b)).Nonempty then
    completionLaw (insert i fixed) (Function.update x i b) h
  else completionLaw fixed x hx

private theorem completion_step_weight {k n : ℕ} (fixed : Finset (Fin n))
    (x : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (i : Fin n) (hi : i ∉ fixed) (b : Bool) (w : Fin n → Bool) :
    ((completionLaw fixed x hx).map (fun v => v i)) b *
        nextCompletionLaw fixed x hx i b w =
      if w i = b then completionLaw fixed x hx w else 0 := by
  classical
  rw [completion_bit_probability]
  unfold nextCompletionLaw
  by_cases h : (completions k n (insert i fixed) (Function.update x i b)).Nonempty
  · rw [dif_pos h, completionLaw_apply, refined_completions fixed x i hi]
    by_cases hw : w ∈ completions k n fixed x
    · by_cases hb : w i = b
      · simp only [Finset.mem_filter, hw, hb, and_self, ite_true]
        rw [completionLaw_apply, if_pos hw, div_eq_mul_inv, mul_right_comm,
          ENNReal.mul_inv_cancel]
        · simp
        · exact_mod_cast Nat.ne_of_gt (by
            rw [refined_completions fixed x i hi] at h
            exact h.card_pos)
        · exact ENNReal.natCast_ne_top _
      · simp [hw, hb]
    · simp [hw, completionLaw_apply]
  · rw [dif_neg h]
    have he : (completions k n fixed x).filter (fun v => v i = b) = ∅ := by
      rw [← refined_completions fixed x i hi]
      exact Finset.not_nonempty_iff_eq_empty.mp h
    have hwzero : w i = b → completionLaw fixed x hx w = 0 := by
      intro hb
      rw [completionLaw_apply, if_neg]
      intro hw
      have hm : w ∈ (completions k n fixed x).filter (fun v => v i = b) := by
        simp [hw, hb]
      rw [he] at hm
      exact Finset.notMem_empty w hm
    rw [he]
    by_cases hb : w i = b <;> simp [hb, hwzero, ENNReal.zero_div]

private theorem completion_disintegration {k n : ℕ} (fixed : Finset (Fin n))
    (x : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (i : Fin n) (hi : i ∉ fixed) :
    ((completionLaw fixed x hx).map (fun w => w i)).bind
        (nextCompletionLaw fixed x hx i) = completionLaw fixed x hx := by
  classical
  apply PMF.ext
  intro w
  rw [PMF.bind_apply, tsum_fintype]
  simp_rw [completion_step_weight fixed x hx i hi]
  cases hb : w i <;> simp [hb, Fintype.sum_bool]

private theorem pmf_le_map {α β : Type*} (p : PMF α) (f : α → β) (a : α) :
    p a ≤ p.map f (f a) := by
  classical
  rw [PMF.map_apply]
  simpa using (ENNReal.le_tsum (f := fun v => if f a = f v then p v else 0) a)

theorem bitCoupling_supported_fibers {k n : ℕ} (fixed : Finset (Fin n))
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty) (i : Fin n) (hi : i ∉ fixed)
    (bits : Bool × Bool)
    (hs : bits ∈ (bitCoupling ((completionLaw fixed x hx).map (fun w => w i))
      ((completionLaw fixed y hy).map (fun w => w i))).support) :
    (completions k n (insert i fixed) (Function.update x i bits.1)).Nonempty ∧
      (completions k n (insert i fixed) (Function.update y i bits.2)).Nonempty := by
  classical
  let p := (completionLaw fixed x hx).map (fun w => w i)
  let q := (completionLaw fixed y hy).map (fun w => w i)
  have hm := bitCoupling_laws p q
  have hfirst := pmf_le_map (bitCoupling p q) Prod.fst bits
  have hsecond := pmf_le_map (bitCoupling p q) Prod.snd bits
  rw [hm.1] at hfirst
  rw [hm.2.1] at hsecond
  have nonempty (v : Fin n → Bool) (hv : (completions k n fixed v).Nonempty)
      (b : Bool) (hb : ((completionLaw fixed v hv).map (fun w => w i)) b ≠ 0) :
      (completions k n (insert i fixed) (Function.update v i b)).Nonempty := by
    rw [refined_completions fixed v i hi]
    by_contra h
    apply hb
    rw [completion_bit_probability, Finset.not_nonempty_iff_eq_empty.mp h]
    simp
  exact ⟨nonempty x hx bits.1 (fun h => hs (le_antisymm (h ▸ hfirst) zero_le)),
    nonempty y hy bits.2 (fun h => hs (le_antisymm (h ▸ hsecond) zero_le))⟩

def independentCompletions {k n : ℕ} (fixed : Finset (Fin n))
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty) :
    PMF ((Fin n → Bool) × (Fin n → Bool)) :=
  (completionLaw fixed x hx).bind fun v =>
    (completionLaw fixed y hy).map fun w => (v, w)

private theorem independentCompletions_laws {k n : ℕ} (fixed : Finset (Fin n))
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty) :
    (independentCompletions fixed x y hx hy).map Prod.fst = completionLaw fixed x hx ∧
      (independentCompletions fixed x y hx hy).map Prod.snd = completionLaw fixed y hy := by
  constructor
  · change ((completionLaw fixed x hx).bind fun v =>
      (completionLaw fixed y hy).map (fun w => (v, w))).map Prod.fst = _
    rw [PMF.map_bind]
    simp only [PMF.map_comp]
    change (completionLaw fixed x hx).bind (fun v =>
      (completionLaw fixed y hy).map (Function.const _ v)) = _
    simp only [PMF.map_const, PMF.bind_pure]
  · rw [independentCompletions, PMF.map_bind]
    simp only [PMF.map_comp]
    change (completionLaw fixed x hx).bind (fun _ =>
      (completionLaw fixed y hy).map id) = _
    rw [PMF.map_id, PMF.bind_const]

theorem completionLaw_congr {k n : ℕ} (fixed : Finset (Fin n))
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty)
    (hxy : ∀ i ∈ fixed, x i = y i) :
    completionLaw fixed x hx = completionLaw fixed y hy := by
  classical
  have he : completions k n fixed x = completions k n fixed y := by
    ext w
    simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, hf⟩
      exact ⟨hw, fun i hi => (hf i hi).trans (hxy i hi)⟩
    · rintro ⟨hw, hf⟩
      exact ⟨hw, fun i hi => (hf i hi).trans (hxy i hi).symm⟩
  apply PMF.ext
  intro w
  simp only [completionLaw_apply, he]

def resetReady {n : ℕ} (fixed : Finset (Fin n)) (x y : Fin n → Bool) : Prop :=
  ∃ z : Fin n, x z = false ∧ y z = false ∧
    (∀ i : Fin n, i.val ≤ z.val → i ∈ fixed) ∧
    ∀ i ∈ fixed, z.val < i.val → x i = y i

private theorem reset_completion_laws {k n : ℕ} (hk : 0 < k)
    (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty)
    (z : Fin n) (hxz : x z = false) (hyz : y z = false)
    (leftFixed : ∀ i : Fin n, i.val ≤ z.val → i ∈ fixed)
    (farSame : ∀ i ∈ fixed, z.val < i.val → x i = y i) :
    (resetCoupling fixed x hy.choose hx z).map Prod.fst = completionLaw fixed x hx ∧
      (resetCoupling fixed x hy.choose hx z).map Prod.snd = completionLaw fixed y hy := by
  classical
  have ha := (Finset.mem_filter.mp hx.choose_spec).2
  have hb := (Finset.mem_filter.mp hy.choose_spec).2
  have haz : hx.choose z = false := (ha.2 z (leftFixed z le_rfl)).trans hxz
  have hbz : hy.choose z = false := (hb.2 z (leftFixed z le_rfl)).trans hyz
  have hs : ∀ i ∈ fixed, z.val < i.val → hx.choose i = hy.choose i := by
    intro i hi hz
    exact (ha.2 i hi).trans ((farSame i hi hz).trans (hb.2 i hi).symm)
  have ht := (reset_law_transport hk fixed hx.choose hy.choose ha.1 hb.1 z
    haz hbz leftFixed hs).1
  have hax := completionLaw_congr fixed hx.choose x
    (completion_nonempty fixed hx.choose ha.1) hx ha.2
  have hby := completionLaw_congr fixed hy.choose y
    (completion_nonempty fixed hy.choose hb.1) hy hb.2
  rw [hax, hby] at ht
  constructor
  · rw [resetCoupling, PMF.map_comp]
    exact PMF.map_id _
  · rw [resetCoupling, PMF.map_comp]
    exact ht

/-- Reveal sites with the actual conditional next-bit couplings until a common
zero screens the fixed prefix, then transport a single uniform suffix.
Impossible bit pairs have zero mass and use an arbitrary fallback. -/
def prefixCoupling {k n : ℕ} (sites : List (Fin n)) (fixed : Finset (Fin n))
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty) :
    PMF ((Fin n → Bool) × (Fin n → Bool)) :=
  if hr : resetReady fixed x y then
    resetCoupling fixed x hy.choose hx hr.choose
  else
    match sites with
    | [] => independentCompletions fixed x y hx hy
    | i :: rest =>
      (bitCoupling ((completionLaw fixed x hx).map (fun w => w i))
        ((completionLaw fixed y hy).map (fun w => w i))).bind fun bits =>
        if hx' : (completions k n (insert i fixed) (Function.update x i bits.1)).Nonempty then
          if hy' : (completions k n (insert i fixed) (Function.update y i bits.2)).Nonempty then
            prefixCoupling rest (insert i fixed) (Function.update x i bits.1)
              (Function.update y i bits.2) hx' hy'
          else independentCompletions fixed x y hx hy
        else independentCompletions fixed x y hx hy

/-- The recursively constructed joint law has the exact full completion-law
marginals, with the complete exterior fixed throughout every prefix refinement. -/
theorem prefix_coupling_marginals {k n : ℕ} (hk : 0 < k) (sites : List (Fin n))
    (hn : sites.Nodup) (fixed : Finset (Fin n))
    (hfree : ∀ i ∈ sites, i ∉ fixed) (x y : Fin n → Bool)
    (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty) :
    (prefixCoupling sites fixed x y hx hy).map Prod.fst = completionLaw fixed x hx ∧
      (prefixCoupling sites fixed x y hx hy).map Prod.snd = completionLaw fixed y hy := by
  classical
  induction sites generalizing fixed x y with
  | nil =>
    by_cases hr : resetReady fixed x y
    · rw [prefixCoupling, dif_pos hr]
      obtain ⟨hzx, hzy, hl, hs⟩ := hr.choose_spec
      exact reset_completion_laws hk fixed x y hx hy hr.choose hzx hzy hl hs
    · simpa only [prefixCoupling, dif_neg hr] using
        independentCompletions_laws fixed x y hx hy
  | cons i rest ih =>
    by_cases hr : resetReady fixed x y
    · rw [prefixCoupling, dif_pos hr]
      obtain ⟨hzx, hzy, hl, hs⟩ := hr.choose_spec
      exact reset_completion_laws hk fixed x y hx hy hr.choose hzx hzy hl hs
    rw [prefixCoupling, dif_neg hr]
    have hi := hfree i (by simp)
    have hrn := (List.nodup_cons.mp hn).2
    have hrf : ∀ j ∈ rest, j ∉ insert i fixed := by
      intro j hj hm
      rcases Finset.mem_insert.mp hm with hji | hjf
      · exact (List.nodup_cons.mp hn).1 (hji ▸ hj)
      · exact hfree j (by simp [hj]) hjf
    let p := (completionLaw fixed x hx).map (fun w => w i)
    let q := (completionLaw fixed y hy).map (fun w => w i)
    let joint := bitCoupling p q
    let child := fun bits : Bool × Bool =>
      if hx' : (completions k n (insert i fixed) (Function.update x i bits.1)).Nonempty then
        if hy' : (completions k n (insert i fixed) (Function.update y i bits.2)).Nonempty then
          prefixCoupling rest (insert i fixed) (Function.update x i bits.1)
            (Function.update y i bits.2) hx' hy'
        else independentCompletions fixed x y hx hy
      else independentCompletions fixed x y hx hy
    have hc : ∀ bits, joint bits ≠ 0 →
        (child bits).map Prod.fst = nextCompletionLaw fixed x hx i bits.1 ∧
          (child bits).map Prod.snd = nextCompletionLaw fixed y hy i bits.2 := by
      intro bits hs
      have hf := bitCoupling_supported_fibers fixed x y hx hy i hi bits hs
      dsimp only [child]
      rw [dif_pos hf.1, dif_pos hf.2]
      simpa only [nextCompletionLaw, dif_pos hf.1, dif_pos hf.2] using
        ih hrn (insert i fixed) hrf (Function.update x i bits.1)
          (Function.update y i bits.2) hf.1 hf.2
    have hm := bitCoupling_laws p q
    constructor
    · change (joint.bind child).map Prod.fst = _
      rw [PMF.map_bind]
      calc
        joint.bind (fun bits => (child bits).map Prod.fst) =
            joint.bind (fun bits => nextCompletionLaw fixed x hx i bits.1) := by
          apply PMF.ext
          intro w
          simp only [PMF.bind_apply]
          apply tsum_congr
          intro bits
          by_cases hs : joint bits = 0
          · simp [hs]
          · rw [(hc bits hs).1]
        _ = (joint.map Prod.fst).bind (nextCompletionLaw fixed x hx i) :=
          (PMF.bind_map joint Prod.fst (nextCompletionLaw fixed x hx i)).symm
        _ = p.bind (nextCompletionLaw fixed x hx i) := by rw [hm.1]
        _ = completionLaw fixed x hx := completion_disintegration fixed x hx i hi
    · change (joint.bind child).map Prod.snd = _
      rw [PMF.map_bind]
      calc
        joint.bind (fun bits => (child bits).map Prod.snd) =
            joint.bind (fun bits => nextCompletionLaw fixed y hy i bits.2) := by
          apply PMF.ext
          intro w
          simp only [PMF.bind_apply]
          apply tsum_congr
          intro bits
          by_cases hs : joint bits = 0
          · simp [hs]
          · rw [(hc bits hs).2]
        _ = (joint.map Prod.snd).bind (nextCompletionLaw fixed y hy i) :=
          (PMF.bind_map joint Prod.snd (nextCompletionLaw fixed y hy i)).symm
        _ = q.bind (nextCompletionLaw fixed y hy i) := by rw [hm.2.1]
        _ = completionLaw fixed y hy := completion_disintegration fixed y hy i hi

def mean {α : Type*} (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, p a * f a

theorem mean_bind {α β : Type*} (p : PMF α) (q : α → PMF β)
    (f : β → ℝ≥0∞) : mean (p.bind q) f = mean p (fun a => mean (q a) f) := by
  simp only [mean, PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc, ENNReal.tsum_mul_left]

theorem mean_map {α β : Type*} (p : PMF α) (g : α → β)
    (f : β → ℝ≥0∞) : mean (p.map g) f = mean p (fun a => f (g a)) := by
  rw [PMF.map, mean_bind]
  simp [mean, PMF.pure_apply]

theorem mean_const {α : Type*} (p : PMF α) (c : ℝ≥0∞) :
    mean p (fun _ => c) = c := by
  rw [mean, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem mean_congr_support {α : Type*} (p : PMF α) (f g : α → ℝ≥0∞)
    (h : ∀ a, p a ≠ 0 → f a = g a) : mean p f = mean p g := by
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ha]

/-- Internal Hamming cost on the listed coordinates. -/
def scanHamming {n : ℕ} : List (Fin n) → ((Fin n → Bool) × (Fin n → Bool)) → ℝ≥0∞
  | [], _ => 0
  | i :: rest, w => (if w.1 i = w.2 i then 0 else 1) + scanHamming rest w

private theorem scanHamming_eq_zero {n : ℕ} (sites : List (Fin n))
    (w : (Fin n → Bool) × (Fin n → Bool)) (h : ∀ i ∈ sites, w.1 i = w.2 i) :
    scanHamming sites w = 0 := by
  induction sites with
  | nil => rfl
  | cons i rest ih =>
    simp only [scanHamming, if_pos (h i (by simp)), zero_add]
    exact ih (fun j hj => h j (by simp [hj]))

theorem reset_mean_zero {k n : ℕ} (sites : List (Fin n))
    (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (hx : (completions k n fixed x).Nonempty) (z : Fin n)
    (leftFixed : ∀ i : Fin n, i.val ≤ z.val → i ∈ fixed)
    (hfree : ∀ i ∈ sites, i ∉ fixed) :
    mean (resetCoupling fixed x y hx z) (scanHamming sites) = 0 := by
  rw [resetCoupling, mean_map]
  have hz : ∀ w : Fin n → Bool, scanHamming sites (w, resetMap z y w) = 0 := by
    intro w
    apply scanHamming_eq_zero
    intro i hi
    have hgt : ¬ i.val ≤ z.val := fun h => hfree i hi (leftFixed i h)
    simp [resetMap, hgt]
  simp only [hz]
  exact mean_const _ 0

theorem coupled_fixed {k n : ℕ} (fixed : Finset (Fin n))
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty)
    (p : PMF ((Fin n → Bool) × (Fin n → Bool)))
    (hm : p.map Prod.fst = completionLaw fixed x hx ∧
      p.map Prod.snd = completionLaw fixed y hy)
    (w : (Fin n → Bool) × (Fin n → Bool)) (hw : p w ≠ 0) :
    ∀ i ∈ fixed, w.1 i = x i ∧ w.2 i = y i := by
  have hf := pmf_le_map p Prod.fst w
  have hs := pmf_le_map p Prod.snd w
  rw [hm.1, completionLaw_apply] at hf
  rw [hm.2, completionLaw_apply] at hs
  have hxw : w.1 ∈ completions k n fixed x := by
    by_contra h
    rw [if_neg h] at hf
    exact hw (le_antisymm hf zero_le)
  have hyw : w.2 ∈ completions k n fixed y := by
    by_contra h
    rw [if_neg h] at hs
    exact hw (le_antisymm hs zero_le)
  exact fun i hi => ⟨(Finset.mem_filter.mp hxw).2.2 i hi,
    (Finset.mem_filter.mp hyw).2.2 i hi⟩

theorem mean_head {n : ℕ} (p : PMF ((Fin n → Bool) × (Fin n → Bool)))
    (i : Fin n) (rest : List (Fin n)) (a b : Bool)
    (h : ∀ w, p w ≠ 0 → w.1 i = a ∧ w.2 i = b) :
    mean p (scanHamming (i :: rest)) =
      (if a = b then 0 else 1) + mean p (scanHamming rest) := by
  calc
    _ = mean p (fun w => (if a = b then 0 else 1) + scanHamming rest w) := by
      apply mean_congr_support
      intro w hw
      simp only [scanHamming, (h w hw).1, (h w hw).2]
    _ = _ := by
      simp only [mean, mul_add, ENNReal.tsum_add]
      rw [← mean, mean_const]

theorem half_failure_budget (p : PMF (Bool × Bool))
    (hh : (1 / 2 : ℝ≥0∞) ≤ p (false, false)) :
    mean p (fun bits => if bits = (false, false) then 0 else 2) ≤ 1 := by
  have ht : ∑ bits : Bool × Bool, (p bits).toNNReal = 1 := by
    rw [← ENNReal.toNNReal_sum (fun a _ => p.apply_ne_top a)]
    have ht0 : ∑ bits : Bool × Bool, p bits = 1 := by
      simpa only [tsum_fintype] using p.tsum_coe
    rw [ht0]
    rfl
  have hh' : (1 / 2 : ℝ≥0) ≤ (p (false, false)).toNNReal := by
    apply (ENNReal.coe_le_coe).mp
    simpa only [ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_one,
      ENNReal.coe_ofNat, ENNReal.coe_toNNReal (p.apply_ne_top _)] using hh
  simp only [mean, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, false_and, and_false,
    and_self, ite_false, ite_true, mul_zero, add_zero]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at ht
  have hb : (p (true, true)).toNNReal * 2 + (p (true, false)).toNNReal * 2 +
      (p (false, true)).toNNReal * 2 ≤ 1 := by nlinarith
  rw [← ENNReal.coe_toNNReal (p.apply_ne_top (true, true)),
    ← ENNReal.coe_toNNReal (p.apply_ne_top (true, false)),
    ← ENNReal.coe_toNNReal (p.apply_ne_top (false, true))]
  exact_mod_cast hb

#print axioms prefix_coupling_marginals
#print axioms conditional_step_coupling
#print axioms zero_screening
#print axioms reset_law_transport

end D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
