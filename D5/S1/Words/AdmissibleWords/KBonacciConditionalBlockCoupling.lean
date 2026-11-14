/- GID: D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Exterior-conditioned legal-word completions and their zero-reset coupling. -/

import D5.S1.Words.ClosedRunStarts
import D5.S0.Tower.DBonacci.TerminalSampling
import Mathlib.Tactic

/-! Actual finite conditional fibers retain every fixed exterior and prefix bit. -/

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling

open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.TerminalSampling
open D5.S1.Words.ClosedRunStarts
open scoped BigOperators ENNReal NNReal

private theorem legal_iff (k n : ℕ) (hk : 0 < k) (w : Fin n → Bool) :
    DBonacciAdmissible k n w ↔ ∀ s, ¬ TrueBlock w s k := by
  by_cases hkn : k ≤ n
  · exact (closed_word_run_start_equivalence n k hk hkn w).1
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hw := runAdmissible_eq_true_of_length_le r r n w (by omega) le_rfl
    exact ⟨fun _ s h => by have := h.1; omega, fun _ => hw⟩

private theorem legal_delete {k n : ℕ} (hk : 0 < k) (w : Fin n → Bool)
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

private theorem completionLaw_apply {k n : ℕ} (fixed : Finset (Fin n))
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

private theorem completion_nonempty {k n : ℕ} (fixed : Finset (Fin n))
    (exterior : Fin n → Bool) (h : DBonacciAdmissible k n exterior) :
    (completions k n fixed exterior).Nonempty := by
  classical
  exact ⟨exterior, by simp [completions, h]⟩

private theorem zero_completion_injection {k n : ℕ} (hk : 0 < k)
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

#print axioms conditional_step_coupling
#print axioms zero_screening
#print axioms reset_law_transport

end D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
