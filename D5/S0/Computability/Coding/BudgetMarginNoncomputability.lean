/- GID: D5/S0/Computability/Coding/BudgetMarginNoncomputability
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/BudgetMarginNoncomputability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Budget programs admit no uniform positive-margin or optimal-mass algorithm. -/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce
import Mathlib.Tactic

open Nat.Partrec (Code)
open Nat.Partrec.Code

set_option backward.isDefEq.respectTransparency false

namespace D5.S0.Computability.Coding.BudgetMarginNoncomputability

private def seen (c : Code) (n : ℕ) : Bool := (evaln n c 0).isSome

private def first (c : Code) (n : ℕ) : Bool := seen c n && !(seen c (n - 1))

private def pulse (d : ℕ) (c : Code) (n : ℕ) : ℕ :=
  bif first c n then d^n - 1 else 0

private theorem prim_seen : Primrec fun q : Code × ℕ => seen q.1 q.2 :=
  Primrec.option_isSome.comp <| primrec_evaln.comp
    ((Primrec.snd.pair Primrec.fst).pair (Primrec.const 0))

private theorem prim_first : Primrec fun q : Code × ℕ => first q.1 q.2 :=
  Primrec.and.comp prim_seen (Primrec.not.comp <|
    prim_seen.comp (Primrec.fst.pair <| Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))

private theorem prim_pulse (d : ℕ) : Primrec fun q : Code × ℕ => pulse d q.1 q.2 := by
  apply Primrec.cond prim_first _ (Primrec.const 0)
  exact Primrec.nat_sub.comp
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const d) Primrec.snd)
    (Primrec.const 1)

set_option maxHeartbeats 1200000 in
-- Elaborating the universal-code composition traverses the encoding implementation.
private theorem exists_compiler (d : ℕ) : ∃ compile : Code → Code,
    Computable compile ∧ ∀ c n, eval (compile c) n = Part.some (pulse d c n) := by
  have hc : Computable fun k : ℕ => pulse d (Denumerable.ofNat Code k.unpair.1) k.unpair.2 :=
    (prim_pulse d).to_comp.comp
      (((Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair)).pair
        (Computable.snd.comp Computable.unpair))
  obtain ⟨q, hq⟩ := exists_code.mp (Partrec.nat_iff.mp hc.partrec)
  refine ⟨fun c => curry q (Encodable.encode c),
    primrec₂_curry.to_comp.comp (Computable.const q) Computable.encode, ?_⟩
  intro c n
  simpa only [eval_curry, hq, PFun.coe_val, Nat.unpair_pair, Denumerable.ofNat_encode]

private theorem seen_mono (c : Code) {n m : ℕ} (h : n ≤ m) : seen c n = true → seen c m = true := by
  simp only [seen, Option.isSome_iff_exists]
  rintro ⟨x, hx⟩
  exact ⟨x, evaln_mono h hx⟩

private theorem first_pos (c : Code) {n : ℕ} (h : first c n = true) : 0 < n := by
  cases n with
  | zero => simp [first, seen, evaln] at h
  | succ n => omega

private theorem first_unique (c : Code) {n m : ℕ}
    (hn : first c n = true) (hm : first c m = true) : n = m := by
  simp only [first, Bool.and_eq_true] at hn hm
  rcases lt_trichotomy n m with h | h | h
  · have hh := seen_mono c (show n ≤ m-1 by omega) hn.1
    cases he : seen c (m-1) <;> simp_all
  · exact h
  · have hh := seen_mono c (show m ≤ n-1 by omega) hm.1
    cases he : seen c (n-1) <;> simp_all

private theorem support_subsingleton (d : ℕ) (c : Code) :
    (Function.support (pulse d c)).Subsingleton := by
  intro n hn m hm
  have hn' : first c n = true := by
    cases h : first c n <;> simp_all [Function.mem_support, pulse]
  have hm' : first c m = true := by
    cases h : first c m <;> simp_all [Function.mem_support, pulse]
  exact first_unique c hn' hm'

private theorem halts_first (c : Code) (h : (eval c 0).Dom) : ∃ n, first c n = true := by
  obtain ⟨x,hx⟩ := Part.dom_iff_mem.mp h
  obtain ⟨n,hn⟩ := evaln_complete.mp hx
  have hex : ∃ n, seen c n = true := ⟨n, Option.isSome_iff_exists.mpr ⟨x,hn⟩⟩
  let t := Nat.find hex
  have ht : seen c t = true := Nat.find_spec hex
  have hpos : 0 < t := by
    by_contra hh
    have ht0 : t = 0 := by omega
    rw [ht0] at ht
    simp [seen,evaln] at ht
  have hprev : seen c (t-1) = false := by
    have := Nat.find_min hex (show t-1 < t by omega)
    cases hv : seen c (t-1) <;> simp_all
  exact ⟨t, by simp [first,ht,hprev]⟩


set_option maxHeartbeats 1200000 in
-- The total evaluator combines dependent partial-function membership proofs.
private theorem no_cutoff : ¬ ∃ A : Code →. ℕ, Partrec A ∧
    ∀ c, ∃ N ∈ A c, ∀ k, first c k = true → k ≤ N := by
  rintro ⟨A, hA, hs⟩
  let cutoff : Code → ℕ := fun c => Classical.choose (hs c)
  have hcut : Computable cutoff := hA.of_eq_tot (fun c => (Classical.choose_spec (hs c)).1)
  have hb : Computable fun c => seen c (cutoff c) :=
    prim_seen.to_comp.comp (Computable.id.pair hcut)
  apply ComputablePred.halting_problem 0
  have hbp : ComputablePred (fun c => seen c (cutoff c) = true) :=
    ⟨inferInstance, by simpa using hb⟩
  apply hbp.of_eq
  intro c
  constructor
  · intro h
    simp only [seen, Option.isSome_iff_exists] at h
    obtain ⟨x, hx⟩ := h
    exact (evaln_sound hx).1
  · intro h
    obtain ⟨t,ht⟩ := halts_first c h
    have hseen : seen c t = true := by
      simp only [first, Bool.and_eq_true] at ht
      exact ht.1
    exact seen_mono c ((Classical.choose_spec (hs c)).2 t ht) hseen


private theorem first_halts (c : Code) {n : ℕ} (h : first c n = true) : (eval c 0).Dom := by
  have h' : seen c n = true := by
    simp only [first, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h'
  exact (evaln_sound hx).1

private theorem pulse_shape (d : ℕ) (c : Code) {n : ℕ} (h : first c n = true) :
    ∀ k, pulse d c k = if k = n then d^n - 1 else 0 := by
  intro k
  by_cases hkn : k = n
  · subst k; simp [pulse, h]
  · have hk : first c k = false := by
      cases hh : first c k
      · rfl
      · exact (hkn (first_unique c hh h)).elim
    simp [pulse, hk, hkn]


open scoped BigOperators ENNReal
open DepthBudgetIidGreedyOptimality

/-- A program presents a total budget, without providing its support. -/
def Presents (e : Code) (b : ℕ → ℕ) : Prop :=
  ∀ n, eval e n = Part.some (b n)

/-- The semantic growth promise does not include an effective threshold. -/
def Subexponential (b : ℕ → ℕ) : Prop :=
  ∀ a : ℝ, 1 < a → ∃ N : ℕ, ∀ n, N ≤ n → (b n : ℝ) ≤ a^n

/-- Uniform budget sum, with the unused root budget required to vanish. -/
noncomputable def budgetSum (d : ℕ) (b : ℕ → ℕ) : ℝ :=
  ∑' n, (b n : ℝ) / (d : ℝ)^n

/-- The supremum uses precisely the frozen legal codes and their iid masses. -/
noncomputable def optimalMass (d : ℕ) (b : ℕ → ℕ) : ℝ :=
  (sSup {x : ℝ≥0∞ | ∃ F : Set (List (Fin d)),
    Legal b F ∧ x = codeMass (fun _ : Fin d => (d : ℝ)⁻¹) F}).toReal

/-- The surviving margin is the complement of the optimal deleted mass. -/
noncomputable def margin (d : ℕ) (b : ℕ → ℕ) : ℝ := 1 - optimalMass d b

/-- All promises concern semantics; the input remains a code. -/
def Promise (d : ℕ) (e : Code) (b : ℕ → ℕ) : Prop :=
  Presents e b ∧ (Function.support b).Finite ∧ b 0 = 0 ∧
  Subexponential b ∧ budgetSum d b < 1

private theorem optimal_eq (d : ℕ) (hd : 2 ≤ d) (b : ℕ → ℕ)
    {x : ℝ≥0∞} (hx : IsGreatest {x : ℝ≥0∞ | ∃ F : Set (List (Fin d)),
      Legal b F ∧ x = codeMass (fun _ : Fin d => (d : ℝ)⁻¹) F} x) :
    optimalMass d b = x.toReal := by
  classical
  let tie : LinearOrder (List (Fin d)) :=
    LinearOrder.lift' Encodable.encode Encodable.encode_injective
  have hp : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hsum : ∑ _ : Fin d, (d : ℝ)⁻¹ = 1 := by simp [ne_of_gt hp]
  have hg := (depth_budget_iid_greedy_optimality
    (fun _ : Fin d => (d : ℝ)⁻¹) (fun _ => inv_pos.mpr hp) hsum b (fun _ => tie)).2.2
  rw [optimalMass, hg.csSup_eq, ← hx.unique hg]

private theorem mem_words {d n : ℕ} (v : List (Fin d)) :
    v ∈ words n ↔ v.length = n := by
  simp [words, List.Vector, Subtype.exists, eq_comm]


private theorem mem_level {d n : ℕ} (F : Set (List (Fin d))) (v : List (Fin d)) :
    v ∈ level F n ↔ v.length = n ∧ v ∈ F := by simp [level, mem_words]

private theorem words_card (d n : ℕ) : (words (α := Fin d) n).card = d^n := by
  classical
  unfold words
  have hi : Function.Injective (fun v : List.Vector (Fin d) n => v.1) :=
    List.Vector.toList_injective
  rw [Finset.card_image_of_injective _ hi]
  simp [card_vector]

private theorem mass_one_level (d n : ℕ) (F : Set (List (Fin d)))
    (hlen : ∀ v ∈ F, v.length = n) :
    codeMass (fun _ : Fin d => (d : ℝ)⁻¹) F =
      ENNReal.ofReal ((level F n).card / (d : ℝ)^n) := by
  classical
  have he : F = (level F n : Set (List (Fin d))) := by
    ext v
    simp only [Finset.mem_coe, mem_level]
    exact ⟨fun hv => ⟨hlen v hv,hv⟩, And.right⟩
  conv_lhs => rw [he]
  unfold codeMass
  change (∑' v : ↥(level F n), ENNReal.ofReal
    (wordMass (fun _ : Fin d => (d : ℝ)⁻¹) v.1)) = _
  rw [Finset.tsum_subtype (level F n)
    (fun v => ENNReal.ofReal (wordMass (fun _ : Fin d => (d : ℝ)⁻¹) v))]
  have hm (v : List (Fin d)) (hv : v ∈ level F n) :
      wordMass (fun _ : Fin d => (d : ℝ)⁻¹) v = (d : ℝ)⁻¹ ^ n := by
    simp [wordMass, List.map_const', (mem_level F v).mp hv |>.1]
  rw [Finset.sum_congr rfl (fun v hv => congrArg ENNReal.ofReal (hm v hv)),
    Finset.sum_const, ← ENNReal.ofReal_nsmul]
  congr 1
  simp [div_eq_mul_inv, inv_pow]

private theorem single_optimal (d : ℕ) (hd : 2 ≤ d) (n k : ℕ)
    (hn : 0 < n) (hk : k ≤ d ^ n) :
    optimalMass d (fun m => if m = n then k else 0) = (k : ℝ) / (d : ℝ)^n := by
  classical
  have hu (F : Set (List (Fin d))) (hF : Legal (fun m => if m = n then k else 0) F) :
      ∀ v ∈ F, v.length = n := by
    intro v hv
    by_contra hlen
    have hc := hF.2.2 v.length
    simp only [if_neg hlen, Nat.le_zero] at hc
    have hmem : v ∈ level F v.length := (mem_level F v).mpr ⟨rfl,hv⟩
    rw [Finset.card_eq_zero.mp hc] at hmem
    exact Finset.notMem_empty _ hmem
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (s := words (α := Fin d) n)
    (by simpa [words_card] using hk)
  have hslen : ∀ v ∈ (S : Set (List (Fin d))), v.length = n :=
    fun v hv => (mem_words v).mp (hS hv)
  have hslegal : Legal (fun m => if m = n then k else 0) (S : Set (List (Fin d))) := by
    refine ⟨fun u hu v hv huv => huv.eq_of_length ((hslen u hu).trans (hslen v hv).symm), ?_, ?_⟩
    · intro h
      have := hslen [] h
      exact (Nat.ne_of_gt hn) this.symm
    · intro m
      by_cases hm : m = n
      · subst m
        have he : level (S : Set (List (Fin d))) n = S := by
          ext v; simp only [mem_level, Finset.mem_coe]
          exact ⟨And.right, fun hv => ⟨hslen v hv,hv⟩⟩
        simp [he,hcard]
      · have he : level (S : Set (List (Fin d))) m = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro v hv
          obtain ⟨hlen,hv⟩ := (mem_level _ v).mp hv
          exact hm (hlen.symm.trans (hslen v hv))
        simp [he,hm]
  have hl : level (S : Set (List (Fin d))) n = S := by
    ext v; simp only [mem_level, Finset.mem_coe]
    exact ⟨And.right, fun hv => ⟨hslen v hv,hv⟩⟩
  have hx : IsGreatest {x : ℝ≥0∞ | ∃ F : Set (List (Fin d)),
      Legal (fun m => if m = n then k else 0) F ∧
      x = codeMass (fun _ : Fin d => (d : ℝ)⁻¹) F}
      (ENNReal.ofReal ((k : ℝ) / (d : ℝ)^n)) := by
    refine ⟨⟨S,hslegal,?_⟩,?_⟩
    · rw [mass_one_level d n _ hslen, hl, hcard]
    · rintro x ⟨F,hF,rfl⟩
      rw [mass_one_level d n F (hu F hF)]
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (show (level F n).card ≤ k by simpa using hF.2.2 n)
  rw [optimal_eq d hd _ hx, ENNReal.toReal_ofReal (by positivity)]

private theorem zero_optimal (d : ℕ) (hd : 2 ≤ d) :
    optimalMass d (fun _ => 0) = 0 := by
  classical
  have hz (F : Set (List (Fin d))) (hF : Legal (fun _ => 0) F) : F = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hmem : v ∈ level F v.length := (mem_level F v).mpr ⟨rfl,hv⟩
    have hc := hF.2.2 v.length
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hc)] at hmem
    exact Finset.notMem_empty _ hmem
  rw [optimal_eq d hd _ (x := 0) ?_]
  · simp
  refine ⟨⟨∅, ?_, ?_⟩, ?_⟩
  · refine ⟨by simp [PrefixFreeCode.IsPrefixFree], by simp, ?_⟩
    intro n; simp [level]
  · simp [codeMass]
  · rintro x ⟨F,hF,rfl⟩
    simp [hz F hF, codeMass]

private theorem finite_subexponential (b : ℕ → ℕ) (hs : (Function.support b).Finite) :
    Subexponential b := by
  intro a ha
  obtain ⟨N, hN⟩ := hs.bddAbove
  refine ⟨N+1, ?_⟩
  intro n hn
  have hz : b n = 0 := by
    by_contra h
    have hh : n ≤ N := hN h
    omega
  rw [hz, Nat.cast_zero]
  exact pow_nonneg (by linarith) _

private theorem margin_at (d : ℕ) (hd : 2 ≤ d) (c : Code) {n : ℕ}
    (h : first c n = true) : margin d (pulse d c) = ((d : ℝ)^n)⁻¹ := by
  have hz : 0 < (d : ℝ)^n := pow_pos (by exact_mod_cast (show 0 < d by omega)) n
  have hdn : 1 ≤ d^n := Nat.one_le_pow n d (by omega)
  have hcast : ((d^n-1 : ℕ) : ℝ) = (d : ℝ)^n-1 := by
    rw [Nat.cast_sub hdn]; norm_cast
  rw [margin, funext (pulse_shape d c h), single_optimal d hd n _
    (first_pos c h) (Nat.sub_le _ _), hcast]
  field_simp
  ring

private theorem pulse_zero (d : ℕ) (c : Code) (h : ¬(eval c 0).Dom) :
    pulse d c = fun _ => 0 := by
  funext n
  cases hn : first c n
  · simp [pulse, hn]
  · exact (h (first_halts c hn)).elim

private theorem margin_never (d : ℕ) (hd : 2 ≤ d) (c : Code) (h : ¬(eval c 0).Dom) :
    margin d (pulse d c) = 1 := by
  simp [margin, pulse_zero d c h, zero_optimal d hd]

private theorem pulse_promise (d : ℕ) (hd : 2 ≤ d) (c e : Code)
    (he : Presents e (pulse d c)) : Promise d e (pulse d c) := by
  have hf := (support_subsingleton d c).finite
  refine ⟨he, hf, by simp [pulse, first, seen, evaln], finite_subexponential _ hf, ?_⟩
  by_cases h : ∃ n, first c n = true
  · obtain ⟨n, hn⟩ := h
    have hz : 0 < (d : ℝ)^n := pow_pos (by exact_mod_cast (show 0 < d by omega)) n
    have hdn : 1 ≤ d^n := Nat.one_le_pow n d (by omega)
    have hcast : ((d^n-1 : ℕ) : ℝ) = (d : ℝ)^n-1 := by
      rw [Nat.cast_sub hdn]; norm_cast
    have hs : budgetSum d (pulse d c) = ((d^n-1 : ℕ) : ℝ) / (d : ℝ)^n := by
      unfold budgetSum
      rw [tsum_eq_single n]
      · simp [pulse_shape d c hn]
      · intro k hk; simp [pulse_shape d c hn, hk]
    rw [hs,hcast]
    exact (div_lt_one hz).mpr (by linarith)
  · have hp : pulse d c = fun _ => 0 := by
      funext n
      cases hn : first c n <;> simp_all [pulse]
    simp [budgetSum,hp]

/-- A pair codes the positive rational (u+1)/(v+1). Every positive rational has this form. -/
def positiveRational (q : ℕ × ℕ) : ℚ := (q.1+1 : ℕ) / (q.2+1 : ℕ)

/-- A triple codes (u-v)/(w+1), allowing every signed rational approximation. -/
def signedRational (q : ℕ × ℕ × ℕ) : ℚ :=
  ((q.1 : ℚ) - q.2.1) / (q.2.2+1 : ℕ)

/-- A partial algorithm returns a positive rational below the actual surviving margin. -/
def MarginSelector (d : ℕ) (A : Code →. (ℕ × ℕ)) : Prop :=
  Partrec A ∧ ∀ e b, Promise d e b →
    ∃ q ∈ A e, 0 < positiveRational q ∧ (positiveRational q : ℝ) ≤ margin d b

/-- On promised programs, each precision query terminates with error at most 2^(-k). -/
private def CauchyQuerySelector (d : ℕ) (A : (Code × ℕ) →. (ℕ × ℕ × ℕ)) : Prop :=
  Partrec A ∧ ∀ e b, Promise d e b → ∀ k,
    ∃ q ∈ A (e,k), |(signedRational q : ℝ) - optimalMass d b| ≤ (2 : ℝ)⁻¹ ^ k

private theorem no_margin_selector (d : ℕ) (hd : 2 ≤ d) :
    ¬ ∃ A, MarginSelector d A := by
  rintro ⟨A,hA,hs⟩
  obtain ⟨compile, hc, heval⟩ := exists_compiler d
  let B : Code →. ℕ := fun c => (A (compile c)).map (fun q => q.2+1)
  have hB : Partrec B := (hA.comp hc).map
    (Computable.succ.comp (Computable.snd.comp Computable.snd)).to₂
  apply no_cutoff
  refine ⟨B,hB,?_⟩
  intro c
  obtain ⟨q,hq,_,hbound⟩ := hs (compile c) (pulse d c)
    (pulse_promise d hd c _ (heval c))
  refine ⟨q.2+1, Part.mem_map _ hq, ?_⟩
  intro k hk
  have hsmall : ((q.2+1 : ℕ) : ℝ)⁻¹ ≤ (positiveRational q : ℝ) := by
    simp only [positiveRational, Rat.cast_div, Rat.cast_natCast]
    rw [inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show 1 ≤ q.1+1 by omega)
  have hbound := hsmall.trans hbound
  rw [margin_at d hd c hk] at hbound
  have hp : 0 < (d : ℝ)^k := pow_pos (by exact_mod_cast (show 0 < d by omega)) _
  have hbound' : (d : ℝ)^k ≤ (q.2+1 : ℕ) :=
    (inv_le_inv₀ (by positivity) hp).mp hbound
  have hn : d^k ≤ q.2+1 := by exact_mod_cast hbound'
  have hk' : k < d^k := (Nat.lt_two_pow_self (n := k)).trans_le (Nat.pow_le_pow_left hd k)
  omega

set_option maxHeartbeats 1200000 in
-- The evaluator and rational threshold bridge are elaborated together.
private theorem no_cauchy_query_selector (d : ℕ) (hd : 2 ≤ d) :
    ¬ ∃ A, CauchyQuerySelector d A := by
  rintro ⟨A,hA,hs⟩
  obtain ⟨compile,hc,heval⟩ := exists_compiler d
  have ht (c : Code) : ∃ q ∈ A (compile c,3),
      |(signedRational q : ℝ) - optimalMass d (pulse d c)| ≤ (2 : ℝ)⁻¹ ^ 3 :=
    hs _ _ (pulse_promise d hd c _ (heval c)) 3
  let Q : Code → ℕ × ℕ × ℕ := fun c => Classical.choose (ht c)
  have hQ : Computable Q :=
    (hA.comp (hc.pair (Computable.const 3))).of_eq_tot
      (fun c => (Classical.choose_spec (ht c)).1)
  let read : (ℕ × ℕ × ℕ) → Bool := fun q =>
    decide (q.2.2+1 + 4*q.2.1 < 4*q.1)
  have hr : Primrec read :=
    (Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.fst.comp Primrec.snd)))
      (Primrec.nat_mul.comp (Primrec.const 4) Primrec.fst)).decide
  have hb : ComputablePred (fun c => read (Q c) = true) :=
    ⟨inferInstance, by simpa using hr.to_comp.comp hQ⟩
  apply ComputablePred.halting_problem 0
  apply hb.of_eq
  intro c
  have herr := (Classical.choose_spec (ht c)).2
  change |(signedRational (Q c) : ℝ) - optimalMass d (pulse d c)| ≤ _ at herr
  have hread : read (Q c) = true ↔ (1/4 : ℝ) < (signedRational (Q c) : ℝ) := by
    simp only [read, decide_eq_true_eq, signedRational, Rat.cast_div, Rat.cast_sub,
      Rat.cast_natCast]
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    constructor
    · intro h
      have hh : ((Q c).2.2 : ℝ)+1 + 4*(Q c).2.1 < 4*(Q c).1 := by
        exact_mod_cast h
      nlinarith
    · intro h
      have hh : ((Q c).2.2 : ℝ)+1 + 4*(Q c).2.1 < 4*(Q c).1 := by
        nlinarith
      exact_mod_cast hh
  rw [hread]
  constructor
  · intro h
    by_contra hn
    have hz : optimalMass d (pulse d c) = 0 := by
      have hm := margin_never d hd c hn
      unfold margin at hm
      linarith
    rw [hz] at herr
    norm_num at herr
    linarith [(abs_le.mp herr).2]
  · intro h
    obtain ⟨n,hn⟩ := halts_first c h
    have hnpos := first_pos c hn
    have hpow : (2 : ℝ) ≤ (d : ℝ)^n := by
      exact_mod_cast ((show 2 ≤ d by exact hd).trans
        (Nat.le_self_pow (by omega) d))
    have hi : ((d : ℝ)^n)⁻¹ ≤ (1/2 : ℝ) := by
      simpa using (inv_le_inv₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hpow)
        (by norm_num : (0 : ℝ) < 2)).mpr hpow
    have hm := margin_at d hd c hn
    unfold margin at hm
    norm_num at herr
    linarith [(abs_le.mp herr).1]

/-- A name program returns encoded signed rationals at every requested precision. -/
def CauchyName (q : Code) (x : ℝ) : Prop :=
  ∀ k, ∃ j ∈ eval q k,
    |(signedRational (Denumerable.ofNat (ℕ × ℕ × ℕ) j) : ℝ) - x| ≤ (2 : ℝ)⁻¹ ^ k

/-- The partial operator terminates on promised budget indices and returns a name index. -/
def CauchySelector (d : ℕ) (A : Code →. Code) : Prop :=
  Partrec A ∧ ∀ e b, Promise d e b → ∃ q ∈ A e, CauchyName q (optimalMass d b)

private theorem no_cauchy_selector (d : ℕ) (hd : 2 ≤ d) :
    ¬ ∃ A, CauchySelector d A := by
  rintro ⟨A,hA,hs⟩
  let B : (Code × ℕ) →. (ℕ × ℕ × ℕ) := fun z =>
    (A z.1).bind fun q => (eval q z.2).map (Denumerable.ofNat (ℕ × ℕ × ℕ))
  have hE : Partrec (fun z : (Code × ℕ) × Code => eval z.2 z.1.2) :=
    eval_part.comp Computable.snd (Computable.snd.comp Computable.fst)
  have hB : Partrec B := (hA.comp Computable.fst).bind
    (hE.map ((Computable.ofNat (ℕ × ℕ × ℕ)).comp Computable.snd).to₂).to₂
  apply no_cauchy_query_selector d hd
  refine ⟨B,hB,?_⟩
  intro e b hb k
  obtain ⟨q,hq,hn⟩ := hs e b hb
  obtain ⟨j,hj,herr⟩ := hn k
  exact ⟨_, Part.mem_bind hq (Part.mem_map _ hj), herr⟩

/-- Neither a positive surviving-margin selector nor an optimal-mass Cauchy algorithm
exists even on total, finite-support, subexponential budget programs of strict budget sum. -/
theorem result (d : ℕ) (hd : 2 ≤ d) :
    (¬ ∃ A, MarginSelector d A) ∧ (¬ ∃ A, CauchySelector d A) :=
  ⟨no_margin_selector d hd, no_cauchy_selector d hd⟩

end D5.S0.Computability.Coding.BudgetMarginNoncomputability
