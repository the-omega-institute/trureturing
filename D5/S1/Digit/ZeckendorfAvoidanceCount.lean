/- GID: D5/S1/Digit/ZeckendorfAvoidanceCount
   generality: I
   mirror-B: none(waiver:source-word-count)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio]
   utility: none
   digest: Legal words avoiding the contextual replacement block have a uniform weighted count bound. -/

import D5.S1.Digit.ZeckendorfContextualReplacement
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ZeckendorfAvoidanceCount

open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfContextualReplacement

/-- Exhaustive legal words with the entering bit retained. -/
def legalWords : ℕ → Fin 2 → List (List (Fin 2))
  | 0, _ => [[]]
  | n + 1, b => (legalWords n 0).map (0 :: ·) ++
      if b = 0 then (legalWords n 1).map (1 :: ·) else []

/-- The actual last bit after reading the word. -/
def endBit : Fin 2 → List (Fin 2) → Fin 2
  | b, [] => b
  | _, a :: w => endBit a w

/-- Perron endpoint weight for the two legal-bit states. -/
noncomputable def endpointWeight (b : Fin 2) : ℝ := if b = 0 then Real.goldenRatio else 1

/-- All words avoiding B1 on aligned 14-blocks, with the short suffix explicit. -/
def blockWords (r : ℕ) : ℕ → Fin 2 → List (List (Fin 2))
  | 0, b => legalWords r b
  | k + 1, b => ((legalWords 14 b).filter (· != B1)).flatMap
      fun p => (blockWords r k (endBit b p)).map (p ++ ·)

/-- Exhaustive B1-avoiding legal words are bounded by a conditional transfer
estimate under both entering states. No block independence premise is used. -/
theorem uniform_avoidance_count (H : ℕ) :
    ((legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))).length ≤
      Real.goldenRatio ^ (H + 1) *
        (1 - (Real.goldenRatio ^ (14 : ℕ))⁻¹) ^ (H / 14) := by
  classical
  let φ := Real.goldenRatio
  have φpos : 0 < φ := Real.goldenRatio_pos
  have φone : 1 < φ := Real.one_lt_goldenRatio
  have φsq : φ ^ 2 = φ + 1 := by
    simpa [φ] using Real.goldenRatio_sq
  have end_append (b : Fin 2) (p u : List (Fin 2)) :
      endBit b (p ++ u) = endBit (endBit b p) u := by
    induction p generalizing b with
    | nil => rfl
    | cons a p ih => exact ih a
  have membership (n : ℕ) (b : Fin 2) (w : List (Fin 2)) :
      w ∈ legalWords n b ↔ w.length = n ∧ NoAdjacentOnes (b :: w) := by
    induction n generalizing b w with
    | zero => cases w <;> simp [legalWords,NoAdjacentOnes]
    | succ n ih =>
      cases w with
      | nil => simp [legalWords]
      | cons a w =>
        fin_cases a <;> fin_cases b <;>
          simp [legalWords,ih,NoAdjacentOnes,List.isChain_cons_cons]
  have nodup (n : ℕ) (b : Fin 2) : (legalWords n b).Nodup := by
    induction n generalizing b with
    | zero => simp [legalWords]
    | succ n ih =>
      simp only [legalWords]
      split
      · apply List.nodup_append.mpr
        refine ⟨(ih 0).map (by intro a b h; exact List.cons.inj h |>.2),
          (ih 1).map (by intro a b h; exact List.cons.inj h |>.2),?_⟩
        intro w hw0 v hw1 hwe
        obtain ⟨u,hu,he⟩ := List.mem_map.mp hw0
        obtain ⟨t,ht,he'⟩ := List.mem_map.mp hw1
        have := List.cons.inj (he.trans (hwe.trans he'.symm))
        norm_num at this
      · simpa using (ih 0).map (by intro a b h; exact List.cons.inj h |>.2)
  have weight_positive (b : Fin 2) : 1 ≤ endpointWeight b := by
    fin_cases b <;> simp [endpointWeight,φone.le,φ]
  have mass (n : ℕ) (b : Fin 2) :
      ((legalWords n b).map (fun w => endpointWeight (endBit b w))).sum =
        φ ^ n * endpointWeight b := by
    induction n generalizing b with
    | zero => simp [legalWords,endBit]
    | succ n ih =>
      have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
      rcases hb with rfl | rfl
      · change (((legalWords n 0).map (0 :: ·) ++ (legalWords n 1).map (1 :: ·)).map
          (fun w => endpointWeight (endBit 0 w))).sum = _
        simp only [List.map_append,List.map_map,List.sum_append,Function.comp_def,endBit]
        rw [ih 0,ih 1]
        simp only [endpointWeight,if_pos rfl,if_neg (by decide : (1 : Fin 2) ≠ 0)]
        change φ ^ n * φ + φ ^ n * 1 = φ ^ (n + 1) * φ
        rw [pow_succ]
        calc
          φ ^ n * φ + φ ^ n * 1 = φ ^ n * (φ + 1) := by ring
          _ = φ ^ n * φ ^ 2 := by rw [φsq]
          _ = φ ^ n * φ * φ := by ring
      · simp only [legalWords,if_neg (by decide : (1 : Fin 2) ≠ 0),List.append_nil]
        change (((legalWords n 0).map (0 :: ·)).map
          (fun w => endpointWeight (endBit 1 w))).sum = _
        simp only [List.map_map,Function.comp_def,endBit]
        rw [ih 0]
        simp only [endpointWeight,if_pos rfl,if_neg (by decide : (1 : Fin 2) ≠ 0)]
        change φ ^ n * φ = φ ^ (n + 1) * 1
        rw [pow_succ,mul_one]
  have b1_legal (b : Fin 2) : B1 ∈ legalWords 14 b := by
    rw [membership]
    fin_cases b <;> norm_num [B1,NoAdjacentOnes,List.isChain_cons_cons]
  have b1_last (b : Fin 2) : endBit b B1 = 0 := by rfl
  have block_mass (b : Fin 2) :
      (((legalWords 14 b).filter (· != B1)).map
        (fun w => endpointWeight (endBit b w))).sum ≤
      φ ^ 14 * (1 - (φ ^ 14)⁻¹) * endpointWeight b := by
    have total := mass 14 b
    have partition :
        ((legalWords 14 b).map (fun w => endpointWeight (endBit b w))).sum =
          (((legalWords 14 b).filter (· != B1)).map
            (fun w => endpointWeight (endBit b w))).sum + φ := by
      have part (l : List (List (Fin 2))) (hn : l.Nodup) (hm : B1 ∈ l) :
          (l.map (fun w => endpointWeight (endBit b w))).sum =
            ((l.filter (· != B1)).map (fun w => endpointWeight (endBit b w))).sum + φ := by
        induction l with
        | nil => simp at hm
        | cons p l ih =>
          obtain ⟨hp,hn⟩ := List.nodup_cons.mp hn
          by_cases he : p = B1
          · subst p
            have hf : l.filter (· != B1) = l := by
              apply List.filter_eq_self.mpr
              intro x hx
              simp only [bne_iff_ne]
              intro he
              subst x
              exact hp hx
            simp [hf,b1_last,endpointWeight,φ,add_comm]
          · have hm' : B1 ∈ l := by simpa [Ne.symm he] using hm
            simp [he,ih hn hm',add_assoc]
      exact part _ (nodup 14 b) (b1_legal b)
    have hp : φ ^ 14 ≠ 0 := ne_of_gt (pow_pos φpos _)
    have cancel : φ ^ 14 * (1 - (φ ^ 14)⁻¹) = φ ^ 14 - 1 := by
      field_simp
    rw [cancel]
    have wb : endpointWeight b ≤ φ := by
      fin_cases b <;> simp [endpointWeight,φ,φone.le]
    nlinarith [partition]
  let δ := 1 - (φ ^ 14)⁻¹
  let rate := φ ^ 14 * δ
  have δnonneg : 0 ≤ δ := by
    have hp : 1 ≤ φ ^ 14 := one_le_pow₀ φone.le
    have := inv_le_one_of_one_le₀ hp
    dsimp [δ]
    linarith
  have ratenonneg : 0 ≤ rate := mul_nonneg (pow_nonneg φpos.le _) δnonneg
  have flat_sum (l : List (List (Fin 2)))
      (F : List (Fin 2) → List (List (Fin 2))) (f : List (Fin 2) → ℝ) :
      ((l.flatMap F).map f).sum = (l.map (fun p => ((F p).map f).sum)).sum := by
    induction l with
    | nil => simp
    | cons p l ih => simp [ih]
  have block_bound (r k : ℕ) (b : Fin 2) :
      ((blockWords r k b).map (fun w => endpointWeight (endBit b w))).sum ≤
        φ ^ r * rate ^ k * endpointWeight b := by
    induction k generalizing b with
    | zero => simpa [blockWords] using (mass r b).le
    | succ k ih =>
      rw [blockWords,flat_sum]
      have component (p : List (Fin 2)) :
          (((blockWords r k (endBit b p)).map (p ++ ·)).map
            (fun w => endpointWeight (endBit b w))).sum ≤
          φ ^ r * rate ^ k * endpointWeight (endBit b p) := by
        simpa only [List.map_map,Function.comp_def,end_append] using ih (endBit b p)
      calc
        _ ≤ ((((legalWords 14 b).filter (· != B1))).map
          (fun p => φ ^ r * rate ^ k * endpointWeight (endBit b p))).sum :=
          List.sum_le_sum (fun p hp => component p)
        _ = φ ^ r * rate ^ k * ((((legalWords 14 b).filter (· != B1))).map
          (fun p => endpointWeight (endBit b p))).sum := List.sum_map_mul_left _ _ _
        _ ≤ φ ^ r * rate ^ k * (rate * endpointWeight b) :=
          mul_le_mul_of_nonneg_left (block_mass b)
            (mul_nonneg (pow_nonneg φpos.le _) (pow_nonneg ratenonneg _))
        _ = φ ^ r * rate ^ (k + 1) * endpointWeight b := by rw [pow_succ]; ring
  have continuation (b : Fin 2) (p u : List (Fin 2))
      (h : NoAdjacentOnes (b :: (p ++ u))) : NoAdjacentOnes (endBit b p :: u) := by
    induction p generalizing b with
    | nil => simpa [endBit] using h
    | cons a p ih =>
      exact ih a h.tail
  have covered (r k : ℕ) (b : Fin 2) (w : List (Fin 2))
      (hw : NoAdjacentOnes (b :: w)) (hl : w.length = r + 14 * k)
      (ha : ¬ B1 <:+: w) : w ∈ blockWords r k b := by
    induction k generalizing b w with
    | zero => apply (membership r b w).mpr; simpa using And.intro hl hw
    | succ k ih =>
      let p := w.take 14
      let u := w.drop 14
      have hpu : p ++ u = w := List.take_append_drop 14 w
      have hpL : p.length = 14 := by simp [p,hl]; omega
      have huL : u.length = r + 14 * k := by simp [u,hl]; omega
      have hp : NoAdjacentOnes (b :: p) := by
        have hh := hw
        rw [← hpu,← List.cons_append] at hh
        exact hh.left_of_append
      have hu : NoAdjacentOnes (endBit b p :: u) := by
        apply continuation
        simpa only [hpu] using hw
      have huavoid : ¬ B1 <:+: u := by
        intro h
        apply ha
        exact h.trans ⟨p,[],by simp [hpu]⟩
      have hpne : p ≠ B1 := by
        intro he
        apply ha
        exact ⟨[],u,by simp [← he,hpu]⟩
      simp only [blockWords,List.mem_flatMap]
      refine ⟨p,?_,?_⟩
      · simp only [List.mem_filter,bne_iff_ne]
        exact ⟨(membership 14 b p).mpr ⟨hpL,hp⟩,hpne⟩
      · exact List.mem_map.mpr ⟨u,ih _ _ hu huL huavoid,hpu⟩
  let r := H % 14
  let k := H / 14
  have hdiv : r + 14 * k = H := Nat.mod_add_div H 14
  let good := (legalWords H 0).filter (fun w => decide (¬ B1 <:+: w))
  have subset : good ⊆ blockWords r k 0 := by
    intro w hw
    obtain ⟨hm,ha⟩ := List.mem_filter.mp hw
    obtain ⟨hl,hlegal⟩ := (membership H 0 w).mp hm
    apply covered r k 0 w hlegal (hl.trans hdiv.symm)
    exact of_decide_eq_true ha
  have length_le : good.length ≤ (blockWords r k 0).length :=
    ((nodup H 0).filter _).length_le_of_subset subset
  have weight_le : ((blockWords r k 0).length : ℝ) ≤
      ((blockWords r k 0).map (fun w => endpointWeight (endBit 0 w))).sum := by
    have hh := List.sum_le_sum (l := blockWords r k 0)
      (f := fun _ => (1 : ℝ)) (g := fun w => endpointWeight (endBit 0 w))
      (fun w hw => weight_positive _)
    simpa using hh
  have power_identity : φ ^ r * rate ^ k * endpointWeight 0 = φ ^ (H + 1) * δ ^ k := by
    rw [show endpointWeight 0 = φ by simp [endpointWeight,φ]]
    rw [show rate ^ k = φ ^ (14 * k) * δ ^ k by simp [rate,mul_pow,pow_mul]]
    calc
      φ ^ r * (φ ^ (14 * k) * δ ^ k) * φ =
          (φ ^ r * φ ^ (14 * k) * φ) * δ ^ k := by ring
      _ = φ ^ (H + 1) * δ ^ k := by rw [← pow_add,hdiv,← pow_succ]
  calc
    (good.length : ℝ) ≤ (blockWords r k 0).length := by exact_mod_cast length_le
    _ ≤ _ := weight_le
    _ ≤ φ ^ r * rate ^ k * endpointWeight 0 := block_bound r k 0
    _ = _ := power_identity

#print axioms uniform_avoidance_count

end D5.S1.Digit.ZeckendorfAvoidanceCount
