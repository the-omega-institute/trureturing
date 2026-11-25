/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/OneUpdateHistoricalCalibration
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/OneUpdateHistoricalCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Sharp one-update historical calibration and freely renewed current terminal bits. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.OneUpdateHistoricalCalibration
open D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
open scoped BigOperators
open scoped BigOperators
abbrev Word := List Bool
inductive Reads (R : Type*)
  | done : R → Reads R
  | read : Word → Reads R → Reads R → Reads R
def Reads.run {R : Type*} (oracle : Word → Bool) : Reads R → R
  | .done r => r
  | .read w f t => if oracle w then t.run oracle else f.run oracle
def Reads.trace {R : Type*} (oracle : Word → Bool) : Reads R → List Word
  | .done _ => []
  | .read w f t => w :: (if oracle w then t.trace oracle else f.trace oracle)
abbrev OneUpdate (R : Type*) := Reads (Reads R)
def run {R : Type*} (pre post : Word → Bool) (P : OneUpdate R) : R :=
  (P.run pre).run post
def trace {R : Type*} (pre post : Word → Bool) (P : OneUpdate R) : List Word :=
  P.trace pre ++ (P.run pre).trace post

/-- Chronological paid actions distinguish the common update acknowledgement
from every literal Read occurrence. -/
inductive CalibrationAction
  | read : Word → CalibrationAction
  | completedUpdate : CalibrationAction
def updateCount {R : Type*} (pre post : Word → Bool) (P : OneUpdate R) : Nat :=
  let actions := (P.trace pre).map CalibrationAction.read ++
    .completedUpdate :: ((P.run pre).trace post).map CalibrationAction.read
  actions.countP fun a => match a with | .completedUpdate => true | .read _ => false
private theorem update_count_one {R : Type*} (pre post : Word → Bool) (P : OneUpdate R) :
    updateCount pre post P = 1 := by
  rw [updateCount]
  simp [List.countP_map, Function.comp_def]
def readQ (ws : List Word) : Nat := ws.length
def readW (ws : List Word) : Nat := (ws.map List.length).sum
def readM (ws : List Word) : Nat := ws.foldr (fun w m => max w.length m) 0
private theorem Reads.run_eq_of_trace_agree {R : Type*} (P : Reads R) (o o' : Word → Bool)
    (h : ∀ w ∈ P.trace o, o' w = o w) : P.run o' = P.run o := by
  induction P with
  | done r => rfl
  | read w f t ihf iht =>
    have hw := h w (by simp [Reads.trace])
    cases ho : o w with
    | false =>
      have ho' : o' w = false := hw.trans ho
      simpa [Reads.run, ho, ho'] using
        ihf (fun v hv => h v (by simpa [Reads.trace, ho] using List.mem_cons_of_mem w hv))
    | true =>
      have ho' : o' w = true := hw.trans ho
      simpa [Reads.run, ho, ho'] using
        iht (fun v hv => h v (by simpa [Reads.trace, ho] using List.mem_cons_of_mem w hv))
private theorem length_le_readM {w : Word} {ws : List Word} (h : w ∈ ws) : w.length ≤ readM ws := by
  induction ws with
  | nil => simp at h
  | cons v vs ih =>
    change w.length ≤ max v.length (readM vs)
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)
private theorem append_two_site_unique {p q : Word} {b c b' c' : Bool}
    (h : p ++ [b, c] = q ++ [b', c']) : p = q := by
  have hl : p.length = q.length := by
    have := congrArg List.length h
    simpa using this
  have ht := congrArg (List.take p.length) h
  simpa [hl] using ht
private theorem readW_sum_get (ws : List Word) :
    (∑ i : Fin ws.length, (ws.get i).length) = readW ws := by
  rw [← List.sum_ofFn]
  unfold readW
  congr 1
  simp
private theorem simultaneous_lower {X R : Type*} {sites : Finset Word}
    (pre : Word → Bool) (post : X → Word → Bool) (P : OneUpdate R)
    (correct : Function.Injective (fun x => run pre (post x) P))
    (flip : ∀ x (p : ↥sites), ∃ x', x' ≠ x ∧
      ∀ w, post x' w ≠ post x w → ∃ b c : Bool, w = p.val ++ [b, c])
    (x : X) :
    sites.card ≤ readQ (trace pre (post x) P) ∧
      (∑ p ∈ sites, (p.length + 2)) ≤ readW (trace pre (post x) P) ∧
      sites.sup (fun p => p.length + 2) ≤ readM (trace pre (post x) P) := by
  classical
  let ws := trace pre (post x) P
  have hit (p : ↥sites) :
      ∃ i : Fin ws.length, ∃ b c : Bool, ws.get i = p.val ++ [b,c] := by
    obtain ⟨x', hne, hloc⟩ := flip x p
    have hdiff : ∃ w ∈ (P.run pre).trace (post x), post x' w ≠ post x w := by
      by_contra h
      apply hne
      have hs := (P.run pre).run_eq_of_trace_agree (post x) (post x') (by
        intro w hw
        by_contra hn
        exact h ⟨w, hw, hn⟩)
      exact correct hs
    obtain ⟨w, hw, hne⟩ := hdiff
    obtain ⟨b,c,haddr⟩ := hloc w hne
    have hw' : w ∈ ws := List.mem_append_right _ hw
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hw'
    exact ⟨i,b,c,hi.trans haddr⟩
  choose i hi using hit
  have hinj : Function.Injective i := by
    intro p q h
    obtain ⟨b,c,hp⟩ := hi p
    obtain ⟨b',c',hq⟩ := hi q
    apply Subtype.ext
    exact append_two_site_unique (hp.symm.trans ((congrArg ws.get h).trans hq))
  have hlen (p : ↥sites) : (ws.get (i p)).length = p.val.length + 2 := by
    obtain ⟨b,c,hp⟩ := hi p
    rw [hp]
    simp
  refine ⟨?_, ?_, ?_⟩
  · simpa [readQ, ws] using Fintype.card_le_of_injective i hinj
  · let e : ↥sites ↪ Fin ws.length := ⟨i, hinj⟩
    calc
      _ = ∑ p : ↥sites, (p.val.length + 2) :=
        (Finset.sum_attach sites (fun p => p.length + 2)).symm
      _ = ∑ p : ↥sites, (ws.get (i p)).length :=
        Finset.sum_congr (s₁ := Finset.univ) rfl (fun p _ => (hlen p).symm)
      _ = ∑ j ∈ Finset.univ.map e, (ws.get j).length :=
        (Finset.sum_map (Finset.univ : Finset ↥sites) e (fun j => (ws.get j).length)).symm
      _ ≤ ∑ j : Fin ws.length, (ws.get j).length :=
        by
          rw [← Finset.sum_sdiff (Finset.subset_univ (Finset.univ.map e))]
          exact Nat.le_add_left _ _
      _ = _ := readW_sum_get ws
  · apply Finset.sup_le
    intro p hp
    rw [← hlen ⟨p,hp⟩]
    exact length_le_readM (List.get_mem _ _)
open D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
private def swapAt {A : Type} : Address → FreeMagma A → FreeMagma A
  | [], .mul l r => .mul r l
  | false :: p, .mul l r => .mul (swapAt p l) r
  | true :: p, .mul l r => .mul l (swapAt p r)
  | _, .of a => .of a
private theorem swapLeaf {A : Type} (p : Address) (a : A) :
    swapAt p (.of a) = .of a := by
  cases p with
  | nil => rfl
  | cons b p => cases b <;> rfl
private theorem swapStep {t w : Labelled} (h : Step t w) (p : Address) :
    Step (swapAt p t) (swapAt p w) := by
  induction h generalizing p with
  | alphaToBeta => simpa only [alpha, beta, swapLeaf] using Step.alphaToBeta
  | betaLeft =>
    cases p with
    | nil => exact .betaRight
    | cons b p => cases b <;> simpa only [swapAt, alpha, beta, swapLeaf] using Step.betaLeft
  | betaRight =>
    cases p with
    | nil => exact .betaLeft
    | cons b p => cases b <;> simpa only [swapAt, alpha, beta, swapLeaf] using Step.betaRight
  | branch hl hr il ir =>
    cases p with
    | nil => exact .branch hr hl
    | cons b p =>
      cases b
      · exact .branch (il p) hr
      · exact .branch hl (ir p)
private theorem swapAfter {n : Nat} {t : Labelled} (h : After n t) (p : Address) :
    After n (swapAt p t) := by
  induction h with
  | zero => simpa only [alpha, swapLeaf] using After.zero
  | next h st ih => exact .next ih (swapStep st p)
private theorem output_not_alpha {t w : Labelled} (h : Step t w) : w ≠ alpha := by
  intro he
  subst w
  cases h
private theorem input_for_beta {t : Labelled} (h : Step t beta) : t = alpha := by
  cases h
  rfl
private def NoAA (t : Labelled) : Prop :=
  ∀ p, atTree t p ≠ some (.mul alpha alpha)
private theorem leaf_noAA (b : Bool) : NoAA (.of b) := by
  intro p h
  cases p with
  | nil => cases h
  | cons b p => cases b <;> cases h
private theorem step_noAA {t w : Labelled} (h : Step t w) : NoAA w := by
  induction h with
  | alphaToBeta => exact leaf_noAA false
  | betaLeft =>
    intro p he
    cases p with
    | nil => cases he
    | cons b p =>
      cases b
      · exact leaf_noAA false p he
      · exact leaf_noAA true p he
  | betaRight =>
    intro p he
    cases p with
    | nil => cases he
    | cons b p =>
      cases b
      · exact leaf_noAA true p he
      · exact leaf_noAA false p he
  | branch hl hr il ir =>
    intro p he
    cases p with
    | nil => cases he; exact output_not_alpha hl rfl
    | cons b p =>
      cases b
      · exact il p he
      · exact ir p he
private theorem after_noAA {n : Nat} {t : Labelled} (h : After n t) : NoAA t := by
  cases h with
  | zero => exact leaf_noAA true
  | next _ st => exact step_noAA st
private theorem shape_cherry_mixed_step {t w : Labelled} (h : Step t w) (hn : NoAA t)
    (p : Address) (hc : atTree (shape w) p = some cherry) :
    atTree w p = some (.mul beta alpha) ∨ atTree w p = some (.mul alpha beta) := by
  induction h generalizing p with
  | alphaToBeta =>
    cases p with
    | nil => cases hc
    | cons b p => cases b <;> cases hc
  | betaLeft =>
    cases p with
    | nil => exact Or.inl rfl
    | cons b p =>
      cases b <;> cases p with
      | nil => cases hc
      | cons b p => cases b <;> cases hc
  | betaRight =>
    cases p with
    | nil => exact Or.inr rfl
    | cons b p =>
      cases b <;> cases p with
      | nil => cases hc
      | cons b p => cases b <;> cases hc
  | @branch l l' r r' hl hr il ir =>
    cases p with
    | nil =>
      cases l' with
      | mul a b => cases hc
      | of a =>
        cases r' with
        | mul b c => cases hc
        | of b =>
          cases a with
          | true => exact False.elim (output_not_alpha hl rfl)
          | false =>
            cases b with
            | true => exact False.elim (output_not_alpha hr rfl)
            | false =>
              have ha := input_for_beta hl
              have hb := input_for_beta hr
              subst l
              subst r
              exact False.elim (hn [] rfl)
    | cons b p =>
      cases b
      · exact il (fun q hq => hn (false :: q) hq) p hc
      · exact ir (fun q hq => hn (true :: q) hq) p hc
private theorem after_cherry_mixed {n : Nat} {t : Labelled} (h : After n t)
    (p : Address) (hc : atTree (shape t) p = some cherry) :
    atTree t p = some (.mul beta alpha) ∨ atTree t p = some (.mul alpha beta) := by
  cases h with
  | zero =>
    cases p with
    | nil => cases hc
    | cons b p => cases b <;> cases hc
  | next hp st => exact shape_cherry_mixed_step st (after_noAA hp) p hc
private theorem shape_swapAt_of_cherry {t : Labelled} {p : Address}
    (hc : atTree (shape t) p = some cherry) : shape (swapAt p t) = shape t := by
  induction p generalizing t with
  | nil =>
    cases t with
    | of a => cases hc
    | mul l r =>
      cases l with
      | mul a b => cases hc
      | of a =>
        cases r with
        | mul b c => cases hc
        | of b => rfl
  | cons bit p ih =>
    cases t with
    | of a => cases bit <;> cases hc
    | mul l r =>
      cases bit
      · exact congrArg (fun z => FreeMagma.mul z (shape r)) (ih hc)
      · exact congrArg (FreeMagma.mul (shape l)) (ih hc)
private theorem swapAt_ne_of_mixed {t : Labelled} {p : Address}
    (hc : atTree t p = some (.mul beta alpha) ∨ atTree t p = some (.mul alpha beta)) :
    swapAt p t ≠ t := by
  induction p generalizing t with
  | nil =>
    simp only [atTree] at hc
    rcases hc with h | h
    · have ht : t = .mul beta alpha := Option.some.inj h
      subst t
      decide
    · have ht : t = .mul alpha beta := Option.some.inj h
      subst t
      decide
  | cons bit p ih =>
    cases t with
    | of a =>
      cases bit <;> rcases hc with h | h <;> cases h
    | mul l r =>
      cases bit
      · have hne := ih (t := l) hc
        intro he
        change FreeMagma.mul (swapAt p l) r = FreeMagma.mul l r at he
        injection he with hh
        exact hne hh
      · have hne := ih (t := r) hc
        intro he
        change FreeMagma.mul l (swapAt p r) = FreeMagma.mul l r at he
        injection he with _ hh
        exact hne hh
private theorem swap_beta_away {t : Labelled} {p r : Address}
    (hc : atTree (shape t) p = some cherry) (haway : ∀ b : Bool, r ≠ p ++ [b]) :
    isBeta (swapAt p t) r = isBeta t r := by
  induction p generalizing t r with
  | nil =>
    cases t with
    | of a => cases hc
    | mul l rr =>
      cases l with
      | mul a b => cases hc
      | of a =>
        cases rr with
        | mul b c => cases hc
        | of b =>
          cases r with
          | nil => rfl
          | cons bit r =>
            cases r with
            | nil => exact False.elim (haway bit rfl)
            | cons bit' r => cases bit <;> cases bit' <;> rfl
  | cons bit p ih =>
    cases t with
    | of a => cases bit <;> cases hc
    | mul l rr =>
      cases r with
      | nil => cases bit <;> rfl
      | cons bit' r =>
        cases bit <;> cases bit'
        · exact ih hc (fun b he => haway b (congrArg (List.cons false) he))
        · rfl
        · rfl
        · exact ih hc (fun b he => haway b (congrArg (List.cons true) he))
private theorem one_changed_cherry (n : Nat) (s : Shape) (hn : 2 ≤ n)
    (hs : s ∈ rankedShapes n) (x : ↥(currentFiber n s)) (p : ↥(cherries s)) :
    ∃ x' : ↥(currentFiber n s), x' ≠ x ∧
      ∀ r : Address, nextPresence x'.val r ≠ nextPresence x.val r →
        ∃ b c : Bool, r = p.val ++ [b, c] := by
  have h := exact_known_seed_fibres n s hn hs
  have hx := (h.2.2.1 x.val).mp x.property
  have hc0 := (h.2.2.2.1 p.val).mp p.property
  have hc : atTree (shape x.val) p.val = some cherry := hx.2.symm ▸ hc0
  let y := swapAt p.val x.val
  have hy : y ∈ currentFiber n s :=
    (h.2.2.1 y).mpr ⟨swapAfter hx.1 _, (shape_swapAt_of_cherry hc).trans hx.2⟩
  refine ⟨⟨y, hy⟩, ?_, ?_⟩
  · intro hxy
    exact swapAt_ne_of_mixed (after_cherry_mixed hx.1 _ hc) (congrArg Subtype.val hxy)
  · intro r hr
    by_contra! hnone
    have law := h.2.2.2.2.2.2.2.2.2.2.1
    have betaEq (q : Address) (b : Bool) (hqb : r = q ++ [b]) :
        isBeta y q = isBeta x.val q := by
      apply swap_beta_away hc
      intro c hqc
      apply hnone c b
      rw [hqb, hqc, List.append_assoc]
      rfl
    apply hr
    apply Bool.eq_iff_iff.mpr
    rw [law y r hy, law x.val r x.property]
    apply or_congr_right
    constructor
    · rintro ⟨q, b, hb, hqb⟩
      exact ⟨q, b, (betaEq q b hqb).symm ▸ hb, hqb⟩
    · rintro ⟨q, b, hb, hqb⟩
      exact ⟨q, b, betaEq q b hqb ▸ hb, hqb⟩
open D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
private def betaPrefix (b : Bool) : Address ↪ Address :=
  ⟨List.cons b, fun _ _ h => (List.cons.inj h).2⟩
def freshBetaSites : Labelled → Finset Address
  | .of b => if b then ∅ else {[]}
  | .mul l r => (freshBetaSites l).map (betaPrefix false) ∪
      (freshBetaSites r).map (betaPrefix true)
private theorem mem_freshBetaSites (t : Labelled) (p : Address) :
    p ∈ freshBetaSites t ↔ isBeta t p = true := by
  have pref (b : Bool) (q : Address) : betaPrefix b q = b :: q := rfl
  induction t generalizing p with
  | of b =>
    cases p with
    | nil => cases b <;> decide
    | cons a p => cases b <;> cases a <;> simp [freshBetaSites, atTree, isBeta]
  | mul l r ihl ihr =>
    cases p with
    | nil => simp [freshBetaSites, atTree, isBeta, pref]
    | cons b p =>
      cases b
      · have hm : false :: p ∈ freshBetaSites (.mul l r) ↔ p ∈ freshBetaSites l := by
          simp [freshBetaSites, Finset.mem_map, pref]
        change false :: p ∈ freshBetaSites (.mul l r) ↔ isBeta l p = true
        exact hm.trans (ihl p)
      · have hm : true :: p ∈ freshBetaSites (.mul l r) ↔ p ∈ freshBetaSites r := by
          simp [freshBetaSites, Finset.mem_map, pref]
        change true :: p ∈ freshBetaSites (.mul l r) ↔ isBeta r p = true
        exact hm.trans (ihr p)
private theorem shape_branch (l r : Labelled) : shape (.mul l r) = .mul (shape l) (shape r) := rfl
private theorem same_shape_of_step {t w v : Labelled} (hw : Step t w) (hv : Step t v) :
    shape w = shape v := by
  induction hw generalizing v with
  | alphaToBeta => cases hv; rfl
  | betaLeft => cases hv <;> rfl
  | betaRight => cases hv <;> rfl
  | branch h₁ h₂ ih₁ ih₂ =>
    cases hv with
    | branch v₁ v₂ => simp only [shape_branch, ih₁ v₁, ih₂ v₂]
private theorem present_eq_of_shape_eq {t w : Labelled} (h : shape t = shape w) :
    present t = present w := by
  funext p
  have erase (u : Labelled) (q : Address) : present u q = present (shape u) q := by
    induction q generalizing u with
    | nil => simp [present, atTree]
    | cons b q ih =>
      cases u with
      | of x => cases b <;> rfl
      | mul l r => cases b
                   · exact ih l
                   · exact ih r
  rw [erase t, erase w, h]
private theorem input_alpha_of_output_tip {t w : Labelled} (hw : Step t w)
    (h : shape w = tip) : t = alpha := by
  cases hw with
  | alphaToBeta => rfl
  | betaLeft => contradiction
  | betaRight => contradiction
  | branch _ _ => cases h
private theorem beta_sites_eq_next_cherries {t w : Labelled}
    (ht : NoAA t) (hw : Step t w) : freshBetaSites t = cherries (shape w) := by
  induction hw with
  | alphaToBeta => rfl
  | betaLeft => decide
  | betaRight => decide
  | @branch l l' r r' hl hr il ir =>
    have hL : NoAA l := fun p => ht (false :: p)
    have hR : NoAA r := fun p => ht (true :: p)
    have he : ¬ (shape l' = tip ∧ shape r' = tip) := by
      rintro ⟨h₁, h₂⟩
      have lA := input_alpha_of_output_tip hl h₁
      have rA := input_alpha_of_output_tip hr h₂
      exact ht [] (by rw [lA, rA]; rfl)
    rw [freshBetaSites, shape_branch, cherries, ite_eq_right he, Finset.empty_union, il hL, ir hR]
    rfl
private theorem some_ranked_tree (n : ℕ) : (rankedTrees n).Nonempty := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨alpha, by decide⟩
  | one => exact ⟨beta, by decide⟩
  | more n ih₀ ih₁ =>
    obtain ⟨u, hu⟩ := ih₁
    obtain ⟨v, hv⟩ := ih₀
    refine ⟨.mul u v, ?_⟩
    rw [rankedTrees]
    apply Finset.mem_union_left
    exact Finset.mem_map.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩
private theorem attained_shape {n : ℕ} {t : Labelled} (hn : 2 ≤ n) (ht : After n t) :
    shape t ∈ rankedShapes n := by
  obtain ⟨u, hu⟩ := some_ranked_tree n
  have hS : shape u ∈ rankedShapes n := Finset.mem_image_of_mem shape hu
  exact ((exact_known_seed_fibres n _ hn hS).2.1 _).mpr ⟨t, ht, rfl⟩
private theorem same_predecessor_shape {n : ℕ} {t u w v : Labelled} (hn : 2 ≤ n)
    (ht : After n t) (hu : After n u) (hw : Step t w) (hv : Step u v)
    (h : shape w = shape v) : shape t = shape u := by
  cases n with
  | zero => omega
  | succ n =>
    cases ht with
    | next hp sp =>
      cases hu with
      | next hq sq =>
        have ep := (exact_local_two_step.1 _ _).mpr ⟨_, _, sp, hw, rfl⟩
        have eq := (exact_local_two_step.1 _ _).mpr ⟨_, _, sq, hv, h.symm⟩
        cases Option.some.inj (ep.symm.trans eq)
        exact same_shape_of_step sp sq
private theorem exact_successor_fibre {n : ℕ} {t w v : Labelled}
    (hn : 2 ≤ n) (ht : After n t) (hw : Step t w) :
    v ∈ currentFiber (n + 1) (shape w) ↔ Step t v := by
  have hW : After (n + 1) w := .next ht hw
  have hN : 2 ≤ n + 1 := by omega
  have hNew := (exact_known_seed_fibres _ _ hN (attained_shape hN hW)).2.2.1
  constructor
  · intro hv
    obtain ⟨hv, hEq⟩ := (hNew v).mp hv
    cases hv with
    | @next _ u _ hu hs =>
      have hEqOld := same_predecessor_shape hn ht hu hw hs hEq.symm
      have hOld := exact_known_seed_fibres _ _ hn (attained_shape hn ht)
      have mt := (hOld.2.2.1 t).mpr ⟨ht, rfl⟩
      have mu := (hOld.2.2.1 u).mpr ⟨hu, hEqOld.symm⟩
      have hI := hOld.2.2.2.2.2.2.2.2.2.2.2.2
      have hUpdate := hOld.2.2.2.2.2.2.2.2.2.1
      have hsF : nextPresence t = nextPresence u := by
        funext p
        rw [hUpdate t w p mt hw, hUpdate u v p mu hs, present_eq_of_shape_eq hEq]
      have hTU : t = u := congrArg Subtype.val (hI (a₁ := ⟨t, mt⟩) (a₂ := ⟨u, mu⟩) hsF)
      exact hTU ▸ hs
  · intro hv
    exact (hNew v).mpr ⟨.next ht hv, same_shape_of_step hv hw⟩
private theorem exact_fresh_residual {n : ℕ} {t w : Labelled}
    (hn : 2 ≤ n) (ht : After n t) (hw : Step t w) :
    (∀ v, v ∈ currentFiber (n + 1) (shape w) ↔ Step t v) ∧
    freshBetaSites t = cherries (shape w) ∧
    (freshBetaSites t).card = Nat.fib n ∧
    (currentFiber (n + 1) (shape w)).card = 2 ^ Nat.fib n ∧
    Function.Bijective (fun (u : ↥(currentFiber (n + 1) (shape w))) (p : ↥(freshBetaSites t)) =>
      terminalBit u.1 p.1) ∧
    (∀ v, Step t v → present v = present w) := by
  have hW : After (n + 1) w := .next ht hw
  have hN : 2 ≤ n + 1 := by omega
  have hNew := exact_known_seed_fibres _ _ hN (attained_shape hN hW)
  have he := beta_sites_eq_next_cherries (after_noAA ht) hw
  refine ⟨fun v => exact_successor_fibre hn ht hw, he, ?_, ?_, ?_,
    fun v hv => present_eq_of_shape_eq (same_shape_of_step hv hw)⟩
  · rw [he]
    exact hNew.2.2.2.2.2.1
  · exact hNew.2.2.2.2.2.2.1
  · rw [he]
    exact hNew.2.2.2.2.1
open D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers

/-- The local growth age starts at 0 on alpha and 1 on beta, and grows once
with every actual update, even where the physical height has not yet changed. -/
private def age : Labelled → Nat
  | .of b => if b then 0 else 1
  | .mul l r => max (age l) (age r) + 1
private theorem age_step {u v : Labelled} (h : Step u v) : age v = age u + 1 := by
  induction h with
  | alphaToBeta => rfl
  | betaLeft => rfl
  | betaRight => rfl
  | branch _ _ ih₁ ih₂ =>
    simp only [age, ih₁, ih₂]
    omega

/-- At a branch, true means the physical left child is semantic L.
Values away from branches are ignored. -/
def oldFrame : Labelled → Address → Bool
  | .of _, _ => false
  | .mul l r, [] => decide (age r < age l)
  | .mul l _, false :: p => oldFrame l p
  | .mul _ r, true :: p => oldFrame r p

/-- Keep an existing frame and use actual new beta placement only at a birth.
No value at a leaf supplies access to a label. This is historical service data
in the correctness relation, not an input to the calibration controller. -/
def frameUpdate (old new : Labelled) (frames : Address → Bool) (p : Address) : Bool :=
  match atTree old p, atTree new p with
  | some (.mul _ _), _ => frames p
  | some (.of false), some (.mul (.of leftLabel) _) => !leftLabel
  | _, _ => false

/-- Histories of hidden local correspondences along actual completed steps. -/
inductive FrameHistory : Nat → Labelled → (Address → Bool) → Prop
  | seed : FrameHistory 0 alpha (fun _ => false)
  | step {n : Nat} {t w : Labelled} {f : Address → Bool} : FrameHistory n t f → Step t w → FrameHistory (n+1) w (frameUpdate t w f)
private theorem frame_step {u v : Labelled} (h : Step u v) :
    frameUpdate u v (oldFrame u) = oldFrame v := by
  funext p
  induction h generalizing p with
  | alphaToBeta => cases p with
    | nil => rfl
    | cons b p => cases b <;> rfl
  | betaLeft => cases p with
    | nil => rfl
    | cons b p => cases b <;> cases p <;> rfl
  | betaRight => cases p with
    | nil => rfl
    | cons b p => cases b <;> cases p <;> rfl
  | branch hl hr ihl ihr =>
    cases p with
    | nil =>
      simp only [frameUpdate, atTree, oldFrame, age_step hl, age_step hr,
        Nat.add_lt_add_iff_right]
    | cons b p =>
      cases b
      · exact ihl p
      · exact ihr p
private theorem genuine_old_frame {n : Nat} {t : Labelled} {f : Address → Bool}
    (h : FrameHistory n t f) : f = oldFrame t := by
  induction h with
  | seed => rfl
  | step _ st ih => rw [ih, frame_step st]
private theorem frame_history_exists {n : Nat} {t : Labelled} (h : After n t) :
    FrameHistory n t (oldFrame t) := by
  induction h with
  | zero => exact .seed
  | next _ st ih =>
    exact frame_step st ▸ .step ih st

/-- Compose actual old local correspondences along the requested semantic word.
False represents L/a, true represents R/b. An invalid old word returns none. -/
def composeOldFrames (t : Labelled) (f : Address → Bool) : Address → Option Address
  | [] => some []
  | b :: p =>
    match t with
    | .of _ => none
    | .mul l r =>
      let q := if f [] then b else !b
      (composeOldFrames (if q then r else l) (fun a => f (q :: a)) p).map (q :: ·)

/-- The old semantic L/R adapter recovered from the full old labelled
physical tree, with no access to the hidden frame history. -/
def oldSemanticAdapter (t : Labelled) : Address → Option Address :=
  composeOldFrames t (oldFrame t)
private theorem exact_old_adapter {n : Nat} {t : Labelled} (h : After n t) :
    (∃ f, FrameHistory n t f) ∧
    ∀ f, FrameHistory n t f → oldSemanticAdapter t = composeOldFrames t f := by
  exact ⟨⟨_, frame_history_exists h⟩, fun f hf => by rw [genuine_old_frame hf]; rfl⟩
private def depth {A : Type} : FreeMagma A → Nat
  | .of _ => 0
  | .mul l r => max (depth l) (depth r) + 1
private theorem depth_shape (t : Labelled) : depth (shape t) = depth t := by
  induction t with
  | of b => rfl
  | mul l r hl hr =>
    change max (depth (shape l)) (depth (shape r)) + 1 = _
    rw [hl, hr]
    rfl
private theorem age_le_depth (t : Labelled) : age t ≤ depth t + 1 := by
  induction t with
  | of b => cases b <;> decide
  | mul l r hl hr =>
    simp only [age, depth]
    omega
private theorem depth_step {u v : Labelled} (h : Step u v) : depth v ≤ depth u + 1 := by
  induction h with
  | alphaToBeta => decide
  | betaLeft => decide
  | betaRight => decide
  | branch _ _ ih₁ ih₂ =>
    simp only [depth]
    omega
private theorem age_after {n : Nat} {t : Labelled} (h : After n t) : age t = n := by
  induction h with
  | zero => rfl
  | next _ st ih => rw [age_step st, ih]
private theorem oldest_leaf {n : Nat} {t : Labelled} (h : After (n+1) t) :
    age t = depth t + 1 := by
  induction n generalizing t with
  | zero =>
    cases h with
    | next h st => cases h; cases st; rfl
  | succ n ih =>
    cases h with
    | next hu st =>
      have hA := age_le_depth t
      have hD := depth_step st
      have hS := age_step st
      have hO := ih hu
      omega

/-- The old completed-update count can be recovered from the acquired shape
alone on the stated (post-seed) domain. -/
def calibrationHorizon (s : Shape) : Nat := depth s + 1
private theorem exact_calibration_horizon {n : Nat} {t : Labelled} (hn : 1 ≤ n) (h : After n t) :
    calibrationHorizon (shape t) = n := by
  cases n with
  | zero => omega
  | succ n =>
    unfold calibrationHorizon
    rw [depth_shape, ← oldest_leaf h, age_after h]
private def cherryList : Shape → List Address
  | .of _ => []
  | .mul l r => if l = tip ∧ r = tip then [[]]
    else (cherryList l).map (false :: ·) ++ (cherryList r).map (true :: ·)
private theorem mem_cherry_list (s : Shape) (p : Address) :
    p ∈ cherryList s ↔ atTree s p = some cherry := by
  induction s generalizing p with
  | of a =>
    cases a
    cases p with
    | nil => simp [cherryList, atTree, cherry, tip]
    | cons b p => cases b <;> simp [cherryList, atTree, cherry, tip]
  | mul l r ihl ihr =>
    by_cases hc : l = tip ∧ r = tip
    · rcases hc with ⟨rfl, rfl⟩
      cases p with
      | nil => simp [cherryList, atTree, cherry]
      | cons b p =>
        cases b <;> cases p <;> simp_all [cherryList, atTree]
    · cases p with
      | nil =>
        have h : ¬ FreeMagma.mul l r = cherry := by
          intro h
          cases h
          exact hc ⟨rfl,rfl⟩
        simpa [cherryList, hc, atTree, List.mem_map] using h
      | cons b p =>
        cases b
        · simpa [cherryList, hc, atTree, List.mem_map] using ihl p
        · simpa [cherryList, hc, atTree, List.mem_map] using ihr p
private theorem cherry_list_nodup (s : Shape) : (cherryList s).Nodup := by
  induction s with
  | of a => simp [cherryList]
  | mul l r ihl ihr =>
    by_cases hc : l = tip ∧ r = tip
    · simp [cherryList, hc]
    · simp only [cherryList, hc, ite_false, List.nodup_append]
      exact ⟨ihl.map (fun _ _ h => (List.cons.inj h).2),
        ihr.map (fun _ _ h => (List.cons.inj h).2), by
          intro p hp q hq h
          obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
          obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq
          simp at h⟩

/-- Traverse the acquired physical shape and read each literal paa once. -/
def calibrationAddresses (s : Shape) : List Address :=
  (cherryList s).map (· ++ [false, false])
private theorem paid_list_exact (s : Shape) :
    (calibrationAddresses s).Nodup ∧
    ∀ p, p ++ [false, false] ∈ calibrationAddresses s ↔ atTree s p = some cherry := by
  have injective : Function.Injective (fun p : Address => p ++ [false, false]) :=
    fun _ _ h => List.append_cancel_right h
  refine ⟨(cherry_list_nodup s).map injective, ?_⟩
  intro p
  rw [← mem_cherry_list, calibrationAddresses]
  exact ⟨fun h => by
    obtain ⟨q, hq, h⟩ := List.mem_map.mp h
    exact injective h ▸ hq, fun h => List.mem_map_of_mem h⟩
private theorem read_witness {w : Address} {ws : List Address} (h : w ∈ ws) :
    w.length ≤ readM ws := length_le_readM h
private theorem readM_le {ws : List Address} {m : Nat}
    (h : ∀ w ∈ ws, w.length ≤ m) : readM ws ≤ m := by
  induction ws with
  | nil => exact Nat.zero_le _
  | cons w ws ih =>
    exact max_le (h w (by simp)) (ih (fun p hp => h p (by simp [hp])))
private theorem calibration_prices (n : Nat) (s : Shape) (hn : 2 ≤ n)
    (hs : s ∈ rankedShapes n) :
    readQ (calibrationAddresses s) = (cherries s).card ∧
    readW (calibrationAddresses s) = ∑ p ∈ cherries s, (p.length + 2) ∧
    readM (calibrationAddresses s) = (cherries s).sup (fun p => p.length + 2) := by
  have hMem := (exact_known_seed_fibres n s hn hs).2.2.2.1
  have hset : (cherryList s).toFinset = cherries s := by
    ext p
    rw [List.mem_toFinset, mem_cherry_list, hMem]
  have hPerm : List.Perm (cherryList s) (cherries s).toList := by
    rw [← hset]
    exact (List.toFinset_toList (cherry_list_nodup s)).symm
  refine ⟨?_, ?_, le_antisymm ?_ ?_⟩
  · rw [readQ, calibrationAddresses, List.length_map, hPerm.length_eq, Finset.length_toList]
  · unfold readW calibrationAddresses
    rw [List.map_map]
    change ((cherryList s).map (fun p => (p ++ [false, false]).length)).sum = _
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    rw [(hPerm.map (fun p : Address => p.length + 2)).sum_eq, Finset.sum_map_toList]
  · apply readM_le
    intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    have hp' : p ∈ cherries s := by simpa [← hset] using hp
    simpa using (Finset.le_sup (f := fun p : Address => p.length + 2) hp')
  · apply Finset.sup_le
    intro p hp
    have hp' : p ∈ cherryList s := by simpa [← hset] using hp
    simpa [calibrationAddresses] using read_witness (List.mem_map_of_mem (f := fun q : Address => q ++ [false,false]) hp')

/-- A finite executable enumeration follows the actual one-round constructors.
It is used for offline decoding; no extra source observation is made. -/
private def updateVariants : Labelled → List Labelled
  | .of true => [beta]
  | .of false => [.mul beta alpha, .mul alpha beta]
  | .mul l r => (updateVariants l).flatMap (fun a => (updateVariants r).map (.mul a))
private theorem mem_update_variants (t u : Labelled) :
    u ∈ updateVariants t ↔ Step t u := by
  induction t generalizing u with
  | of v =>
    cases v
    · constructor
      · intro h
        simp [updateVariants] at h
        rcases h with rfl | rfl
        · exact .betaLeft
        · exact .betaRight
      · intro h
        cases h <;> simp [updateVariants, beta]
    · constructor
      · intro h
        simp [updateVariants] at h
        simpa [h, alpha] using Step.alphaToBeta
      · intro h
        cases h
        simp [updateVariants, beta]
  | mul l r ihl ihr =>
    simp only [updateVariants, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact .branch ((ihl a).mp ha) ((ihr b).mp hb)
    · intro h
      cases h with
      | branch hl hr => exact ⟨_, (ihl _).mpr hl, _, (ihr _).mpr hr, rfl⟩
private def historyCandidates : Nat → List Labelled
  | 0 => [alpha]
  | n+1 => (historyCandidates n).flatMap updateVariants
private theorem history_candidates_iff (n : Nat) (t : Labelled) :
    t ∈ historyCandidates n ↔ After n t := by
  induction n generalizing t with
  | zero =>
    constructor
    · intro h
      have h' : t = alpha := by simpa [historyCandidates] using h
      cases h'
      exact .zero
    · intro h
      cases h
      simp [historyCandidates]
  | succ n ih =>
    simp only [historyCandidates, List.mem_flatMap]
    constructor
    · rintro ⟨u, hu, ht⟩
      exact .next ((ih u).mp hu) ((mem_update_variants u t).mp ht)
    · intro h
      cases h with
      | next hu ht => exact ⟨_, (ih _).mpr hu, (mem_update_variants _ t).mpr ht⟩

/-- The finite reconstruction accepts both the acquired shape and the paid reply
list only. Its enumeration is offline local work, not a Read optimization. -/
def decodeCalibration (s : Shape) (replies : List Bool) :
    Option (Labelled × (Address → Option Address)) :=
  ((historyCandidates (calibrationHorizon s)).find? fun u =>
    decide (shape u = s ∧ (calibrationAddresses s).map (nextPresence u) = replies)).map
    (fun u => (u, oldSemanticAdapter u))

/-- Literal paid replies from the actual current register after the one update. -/
def calibrationReplies (s : Shape) (w : Labelled) : List Bool :=
  (calibrationAddresses s).map (present w)
private theorem restore_of_step {n : Nat} {s : Shape} {t w : Labelled}
    (hn : 2 ≤ n) (hs : s ∈ rankedShapes n) (hT : t ∈ currentFiber n s) (hw : Step t w) :
    decodeCalibration s (calibrationReplies s w) = some (t, oldSemanticAdapter t) := by
  have core := exact_known_seed_fibres n s hn hs
  obtain ⟨ht, htS⟩ := (core.2.2.1 t).mp hT
  have hH := exact_calibration_horizon (by omega) ht
  rw [htS] at hH
  have hupdate := core.2.2.2.2.2.2.2.2.2.1
  have hterminal := core.2.2.2.2.2.2.2.2.2.2.2.1
  have hbij := core.2.2.2.2.1
  unfold decodeCalibration
  rw [hH]
  let pred (u : Labelled) := decide
    (shape u = s ∧ (calibrationAddresses s).map (nextPresence u) = calibrationReplies s w)
  change ((historyCandidates n).find? pred).map _ = _
  have htP : pred t = true :=
    decide_eq_true ⟨htS, List.map_congr_left (fun p _ => hupdate t w p hT hw)⟩
  cases h : (historyCandidates n).find? pred with
  | none =>
    exact ((List.find?_eq_none.mp h) t ((history_candidates_iff n t).mpr ht) htP).elim
  | some u =>
    have huA := (history_candidates_iff n u).mp (List.mem_of_find?_eq_some h)
    have hp : pred u = true := List.find?_some h
    have huP := of_decide_eq_true hp
    have huT := (core.2.2.1 u).mpr ⟨huA, huP.1⟩
    have heq : (⟨u, huT⟩ : ↥(currentFiber n s)) = ⟨t, hT⟩ := by
      apply hbij.1
      funext p
      have hm : p.val ++ [false,false] ∈ calibrationAddresses s :=
        List.mem_map_of_mem (f := fun q => q ++ [false,false]) ((mem_cherry_list s p.val).mpr ((core.2.2.2.1 _).mp p.2))
      have he := (List.map_inj_left.mp huP.2) _ hm
      exact (hterminal ⟨u, huT⟩ p).symm.trans
        (he.trans ((hupdate t w _ hT hw).symm.trans (hterminal ⟨t, hT⟩ p)))
    have hEq := congrArg Subtype.val heq
    change u = t at hEq
    subst u
    rfl
private def Reads.map {A B : Type*} (f : A → B) : Reads A → Reads B
  | .done a => .done (f a)
  | .read p l r => .read p (l.map f) (r.map f)
private theorem Reads.run_map {A B : Type*} (f : A → B) (R : Reads A) (oracle : Address → Bool) :
    (R.map f).run oracle = f (R.run oracle) := by
  induction R with
  | done => rfl
  | read p l r hl hr => cases h : oracle p <;> simp [Reads.map, Reads.run, hl, hr, h]
private theorem Reads.trace_map {A B : Type*} (f : A → B) (R : Reads A) (oracle : Address → Bool) :
    (R.map f).trace oracle = R.trace oracle := by
  induction R with
  | done => rfl
  | read p l r hl hr => cases h : oracle p <;> simp [Reads.map, Reads.trace, hl, hr, h]
private def collect : List Address → Reads (List Bool)
  | [] => .done []
  | p :: ps => .read p ((collect ps).map (false :: ·)) ((collect ps).map (true :: ·))
private theorem collect_run (ps : List Address) (oracle : Address → Bool) :
    (collect ps).run oracle = ps.map oracle := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases h : oracle p <;> simp [collect, Reads.run, Reads.run_map, h, ih]
private theorem collect_trace (ps : List Address) (oracle : Address → Bool) :
    (collect ps).trace oracle = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases h : oracle p <;> simp [collect, Reads.trace, Reads.trace_map, h, ih]

/-- No pre-update reads: one common update acknowledgement, then each paid
absolute word once, with a finite offline decode of the reply vector. -/
def calibrationProgram (s : Shape) : OneUpdate (Option (Labelled × (Address → Option Address))) :=
  .done ((collect (calibrationAddresses s)).map (decodeCalibration s))
private theorem actual_calibration_run (s : Shape) (w : Labelled) :
    run (present s) (present w) (calibrationProgram s) = decodeCalibration s (calibrationReplies s w) ∧
    trace (present s) (present w) (calibrationProgram s) = calibrationAddresses s := by
  constructor
  · simp [run, calibrationProgram, Reads.run, Reads.run_map, collect_run, calibrationReplies]
  · simp [trace, calibrationProgram, Reads.run, Reads.trace, Reads.trace_map, collect_trace]
private theorem exists_update (t : Labelled) : ∃ w, Step t w := by
  induction t with
  | of b =>
    cases b
    · exact ⟨_, .betaLeft⟩
    · exact ⟨_, .alphaToBeta⟩
  | mul l r hl hr =>
    obtain ⟨v, hv⟩ := hl
    obtain ⟨w, hw⟩ := hr
    exact ⟨_, .branch hv hw⟩

/-- Exact one-update historical calibration and renewed current residual under
the installed paid presence-only interface. Equal public inputs fix the old
shape and the controller; branch selection sees only previous paid replies. -/
theorem exact_one_update_calibration (n : Nat) (s : Shape) (hn : 2 ≤ n)
    (hs : s ∈ rankedShapes n) (t w : Labelled) (ht : t ∈ currentFiber n s) (hw : Step t w) :
    (∀ p : Address, p ∈ cherries s → present w (p ++ [false, false]) = terminalBit t p) ∧
    run (present s) (present w) (calibrationProgram s) = some (t, oldSemanticAdapter t) ∧
    (∀ f, FrameHistory n t f → oldSemanticAdapter t = composeOldFrames t f) ∧
    trace (present s) (present w) (calibrationProgram s) = calibrationAddresses s ∧
    ((calibrationAddresses s).Nodup ∧
      ∀ p, p ++ [false, false] ∈ calibrationAddresses s ↔ p ∈ cherries s) ∧
    (let ws := trace (present s) (present w) (calibrationProgram s)
     updateCount (present s) (present w) (calibrationProgram s) = 1 ∧
     readQ ws = (cherries s).card ∧
     readW ws = ∑ p ∈ cherries s, (p.length + 2) ∧
     readM ws = (cherries s).sup (fun p => p.length + 2)) ∧
    (∀ P : OneUpdate Labelled,
      (∀ (x : ↥(currentFiber n s)) (v : Labelled), Step x.val v →
        run (present s) (present v) P = x.val) →
      let ws := trace (present s) (present w) P
      (cherries s).card ≤ readQ ws ∧
      (∑ p ∈ cherries s, (p.length + 2)) ≤ readW ws ∧
      (cherries s).sup (fun p => p.length + 2) ≤ readM ws) ∧
    (∀ v, v ∈ currentFiber (n + 1) (shape w) ↔ Step t v) ∧
    freshBetaSites t = cherries (shape w) ∧
    (freshBetaSites t).card = Nat.fib n ∧
    (currentFiber (n + 1) (shape w)).card = 2 ^ Nat.fib n ∧
    Function.Bijective (fun (u : ↥(currentFiber (n + 1) (shape w))) (p : ↥(freshBetaSites t)) =>
      terminalBit u.val p.val) ∧
    (∀ v, Step t v → present v = present w) := by
  have hCore := exact_known_seed_fibres n s hn hs
  have hT := ((hCore.2.2.1 t).mp ht).1
  have hUpdate := hCore.2.2.2.2.2.2.2.2.2.1
  have hTerminal := hCore.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hRun, hTrace⟩ := actual_calibration_run s w
  refine ⟨?_, hRun.trans (restore_of_step hn hs ht hw), (exact_old_adapter hT).2,
    hTrace, ?_, ?_, ?_, exact_fresh_residual hn hT hw⟩
  · intro p hp
    exact (hUpdate t w _ ht hw).symm.trans (hTerminal ⟨t, ht⟩ ⟨p, hp⟩)
  · obtain ⟨nd, he⟩ := paid_list_exact s
    exact ⟨nd, fun p => (he p).trans (hCore.2.2.2.1 p).symm⟩
  · dsimp only
    rw [hTrace]
    exact ⟨update_count_one _ _ _, calibration_prices n s hn hs⟩
  · intro P hP
    have hObserve (x : ↥(currentFiber n s)) (v : Labelled) (hv : Step x.val v) :
        nextPresence x.val = present v := funext fun p => hUpdate x.val v p x.2 hv
    show (cherries s).card ≤ readQ (trace (present s) (present w) P) ∧
      (∑ p ∈ cherries s, (p.length + 2)) ≤ readW (trace (present s) (present w) P) ∧
      (cherries s).sup (fun p => p.length + 2) ≤ readM (trace (present s) (present w) P)
    rw [← hObserve ⟨t, ht⟩ w hw]
    apply simultaneous_lower (sites := cherries s) (present s)
      (fun x : ↥(currentFiber n s) => nextPresence x.val) P _ (one_changed_cherry n s hn hs) ⟨t, ht⟩
    have hR (x : ↥(currentFiber n s)) :
        run (present s) (nextPresence x.val) P = x.val := by
      obtain ⟨v, hv⟩ := exists_update x.val
      rw [hObserve x v hv]
      exact hP x v hv
    intro x y e
    exact Subtype.ext ((hR x).symm.trans (e.trans (hR y)))
#print axioms exact_one_update_calibration
end D5.S3.Arith.FibonacciAtomic.LocalWiring.OneUpdateHistoricalCalibration
