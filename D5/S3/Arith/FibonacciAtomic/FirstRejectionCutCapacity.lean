/- GID: D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual window profiles determine ordered and Boolean capacities for every cut. -/

import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
import D5.S3.ConceptDynamics.Communication.LanguagePostprocessingObstruction
import Mathlib.Tactic
import Mathlib.Data.List.ChainOfFn
set_option autoImplicit false
set_option maxRecDepth 4096
namespace D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
open LiteralWindowEnd (Window first last nonzero run endable execution)
open scoped BigOperators
abbrev Word (k : ℕ) := Fin (k + 1) → Window
abbrev Side (k : ℕ) (A : Finset (Fin (k + 1))) := {r // r ∈ A} → Window
abbrev Label (k : ℕ) := WithTop (Fin (k + 1))
def left {k : ℕ} (i : Fin k) : Fin (k + 1) := i.castSucc
def right {k : ℕ} (i : Fin k) : Fin (k + 1) := i.succ
def Cross {k : ℕ} (A : Finset (Fin (k + 1))) (i : Fin k) : Prop :=
  (left i ∈ A ∧ right i ∉ A) ∨ (left i ∉ A ∧ right i ∈ A)
def Internal {k : ℕ} (A : Finset (Fin (k + 1))) (i : Fin k) : Prop :=
  left i ∈ A ∧ right i ∈ A
def bad {k : ℕ} (w : Word k) (j : Fin (k + 1)) : Prop :=
  if h : j.val < k then last (w j) = true ∧
    first (w ⟨j.val+1, by omega⟩) = true else w j = .zero
noncomputable def task {k : ℕ} (w : Word k) : Label k := by
  classical
  exact Finset.univ.inf (fun j => if bad w j then (j : Label k) else ⊤)
def boolean {k : ℕ} (w : Word k) : Bool :=
  endable (run (some (false,false)) (List.ofFn w))
noncomputable def extend {k : ℕ} (A : Finset (Fin (k + 1))) (a : Side k A) : Word k :=
  fun r => if h : r ∈ A then a ⟨r,h⟩ else .middle
noncomputable def closed {k : ℕ} (A : Finset (Fin (k + 1))) (a : Side k A) : Label k :=
  task (extend A a)
noncomputable def port {k : ℕ} (A : Finset (Fin (k + 1))) (a : Side k A) (i : Fin k) : Bool :=
  if left i ∈ A then last (extend A a (left i)) else first (extend A a (right i))
noncomputable def code {k : ℕ} (A : Finset (Fin (k + 1))) (a : Side k A) :
    Label k × (Fin k → Bool) := by
  classical
  exact (closed A a, fun i => if Cross A i ∧ (left i : Label k) < closed A a then port A a i else false)
def Allowed {k : ℕ} (A : Finset (Fin (k + 1))) (t : Label k) : Prop :=
  t = ⊤ ∨ (∃ i : Fin k, Internal A i ∧ t = (left i : Label k)) ∨
    (Fin.last k ∈ A ∧ t = (Fin.last k : Label k))
def Active {k : ℕ} (A : Finset (Fin (k + 1))) (t : Label k) (i : Fin k) : Prop :=
  Cross A i ∧ (left i : Label k) < t ∧
    ¬ (t = (Fin.last k : Label k) ∧ right i = Fin.last k)
noncomputable def Profile (k : ℕ) (A : Finset (Fin (k + 1))) :=
  (t : {t : Label k // Allowed A t}) × ({i : Fin k // Active A t.val i} → Bool)
noncomputable def encode {k : ℕ} {A : Finset (Fin (k + 1))} (P : Profile k A) :
    Label k × (Fin k → Bool) := by
  classical
  exact (P.1.val, fun i => if h : Active A P.1.val i then P.2 ⟨i,h⟩ else false)
def codec (lo hi : Bool) : Window :=
  match lo, hi with
  | false, false => .middle
  | true, false => .low
  | false, true => .high
  | true, true => .ends
noncomputable def desired {k : ℕ} {A : Finset (Fin (k + 1))} (P : Profile k A) (i : Fin k) : Bool := by
  classical
  exact if Cross A i then (encode P).2 i else decide (P.1.val = (left i : Label k))
noncomputable def representative {k : ℕ} {A : Finset (Fin (k + 1))} (P : Profile k A) : Side k A := by
  classical
  exact fun r => if P.1.val = (Fin.last k : Label k) ∧ r.val = Fin.last k then .zero else
    codec (if h : 0 < r.val.val then desired P ⟨r.val.val-1, by omega⟩ else false)
      (if h : r.val.val < k then desired P ⟨r.val.val, h⟩ else false)
noncomputable def merge {k : ℕ} (A : Finset (Fin (k + 1))) (a : Side k A)
    (b : {r : Fin (k + 1) // r ∉ A} → Window) : Word k :=
  (Equiv.piEquivPiSubtypeProd (fun r => r ∈ A) (fun _ => Window)).symm (a,b)

noncomputable def crossings {k : ℕ} (A : Finset (Fin (k + 1))) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (Cross A)
noncomputable def internals {k : ℕ} (A : Finset (Fin (k + 1))) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (Internal A)
noncomputable def d {k : ℕ} (A : Finset (Fin (k + 1))) : ℕ := (crossings A).card
noncomputable def c {k : ℕ} (A : Finset (Fin (k + 1))) (j : Fin k) : ℕ :=
  ((crossings A).filter (fun i => i.val < j.val)).card
noncomputable def delta {k : ℕ} (A : Finset (Fin (k + 1))) : ℕ := by
  classical
  exact if h : 0 < k then if Fin.last k ∈ A ∧ left (⟨k-1,by omega⟩ : Fin k) ∉ A then 1 else 0 else 0
noncomputable def epsilon {k : ℕ} (A : Finset (Fin (k + 1))) : ℕ := by
  classical
  exact if Fin.last k ∈ A ∨ (internals A).Nonempty then 1 else 0
noncomputable def interval (k l r : ℕ) : Finset (Fin (k + 1)) := by
  classical
  exact Finset.univ.filter (fun i => l ≤ i.val ∧ i.val < r)
def x (k : ℕ) : Word k := fun r => if r.val = 0 then .high else if r.val = 1 then .low else .middle
def y (k : ℕ) : Word k := fun r => if r = Fin.last k then .zero else .middle

set_option maxHeartbeats 2000000 in
-- The representative, fiber, and endpoint arguments are elaborated in one proof.
/-- Every positive length and cut has the stated actual profile fibers and capacities. -/
theorem result (k : ℕ) (A : Finset (Fin (k + 1))) :
    (∀ P : Profile k A, code A (representative P) = encode P) ∧
    (∀ a : Side k A, ∃ P : Profile k A, code A a = encode P) ∧
    (∀ a a' : Side k A,
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response (fun _ : Fin (k + 1) => Window)
        task (fun r => r ∈ A) a =
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response (fun _ : Fin (k + 1) => Window)
        task (fun r => r ∈ A) a' ↔ code A a = code A a') ∧
    delta A ≤ d A ∧
    D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity (fun _ : Fin (k + 1) => Window)
      task (fun r => r ∈ A) = 2 ^ d A + (∑ j ∈ internals A, 2 ^ c A j) +
        (if Fin.last k ∈ A then 2 ^ (d A - delta A) else 0) ∧
    (∀ w : Word k, boolean w = decide (task w = ⊤)) ∧
    (∀ a : Side k A,
      (∀ b, boolean (merge A a b) = false) ↔ closed A a ≠ ⊤) ∧
    (∀ a a' : Side k A,
      (∀ b, boolean (merge A a b) = boolean (merge A a' b)) ↔
        (closed A a ≠ ⊤ ∧ closed A a' ≠ ⊤) ∨
        (closed A a = ⊤ ∧ closed A a' = ⊤ ∧ ∀ i, Cross A i → port A a i = port A a' i)) ∧
    D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity (fun _ : Fin (k + 1) => Window)
      boolean (fun r => r ∈ A) = 2 ^ d A + epsilon A ∧
    (A = ∅ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = 1) ∧
    (A = Finset.univ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = k + 2) ∧
    (∀ m : ℕ, 1 ≤ m → m < k + 1 → A = interval k 0 m →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = m+1) ∧
    (1 ≤ k → A = {Fin.last k} → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = 3) ∧
    (∀ l : ℕ, 0 < l → l < k → A = interval k l (k + 1) →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = 2*(k + 1-l)+2) ∧
    (∀ l r : ℕ, 0 < l → l < r → r < k + 1 → A = interval k l r →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = 2*(r-l)+2) ∧
    (A = {(0 : Fin (k + 1))} → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = 2) ∧
    (∀ i : Fin (k + 1), 0 < i.val → i.val < k → A = {i} →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = 4) ∧
    (∀ l r : ℕ, 0 < l → l+1 < r → r ≤ k + 1 → A = interval k l r →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = 2*(r-l)+2) ∧
    (k = 0 → (A = ∅ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = 1) ∧
      (A = Finset.univ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A) = 2)) ∧
    (1 ≤ k →
      List.ofFn (x k) = .high :: .low :: List.replicate (k-1) .middle ∧
      List.ofFn (y k) = List.replicate k .middle ++ [.zero] ∧
      boolean (x k) = false ∧ boolean (y k) = false ∧
      task (x k) = ((0 : Fin (k + 1)) : Label k) ∧
      task (y k) = (Fin.last k : Label k) ∧
      ¬ ∃ post : Bool → Label k, ∀ w : Word k, post (boolean w) = task w) := by
  classical
  have spec (w : Word k) (j : Fin (k + 1)) :
      task w ≤ (j : Label k) ↔ ∃ i, bad w i ∧ i ≤ j := by
    simp only [task, Finset.inf_le_iff (WithTop.coe_lt_top j), Finset.mem_univ, true_and]
    apply exists_congr
    intro i
    by_cases h : bad w i <;> simp [h]
  have hit (w : Word k) (j : Fin (k + 1)) (h : task w = (j : Label k)) : bad w j := by
    obtain ⟨i, hi, hij⟩ := (spec w j).mp (le_of_eq h)
    have hji : j ≤ i := by
      have hle := (spec w i).mpr ⟨i,hi,le_rfl⟩
      rw [h] at hle
      exact WithTop.coe_le_coe.mp hle
    have he : i = j := le_antisymm hij hji
    simpa [he] using hi
  have allowed_at (j : Fin (k + 1)) : Allowed A (j : Label k) ↔
      if h : j.val < k then Internal A ⟨j.val,h⟩ else j ∈ A := by
    constructor
    · intro h
      rcases h with h | ⟨i,hi,he⟩ | ⟨ha,he⟩
      · exact (WithTop.coe_ne_top h).elim
      · have e : j = left i := WithTop.coe_inj.mp he
        subst j
        simp only [left, Fin.val_castSucc, i.isLt, ↓reduceDIte]
        exact hi
      · have e : j = Fin.last k := WithTop.coe_inj.mp he
        subst j
        simpa using ha
    · split_ifs with h
      · intro hi
        exact Or.inr (Or.inl ⟨⟨j.val,h⟩,hi, by simp [left]⟩)
      · intro ha
        have e : j = Fin.last k := Fin.ext (by simp; omega)
        exact Or.inr (Or.inr ⟨by simpa [e] using ha, by simp [e]⟩)
  have realizable : ∀ P : Profile k A, code A (representative P) = encode P := by
    have codec_first (lo hi : Bool) : first (codec lo hi) = lo := by
      cases lo <;> cases hi <;> rfl
    have codec_last (lo hi : Bool) : last (codec lo hi) = hi := by
      cases lo <;> cases hi <;> rfl
    have codec_ne (lo hi : Bool) : codec lo hi ≠ .zero := by
      cases lo <;> cases hi <;> decide
    intro P
    have terminal_desired (i : Fin k)
        (ht : P.1.val = (Fin.last k : Label k)) (hr : right i = Fin.last k) :
        desired P i = false := by
      have hn : P.1.val ≠ (left i : Label k) := by
        rw [ht]
        simp only [ne_eq, WithTop.coe_inj, left, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
        omega
      by_cases hc : Cross A i
      · have hnact : ¬ Active A P.1.val i := by simp [Active,ht,hr]
        simp [desired,hc,encode,hnact]
      · simp [desired,hc,hn]
    have rep_first (i : Fin k) :
        first (extend A (representative P) (right i)) =
          if right i ∈ A then desired P i else false := by
      by_cases ha : right i ∈ A
      · simp only [extend, dif_pos ha, if_pos ha, representative]
        by_cases hz : P.1.val = (Fin.last k : Label k) ∧ right i = Fin.last k
        · rw [if_pos hz]
          simpa [first] using (terminal_desired i hz.1 hz.2).symm
        · rw [if_neg hz,codec_first]
          have hp : 0 < (right i).val := by simp [right]
          rw [dif_pos hp]
          congr 1 <;> apply Fin.ext <;> simp [right]
      · simp [extend,ha,first]
    have rep_last (i : Fin k) :
        last (extend A (representative P) (left i)) =
          if left i ∈ A then desired P i else false := by
      by_cases ha : left i ∈ A
      · have hn : left i ≠ Fin.last k := by
          simp only [left, ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]
          omega
        simp only [extend,dif_pos ha,if_pos ha,representative,hn,and_false,↓reduceIte]
        rw [codec_last]
        simp [left]
      · simp [extend,ha,last]
    have rep_terminal : extend A (representative P) (Fin.last k) = .zero ↔
        P.1.val = (Fin.last k : Label k) ∧ Fin.last k ∈ A := by
      by_cases ha : Fin.last k ∈ A
      · simp only [extend,dif_pos ha,representative,and_true,ha,eq_self_iff_true]
        by_cases ht : P.1.val = (Fin.last k : Label k)
        · simp [ht]
        · simp [codec_ne,ht]
      · simp [extend,ha]
    have rep_bad (j : Fin (k + 1)) : bad (extend A (representative P)) j ↔
        P.1.val = (j : Label k) := by
      by_cases hj : j.val < k
      · let i : Fin k := ⟨j.val,hj⟩
        have hl : left i = j := by rfl
        have hr : right i = ⟨j.val+1,by omega⟩ := by rfl
        rw [bad, dif_pos hj]
        change last (extend A (representative P) (left i)) = true ∧
          first (extend A (representative P) (right i)) = true ↔ P.1.val = (left i : Label k)
        rw [rep_last,rep_first]
        by_cases ha : left i ∈ A <;> by_cases hb : right i ∈ A
        · have hc : ¬ Cross A i := by simp [Cross,ha,hb]
          simp [ha,hb,desired,hc]
        all_goals
          have hn : P.1.val ≠ (j : Label k) := by
            intro he
            have hallowed := P.1.property
            rw [he] at hallowed
            have hint := (allowed_at j).mp hallowed
            simp only [hj,↓reduceDIte,Internal] at hint
            simp_all [i,hl]
          have hn' : P.1.val ≠ (left i : Label k) := by simpa only [hl] using hn
          simp [ha,hb,hn']
      · have he : j = Fin.last k := Fin.ext (by simp; omega)
        rw [bad,dif_neg hj,he,rep_terminal]
        constructor
        · exact And.left
        · intro ht
          have ha := P.1.property
          rw [ht] at ha
          have hh := (allowed_at (Fin.last k)).mp ha
          simpa using And.intro ht hh
    have ht : closed A (representative P) = P.1.val := by
      unfold closed
      apply le_antisymm
      · cases h : P.1.val with
        | none => exact le_top
        | some j =>
          apply (spec _ j).mpr
          exact ⟨j,(rep_bad j).mpr h,le_rfl⟩
      · unfold task
        apply Finset.le_inf_iff.mpr
        intro j _
        by_cases hb : bad (extend A (representative P)) j
        · simpa [hb] using le_of_eq ((rep_bad j).mp hb)
        · simp [hb]
    apply Prod.ext
    · exact ht
    · funext i
      simp only [code,ht,encode]
      by_cases hc : Cross A i ∧ (left i : Label k) < P.1.val
      · by_cases hz : P.1.val = (Fin.last k : Label k) ∧ right i = Fin.last k
        · have hdes := terminal_desired i hz.1 hz.2
          have hnact : ¬ Active A P.1.val i := by simp [Active,hz.1,hz.2]
          simp only [if_pos hc,dif_neg hnact]
          unfold port
          rw [rep_last,rep_first]
          simp [hdes]
        · have hact : Active A P.1.val i := ⟨hc.1,hc.2,hz⟩
          simp only [if_pos hc,dif_pos hact]
          unfold port
          rw [rep_last,rep_first]
          rcases hc.1 with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [ha,hb,desired,encode,hact,Cross]
      · have hnact : ¬ Active A P.1.val i := by
          exact fun h => hc ⟨h.1,h.2.1⟩
        simp [hc,hnact]
  have raw_profile (a : Side k A) : ∃ P : Profile k A, code A a = encode P := by
    have ha : Allowed A (closed A a) := by
      cases h : closed A a with
      | none => exact Or.inl rfl
      | some j =>
        apply (allowed_at j).mpr
        have hb : bad (extend A a) j := hit _ j h
        by_cases hj : j.val < k
        · simp only [hj,↓reduceDIte,Internal]
          have hh : j ∈ A ∧ (⟨j.val+1,by omega⟩ : Fin (k + 1)) ∈ A := by
            by_cases h1 : j ∈ A <;> by_cases h2 : (⟨j.val+1,by omega⟩ : Fin (k + 1)) ∈ A <;>
              simp_all [bad,extend,first,last]
          exact hh
        · simp only [hj,↓reduceDIte]
          by_cases h1 : j ∈ A
          · exact h1
          · simp [bad,hj,extend,h1] at hb
    let P : Profile k A := ⟨⟨closed A a,ha⟩,fun i => port A a i.val⟩
    refine ⟨P,Prod.ext rfl ?_⟩
    funext i
    by_cases hc : Cross A i ∧ (left i : Label k) < closed A a
    · by_cases hz : closed A a = (Fin.last k : Label k) ∧ right i = Fin.last k
      · have hb := hit (extend A a) (Fin.last k) hz.1
        have hzwin : extend A a (Fin.last k) = .zero := by simpa [bad] using hb
        have hl : left i ∉ A := by
          rcases hc.1 with ⟨hl,hr⟩ | ⟨hl,hr⟩
          · have hn : Fin.last k ∈ A := by
              by_cases h : Fin.last k ∈ A
              · exact h
              · simp [extend,h] at hzwin
            exact (hr (hz.2.symm ▸ hn)).elim
          · exact hl
        have hp : port A a i = false := by simp [port,hl,hz.2,hzwin,first]
        have hnact : ¬ Active A (closed A a) i := by simp [Active,hz.1,hz.2]
        simp [code,encode,P,hc,hnact,hp]
      · have hact : Active A (closed A a) i := ⟨hc.1,hc.2,hz⟩
        simp [code,encode,P,hc,hact]
    · have hnact : ¬ Active A (closed A a) i := fun h => hc ⟨h.1,h.2.1⟩
      simp [code,encode,P,hc,hnact]
  have encode_inj : Function.Injective (@encode k A) := by
    rintro ⟨⟨t,ht⟩,p⟩ ⟨⟨u,hu⟩,q⟩ he
    have htu : t = u := congrArg Prod.fst he
    subst u
    congr 1
    funext i
    have hb := congrFun (congrArg Prod.snd he) i.val
    simpa only [encode,dif_pos i.property] using hb
  have eq_diag (u v : Word k) (h : ∀ j : Fin (k + 1), (task u ≤ (j : Label k)) ↔ task v ≤ (j : Label k)) :
      task u = task v := by
    apply le_antisymm
    · cases hv : task v with
      | none => exact le_top
      | some j => exact (h j).mpr (le_of_eq hv)
    · cases hu : task u with
      | none => exact le_top
      | some j => exact (h j).mp (le_of_eq hu)
  let outside (b : {r : Fin (k + 1) // r ∉ A} → Window) : Word k :=
    fun r => if h : r ∉ A then b ⟨r,h⟩ else .middle
  let q (b : {r : Fin (k + 1) // r ∉ A} → Window) (i : Fin k) : Bool :=
    if left i ∈ A then first (outside b (right i)) else last (outside b (left i))
  have event (a : Side k A) (b : {r : Fin (k + 1) // r ∉ A} → Window) (j : Fin (k + 1)) :
      bad (merge A a b) j ↔ bad (extend A a) j ∨ bad (outside b) j ∨
        (if h : j.val < k then Cross A ⟨j.val,h⟩ ∧ port A a ⟨j.val,h⟩ = true ∧
          q b ⟨j.val,h⟩ = true else False) := by
    by_cases hj : j.val < k
    · let i : Fin k := ⟨j.val,hj⟩
      change (if _ : j.val < k then _ else _) ↔ _
      simp only [bad,dif_pos hj]
      change last (merge A a b (left i)) = true ∧ first (merge A a b (right i)) = true ↔
        (last (extend A a (left i)) = true ∧ first (extend A a (right i)) = true) ∨
        (last (outside b (left i)) = true ∧ first (outside b (right i)) = true) ∨
        (Cross A i ∧ port A a i = true ∧ q b i = true)
      by_cases ha : left i ∈ A <;> by_cases hb : right i ∈ A <;>
        simp [merge,Equiv.piEquivPiSubtypeProd,extend,outside,port,q,Cross,ha,hb,first,last] <;> tauto
    · simp only [bad,dif_neg hj]
      by_cases ha : j ∈ A <;>
        simp [merge,Equiv.piEquivPiSubtypeProd,extend,outside,ha]
  have decomp (a : Side k A) (b : {r : Fin (k + 1) // r ∉ A} → Window) (j : Fin (k + 1)) :
      task (merge A a b) ≤ (j : Label k) ↔
        closed A a ≤ (j : Label k) ∨ task (outside b) ≤ (j : Label k) ∨
          ∃ i : Fin k, Cross A i ∧ left i ≤ j ∧ port A a i = true ∧ q b i = true := by
    rw [spec]
    constructor
    · rintro ⟨r,hb,hr⟩
      rcases (event a b r).mp hb with h | h | h
      · exact Or.inl ((spec _ _).mpr ⟨r,h,hr⟩)
      · exact Or.inr (Or.inl ((spec _ _).mpr ⟨r,h,hr⟩))
      · split_ifs at h with hlt
        · exact Or.inr (Or.inr ⟨⟨r.val,hlt⟩,h.1,hr,h.2⟩)

    · rintro (h | h | ⟨i,hc,hij,hp,hq⟩)
      · obtain ⟨r,hb,hr⟩ := (spec _ _).mp h
        exact ⟨r,(event a b r).mpr (Or.inl hb),hr⟩
      · obtain ⟨r,hb,hr⟩ := (spec _ _).mp h
        exact ⟨r,(event a b r).mpr (Or.inr (Or.inl hb)),hr⟩
      · refine ⟨left i,(event a b (left i)).mpr (Or.inr (Or.inr ?_)),hij⟩
        simpa [left] using And.intro hc (And.intro hp hq)
  have neutral (a : Side k A) : merge A a (fun _ => .middle) = extend A a := by
    funext r
    simp [merge,Equiv.piEquivPiSubtypeProd,extend]
  let test (i : Fin k) : {r : Fin (k + 1) // r ∉ A} → Window :=
    fun r => if left i ∈ A then (if r.val = right i then .low else .middle)
      else if r.val = left i then .high else .middle
  have test_q (i j : Fin k) (hi : Cross A i) : q (test i) j =
      if i = j then true else false := by
    by_cases he : i = j
    · subst j
      rcases hi with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;>
        simp [q,outside,test,hl,hr,first,last]
    · have hleft : left j ≠ left i := by
        intro h
        exact he (Fin.ext (congrArg Fin.val h).symm)
      have hright : right j ≠ right i := by
        intro h
        apply he
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp only [right,Fin.val_succ] at hv
        omega
      rcases hi with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;>
        by_cases hja : left j ∈ A <;> by_cases hjr : right j ∈ A <;>
        simp [q,outside,test,hl,hja,hjr,he,hleft,hright] <;>
        (try split_ifs) <;> rfl
  have test_live (i : Fin k) (hi : Cross A i) : task (outside (test i)) = ⊤ := by
    rw [eq_top_iff,task,Finset.le_inf_iff]
    intro j _
    have hn : ¬ bad (outside (test i)) j := by
      by_cases hj : j.val < k
      · simp only [bad,dif_pos hj]
        rcases hi with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;>
          simp only [outside,test,hl,↓reduceIte] <;> split_ifs <;> simp [first,last]
      · simp only [bad,dif_neg hj]
        rcases hi with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;> simp only [outside,test,hl,↓reduceIte] <;> split_ifs <;> decide
    simp [hn]
  have test_read (a : Side k A) (i : Fin k) (hi : Cross A i)
      (hlt : (left i : Label k) < closed A a) :
      task (merge A a (test i)) ≤ (left i : Label k) ↔ port A a i = true := by
    rw [decomp,test_live i hi]
    simp only [not_le_of_gt hlt,WithTop.top_le_iff,WithTop.coe_ne_top,false_or]
    constructor
    · rintro ⟨j,hc,hji,hp,hq⟩
      rw [test_q i j hi] at hq
      by_cases he : i = j
      · simpa [he] using hp
      · simp [he] at hq
    · intro hp
      exact ⟨i,hi,le_rfl,hp,by simp [test_q i i hi]⟩
  have fibers : ∀ a a' : Side k A,
      (∀ b, task (merge A a b) = task (merge A a' b)) ↔ code A a = code A a' := by
    intro a a'
    constructor
    · intro he
      have ht : closed A a = closed A a' := by
        simpa only [neutral,closed] using he (fun _ => .middle)
      apply Prod.ext ht
      funext i
      by_cases hi : Cross A i ∧ (left i : Label k) < closed A a
      · have hi' : (left i : Label k) < closed A a' := by simpa [ht] using hi.2
        have hb : port A a i = true ↔ port A a' i = true := by
          rw [← test_read a i hi.1 hi.2, ← test_read a' i hi.1 hi',he]
        have hp : port A a i = port A a' i := Bool.eq_iff_iff.mpr hb
        simp [code,ht,hi,hp]
      · simp only [code,← ht,if_neg hi]
    · intro he b
      have ht : closed A a = closed A a' := congrArg Prod.fst he
      apply eq_diag
      intro j
      rw [decomp,decomp]
      by_cases hj : closed A a ≤ (j : Label k)
      · simp [hj,← ht]
      · have hlt : (j : Label k) < closed A a := lt_of_not_ge hj
        have hp (i : Fin k) (hc : Cross A i) (hij : left i ≤ j) : port A a i = port A a' i := by
          have hil : (left i : Label k) < closed A a := lt_of_le_of_lt (WithTop.coe_le_coe.mpr hij) hlt
          have hci : Cross A i ∧ (left i : Label k) < closed A a := ⟨hc,hil⟩
          have eq := congrFun (congrArg Prod.snd he) i
          simpa [code,← ht,hci] using eq
        simp only [hj,← ht,false_or]
        apply or_congr Iff.rfl
        apply exists_congr
        intro i
        by_cases hc : Cross A i <;> by_cases hij : left i ≤ j
        · rw [hp i hc hij]
        all_goals simp [hc,hij]
  have active_top : Nat.card {i : Fin k // Active A (⊤ : Label k) i} = d A := by
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype,Active,d,crossings]
  have active_seam (j : Fin k) : Nat.card {i : Fin k // Active A (left j : Label k) i} = c A j := by
    have hn : (left j : Label k) ≠ (Fin.last k : Label k) := by simp [left]
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
    unfold c crossings
    congr 1
    ext i
    simp [Active,hn,left,Fin.lt_def,-Fin.val_fin_lt,Finset.mem_filter,Finset.mem_univ]
  have active_terminal (ha : Fin.last k ∈ A) :
      Nat.card {i : Fin k // Active A (Fin.last k : Label k) i} = d A - delta A := by
    by_cases hk : 0 < k
    · let e : Fin k := ⟨k-1,by omega⟩
      have hr : right e = Fin.last k := Fin.ext (by simp [right,e]; omega)
      have hre (i : Fin k) : right i = Fin.last k ↔ i = e := by
        simp only [right,Fin.ext_iff,Fin.val_succ,Fin.val_last]
        dsimp [e]
        omega
      have hs : Finset.univ.filter (Active A (Fin.last k : Label k)) = (crossings A).erase e := by
        ext i
        simp [Active,crossings,hre,left,Fin.lt_def,-Fin.val_fin_lt,i.isLt,and_comm]
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype,hs]
      by_cases hl : left e ∈ A
      · have he : e ∉ crossings A := by simp [crossings,Cross,hl,hr,ha]
        simp [Finset.erase_eq_of_notMem he,d,delta,hk,ha,hl,e]
      · have he : e ∈ crossings A := by simp [crossings,Cross,hl,hr,ha]
        rw [Finset.card_erase_of_mem he]
        simp [d,delta,hk,ha,hl,e]
    · have he : k = 0 := by omega
      subst k
      simp [Nat.card_eq_fintype_card,Active,d,crossings,delta]
  have delta_le : delta A ≤ d A := by
    by_cases hk : 0 < k
    · by_cases h : Fin.last k ∈ A ∧ left (⟨k-1,by omega⟩ : Fin k) ∉ A
      · let e : Fin k := ⟨k-1,by omega⟩
        have hr : right e = Fin.last k := Fin.ext (by simp [right,e]; omega)
        have he : e ∈ crossings A := by simp [crossings,Cross,e,hr,h.1,h.2]
        have hp : 0 < (crossings A).card := Finset.card_pos.mpr ⟨e,he⟩
        simpa only [delta,dif_pos hk,if_pos h,d] using (Nat.succ_le_of_lt hp)
      · simp [delta,hk,h]
    · simp [delta,hk]
  have card_profile : Nat.card (Profile k A) = 2 ^ d A +
      (∑ j ∈ internals A, 2 ^ c A j) +
      (if Fin.last k ∈ A then 2 ^ (d A - delta A) else 0) := by
    letI : Fintype (Profile k A) := by unfold Profile; infer_instance
    have hsum : Nat.card (Profile k A) = ∑ t : Label k,
        if Allowed A t then 2 ^ Nat.card {i : Fin k // Active A t i} else 0 := by
      simp only [Nat.card_eq_fintype_card]
      unfold Profile
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fun,Fintype.card_bool]
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (p := Allowed A) (Finset.univ.filter (Allowed A))
        (by intro t; simp only [Finset.mem_filter,Finset.mem_univ,true_and])
        (fun t => 2 ^ Fintype.card {i : Fin k // Active A t i})).symm
    rw [hsum]
    let e : Option (Fin (k + 1)) ≃ Label k :=
      { toFun := fun t => match t with | none => ⊤ | some j => (j : Label k)
        invFun := fun t => match t with | none => none | some j => some j
        left_inv := by intro t; cases t <;> rfl
        right_inv := by intro t; cases t <;> rfl }
    let f : Label k → ℕ := fun t => if Allowed A t then 2 ^ Nat.card {i : Fin k // Active A t i} else 0
    change (∑ t : Label k, f t) = _
    rw [← Fintype.sum_equiv e (fun t => f (e t)) f (fun _ => rfl),Fintype.sum_option]
    change f ⊤ + (∑ j : Fin (k + 1), f (j : Label k)) = _
    rw [Fin.sum_univ_castSucc]
    dsimp only [f]
    have ht : Allowed A (⊤ : Label k) := Or.inl rfl
    have hlast : Allowed A (Fin.last k : Label k) ↔ Fin.last k ∈ A := by
      simpa using allowed_at (Fin.last k)
    have hseam (j : Fin k) : Allowed A (left j : Label k) ↔ Internal A j := by
      simpa [left] using allowed_at (left j)
    have hterm : (if Allowed A (Fin.last k : Label k) then
        2 ^ Nat.card {i : Fin k // Active A (Fin.last k : Label k) i} else 0) =
        (if Fin.last k ∈ A then 2 ^ (d A - delta A) else 0) := by
      by_cases ha : Fin.last k ∈ A
      · rw [hlast,if_pos ha,active_terminal ha,if_pos ha]
      · simp [hlast,ha]
    simp only [ht,if_pos,active_top,hterm]
    have hsumj : (∑ j : Fin k, if Allowed A (j.castSucc : Label k) then
        2 ^ Nat.card {i : Fin k // Active A (j.castSucc : Label k) i} else 0) =
        ∑ j ∈ internals A, 2 ^ c A j := by
      change (∑ j : Fin k, if Allowed A (left j : Label k) then
        2 ^ Nat.card {i : Fin k // Active A (left j : Label k) i} else 0) = _
      simp only [hseam,active_seam]
      rw [← Finset.sum_filter]
      rfl
    rw [hsumj]
    omega
  have response_apply {O : Type} (F : Word k → O) (a : Side k A)
      (b : {r : Fin (k + 1) // r ∉ A} → Window) :
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response (fun _ : Fin (k + 1) => Window)
        F (fun r => r ∈ A) a b = F (merge A a b) := by
    unfold D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response merge
    congr 1
    funext r
    by_cases ha : r ∈ A <;> simp [Equiv.piEquivPiSubtypeProd,ha]
  have response_eq (a a' : Side k A) :
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response (fun _ : Fin (k + 1) => Window)
        task (fun r => r ∈ A) a =
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response (fun _ : Fin (k + 1) => Window)
        task (fun r => r ∈ A) a' ↔ code A a = code A a' := by
    rw [funext_iff]
    simpa only [response_apply] using fibers a a'

  have capacity_exact :
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity (fun _ : Fin (k + 1) => Window)
        task (fun r => r ∈ A) = Nat.card (Profile k A) := by
    let resp := D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response
      (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A)
    let f (P : Profile k A) : Set.range resp := ⟨resp (representative P),⟨representative P,rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro P Q he
        have he' := congrArg Subtype.val he
        have hc := (response_eq (representative P) (representative Q)).mp he'
        rw [realizable,realizable] at hc
        exact encode_inj hc
      · rintro ⟨_,⟨a,rfl⟩⟩
        obtain ⟨P,hP⟩ := raw_profile a
        refine ⟨P,Subtype.ext ?_⟩
        apply (response_eq _ _).mpr
        rw [realizable]
        exact hP.symm
    exact Nat.card_congr (Equiv.ofBijective f hf).symm
  have projection : ∀ w : Word k, boolean w = decide (task w = ⊤) := by
    intro w
    classical
    have guard (s : Bool) (b : Window) (v : List Window) :
        D5.S3.Arith.ZeckendorfFutureKernel.legal s (LiteralWindowEnd.flatten (b :: v)) ↔
          ¬ (s = true ∧ first b = true) ∧
          D5.S3.Arith.ZeckendorfFutureKernel.legal (last b) (LiteralWindowEnd.flatten v) := by
      cases s <;> cases b <;>
        simp [LiteralWindowEnd.flatten,LiteralWindowEnd.bits,D5.S3.Arith.ZeckendorfFutureKernel.legal,first,last]
    have chain (v : List Window) (b : Window) (s : Bool) :
        D5.S3.Arith.ZeckendorfFutureKernel.legal s (LiteralWindowEnd.flatten (b :: v)) ↔
          ¬ (s = true ∧ first b = true) ∧
          (b :: v).IsChain (fun a b => ¬ (last a = true ∧ first b = true)) := by
      induction v generalizing b s with
      | nil => rw [guard]; simp [LiteralWindowEnd.flatten,D5.S3.Arith.ZeckendorfFutureKernel.legal]
      | cons c v ih =>
        rw [guard,ih, List.isChain_cons_cons]
    have leg : D5.S3.Arith.ZeckendorfFutureKernel.legal false (LiteralWindowEnd.flatten (List.ofFn w)) ↔
        ∀ i : Fin k, ¬ (last (w (left i)) = true ∧ first (w (right i)) = true) := by
      rw [List.ofFn_succ,chain]
      simp only [Bool.false_eq_true,false_and,not_false_eq_true,true_and]
      rw [← List.ofFn_succ, List.isChain_ofFn]
      constructor
      · intro h i
        exact h i.val (by omega)
      · intro h i hi
        exact h ⟨i,by omega⟩
    have fold_end : (List.ofFn w).foldl (fun _ b => nonzero b) false = nonzero (w (Fin.last k)) := by
      rw [List.ofFn_succ']
      simp [List.concat_eq_append,List.foldl_append]
    have no_bad : (∀ j, ¬ bad w j) ↔
        (∀ i : Fin k, ¬ (last (w (left i)) = true ∧ first (w (right i)) = true)) ∧
          w (Fin.last k) ≠ .zero := by
      rw [Fin.forall_fin_succ']
      have hs (i : Fin k) : ¬ bad w i.castSucc ↔
          ¬ (last (w (left i)) = true ∧ first (w (right i)) = true) := by
        simp only [bad,Fin.val_castSucc,i.isLt,↓reduceDIte]
        rfl
      simp_rw [hs]
      simp only [bad,Fin.val_last,lt_self_iff_false,↓reduceDIte]

    have top_task : task w = ⊤ ↔ ∀ j, ¬ bad w j := by
      rw [eq_top_iff,task,Finset.le_inf_iff]
      simp
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.decide_iff,top_task,no_bad,← leg]
    unfold boolean
    by_cases hl : D5.S3.Arith.ZeckendorfFutureKernel.legal false (LiteralWindowEnd.flatten (List.ofFn w))
    · rw [(execution false false (List.ofFn w)).1.mpr hl]
      change (List.ofFn w).foldl (fun _ b => nonzero b) false = true ↔ _
      rw [fold_end]
      simp only [hl,true_and,nonzero,bne_iff_ne,decide_eq_true_eq]
    · rw [(execution false false (List.ofFn w)).2.mpr hl]
      simp only [endable,Option.any_none,hl,false_and,Bool.false_eq_true,iff_false,not_false_eq_true]
  have task_le_closed (a : Side k A) (b : {r : Fin (k + 1) // r ∉ A} → Window) :
      task (merge A a b) ≤ closed A a := by
    cases h : closed A a with
    | none => exact le_top
    | some j => exact (decomp a b j).mpr (Or.inl (le_of_eq h))
  have closed_false (a : Side k A) (ha : closed A a ≠ ⊤)
      (b : {r : Fin (k + 1) // r ∉ A} → Window) : boolean (merge A a b) = false := by
    have hn : task (merge A a b) ≠ ⊤ := by
      intro ht
      have hle := task_le_closed a b
      rw [ht] at hle
      exact ha (top_le_iff.mp hle)
    rw [projection]
    simp [hn]
  have live_test (a : Side k A) (ha : closed A a = ⊤) (i : Fin k) (hi : Cross A i) :
      boolean (merge A a (test i)) = true ↔ port A a i = false := by
    rw [projection]
    simp only [Bool.decide_iff]
    constructor
    · intro ht
      by_cases hp : port A a i = true
      · have hle := (test_read a i hi (by rw [ha]; exact WithTop.coe_lt_top _)).mpr hp
        rw [ht] at hle
        simp at hle
      · exact Bool.eq_false_iff.mpr hp
    · intro hp
      cases ht : task (merge A a (test i)) with
      | none => rfl
      | some j =>
        have hle : task (merge A a (test i)) ≤ (j : Label k) := le_of_eq ht
        rw [decomp,ha,test_live i hi] at hle
        simp only [top_le_iff,WithTop.coe_ne_top,false_or] at hle
        obtain ⟨qj,hc,hqj,hp',hq⟩ := hle
        have he : i = qj := by
          by_cases he : i = qj
          · exact he
          · simp [test_q i qj hi,he] at hq
        subst qj
        simp [hp] at hp'
  have boolean_fibers (a a' : Side k A) :
      (∀ b, boolean (merge A a b) = boolean (merge A a' b)) ↔
        (closed A a ≠ ⊤ ∧ closed A a' ≠ ⊤) ∨
        (closed A a = ⊤ ∧ closed A a' = ⊤ ∧
          ∀ i, Cross A i → port A a i = port A a' i) := by
    constructor
    · intro he
      by_cases ha : closed A a = ⊤ <;> by_cases hb : closed A a' = ⊤
      · refine Or.inr ⟨ha,hb,?_⟩
        intro i hi
        have hp : port A a i = false ↔ port A a' i = false := by
          rw [← live_test a ha i hi, ← live_test a' hb i hi,he]
        cases hpa : port A a i <;> cases hpb : port A a' i <;>
          simp [hpa,hpb] at hp <;> rfl
      · have hn := he (fun _ => .middle)
        rw [closed_false a' hb,neutral,projection] at hn
        change decide (closed A a = ⊤) = false at hn
        simp [ha] at hn
      · have hn := he (fun _ => .middle)
        rw [closed_false a ha,neutral,projection] at hn
        change false = decide (closed A a' = ⊤) at hn
        simp [hb] at hn
      · exact Or.inl ⟨ha,hb⟩
    · rintro (⟨ha,hb⟩ | ⟨ha,hb,hp⟩) b
      · rw [closed_false a ha,closed_false a' hb]
      · have hc : code A a = code A a' := by
          apply Prod.ext (ha.trans hb.symm)
          funext i
          by_cases hi : Cross A i
          · simp only [code,ha,hb,WithTop.coe_lt_top,and_true,if_pos hi,hp i hi]
          · simp only [code,ha,hb,hi,false_and,if_false]
        rw [projection,projection,(fibers a a').mpr hc b]
  have zero_iff (a : Side k A) :
      (∀ b, boolean (merge A a b) = false) ↔ closed A a ≠ ⊤ := by
    constructor
    · intro h ha
      have hn := h (fun _ => .middle)
      rw [neutral,projection] at hn
      change decide (closed A a = ⊤) = false at hn
      simp [ha] at hn
    · exact closed_false a
  have closed_exists_iff : (∃ a : Side k A, closed A a ≠ ⊤) ↔
      Fin.last k ∈ A ∨ (internals A).Nonempty := by
    constructor
    · rintro ⟨a,ha⟩
      obtain ⟨P,hP⟩ := raw_profile a
      have ht : closed A a = P.1.val := congrArg Prod.fst hP
      rcases P.1.property with h | ⟨i,hi,he⟩ | ⟨h,he⟩
      · exact (ha (ht.trans h)).elim
      · exact Or.inr ⟨i,by simpa [internals] using hi⟩
      · exact Or.inl h
    · intro h
      have hex : ∃ P : Profile k A, P.1.val ≠ ⊤ := by
        rcases h with h | ⟨j,hj⟩
        · refine ⟨⟨⟨(Fin.last k : Label k),Or.inr (Or.inr ⟨h,rfl⟩)⟩,fun _ => false⟩,?_⟩
          exact WithTop.coe_ne_top
        · refine ⟨⟨⟨(left j : Label k),Or.inr (Or.inl ⟨j,by simpa [internals] using hj,rfl⟩)⟩,
            fun _ => false⟩,?_⟩
          exact WithTop.coe_ne_top
      obtain ⟨P,hP⟩ := hex
      refine ⟨representative P,?_⟩
      have ht : closed A (representative P) = P.1.val := congrArg Prod.fst (realizable P)
      exact fun h => hP (ht.symm.trans h)
  let Good := {i : Fin k // Cross A i} → Bool
  let live (p : Good) : Profile k A :=
    ⟨⟨⊤,Or.inl rfl⟩,fun i => p ⟨i.val,i.property.1⟩⟩
  have live_ports (p : Good) : closed A (representative (live p)) = ⊤ ∧
      ∀ i (hi : Cross A i), port A (representative (live p)) i = p ⟨i,hi⟩ := by
    have he := realizable (live p)
    have ht : closed A (representative (live p)) = ⊤ := congrArg Prod.fst he
    refine ⟨ht,?_⟩
    intro i hi
    have hp := congrFun (congrArg Prod.snd he) i
    have ha : Active A (⊤ : Label k) i := by simp [Active,hi]
    simpa only [code,encode,live,ht,WithTop.coe_lt_top,and_true,if_pos hi,dif_pos ha] using hp
  have bool_capacity :
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity (fun _ : Fin (k + 1) => Window)
        boolean (fun r => r ∈ A) = 2 ^ d A + epsilon A := by
    let ClosedType := {u : Unit // Fin.last k ∈ A ∨ (internals A).Nonempty}
    let Types := Good ⊕ ClosedType
    let resp := D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response
      (fun _ : Fin (k + 1) => Window) boolean (fun r => r ∈ A)
    have req (a a' : Side k A) : resp a = resp a' ↔
        (closed A a ≠ ⊤ ∧ closed A a' ≠ ⊤) ∨
        (closed A a = ⊤ ∧ closed A a' = ⊤ ∧ ∀ i, Cross A i → port A a i = port A a' i) := by
      rw [funext_iff]
      simpa only [resp,response_apply] using boolean_fibers a a'

    let pickClosed (u : ClosedType) : Side k A := Classical.choose (closed_exists_iff.mpr u.property)
    have pick_bad (u : ClosedType) : closed A (pickClosed u) ≠ ⊤ :=
      Classical.choose_spec (closed_exists_iff.mpr u.property)
    let assign : Types → Side k A := fun t =>
      match t with
      | .inl p => representative (live p)
      | .inr u => pickClosed u
    let f (t : Types) : Set.range resp := ⟨resp (assign t),⟨assign t,rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro u v he
        have hr := congrArg Subtype.val he
        have hh := (req (assign u) (assign v)).mp hr
        cases u with
        | inl p =>
          cases v with
          | inl q =>
            have hlp := live_ports p
            have hlq := live_ports q
            have hports : ∀ i, Cross A i → port A (representative (live p)) i =
                port A (representative (live q)) i := by simpa [assign,hlp.1,hlq.1] using hh
            congr 1
            funext i
            exact (hlp.2 i.val i.property).symm.trans ((hports i.val i.property).trans (hlq.2 i.val i.property))
          | inr u =>
            have hp := (live_ports p).1
            have hu := pick_bad u
            simp [assign,hp,hu] at hh
        | inr u =>
          cases v with
          | inl p =>
            have hp := (live_ports p).1
            have hu := pick_bad u
            simp [assign,hp,hu] at hh
          | inr v => congr 1; exact Subtype.ext (Subsingleton.elim _ _)
      · rintro ⟨_,⟨a,rfl⟩⟩
        by_cases ha : closed A a = ⊤
        · let p : Good := fun i => port A a i.val
          refine ⟨.inl p,Subtype.ext ((req _ _).mpr (Or.inr ⟨(live_ports p).1,ha,?_⟩))⟩
          intro i hi
          exact (live_ports p).2 i hi
        · have h := closed_exists_iff.mp ⟨a,ha⟩
          let u : ClosedType := ⟨(),h⟩
          exact ⟨.inr u,Subtype.ext ((req _ _).mpr (Or.inl ⟨pick_bad u,ha⟩))⟩
    have hc : Nat.card (Set.range resp) = Nat.card Types :=
      Nat.card_congr (Equiv.ofBijective f hf).symm
    change Nat.card (Set.range resp) = _
    rw [hc]
    have hgood : Nat.card Good = 2 ^ d A := by
      simp [Good,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_subtype,d,crossings]
    have hclosed : Nat.card ClosedType = epsilon A := by
      by_cases h : Fin.last k ∈ A ∨ (internals A).Nonempty <;>
        simp [ClosedType,Nat.card_eq_fintype_card,Fintype.card_subtype,epsilon,h]
    simpa only [Types,Nat.card_sum,hgood,hclosed]
  have interval_data (l r : ℕ) (hlr : l < r) (hr : r ≤ k + 1) :
      d (interval k l r) = (if l = 0 then 0 else 1) + (if r = k + 1 then 0 else 1) ∧
      (internals (interval k l r)).card = r-l-1 ∧
      (∀ j ∈ internals (interval k l r), c (interval k l r) j = if l = 0 then 0 else 1) ∧
      (Fin.last k ∈ interval k l r ↔ r = k + 1) ∧
      delta (interval k l r) = if 0 < l ∧ r = k + 1 ∧ r-l = 1 then 1 else 0 := by
    have cross_iff (i : Fin k) : Cross (interval k l r) i ↔
        (0 < l ∧ i.val+1 = l) ∨ (r < k + 1 ∧ i.val+1 = r) := by
      simp only [Cross,interval,Finset.mem_filter,Finset.mem_univ,true_and,left,right,
        Fin.val_castSucc,Fin.val_succ]
      omega
    have internal_iff (i : Fin k) : Internal (interval k l r) i ↔
        l ≤ i.val ∧ i.val+1 < r := by
      simp only [Internal,interval,Finset.mem_filter,Finset.mem_univ,true_and,left,right,
        Fin.val_castSucc,Fin.val_succ]
      omega
    have dc : d (interval k l r) = (if l = 0 then 0 else 1) + (if r = k + 1 then 0 else 1) := by
      unfold d
      by_cases hl : l = 0
      · by_cases hrt : r = k + 1
        · have he : crossings (interval k l r) = ∅ := by
            ext i
            simp only [crossings,Finset.mem_filter,Finset.mem_univ,true_and,cross_iff]
            simp [hl,hrt]
          rw [he]
          simp [hl,hrt]
        · let e : Fin k := ⟨r-1,by omega⟩
          have he : crossings (interval k l r) = {e} := by
            ext i
            simp only [crossings,Finset.mem_filter,Finset.mem_univ,true_and,cross_iff,
              Finset.mem_singleton,Fin.ext_iff]
            dsimp [e]
            omega
          rw [he]
          simp [hl,hrt]
      · let e : Fin k := ⟨l-1,by omega⟩
        by_cases hrt : r = k + 1
        · have he : crossings (interval k l r) = {e} := by
            ext i
            simp only [crossings,Finset.mem_filter,Finset.mem_univ,true_and,cross_iff,
              Finset.mem_singleton,Fin.ext_iff]
            dsimp [e]
            omega
          rw [he]
          simp [hl,hrt]
        · let f : Fin k := ⟨r-1,by omega⟩
          have hef : e ≠ f := by
            simp only [ne_eq,Fin.ext_iff]
            dsimp [e,f]
            omega
          have he : crossings (interval k l r) = {e,f} := by
            ext i
            simp only [crossings,Finset.mem_filter,Finset.mem_univ,true_and,cross_iff,
              Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff]
            dsimp [e,f]
            omega
          rw [he]
          simp [hl,hrt,hef]
    have jc : (internals (interval k l r)).card = r-l-1 := by
      let f : {i : Fin k // Internal (interval k l r) i} → Fin (r-l-1) :=
        fun i => ⟨i.val.val-l,by have hi := (internal_iff i.val).mp i.property; omega⟩
      have hf : Function.Bijective f := by
        constructor
        · intro a b h
          apply Subtype.ext
          apply Fin.ext
          have ha := (internal_iff a.val).mp a.property
          have hb := (internal_iff b.val).mp b.property
          have he := congrArg Fin.val h
          dsimp [f] at he
          omega
        · intro a
          have hbound := a.isLt
          let j : Fin k := ⟨a.val+l,by omega⟩
          have hj : Internal (interval k l r) j := (internal_iff j).mpr
            ⟨by dsimp [j]; omega,by dsimp [j]; omega⟩
          refine ⟨⟨j,hj⟩,?_⟩
          apply Fin.ext
          simp [f,j]
      have hc := Fintype.card_congr (Equiv.ofBijective f hf)
      simpa [Fintype.card_subtype,internals] using hc
    have pc (j : Fin k) (hj : j ∈ internals (interval k l r)) :
        c (interval k l r) j = if l = 0 then 0 else 1 := by
      have hint : l ≤ j.val ∧ j.val+1 < r :=
        (internal_iff j).mp (by simpa [internals] using hj)
      unfold c
      by_cases hl : l = 0
      · have he : (crossings (interval k l r)).filter (fun i => i.val < j.val) = ∅ := by
          ext i
          simp only [Finset.mem_filter,crossings,Finset.mem_univ,true_and,cross_iff,
            Finset.notMem_empty,iff_false]
          omega
        rw [he]
        simp [hl]
      · let e : Fin k := ⟨l-1,by omega⟩
        have he : (crossings (interval k l r)).filter (fun i => i.val < j.val) = {e} := by
          ext i
          simp only [Finset.mem_filter,crossings,Finset.mem_univ,true_and,cross_iff,
            Finset.mem_singleton,Fin.ext_iff]
          dsimp [e]
          omega
        rw [he]
        simp [hl]
    have terminal_iff : Fin.last k ∈ interval k l r ↔ r = k + 1 := by
      simp only [interval,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_last]
      omega
    have del : delta (interval k l r) = if 0 < l ∧ r = k + 1 ∧ r-l = 1 then 1 else 0 := by
      by_cases hk : 0 < k
      · simp only [delta,dif_pos hk,terminal_iff,interval,Finset.mem_filter,
          Finset.mem_univ,true_and,left,Fin.val_castSucc,Fin.val_last]
        congr 1
        apply propext
        omega
      · have hk0 : k = 0 := by omega
        have hl0 : l = 0 := by omega
        simp [delta,hk,hl0]
    exact ⟨dc,jc,pc,terminal_iff,del⟩
  have interval_formula (l r : ℕ) (hlr : l < r) (hr : r ≤ k + 1) :
      2 ^ d (interval k l r) + (∑ j ∈ internals (interval k l r),2 ^ c (interval k l r) j) +
        (if Fin.last k ∈ interval k l r then
          2 ^ (d (interval k l r) - delta (interval k l r)) else 0) =
      2 ^ ((if l = 0 then 0 else 1) + (if r = k + 1 then 0 else 1)) +
        (r-l-1) * 2 ^ (if l = 0 then 0 else 1) +
        (if r = k + 1 then 2 ^ (((if l = 0 then 0 else 1) + (if r = k + 1 then 0 else 1)) -
          (if 0 < l ∧ r = k + 1 ∧ r-l = 1 then 1 else 0)) else 0) := by
    obtain ⟨hd,hj,hc,ht,hdel⟩ := interval_data l r hlr hr
    simp only [hd,hdel,ht]
    congr 2
    calc
      (∑ j ∈ internals (interval k l r),2 ^ c (interval k l r) j) =
          ∑ _j ∈ internals (interval k l r), 2 ^ (if l = 0 then 0 else 1) :=
        Finset.sum_congr rfl (fun j hj => by rw [hc j hj])
      _ = _ := by simp [hj]
  let cap := D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
    (fun _ : Fin (k + 1) => Window) task (fun r => r ∈ A)
  have hcap : cap = 2 ^ d A + (∑ j ∈ internals A,2 ^ c A j) +
      (if Fin.last k ∈ A then 2 ^ (d A - delta A) else 0) := capacity_exact.trans card_profile
  have empty_cap (he : A = ∅) : cap = 1 := by
    have hc : crossings (∅ : Finset (Fin (k + 1))) = ∅ := by
      ext i
      simp [crossings,Cross]
    have hj : internals (∅ : Finset (Fin (k + 1))) = ∅ := by
      ext i
      simp [internals,Internal]
    rw [hcap,he,d,hc,hj]
    simp
  have full_cap (he : A = Finset.univ) : cap = k + 2 := by
    have hc : crossings (Finset.univ : Finset (Fin (k + 1))) = ∅ := by
      ext i
      simp [crossings,Cross]
    have hj : internals (Finset.univ : Finset (Fin (k + 1))) = Finset.univ := by
      ext i
      simp [internals,Internal]
    have hp (j : Fin k) : c (Finset.univ : Finset (Fin (k + 1))) j = 0 := by
      rw [c,hc]
      simp
    have hd : delta (Finset.univ : Finset (Fin (k + 1))) = 0 := by simp [delta]
    rw [hcap,he,d,hc,hj,hd]
    simp [hp]
    omega
  have int_cap (l r : ℕ) (hlr : l < r) (hr : r ≤ k + 1) (he : A = interval k l r) :
      cap = 2 ^ ((if l = 0 then 0 else 1) + (if r = k + 1 then 0 else 1)) +
        (r-l-1) * 2 ^ (if l = 0 then 0 else 1) +
        (if r = k + 1 then 2 ^ (((if l = 0 then 0 else 1) + (if r = k + 1 then 0 else 1)) -
          (if 0 < l ∧ r = k + 1 ∧ r-l = 1 then 1 else 0)) else 0) := by
    rw [hcap,he,interval_formula l r hlr hr]
  have prefix_cap (m : ℕ) (hm : 1 ≤ m) (hmn : m < k + 1) (he : A = interval k 0 m) : cap = m+1 := by
    have h := int_cap 0 m (by omega) (by omega) he
    have hn : m ≠ k + 1 := by omega
    simp [hn] at h
    omega
  have last_cap (hk : 1 ≤ k) (he : A = {Fin.last k}) : cap = 3 := by
    have hI : ({Fin.last k} : Finset (Fin (k + 1))) = interval k k (k + 1) := by
      ext i
      simp only [Finset.mem_singleton,interval,Finset.mem_filter,Finset.mem_univ,true_and,Fin.ext_iff,Fin.val_last]
      omega
    have h := int_cap k (k + 1) (by omega) le_rfl (he.trans hI)
    have hk0 : k ≠ 0 := by omega
    simp [hk0,show 0 < k by omega] at h
    exact h
  have nonprefix_cap (l r : ℕ) (hl : 0 < l) (hlr : l+1 < r) (hr : r ≤ k + 1)
      (he : A = interval k l r) : cap = 2*(r-l)+2 := by
    have h := int_cap l r (by omega) hr he
    have hl0 : l ≠ 0 := by omega
    have hdiff : r-l ≠ 1 := by omega
    by_cases hrt : r = k + 1
    · subst r
      simp [hl0,hdiff] at h
      omega
    · simp [hl0,hrt] at h
      omega
  have suffix_cap (l : ℕ) (hl : 0 < l) (hlk : l < k)
      (he : A = interval k l (k + 1)) : cap = 2*(k + 1-l)+2 :=
    nonprefix_cap l (k + 1) hl (by omega) le_rfl he
  have internal_cap (l r : ℕ) (hl : 0 < l) (hlr : l < r) (hr : r < k + 1)
      (he : A = interval k l r) : cap = 2*(r-l)+2 := by
    have h := int_cap l r hlr (by omega) he
    have hl0 : l ≠ 0 := by omega
    have hrt : r ≠ k + 1 := by omega
    simp [hl0,hrt] at h
    omega
  have first_cap (he : A = {(0 : Fin (k + 1))}) : cap = 2 := by
    by_cases hk : k = 0
    · have hfull : A = Finset.univ := by
        rw [he]
        ext i
        simp only [Finset.mem_singleton,Finset.mem_univ,iff_true,Fin.ext_iff,Fin.val_zero]
        have hi := i.isLt
        omega
      simpa [hk] using full_cap hfull
    · have hI : ({(0 : Fin (k + 1))} : Finset (Fin (k + 1))) = interval k 0 1 := by
        ext i
        simp only [Finset.mem_singleton,interval,Finset.mem_filter,Finset.mem_univ,true_and,Fin.ext_iff,Fin.val_zero]
        omega
      exact prefix_cap 1 le_rfl (by omega) (he.trans hI)
  have singleton_cap (i : Fin (k + 1)) (hi0 : 0 < i.val) (hik : i.val < k)
      (he : A = {i}) : cap = 4 := by
    have hI : ({i} : Finset (Fin (k + 1))) = interval k i.val (i.val+1) := by
      ext j
      simp only [Finset.mem_singleton,interval,Finset.mem_filter,Finset.mem_univ,true_and,Fin.ext_iff]
      omega
    have h := internal_cap i.val (i.val+1) hi0 (by omega) (by omega) (he.trans hI)
    simpa using h
  have n1_cap (hk : k = 0) : (A = ∅ → cap = 1) ∧ (A = Finset.univ → cap = 2) :=
    ⟨empty_cap, fun he => by simpa [hk] using full_cap he⟩
  have words (hk : 1 ≤ k) :
      List.ofFn (x k) = .high :: .low :: List.replicate (k-1) .middle ∧
      List.ofFn (y k) = List.replicate k .middle ++ [.zero] ∧
      boolean (x k) = false ∧ boolean (y k) = false ∧
      task (x k) = ((0 : Fin (k + 1)) : Label k) ∧
      task (y k) = (Fin.last k : Label k) ∧
      ¬ ∃ post : Bool → Label k, ∀ w : Word k, post (boolean w) = task w := by
    have hxlist : List.ofFn (x k) = .high :: .low :: List.replicate (k-1) .middle := by
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [List.ofFn_succ,List.ofFn_succ]
      have hconst : (fun i : Fin m => x (m+1) i.succ.succ) = fun _ => Window.middle := by
        funext i
        simp only [x,Fin.val_succ]
        split_ifs <;> (first | rfl | omega)
      change (.high :: .low :: List.ofFn (fun i : Fin m => x (m+1) i.succ.succ)) =
        .high :: .low :: List.replicate m .middle
      rw [hconst]
      simp [List.ofFn_const]
    have hylist : List.ofFn (y k) = List.replicate k .middle ++ [.zero] := by
      rw [List.ofFn_succ']
      simp [y,Fin.castSucc_ne_last,List.ofFn_const,List.concat_eq_append]
    have hx : task (x k) = ((0 : Fin (k + 1)) : Label k) := by
      apply le_antisymm
      · apply (spec _ _).mpr
        refine ⟨0,?_,le_rfl⟩
        simp [bad,x,show 0 < k by omega,first,last]
      · exact bot_le
    have ybad (j : Fin (k + 1)) : bad (y k) j ↔ j = Fin.last k := by
      by_cases hj : j.val < k
      · have hn : j ≠ Fin.last k := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
        simp [bad,hj,y,hn,last]
      · have he : j = Fin.last k := Fin.ext (by simp; omega)
        simp [bad,hj,he,y]
    have hy : task (y k) = (Fin.last k : Label k) := by
      apply le_antisymm
      · exact (spec _ _).mpr ⟨Fin.last k,(ybad _).mpr rfl,le_rfl⟩
      · unfold task
        apply Finset.le_inf_iff.mpr
        intro j _
        by_cases hj : j = Fin.last k
        · simp [ybad,hj]
        · simp [ybad,hj]
    have bx : boolean (x k) = false := by rw [projection,hx]; simp
    have by' : boolean (y k) = false := by rw [projection,hy]; simp
    have hxy : task (x k) ≠ task (y k) := by
      rw [hx,hy]
      simp only [ne_eq,WithTop.coe_inj,Fin.ext_iff,Fin.val_zero,Fin.val_last]
      omega
    have no_post : ¬ ∃ post : Bool → Label k, ∀ w : Word k, post (boolean w) = task w := by
      rintro ⟨post,hpost⟩
      have he := D5.S3.ConceptDynamics.Communication.LanguagePostprocessingObstruction.language_postprocessing_preserves_missing_distinction
        boolean task (x k) (y k) ⟨by rw [bx,by'],hxy⟩ post
      exact hxy (by simpa only [Function.comp_apply,hpost] using he)
    exact ⟨hxlist,hylist,bx,by',hx,hy,no_post⟩
  exact ⟨realizable,raw_profile,response_eq,delta_le,capacity_exact.trans card_profile,projection,
    zero_iff,boolean_fibers,bool_capacity,empty_cap,full_cap,prefix_cap,last_cap,suffix_cap,
    internal_cap,first_cap,singleton_cap,nonprefix_cap,n1_cap,words⟩

#print axioms result
end D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
