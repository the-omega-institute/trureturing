/- GID: D5/S3/Combinatorics/ArrowWilfFixedInsertion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfFixedInsertion
   mirror-E: none(waiver:fixed-point-insertion-bijection-for-foata-words)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: A fixed point of the Foata map can be deleted and uniquely reinserted by value order. -/

import D5.S3.Combinatorics.ArrowWilfCharacterization
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfFixedInsertion

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization

/-- Insert `f` immediately before the first entry not smaller than `f`, or at the end. -/
def fixedInsert (f : ℕ) : List ℕ → List ℕ
  | [] => [f]
  | a :: p => if f ≤ a then f :: a :: p else a :: fixedInsert f p

/-- Fixed-point insertion adds exactly its distinguished entry. -/
theorem fixedInsert_perm (f : ℕ) (p : List ℕ) : (fixedInsert f p).Perm (f :: p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      simp only [fixedInsert]
      split
      · rfl
      · exact ih.cons a |>.trans (.swap _ _ _)

/-- Erasing a newly inserted value recovers the original duplicate-free word. -/
theorem erase_fixedInsert {f : ℕ} {p : List ℕ} (hf : f ∉ p) :
    (fixedInsert f p).erase f = p := by
  induction p with
  | nil => simp [fixedInsert]
  | cons a p ih =>
      have hfa : f ≠ a := by grind
      have haf : a ≠ f := Ne.symm hfa
      have hfp : f ∉ p := by grind
      simp only [fixedInsert]
      split
      · simp [hfa, haf]
      · simp [hfa, haf, ih hfp]

/-- Inserting distinct fixed points is independent of insertion order. -/
theorem fixedInsert_comm {f g : ℕ} (hfg : f ≠ g) {p : List ℕ}
    (hf : f ∉ p) (hg : g ∉ p) :
    fixedInsert f (fixedInsert g p) = fixedInsert g (fixedInsert f p) := by
  induction p with
  | nil =>
      simp only [fixedInsert]
      by_cases h : f ≤ g
      · have hlt : f < g := by omega
        simp [h, Nat.not_le.mpr hlt]
      · have hlt : g < f := Nat.lt_of_not_ge h
        simp [h, hlt.le]
  | cons a p ih =>
      have haf : a ≠ f := by grind
      have hag : a ≠ g := by grind
      have hfp : f ∉ p := by grind
      have hgp : g ∉ p := by grind
      by_cases hfa : f ≤ a <;> by_cases hga : g ≤ a <;>
        by_cases hfg' : f ≤ g <;>
        simp [fixedInsert, hfa, hga, hfg', ih hfp hgp] <;> omega

/-- The recursive insertion position is exactly the singleton-block fixed-point condition. -/
theorem fixedInsert_erase_eq_iff_hat_fixed {p : List ℕ} (hp : p.Nodup) {f : ℕ}
    (hf : f ∈ p) : fixedInsert f (p.erase f) = p ↔ hat p f = f := by
  rw [hat_fixed_iff hp hf]
  induction p with
  | nil => simp at hf
  | cons a p ih =>
      have hp' := hp.of_cons
      have hfa : a ≠ f → f ∈ p := by grind
      by_cases haf : a = f
      · subst a
        have hfp : f ∉ p := hp.notMem
        rcases p with _ | ⟨b, p⟩
        · simp [fixedInsert, IsLtrMax]
        · have hfb_ne : f ≠ b := by grind
          have hbf_ne : b ≠ f := Ne.symm hfb_ne
          by_cases hfb : f ≤ b
          · have hfb' : f < b := by omega
            simp [fixedInsert, hfb, IsLtrMax, hfb']
          · have hbf : b < f := Nat.lt_of_not_ge hfb
            have hble : b ≤ f := hbf.le
            have hne : fixedInsert f (b :: p) ≠ f :: b :: p := by
              simp [fixedInsert, hfb, hbf_ne]
            simp [fixedInsert, hfb, hne, IsLtrMax, hbf, hble, hbf_ne]
      · have hmem : f ∈ p := hfa haf
        have herase : (a :: p).erase f = a :: p.erase f := by simp [haf]
        rw [herase]
        simp only [fixedInsert]
        by_cases haflt : a < f
        · have hidx : (a :: p).idxOf f = p.idxOf f + 1 := by simp [haf]
          have hget_succ : ∀ j, (a :: p).getD (j + 1) 0 = p.getD j 0 := by
            intro j
            simp [List.getD]
          have hltr : IsLtrMax (a :: p) (p.idxOf f + 1) ↔ IsLtrMax p (p.idxOf f) := by
            constructor
            · intro h j hj
              simpa [hget_succ] using h (j + 1) (by omega)
            · intro h j hj
              rcases j with _ | j
              · have hfi : p.getD (p.idxOf f) 0 = f := by
                  have hi := List.idxOf_lt_length_of_mem hmem
                  rw [List.getD_eq_getElem (l := p) 0 hi, List.getElem_idxOf hi]
                change a < p.getD (p.idxOf f) 0
                rw [hfi]
                exact haflt
              · simpa [hget_succ] using h j (by omega)
          have hnext :
              (p.idxOf f + 1 = p.length ∨ f < p.getD (p.idxOf f + 1) 0) ↔
                ((a :: p).idxOf f + 1 = (a :: p).length ∨
                  f < (a :: p).getD ((a :: p).idxOf f + 1) 0) := by
            simp [hidx, hget_succ, Nat.add_assoc]
          have hnle : ¬ f ≤ a := Nat.not_le.mpr haflt
          simp only [hnle, ↓reduceIte, List.cons.injEq, true_and]
          rw [ih hp' hmem]
          exact and_congr (by simpa [hidx] using hltr.symm) hnext
        · have hleft_false : ¬ IsLtrMax (a :: p) ((a :: p).idxOf f) := by
            intro h
            have hi : 0 < (a :: p).idxOf f := by simp [haf]
            have hfi : (a :: p).getD ((a :: p).idxOf f) 0 = f := by
              have hmem' : f ∈ a :: p := by simp [hmem]
              have hidxlt := List.idxOf_lt_length_of_mem hmem'
              rw [List.getD_eq_getElem (l := a :: p) 0 hidxlt, List.getElem_idxOf hidxlt]
            have := h 0 hi
            change a < (a :: p).getD ((a :: p).idxOf f) 0 at this
            rw [hfi] at this
            exact haflt this
          have hle : f ≤ a := Nat.le_of_not_gt haflt
          simp only [hle, ↓reduceIte]
          constructor
          · intro heq
            have hfa_eq : f = a := by injection heq
            exact (haf hfa_eq.symm).elim
          · intro hr
            exact (hleft_false hr.1).elim

/-- Recursive form of the singleton-block condition, convenient for insertion arguments. -/
def FixedSyntax (f : ℕ) : List ℕ → Prop
  | [] => False
  | [a] => a = f
  | a :: b :: p => if a = f then f < b else a < f ∧ FixedSyntax f (b :: p)

/-- The recursive singleton-block condition is the fixed-point condition for `hat`. -/
theorem fixedSyntax_iff_hat_fixed {p : List ℕ} (hp : p.Nodup) {f : ℕ} (hf : f ∈ p) :
    FixedSyntax f p ↔ hat p f = f := by
  have hsyntax : ∀ {q : List ℕ} (hq : q.Nodup) {g : ℕ} (hg : g ∈ q),
      fixedInsert g (q.erase g) = q ↔ FixedSyntax g q := by
    intro q
    induction q with
    | nil => intro hq g hg; simp at hg
    | cons a q ih =>
        intro hq g hg
        by_cases hag : a = g
        · subst a
          have hgq : g ∉ q := hq.notMem
          rcases q with _ | ⟨b, q⟩
          · simp [fixedInsert, FixedSyntax]
          · have hgb : g ≠ b := by grind
            by_cases hle : g ≤ b
            · have hlt : g < b := by omega
              simp [fixedInsert, FixedSyntax, hle, hlt]
            · have hbg : b < g := Nat.lt_of_not_ge hle
              have hbg_ne : b ≠ g := by omega
              have hble : b ≤ g := hbg.le
              simp [fixedInsert, FixedSyntax, hle, hbg, hble, hbg_ne]
        · have hmem : g ∈ q := by grind
          have hq' := hq.of_cons
          have herase : (a :: q).erase g = a :: q.erase g := by simp [hag]
          rw [herase]
          rcases q with _ | ⟨b, q⟩
          · simp at hmem
          · by_cases hlt : a < g
            · have hnle : ¬ g ≤ a := Nat.not_le.mpr hlt
              simp [fixedInsert, FixedSyntax, hag, hnle, hlt, ih hq' hmem]
            · have hle : g ≤ a := Nat.le_of_not_gt hlt
              simp only [fixedInsert, hle, ↓reduceIte, List.cons.injEq, FixedSyntax,
                if_neg hag]
              constructor
              · intro heq
                exact (hag heq.1.symm).elim
              · intro hs
                exact (hlt hs.1).elim
  rw [← hsyntax hp hf, fixedInsert_erase_eq_iff_hat_fixed hp hf]

/-- Inserting a new fixed point preserves all fixed-point decisions for old entries. -/
theorem hat_fixed_fixedInsert_iff {p : List ℕ} (hp : p.Nodup) {f g : ℕ}
    (hf : f ∉ p) (hg : g ∈ p) (hfg : f ≠ g) :
    hat (fixedInsert f p) g = g ↔ hat p g = g := by
  have hsyntax : ∀ {q : List ℕ} (hq : q.Nodup) {a b : ℕ}
      (ha : a ∉ q) (hb : b ∈ q) (hab : a ≠ b),
      FixedSyntax b (fixedInsert a q) ↔ FixedSyntax b q := by
    intro q
    induction q with
    | nil => intro hq a b ha hb hab; simp at hb
    | cons x q ih =>
        intro hq a b ha hb hab
        have hax : a ≠ x := by grind
        have hxa : x ≠ a := Ne.symm hax
        have haq : a ∉ q := by grind
        by_cases hxb : x = b
        · subst x
          have hbq : b ∉ q := hq.notMem
          have hba : b ≠ a := Ne.symm hab
          rcases q with _ | ⟨y, q⟩
          · by_cases hle : a ≤ b <;> simp [fixedInsert, FixedSyntax, hle] <;> omega
          · by_cases hle : a ≤ b <;> by_cases hay : a ≤ y <;>
              simp [fixedInsert, FixedSyntax, hle, hay, hab, hba, hbq] <;> omega
        · have hbq : b ∈ q := by grind
          have hbx : b ≠ x := Ne.symm hxb
          have syntax_cons_of_ne (z : ℕ) (hz : z ≠ b) (r : List ℕ) :
              FixedSyntax b (z :: r) ↔ z < b ∧ FixedSyntax b r := by
            rcases r with _ | ⟨y, r⟩ <;> simp [FixedSyntax, hz]
          by_cases hle : a ≤ x
          · have hins : fixedInsert a (x :: q) = a :: x :: q := by simp [fixedInsert, hle]
            rw [hins, syntax_cons_of_ne a hab, syntax_cons_of_ne x hxb]
            constructor
            · exact fun h => h.2
            · rintro ⟨hxb_lt, hs⟩
              exact ⟨by omega, hxb_lt, hs⟩
          · have hxa_lt : x < a := Nat.lt_of_not_ge hle
            have hins : fixedInsert a (x :: q) = x :: fixedInsert a q := by
              simp [fixedInsert, hle]
            rw [hins, syntax_cons_of_ne x hxb, ih hq.of_cons haq hbq hab]
            exact (syntax_cons_of_ne x hxb q).symm
  have hins_nodup : (fixedInsert f p).Nodup :=
    (fixedInsert_perm f p).nodup_iff.mpr (by simp [hp, hf])
  have hgins : g ∈ fixedInsert f p :=
    (fixedInsert_perm f p).mem_iff.mpr (by simp [hg])
  rw [← fixedSyntax_iff_hat_fixed hins_nodup hgins,
    ← fixedSyntax_iff_hat_fixed hp hg]
  exact hsyntax hp hf hg hfg

end D5.S3.Combinatorics.ArrowWilfFixedInsertion
