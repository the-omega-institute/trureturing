/- GID: D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ReflectionDiagonalParityCounting
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Birth outputs span even wire labels and force compensating odd output updates. -/

import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-! Counting parity-network outputs, births, and returns. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting

private def parity {m : ℕ} (v : Fin m → Bool) : Bool := ∑ i, v i

private def update {m : ℕ} (ls : Fin m → Fin m → Bool) (p : Fin m × Fin m) :
    Fin m → Fin m → Bool := Function.update ls p.1 (ls p.1 + ls p.2)

def labels {m : ℕ} (gs : List (Fin m × Fin m)) (ls : Fin m → Fin m → Bool) :
    Fin m → Fin m → Bool := gs.foldl update ls

def outputs {m : ℕ} : List (Fin m × Fin m) → (Fin m → Fin m → Bool) → List (Fin m → Bool)
  | [], _ => []
  | p :: gs, ls => (ls p.1 + ls p.2) :: outputs gs (update ls p)

private def evenOutputs {m : ℕ} : List (Fin m × Fin m) →
    (Fin m → Fin m → Bool) → List (Fin m → Bool)
  | [], _ => []
  | p :: gs, ls =>
    if parity (ls p.1 + ls p.2) = false then
      (ls p.1 + ls p.2) :: evenOutputs gs (update ls p)
    else evenOutputs gs (update ls p)

private def births {m : ℕ} : List (Fin m × Fin m) →
    (Fin m → Fin m → Bool) → List (Fin m → Bool)
  | [], _ => []
  | p :: gs, ls =>
    if parity (ls p.1) = true ∧ parity (ls p.2) = true then
      (ls p.1 + ls p.2) :: births gs (update ls p)
    else births gs (update ls p)

private def returns {m : ℕ} : List (Fin m × Fin m) → (Fin m → Fin m → Bool) → ℕ
  | [], _ => 0
  | p :: gs, ls =>
    (if parity (ls p.1) = false ∧ parity (ls p.2) = true then 1 else 0) +
      returns gs (update ls p)

private def evenWires {m : ℕ} (ls : Fin m → Fin m → Bool) : ℕ :=
  ∑ j, if parity (ls j) = false then 1 else 0

private lemma parity_add {m : ℕ} (v w : Fin m → Bool) :
    parity (v + w) = parity v + parity w := Finset.sum_add_distrib

private lemma add_self_label {m : ℕ} (v : Fin m → Bool) : v + v = 0 := by
  funext i
  exact Bool.xor_self _

private lemma even_card (m : ℕ) (hm : 0 < m) :
    ((Finset.univ : Finset (Fin m → Bool)).filter (fun v => parity v = false)).card =
      2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let f : (Fin k → Bool) → {v : Fin (k + 1) → Bool // parity v = false} :=
    fun x => ⟨Fin.snoc x (parity x), by
      simp only [parity, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      exact Bool.xor_self _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have he := congrArg (fun z => Fin.init z.1) h
      simpa [f] using he
    · intro v
      refine ⟨Fin.init v.1, ?_⟩
      apply Subtype.ext
      have hv := v.2
      change (∑ i, v.1 i) = false at hv
      rw [Fin.sum_univ_castSucc] at hv
      have hlast : parity (Fin.init v.1) = v.1 (Fin.last k) := by
        change (∑ i : Fin k, v.1 i.castSucc) = _
        cases hs : ∑ i : Fin k, v.1 i.castSucc <;>
          cases hl : v.1 (Fin.last k) <;> simp_all [Bool.add_eq_xor]
      change Fin.snoc (Fin.init v.1) (parity (Fin.init v.1)) = v.1
      rw [hlast, Fin.snoc_init_self]
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa [Fintype.card_subtype, Fintype.card_fun] using hc.symm

private def listSpan {m : ℕ} : List (Fin m → Bool) → Finset (Fin m → Bool)
  | [] => {0}
  | v :: vs => listSpan vs ∪ (listSpan vs).image (fun w => v + w)

private lemma span_zero {m : ℕ} (vs : List (Fin m → Bool)) : 0 ∈ listSpan vs := by
  induction vs with
  | nil => simp [listSpan]
  | cons v vs ih => exact Finset.mem_union_left _ ih

private lemma span_add {m : ℕ} (vs : List (Fin m → Bool)) :
    ∀ a ∈ listSpan vs, ∀ b ∈ listSpan vs, a + b ∈ listSpan vs := by
  classical
  induction vs with
  | nil => simp [listSpan]
  | cons v vs ih =>
    intro a ha b hb
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact Finset.mem_union_left _ (ih a ha b hb)
    · obtain ⟨b1, hb1, hbeq⟩ := Finset.mem_image.mp hb
      subst b
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨a + b1, ih a ha b1 hb1, ?_⟩
      simp only [add_assoc, add_left_comm]
    · obtain ⟨a1, ha1, haeq⟩ := Finset.mem_image.mp ha
      subst a
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨a1 + b, ih a1 ha1 b hb, by simp only [add_assoc]⟩
    · obtain ⟨a1, ha1, haeq⟩ := Finset.mem_image.mp ha
      subst a
      obtain ⟨b1, hb1, hbeq⟩ := Finset.mem_image.mp hb
      subst b
      apply Finset.mem_union_left
      have he : (v + a1) + (v + b1) = a1 + b1 := by
        rw [add_add_add_comm, add_self_label, zero_add]
      rw [he]
      exact ih a1 ha1 b1 hb1

private lemma span_mem {m : ℕ} (vs : List (Fin m → Bool)) :
    ∀ v ∈ vs, v ∈ listSpan vs := by
  classical
  induction vs with
  | nil => simp
  | cons a vs ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨0, span_zero vs, add_zero _⟩
    · exact Finset.mem_union_left _ (ih v hv)

private lemma span_card {m : ℕ} (vs : List (Fin m → Bool)) :
    (listSpan vs).card ≤ 2 ^ vs.length := by
  classical
  induction vs with
  | nil => simp [listSpan]
  | cons v vs ih =>
    have hc := Finset.card_union_le (listSpan vs) ((listSpan vs).image (fun w => v + w))
    have hi := Finset.card_image_le (s := listSpan vs) (f := fun w => v + w)
    change (listSpan vs ∪ (listSpan vs).image (fun w => v + w)).card ≤ _
    rw [List.length_cons, pow_succ]
    omega

private lemma even_mem_outputs {m : ℕ} (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool) (v : Fin m → Bool) :
    v ∈ evenOutputs gs ls ↔ v ∈ outputs gs ls ∧ parity v = false := by
  induction gs generalizing ls with
  | nil => simp [evenOutputs, outputs]
  | cons p gs ih =>
    by_cases he : parity (ls p.1 + ls p.2) = false
    · simp only [evenOutputs, if_pos he, outputs, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hv, he⟩)
        · exact ⟨Or.inl rfl, he⟩
        · exact ⟨Or.inr hv, he⟩
      · rintro ⟨rfl | hv, hvp⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hv, hvp⟩
    · simp only [evenOutputs, if_neg he, outputs, List.mem_cons, ih]
      constructor
      · rintro ⟨hv, he⟩
        exact ⟨Or.inr hv, he⟩
      · rintro ⟨rfl | hv, hvp⟩
        · exact (he hvp).elim
        · exact ⟨hv, hvp⟩

private lemma even_output_count {m : ℕ} (hm : 0 < m)
    (gs : List (Fin m × Fin m)) (ls : Fin m → Fin m → Bool)
    (hseen : ∀ v, parity v = false → v ≠ 0 → v ∈ outputs gs ls) :
    2 ^ (m - 1) - 1 ≤ (evenOutputs gs ls).length := by
  classical
  let e := ((Finset.univ : Finset (Fin m → Bool)).filter (fun v => parity v = false)).erase 0
  have hecard : e.card = 2 ^ (m - 1) - 1 := by
    rw [Finset.card_erase_of_mem]
    · exact congrArg (fun a => a - 1) (even_card m hm)
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (∑ i : Fin m, (0 : Bool)) = 0
      exact Finset.sum_const_zero
  have hsub : e ⊆ (evenOutputs gs ls).toFinset := by
    intro v hv
    have hvp := Finset.mem_filter.mp (Finset.mem_erase.mp hv).2
    exact List.mem_toFinset.mpr ((even_mem_outputs gs ls v).mpr
      ⟨hseen v hvp.2 (Finset.mem_erase.mp hv).1, hvp.2⟩)
  rw [← hecard]
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _)

private lemma span_outputs {m : ℕ} (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool) (s : Finset (Fin m → Bool))
    (hadd : ∀ a ∈ s, ∀ b ∈ s, a + b ∈ s)
    (hinit : ∀ j, parity (ls j) = false → ls j ∈ s)
    (hb : ∀ v ∈ births gs ls, v ∈ s) :
    ∀ v ∈ outputs gs ls, parity v = false → v ∈ s := by
  classical
  induction gs generalizing ls with
  | nil => simp [outputs]
  | cons p gs ih =>
    have hout : parity (ls p.1 + ls p.2) = false → ls p.1 + ls p.2 ∈ s := by
      intro he
      rw [parity_add] at he
      cases ht : parity (ls p.1) <;> cases hc : parity (ls p.2)
      · exact hadd _ (hinit _ ht) _ (hinit _ hc)
      · simp [ht, hc, Bool.add_eq_xor] at he
      · simp [ht, hc, Bool.add_eq_xor] at he
      · apply hb
        simp [births, ht, hc]
    have hnext : ∀ j, parity (update ls p j) = false → update ls p j ∈ s := by
      intro j he
      by_cases hj : j = p.1
      · subst j
        simpa only [update, Function.update_self] using
          hout (by simpa only [update, Function.update_self] using he)
      · simpa [update, Function.update_of_ne hj] using
          hinit j (by simpa [update, Function.update_of_ne hj] using he)
    have hbt : ∀ v ∈ births gs (update ls p), v ∈ s := by
      intro v hv
      apply hb
      by_cases hh : parity (ls p.1) = true ∧ parity (ls p.2) = true <;>
        simp [births, hh, hv]
    intro v hv he
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hout he
    · exact ih (update ls p) hnext hbt v hv he

private lemma birth_count {m : ℕ} (hm : 0 < m)
    (gs : List (Fin m × Fin m)) (ls : Fin m → Fin m → Bool)
    (hstart : ∀ j, parity (ls j) = true)
    (hseen : ∀ v, parity v = false → v ≠ 0 → v ∈ outputs gs ls) :
    m - 1 ≤ (births gs ls).length := by
  classical
  let s := listSpan (births gs ls)
  have hsp := span_outputs gs ls s (span_add _) (by intro j he; simp [hstart j] at he)
    (span_mem _)
  have hsub : (Finset.univ.filter fun v : Fin m → Bool => parity v = false) ⊆ s := by
    intro v hv
    have he := (Finset.mem_filter.mp hv).2
    by_cases hz : v = 0
    · subst v
      exact span_zero _
    · exact hsp v (hseen v he hz) he
  have hp : 2 ^ (m - 1) ≤ 2 ^ (births gs ls).length := by
    rw [← even_card m hm]
    exact (Finset.card_le_card hsub).trans (span_card _)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hp

private lemma wire_update_count {m : ℕ} (ls : Fin m → Fin m → Bool) (p : Fin m × Fin m) :
    evenWires (update ls p) +
      (if parity (ls p.1) = false ∧ parity (ls p.2) = true then 1 else 0) =
    evenWires ls + (if parity (ls p.1) = true ∧ parity (ls p.2) = true then 1 else 0) := by
  classical
  have hrest : (∑ j ∈ Finset.univ.erase p.1,
      if parity (update ls p j) = false then 1 else 0) =
      ∑ j ∈ Finset.univ.erase p.1, if parity (ls j) = false then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [update, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  unfold evenWires
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p.1),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ p.1), hrest]
  simp only [update, Function.update_self, parity_add]
  cases ht : parity (ls p.1) <;> cases hc : parity (ls p.2) <;>
    simp [ht, hc, Bool.add_eq_xor]

private lemma return_balance {m : ℕ} (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool) :
    evenWires (labels gs ls) + returns gs ls = evenWires ls + (births gs ls).length := by
  induction gs generalizing ls with
  | nil => simp [labels, returns, births]
  | cons p gs ih =>
    have hi := ih (update ls p)
    have hs := wire_update_count ls p
    change evenWires (labels gs (update ls p)) +
      ((if _ then 1 else 0) + returns gs (update ls p)) =
      evenWires ls + (if _ then _ :: births gs (update ls p) else births gs (update ls p)).length
    by_cases hb : parity (ls p.1) = true ∧ parity (ls p.2) = true <;>
      by_cases hr : parity (ls p.1) = false ∧ parity (ls p.2) = true <;>
      simp [hb, hr] at hi hs ⊢ <;> omega

private lemma disjoint_counts {m : ℕ} (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool) :
    (evenOutputs gs ls).length + returns gs ls ≤ gs.length := by
  induction gs generalizing ls with
  | nil => simp [evenOutputs, returns]
  | cons p gs ih =>
    have hi := ih (update ls p)
    simp only [evenOutputs, returns, List.length_cons]
    cases ht : parity (ls p.1) <;> cases hc : parity (ls p.2) <;>
      simp [parity_add, ht, hc, Bool.add_eq_xor] <;> omega

theorem count_bound {m : ℕ} (hm : 0 < m) (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool)
    (hstart : ∀ j, (∑ i, ls j i) = true)
    (hend : ∀ j, (∑ i, labels gs ls j i) = true)
    (hseen : ∀ v : Fin m → Bool, (∑ i, v i) = false → v ≠ 0 → v ∈ outputs gs ls) :
    2 ^ (m - 1) + m - 2 ≤ gs.length := by
  have he := even_output_count hm gs ls hseen
  have hb := birth_count hm gs ls hstart hseen
  have hr := return_balance gs ls
  have hd := disjoint_counts gs ls
  have hs : evenWires ls = 0 := by simp [evenWires, parity, hstart]
  have ht : evenWires (labels gs ls) = 0 := by simp [evenWires, parity, hend]
  rw [hs, ht] at hr
  have hp : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
  omega

end D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting
