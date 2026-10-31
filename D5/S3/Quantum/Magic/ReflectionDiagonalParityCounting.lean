/- GID: D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ReflectionDiagonalParityCounting
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Birth outputs span even wire labels and force compensating odd output updates. -/

import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.BigOperators.Fin

/-! Counting parity-network outputs, births, and returns. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting

def update {m : ℕ} (ls : Fin m → Fin m → Bool) (p : Fin m × Fin m) :
    Fin m → Fin m → Bool := Function.update ls p.1 (ls p.1 + ls p.2)

def labels {m : ℕ} (gs : List (Fin m × Fin m)) (ls : Fin m → Fin m → Bool) :
    Fin m → Fin m → Bool := gs.foldl update ls

noncomputable def outputs {m : ℕ} :
    List (Fin m × Fin m) → (Fin m → Fin m → Bool) → List (Fin m → Bool) :=
  List.foldr (fun p next ls => (ls p.1 + ls p.2) :: next (update ls p)) (fun _ => [])

private def evenOutputs {m : ℕ} (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool) : List (Fin m → Bool) :=
  (outputs gs ls).filter (fun v => decide ((∑ i, v i) = false))

private noncomputable def births {m : ℕ} (gs : List (Fin m × Fin m)) :
    (Fin m → Fin m → Bool) → List (Fin m → Bool) :=
  gs.foldr (fun p next ls =>
    if (∑ i, ls p.1 i) = true ∧ (∑ i, ls p.2 i) = true then
      (ls p.1 + ls p.2) :: next (update ls p)
    else next (update ls p)) (fun _ => [])

private noncomputable def returns {m : ℕ} (gs : List (Fin m × Fin m)) :
    (Fin m → Fin m → Bool) → ℕ :=
  gs.foldr (fun p next ls =>
    (if (∑ i, ls p.1 i) = false ∧ (∑ i, ls p.2 i) = true then 1 else 0) +
      next (update ls p)) (fun _ => 0)

private def evenWires {m : ℕ} (ls : Fin m → Fin m → Bool) : ℕ :=
  ∑ j, if (∑ i, ls j i) = false then 1 else 0

private lemma even_card (m : ℕ) (hm : 0 < m) :
    ((Finset.univ : Finset (Fin m → Bool)).filter (fun v => (∑ i, v i) = false)).card =
      2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let f : (Fin k → Bool) → {v : Fin (k + 1) → Bool // (∑ i, v i) = false} :=
    fun x => ⟨Fin.snoc x (∑ i, x i), by
      simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
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
      have hlast : (∑ i, Fin.init v.1 i) = v.1 (Fin.last k) := by
        change (∑ i : Fin k, v.1 i.castSucc) = _
        exact (BooleanRing.add_eq_zero' _ _).mp hv
      change Fin.snoc (Fin.init v.1) (∑ i, Fin.init v.1 i) = v.1
      rw [hlast, Fin.snoc_init_self]
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa [Fintype.card_subtype, Fintype.card_fun] using hc.symm

private noncomputable def listSpan {m : ℕ} (vs : List (Fin m → Bool)) :
    Finset (Fin m → Bool) :=
  vs.foldr (fun v s => s ∪ s.image (fun w => v + w)) {0}

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
    change a ∈ listSpan vs ∪ (listSpan vs).image (fun w => v + w) at ha
    change b ∈ listSpan vs ∪ (listSpan vs).image (fun w => v + w) at hb
    change a + b ∈ listSpan vs ∪ (listSpan vs).image (fun w => v + w)
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact Finset.mem_union_left _ (ih a ha b hb)
    · obtain ⟨b1, hb1, hbeq⟩ := Finset.mem_image.mp hb
      subst b
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨a + b1, ih a ha b1 hb1, ?_⟩
      simp only [add_left_comm]
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
        rw [add_add_add_comm, (show v + v = 0 from funext fun i => Bool.xor_self (v i)), zero_add]
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

private lemma even_output_count {m : ℕ} (hm : 0 < m)
    (gs : List (Fin m × Fin m)) (ls : Fin m → Fin m → Bool)
    (hseen : ∀ v : Fin m → Bool, (∑ i, v i) = false → v ≠ 0 → v ∈ outputs gs ls) :
    2 ^ (m - 1) - 1 ≤ (evenOutputs gs ls).length := by
  classical
  let e := ((Finset.univ : Finset (Fin m → Bool)).filter (fun v => (∑ i, v i) = false)).erase 0
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
    apply List.mem_toFinset.mpr
    simpa only [evenOutputs, List.mem_filter, decide_eq_true_eq] using
      (show v ∈ outputs gs ls ∧ (∑ i, v i) = false from
        ⟨hseen v hvp.2 (Finset.mem_erase.mp hv).1, hvp.2⟩)
  rw [← hecard]
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _)

private lemma span_outputs {m : ℕ} (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool) (s : Finset (Fin m → Bool))
    (hadd : ∀ a ∈ s, ∀ b ∈ s, a + b ∈ s)
    (hinit : ∀ j, (∑ i, ls j i) = false → ls j ∈ s)
    (hb : ∀ v ∈ births gs ls, v ∈ s) :
    ∀ v ∈ outputs gs ls, (∑ i, v i) = false → v ∈ s := by
  classical
  induction gs generalizing ls with
  | nil => simp [outputs]
  | cons p gs ih =>
    have hout : (∑ i, (ls p.1 + ls p.2) i) = false → ls p.1 + ls p.2 ∈ s := by
      intro he
      simp only [Pi.add_apply, Finset.sum_add_distrib] at he
      cases ht : (∑ i, ls p.1 i) <;> cases hc : (∑ i, ls p.2 i)
      · exact hadd _ (hinit _ ht) _ (hinit _ hc)
      · simp [ht, hc, Bool.add_eq_xor] at he
      · simp [ht, hc, Bool.add_eq_xor] at he
      · apply hb
        simp [births, ht, hc]
    have hnext : ∀ j, (∑ i, update ls p j i) = false → update ls p j ∈ s := by
      intro j he
      by_cases hj : j = p.1
      · subst j
        simpa only [update.eq_1, Function.update_self] using
          hout (by simpa only [update.eq_1, Function.update_self] using he)
      · simpa [update.eq_1, Function.update_of_ne hj] using
          hinit j (by simpa [update.eq_1, Function.update_of_ne hj] using he)
    have hbt : ∀ v ∈ births gs (update ls p), v ∈ s := by
      intro v hv
      apply hb
      change v ∈ (if (∑ i, ls p.1 i) = true ∧ (∑ i, ls p.2 i) = true then
        (ls p.1 + ls p.2) :: births gs (update ls p) else births gs (update ls p))
      by_cases hh : (∑ i, ls p.1 i) = true ∧ (∑ i, ls p.2 i) = true
      · rw [ite_eq_left hh]
        exact List.mem_cons_of_mem _ hv
      · rw [ite_eq_right hh]
        exact hv
    intro v hv he
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hout he
    · exact ih (update ls p) hnext hbt v hv he

private lemma birth_count {m : ℕ} (hm : 0 < m)
    (gs : List (Fin m × Fin m)) (ls : Fin m → Fin m → Bool)
    (hstart : ∀ j, (∑ i, ls j i) = true)
    (hseen : ∀ v : Fin m → Bool, (∑ i, v i) = false → v ≠ 0 → v ∈ outputs gs ls) :
    m - 1 ≤ (births gs ls).length := by
  classical
  let s := listSpan (births gs ls)
  have hsp := span_outputs gs ls s (span_add _) (by intro j he; simp [hstart j] at he)
    (span_mem _)
  have hsub : (Finset.univ.filter fun v : Fin m → Bool => (∑ i, v i) = false) ⊆ s := by
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
      (if (∑ i, ls p.1 i) = false ∧ (∑ i, ls p.2 i) = true then 1 else 0) =
    evenWires ls + (if (∑ i, ls p.1 i) = true ∧ (∑ i, ls p.2 i) = true then 1 else 0) := by
  classical
  have hrest : (∑ j ∈ Finset.univ.erase p.1,
      if (∑ i, update ls p j i) = false then 1 else 0) =
      ∑ j ∈ Finset.univ.erase p.1, if (∑ i, ls j i) = false then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [update.eq_1, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  unfold evenWires
  rw [← Finset.sum_erase_add _
      (fun j => if (∑ i, update ls p j i) = false then (1 : ℕ) else 0) (Finset.mem_univ p.1),
    ← Finset.sum_erase_add _
      (fun j => if (∑ i, ls j i) = false then (1 : ℕ) else 0) (Finset.mem_univ p.1), hrest]
  simp only [update.eq_1, Function.update_self, Pi.add_apply, Finset.sum_add_distrib]
  cases ht : (∑ i, ls p.1 i) <;> cases hc : (∑ i, ls p.2 i) <;>
    simp_all [Bool.add_eq_xor]

private lemma return_balance {m : ℕ} (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool) :
    evenWires (labels gs ls) + returns gs ls = evenWires ls + (births gs ls).length := by
  induction gs generalizing ls with
  | nil => simp [labels.eq_1, returns, births]
  | cons p gs ih =>
    have hi := ih (update ls p)
    have hs := wire_update_count ls p
    change evenWires (labels gs (update ls p)) +
      ((if _ then 1 else 0) + returns gs (update ls p)) =
      evenWires ls + (if _ then _ :: births gs (update ls p) else births gs (update ls p)).length
    by_cases hb : (∑ i, ls p.1 i) = true ∧ (∑ i, ls p.2 i) = true <;>
      by_cases hr : (∑ i, ls p.1 i) = false ∧ (∑ i, ls p.2 i) = true <;>
      simp [hb, hr] at hi hs ⊢ <;> omega

private lemma disjoint_counts {m : ℕ} (gs : List (Fin m × Fin m))
    (ls : Fin m → Fin m → Bool) :
    (evenOutputs gs ls).length + returns gs ls ≤ gs.length := by
  induction gs generalizing ls with
  | nil => simp [evenOutputs, outputs, returns]
  | cons p gs ih =>
    have hi := ih (update ls p)
    simp only [evenOutputs, outputs, returns, List.foldr_cons, List.filter_cons,
      Pi.add_apply, Finset.sum_add_distrib] at hi ⊢
    cases ht : (∑ i, ls p.1 i) <;> cases hc : (∑ i, ls p.2 i) <;>
      simp [Bool.add_eq_xor] at hi ⊢ <;> omega

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
  have hs : evenWires ls = 0 := by simp [evenWires.eq_1, hstart]
  have ht : evenWires (labels gs ls) = 0 := by simp [evenWires.eq_1, hend]
  rw [hs, ht] at hr
  have hp : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
  omega

end D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting
