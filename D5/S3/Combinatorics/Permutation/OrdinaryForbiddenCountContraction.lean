/- GID: D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction
   mirror-E: none(waiver:noncomputable-forbidden-count-contraction)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Basic]
   utility: none
   digest: Ordinary deletion contracts both actual forbidden counts by their first high-prefix cardinalities. -/

import D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction
open D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse

def Eligible {K : Nat} (F G : Fin K → Nat)
    (σ : Equiv.Perm (Fin (K+1))) (π : Equiv.Perm (Fin K)) : Prop :=
  ∀ i, (σ (π i).castSucc).val < F i ∧ (σ (π i).succ).val < G i


def Front {K : Nat} (F : Fin K → Nat)
    (σ : Equiv.Perm (Fin (K+1))) (π : Equiv.Perm (Fin K)) (i : Fin K) : Finset (Fin K) :=
  Finset.univ.filter (fun j => i < j ∧ σ (π i).castSucc < σ (π j).castSucc ∧
    π j < π i ∧ F i ≤ (σ (π j).castSucc).val)

-- none encodes precisely the distinguished target j=K+1; some j encodes an ordinary column.
noncomputable def Back {K : Nat} (G : Fin K → Nat)
    (σ : Equiv.Perm (Fin (K+1))) (π : Equiv.Perm (Fin K)) (i : Fin K) : Finset (Option (Fin K)) :=
  by
  classical
  exact Finset.univ.filter (fun q => match q with
    | none => σ (π i).succ < σ 0 ∧ G i ≤ (σ 0).val
    | some j => i < j ∧ σ (π i).succ < σ (π j).succ ∧
      π j < π i ∧ G i ≤ (σ (π j).succ).val)

noncomputable def ForbiddenCount {K : Nat} (F G : Fin K → Nat)
    (σ : Equiv.Perm (Fin (K+1))) (π : Equiv.Perm (Fin K)) : Nat × Nat :=
  (∑ i, (Front F σ π i).card, ∑ i, (Back G σ π i).card)

 theorem ordinary_forbidden_count_contraction {n : Nat} (F G : Fin (n+1) → Nat)
    (σ : Equiv.Perm (Fin (n+2))) (π : Equiv.Perm (Fin (n+1)))
    (hF : Monotone F) (hG : Monotone G) (hFG : ∀ i, F i ≤ G i)
    (hel : Eligible F G σ π) :
    let Ft := fun i : Fin n => F i.succ - 1
    let Gt := fun i : Fin n => G i.succ - 1
    let s := cut σ (π 0).castSucc
    let p := cut π 0
    (ForbiddenCount F G σ π).1 = (ForbiddenCount Ft Gt s p).1 +
      (Finset.univ.filter (fun u : Fin (n+2) => u.val < (π 0).val ∧ F 0 ≤ (σ u).val)).card ∧
    (ForbiddenCount F G σ π).2 = (ForbiddenCount Ft Gt s p).2 +
      (Finset.univ.filter (fun u : Fin (n+2) => u.val < (π 0).val ∧ G 0 ≤ (σ u).val)).card := by
  classical
  let Prefix {K : Nat} (σ : Equiv.Perm (Fin (K+1))) (r : Fin K) (T : Nat) : Finset (Fin (K+1)) :=
    Finset.univ.filter (fun u => u.val < r.val ∧ T ≤ (σ u).val)
  have prefix_counts {K : Nat} (F G : Fin K → Nat)
      (σ : Equiv.Perm (Fin (K+1))) (π : Equiv.Perm (Fin K))
      (hF : Monotone F) (hG : Monotone G) (hFG : ∀ i, F i ≤ G i)
      (hel : Eligible F G σ π) (i : Fin K) :
      (Front F σ π i).card = (Prefix σ (π i) (F i)).card ∧
      (Back G σ π i).card = (Prefix σ (π i) (G i)).card := by
    classical
    constructor
    · apply Finset.card_bij (fun j _ => (π j).castSucc)
      · intro j hj
        simp only [Front, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Prefix, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hj.2.2.1, hj.2.2.2⟩
      · intro j hj l hl he
        exact π.injective (Fin.castSucc_injective _ he)
      · intro u hu
        simp only [Prefix, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        let r : Fin K := ⟨u.val, hu.1.trans (π i).isLt⟩
        let j := π.symm r
        have hπ : π j = r := π.apply_symm_apply r
        have hu' : (π j).castSucc = u := by rw [hπ]; exact Fin.ext rfl
        have hij : i < j := by
          by_contra hn
          have hjbound := (hel j).1
          have hmono := hF (le_of_not_gt hn)
          rw [hu'] at hjbound
          omega
        have hrow : σ (π i).castSucc < σ (π j).castSucc := by
          rw [hu']
          exact (hel i).1.trans_le hu.2
        refine ⟨j, ?_, hu'⟩
        simp only [Front, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hu']
        exact ⟨hij, hu' ▸ hrow, by rw [hπ]; exact hu.1, hu.2⟩
    · let target : Option (Fin K) → Fin (K+1) := fun q =>
        match q with | none => 0 | some j => (π j).succ
      apply Finset.card_bij (fun q _ => target q)
      · intro q hq
        simp only [Back, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        simp only [Prefix, Finset.mem_filter, Finset.mem_univ, true_and]
        cases q with
        | none =>
          dsimp at hq
          change 0 < (π i).val ∧ G i ≤ (σ 0).val
          constructor
          · have hfront := (hel i).1
            have hfg := hFG i
            by_contra hn
            have hp : (π i).castSucc = 0 := Fin.ext (by simp only [Fin.val_castSucc, Fin.val_zero]; omega)
            rw [hp] at hfront
            omega
          · exact hq.2
        | some j =>
          dsimp at hq
          change (π j).val + 1 < (π i).val ∧ G i ≤ (σ (π j).succ).val
          constructor
          · have hp : (π j).val < (π i).val := hq.2.2.1
            have hfront := (hel i).1
            have hfg := hFG i
            have hn : (π j).val + 1 ≠ (π i).val := by
              intro he
              have he' : (π j).succ = (π i).castSucc := Fin.ext he
              rw [he'] at hq
              omega
            omega
          · exact hq.2.2.2
      · intro q hq r hr he
        cases q <;> cases r
        · rfl
        · exact False.elim (Fin.succ_ne_zero _ he.symm)
        · exact False.elim (Fin.succ_ne_zero _ he)
        · exact congrArg some (π.injective (Fin.succ_injective _ he))
      · intro u hu
        simp only [Prefix, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        by_cases hz : u = 0
        · refine ⟨none, ?_, ?_⟩
          · simp only [Back, Finset.mem_filter, Finset.mem_univ, true_and]
            subst u
            exact ⟨(hel i).2.trans_le hu.2, hu.2⟩
          · exact hz.symm
        · let r : Fin K := u.pred hz
          let j := π.symm r
          have hπ : π j = r := π.apply_symm_apply r
          have hu' : (π j).succ = u := by rw [hπ]; exact Fin.succ_pred u hz
          have hij : i < j := by
            by_contra hn
            have hjbound := (hel j).2
            have hmono := hG (le_of_not_gt hn)
            rw [hu'] at hjbound
            omega
          have hp : π j < π i := by
            have he := congrArg Fin.val hu'
            simp only [Fin.val_succ] at he
            change (π j).val < (π i).val
            omega
          refine ⟨some j, ?_, hu'⟩
          simp only [Back, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hu']
          exact ⟨hij, (hel i).2.trans_le hu.2, hp, hu.2⟩

  have prefix_cut {n : Nat} (σ : Equiv.Perm (Fin (n+2)))
      (t : Fin (n+1)) (z : Fin n) (T : Nat)
      (ha : (σ t.castSucc).val < T) :
      (Prefix (cut σ t.castSucc) z (T-1)).card =
        (Prefix σ (t.succAbove z) T).card := by
    classical
    let a := σ t.castSucc
    let s := cut σ t.castSucc
    have lift (u : Fin (n+1)) : a.succAbove (s u) = σ (t.castSucc.succAbove u) := by
      have hh := (finSuccAboveEquiv a).apply_symm_apply
        ((Equiv.subtypeEquiv σ (by intro x; exact σ.injective.ne_iff.symm))
          ((finSuccAboveEquiv t.castSucc) u))
      exact congrArg Subtype.val hh
    have position : t.castSucc.succAbove z.castSucc = (t.succAbove z).castSucc := by
      by_cases hz : z.castSucc < t
      · rw [Fin.succAbove_of_castSucc_lt _ _ hz,
          Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hz)]
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hz),
          Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (le_of_not_gt hz))]
        exact Fin.ext rfl
    have threshold (u : Fin (n+1)) : T-1 ≤ (s u).val ↔ T ≤ (σ (t.castSucc.succAbove u)).val := by
      rw [← lift u]
      have ha' : a.val < T := ha
      by_cases hlow : (s u).castSucc < a
      · rw [Fin.succAbove_of_castSucc_lt _ _ hlow]
        have hv : (s u).val < a.val := hlow
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hlow)]
        simp only [Fin.val_succ]
        omega
    apply Finset.card_bij (fun u _ => t.castSucc.succAbove u)
    · intro u hu
      simp only [Prefix, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      constructor
      · change t.castSucc.succAbove u < (t.succAbove z).castSucc
        rw [← position, Fin.succAbove_lt_succAbove_iff]
        exact hu.1
      · exact (threshold u).mp hu.2
    · intro u hu v hv he
      exact (Fin.strictMono_succAbove t.castSucc).injective he
    · intro x hx
      simp only [Prefix, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hne : x ≠ t.castSucc := by
        intro he
        rw [he] at hx
        omega
      let u := (finSuccAboveEquiv t.castSucc).symm ⟨x,hne⟩
      have he : t.castSucc.succAbove u = x :=
        congrArg Subtype.val ((finSuccAboveEquiv t.castSucc).apply_symm_apply ⟨x,hne⟩)
      refine ⟨u, ?_, he⟩
      simp only [Prefix, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · have hp : t.castSucc.succAbove u < (t.succAbove z).castSucc := by
          rw [he]
          exact hx.1
        rw [← position, Fin.succAbove_lt_succAbove_iff] at hp
        exact hp
      · apply (threshold u).mpr
        rw [he]
        exact hx.2

  have ordinary_eligibility {n : Nat} (F G : Fin (n+1) → Nat)
      (σ : Equiv.Perm (Fin (n+2))) (π : Equiv.Perm (Fin (n+1)))
      (hF : Monotone F) (hG : Monotone G) (hFG : ∀ i, F i ≤ G i)
      (hel : Eligible F G σ π) :
      Eligible (fun i : Fin n => F i.succ - 1) (fun i : Fin n => G i.succ - 1)
        (cut σ (π 0).castSucc) (cut π 0) := by
    classical
    let t := π 0
    let a := σ t.castSucc
    let s := cut σ t.castSucc
    let p := cut π 0
    have column (i : Fin n) : t.succAbove (p i) = π i.succ := by
      have hh := (finSuccAboveEquiv t).apply_symm_apply
        ((Equiv.subtypeEquiv π (by intro x; exact π.injective.ne_iff.symm))
          ((finSuccAboveEquiv (0 : Fin (n+1))) i))
      have he := congrArg Subtype.val hh
      change t.succAbove (p i) = π ((0 : Fin (n+1)).succAbove i) at he
      simpa only [Fin.succAbove_zero_apply] using he
    have lift (u : Fin (n+1)) : a.succAbove (s u) = σ (t.castSucc.succAbove u) := by
      have hh := (finSuccAboveEquiv a).apply_symm_apply
        ((Equiv.subtypeEquiv σ (by intro x; exact σ.injective.ne_iff.symm))
          ((finSuccAboveEquiv t.castSucc) u))
      exact congrArg Subtype.val hh
    have threshold (u : Fin (n+1)) (T : Nat) (ha : a.val < T) :
        (s u).val < T-1 ↔ (σ (t.castSucc.succAbove u)).val < T := by
      rw [← lift u]
      by_cases hlow : (s u).castSucc < a
      · rw [Fin.succAbove_of_castSucc_lt _ _ hlow]
        have hv : (s u).val < a.val := hlow
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hlow)]
        simp only [Fin.val_succ]
        omega
    intro i
    have haf : a.val < F i.succ := (hel 0).1.trans_le (hF (Fin.zero_le _))
    have hag : a.val < G i.succ := haf.trans_le (hFG i.succ)
    have frontpos : t.castSucc.succAbove (p i).castSucc = (π i.succ).castSucc := by
      rw [← column i]
      by_cases hz : (p i).castSucc < t
      · rw [Fin.succAbove_of_castSucc_lt _ _ hz,
          Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hz)]
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hz),
          Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (le_of_not_gt hz))]
        exact Fin.ext rfl
    constructor
    · apply (threshold (p i).castSucc (F i.succ) haf).mpr
      rw [frontpos]
      exact (hel i.succ).1
    · apply (threshold (p i).succ (G i.succ) hag).mpr
      by_cases hp : (p i).val + 1 = t.val
      · have backpos : t.castSucc.succAbove (p i).succ = t.succ := by
          have hnext : (p i).succ = t := Fin.ext hp
          rw [hnext, Fin.succAbove_castSucc_self]
        rw [backpos]
        exact (hel 0).2.trans_le (hG (Fin.zero_le _))
      · have backpos : t.castSucc.succAbove (p i).succ = (π i.succ).succ := by
          rw [← column i]
          by_cases hq : (p i).castSucc < t
          · have hnext : ((p i).succ).castSucc < t.castSucc := by
              change (p i).val + 1 < t.val
              have hh : (p i).val < t.val := hq
              omega
            rw [Fin.succAbove_of_castSucc_lt _ _ hq,
              Fin.succAbove_of_castSucc_lt _ _ hnext]
            exact Fin.ext rfl
          · have hnext : t.castSucc ≤ ((p i).succ).castSucc := by
              change t.val ≤ (p i).val + 1
              have hh : t.val ≤ (p i).val := le_of_not_gt hq
              omega
            rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hq),
              Fin.succAbove_of_le_castSucc _ _ hnext]
        rw [backpos]
        exact (hel i.succ).2

  let t := π 0
  let s := cut σ t.castSucc
  let p := cut π 0
  let Ft := fun i : Fin n => F i.succ - 1
  let Gt := fun i : Fin n => G i.succ - 1
  have hFt : Monotone Ft := by
    intro i j hij
    exact Nat.sub_le_sub_right (hF (Fin.succ_le_succ_iff.mpr hij)) 1
  have hGt : Monotone Gt := by
    intro i j hij
    exact Nat.sub_le_sub_right (hG (Fin.succ_le_succ_iff.mpr hij)) 1
  have hFGt : ∀ i, Ft i ≤ Gt i := by
    intro i
    exact Nat.sub_le_sub_right (hFG i.succ) 1
  have helt : Eligible Ft Gt s p := ordinary_eligibility F G σ π hF hG hFG hel
  have column (i : Fin n) : t.succAbove (p i) = π i.succ := by
    have hh := (finSuccAboveEquiv t).apply_symm_apply
      ((Equiv.subtypeEquiv π (by intro x; exact π.injective.ne_iff.symm))
        ((finSuccAboveEquiv (0 : Fin (n+1))) i))
    have he := congrArg Subtype.val hh
    change t.succAbove (p i) = π ((0 : Fin (n+1)).succAbove i) at he
    simpa only [Fin.succAbove_zero_apply] using he
  have high_total (T : Fin (n+1) → Nat) (hT : Monotone T)
      (ha : (σ t.castSucc).val < T 0) :
      (∑ i, (Prefix σ (π i) (T i)).card) =
        (∑ i : Fin n, (Prefix s (p i) (T i.succ - 1)).card) + (Prefix σ t (T 0)).card := by
    rw [Fin.sum_univ_succ]
    have he : (∑ i : Fin n, (Prefix σ (π i.succ) (T i.succ)).card) =
        ∑ i : Fin n, (Prefix s (p i) (T i.succ - 1)).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← column i]
      exact (prefix_cut σ t (p i) (T i.succ) (ha.trans_le (hT (Fin.zero_le _)))).symm
    rw [he]
    exact Nat.add_comm _ _
  have hf0 : (σ t.castSucc).val < F 0 := (hel 0).1
  have hg0 : (σ t.castSucc).val < G 0 := hf0.trans_le (hFG 0)
  constructor
  · change (∑ i, (Front F σ π i).card) = (∑ i : Fin n, (Front Ft s p i).card) + (Prefix σ t (F 0)).card
    calc
      (∑ i, (Front F σ π i).card) = ∑ i, (Prefix σ (π i) (F i)).card := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (prefix_counts F G σ π hF hG hFG hel i).1
      _ = (∑ i : Fin n, (Prefix s (p i) (Ft i)).card) + (Prefix σ t (F 0)).card :=
        high_total F hF hf0
      _ = (∑ i : Fin n, (Front Ft s p i).card) + (Prefix σ t (F 0)).card := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        exact (prefix_counts Ft Gt s p hFt hGt hFGt helt i).1.symm
  · change (∑ i, (Back G σ π i).card) = (∑ i : Fin n, (Back Gt s p i).card) + (Prefix σ t (G 0)).card
    calc
      (∑ i, (Back G σ π i).card) = ∑ i, (Prefix σ (π i) (G i)).card := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (prefix_counts F G σ π hF hG hFG hel i).2
      _ = (∑ i : Fin n, (Prefix s (p i) (Gt i)).card) + (Prefix σ t (G 0)).card :=
        high_total G hG hg0
      _ = (∑ i : Fin n, (Back Gt s p i).card) + (Prefix σ t (G 0)).card := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        exact (prefix_counts Ft Gt s p hFt hGt hFGt helt i).2.symm

end D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction
