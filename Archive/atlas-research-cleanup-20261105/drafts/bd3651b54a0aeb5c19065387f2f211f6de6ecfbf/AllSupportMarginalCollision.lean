import D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.SMul

/-! A constructive all-size collision. Linear words are extended at their two ends;
then a fresh anchor embeds them into the actual quotient by rotation. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.CircularWords.AllSupportMarginalCollision
open CircularDeletionTransport CyclicInsertionGap
noncomputable section
universe u v
variable {α : Type u} [DecidableEq α]

private def erase (i : α) (L : List α) : List α :=
  L.filter (fun a => decide (a ≠ i))

private def mass {β : Type v} (m : β →₀ ℚ) : ℚ :=
  (Finsupp.mapDomain (fun _ : β => ()) m) ()

private def mix {β γ : Type*} (f g : β → γ) (m n : β →₀ ℚ) : γ →₀ ℚ :=
  (1/2 : ℚ) • (Finsupp.mapDomain f m + Finsupp.mapDomain g n)

private theorem mem_mix {β γ : Type*} [DecidableEq γ]
    {f g : β → γ} {m n : β →₀ ℚ} {z : γ} (h : z ∈ (mix f g m n).support) :
    (∃ w ∈ m.support, f w = z) ∨ (∃ w ∈ n.support, g w = z) := by
  have h' := Finsupp.support_add (Finsupp.support_smul h)
  rcases Finset.mem_union.mp h' with h' | h'
  · exact Or.inl (Finset.mem_image.mp (Finsupp.mapDomain_support h'))
  · exact Or.inr (Finset.mem_image.mp (Finsupp.mapDomain_support h'))

private theorem nonneg_mix {β γ : Type*} {f g : β → γ} {m n : β →₀ ℚ}
    (hm : ∀ w, 0 ≤ m w) (hn : ∀ w, 0 ≤ n w) : ∀ z, 0 ≤ mix f g m n z := by
  intro z
  exact mul_nonneg (by norm_num) (add_nonneg
    (Finsupp.mapDomain_nonneg (show 0 ≤ m from hm) z)
    (Finsupp.mapDomain_nonneg (show 0 ≤ n from hn) z))

private theorem mass_mix {β γ : Type*} (f g : β → γ) (m n : β →₀ ℚ)
    (hm : mass m = 1) (hn : mass n = 1) : mass (mix f g m n) = 1 := by
  simp only [mass, mix, Finsupp.mapDomain_smul, Finsupp.mapDomain_add,
    ← Finsupp.mapDomain_comp, Function.comp_def, Finsupp.smul_apply,
    Finsupp.add_apply, smul_eq_mul] at *
  rw [hm, hn]
  norm_num

private theorem map_mix {β γ δ : Type*} (h : γ → δ) (f g : β → γ) (m n : β →₀ ℚ) :
    Finsupp.mapDomain h (mix f g m n) = mix (h ∘ f) (h ∘ g) m n := by
  simp only [mix, Finsupp.mapDomain_smul, Finsupp.mapDomain_add,
    Finsupp.mapDomain_comp]

private def Valid (B : Finset α) (m : List α →₀ ℚ) : Prop :=
  ∀ L ∈ m.support, L.Nodup ∧ L.toFinset = B

private structure Trade (B : Finset α) (m n : List α →₀ ℚ) : Prop where
  valid_m : Valid B m
  valid_n : Valid B n
  nonneg_m : ∀ L, 0 ≤ m L
  nonneg_n : ∀ L, 0 ≤ n L
  mass_m : mass m = 1
  mass_n : mass n = 1
  disjoint : Disjoint m.support n.support
  deletions : ∀ i ∈ B, Finsupp.mapDomain (erase i) m = Finsupp.mapDomain (erase i) n
  circular : Finsupp.mapDomain Cycle.ofList m = Finsupp.mapDomain Cycle.ofList n

private theorem erase_of_not_mem {x : α} {L : List α} (hx : x ∉ L) : erase x L = L := by
  apply List.filter_eq_self.mpr
  intro y hy
  simp only [decide_eq_true_eq]
  exact fun e => hx (e ▸ hy)

private theorem valid_fresh {B : Finset α} {m : List α →₀ ℚ} (hm : Valid B m)
    {x : α} (hx : x ∉ B) {L : List α} (hL : L ∈ m.support) : x ∉ L := by
  intro h
  exact hx ((hm L hL).2 ▸ List.mem_toFinset.mpr h)

private theorem valid_nonempty {B : Finset α} {m : List α →₀ ℚ} (hm : Valid B m)
    (hB : 2 ≤ B.card) {L : List α} (hL : L ∈ m.support) : L ≠ [] := by
  intro he
  have h := (hm L hL).2
  rw [he] at h
  have : B.card = 0 := by rw [← h]; rfl
  omega

omit [DecidableEq α] in
private theorem prepend_ne_append {x : α} {L K : List α}
    (hL : L ≠ []) (hx : x ∉ K) : x :: L ≠ K ++ [x] := by
  intro he
  cases K with
  | nil => exact hL (List.cons.inj he).2
  | cons y K =>
    have : x = y := (List.cons.inj he).1
    exact hx (by simp [this])

private theorem valid_extend {B : Finset α} {m n : List α →₀ ℚ}
    (hm : Valid B m) (hn : Valid B n) {x : α} (hx : x ∉ B) :
    Valid (insert x B) (mix (List.cons x) (fun L => L ++ [x]) m n) := by
  intro L hL
  rcases mem_mix hL with ⟨K, hK, rfl⟩ | ⟨K, hK, rfl⟩
  · exact ⟨List.nodup_cons.mpr ⟨valid_fresh hm hx hK, (hm K hK).1⟩,
      by simp [(hm K hK).2]⟩
  · refine ⟨?_, ?_⟩
    · simpa using List.Nodup.concat (valid_fresh hn hx hK) (hn K hK).1
    · simp [(hn K hK).2]

private theorem disjoint_extend {B : Finset α} {m n : List α →₀ ℚ}
    (hm : Valid B m) (hn : Valid B n) (hB : 2 ≤ B.card)
    (hd : Disjoint m.support n.support) {x : α} (hx : x ∉ B) :
    Disjoint (mix (List.cons x) (fun L => L ++ [x]) m n).support
      (mix (List.cons x) (fun L => L ++ [x]) n m).support := by
  apply Finset.disjoint_left.mpr
  intro L hL hR
  rcases mem_mix hL with ⟨K, hK, heK⟩ | ⟨K, hK, heK⟩ <;>
    rcases mem_mix hR with ⟨J, hJ, heJ⟩ | ⟨J, hJ, heJ⟩
  · have he : K = J := List.cons.inj (heK.trans heJ.symm) |>.2
    exact Finset.disjoint_left.mp hd hK (he.symm ▸ hJ)
  · exact prepend_ne_append (valid_nonempty hm hB hK) (valid_fresh hm hx hJ)
      (heK.trans heJ.symm)
  · exact prepend_ne_append (valid_nonempty hn hB hJ) (valid_fresh hn hx hK)
      (heJ.trans heK.symm)
  · have he : K = J := List.append_cancel_right (heK.trans heJ.symm)
    exact Finset.disjoint_left.mp hd hJ (he ▸ hK)

private theorem extend_trade {B : Finset α} {m n : List α →₀ ℚ}
    (T : Trade B m n) (hB : 2 ≤ B.card) {x : α} (hx : x ∉ B) :
    Trade (insert x B)
      (mix (List.cons x) (fun L => L ++ [x]) m n)
      (mix (List.cons x) (fun L => L ++ [x]) n m) := by
  refine ⟨valid_extend T.valid_m T.valid_n hx,
    valid_extend T.valid_n T.valid_m hx,
    nonneg_mix T.nonneg_m T.nonneg_n, nonneg_mix T.nonneg_n T.nonneg_m,
    mass_mix _ _ _ _ T.mass_m T.mass_n,
    mass_mix _ _ _ _ T.mass_n T.mass_m,
    disjoint_extend T.valid_m T.valid_n hB T.disjoint hx, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      have a (q : List α →₀ ℚ) (hq : Valid B q) :
          Finsupp.mapDomain (erase x ∘ List.cons x) q = q := by
        calc
          _ = Finsupp.mapDomain id q := Finsupp.mapDomain_congr (by
            intro L hL
            change erase x (x :: L) = L
            have hf := erase_of_not_mem (valid_fresh hq hx hL)
            simpa only [erase, List.filter_cons, ne_eq, not_true_eq_false,
              decide_false, Bool.false_eq_true, ↓reduceIte] using hf)
          _ = q := Finsupp.mapDomain_id
      have b (q : List α →₀ ℚ) (hq : Valid B q) :
          Finsupp.mapDomain (erase x ∘ (fun L => L ++ [x])) q = q := by
        calc
          _ = Finsupp.mapDomain id q := Finsupp.mapDomain_congr (by
            intro L hL
            change (L ++ [x]).filter (fun a => decide (a ≠ x)) = L
            simp only [List.filter_append, List.filter_cons, ne_eq,
              not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
              List.filter_nil, List.append_nil]
            exact erase_of_not_mem (valid_fresh hq hx hL))
          _ = q := Finsupp.mapDomain_id
      simp only [map_mix]
      simp only [mix, a m T.valid_m, a n T.valid_n,
        b m T.valid_m, b n T.valid_n, add_comm]
    · have hix : x ≠ i := fun e => hx (e ▸ hi)
      have a : erase i ∘ List.cons x = List.cons x ∘ erase i := by
        funext L; simp [erase, hix]
      have b : erase i ∘ (fun L => L ++ [x]) =
          (fun L => L ++ [x]) ∘ erase i := by
        funext L; simp [erase, List.filter_append, hix]
      simp only [map_mix]
      simp only [mix, a, b, Finsupp.mapDomain_comp, T.deletions i hi]
  · have h (q : List α →₀ ℚ) :
        Finsupp.mapDomain (Cycle.ofList ∘ List.cons x) q =
          Finsupp.mapDomain (Cycle.ofList ∘ (fun L => L ++ [x])) q := by
      apply Finsupp.mapDomain_congr
      intro L _
      exact Cycle.coe_cons_eq_coe_append L x
    simp only [map_mix]
    simp only [mix, h m, h n]
    rw [add_comm]

private theorem seed_trade {a b : α} (hab : a ≠ b) :
    Trade {a,b} (Finsupp.single [a,b] 1) (Finsupp.single [b,a] 1) := by
  have hv (c d : α) (hcd : c ≠ d) : Valid {c,d} (Finsupp.single [c,d] (1:ℚ)) := by
    intro L hL
    have : L = [c,d] := by simpa using hL
    subst L
    exact ⟨by simp [hcd], by simp⟩
  refine ⟨hv a b hab, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Finset.pair_comm] using hv b a hab.symm
  · intro L; simp only [Finsupp.single_apply]; split_ifs <;> norm_num
  · intro L; simp only [Finsupp.single_apply]; split_ifs <;> norm_num
  · simp [mass]
  · simp [mass]
  · simp [hab, hab.symm]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;>
      simp [erase, hab, hab.symm]
  · simp only [Finsupp.mapDomain_single]
    congr 1
    exact Cycle.coe_cons_eq_coe_append [b] a

private theorem exists_trade (B : Finset α) (hB : 2 ≤ B.card) :
    ∃ m n : List α →₀ ℚ, Trade B m n := by
  revert hB
  refine Finset.strongInductionOn B ?_
  intro B ih hB
  by_cases hb : B.card = 2
  · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hb
    exact ⟨_, _, seed_trade hab⟩
  · obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
    have hc : 2 ≤ (B.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨m,n,T⟩ := ih (B.erase x) (Finset.erase_ssubset hx) hc
    have TT := extend_trade T hc (Finset.notMem_erase x B)
    rw [Finset.insert_erase hx] at TT
    exact ⟨_, _, TT⟩

private def anchor (p : α) (L : List α) : Cycle α := (p :: L : List α)

/-- For every finite labeled support of size at least four, there are two
nonnegative rational probability laws on disjoint actual oriented cycles with
that exact support, and all individual deletion pushforwards agree. -/
theorem all_support_marginal_collision (A : Finset α) (hA : 4 ≤ A.card) :
    ∃ μ ν : Cycle α →₀ ℚ,
      (∀ C ∈ μ.support ∪ ν.support, C.Nodup ∧ C.toFinset = A) ∧
      (∀ C, 0 ≤ μ C ∧ 0 ≤ ν C) ∧
      (Finsupp.mapDomain (fun _ : Cycle α => ()) μ) () = 1 ∧
      (Finsupp.mapDomain (fun _ : Cycle α => ()) ν) () = 1 ∧
      Disjoint μ.support ν.support ∧
      (∀ i ∈ A, Finsupp.mapDomain (delete i) μ = Finsupp.mapDomain (delete i) ν) := by
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  let B := A.erase p
  have hB : 2 ≤ B.card := by dsimp [B]; rw [Finset.card_erase_of_mem hp]; omega
  have hpB : p ∉ B := Finset.notMem_erase p A
  obtain ⟨m,n,T⟩ := exists_trade B hB
  let μ := Finsupp.mapDomain (anchor p) m
  let ν := Finsupp.mapDomain (anchor p) n
  have hinv : ∀ q : List α →₀ ℚ, Valid B q → ∀ C ∈ (Finsupp.mapDomain (anchor p) q).support,
      C.Nodup ∧ C.toFinset = A := by
    intro q hq C hC
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hC)
    refine ⟨Cycle.nodup_coe_iff.mpr
      (List.nodup_cons.mpr ⟨valid_fresh hq hpB hL, (hq L hL).1⟩), ?_⟩
    change (p :: L).toFinset = A
    simp [(hq L hL).2, B, Finset.insert_erase hp]
  refine ⟨μ,ν,?_,?_,?_,?_,?_,?_⟩
  · intro C hC
    rcases Finset.mem_union.mp hC with h | h
    · exact hinv m T.valid_m C h
    · exact hinv n T.valid_n C h
  · intro C
    exact ⟨Finsupp.mapDomain_nonneg (show 0 ≤ m from T.nonneg_m) C,
      Finsupp.mapDomain_nonneg (show 0 ≤ n from T.nonneg_n) C⟩
  · change mass (Finsupp.mapDomain (anchor p) m) = 1
    simpa only [mass, ← Finsupp.mapDomain_comp, Function.comp_def] using T.mass_m
  · change mass (Finsupp.mapDomain (anchor p) n) = 1
    simpa only [mass, ← Finsupp.mapDomain_comp, Function.comp_def] using T.mass_n
  · apply Finset.disjoint_left.mpr
    intro C hμ hν
    obtain ⟨L,hL,heL⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hμ)
    obtain ⟨K,hK,heK⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hν)
    have he : L = K := anchored_coe_injective
      (List.nodup_cons.mpr ⟨valid_fresh T.valid_m hpB hL, (T.valid_m L hL).1⟩)
      (heL.trans heK.symm)
    exact Finset.disjoint_left.mp T.disjoint hL (he.symm ▸ hK)
  · intro i hi
    change Finsupp.mapDomain (delete i) (Finsupp.mapDomain (anchor p) m) =
      Finsupp.mapDomain (delete i) (Finsupp.mapDomain (anchor p) n)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    by_cases hip : i = p
    · subst i
      have h (q : List α →₀ ℚ) (hq : Valid B q) :
          Finsupp.mapDomain (delete p ∘ anchor p) q = Finsupp.mapDomain Cycle.ofList q := by
        apply Finsupp.mapDomain_congr
        intro L hL
        change ((erase p (p :: L) : List α) : Cycle α) = (L : Cycle α)
        have hf := erase_of_not_mem (valid_fresh hq hpB hL)
        simpa only [erase, List.filter_cons, ne_eq, not_true_eq_false,
          decide_false, Bool.false_eq_true, ↓reduceIte] using congrArg Cycle.ofList hf
      rw [h m T.valid_m, h n T.valid_n]
      exact T.circular
    · have he : delete i ∘ anchor p = anchor p ∘ erase i := by
        funext L
        change ((erase i (p :: L) : List α) : Cycle α) = ((p :: erase i L : List α) : Cycle α)
        simp [erase, Ne.symm hip]
      simp only [he, Finsupp.mapDomain_comp,
        T.deletions i (Finset.mem_erase.mpr ⟨hip,hi⟩)]

set_option pp.universes true in
#check @all_support_marginal_collision
#print axioms all_support_marginal_collision
end
end D5.S3.Combinatorics.CircularWords.AllSupportMarginalCollision
