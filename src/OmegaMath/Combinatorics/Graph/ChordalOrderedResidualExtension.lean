import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.EliminationForest
import OmegaMath.Combinatorics.Graph.ChordalResidualExtension
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Abel

compile_only_with_mathlib

/-! # Reverse elimination with an ordered triangle invariant -/

namespace SimpleGraph.ChordalResidualExtension

variable {V E : Type*} [Finite V] [NormedAddCommGroup E] {G : SimpleGraph V}

/-- A one-vertex placement rule on predecessor cliques extends along a reverse
perfect elimination order. The invariant reads the oldest edge first. -/
theorem reconstruct_ordered (hG : G.IsChordal) (cap : ℝ)
    (face : E → E → E → E → Prop) (sizeAllowed : ℕ → Prop)
    (hsize : ∀ s : Finset V, G.IsClique (s : Set V) → s.Nonempty → sizeAllowed (s.card - 1))
    (place : ∀ n, sizeAllowed n → ∀ (c : Fin n → E) (r : Fin n → Fin n → E), Skew r →
      (∀ i j, i < j → ‖r i j‖ ≤ cap) →
      (∀ i j k, i < j → j < k → ‖holonomy r i j k‖ ≤ 1 ∧
        face (r i j) (r i k) (r j k) (holonomy r i j k)) →
      (∀ i j, i < j → ‖r i j - (c i - c j)‖ ≤ 1) →
      ∃ z, (∀ i, ‖c i - z‖ ≤ cap) ∧
        ∀ i j, i < j → face (r i j) (c i - z) (c j - z) (r i j - (c i - c j)))
    (g : V → V → E) (hg : Skew g)
    (ht : ∀ i j k, Triangle G i j k → ‖holonomy g i j k‖ ≤ 1) :
    ∃ p : V → E, ∀ i j, G.Adj i j → ‖residual g p i j‖ ≤ cap := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨ord, ho⟩ := hG.exists_isPEO
  let rank := peoRank ord
  have hinj : Function.Injective rank := peoRank_injective ho.injective
  letI : LinearOrder V := LinearOrder.lift' rank hinj
  have less {i j : V} : i < j ↔ rank i < rank j := Iff.rfl
  have ord_lt {i j : V} (h : i < j) : ord j < ord i := by
    rcases lt_trichotomy (ord i) (ord j) with hlt | heq | hgt
    · exact (less.mp h |>.not_gt (peoRank_lt_of_ord_lt hlt)).elim
    · exact (h.ne (ho.injective heq)).elim
    · exact hgt
  let earlier (z : V) := laterNbrs G ord z
  have mem_earlier {i z : V} : i ∈ earlier z ↔ i < z ∧ G.Adj i z := by
    change _ ∈ laterNbrs G ord _ ↔ _
    rw [mem_laterNbrs]
    exact ⟨fun h => ⟨less.mpr (peoRank_lt_of_ord_lt h.1), h.2.symm⟩,
      fun h => ⟨ord_lt h.1, h.2.symm⟩⟩
  have earlier_adj {i j z : V} (hi : i ∈ earlier z) (hj : j ∈ earlier z) (h : i < j) :
      G.Adj i j :=
    ho.isClique_later z ⟨ord_lt (mem_earlier.mp hi).1, (mem_earlier.mp hi).2.symm⟩
      ⟨ord_lt (mem_earlier.mp hj).1, (mem_earlier.mp hj).2.symm⟩ h.ne
  have attach (p : V → E) (z : V)
      (hedge : ∀ i ∈ earlier z, ∀ j ∈ earlier z, i < j → ‖residual g p i j‖ ≤ cap)
      (hface : ∀ i ∈ earlier z, ∀ j ∈ earlier z, ∀ k ∈ earlier z, i < j → j < k →
        face (residual g p i j) (residual g p i k) (residual g p j k)
          (holonomy g i j k)) :
      ∃ q, (∀ i ∈ earlier z, ‖g i z - (q - p i)‖ ≤ cap) ∧
        ∀ i ∈ earlier z, ∀ j ∈ earlier z, i < j →
          face (residual g p i j) (g i z - (q - p i)) (g j z - (q - p j))
            (holonomy g i j z) := by
    let S := earlier z
    have hzS : z ∉ S := fun h => (mem_earlier.mp h).1.false
    have hbag : G.IsClique (↑(insert z S) : Set V) := ho.peoBag_isClique z
    have hs := hsize (insert z S) hbag (Finset.insert_nonempty z S)
    rw [Finset.card_insert_of_notMem hzS, Nat.add_sub_cancel] at hs
    let e : Fin S.card ≃o {v // v ∈ S} := S.orderIsoOfFin rfl
    let c (i : Fin S.card) := g (e i).val z + p (e i).val
    let r (i j : Fin S.card) := residual g p (e i).val (e j).val
    have oldCurl (i j k : Fin S.card) :
        holonomy r i j k = holonomy g (e i).val (e j).val (e k).val :=
      residual_holonomy g p _ _ _
    have newCurl (i j : Fin S.card) :
        r i j - (c i - c j) = holonomy g (e i).val (e j).val z := by
      dsimp [r, c, residual, holonomy]
      abel
    obtain ⟨q, hq, hf⟩ := place S.card hs c r (fun i j => residual_skew hg p _ _)
      (fun i j hij => hedge _ (e i).property _ (e j).property (e.strictMono hij))
      (fun i j k hij hjk => by
        rw [oldCurl]
        have hij' := e.strictMono hij
        have hjk' := e.strictMono hjk
        exact ⟨ht _ _ _ ⟨earlier_adj (e i).property (e j).property hij',
          earlier_adj (e j).property (e k).property hjk',
          earlier_adj (e i).property (e k).property (hij'.trans hjk')⟩,
          hface _ (e i).property _ (e j).property _ (e k).property hij' hjk'⟩)
      (fun i j hij => by
        rw [newCurl]
        exact ht _ _ _ ⟨earlier_adj (e i).property (e j).property (e.strictMono hij),
          (mem_earlier.mp (e j).property).2, (mem_earlier.mp (e i).property).2⟩)
    have eqResidual (i : Fin S.card) :
        c i - q = g (e i).val z - (q - p (e i).val) := by dsimp [c]; abel
    refine ⟨q, ?_, ?_⟩
    · intro i hi
      simpa only [eqResidual, e.apply_symm_apply] using hq (e.symm ⟨i, hi⟩)
    · intro i hi j hj hij
      have hij' : e.symm ⟨i, hi⟩ < e.symm ⟨j, hj⟩ := e.symm.strictMono hij
      have hh := hf (e.symm ⟨i, hi⟩) (e.symm ⟨j, hj⟩) hij'
      rw [newCurl, eqResidual, eqResidual] at hh
      simpa only [r, e.apply_symm_apply] using hh
  have stages (n : ℕ) : ∃ p : V → E,
      (∀ i j, i < j → rank j < n → G.Adj i j → ‖residual g p i j‖ ≤ cap) ∧
      (∀ i j k, i < j → j < k → rank k < n → Triangle G i j k →
        face (residual g p i j) (residual g p i k) (residual g p j k) (holonomy g i j k)) := by
    induction n with
    | zero => exact ⟨fun _ => 0, fun _ _ _ h _ => (Nat.not_lt_zero _ h).elim,
        fun _ _ _ _ _ h _ => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨p, hE, hF⟩ := ih
      by_cases hz : ∃ z, rank z = n
      · obtain ⟨z, hz⟩ := hz
        have old {i : V} (hi : i ∈ earlier z) : rank i < n :=
          hz ▸ less.mp (mem_earlier.mp hi).1
        obtain ⟨q, hq, hf⟩ := attach p z
          (fun i hi j hj hij => hE i j hij (old hj) (earlier_adj hi hj hij))
          (fun i hi j hj k hk hij hjk => hF i j k hij hjk (old hk)
            ⟨earlier_adj hi hj hij, earlier_adj hj hk hjk, earlier_adj hi hk (hij.trans hjk)⟩)
        let p' (i : V) := if i = z then q else p i
        have stay (i : V) (hi : rank i < n) : p' i = p i := by
          have hne : i ≠ z := fun he => by subst i; omega
          simp [p', hne]
        have new : p' z = q := by simp [p']
        refine ⟨p', ?_, ?_⟩
        · intro i j hij hj adj
          by_cases h : rank j < n
          · simpa only [residual, stay i ((less.mp hij).trans h), stay j h] using hE i j hij h adj
          · have he : j = z := hinj (by omega)
            subst j
            have hi := mem_earlier.mpr ⟨hij, adj⟩
            simpa only [residual, stay i (old hi), new] using hq i hi
        · intro i j k hij hjk hk ht
          by_cases h : rank k < n
          · have hj := (less.mp hjk).trans h
            have hi := (less.mp hij).trans hj
            simpa only [residual, stay i hi, stay j hj, stay k h] using hF i j k hij hjk h ht
          · have he : k = z := hinj (by omega)
            subst k
            have hi := mem_earlier.mpr ⟨hij.trans hjk, ht.2.2⟩
            have hj := mem_earlier.mpr ⟨hjk, ht.2.1⟩
            simpa only [residual, stay i (old hi), stay j (old hj), new] using hf i hi j hj hij
      · have prev {i : V} (hi : rank i < n + 1) : rank i < n := by
          have hn : rank i ≠ n := fun h => hz ⟨i, h⟩
          omega
        exact ⟨p, fun i j hij hj => hE i j hij (prev hj),
          fun i j k hij hjk hk => hF i j k hij hjk (prev hk)⟩
  obtain ⟨p, hp, _⟩ := stages ((Finset.univ : Finset V).sup rank + 1)
  have hr (i : V) : rank i < (Finset.univ : Finset V).sup rank + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ _))
  refine ⟨p, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij.ne with h | h
  · exact hp i j h (hr j) hij
  · rw [residual_skew hg p j i, norm_neg]
    exact hp j i h (hr i) hij.symm

end SimpleGraph.ChordalResidualExtension
