/- GID: D5/S1/Words/GraphRepresentation/UniformHierarchy
   generality: G
   mirror-B: D5/B/S1/Words/GraphRepresentation/UniformHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every positive uniform projection-equality graph class has a proper next class. -/

import D5.S1.Words.GraphRepresentation.UniformVertexExtension
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
The classes use the admitted positive-uniform `InG`, with actual List words
and equality of actual two-letter projections. The separator is an induced
subset of a finite membership graph, on the same carrier in both conclusions.
The all-parameter nonuniversality argument is internal to the full consumer.
This is a structural proof, without bounded enumeration, certified finite
instance evaluation, a checker or a numerical reduction; utility is `none`.
-/

universe u

namespace D5.S1.Words.GraphRepresentation.UniformHierarchy

open ExplicitNonTwoUniform UniformVertexExtension

/-- The bipartite membership graph on points and all their subsets. -/
def membershipGraph (m : ℕ) : SimpleGraph (Fin m ⊕ Finset (Fin m)) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inr s => a ∈ s
    | Sum.inr s, Sum.inl a => a ∈ s
    | _, _ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

/-- Adjacent inclusion and a finite same-carrier separator for every positive k. -/
def claim : Prop :=
  ∀ k : ℕ, 0 < k →
    (∀ (V : Type u) [Finite V] [DecidableEq V] (G : SimpleGraph V),
      InG k G → InG (k + 1) G) ∧
    (let Ω := Fin (64 * k ^ 2) ⊕ Finset (Fin (64 * k ^ 2))
     ∃ s : Finset Ω,
       InG (k + 1) ((membershipGraph (64 * k ^ 2)).comap (Subtype.val : s → Ω)) ∧
       ¬ InG k ((membershipGraph (64 * k ^ 2)).comap (Subtype.val : s → Ω)))

/-- The unconditional full positive-uniform hierarchy assertion. -/
theorem result : claim := by
  classical
  intro k hk
  constructor
  · intro V _ _ G h
    let := Fintype.ofFinite V
    let : BEq V := instBEqOfDecidableEq
    rcases h with ⟨_, w, v, hw, hv, hadj⟩
    let q := (Finset.univ : Finset V).toList
    have qc (z : V) : q.count z = 1 := by
      simp [q, Finset.nodup_toList]
    refine ⟨by omega, w ++ q, v ++ q, ?_, ?_, ?_⟩
    · intro z; simp [hw, qc]
    · intro z; simp [hv, qc]
    · intro a b hab
      simpa only [twoProjection, List.filter_append, List.append_left_inj]
        using hadj a b hab
  · let m := 64 * k ^ 2
    let Ω := Fin m ⊕ Finset (Fin m)
    let U := membershipGraph m
    let : BEq Ω := instBEqOfDecidableEq
    have nonuniversal : ¬ InG k U := by
      rintro ⟨_, w, v, hw, hv, hadj⟩
      have cut_data (u : List Ω) (hu : ∀ z, u.count z = k)
          (s : Finset (Fin m)) :
          ∃ f : Fin k → Fin (k * m + 1),
            leftCuts s u = List.ofFn (fun i => (f i).val) := by
        let r := u.filterMap Sum.getLeft?
        have rcount (a : Fin m) : r.count a = k := by
          calc
            r.count a = u.count (Sum.inl a) := by
              change (u.filterMap Sum.getLeft?).count a = _
              rw [List.count_filterMap, List.count_eq_countP]
              congr 1
              funext z
              cases z <;> simp
            _ = k := hu _
        have rall : r.toFinset = Finset.univ := by
          apply Finset.eq_univ_iff_forall.mpr
          intro a
          apply List.mem_toFinset.mpr
          apply List.count_pos_iff.mp
          rw [rcount]
          exact hk
        have rlength : r.length = k * m := by
          rw [← List.sum_toFinset_count_eq_length, rall]
          simp [rcount, Nat.mul_comm]
        have count_cuts (l : List Ω) :
            (leftCuts s l).length = l.count (Sum.inr s) := by
          induction l with
          | nil => simp [leftCuts]
          | cons z l ih =>
            cases z with
            | inl a => simpa [leftCuts, List.count_cons] using ih
            | inr t => by_cases h : t = s <;> simp [leftCuts, h, ih]
        have bound_cuts (l : List Ω) :
            ∀ n ∈ leftCuts s l, n ≤ (l.filterMap Sum.getLeft?).length := by
          induction l with
          | nil => simp [leftCuts]
          | cons z l ih =>
            cases z with
            | inl a =>
              intro n hn
              obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hn
              simpa [List.filterMap_cons, Sum.getLeft?_inl]
                using Nat.succ_le_succ (ih j hj)
            | inr t =>
              by_cases h : t = s
              · subst t
                intro n hn
                simp only [leftCuts, if_pos, List.mem_cons] at hn
                rcases hn with rfl | hn
                · exact Nat.zero_le _
                · simpa [List.filterMap_cons, Sum.getLeft?_inr] using ih n hn
              · simpa [leftCuts, h, List.filterMap_cons, Sum.getLeft?_inr] using ih
        have hlen : (leftCuts s u).length = k := (count_cuts u).trans (hu _)
        let f : Fin k → Fin (k * m + 1) := fun i =>
          ⟨(leftCuts s u).get (Fin.cast hlen.symm i), by
            have hb := bound_cuts u ((leftCuts s u).get (Fin.cast hlen.symm i))
              (List.get_mem (leftCuts s u) (Fin.cast hlen.symm i))
            change _ ≤ r.length at hb
            rw [rlength] at hb
            omega⟩
        refine ⟨f, ?_⟩
        exact (List.ofFn_get (leftCuts s u)).symm.trans
          (List.ofFn_congr hlen (leftCuts s u).get)
      have hbound : k * m + 1 ≤ 2 ^ (10 * k) := by
        have hcube : 1 ≤ k ^ 3 := one_le_pow₀ (by omega)
        calc
          k * m + 1 ≤ 128 * k ^ 3 := by dsimp [m]; nlinarith
          _ ≤ 128 * (2 ^ k) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) 3)
          _ = 2 ^ (7 + 3 * k) := by
            rw [Nat.mul_comm 3 k, Nat.pow_add, Nat.pow_mul]
          _ ≤ 2 ^ (10 * k) := Nat.pow_le_pow_right (by decide) (by omega)
      have hsignature : (k * m + 1) ^ k * (k * m + 1) ^ k < 2 ^ m := by
        calc
          (k * m + 1) ^ k * (k * m + 1) ^ k = (k * m + 1) ^ (2 * k) := by
            rw [two_mul, Nat.pow_add]
          _ ≤ (2 ^ (10 * k)) ^ (2 * k) := Nat.pow_le_pow_left hbound _
          _ = 2 ^ (20 * k ^ 2) := by rw [← Nat.pow_mul]; congr 1; ring
          _ < 2 ^ m := Nat.pow_lt_pow_right (by decide) (by
            dsimp [m]
            have hsq : 0 < k ^ 2 := Nat.pow_pos hk
            omega)
      let cw (s : Finset (Fin m)) : Fin k → Fin (k * m + 1) := (cut_data w hw s).choose
      let cv (s : Finset (Fin m)) : Fin k → Fin (k * m + 1) := (cut_data v hv s).choose
      let signature (s : Finset (Fin m)) := (cw s, cv s)
      obtain ⟨s, t, hne, hsig⟩ :=
        D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber signature (by
          simp only [Cardinal.mk_fintype, Fintype.card_prod, Fintype.card_pi_const,
            Fintype.card_fin, Fintype.card_finset]
          exact Nat.cast_lt.mpr hsignature)
      have hwcuts : leftCuts s w = leftCuts t w := by
        rw [(cut_data w hw s).choose_spec, (cut_data w hw t).choose_spec]
        change List.ofFn (fun i => (cw s i).val) = List.ofFn (fun i => (cw t i).val)
        rw [show cw s = cw t from congrArg Prod.fst hsig]
      have hvcuts : leftCuts s v = leftCuts t v := by
        rw [(cut_data v hv s).choose_spec, (cut_data v hv t).choose_spec]
        change List.ofFn (fun i => (cv s i).val) = List.ofFn (fun i => (cv t i).val)
        rw [show cv s = cv t from congrArg Prod.snd hsig]
      apply hne
      apply Finset.ext
      intro a
      have hs := hadj (Sum.inl a) (Sum.inr s) (by simp)
      have ht := hadj (Sum.inl a) (Sum.inr t) (by simp)
      change (a ∈ s ↔ _) at hs
      change (a ∈ t ↔ _) at ht
      rw [projection_eq_reconstruction a s w, projection_eq_reconstruction a s v] at hs
      rw [projection_eq_reconstruction a t w, projection_eq_reconstruction a t v] at ht
      have hinj (b : Finset (Fin m)) :
          Function.Injective (Sum.map (id : Fin m → Fin m) (fun _ : Unit => b)) :=
        Sum.map_injective.mpr ⟨Function.injective_id, fun _ _ _ => Subsingleton.elim _ _⟩
      rw [List.map_inj_right (hinj s)] at hs
      rw [List.map_inj_right (hinj t)] at ht
      rw [hwcuts, hvcuts] at hs
      exact hs.trans ht.symm
    have transport {A B : Type} [DecidableEq A] [DecidableEq B]
        (e : A ≃ B) (j : ℕ) (G : SimpleGraph B)
        (h : InG j (G.comap e)) : InG j G := by
      let : BEq A := instBEqOfDecidableEq
      let : BEq B := instBEqOfDecidableEq
      rcases h with ⟨hj, w, v, hw, hv, hadj⟩
      have proj (u : List A) (a b : A) :
          twoProjection (e a) (e b) (u.map e) = (twoProjection a b u).map e := by
        simp [twoProjection, List.filter_map, Function.comp_def, Bool.beq_eq_decide_eq]
      refine ⟨hj, w.map e, v.map e, ?_, ?_, ?_⟩
      · intro z
        calc
          (w.map e).count z = (w.map e).count (e (e.symm z)) := by
            rw [e.apply_symm_apply]
          _ = w.count (e.symm z) := List.count_map_of_injective w e e.injective _
          _ = j := hw _
      · intro z
        calc
          (v.map e).count z = (v.map e).count (e (e.symm z)) := by
            rw [e.apply_symm_apply]
          _ = v.count (e.symm z) := List.count_map_of_injective v e e.injective _
          _ = j := hv _
      · intro a b hab
        have hne : e.symm a ≠ e.symm b := e.symm.injective.ne hab
        have h := hadj (e.symm a) (e.symm b) hne
        have pw := proj w (e.symm a) (e.symm b)
        have pv := proj v (e.symm a) (e.symm b)
        simp only [e.apply_symm_apply] at pw pv
        rw [pw, pv, List.map_inj_right e.injective]
        simpa only [SimpleGraph.comap_adj, e.apply_symm_apply] using h
    let P (n : ℕ) : Prop := ∃ s : Finset Ω, s.card = n ∧
      ¬ InG k (U.comap (Subtype.val : s → Ω))
    have hex : ∃ n, P n := by
      refine ⟨Fintype.card Ω, Finset.univ, Finset.card_univ, ?_⟩
      intro h
      let e : (Finset.univ : Finset Ω) ≃ Ω :=
        { toFun := Subtype.val
          invFun := fun z => ⟨z, Finset.mem_univ z⟩
          left_inv := by intro z; rfl
          right_inv := by intro z; rfl }
      exact nonuniversal (transport e k U h)
    obtain ⟨s, hs_card, hs_bad⟩ := Nat.find_spec hex
    have hs_nonempty : s.Nonempty := by
      by_contra he
      have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      subst s
      apply hs_bad
      refine ⟨hk, ([] : List (∅ : Finset Ω)), [], ?_, ?_, ?_⟩
      · intro z; exact (Finset.notMem_empty z.val z.property).elim
      · intro z; exact (Finset.notMem_empty z.val z.property).elim
      · intro z; exact (Finset.notMem_empty z.val z.property).elim
    obtain ⟨a, ha⟩ := hs_nonempty
    let t := s.erase a
    have ht_good : InG k (U.comap (Subtype.val : t → Ω)) := by
      by_contra hbad
      have hlt : t.card < Nat.find hex := by
        rw [← hs_card]
        exact Finset.card_erase_lt_of_mem ha
      exact Nat.find_min hex hlt ⟨t, rfl, hbad⟩
    let x : s := ⟨a, ha⟩
    let d : t ≃ {y : s // y ≠ x} :=
      { toFun := fun z => ⟨⟨z.val, (Finset.mem_erase.mp z.property).2⟩, by
          intro heq
          exact (Finset.mem_erase.mp z.property).1 (congrArg Subtype.val heq)⟩
        invFun := fun y => ⟨y.val.val, Finset.mem_erase.mpr ⟨by
          intro heq
          exact y.property (Subtype.ext heq), y.val.property⟩⟩
        left_inv := by intro z; rfl
        right_inv := by intro y; rfl }
    let E : Option t ≃ s := (Equiv.optionCongr d).trans (Equiv.optionSubtypeNe x)
    let H := U.comap (Subtype.val : s → Ω)
    let K := H.comap E
    have deletion : K.comap Option.some = U.comap (Subtype.val : t → Ω) := by
      apply SimpleGraph.ext
      funext z y
      simp [K, H, E, Equiv.optionCongr, d, SimpleGraph.comap_adj]
    have extended : InG (k + 1) K := vertex_extension k K (by rw [deletion]; exact ht_good)
    exact ⟨s, transport E (k + 1) H extended, hs_bad⟩

end D5.S1.Words.GraphRepresentation.UniformHierarchy
