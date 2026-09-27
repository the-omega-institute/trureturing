/- GID: D5/S3/Observer/Budget/ResidueLeafOptimality
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ResidueLeafOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sibling residue queries attain the sorted weighted identification minimum. -/

import D5.S3.Observer.Budget.EqualityQueryScheduleNormalForm
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Tactic

set_option autoImplicit false
namespace D5.S3.Observer.Budget.ResidueLeafOptimality
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.Observer.Budget.EqualityQueryScheduleNormalForm
open scoped BigOperators

/-- The greatest congruence depth of the actual prime-power residues, with
zero and full depth both included. -/
def residueReadout (p e : ℕ) (center target : ZMod (p ^ e)) : ℕ :=
  ((Finset.range (e + 1)).filter fun i =>
    target.val % p ^ i = center.val % p ^ i).sup id

/-- Every sibling-leaf enumeration is attained by an actual identifying residue
protocol with the equality scan's exact center trace and capped position costs.
A mass-antitone enumeration gives the least weighted cost among all actual
identifying protocols, allowing arbitrary centers, repetitions and stopping. -/
theorem leaf_sibling_weighted_minimum (p d : ℕ) (hp : p.Prime) (s : Finset (ZMod (p ^ (d + 1))))
    (siblings : ∀ a ∈ s, ∀ b ∈ s, Nat.ModEq (p ^ d) a.val b.val)
    (mass : ZMod (p ^ (d + 1)) → ℚ) (positive : ∀ a ∈ s, 0 < mass a)
    (o : Fin s.card ≃ s) (sorted : Antitone (fun i => mass (o i).val)) :
    (∀ order : Fin s.card ≃ s,
      ∃ tree : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => ℕ),
        (∀ a ∈ s, ∀ b ∈ s,
          runPassiveProtocol (residueReadout p (d + 1)) tree a =
            runPassiveProtocol (residueReadout p (d + 1)) tree b → a = b) ∧
        (∀ i : Fin s.card,
          (runPassiveProtocol (residueReadout p (d + 1)) tree (order i).val).length =
            min (i.val + 1) (s.card - 1)) ∧
        (∀ a ∈ s,
          (runPassiveProtocol (residueReadout p (d + 1)) tree a).map Sigma.fst =
            (runPassiveProtocol equalityReadout
              (scan (List.ofFn (fun i => (order i).val))) a).map Sigma.fst)) ∧
    IsLeast {v : ℚ | ∃ tree : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => ℕ),
      (∀ a ∈ s, ∀ b ∈ s,
        runPassiveProtocol (residueReadout p (d + 1)) tree a =
          runPassiveProtocol (residueReadout p (d + 1)) tree b → a = b) ∧
      v = ∑ a : s, mass a.val *
        ((runPassiveProtocol (residueReadout p (d + 1)) tree a.val).length : ℚ)}
      (∑ i : Fin s.card, mass (o i).val * (min (i.val + 1) (s.card - 1) : ℕ)) := by
  classical
  have equivalence :
    (∀ tree : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => ℕ),
      (∀ a ∈ s, ∀ b ∈ s,
        runPassiveProtocol (residueReadout p (d + 1)) tree a =
          runPassiveProtocol (residueReadout p (d + 1)) tree b → a = b) →
      ∃ other : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => Bool),
        (∀ a ∈ s, ∀ b ∈ s,
          runPassiveProtocol equalityReadout other a =
            runPassiveProtocol equalityReadout other b → a = b) ∧
        (∀ a ∈ s,
          (runPassiveProtocol equalityReadout other a).map Sigma.fst =
            (runPassiveProtocol (residueReadout p (d + 1)) tree a).map Sigma.fst) ∧
        (∀ a ∈ s,
          (runPassiveProtocol equalityReadout other a).length =
            (runPassiveProtocol (residueReadout p (d + 1)) tree a).length)) ∧
    (∀ tree : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => Bool),
      (∀ a ∈ s, ∀ b ∈ s,
        runPassiveProtocol equalityReadout tree a =
          runPassiveProtocol equalityReadout tree b → a = b) →
      ∃ other : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => ℕ),
        (∀ a ∈ s, ∀ b ∈ s,
          runPassiveProtocol (residueReadout p (d + 1)) other a =
            runPassiveProtocol (residueReadout p (d + 1)) other b → a = b) ∧
        (∀ a ∈ s,
          (runPassiveProtocol (residueReadout p (d + 1)) other a).map Sigma.fst =
            (runPassiveProtocol equalityReadout tree a).map Sigma.fst) ∧
        (∀ a ∈ s,
          (runPassiveProtocol (residueReadout p (d + 1)) other a).length =
            (runPassiveProtocol equalityReadout tree a).length)) := by
    let : NeZero (p ^ (d + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have full (a c : ZMod (p ^ (d + 1))) :
        Nat.ModEq (p ^ (d + 1)) a.val c.val ↔ a = c := by
      constructor
      · intro h
        exact ZMod.val_injective _ (h.eq_of_lt_of_lt a.val_lt c.val_lt)
      · rintro rfl; rfl
    have top (a c : ZMod (p ^ (d + 1))) :
        residueReadout p (d + 1) c a = d + 1 ↔ a = c := by
      constructor
      · intro h
        by_contra hn
        have bound : residueReadout p (d + 1) c a ≤ d := by
          apply Finset.sup_le
          intro i hi
          obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
          have hil := Finset.mem_range.mp hi
          have hine : i ≠ d + 1 := by
            rintro rfl
            exact hn ((full a c).mp he)
          dsimp
          omega
        omega
      · rintro rfl
        apply le_antisymm
        · apply Finset.sup_le
          intro i hi
          have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
          dsimp
          omega
        · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨by simp, rfl⟩)
    have miss (c a b : ZMod (p ^ (d + 1))) (ha : a ∈ s) (hb : b ∈ s)
        (hac : a ≠ c) (hbc : b ≠ c) :
        residueReadout p (d + 1) c a = residueReadout p (d + 1) c b := by
      unfold residueReadout
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor <;> rintro ⟨hi, he⟩
      · refine ⟨hi, ?_⟩
        by_cases hit : i = d + 1
        · subst i; exact (hac ((full a c).mp he)).elim
        · have hid : i ≤ d := by omega
          exact ((siblings a ha b hb).of_dvd (pow_dvd_pow p hid)).symm.trans he
      · refine ⟨hi, ?_⟩
        by_cases hit : i = d + 1
        · subst i; exact (hbc ((full b c).mp he)).elim
        · have hid : i ≤ d := by omega
          exact ((siblings a ha b hb).of_dvd (pow_dvd_pow p hid)).trans he
    have simulate : ∀ (R T : Type)
        (q : ZMod (p ^ (d + 1)) → ZMod (p ^ (d + 1)) → R)
        (r : ZMod (p ^ (d + 1)) → ZMod (p ^ (d + 1)) → T)
        (decode : ZMod (p ^ (d + 1)) → T → R),
        (∀ c a, a ∈ s → q c a = decode c (r c a)) →
        ∀ tree : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => R),
        ∃ other : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => T),
          ∀ a ∈ s, runPassiveProtocol q tree a =
            (runPassiveProtocol r other a).map (fun x => ⟨x.1, decode x.1 x.2⟩) := by
      intro R T q r decode agrees tree
      induction tree with
      | stop => exact ⟨.stop, fun _ _ => rfl⟩
      | query c next ih =>
        choose children children_ok using ih
        refine ⟨.query c (fun t => children (decode c t)), ?_⟩
        intro a ha
        simp only [runPassiveProtocol, List.map_cons]
        rw [agrees c a ha, children_ok _ a ha]
    have transport : ∀ (R T : Type)
        (q : ZMod (p ^ (d + 1)) → ZMod (p ^ (d + 1)) → R)
        (r : ZMod (p ^ (d + 1)) → ZMod (p ^ (d + 1)) → T)
        (decode : ZMod (p ^ (d + 1)) → T → R),
        (∀ c a, a ∈ s → q c a = decode c (r c a)) →
        ∀ tree : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => R),
        (∀ a ∈ s, ∀ b ∈ s, runPassiveProtocol q tree a =
          runPassiveProtocol q tree b → a = b) →
        ∃ other : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => T),
          (∀ a ∈ s, ∀ b ∈ s, runPassiveProtocol r other a =
            runPassiveProtocol r other b → a = b) ∧
          (∀ a ∈ s, (runPassiveProtocol r other a).map Sigma.fst =
            (runPassiveProtocol q tree a).map Sigma.fst) ∧
          (∀ a ∈ s, (runPassiveProtocol r other a).length =
            (runPassiveProtocol q tree a).length) := by
      intro R T q r decode agrees tree identifies
      obtain ⟨other, eqn⟩ := simulate R T q r decode agrees tree
      refine ⟨other, ?_, ?_, ?_⟩
      · intro a ha b hb same
        apply identifies a ha b hb
        rw [eqn a ha, eqn b hb, same]
      · intro a ha
        rw [eqn a ha, List.map_map]
        rfl
      · intro a ha
        rw [eqn a ha, List.length_map]
    constructor
    · let decode (c : ZMod (p ^ (d + 1))) (hit : Bool) : ℕ :=
        if hit then d + 1 else
          if h : ∃ a ∈ s, a ≠ c then residueReadout p (d + 1) c h.choose else 0
      apply transport ℕ Bool (residueReadout p (d + 1)) equalityReadout decode
      intro c a ha
      by_cases hac : a = c
      · subst a
        simp [decode, equalityReadout, (top c c).mpr rfl]
      · have witness : ∃ b ∈ s, b ≠ c := ⟨a, ha, hac⟩
        simp only [decode, equalityReadout, hac, decide_false, Bool.false_eq_true,
          ↓reduceIte, dif_pos witness]
        exact miss c a witness.choose ha witness.choose_spec.1 hac witness.choose_spec.2
    · apply transport Bool ℕ equalityReadout (residueReadout p (d + 1))
        (fun _ n => decide (n = d + 1))
      intro c a _
      simp only [equalityReadout, top a c]
  let coeff : Fin s.card → ℚ := fun i => (min (i.val + 1) (s.card - 1) : ℕ)
  have monotone_coeff : Monotone coeff := by
    intro i j hij
    dsimp [coeff]
    exact_mod_cast min_le_min_right (s.card - 1) (Nat.add_le_add_right hij 1)
  have realize (order : Fin s.card ≃ s) :
      ∃ tree : PassiveProtocol (ZMod (p ^ (d + 1))) (fun _ => ℕ),
        (∀ a ∈ s, ∀ b ∈ s,
          runPassiveProtocol (residueReadout p (d + 1)) tree a =
            runPassiveProtocol (residueReadout p (d + 1)) tree b → a = b) ∧
        (∀ i : Fin s.card,
          (runPassiveProtocol (residueReadout p (d + 1)) tree (order i).val).length =
            min (i.val + 1) (s.card - 1)) ∧
        (∀ a ∈ s,
          (runPassiveProtocol (residueReadout p (d + 1)) tree a).map Sigma.fst =
            (runPassiveProtocol equalityReadout
              (scan (List.ofFn (fun i => (order i).val))) a).map Sigma.fst) := by
    let L := List.ofFn (fun i => (order i).val)
    have nd : L.Nodup := List.nodup_ofFn.mpr (Subtype.val_injective.comp order.injective)
    have length : L.length = s.card := by simp [L]
    have mem (a : ZMod (p ^ (d + 1))) : a ∈ L ↔ a ∈ s := by
      simp only [L, List.mem_ofFn]
      constructor
      · rintro ⟨i, rfl⟩; exact (order i).property
      · intro ha
        exact ⟨order.symm ⟨a, ha⟩, by simp⟩
    obtain ⟨ident, depth⟩ := scan_identifies_with_exact_depth L nd
    obtain ⟨tree, ht, centers, hl⟩ := equivalence.2 (scan L)
      (fun a ha b hb => ident a ((mem a).mpr ha) b ((mem b).mpr hb))
    refine ⟨tree, ht, ?_, centers⟩
    intro i
    rw [hl _ (order i).property, depth _ ((mem _).mpr (order i).property), length]
    have index := List.get_idxOf nd ⟨i.val, by simpa [length] using i.isLt⟩
    have get : L.get ⟨i.val, by simpa [length] using i.isLt⟩ = (order i).val := by
      simp [L]
    rw [get] at index
    rw [index]
  refine ⟨realize, ?_⟩
  constructor
  · obtain ⟨tree, ident, depth, _⟩ := realize o
    refine ⟨tree, ident, ?_⟩
    rw [← o.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [depth i]
  · rintro v ⟨tree, ident, rfl⟩
    obtain ⟨eqtree, identifies, _, lengths⟩ := equivalence.1 tree ident
    obtain ⟨L, nd, exhaustive, _, _, faster⟩ :=
      equality_protocol_schedule_normal_form eqtree s identifies
    have length : L.length = s.card := by
      rw [← exhaustive, List.toFinset_card_of_nodup nd]
    have mem (a : ZMod (p ^ (d + 1))) : a ∈ L ↔ a ∈ s := by
      rw [← exhaustive, List.mem_toFinset]
    let indexed : Fin L.length ≃ s := (nd.getEquiv L).trans
      (Equiv.subtypeEquivRight fun a => mem a)
    let other : Fin s.card ≃ s := (finCongr length.symm).trans indexed
    have get (i : Fin s.card) : (other i).val =
        L.get ⟨i.val, by simpa [length] using i.isLt⟩ := rfl
    have index (i : Fin s.card) : L.idxOf (other i).val = i.val := by
      rw [get]
      exact List.get_idxOf nd _
    have pointwise (i : Fin s.card) :
        coeff i ≤ ((runPassiveProtocol (residueReadout p (d + 1)) tree
          (other i).val).length : ℚ) := by
      have bound := faster (other i).val (other i).property
      have scanDepth := (scan_identifies_with_exact_depth L nd).2
        (other i).val ((mem _).mpr (other i).property)
      rw [scanDepth, length, index i, lengths _ (other i).property] at bound
      dsimp [coeff]
      exact_mod_cast bound
    let perm : Equiv.Perm (Fin s.card) := other.trans o.symm
    have rearrange := (sorted.antivary monotone_coeff).sum_mul_le_sum_comp_perm_mul
      (σ := perm)
    calc
      _ ≤ ∑ i : Fin s.card, mass (other i).val * coeff i := by
        simpa only [perm, Equiv.trans_apply, Equiv.apply_symm_apply] using rearrange
      _ ≤ ∑ i : Fin s.card, mass (other i).val *
          ((runPassiveProtocol (residueReadout p (d + 1)) tree (other i).val).length : ℚ) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (pointwise i)
          (positive _ (other i).property).le)
      _ = _ := other.sum_comp (fun a : s => mass a.val *
        ((runPassiveProtocol (residueReadout p (d + 1)) tree a.val).length : ℚ))

#print axioms leaf_sibling_weighted_minimum
end D5.S3.Observer.Budget.ResidueLeafOptimality
