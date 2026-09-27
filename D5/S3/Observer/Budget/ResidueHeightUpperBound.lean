/- GID: D5/S3/Observer/Budget/ResidueHeightUpperBound
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ResidueHeightUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete residue nodes admit uniformly height-bounded identifying protocols. -/

import D5.S3.Observer.Budget.ResidueChildPrefixStructure

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Observer.Budget.ResiduePosteriorClosure
open D5.S3.Observer.Budget.ResidueLeafOptimality
open D5.S3.Observer.Budget.ResidueChildPrefixStructure
open D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

namespace D5.S3.Observer.Budget.ResidueHeightUpperBound

/-- Every complete node has an actual identifying residue protocol whose trace
on each of its targets has length at most its remaining height times `p - 1`. -/
theorem residue_height_upper_bound (p e : ℕ) [Fact p.Prime]
    (d : ℕ) (hd : d ≤ e) (b : ZMod (p ^ d)) :
    ∃ T : PassiveProtocol (ZMod (p ^ e)) (fun _ => ℕ),
      Set.InjOn (runPassiveProtocol (residueReadout p e) T)
        (node p e d hd b : Set (ZMod (p ^ e))) ∧
      ∀ a ∈ node p e d hd b,
        (runPassiveProtocol (residueReadout p e) T a).length ≤ (e - d) * (p - 1) := by
  classical
  have hp : p.Prime := Fact.out
  have positive : ∀ _ : ZMod (p ^ e), (0 : ℚ) < (p ^ e : ℚ)⁻¹ :=
    fun _ => inv_pos.mpr (pow_pos (by exact_mod_cast hp.pos) _)
  have normalized : ∑ _ : ZMod (p ^ e), (p ^ e : ℚ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_pow]
    exact mul_inv_cancel₀ (ne_of_gt (pow_pos (by exact_mod_cast hp.pos) _))
  have geo := residue_posterior_closure p e (fun _ => (p ^ e : ℚ)⁻¹) positive normalized
  have cards := geo.2.2.2.1
  have childrenFacts := geo.2.2.2.2.1
  clear geo positive normalized
  generalize hh : e - d = h
  induction h generalizing d with
  | zero =>
    have small : (node p e d hd b).card ≤ 1 := by rw [cards, hh]; simp
    refine ⟨.stop, ?_, ?_⟩
    · intro a ha a' ha' _
      exact Finset.card_le_one.mp small a ha a' ha'
    · intro a _
      simp only [runPassiveProtocol, List.length_nil, zero_le]
  | succ h ih =>
    by_cases hz : h = 0
    · have he : e = d + 1 := by omega
      subst e
      let s := node p (d + 1) d hd b
      have hs : ∀ a ∈ s, ∀ a' ∈ s, Nat.ModEq (p ^ d) a.val a'.val := by
        intro a ha a' ha'
        have eqp : primePowerProjection p hd a = primePowerProjection p hd a' :=
          (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp ha').2.symm
        simpa only [primePowerProjection, ZMod.castHom_apply, ZMod.cast_eq_val,
          ZMod.natCast_eq_natCast_iff] using eqp
      let o : Fin s.card ≃ s := s.equivFin.symm
      obtain ⟨T, ident, lengths, _⟩ :=
        (leaf_sibling_weighted_minimum p d hp s hs (fun _ => 1)
          (by intros; norm_num) o (fun _ _ _ => le_rfl)).1 o
      refine ⟨T, fun a ha a' ha' heq => ident a ha a' ha' heq, ?_⟩
      intro a ha
      obtain ⟨i, hi⟩ := o.surjective ⟨a, ha⟩
      have len := lengths i
      rw [hi] at len
      have scard : s.card = p := by
        dsimp only [s]
        rw [cards]
        simp
      rw [len]
      simpa only [scard, hz, Nat.zero_add, Nat.one_mul] using
        (Nat.min_le_right (i.val + 1) (s.card - 1))
    · have hde : d < e := by omega
      have hnonleaf : d + 1 < e := by omega
      let X := ZMod (p ^ e)
      let Tree := PassiveProtocol X (fun _ => ℕ)
      let R := runPassiveProtocol (residueReadout p e)
      let I := children p d b
      let C := node p e (d + 1) (Nat.succ_le_of_lt hde)
      have icard : I.card = p := (childrenFacts d hde b).1
      have ine : I.Nonempty := Finset.card_pos.mp (by simpa only [icard] using hp.pos)
      have actualChildren : ∀ j : I, ∃ U : Tree,
          Set.InjOn (R U) (C j.val : Set X) ∧
          (∀ a ∈ C j.val, (R U a).length ≤ h * (p - 1)) ∧
          ∃ c ∈ C j.val, ∃ next : ℕ → Tree, U = .query c next := by
        intro j
        obtain ⟨T, ident, bound⟩ :=
          ih (d + 1) (Nat.succ_le_of_lt hde) j.val (by omega)
        have alone : siblings p e d hde {j.val} = C j.val := by
          simp only [siblings, C, node, Finset.mem_singleton]
        obtain ⟨o, U, P, c, next, spec, _⟩ :=
          (residue_child_prefix_structure p e d hde b {j.val}
            (Finset.singleton_nonempty _) (Finset.singleton_subset_iff.mpr j.property)).1 T
              (by simpa only [alone] using ident)
        let i : Fin ({j.val} : Finset (ZMod (p ^ (d + 1)))).card := ⟨0, by simp⟩
        have label : (o i).val = j.val := Finset.mem_singleton.mp (o i).property
        obtain ⟨hc, hu, head, _, traces⟩ := spec i
        rw [label] at hc hu traces
        refine ⟨U i, hu, ?_, c i, hc, next i, ?_⟩
        · intro a ha
          have lengthEq := congrArg List.length (traces a ha)
          rw [List.length_append] at lengthEq
          have oldBound := bound a ha
          dsimp only [R]
          omega
        · exact head (Or.inr ⟨Finset.card_singleton _, hnonleaf⟩)
      choose U ident bound heads using actualChildren
      let o : Fin I.card ≃ I := I.equivFin.symm
      obtain ⟨c, next, V, _, identifies, traces⟩ :=
        (residue_child_prefix_structure p e d hde b I ine (fun _ hz => hz)).2 o
          (fun i => U (o i)) (fun i => ident (o i)) (fun i _ => heads (o i))
      have parent : siblings p e d hde I = node p e d hd b := by
        rw [(childrenFacts d hde b).2.2.2, (childrenFacts d hde b).2.1]
      refine ⟨V, ?_, ?_⟩
      · simpa only [parent] using identifies
      · intro a ha
        have haI : a ∈ I.biUnion C := by
          rw [(childrenFacts d hde b).2.1]
          exact ha
        obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp haI
        obtain ⟨i, hi⟩ := o.surjective ⟨j, hj⟩
        have label : (o i).val = j := congrArg Subtype.val hi
        have haj' : a ∈ C (o i).val := by simpa only [label] using haj
        have len := (traces i a haj').2
        have childBound := bound (o i) a haj'
        have indexBound : i.val ≤ p - 1 := by have := i.isLt; omega
        rw [len]
        calc
          i.val + (R (U (o i)) a).length ≤ (p - 1) + h * (p - 1) :=
            Nat.add_le_add indexBound childBound
          _ = (h + 1) * (p - 1) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

#print axioms residue_height_upper_bound

end D5.S3.Observer.Budget.ResidueHeightUpperBound
