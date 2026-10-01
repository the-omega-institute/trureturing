import D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum
import Reg.Support.DependentFamily
import Reg.D5.S1.Words.Attractors.FiniteWordAttractors

open _root_.D5.S1.Words.Attractors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum
noncomputable section

abbrev signature : Signature where
  Params := Σ k : Nat, Fin k → Nat
  State := fun p => List (Fin p.1)
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ w => gamma w)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat),
    1 ≤ c ⟨0, by omega⟩ → 1 ≤ c ⟨k - 1, by omega⟩ → CyclicMaximal c →
    ∀ m : Nat, 0 < m →
      (∀ i : Nat, i ≤ k - 2 → cyclicLength (by omega) c i ≤ m →
        m < cyclicLength (by omega) c (i + 1) →
          R.readout 0 ⟨k, c⟩ (cyclicPrefix (k := k) (by omega) c m) = i + 1) ∧
      (cyclicLength (by omega) c (k - 1) ≤ m →
        R.readout 1 ⟨k, c⟩ (cyclicPrefix (k := k) (by omega) c m) = k)

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let c : Fin 2 → Nat := fun _ => 1
  have hcyc : CyclicMaximal c := by
    intro r
    have hd : List.ofFn (cyclicDigit c) = [1, 0] := by decide
    rw [hd, ← List.rotate_mod]
    have hr : r % 2 = 0 ∨ r % 2 = 1 := by have := Nat.mod_lt r (by omega : 0 < 2); omega
    simp only [List.length_cons, List.length_nil] at *
    rcases hr with hr | hr
    · rw [hr]; decide
    · rw [hr]; decide
  have hh := (h (by omega : 2 ≤ 2) c (by decide) (by decide) hcyc 1 (by omega)).1
    0 (by omega) (by decide) (by decide)
  norm_num [rejected, realize] at hh

def rejectedAt (i : Fin 2) : Realization signature :=
  realize signature (fun j _ w => if j = i then 0 else gamma w) (fun e => nomatch e)

theorem rejectedAt_law (i : Fin 2) : ¬ arena.Law (rejectedAt i) := by
  intro h
  let c : Fin 2 → Nat := fun _ => 1
  have hcyc : CyclicMaximal c := by
    intro r
    have hd : List.ofFn (cyclicDigit c) = [1, 0] := by decide
    rw [hd, ← List.rotate_mod]
    have hr : r % 2 = 0 ∨ r % 2 = 1 := by have := Nat.mod_lt r (by omega : 0 < 2); omega
    simp only [List.length_cons, List.length_nil] at *
    rcases hr with hr | hr
    · rw [hr]; decide
    · rw [hr]; decide
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with hi | hi
  · subst i
    have hh := (h (by omega : 2 ≤ 2) c (by decide) (by decide) hcyc 1 (by omega)).1
      0 (by omega) (by decide) (by decide)
    norm_num [rejectedAt, realize] at hh
  · subst i
    have hh := (h (by omega : 2 ≤ 2) c (by decide) (by decide) hcyc 2 (by omega)).2
      (by decide)
    norm_num [rejectedAt, realize] at hh

def registration : Registration arena
    (∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat),
      1 ≤ c ⟨0, by omega⟩ → 1 ≤ c ⟨k - 1, by omega⟩ → CyclicMaximal c →
        CyclicAttractorMinimum (by omega) c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro k hk c h0 hl hc; exact result hk c h0 hl hc, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedAt i, ?_, rfl, rejectedAt_law i⟩
      intro j h
      simp [rejectedAt, actual, realize, h]
    · intro e; exact nomatch e
  dependence := by
    intro i
    let z : Fin 2 := 0
    have hnil : IsAttractor ([] : List (Fin 2)) ∅ := by
      refine ⟨by simp, ?_⟩
      intro a l hl ha; simp only [List.length_nil] at ha; omega
    have hg0 : gamma ([] : List (Fin 2)) = 0 := by
      have h := (attractor_minimum ([] : List (Fin 2))).2.1 ∅ hnil
      simpa using h
    have hs : IsAttractor [z] {0} := by
      refine ⟨by simp, ?_⟩
      intro a l hl ha
      simp only [List.length_singleton] at ha
      have ha0 : a = 0 := by omega
      have hl1 : l = 1 := by omega
      subst a; subst l
      exact ⟨0, 0, by simp, by simp, le_rfl, by omega, rfl⟩
    have hg1 : gamma [z] = 1 := by
      have lo := (attractor_minimum [z]).2.2
      have hi := (attractor_minimum [z]).2.1 {0} hs
      simp only [List.toFinset_cons, List.toFinset_nil] at lo
      simp at lo hi
      omega
    refine ⟨⟨2, fun _ => 1⟩, [], [z], ?_⟩
    simp only [actual, realize, hg0, hg1]
    decide

def selection : LeanInformationAudit.SourceSelection where
  owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum
  coordinates := #[0, 2]
  readouts := #[
    {path := #["body", "body", "body", "body", "body", "body", "body", "body",
      "fn", "arg", "body", "body", "body", "body", "fn", "arg"],
      stateOperand := some #["arg"]},
    {path := #["body", "body", "body", "body", "body", "body", "body", "body",
      "arg", "body", "fn", "arg"], stateOperand := some #["arg"]}]


register_information_theorem result in arena
  readout via (realize signature (fun _ _ w => gamma w) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

#print axioms registration
end
end Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum


universe u
namespace Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits
open TrureTuring.Raney
open _root_.D5.S1.Words.Powers
open _root_.Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits
noncomputable section

namespace Fractional
abbrev signature : Signature where
  Params := Nat
  State := fun k => List (Fin k)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ k => List (Fin k)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ w => w.dropLast) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ w => w) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩)
    (hcyc : CyclicMaximal c) (n : Nat),
R.readout () k (cyclicWord (by omega) c (n + 1)) <+:
      wordPower (c ⟨0, by omega⟩ + 1) (cyclicWord (by omega) c n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : CyclicMaximal (fun _ : Fin 2 => 1) := by
    intro r
    have hd : List.ofFn (cyclicDigit (fun _ : Fin 2 => 1)) = [1,0] := by decide
    rw [hd, ← List.rotate_mod]
    have hr : r % 2 = 0 ∨ r % 2 = 1 := by have := Nat.mod_lt r (by omega : 0 < 2); omega
    simp only [List.length_cons,List.length_nil] at *
    rcases hr with hr | hr <;> rw [hr] <;> decide
  have hh := h (by omega : 2 ≤ 2) (fun _ => 1) (by decide) (by decide) hc 0
  change ([0,1] : List (Fin 2)) <+: [0,0] at hh
  have := hh.getElem (by decide : 1 < ([0,1] : List (Fin 2)).length)
  simp at this

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_fractional_prefix, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨2, [], [0,0], by cases i; decide⟩

register_information_theorem cyclic_fractional_prefix in arena
  readout via (realize signature (fun _ _ w => w.dropLast) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum
    coordinates := #[0]
    readouts := #[{path := #["body","body","body","body","body","body","body","fn","arg"], stateOperand := some #["arg"]}] })
  escape continues (open)


end Fractional

namespace Structure
abbrev signature : Signature where
  Params := Σ k : Nat, {c : Fin k → Nat // 2 ≤ k}
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p n => cyclicLength (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩),
(∀ (n : Nat) (a : Fin k),
      morphismPower (cyclicMorphism (by omega) c) n [a] =
        cyclicInterior (by omega) c n a ++
          [⟨(a.val + n) % k, Nat.mod_lt _ (by omega)⟩]) ∧
    (∀ n, cyclicWord (by omega) c n <+: cyclicWord (by omega) c (n + 1)) ∧
    (∀ n, cyclicLength (by omega) c n < cyclicLength (by omega) c (n + 1)) ∧
    (∀ n, n + 1 ≤ R.readout () ⟨k,⟨c,hk⟩⟩ n) ∧
    (Monotone fun n => cyclicLength (by omega) c (n + 1) - cyclicLength (by omega) c n) ∧
    (∀ (m n : Nat), m ≤ cyclicLength (by omega) c n →
      cyclicPrefix (by omega) c m = (cyclicWord (by omega) c n).take m)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (by omega : 2 ≤ 2) (fun _ => 1) (by decide) (by decide)).2.2.2.1 0
  change 0+1 ≤ 0 at hh
  exact Nat.not_succ_le_zero 0 hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_iterate_structure, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨2,⟨fun _ => 1,by omega⟩⟩,0,1,by cases i; decide⟩

register_information_theorem cyclic_iterate_structure in arena
  readout via (realize signature (fun _ p n => cyclicLength (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum
    coordinates := #[0,1,2]
    readouts := #[{path := #["body","body","body","body","body","arg","arg","arg","fn","arg","body","arg"], stateBinder := 5}] })
  escape continues (open)


end Structure

namespace Recurrence
abbrev signature : Signature where
  Params := Σ k : Nat, {c : Fin k → Nat // 2 ≤ k}
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => List (Fin p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p n => cyclicWord (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩),
(∀ (n : Nat) (hn : n < k), R.readout () ⟨k,⟨c,hk⟩⟩ n =
      cyclicBlockProduct (by omega) c n n hn.le ++ [⟨n, hn⟩]) ∧
    (∀ (n : Nat), k ≤ n → cyclicWord (by omega) c n =
      cyclicBlockProduct (by omega) c n k le_rfl)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (by omega : 2 ≤ 2) (fun _ => 1) (by decide) (by decide)).1 0 (by omega)
  change ([] : List (Fin 2)) = [0] at hh
  simp at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_word_recurrence, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨2,⟨fun _ => 1,by omega⟩⟩,0,1,by cases i; decide⟩

register_information_theorem cyclic_word_recurrence in arena
  readout via (realize signature (fun _ p n => cyclicWord (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum
    coordinates := #[0,1,2]
    readouts := #[{path := #["body","body","body","body","body","fn","arg","body","body","fn","arg"], stateBinder := 5}] })
  escape continues (open)


end Recurrence

end
end Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits
