import D5.S1.Digit.ZeckendorfRawWindow
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S1.Words

namespace Reg.D5.S1.Digit.ZeckendorfRawWindow
noncomputable section
open Classical

abbrev coordinateSignature : Signature where
  Params := Unit
  State := fun _ => List (Fin 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateActual : Realization coordinateSignature := realize coordinateSignature
  (fun _ _ w => support w) (fun e => nomatch e)

abbrev coordinateArena : Arena where
  signature := coordinateSignature
  Law R := ∀ w : List (Fin 2), NoAdjacentOnes w →
    (R.readout () () w).IsZeckendorfRep ∧
      (∀ k ∈ R.readout () () w, k < w.length + 2) ∧
      ((R.readout () () w).map Nat.fib).sum = (fibPair w).1 ∧
      ((R.readout () () w).map (fun k => Nat.fib (k + 1))).sum = (fibPair w).2

def coordinateRejected : Realization coordinateSignature := realize coordinateSignature
  (fun _ _ _ => [2]) (fun e => nomatch e)

theorem coordinateRejectedLaw : ¬ coordinateArena.Law coordinateRejected := by
  intro h
  have hh := (h [] (by simp [NoAdjacentOnes])).2.2.2
  norm_num [coordinateRejected, realize, fibPair] at hh

def coordinateRegistration : Registration coordinateArena (coordinateArena.Law coordinateActual) where
  actual := coordinateActual
  bridge := Iff.rfl
  variation := ⟨source_word_coordinates, coordinateRejected, coordinateRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coordinateRejected, ?_, rfl, coordinateRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), [], [1], ?_⟩
    simp [coordinateActual, coordinateRejected, realize, support]

register_information_theorem source_word_coordinates in coordinateArena
  readout via (realize coordinateSignature (fun _ _ w => support w) (fun e => nomatch e))
  realizes coordinateRegistration
  escape from source ({
    owner := `D5.S1.Digit.ZeckendorfRawWindow
    coordinates := #[]
    readouts := #[{path := #["body", "body", "fn", "arg", "arg"], stateBinder := 0}]})
  escape continues (open)

abbrev expansionSignature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List (Bool × Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def expansionActual : Realization expansionSignature := realize expansionSignature
  (fun _ n t => ((List.range t).map (fun i => q (n + i))).flatMap mu)
  (fun e => nomatch e)

abbrev expansionArena : Arena where
  signature := expansionSignature
  Law R := ∀ n t : ℕ,
    R.readout () n t =
      (List.range (goldenSubstStart (n + t) - goldenSubstStart n)).map
        (fun i => q (goldenSubstStart n + i))

def expansionRejected : Realization expansionSignature := realize expansionSignature
  (fun _ _ _ => [(false, false)]) (fun e => nomatch e)

theorem expansionRejectedLaw : ¬ expansionArena.Law expansionRejected := by
  intro h
  have hh := h 0 0
  simp [expansionRejected, realize, expansionActual, q, mu] at hh

def expansionRegistration : Registration expansionArena (expansionArena.Law expansionActual) where
  actual := expansionActual
  bridge := Iff.rfl
  variation := ⟨source_expansion, expansionRejected, expansionRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨expansionRejected, ?_, rfl, expansionRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    intro he
    norm_num [expansionActual, realize, q, parity, D5.S0.Conventions.wdigits,
      Nat.greatestFib] at he
    simp [mu] at he

register_information_theorem source_expansion in expansionArena
  readout via (realize expansionSignature
    (fun _ n t => ((List.range t).map (fun i => q (n + i))).flatMap mu)
    (fun e => nomatch e))
  realizes expansionRegistration
  escape from source ({
    owner := `D5.S1.Digit.ZeckendorfRawWindow
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "fn", "arg"], stateBinder := 1}] })
  escape continues (open)

abbrev congruenceSignature : Signature where
  Params := ℕ
  State := fun _ => List (Fin 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List (Fin 2) → Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def congruenceActual : Realization congruenceSignature := realize congruenceSignature
  (fun _ c w => residual c w) (fun e => nomatch e)

abbrev congruenceArena : Arena where
  signature := congruenceSignature
  Law R := ∀ (c : ℕ) (w v : List (Fin 2)), NoAdjacentOnes w → NoAdjacentOnes v →
    window c (value w) = window c (value v) →
    R.readout () c w = residual c v

def congruenceRejected : Realization congruenceSignature := realize congruenceSignature
  (fun _ _ _ => fun _ => some true) (fun e => nomatch e)

theorem congruenceRejectedLaw : ¬ congruenceArena.Law congruenceRejected := by
  intro h
  have hh := h 0 [] [] (by simp [NoAdjacentOnes]) (by simp [NoAdjacentOnes]) rfl
  have := congrFun hh []
  norm_num [congruenceRejected, realize, D5.S1.Digit.ZeckendorfRawWindow.residual,
    parity, value, fibPair, D5.S0.Conventions.wdigits,
    NoAdjacentOnes, List.isChain_cons_cons, Nat.greatestFib] at this

def congruenceRegistration : Registration congruenceArena (congruenceArena.Law congruenceActual) where
  actual := congruenceActual
  bridge := Iff.rfl
  variation := ⟨window_residual_congruence, congruenceRejected, congruenceRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨congruenceRejected, ?_, rfl, congruenceRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨0, [], [1], ?_⟩
    intro he
    have hh := congrFun he []
    have h0 : residual 0 [] [] = some false := by
      norm_num [D5.S1.Digit.ZeckendorfRawWindow.residual, value, fibPair, parity,
        D5.S0.Conventions.wdigits, NoAdjacentOnes, List.isChain_cons_cons,
        Nat.greatestFib]
    have h1 : residual 0 [1] [] = some true := by
      norm_num [D5.S1.Digit.ZeckendorfRawWindow.residual, value, fibPair, parity,
        D5.S0.Conventions.wdigits, NoAdjacentOnes, List.isChain_cons_cons,
        Nat.greatestFib]
    change residual 0 [] [] = residual 0 [1] [] at hh
    rw [h0, h1] at hh
    cases hh

register_information_theorem window_residual_congruence in congruenceArena
  readout via (realize congruenceSignature (fun _ c w => residual c w) (fun e => nomatch e))
  realizes congruenceRegistration
  escape from source ({
    owner := `D5.S1.Digit.ZeckendorfRawWindow
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 1}]})
  escape continues (open)

#print axioms coordinateRegistration
#print axioms expansionRegistration
#print axioms congruenceRegistration
end
end Reg.D5.S1.Digit.ZeckendorfRawWindow
