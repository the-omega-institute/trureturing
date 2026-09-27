/- GID: D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.claim; result=D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.result; claim=D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation.claim
   digest: A six-vertex 4-uniform hypergraph refutes the proposed panchromatic pairing equality. -/

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.PanchromaticPairingConjectureRefutation

private abbrev Hypergraph (V : Type) [DecidableEq V] := Finset (Finset V)

private def Panchromatic {V : Type} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (k : Nat) (c : V -> Fin k) : Prop :=
  ∀ e ∈ H, e.image c = Finset.univ

private def Bipanchromatic {V : Type} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (k : Nat) (c : V -> Fin k) : Prop :=
  Panchromatic H k c ∧
    ∀ color : Fin k, 2 <= (Finset.univ.filter fun v => c v = color).card

private def singletonCount {V : Type} [Fintype V] [DecidableEq V]
    {k : Nat} (c : V -> Fin k) : Nat :=
  (Finset.univ.filter fun color =>
    (Finset.univ.filter fun v => c v = color).card = 1).card

private def IsPanchromaticMaximum {V : Type} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (p : Nat) : Prop :=
  (Exists fun c : V -> Fin p => Panchromatic H p c) ∧
    ∀ k : Nat, (Exists fun c : V -> Fin k => Panchromatic H k c) -> k <= p

private def IsBipanchromaticMaximum {V : Type} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (b : Nat) : Prop :=
  (Exists fun c : V -> Fin b => Bipanchromatic H b c) ∧
    ∀ k : Nat, (Exists fun c : V -> Fin k => Bipanchromatic H k c) -> k <= b

private def IsSingletonMinimum {V : Type} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (p a : Nat) : Prop :=
  (Exists fun c : V -> Fin p => Panchromatic H p c ∧ singletonCount c = a) ∧
    ∀ c : V -> Fin p, Panchromatic H p c -> a <= singletonCount c

/-- Lalou--Mbarek--Skender--Togni Conjecture 1, with all three extrema
expressed by attainment and their universal order properties. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Hypergraph V) (p b a : Nat),
    IsPanchromaticMaximum H p ->
    IsBipanchromaticMaximum H b ->
    IsSingletonMinimum H p a ->
    b = p - a ⌈/⌉ 2

/-- The three four-edges with common core `{0,1,2}` give extrema
`chi_p = 4`, `alpha_4 = 3`, and `chi_p^2 = 3`, contradicting the claim. -/
theorem result : Not claim := by
  let e3 : Finset (Fin 6) := {0, 1, 2, 3}
  let e4 : Finset (Fin 6) := {0, 1, 2, 4}
  let e5 : Finset (Fin 6) := {0, 1, 2, 5}
  let H : Hypergraph (Fin 6) := {e3, e4, e5}
  let c4 : Fin 6 -> Fin 4 := fun v =>
    if v = 0 then 0 else if v = 1 then 1 else if v = 2 then 2 else 3
  let c3 : Fin 6 -> Fin 3 := fun v => ⟨v.val % 3, Nat.mod_lt _ (by omega)⟩
  have hsource :
      H.card = 3 ∧
        (∀ e ∈ H, e.Nonempty ∧ e.card = 4) ∧
        (∀ v : Fin 6, ∃ e ∈ H, v ∈ e) ∧
        e3 ∈ H ∧ e4 ∈ H ∧ e5 ∈ H := by
    dsimp [H, e3, e4, e5]
    decide
  have hpan4 : Panchromatic H 4 c4 := by
    intro e he
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> decide
  have hsingle4 : singletonCount c4 = 3 := by
    decide
  have hbi3 : Bipanchromatic H 3 c3 := by
    constructor
    · intro e he
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> decide
    · intro color
      fin_cases color <;> decide
  have hpmax : IsPanchromaticMaximum H 4 := by
    refine ⟨⟨c4, hpan4⟩, ?_⟩
    intro k hk
    rcases hk with ⟨c, hc⟩
    have himage : e3.image c = Finset.univ := hc e3 (by simp [H])
    calc
      k = (Finset.univ : Finset (Fin k)).card := by simp
      _ = (e3.image c).card := congrArg Finset.card himage.symm
      _ <= e3.card := Finset.card_image_le
      _ = 4 := (hsource.2.1 e3 hsource.2.2.2.1).2
  have hbmax : IsBipanchromaticMaximum H 3 := by
    refine ⟨⟨c3, hbi3⟩, ?_⟩
    intro k hk
    rcases hk with ⟨c, hc⟩
    have hsum :
        (Finset.univ : Finset (Fin 6)).card =
          ∑ color : Fin k, (Finset.univ.filter fun v => c v = color).card := by
      exact Finset.card_eq_sum_card_fiberwise (by simp)
    have htwice : 2 * k <= 6 := by
      calc
        2 * k = ∑ _color : Fin k, 2 := by simp [mul_comm]
        _ <= ∑ color : Fin k,
            (Finset.univ.filter fun v => c v = color).card := by
          exact Finset.sum_le_sum fun color _ => hc.2 color
        _ = 6 := by simpa using hsum.symm
    omega
  have hamin : IsSingletonMinimum H 4 3 := by
    refine ⟨⟨c4, hpan4, hsingle4⟩, ?_⟩
    intro c hc
    have hi3 : e3.image c = Finset.univ := hc e3 (by simp [H])
    have hi4 : e4.image c = Finset.univ := hc e4 (by simp [H])
    have hi5 : e5.image c = Finset.univ := hc e5 (by simp [H])
    have hinj : Set.InjOn c e3 := by
      apply Finset.card_image_iff.mp
      rw [hi3]
      simp [e3]
    have h01 : c 0 ≠ c 1 := by
      intro h
      have : (0 : Fin 6) = 1 := hinj (by simp [e3]) (by simp [e3]) h
      omega
    have h02 : c 0 ≠ c 2 := by
      intro h
      have : (0 : Fin 6) = 2 := hinj (by simp [e3]) (by simp [e3]) h
      omega
    have h12 : c 1 ≠ c 2 := by
      intro h
      have : (1 : Fin 6) = 2 := hinj (by simp [e3]) (by simp [e3]) h
      omega
    have h03 : c 0 ≠ c 3 := by
      intro h
      have : (0 : Fin 6) = 3 := hinj (by simp [e3]) (by simp [e3]) h
      omega
    have h13 : c 1 ≠ c 3 := by
      intro h
      have : (1 : Fin 6) = 3 := hinj (by simp [e3]) (by simp [e3]) h
      omega
    have h23 : c 2 ≠ c 3 := by
      intro h
      have : (2 : Fin 6) = 3 := hinj (by simp [e3]) (by simp [e3]) h
      omega
    have h43 : c 4 = c 3 := by
      have hm : c 3 ∈ e4.image c := by rw [hi4]; simp
      rcases Finset.mem_image.mp hm with ⟨v, hv, hvc⟩
      simp only [e4, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with h | h | h | h <;> subst v
      · exact False.elim (h03 hvc)
      · exact False.elim (h13 hvc)
      · exact False.elim (h23 hvc)
      · exact hvc
    have h53 : c 5 = c 3 := by
      have hm : c 3 ∈ e5.image c := by rw [hi5]; simp
      rcases Finset.mem_image.mp hm with ⟨v, hv, hvc⟩
      simp only [e5, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with h | h | h | h <;> subst v
      · exact False.elim (h03 hvc)
      · exact False.elim (h13 hvc)
      · exact False.elim (h23 hvc)
      · exact hvc
    have hf0 :
        (Finset.univ.filter fun v : Fin 6 => c v = c 0) = {0} := by
      ext v
      fin_cases v <;> simp [h01.symm, h02.symm, h03.symm, h43, h53]
    have hf1 :
        (Finset.univ.filter fun v : Fin 6 => c v = c 1) = {1} := by
      ext v
      fin_cases v <;> simp [h01, h12.symm, h13.symm, h43, h53]
    have hf2 :
        (Finset.univ.filter fun v : Fin 6 => c v = c 2) = {2} := by
      ext v
      fin_cases v <;> simp [h02, h12, h23.symm, h43, h53]
    have hsub :
        ({c 0, c 1, c 2} : Finset (Fin 4)) ⊆
          Finset.univ.filter (fun color =>
            (Finset.univ.filter fun v => c v = color).card = 1) := by
      intro color hcolor
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcolor
      rcases hcolor with rfl | rfl | rfl
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hf0]
        simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hf1]
        simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hf2]
        simp
    have hthree : ({c 0, c 1, c 2} : Finset (Fin 4)).card = 3 := by
      simp [h01, h02, h12]
    rw [singletonCount]
    rw [← hthree]
    exact Finset.card_le_card hsub
  intro hclaim
  have heq := hclaim (Fin 6) H 4 3 3 hpmax hbmax hamin
  norm_num [Nat.ceilDiv_eq_add_pred_div] at heq

#print axioms claim
#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.PanchromaticPairingConjectureRefutation
