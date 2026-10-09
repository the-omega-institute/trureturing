/- GID: D5/S3/ObserverMemory/Algorithms/SaturatedActualCone
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SaturatedActualCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete actual event fibers and their saturated successor transport. -/

import D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories
import D5.S0.Computability.Coding.PrefixFreeCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.SaturatedActualCone

open ActualControlSlots SaturatedActualHistories
open scoped BigOperators

variable {p P : Nat} {Q : Type} [Fintype Q] [DecidableEq Q]
variable (hp : 2 ≤ p) (hP : 0 < P) (C : Controller p P Q) (I : C.Correct hp hP)

attribute [local instance] Classical.propDecidable
local notation "Source" => ZMod (p * P)
local notation "Slot" => {q : Q // ∃ b, C.Used I q b} × Fin p

/-- All initialized occurrences at a slot, retaining the original input and physical time. -/
noncomputable def events (u : Slot) : Finset (Source × Nat) :=
  (Finset.univ.biUnion (fun x : Source =>
    (Finset.range (I.length x)).image (fun t => (x,t)))).filter
      (fun e => C.Occurs I e.1 e.2 u)

private theorem mem_events {u : Slot} {e : Source × Nat} :
    e ∈ events hp hP C I u ↔ C.Occurs I e.1 e.2 u := by
  classical
  simp only [events, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨⟨e.1,e.2,h.1,rfl⟩,h⟩⟩

/-- The one-based read index at an actual occurrence. -/
noncomputable def readIndex (e : Source × Nat) : Nat :=
  ((readEvents hp hP C I e.1).filter (fun t => t ≤ e.2)).card

/-- Dyadic mass of the entire slot event fiber at the common read deadline. -/
noncomputable def mass (h : Nat) (u : Slot) : Real :=
  ∑ e ∈ events hp hP C I u, (1 / 2 : Real) ^ (h - readIndex hp hP C I e)

private noncomputable def answer (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    (u v : Slot) : Fin 2 :=
  if hn : (G.next u).Nonempty then if v = hn.choose then 0 else 1 else 0

private theorem answer_injective (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    {u v w : Slot} (hv : v ∈ G.next u) (hw : w ∈ G.next u)
    (eq : answer hp hP C I G u v = answer hp hP C I G u w) : v = w := by
  classical
  have hn : (G.next u).Nonempty := ⟨v,hv⟩
  by_cases vf : v = hn.choose
  · by_cases wf : w = hn.choose
    · exact vf.trans wf.symm
    · simp [answer, hn, vf, wf] at eq
  · by_cases wf : w = hn.choose
    · simp [answer, hn, vf, wf] at eq
    · have small : (G.next u |>.erase hn.choose).card ≤ 1 := by
        have hc := Finset.card_erase_of_mem hn.choose_mem
        have bound := G.at_most_two u
        omega
      exact (Finset.card_le_one.mp small) v (Finset.mem_erase.mpr ⟨vf,hv⟩)
        w (Finset.mem_erase.mpr ⟨wf,hw⟩)

/-- A binary word follows the original run, with only waits between consecutive reads. -/
private inductive FutureWord (G : SlotGraph p {q : Q // ∃ b, C.Used I q b}) :
    Slot → Source → Nat → List (Fin 2) → Prop where
  | stop {u : Slot} {x : Source} {t : Nat}
      (occurs : C.Occurs I x t u) (halt : C.action (C.readNext u.1.val u.2) = .halt) :
      FutureWord G u x t []
  | next {u v : Slot} {x : Source} {t k : Nat} {word : List (Fin 2)}
      (occurs : C.Occurs I x t u) (child : C.Occurs I x k v)
      (before : t < k)
      (waits : ∀ i, t < i → i < k → C.action (C.run hp hP x i).2 = .wait)
      (edge : v ∈ G.next u) (tail : FutureWord G v x k word) :
      FutureWord G u x t (answer hp hP C I G u v :: word)

end D5.S3.ObserverMemory.Algorithms.SaturatedActualCone
