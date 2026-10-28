/- GID: D5/S1/Words/EndpointShuffleSupport
   generality: G
   mirror-B: D5/B/S1/Words/EndpointShuffleSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constructive distinct endpoint-gap families in ordinary self-shuffle support. -/

import D5.S1.Words.UnaryGapWords
import D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.EndpointShuffleSupport

open D5.S1.Words.UnaryGapWords
open D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration

/-- Two endpoint ones separated by an arbitrary number of zeros. -/
def endpointWord (m : Nat) : List Bool :=
  [true] ++ List.replicate m false ++ [true]

/-- The two outer zero gaps determine the middle gap. -/
def endpointOutput (m a c : Nat) : List Bool :=
  gap false [true, true, true, true] [0, a, (m - a) + (m - c), c, 0]

/-- A set of output words, with equal words counted only once. -/
def endpointFamily (m : Nat) : Finset (List Bool) :=
  Finset.univ.image (fun p : Fin (m + 1) × Fin (m + 1) =>
    endpointOutput m p.1.val p.2.val)

private theorem prefix_left {α : Type*} (p u v z : List α)
    (hz : z ∈ ordinaryShuffles u v) :
    p ++ z ∈ ordinaryShuffles (p ++ u) v := by
  induction p with
  | nil => simpa using hz
  | cons x p ih =>
      cases v with
      | nil =>
          have hzu : z = u := by simpa [ordinaryShuffles] using hz
          subst z
          simp [ordinaryShuffles]
      | cons y v =>
          simp only [List.cons_append, ordinaryShuffles, List.mem_append, List.mem_map]
          exact Or.inl ⟨p ++ z, ih, rfl⟩

private theorem prefix_right {α : Type*} (p u v z : List α)
    (hz : z ∈ ordinaryShuffles u v) :
    p ++ z ∈ ordinaryShuffles u (p ++ v) := by
  induction p with
  | nil => simpa using hz
  | cons y p ih =>
      cases u with
      | nil =>
          have hzv : z = v := by simpa [ordinaryShuffles] using hz
          subst z
          simp [ordinaryShuffles]
      | cons x u =>
          simp only [List.cons_append, ordinaryShuffles, List.mem_append, List.mem_map]
          exact Or.inr ⟨p ++ z, ih, rfl⟩

/-- Every bounded pair of outer gaps is realized by an actual ordinary shuffle. -/
theorem endpointOutput_mem (m a c : Nat) (ha : a ≤ m) (hc : c ≤ m) :
    endpointOutput m a c ∈ ordinaryShuffles (endpointWord m) (endpointWord m) := by
  let za := List.replicate a false
  let zr := List.replicate (m - a) false
  let zs := List.replicate (m - c) false
  let zc := List.replicate c false
  have h0 : zc ++ [true] ∈ ordinaryShuffles [] (zc ++ [true]) := by
    simp [ordinaryShuffles]
  have h1 := prefix_left [true] [] (zc ++ [true]) (zc ++ [true]) h0
  have h2 := prefix_right zs ([true] ++ []) (zc ++ [true])
    ([true] ++ (zc ++ [true])) h1
  have h3 := prefix_left zr ([true] ++ []) (zs ++ (zc ++ [true]))
    (zs ++ ([true] ++ (zc ++ [true]))) h2
  have h4 := prefix_right [true] (zr ++ ([true] ++ []))
    (zs ++ (zc ++ [true]))
    (zr ++ (zs ++ ([true] ++ (zc ++ [true])))) h3
  have h5 := prefix_left ([true] ++ za) (zr ++ ([true] ++ []))
    ([true] ++ (zs ++ (zc ++ [true])))
    ([true] ++ (zr ++ (zs ++ ([true] ++ (zc ++ [true]))))) h4
  have hab : a + (m - a) = m := by omega
  have hcd : (m - c) + c = m := by omega
  have hmerge (r s : Nat) (t : List Bool) :
      List.replicate r false ++ (List.replicate s false ++ t) =
        List.replicate (r + s) false ++ t := by
    rw [← List.append_assoc, ← List.replicate_add]
  simpa only [za, zr, zs, zc, endpointWord, endpointOutput, gap,
    List.headD_cons, List.tail_cons, List.replicate_zero, List.nil_append,
    List.append_nil, List.singleton_append, List.cons_append, List.append_assoc,
    hmerge, hab, hcd] using h5

private theorem endpointOutput_injective (m : Nat) :
    Function.Injective (fun p : Fin (m + 1) × Fin (m + 1) =>
      endpointOutput m p.1.val p.2.val) := by
  intro p q hpq
  have hg := (gap_injective false [true, true, true, true] [true, true, true, true]
    [0, p.1.val, (m - p.1.val) + (m - p.2.val), p.2.val, 0]
    [0, q.1.val, (m - q.1.val) + (m - q.2.val), q.2.val, 0]
    (by simp) (by simp) (by simp) (by simp) hpq).2
  have ha : p.1.val = q.1.val := by
    simpa using congrArg (fun l : List Nat => l[1]?.getD 0) hg
  have hc : p.2.val = q.2.val := by
    simpa using congrArg (fun l : List Nat => l[3]?.getD 0) hg
  exact Prod.ext (Fin.ext ha) (Fin.ext hc)

/-- The parameter rectangle counts distinct words, independently of schedules. -/
theorem endpointFamily_card (m : Nat) : (endpointFamily m).card = (m + 1) ^ 2 := by
  rw [endpointFamily, Finset.card_image_of_injective _ (endpointOutput_injective m)]
  simp [pow_two]

/-- An unbounded lower bound on distinct ordinary self-shuffle words. -/
theorem endpoint_self_shuffle_card_lower (m : Nat) :
    (m + 1) ^ 2 ≤
      ((ordinaryShuffles (endpointWord m) (endpointWord m)).toFinset).card := by
  rw [← endpointFamily_card m]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw
  exact List.mem_toFinset.mpr
    (endpointOutput_mem m p.1.val p.2.val (by omega) (by omega))

end D5.S1.Words.EndpointShuffleSupport
