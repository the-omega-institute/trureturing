/- GID: D5/S1/Dynamics/Shadowing/StoneanForwardTubeObstruction
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/StoneanForwardTubeObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An infinite disjoint open forward tube in a Stonean source prevents shadowing. -/

import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Clopen
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.GroupWithZero.Basic

open Set Function

namespace D5.S1.Dynamics.Shadowing

noncomputable section
universe u

private theorem no_power_between {n k : ℕ} (hlo : 2 ^ k < n) (hhi : n < 2 ^ (k + 1)) :
    ¬ ∃ l : ℕ, n = 2 ^ l := by
  rintro ⟨l, rfl⟩
  have hkl : k < l := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlo
  have hlk : l < k + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hhi
  omega

private theorem consecutive_power_distance {n d : ℕ} (hd : 0 < d)
    (hn : ∃ k : ℕ, n = 2 ^ k) (hend : ∃ k : ℕ, n + d = 2 ^ k)
    (hmid : ∀ t : ℕ, 0 < t → t < d → ¬ ∃ k : ℕ, n + t = 2 ^ k) :
    ∃ k : ℕ, d = 2 ^ k := by
  obtain ⟨k, rfl⟩ := hn
  obtain ⟨l, hl⟩ := hend
  have hkl : k < l := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by omega)
  have hnext : 2 ^ (k + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by decide) (by omega)
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  have hle : 2 ^ k ≤ d := by omega
  have heq : d = 2 ^ k := by
    by_contra hne
    have hlt : 2 ^ k < d := by omega
    exact hmid (2 ^ k) (Nat.two_pow_pos _) hlt ⟨k + 1, by omega⟩
  exact ⟨k, heq⟩

private def eraseCycle {V : Type*} (p : ℕ → V) (i j : ℕ) (n : ℕ) : V :=
  if n < i then p n else p (n + (j - i))

private theorem eraseCycle_path {V : Type*} (edge : V → V → Prop) (p : ℕ → V)
    (hp : ∀ n, edge (p n) (p (n + 1))) {i j : ℕ} (hij : i < j)
    (hrep : p i = p j) : ∀ n, edge (eraseCycle p i j n) (eraseCycle p i j (n + 1)) := by
  intro n
  by_cases hn : n < i
  · by_cases hn1 : n + 1 < i
    · simpa [eraseCycle, hn, hn1] using hp n
    · have hni : n + 1 = i := by omega
      have hnj : n + 1 + (j - i) = j := by omega
      simp only [eraseCycle, if_pos hn, if_neg hn1, hnj]
      rw [← hrep, ← hni]
      exact hp n
  · have hn1 : ¬ n + 1 < i := by omega
    simpa [eraseCycle, hn, hn1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hp (n + (j - i))

private theorem ordered_repetition {N : ℕ} (p : ℕ → Fin N) :
    ∃ i j : ℕ, 0 < i ∧ i < j ∧ j ≤ N + 1 ∧ p i = p j := by
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun t : Fin (N + 1) => p (t.val + 1)) (by simp)
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · exact ⟨a.val + 1, b.val + 1, by omega, by omega, by omega, heq⟩
  · exact ⟨b.val + 1, a.val + 1, by omega, by omega, by omega, heq.symm⟩

/-- In an extremally disconnected source, a nonempty infinite family of disjoint
open sets carried successively forward by a continuous map rules out finite-cover
shadowing. No compactness, separation, metrizability, countability of the source,
invertibility, surjectivity or density of the tube union is assumed. -/
theorem not_has_shadowing_of_disjoint_open_forward_tubes
    {Y : Type u} [TopologicalSpace Y] [ExtremallyDisconnected Y]
    (g : Y → Y) (hg : Continuous g) (U : ℕ → Set Y)
    (hU : ∀ n, IsOpen (U n))
    (hdis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hne : (U 0).Nonempty) (hforward : ∀ n, MapsTo g (U n) (U (n + 1))) :
    ¬ HasShadowing g := by
  classical
  intro hs
  let O : Set Y := ⋃ n, U n
  let B : Set Y := ⋃ k : ℕ, U (2 ^ k)
  let W : Set Y := closure B
  let a : Y → Bool := W.boolIndicator
  have hB : IsOpen B := isOpen_iUnion (fun k => hU (2 ^ k))
  have hW : IsClopen W := ⟨isClosed_closure, ExtremallyDisconnected.open_closure B hB⟩
  have ha : Continuous a := (continuous_boolIndicator_iff_isClopen W).mpr hW
  have hBO : B ⊆ O := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨2 ^ k, hk⟩
  have hWU (n : ℕ) {x : Y} (hx : x ∈ U n) :
      x ∈ W ↔ ∃ k : ℕ, n = 2 ^ k := by
    constructor
    · intro hw
      by_contra hn
      have hd : Disjoint (U n) B := by
        refine disjoint_iUnion_right.mpr fun k => hdis n (2 ^ k) ?_
        intro he
        exact hn ⟨k, he⟩
      exact Set.disjoint_left.mp (hd.closure_right (hU n)) hx hw
    · rintro ⟨k, rfl⟩
      exact subset_closure (mem_iUnion.mpr ⟨k, hx⟩)
  have hit (n t : ℕ) {x : Y} (hx : x ∈ U n) : g^[t] x ∈ U (n + t) := by
    induction t with
    | zero => simpa using hx
    | succ t ih =>
      simpa only [iterate_succ_apply', Nat.add_assoc] using hforward (n + t) ih
  have gap (z : Y) (d : ℕ) (hd : 0 < d)
      (hzero : a z = true) (hend : a (g^[d] z) = true)
      (hmid : ∀ t : ℕ, 0 < t → t < d → a (g^[t] z) = false) :
      ∃ k : ℕ, d = 2 ^ k := by
    let T : Set Y := ⋂ t : Fin (d + 1),
      (g^[t.val]) ⁻¹' (a ⁻¹' {a (g^[t.val] z)})
    have hT : IsOpen T := isOpen_iInter_of_finite fun t =>
      (isOpen_discrete _).preimage (ha.comp (hg.iterate t.val))
    have hzT : z ∈ T := mem_iInter.mpr fun _ => rfl
    have hzO : z ∈ closure O := closure_mono hBO ((W.mem_iff_boolIndicator z).mpr hzero)
    obtain ⟨x, hxT, hxO⟩ := (mem_closure_iff.mp hzO) T hT hzT
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hxO
    have hsame (t : ℕ) (ht : t ≤ d) : a (g^[t] x) = a (g^[t] z) :=
      mem_iInter.mp hxT ⟨t, by omega⟩
    have hn : ∃ k : ℕ, n = 2 ^ k := (hWU n hxn).mp <|
      (W.mem_iff_boolIndicator x).mpr (by simpa using (hsame 0 (by omega)).trans hzero)
    have hnd : ∃ k : ℕ, n + d = 2 ^ k := (hWU (n + d) (hit n d hxn)).mp <|
      (W.mem_iff_boolIndicator _).mpr ((hsame d le_rfl).trans hend)
    refine consecutive_power_distance hd hn hnd ?_
    intro t ht htd hp
    have htrue : a (g^[t] x) = true :=
      (W.mem_iff_boolIndicator _).mp ((hWU (n + t) (hit n t hxn)).mpr hp)
    have hfalse : a (g^[t] x) = false := (hsame t (by omega)).trans (hmid t ht htd)
    exact Bool.noConfusion (htrue.symm.trans hfalse)
  obtain ⟨N, edge, label, heq⟩ := finite_observation_isSofic g a ha hs
  let D : ℕ := 2 ^ (N + 2)
  have hhalf : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
  have hD : D = 2 * 2 ^ (N + 1) := by dsimp [D]; rw [pow_succ]; omega
  obtain ⟨x₀, hx₀⟩ := hne
  let z : Y := g^[D] x₀
  have hz : z ∈ U D := by simpa [z] using hit 0 D hx₀
  have hstart : a z = true :=
    (W.mem_iff_boolIndicator _).mp ((hWU D hz).mpr ⟨N + 2, rfl⟩)
  have hend : a (g^[D] z) = true := by
    apply (W.mem_iff_boolIndicator _).mp
    apply (hWU (D + D) (hit D D hz)).mpr
    refine ⟨N + 3, ?_⟩
    dsimp [D]
    rw [show N + 3 = (N + 2) + 1 by omega, pow_succ]
    omega
  have hmid : ∀ t : ℕ, 0 < t → t < D → a (g^[t] z) = false := by
    intro t ht htd
    apply (W.notMem_iff_boolIndicator _).mp
    intro hw
    have hp := (hWU (D + t) (hit D t hz)).mp hw
    apply no_power_between (k := N + 2) (n := D + t) (by omega) ?_ hp
    rw [show N + 2 + 1 = (N + 2) + 1 by omega, pow_succ]
    dsimp [D] at *
    omega
  have hm : (fun n => a (g^[n] z)) ∈ graphLanguage edge label := by
    rw [← heq]
    exact ⟨z, rfl⟩
  obtain ⟨p, hp, hl⟩ := hm
  obtain ⟨i, j, hi, hij, hj, hrep⟩ := ordered_repetition p
  let p' := eraseCycle p i j
  let d : ℕ := D - (j - i)
  have hd : 0 < d := by dsimp [d]; omega
  have hm' : (fun n => label (p' n)) ∈ graphLanguage edge label :=
    ⟨p', eraseCycle_path edge p hp hij hrep, fun _ => rfl⟩
  rw [← heq] at hm'
  obtain ⟨z', hz'⟩ := hm'
  have hlabels (n : ℕ) : a (g^[n] z') = label (p' n) := congrFun hz' n
  have hs' : a z' = true := by
    have he : p' 0 = p 0 := by simp [p', eraseCycle, hi]
    calc
      a z' = label (p' 0) := by simpa using hlabels 0
      _ = label (p 0) := congrArg label he
      _ = a z := by simpa using hl 0
      _ = true := hstart
  have he' : a (g^[d] z') = true := by
    have hdi : ¬ d < i := by dsimp [d]; omega
    have hdD : d + (j - i) = D := by dsimp [d]; omega
    rw [hlabels, show p' d = p D by simp [p', eraseCycle, hdi, hdD], hl]
    exact hend
  have hmids' : ∀ t : ℕ, 0 < t → t < d → a (g^[t] z') = false := by
    intro t ht htd
    rw [hlabels]
    dsimp [p', eraseCycle]
    split_ifs with hti
    · rw [hl]
      exact hmid t ht (by dsimp [d] at htd; omega)
    · rw [hl]
      exact hmid (t + (j - i)) (by omega) (by dsimp [d] at htd; omega)
  obtain ⟨k, hk⟩ := gap z' d hd hs' he' hmids'
  have hlow : 2 ^ (N + 1) < d := by dsimp [d]; omega
  have hhigh : d < 2 ^ (N + 1 + 1) := by dsimp [d]; omega
  exact no_power_between hlow hhigh ⟨k, hk⟩

#print axioms not_has_shadowing_of_disjoint_open_forward_tubes

end
end D5.S1.Dynamics.Shadowing
