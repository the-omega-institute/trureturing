/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialRefinement
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/FactorialRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal refinement of factorial-word tilings into their constituent blocks. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialWords
import D5.S1.Dynamics.Symbolic.PermutativeLifts.MarkedTiling

/-! Literal refinement, recognizability and the simultaneous factorial subshift. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

def cyclicState (W : Bool → List Bool) (a : Bool)
    (ha : 0 < (W a).length) (p : ℕ) : TileState W :=
  ⟨a, ⟨p % (W a).length, Nat.mod_lt _ ha⟩⟩

theorem cyclicState_next (W : Bool → List Bool) (a : Bool)
    (ha : 0 < (W a).length) (p : ℕ) :
    TileNext W (cyclicState W a ha p) (cyclicState W a ha (p + 1)) := by
  have hr := Nat.mod_lt p ha
  have he : (p + 1) % (W a).length = (p % (W a).length + 1) % (W a).length := by
    exact (Nat.mod_add_mod p (W a).length 1).symm
  change (a = a ∧ (p + 1) % (W a).length = p % (W a).length + 1) ∨
    (p % (W a).length + 1 = (W a).length ∧ (p + 1) % (W a).length = 0)
  by_cases h : p % (W a).length + 1 < (W a).length
  · exact Or.inl ⟨rfl, he.trans (Nat.mod_eq_of_lt h)⟩
  · have hlast : p % (W a).length + 1 = (W a).length := by omega
    exact Or.inr ⟨hlast, by rw [he, hlast, Nat.mod_self]⟩

theorem mod_before_multiple {p d : ℕ} (hd : 0 < d)
    (hp : (p + 1) % d = 0) : p % d + 1 = d := by
  have hr := Nat.mod_lt p hd
  have he : (p % d + 1) % d = 0 := by simpa only [Nat.mod_add_mod] using hp
  by_contra h
  have hlt : p % d + 1 < d := by omega
  rw [Nat.mod_eq_of_lt hlt] at he
  omega

/-- A higher block contains a zero-type run followed by a one-type run.
The state records the actual lower block and its physical offset. -/
def refineState (n : ℕ) (s : TileState (word (n + 1))) : TileState (word n) :=
  if (s.2 : ℕ) < (n + 1).factorial * (word n false).length then
    ⟨false, ⟨(s.2 : ℕ) % (word n false).length,
      Nat.mod_lt _ (word_length_pos n false)⟩⟩
  else
    ⟨true, ⟨((s.2 : ℕ) - (n + 1).factorial * (word n false).length) %
      (word n true).length, Nat.mod_lt _ (word_length_pos n true)⟩⟩

private theorem refineState_of_lt (n : ℕ) (s : TileState (word (n + 1)))
    (h : (s.2 : ℕ) < (n + 1).factorial * (word n false).length) :
    refineState n s =
      ⟨false, ⟨(s.2 : ℕ) % (word n false).length,
        Nat.mod_lt _ (word_length_pos n false)⟩⟩ := by
  simp only [refineState, ite_eq_left h]

private theorem refineState_of_not_lt (n : ℕ) (s : TileState (word (n + 1)))
    (h : ¬ (s.2 : ℕ) < (n + 1).factorial * (word n false).length) :
    refineState n s =
      ⟨true, ⟨((s.2 : ℕ) - (n + 1).factorial * (word n false).length) %
        (word n true).length, Nat.mod_lt _ (word_length_pos n true)⟩⟩ := by
  simp only [refineState, ite_eq_right h]

theorem refineState_type_false_iff (n : ℕ) (s : TileState (word (n + 1))) :
    (refineState n s).1 = false ↔
      (s.2 : ℕ) < (n + 1).factorial * (word n false).length := by
  simp only [refineState]
  split <;> simp_all

theorem refineState_type_true_iff (n : ℕ) (s : TileState (word (n + 1))) :
    (refineState n s).1 = true ↔
      ¬ (s.2 : ℕ) < (n + 1).factorial * (word n false).length := by
  simp only [refineState]
  split <;> simp_all

/-- Refining one adjacent pair preserves the actual local tiling rule. -/
theorem refineState_next (n : ℕ) {s t : TileState (word (n + 1))}
    (hst : TileNext (word (n + 1)) s t) :
    TileNext (word n) (refineState n s) (refineState n t) := by
  let f := (n + 1).factorial
  let h₀ := (word n false).length
  let h₁ := (word n true).length
  let c := f * h₀
  have hf : 0 < f := Nat.factorial_pos _
  have h₀pos : 0 < h₀ := word_length_pos n false
  have h₁pos : 0 < h₁ := word_length_pos n true
  have hc : 0 < c := Nat.mul_pos hf h₀pos
  have hslen : (word (n + 1) s.1).length =
      c + ((if s.1 then 2 else 1) * f) * h₁ := word_length_succ n s.1
  have htail : 0 < ((if s.1 then 2 else 1) * f) * h₁ := by
    cases s.1 <;> simp [hf, h₁pos]
  rcases hst with ⟨htype, hoff⟩ | ⟨hlast, hstart⟩
  · by_cases hs : (s.2 : ℕ) < c
    · by_cases ht : (t.2 : ℕ) < c
      · have he := cyclicState_next (word n) false h₀pos (s.2 : ℕ)
        rw [refineState_of_lt n s hs, refineState_of_lt n t ht]
        simpa only [cyclicState, hoff] using he
      · have hcross : (t.2 : ℕ) = c := by omega
        have hmod : ((s.2 : ℕ) + 1) % h₀ = 0 := by
          rw [← hoff, hcross]
          simp [c]
        have hbefore := mod_before_multiple h₀pos hmod
        rw [refineState_of_lt n s hs, refineState_of_not_lt n t ht]
        right
        change (s.2 : ℕ) % h₀ + 1 = h₀ ∧ ((t.2 : ℕ) - c) % h₁ = 0
        exact ⟨hbefore, by rw [hcross]; simp⟩
    · have ht : ¬ (t.2 : ℕ) < c := by omega
      have hdiff : (t.2 : ℕ) - c = (s.2 : ℕ) - c + 1 := by omega
      have he := cyclicState_next (word n) true h₁pos ((s.2 : ℕ) - c)
      rw [refineState_of_not_lt n s hs, refineState_of_not_lt n t ht]
      change TileNext (word n)
        (cyclicState (word n) true h₁pos ((s.2 : ℕ) - c))
        (cyclicState (word n) true h₁pos ((t.2 : ℕ) - c))
      simpa only [hdiff] using he
  · have hs : ¬ (s.2 : ℕ) < c := by omega
    have ht : (t.2 : ℕ) < c := by omega
    have hdiff : (s.2 : ℕ) - c + 1 = ((if s.1 then 2 else 1) * f) * h₁ := by
      omega
    have hmod : ((s.2 : ℕ) - c + 1) % h₁ = 0 := by
      rw [hdiff]
      exact Nat.mul_mod_left _ _
    have hbefore := mod_before_multiple h₁pos hmod
    rw [refineState_of_not_lt n s hs, refineState_of_lt n t ht]
    right
    change ((s.2 : ℕ) - c) % h₁ + 1 = h₁ ∧ (t.2 : ℕ) % h₀ = 0
    exact ⟨hbefore, by rw [hstart]; simp⟩

/-- The refinement is an actual map of compact marked tiling spaces. -/
def refineTiling (n : ℕ) (x : MarkedTiling (word (n + 1))) :
    MarkedTiling (word n) :=
  ⟨fun i => refineState n (x.1 i), fun i => refineState_next n (x.2 i)⟩

/-- The lower block types display exactly the parent starts as their 10 markers. -/
theorem refineTiling_boundary_iff (n : ℕ) (x : MarkedTiling (word (n + 1))) (i : ℤ) :
    (x.1 i).2.val = 0 ↔
      ((refineTiling n x).1 (i - 1)).1 = true ∧
      ((refineTiling n x).1 i).1 = false := by
  let c := (n + 1).factorial * (word n false).length
  have hc : 0 < c := Nat.mul_pos (Nat.factorial_pos _) (word_length_pos n false)
  have hnext : TileNext (word (n + 1)) (x.1 (i - 1)) (x.1 i) := by
    simpa using x.2 (i - 1)
  have hlen := word_length_succ n (x.1 (i - 1)).1
  have htail : 0 < ((if (x.1 (i - 1)).1 then 2 else 1) * (n + 1).factorial) *
      (word n true).length := by
    cases (x.1 (i - 1)).1 <;> simp [Nat.factorial_pos, word_length_pos]
  change (x.1 i).2.val = 0 ↔
    (refineState n (x.1 (i - 1))).1 = true ∧ (refineState n (x.1 i)).1 = false
  rw [refineState_type_true_iff, refineState_type_false_iff]
  change (x.1 i).2.val = 0 ↔ ¬ (x.1 (i - 1)).2.val < c ∧ (x.1 i).2.val < c
  rcases hnext with ⟨_, hoff⟩ | ⟨hlast, hstart⟩
  · omega
  · constructor
    · intro _
      constructor <;> dsimp [c] at * <;> omega
    · exact fun _ => hstart

theorem word_length_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun a => (word n a).length) := by
  intro a b hab
  have hlt := word_false_length_lt_true hn
  cases a <;> cases b <;> simp_all

/-- Refinement preserves the binary symbol at every physical coordinate. -/
theorem readTile_refineState (n : ℕ) (s : TileState (word (n + 1))) :
    readTile (word n) (refineState n s) = readTile (word (n + 1)) s := by
  rcases s with ⟨a, ⟨i, hiBound⟩⟩
  by_cases hs : i < (n + 1).factorial * (word n false).length
  · have hi : i <
        (repeatWord (word n false) (n + 1).factorial).length := by simpa using hs
    rw [refineState_of_lt n ⟨a, ⟨i, hiBound⟩⟩ hs]
    simp only [readTile, List.get_eq_getElem, word_succ, List.getElem_append_left hi]
    exact (repeatWord_getElem (word n false) (word_length_pos n false) hs).symm
  · have hi : (repeatWord (word n false) (n + 1).factorial).length ≤
        i := by simpa using Nat.le_of_not_gt hs
    have hlt : i < (n + 1).factorial * (word n false).length +
        ((if a then 2 else 1) * (n + 1).factorial) * (word n true).length := by
      simpa only [word_length_succ] using hiBound
    have hj : i - (n + 1).factorial * (word n false).length <
        ((if a then 2 else 1) * (n + 1).factorial) * (word n true).length := by omega
    rw [refineState_of_not_lt n ⟨a, ⟨i, hiBound⟩⟩ hs]
    simp only [readTile, List.get_eq_getElem, word_succ, List.getElem_append_right hi]
    simpa only [length_repeatWord] using
      (repeatWord_getElem (word n true) (word_length_pos n true) hj).symm

theorem readTiling_refineTiling (n : ℕ) (x : MarkedTiling (word (n + 1))) :
    readTiling (word n) (refineTiling n x) = readTiling (word (n + 1)) x := by
  funext i
  exact readTile_refineState n (x.1 i)

/-- Recognizability is proved for the actual words by finite induction. -/
theorem readTiling_injective (n : ℕ) : Function.Injective (readTiling (word n)) := by
  induction n with
  | zero =>
    intro x y hxy
    apply Subtype.ext
    funext i
    have hs := congrFun hxy i
    change readTile (word 0) (x.1 i) = readTile (word 0) (y.1 i) at hs
    have hab : (x.1 i).1 = (y.1 i).1 := by
      simpa [readTile, word_zero] using hs
    have hp : (x.1 i).2.val = 0 := by
      have := (x.1 i).2.isLt
      simp only [word_zero, List.length_singleton] at this
      omega
    have hq : (y.1 i).2.val = 0 := by
      have := (y.1 i).2.isLt
      simp only [word_zero, List.length_singleton] at this
      omega
    apply Sigma.ext hab
    apply (Fin.heq_ext_iff (by simp only [word_zero, List.length_singleton])).mpr
    exact hp.trans hq.symm
  | succ n ih =>
    intro x y hxy
    have hr : refineTiling n x = refineTiling n y := by
      apply ih
      rw [readTiling_refineTiling, readTiling_refineTiling, hxy]
    apply Subtype.ext
    apply tiled_eq_of_boundaries (word (n + 1)) (word_length_injective (by omega)) x.2 y.2
    intro i
    rw [refineTiling_boundary_iff, refineTiling_boundary_iff, hr]

/-- Each upper tiling really supplies a lower tiling of the same configuration. -/
theorem factorial_subshift_succ_subset (n : ℕ) :
    (tiledSubshift (word (n + 1))).carrier ⊆ (tiledSubshift (word n)).carrier := by
  rintro y ⟨x, rfl⟩
  exact ⟨refineTiling n x, readTiling_refineTiling n x⟩

/-- The actual simultaneous factorial-word subshift, with no assumed tower data. -/
def factorialSubshift : SymbolicDynamics.FullShift.Subshift Bool ℤ where
  carrier := ⋂ n : ℕ, (tiledSubshift (word n)).carrier
  isClosed := isClosed_iInter fun n => (tiledSubshift (word n)).isClosed
  mapsTo := by
    intro k y hy
    simp only [Set.mem_iInter] at hy ⊢
    exact fun n => (tiledSubshift (word n)).mapsTo k (hy n)

theorem factorial_subshift_nonempty : factorialSubshift.carrier.Nonempty := by
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => (tiledSubshift (word n)).carrier)
    factorial_subshift_succ_subset
    (fun n => tiledSubshift_nonempty (word n) (word_length_pos n))
    (tiledSubshift (word 0)).isClosed.isCompact
    (fun n => (tiledSubshift (word n)).isClosed)

end D5.S1.Dynamics.Symbolic.PermutativeLifts
