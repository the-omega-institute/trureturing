/- GID: D5/S3/Combinatorics/FreeGroups/NormalIndependenceWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FreeGroups/NormalIndependenceWords
   mirror-E: none(waiver:explicit-binary-commutator-family)
   anchors: [mathlib/module/Mathlib.GroupTheory.FreeGroup.Reduce]
   utility: none
   digest: Binary commutators have exact reduced lengths in every free rank. -/

import Mathlib.GroupTheory.FreeGroup.Reduce

set_option autoImplicit false

namespace D5.S3.Combinatorics.FreeGroups.NormalIndependenceWords

/-- The positive binary coding word. -/
def u {α : Type*} (a b : α) (ε : List Bool) : FreeGroup α :=
  FreeGroup.of b * (ε.map fun bit =>
    FreeGroup.of a ^ (if bit then 3 else 0) * FreeGroup.of b).prod

/-- The commutator of two conjugate squares used for normal independence. -/
def s {α : Type*} (a b : α) (ε : List Bool) : FreeGroup α :=
  FreeGroup.of a ^ 2 * u a b ε * FreeGroup.of a ^ 2 * (u a b ε)⁻¹ *
    (FreeGroup.of a ^ 2)⁻¹ * u a b ε * (FreeGroup.of a ^ 2)⁻¹ * (u a b ε)⁻¹

/-- The displayed commutator word is reduced, with its exact binary-weight length. -/
theorem relator_length {α : Type*} [DecidableEq α] (a b : α) (hab : a ≠ b) (ε : List Bool) :
    (FreeGroup.toWord (s a b ε)).length = 4 * ε.length + 12 + 12 * ε.count true := by
  classical
  let V : List Bool → List (α × Bool) := fun e =>
    (b, true) :: e.flatMap (fun bit =>
      if bit then [(a, true), (a, true), (a, true), (b, true)] else [(b, true)])
  have hV (e : List Bool) :
      FreeGroup.mk (V e) = u a b e ∧
      (V e).length = e.length + 1 + 3 * e.count true ∧
      (V e).head? = some (b, true) ∧ (V e).getLast? = some (b, true) ∧
      ∀ z ∈ V e, z.2 = true := by
    induction e using List.reverseRecOn with
    | nil => simp [V, u, FreeGroup.of]
    | append_singleton e bit ih =>
      obtain ⟨he, hl, hh, ht, hp⟩ := ih
      have hv : V (e ++ [bit]) = V e ++
          (if bit then [(a, true), (a, true), (a, true), (b, true)]
            else [(b, true)]) := by simp [V, List.flatMap_append]
      rw [hv]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [← FreeGroup.mul_mk, he]
        cases bit <;>
          simp [u, List.map_append, List.prod_append, FreeGroup.of, pow_succ,
            FreeGroup.mul_mk, mul_assoc]
      · cases bit <;> simp [hl, List.count_append] <;> omega
      · cases bit <;> simp [V]
      · cases bit <;> simp
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hp z hz
        · cases bit <;> simp only [Bool.false_eq_true, if_false, if_true,
            List.mem_cons, List.not_mem_nil, or_false] at hz <;>
            rcases hz with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨hVm, hVl, hVh, hVt, hVp⟩ := hV ε
  let W := V ε
  let A : List (α × Bool) := [(a, true), (a, true)]
  let B := FreeGroup.invRev A
  let I := FreeGroup.invRev W
  let R := A ++ W ++ A ++ I ++ B ++ W ++ B ++ I
  have hp : FreeGroup.IsReduced W := by
    unfold FreeGroup.IsReduced
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y l t h
    have hx : x ∈ W := by rw [h]; simp
    have hy : y ∈ W := by rw [h]; simp
    simp [hVp x hx, hVp y hy]
  have hi : FreeGroup.IsReduced I := by
    change FreeGroup.IsReduced (FreeGroup.invRev W)
    unfold FreeGroup.IsReduced FreeGroup.invRev
    rw [List.isChain_reverse, List.isChain_map]
    exact hp.imp fun x y hxy h => congrArg Bool.not (hxy h.symm).symm
  have ha : FreeGroup.IsReduced A := by
    simp [A, FreeGroup.isReduced_cons_cons]
  have hb : FreeGroup.IsReduced B := by
    simp [B, A, FreeGroup.invRev, FreeGroup.isReduced_cons_cons]
  have hIh : I.head? = some (b, false) := by
    simp [I, FreeGroup.invRev, List.head?_reverse, hVt, W]
  have hIt : I.getLast? = some (b, false) := by
    simp [I, FreeGroup.invRev, List.getLast?_reverse, hVh, W]
  have happend (l t : List (α × Bool))
      (hl : FreeGroup.IsReduced l) (ht : FreeGroup.IsReduced t)
      (hx : α) (hy : α) (bx bt : Bool)
      (hxlast : l.getLast? = some (hx, bx)) (hyhead : t.head? = some (hy, bt))
      (hne : hx ≠ hy) : FreeGroup.IsReduced (l ++ t) := by
    exact hl.append ht (by simp [hxlast, hyhead, hne])
  have last (l t : List (α × Bool)) (x : α × Bool)
      (hx : t.getLast? = some x) : (l ++ t).getLast? = some x := by
    rw [List.getLast?_append_of_ne_nil l (by intro h; simp [h] at hx), hx]
  have hAh : A.head? = some (a, true) := rfl
  have hAt : A.getLast? = some (a, true) := rfl
  have hBh : B.head? = some (a, false) := by simp [B, A, FreeGroup.invRev]
  have hBt : B.getLast? = some (a, false) := by simp [B, A, FreeGroup.invRev]
  have hred : FreeGroup.IsReduced R := by
    dsimp only [R]
    apply happend _ _ _ hi a b false false (last _ B _ hBt) hIh hab
    apply happend _ _ _ hb b a true false (last _ W _ hVt) hBh hab.symm
    apply happend _ _ _ hp a b false true (last _ B _ hBt) hVh hab
    apply happend _ _ _ hb b a false false (last _ I _ hIt) hBh hab.symm
    apply happend _ _ _ hi a b true false (last _ A _ hAt) hIh hab
    apply happend _ _ _ ha b a true true (last _ W _ hVt) hAh hab.symm
    exact happend A W ha hp a b true true hAt hVh hab
  have hmk : FreeGroup.mk R = s a b ε := by
    simp only [R, B, I, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    have hA : FreeGroup.mk A = FreeGroup.of a ^ 2 := by
      simp [A, FreeGroup.of, pow_succ, FreeGroup.mul_mk]
    rw [hA, hVm]
    rfl
  rw [← hmk, FreeGroup.toWord_mk, hred.reduce_eq]
  simp only [R, List.length_append, I, B, FreeGroup.invRev_length, A,
    List.length_cons, List.length_nil]
  dsimp [W]
  rw [hVl]
  omega

end D5.S3.Combinatorics.FreeGroups.NormalIndependenceWords
