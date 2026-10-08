/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedMatching
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedMatching
   mirror-E: none(waiver:cyclic-reflection-interface)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Fin.Basic]
   utility: none
   digest: Cyclic nested copies are precisely odd rank reflections. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedRamseyDefs
import Mathlib.Algebra.Group.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedMatching

open DihedralRamseyDefs CyclicRamseyDefs NestedRamseyDefs

theorem cyclic_iff_reflection {a n : ℕ} (hap : 0 < a) (ha : a % 2 = 0)
    (G : SimpleGraph (Fin n)) :
    CyclicEmbeddable (nestMatching a) G ↔
      ∃ ψ : Fin a → Fin n, StrictMono ψ ∧ ∃ c : Fin a,
        c.val % 2 = 1 ∧ ∀ i j : Fin a,
          (i.val + j.val) % a = c.val → G.Adj (ψ i) (ψ j) := by
  let : NeZero a := ⟨by omega⟩
  let z : Fin a := ⟨a - 1, by omega⟩
  have hz : ∀ i j : Fin a, i + j = z ↔ i.val + j.val + 1 = a := by
    intro i j
    rw [Fin.ext_iff, Fin.val_add_eq_ite]
    dsimp [z]
    have := i.isLt
    have := j.isLt
    split <;> omega
  have he : ∀ i j : Fin a, (nestMatching a).Adj i j ↔ i + j = z := by
    intro i j
    rw [nestMatching, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, hij | hij⟩ <;> apply (hz i j).mpr <;> omega
    · intro hij
      have hh := (hz i j).mp hij
      refine ⟨?_, Or.inl hh⟩
      intro h
      subst j
      omega
  have rot : ∀ s (i : Fin a),
      dihedralPerm s false i = i + (⟨s % a, Nat.mod_lt _ hap⟩ : Fin a) := by
    intro s i
    apply Fin.ext
    simp only [dihedralPerm, Bool.false_eq_true, ↓reduceIte, Fin.val_add]
    exact (Nat.add_mod_mod _ _ _).symm
  constructor
  · rintro ⟨s, ψ, hψ, hG⟩
    let t : Fin a := ⟨s % a, Nat.mod_lt _ hap⟩
    let c := z + t + t
    refine ⟨ψ, hψ, c, ?_, ?_⟩
    · have hc : c.val = (a - 1 + 2 * t.val) % a := by
        simp only [c, z, Fin.val_add, Nat.mod_add_mod]
        congr 1
        omega
      rw [hc, Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero ha)]
      omega
    · intro i j hij
      have hc : i + j = c := Fin.ext hij
      have huv : (i - t) + (j - t) = z := by
        dsimp [c] at hc
        have := congrArg (fun x : Fin a => x - t - t) hc
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have h := hG (i - t) (j - t) ((he _ _).mpr huv)
      simpa [rot, t] using h
  · rintro ⟨ψ, hψ, c, hc, hG⟩
    let t : Fin a := ⟨(c.val + 1) / 2, by have := c.isLt; omega⟩
    have hct : c = z + t + t := by
      apply Fin.ext
      have htv : 2 * t.val = c.val + 1 := by dsimp [t]; omega
      simp only [Fin.val_add]
      rw [Nat.mod_add_mod]
      change c.val = (a - 1 + t.val + t.val) % a
      have hh : a - 1 + t.val + t.val = a + c.val := by omega
      simp [hh, Nat.mod_eq_of_lt c.isLt]
    refine ⟨t.val, ψ, hψ, ?_⟩
    intro i j hij
    have hh := (he i j).mp hij
    apply hG
    have hsum : (i + t) + (j + t) = c := by
      rw [hct]
      calc
        _ = (i + j) + t + t := by simp only [add_assoc, add_left_comm, add_comm]
        _ = z + t + t := by rw [hh]
    have ht : (⟨t.val % a, Nat.mod_lt _ hap⟩ : Fin a) = t := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt t.isLt
    simpa only [rot, ht, Fin.val_add] using congrArg Fin.val hsum

end D5.S3.Combinatorics.DihedralRamsey.NestedMatching
