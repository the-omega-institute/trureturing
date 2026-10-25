/- GID: D5/S3/Arith/Lattices/Golay/GolayOctadCount
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/Golay/GolayOctadCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=bounded-enumeration; basis=consumer=D5/S3/Arith/Lattices/Golay/LeechMinimalCount.shortest_vectors_card
   digest: Kernel enumeration of the actual Golay octads. -/

import D5.S3.Arith.Lattices.Golay.GolayEncoder
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

open scoped BigOperators
namespace D5.S3.Arith.Lattices.Golay.GolayOctadCount
open GolayEncoder

abbrev Octad := {c : code // weight (c : Word) = 8}

def blockCode (p : Fin 64 × Fin 64) : code :=
  ⟨encode (message (p.1.val * 64 + p.2.val)), ⟨_, rfl⟩⟩

/-- Every pair is a distinct actual codeword; leading zeroes are retained. -/
noncomputable def blockCodeEquiv : (Fin 64 × Fin 64) ≃ code :=
  Equiv.ofBijective blockCode (by
    constructor
    · intro p q hpq
      have h := encode_injective (congrArg Subtype.val hpq)
      let pn : Fin 4096 := ⟨p.1.val * 64 + p.2.val, by omega⟩
      let qn : Fin 4096 := ⟨q.1.val * 64 + q.2.val, by omega⟩
      have hn : pn = qn := message_injective h
      have hv := congrArg Fin.val hn
      apply Prod.ext <;> apply Fin.ext <;> dsimp [pn, qn] at hv <;> omega
    · intro c
      obtain ⟨m, hm⟩ := c.property
      obtain ⟨n, hn⟩ := message_surjective m
      let p : Fin 64 × Fin 64 :=
        (⟨n.val / 64, by omega⟩, ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩)
      refine ⟨p, ?_⟩
      apply Subtype.ext
      change encode (message (n.val / 64 * 64 + n.val % 64)) = c.val
      have he : n.val / 64 * 64 + n.val % 64 = n.val := by omega
      rw [he, hn, hm])

abbrev BlockOctad :=
  {p : Fin 64 × Fin 64 // weight (blockCode p : Word) = 8}

noncomputable def octadEquivBlock : Octad ≃ BlockOctad where
  toFun c := ⟨blockCodeEquiv.symm c.val, by
    change weight (blockCodeEquiv (blockCodeEquiv.symm c.val) : Word) = 8
    simpa using c.property⟩
  invFun p := ⟨blockCodeEquiv p.val, p.property⟩
  left_inv c := by apply Subtype.ext; exact blockCodeEquiv.apply_symm_apply c.val
  right_inv p := by apply Subtype.ext; exact blockCodeEquiv.symm_apply_apply p.val

private def octadBlock (b : ℕ) : ℕ :=
  ∑ l : Fin 64, if weight (encode (message (b * 64 + l.val))) = 8 then 1 else 0

private theorem octad_block_0 : octadBlock 0 = 45 := by decide +kernel
private theorem octad_block_1 : octadBlock 1 = 33 := by decide +kernel
private theorem octad_block_2 : octadBlock 2 = 33 := by decide +kernel
private theorem octad_block_3 : octadBlock 3 = 19 := by decide +kernel
private theorem octad_block_4 : octadBlock 4 = 19 := by decide +kernel
private theorem octad_block_5 : octadBlock 5 = 33 := by decide +kernel
private theorem octad_block_6 : octadBlock 6 = 9 := by decide +kernel
private theorem octad_block_7 : octadBlock 7 = 19 := by decide +kernel
private theorem octad_block_8 : octadBlock 8 = 19 := by decide +kernel
private theorem octad_block_9 : octadBlock 9 = 9 := by decide +kernel
private theorem octad_block_10 : octadBlock 10 = 33 := by decide +kernel
private theorem octad_block_11 : octadBlock 11 = 19 := by decide +kernel
private theorem octad_block_12 : octadBlock 12 = 3 := by decide +kernel
private theorem octad_block_13 : octadBlock 13 = 9 := by decide +kernel
private theorem octad_block_14 : octadBlock 14 = 9 := by decide +kernel
private theorem octad_block_15 : octadBlock 15 = 19 := by decide +kernel
private theorem octad_block_16 : octadBlock 16 = 9 := by decide +kernel
private theorem octad_block_17 : octadBlock 17 = 19 := by decide +kernel
private theorem octad_block_18 : octadBlock 18 = 3 := by decide +kernel
private theorem octad_block_19 : octadBlock 19 = 9 := by decide +kernel
private theorem octad_block_20 : octadBlock 20 = 33 := by decide +kernel
private theorem octad_block_21 : octadBlock 21 = 19 := by decide +kernel
private theorem octad_block_22 : octadBlock 22 = 19 := by decide +kernel
private theorem octad_block_23 : octadBlock 23 = 9 := by decide +kernel
private theorem octad_block_24 : octadBlock 24 = 1 := by decide +kernel
private theorem octad_block_25 : octadBlock 25 = 3 := by decide +kernel
private theorem octad_block_26 : octadBlock 26 = 3 := by decide +kernel
private theorem octad_block_27 : octadBlock 27 = 9 := by decide +kernel
private theorem octad_block_28 : octadBlock 28 = 9 := by decide +kernel
private theorem octad_block_29 : octadBlock 29 = 3 := by decide +kernel
private theorem octad_block_30 : octadBlock 30 = 19 := by decide +kernel
private theorem octad_block_31 : octadBlock 31 = 9 := by decide +kernel
private theorem octad_block_32 : octadBlock 32 = 3 := by decide +kernel
private theorem octad_block_33 : octadBlock 33 = 9 := by decide +kernel
private theorem octad_block_34 : octadBlock 34 = 9 := by decide +kernel
private theorem octad_block_35 : octadBlock 35 = 19 := by decide +kernel
private theorem octad_block_36 : octadBlock 36 = 3 := by decide +kernel
private theorem octad_block_37 : octadBlock 37 = 1 := by decide +kernel
private theorem octad_block_38 : octadBlock 38 = 9 := by decide +kernel
private theorem octad_block_39 : octadBlock 39 = 3 := by decide +kernel
private theorem octad_block_40 : octadBlock 40 = 19 := by decide +kernel
private theorem octad_block_41 : octadBlock 41 = 33 := by decide +kernel
private theorem octad_block_42 : octadBlock 42 = 9 := by decide +kernel
private theorem octad_block_43 : octadBlock 43 = 19 := by decide +kernel
private theorem octad_block_44 : octadBlock 44 = 19 := by decide +kernel
private theorem octad_block_45 : octadBlock 45 = 9 := by decide +kernel
private theorem octad_block_46 : octadBlock 46 = 9 := by decide +kernel
private theorem octad_block_47 : octadBlock 47 = 3 := by decide +kernel
private theorem octad_block_48 : octadBlock 48 = 1 := by decide +kernel
private theorem octad_block_49 : octadBlock 49 = 0 := by decide +kernel
private theorem octad_block_50 : octadBlock 50 = 3 := by decide +kernel
private theorem octad_block_51 : octadBlock 51 = 1 := by decide +kernel
private theorem octad_block_52 : octadBlock 52 = 1 := by decide +kernel
private theorem octad_block_53 : octadBlock 53 = 3 := by decide +kernel
private theorem octad_block_54 : octadBlock 54 = 3 := by decide +kernel
private theorem octad_block_55 : octadBlock 55 = 9 := by decide +kernel
private theorem octad_block_56 : octadBlock 56 = 9 := by decide +kernel
private theorem octad_block_57 : octadBlock 57 = 3 := by decide +kernel
private theorem octad_block_58 : octadBlock 58 = 3 := by decide +kernel
private theorem octad_block_59 : octadBlock 59 = 1 := by decide +kernel
private theorem octad_block_60 : octadBlock 60 = 9 := by decide +kernel
private theorem octad_block_61 : octadBlock 61 = 19 := by decide +kernel
private theorem octad_block_62 : octadBlock 62 = 3 := by decide +kernel
private theorem octad_block_63 : octadBlock 63 = 9 := by decide +kernel

/-- Exhaustive computation is only over 4096 messages, in 64 small blocks. -/
theorem octad_card : Nat.card Octad = 759 := by
  rw [Nat.card_congr octadEquivBlock, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  change (∑ b : Fin 64, octadBlock b.val) = 759
  have hb : ∀ b : Fin 64, octadBlock b.val =
      (![45, 33, 33, 19, 19, 33, 9, 19, 19, 9, 33, 19, 3, 9, 9, 19, 9, 19, 3, 9, 33, 19, 19, 9, 1, 3, 3, 9, 9, 3, 19, 9, 3, 9, 9, 19, 3, 1, 9, 3, 19, 33, 9, 19, 19, 9, 9, 3, 1, 0, 3, 1, 1, 3, 3, 9, 9, 3, 3, 1, 9, 19, 3, 9] : Fin 64 → ℕ) b := by
    intro b
    fin_cases b
    · exact octad_block_0
    · exact octad_block_1
    · exact octad_block_2
    · exact octad_block_3
    · exact octad_block_4
    · exact octad_block_5
    · exact octad_block_6
    · exact octad_block_7
    · exact octad_block_8
    · exact octad_block_9
    · exact octad_block_10
    · exact octad_block_11
    · exact octad_block_12
    · exact octad_block_13
    · exact octad_block_14
    · exact octad_block_15
    · exact octad_block_16
    · exact octad_block_17
    · exact octad_block_18
    · exact octad_block_19
    · exact octad_block_20
    · exact octad_block_21
    · exact octad_block_22
    · exact octad_block_23
    · exact octad_block_24
    · exact octad_block_25
    · exact octad_block_26
    · exact octad_block_27
    · exact octad_block_28
    · exact octad_block_29
    · exact octad_block_30
    · exact octad_block_31
    · exact octad_block_32
    · exact octad_block_33
    · exact octad_block_34
    · exact octad_block_35
    · exact octad_block_36
    · exact octad_block_37
    · exact octad_block_38
    · exact octad_block_39
    · exact octad_block_40
    · exact octad_block_41
    · exact octad_block_42
    · exact octad_block_43
    · exact octad_block_44
    · exact octad_block_45
    · exact octad_block_46
    · exact octad_block_47
    · exact octad_block_48
    · exact octad_block_49
    · exact octad_block_50
    · exact octad_block_51
    · exact octad_block_52
    · exact octad_block_53
    · exact octad_block_54
    · exact octad_block_55
    · exact octad_block_56
    · exact octad_block_57
    · exact octad_block_58
    · exact octad_block_59
    · exact octad_block_60
    · exact octad_block_61
    · exact octad_block_62
    · exact octad_block_63
  simp_rw [hb]
  decide +kernel

#print axioms octad_card
end D5.S3.Arith.Lattices.Golay.GolayOctadCount
