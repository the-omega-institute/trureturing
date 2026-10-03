/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalReverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalReverse
   mirror-E: none(waiver:royal-reversed-occurrence-queues)
   anchors: []
   utility: none
   digest: Reflects Dyck words and reverses their two interleaved occurrence queues. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalEncoding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse

open DyckStep NonnestingBasicRoyalEncoding

def reflection : DyckWord ≃ DyckWord := by
  classical
  let exchange : DyckStep → DyckStep
    | U => D
    | D => U
  have hU (s : List DyckStep) : (s.map exchange).count U = s.count D := by
    induction s with
    | nil => rfl
    | cons a s ih => cases a <;> simp [exchange, ih]
  have hD (s : List DyckStep) : (s.map exchange).count D = s.count U := by
    induction s with
    | nil => rfl
    | cons a s ih => cases a <;> simp [exchange, ih]
  let reflect (d : DyckWord) : DyckWord :=
    { toList := d.toList.reverse.map exchange
      count_U_eq_count_D := by
        rw [hU, hD, List.count_reverse, List.count_reverse, d.count_U_eq_count_D]
      count_D_le_count_U := by
        intro i
        rw [← List.map_take, List.take_reverse, hD, hU,
          List.count_reverse, List.count_reverse]
        have hp := d.count_D_le_count_U (d.toList.length - i); have htotal := d.count_U_eq_count_D
        have hs := d.toList.take_append_drop (d.toList.length - i)
        have hcU := congrArg (List.count U) hs; have hcD := congrArg (List.count D) hs
        simp only [List.count_append] at hcU hcD
        omega }
  have hinv : Function.Involutive reflect := by
    intro d; apply DyckWord.ext
    change (((d.toList.reverse.map exchange).reverse).map exchange) = d.toList
    rw [← List.map_reverse, List.reverse_reverse, List.map_map]
    have he : exchange ∘ exchange = id := by
      funext a
      cases a <;> rfl
    rw [he, List.map_id]
  exact ⟨reflect, reflect, hinv, hinv⟩
#print axioms reflection

end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse
