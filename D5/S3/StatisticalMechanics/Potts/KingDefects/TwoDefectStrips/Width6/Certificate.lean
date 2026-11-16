/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-six exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229753.result)
class_relabel: proof_shape=bind-only; consumers=transition_counts
bond_relabel: proof_shape=bind-only; consumers=transition_counts
canonical_successors: proof_shape=bind-only; consumers=transition_counts
class_counts: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=HardinA229753.result
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes0
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes1
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes2
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes3
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes4
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes5
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes6
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes7
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes8
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes9
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes10
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes11
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes12
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes13
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes14
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes15
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes16
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes17
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes18
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes19
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes20
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes21
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes22
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes23
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes24
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes25
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes26
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes27
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes28
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes29
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes30
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes31
/-! Every admissible boundary has the certified successor multiset. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Certificate
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

private theorem class_relabel (e : Equiv.Perm (Fin 4)) (p : Row) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl, Function.comp_apply, e.injective.eq_iff]

private theorem bond_relabel (E : Finset (Fin 6 × Fin 6))
    (e : Equiv.Perm (Fin 4)) (p r : Row) :
    bondDefects E (e ∘ p) (e ∘ r) = bondDefects E p r := by
  simp only [bondDefects, Function.comp_apply, e.injective.eq_iff]

private theorem canonical_successors (p : Row) (d : Fin 3) (hp : Valid p d.val)
    (hc : Canonical p) : successors p d.val = classList (cl p d.val) := by
  by_cases h0 : cl p d.val = 0
  · rw [h0]; exact Classes0.class_successors ⟨0, by decide⟩ p d hp hc h0
  by_cases h1 : cl p d.val = 1
  · rw [h1]; exact Classes0.class_successors ⟨1, by decide⟩ p d hp hc h1
  by_cases h2 : cl p d.val = 2
  · rw [h2]; exact Classes0.class_successors ⟨2, by decide⟩ p d hp hc h2
  by_cases h3 : cl p d.val = 3
  · rw [h3]; exact Classes1.class_successors ⟨0, by decide⟩ p d hp hc h3
  by_cases h4 : cl p d.val = 4
  · rw [h4]; exact Classes1.class_successors ⟨1, by decide⟩ p d hp hc h4
  by_cases h5 : cl p d.val = 5
  · rw [h5]; exact Classes1.class_successors ⟨2, by decide⟩ p d hp hc h5
  by_cases h6 : cl p d.val = 6
  · rw [h6]; exact Classes2.class_successors ⟨0, by decide⟩ p d hp hc h6
  by_cases h7 : cl p d.val = 7
  · rw [h7]; exact Classes2.class_successors ⟨1, by decide⟩ p d hp hc h7
  by_cases h8 : cl p d.val = 8
  · rw [h8]; exact Classes2.class_successors ⟨2, by decide⟩ p d hp hc h8
  by_cases h9 : cl p d.val = 9
  · rw [h9]; exact Classes3.class_successors ⟨0, by decide⟩ p d hp hc h9
  by_cases h10 : cl p d.val = 10
  · rw [h10]; exact Classes3.class_successors ⟨1, by decide⟩ p d hp hc h10
  by_cases h11 : cl p d.val = 11
  · rw [h11]; exact Classes3.class_successors ⟨2, by decide⟩ p d hp hc h11
  by_cases h12 : cl p d.val = 12
  · rw [h12]; exact Classes4.class_successors ⟨0, by decide⟩ p d hp hc h12
  by_cases h13 : cl p d.val = 13
  · rw [h13]; exact Classes4.class_successors ⟨1, by decide⟩ p d hp hc h13
  by_cases h14 : cl p d.val = 14
  · rw [h14]; exact Classes4.class_successors ⟨2, by decide⟩ p d hp hc h14
  by_cases h15 : cl p d.val = 15
  · rw [h15]; exact Classes5.class_successors ⟨0, by decide⟩ p d hp hc h15
  by_cases h16 : cl p d.val = 16
  · rw [h16]; exact Classes5.class_successors ⟨1, by decide⟩ p d hp hc h16
  by_cases h17 : cl p d.val = 17
  · rw [h17]; exact Classes5.class_successors ⟨2, by decide⟩ p d hp hc h17
  by_cases h18 : cl p d.val = 18
  · rw [h18]; exact Classes6.class_successors ⟨0, by decide⟩ p d hp hc h18
  by_cases h19 : cl p d.val = 19
  · rw [h19]; exact Classes6.class_successors ⟨1, by decide⟩ p d hp hc h19
  by_cases h20 : cl p d.val = 20
  · rw [h20]; exact Classes6.class_successors ⟨2, by decide⟩ p d hp hc h20
  by_cases h21 : cl p d.val = 21
  · rw [h21]; exact Classes7.class_successors ⟨0, by decide⟩ p d hp hc h21
  by_cases h22 : cl p d.val = 22
  · rw [h22]; exact Classes7.class_successors ⟨1, by decide⟩ p d hp hc h22
  by_cases h23 : cl p d.val = 23
  · rw [h23]; exact Classes7.class_successors ⟨2, by decide⟩ p d hp hc h23
  by_cases h24 : cl p d.val = 24
  · rw [h24]; exact Classes8.class_successors ⟨0, by decide⟩ p d hp hc h24
  by_cases h25 : cl p d.val = 25
  · rw [h25]; exact Classes8.class_successors ⟨1, by decide⟩ p d hp hc h25
  by_cases h26 : cl p d.val = 26
  · rw [h26]; exact Classes8.class_successors ⟨2, by decide⟩ p d hp hc h26
  by_cases h27 : cl p d.val = 27
  · rw [h27]; exact Classes9.class_successors ⟨0, by decide⟩ p d hp hc h27
  by_cases h28 : cl p d.val = 28
  · rw [h28]; exact Classes9.class_successors ⟨1, by decide⟩ p d hp hc h28
  by_cases h29 : cl p d.val = 29
  · rw [h29]; exact Classes9.class_successors ⟨2, by decide⟩ p d hp hc h29
  by_cases h30 : cl p d.val = 30
  · rw [h30]; exact Classes10.class_successors ⟨0, by decide⟩ p d hp hc h30
  by_cases h31 : cl p d.val = 31
  · rw [h31]; exact Classes10.class_successors ⟨1, by decide⟩ p d hp hc h31
  by_cases h32 : cl p d.val = 32
  · rw [h32]; exact Classes10.class_successors ⟨2, by decide⟩ p d hp hc h32
  by_cases h33 : cl p d.val = 33
  · rw [h33]; exact Classes11.class_successors ⟨0, by decide⟩ p d hp hc h33
  by_cases h34 : cl p d.val = 34
  · rw [h34]; exact Classes11.class_successors ⟨1, by decide⟩ p d hp hc h34
  by_cases h35 : cl p d.val = 35
  · rw [h35]; exact Classes11.class_successors ⟨2, by decide⟩ p d hp hc h35
  by_cases h36 : cl p d.val = 36
  · rw [h36]; exact Classes12.class_successors ⟨0, by decide⟩ p d hp hc h36
  by_cases h37 : cl p d.val = 37
  · rw [h37]; exact Classes12.class_successors ⟨1, by decide⟩ p d hp hc h37
  by_cases h38 : cl p d.val = 38
  · rw [h38]; exact Classes12.class_successors ⟨2, by decide⟩ p d hp hc h38
  by_cases h39 : cl p d.val = 39
  · rw [h39]; exact Classes13.class_successors ⟨0, by decide⟩ p d hp hc h39
  by_cases h40 : cl p d.val = 40
  · rw [h40]; exact Classes13.class_successors ⟨1, by decide⟩ p d hp hc h40
  by_cases h41 : cl p d.val = 41
  · rw [h41]; exact Classes13.class_successors ⟨2, by decide⟩ p d hp hc h41
  by_cases h42 : cl p d.val = 42
  · rw [h42]; exact Classes14.class_successors ⟨0, by decide⟩ p d hp hc h42
  by_cases h43 : cl p d.val = 43
  · rw [h43]; exact Classes14.class_successors ⟨1, by decide⟩ p d hp hc h43
  by_cases h44 : cl p d.val = 44
  · rw [h44]; exact Classes14.class_successors ⟨2, by decide⟩ p d hp hc h44
  by_cases h45 : cl p d.val = 45
  · rw [h45]; exact Classes15.class_successors ⟨0, by decide⟩ p d hp hc h45
  by_cases h46 : cl p d.val = 46
  · rw [h46]; exact Classes15.class_successors ⟨1, by decide⟩ p d hp hc h46
  by_cases h47 : cl p d.val = 47
  · rw [h47]; exact Classes15.class_successors ⟨2, by decide⟩ p d hp hc h47
  by_cases h48 : cl p d.val = 48
  · rw [h48]; exact Classes16.class_successors ⟨0, by decide⟩ p d hp hc h48
  by_cases h49 : cl p d.val = 49
  · rw [h49]; exact Classes16.class_successors ⟨1, by decide⟩ p d hp hc h49
  by_cases h50 : cl p d.val = 50
  · rw [h50]; exact Classes16.class_successors ⟨2, by decide⟩ p d hp hc h50
  by_cases h51 : cl p d.val = 51
  · rw [h51]; exact Classes17.class_successors ⟨0, by decide⟩ p d hp hc h51
  by_cases h52 : cl p d.val = 52
  · rw [h52]; exact Classes17.class_successors ⟨1, by decide⟩ p d hp hc h52
  by_cases h53 : cl p d.val = 53
  · rw [h53]; exact Classes17.class_successors ⟨2, by decide⟩ p d hp hc h53
  by_cases h54 : cl p d.val = 54
  · rw [h54]; exact Classes18.class_successors ⟨0, by decide⟩ p d hp hc h54
  by_cases h55 : cl p d.val = 55
  · rw [h55]; exact Classes18.class_successors ⟨1, by decide⟩ p d hp hc h55
  by_cases h56 : cl p d.val = 56
  · rw [h56]; exact Classes18.class_successors ⟨2, by decide⟩ p d hp hc h56
  by_cases h57 : cl p d.val = 57
  · rw [h57]; exact Classes19.class_successors ⟨0, by decide⟩ p d hp hc h57
  by_cases h58 : cl p d.val = 58
  · rw [h58]; exact Classes19.class_successors ⟨1, by decide⟩ p d hp hc h58
  by_cases h59 : cl p d.val = 59
  · rw [h59]; exact Classes19.class_successors ⟨2, by decide⟩ p d hp hc h59
  by_cases h60 : cl p d.val = 60
  · rw [h60]; exact Classes20.class_successors ⟨0, by decide⟩ p d hp hc h60
  by_cases h61 : cl p d.val = 61
  · rw [h61]; exact Classes20.class_successors ⟨1, by decide⟩ p d hp hc h61
  by_cases h62 : cl p d.val = 62
  · rw [h62]; exact Classes20.class_successors ⟨2, by decide⟩ p d hp hc h62
  by_cases h63 : cl p d.val = 63
  · rw [h63]; exact Classes21.class_successors ⟨0, by decide⟩ p d hp hc h63
  by_cases h64 : cl p d.val = 64
  · rw [h64]; exact Classes21.class_successors ⟨1, by decide⟩ p d hp hc h64
  by_cases h65 : cl p d.val = 65
  · rw [h65]; exact Classes21.class_successors ⟨2, by decide⟩ p d hp hc h65
  by_cases h66 : cl p d.val = 66
  · rw [h66]; exact Classes22.class_successors ⟨0, by decide⟩ p d hp hc h66
  by_cases h67 : cl p d.val = 67
  · rw [h67]; exact Classes22.class_successors ⟨1, by decide⟩ p d hp hc h67
  by_cases h68 : cl p d.val = 68
  · rw [h68]; exact Classes22.class_successors ⟨2, by decide⟩ p d hp hc h68
  by_cases h69 : cl p d.val = 69
  · rw [h69]; exact Classes23.class_successors ⟨0, by decide⟩ p d hp hc h69
  by_cases h70 : cl p d.val = 70
  · rw [h70]; exact Classes23.class_successors ⟨1, by decide⟩ p d hp hc h70
  by_cases h71 : cl p d.val = 71
  · rw [h71]; exact Classes23.class_successors ⟨2, by decide⟩ p d hp hc h71
  by_cases h72 : cl p d.val = 72
  · rw [h72]; exact Classes24.class_successors ⟨0, by decide⟩ p d hp hc h72
  by_cases h73 : cl p d.val = 73
  · rw [h73]; exact Classes24.class_successors ⟨1, by decide⟩ p d hp hc h73
  by_cases h74 : cl p d.val = 74
  · rw [h74]; exact Classes24.class_successors ⟨2, by decide⟩ p d hp hc h74
  by_cases h75 : cl p d.val = 75
  · rw [h75]; exact Classes25.class_successors ⟨0, by decide⟩ p d hp hc h75
  by_cases h76 : cl p d.val = 76
  · rw [h76]; exact Classes25.class_successors ⟨1, by decide⟩ p d hp hc h76
  by_cases h77 : cl p d.val = 77
  · rw [h77]; exact Classes25.class_successors ⟨2, by decide⟩ p d hp hc h77
  by_cases h78 : cl p d.val = 78
  · rw [h78]; exact Classes26.class_successors ⟨0, by decide⟩ p d hp hc h78
  by_cases h79 : cl p d.val = 79
  · rw [h79]; exact Classes26.class_successors ⟨1, by decide⟩ p d hp hc h79
  by_cases h80 : cl p d.val = 80
  · rw [h80]; exact Classes26.class_successors ⟨2, by decide⟩ p d hp hc h80
  by_cases h81 : cl p d.val = 81
  · rw [h81]; exact Classes27.class_successors ⟨0, by decide⟩ p d hp hc h81
  by_cases h82 : cl p d.val = 82
  · rw [h82]; exact Classes27.class_successors ⟨1, by decide⟩ p d hp hc h82
  by_cases h83 : cl p d.val = 83
  · rw [h83]; exact Classes27.class_successors ⟨2, by decide⟩ p d hp hc h83
  by_cases h84 : cl p d.val = 84
  · rw [h84]; exact Classes28.class_successors ⟨0, by decide⟩ p d hp hc h84
  by_cases h85 : cl p d.val = 85
  · rw [h85]; exact Classes28.class_successors ⟨1, by decide⟩ p d hp hc h85
  by_cases h86 : cl p d.val = 86
  · rw [h86]; exact Classes28.class_successors ⟨2, by decide⟩ p d hp hc h86
  by_cases h87 : cl p d.val = 87
  · rw [h87]; exact Classes29.class_successors ⟨0, by decide⟩ p d hp hc h87
  by_cases h88 : cl p d.val = 88
  · rw [h88]; exact Classes29.class_successors ⟨1, by decide⟩ p d hp hc h88
  by_cases h89 : cl p d.val = 89
  · rw [h89]; exact Classes29.class_successors ⟨2, by decide⟩ p d hp hc h89
  by_cases h90 : cl p d.val = 90
  · rw [h90]; exact Classes30.class_successors ⟨0, by decide⟩ p d hp hc h90
  by_cases h91 : cl p d.val = 91
  · rw [h91]; exact Classes30.class_successors ⟨1, by decide⟩ p d hp hc h91
  by_cases h92 : cl p d.val = 92
  · rw [h92]; exact Classes30.class_successors ⟨2, by decide⟩ p d hp hc h92
  by_cases h93 : cl p d.val = 93
  · rw [h93]; exact Classes31.class_successors ⟨0, by decide⟩ p d hp hc h93
  by_cases h94 : cl p d.val = 94
  · rw [h94]; exact Classes31.class_successors ⟨1, by decide⟩ p d hp hc h94
  have hh : cl p d.val = 95 := by apply Fin.ext; omega
  rw [hh]; exact Classes31.class_successors ⟨2, by decide⟩ p d hp hc hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem class_counts : ∀ c s : Fin 96, ((classList c).count s : ℤ) = T c s := by
  intro c
  fin_cases c <;> decide +kernel

theorem transition_counts (p : Row) (d : ℕ) (hp : Valid p d) (s : Fin 96) :
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d ∧
      cl r (d - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d) s := by
  obtain ⟨p', ⟨hnormal, e, he⟩, _⟩ := canonical_exists_unique p
  have hv : Valid p' d := by
    rw [he]
    simpa only [Valid, bond_relabel] using hp
  have hd : d < 3 := by change d ≤ 2 ∧ _ at hp; omega
  have hlist := canonical_successors p' ⟨d, hd⟩ hv hnormal
  have hT :
      (∑ r : Row, if bondDefects between p' r + bondDefects horizontal r r ≤ d ∧
        cl r (d - (bondDefects between p' r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p' d) s := by
    have h := TableBridge.count_successors
      (fun r : Row => bondDefects between p' r + bondDefects horizontal r r ≤ d)
      (fun r => cl r (d - (bondDefects between p' r + bondDefects horizontal r r))) s
    change (successors p' d).count s = _ at h
    rw [hlist] at h
    have hh : (∑ r : Row, if bondDefects between p' r + bondDefects horizontal r r ≤ d ∧
        cl r (d - (bondDefects between p' r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = ((classList (cl p' d)).count s : ℤ) := by
      exact_mod_cast h.symm
    exact hh.trans (class_counts _ _)
  rw [he] at hT
  let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 6 => e
  rw [← E.sum_comp] at hT
  change (∑ r : Row, if bondDefects between (e ∘ p) (e ∘ r) +
    bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d ∧
    cl (e ∘ r) (d - (bondDefects between (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
      T (cl (e ∘ p) d) s at hT
  simpa only [bond_relabel, class_relabel] using hT

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Certificate
