/- GID: D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate2
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate2
   mirror-E: none(waiver:finite-marker-successor-completeness)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization.prefix_path_realization; instance=D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixTable
   digest: Exact marker successor reconstruction for indices 1024 through 1535. -/

/-
proof_shape: content (prefix_realization_rows_2)
escape_witness: Kernel reduction checks every reconstructed successor in the stated finite interval.
admission_basis: escape-witness
Direct frozen dependencies: none; MarkedPrefixCertificates is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.MarkedPrefixCertificates
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open MarkedPrefixCertificates

theorem prefix_realization_rows_2 (i : ℕ) (hlo : 1024 ≤ i) (hi : i < 1536) :
    prefixRealizationRowCheck i=true := by
  have blocks : ∀ b : Fin 8,
      prefixRealizationBlockCheck (1024+64*b.val) (min 64 (512-64*b.val))=true := by
    intro b
    fin_cases b <;> decide
  have hb:=blocks ⟨(i-1024)/64,by omega⟩
  dsimp [prefixRealizationBlockCheck] at hb
  have hk : (i-1024)%64 ∈ List.range (min 64 (512-64*((i-1024)/64))) := by
    simp only [List.mem_range];omega
  have hh:=List.all_eq_true.mp hb ((i-1024)%64) hk
  change prefixRealizationRowCheck (1024+64*((i-1024)/64)+(i-1024)%64)=true at hh
  rw [show 1024+64*((i-1024)/64)+(i-1024)%64=i by omega] at hh
  exact hh

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.prefix_realization_rows_2
