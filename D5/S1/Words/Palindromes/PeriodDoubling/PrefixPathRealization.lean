/- GID: D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization
   mirror-E: none(waiver:complete-symbolic-marker-realization)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixRigidity.marked_prefix_rigidity_and_charge; instance=D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.prefixTable
   digest: Symbolic marked-prefix paths lift to the complete finite certificate graph. -/

/-
proof_shape: content (prefix_path_realization)
escape_witness: Complete finite successor checks construct indexed paths for arbitrary symbolic runs.
admission_basis: escape-witness
Direct frozen dependencies: none; MarkedPrefixCertificates is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.PrefixRealizationCertificate0
import D5.S1.Words.Palindromes.PeriodDoubling.PrefixRealizationCertificate1
import D5.S1.Words.Palindromes.PeriodDoubling.PrefixRealizationCertificate2
import D5.S1.Words.Palindromes.PeriodDoubling.PrefixRealizationCertificate3
import D5.S1.Words.Palindromes.PeriodDoubling.PrefixRealizationCertificate4
import D5.S1.Words.Palindromes.PeriodDoubling.PrefixRealizationCertificate5
import D5.S1.Words.Palindromes.PeriodDoubling.PrefixRealizationCertificate6
import D5.S1.Words.Palindromes.PeriodDoubling.PrefixRealizationCertificate7
import D5.S1.Words.Palindromes.PeriodDoubling.PrefixRealizationCertificate8
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open MarkedPrefixCertificates

/-- The literal marker transition relation on full states, without endpoint restrictions. -/
def prefixRawAutomaton : NFA (ℤ × ℤ × ℤ × ℤ) (List ℤ) where
  start := Set.univ
  step s a := {t | (t,a) ∈ successors s}
  accept := Set.univ

/-- No literal marker transition can leave the indexed graph. -/
theorem prefix_path_realization (charge : Bool) {s t : List ℤ}
    {xs : List (ℤ × ℤ × ℤ × ℤ)} (p : prefixRawAutomaton.Path s t xs)
    (u : Fin 4262) (hu : (prefixTable u.val).1=s) :
    ∃ v : Fin 4262, (prefixTable v.val).1=t ∧
      Nonempty ((prefixAutomaton charge).Path u v xs) := by
  have checked (i : ℕ) (hi : i < 4262) : prefixRealizationRowCheck i=true := by
    by_cases h0 : i < 512
    · exact prefix_realization_rows_0 i (by omega) h0
    by_cases h1 : i < 1024
    · exact prefix_realization_rows_1 i (by omega) h1
    by_cases h2 : i < 1536
    · exact prefix_realization_rows_2 i (by omega) h2
    by_cases h3 : i < 2048
    · exact prefix_realization_rows_3 i (by omega) h3
    by_cases h4 : i < 2560
    · exact prefix_realization_rows_4 i (by omega) h4
    by_cases h5 : i < 3072
    · exact prefix_realization_rows_5 i (by omega) h5
    by_cases h6 : i < 3584
    · exact prefix_realization_rows_6 i (by omega) h6
    by_cases h7 : i < 4096
    · exact prefix_realization_rows_7 i (by omega) h7
    exact prefix_realization_rows_8 i (by omega) hi
  induction p generalizing u with
  | nil s => exact ⟨u,hu,⟨.nil u⟩⟩
  | cons q s t a xs he p ih =>
    have hr:=checked u.val u.isLt
    simp only [prefixRealizationRowCheck,Bool.and_eq_true] at hr
    have hexpected : (q,a) ∈ successors (prefixTable u.val).1 := by
      rw [hu];exact he
    have hcontains:=List.all_eq_true.mp hr.1 (q,a) hexpected
    have hmem : (q,a) ∈ ((prefixTable u.val).2.1).map (fun e => ((prefixTable e.1).1,e.2)) := by
      simpa only [List.contains_eq_mem,decide_eq_true_eq] using hcontains
    obtain ⟨e,he',heq⟩:=List.mem_map.mp hmem
    have hlt : e.1 < 4262 := of_decide_eq_true (List.all_eq_true.mp hr.2 e he')
    let v : Fin 4262:=⟨e.1,hlt⟩
    have hv : (prefixTable v.val).1=q := congrArg Prod.fst heq
    have ha : e.2=a := congrArg Prod.snd heq
    obtain ⟨w,hw,⟨pw⟩⟩:=ih v hv
    refine ⟨w,hw,⟨.cons v u w a xs ?_ pw⟩⟩
    change (e.1,a) ∈ (prefixTable u.val).2.1
    rw [← ha];exact he'

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.prefix_path_realization
