/- GID: D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/BinaryEAAttainmentRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Quantum/Codes/BinaryEAAttainment.Attainment; result=D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation.result; claim=D5/S3/Quantum/Codes/BinaryEAAttainment.Attainment
   digest: No binary entanglement-assisted stabilizer parameters in the specified family attain the Singleton equality. -/

import D5.S3.Quantum.Codes.BinaryEAAttainmentBridge
import D5.S3.Quantum.Codes.BinaryEAShorteningLengthSeven

/-!
The binary symplectic obstruction to exact attainment at every length in scope.

admission_basis: open-problem-resolution (#34860; Refuted).
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
-/

set_option autoImplicit false

namespace D5.S3.Quantum.Codes.BinaryEAAttainmentRefutation

open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (sp_alt)

/-- The exact binary attainment event is impossible. -/
theorem result : ¬ BinaryEAAttainment.Attainment := by
  apply BinaryEAAttainmentBridge.refute_attainment_of_length_seven_rank_two
  rintro U hU hH hzeros ⟨i, hi⟩
  exact BinaryEAShortening.length_seven_no_rank_two_site
    (BinaryEAAttainment.radical U) U inf_le_left hH hU
    (fun h hh u hu => (sp_alt 7).isRefl u h (hh.2 u hu)) hzeros i hi

#print axioms result

end D5.S3.Quantum.Codes.BinaryEAAttainmentRefutation
