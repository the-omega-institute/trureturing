/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueTrees
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueTrees.residue_tree_ok
   digest: Exact assembly of the twenty complete residue-tree certificates. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP19
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP23
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP29
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP31
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP37
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP41
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP43
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP47
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP53
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP59
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP61
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP67
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP71
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP73
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP79
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP83
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP89
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP97
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP101
import D5.S3.Arith.Divisors.ErdosNicolas.Data.ResidueP103

/-! The maximum-prime domain is exactly the twenty primes in the closed interval. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas.Data.ResidueTrees

private theorem prime_values :
    largePrimes 107 =
      {19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
        103} := by
  unfold largePrimes
  decide +kernel

theorem residue_tree_ok : ResidueTreeOK := by
  intro p hp
  rw [prime_values] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ResidueP19.residue_step
  · exact ResidueP23.residue_step
  · exact ResidueP29.residue_step
  · exact ResidueP31.residue_step
  · exact ResidueP37.residue_step
  · exact ResidueP41.residue_step
  · exact ResidueP43.residue_step
  · exact ResidueP47.residue_step
  · exact ResidueP53.residue_step
  · exact ResidueP59.residue_step
  · exact ResidueP61.residue_step
  · exact ResidueP67.residue_step
  · exact ResidueP71.residue_step
  · exact ResidueP73.residue_step
  · exact ResidueP79.residue_step
  · exact ResidueP83.residue_step
  · exact ResidueP89.residue_step
  · exact ResidueP97.residue_step
  · exact ResidueP101.residue_step
  · exact ResidueP103.residue_step

#print axioms residue_tree_ok

end D5.S3.Arith.ErdosNicolas.Data.ResidueTrees
