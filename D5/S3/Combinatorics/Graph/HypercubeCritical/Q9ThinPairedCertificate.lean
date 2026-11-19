import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinExtensionReduction

/-! The paired thin Q9 case is covered by coordinate images of the existing
weighted-edge certificates. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinPairedCertificate

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9ThinExtensionReduction
  (pairedHighs eq_pairedHighs_of_signing exists_paired_cube_of_extension)
open Q9SeventyTwoSignedCompletion (signsFromMask support)
open private Witness Witness.mk Witness.representative rowChecked row_preimages from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinOrbitCertificate
open private image_adj_iff card_le_of_map_representative from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinExtensionReduction

attribute [local instance] Classical.propDecidable

private def transports : Array (Fin 7 × (Fin 9 → Fin 9) × BitVec 9) := #[
  (6, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 0),
  (3, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 18),
  (3, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 36),
  (4, ![0, 2, 3, 4, 5, 6, 1, 7, 8], 0),
  (3, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 54),
  (5, ![0, 1, 6, 5, 4, 3, 2, 7, 8], 0),
  (5, ![0, 6, 1, 5, 3, 4, 2, 7, 8], 0),
  (3, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 0),
  (3, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 72),
  (4, ![0, 2, 4, 3, 5, 1, 6, 7, 8], 0),
  (4, ![0, 4, 2, 3, 1, 5, 6, 7, 8], 0),
  (3, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 126),
  (2, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 0),
  (3, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 108),
  (3, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 90),
  (5, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 0),
  (3, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 90),
  (5, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 0),
  (2, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 0),
  (3, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 108),
  (4, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 0),
  (3, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 126),
  (3, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 72),
  (4, ![0, 2, 1, 6, 5, 4, 3, 7, 8], 0),
  (5, ![0, 6, 5, 1, 3, 2, 4, 7, 8], 0),
  (3, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 0),
  (3, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 54),
  (5, ![0, 1, 3, 2, 4, 6, 5, 7, 8], 0),
  (3, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 36),
  (4, ![0, 2, 6, 1, 5, 3, 4, 7, 8], 0),
  (6, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 0),
  (3, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 18),
  (3, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 108),
  (2, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 0),
  (5, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 0),
  (3, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 90),
  (4, ![0, 5, 4, 6, 2, 1, 3, 7, 8], 0),
  (3, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 72),
  (3, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 126),
  (4, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 0),
  (5, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 0),
  (3, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 54),
  (3, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 0),
  (5, ![0, 3, 1, 2, 6, 4, 5, 7, 8], 0),
  (3, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 18),
  (6, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 0),
  (4, ![0, 6, 2, 1, 3, 5, 4, 7, 8], 0),
  (3, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 36),
  (4, ![0, 5, 6, 4, 2, 3, 1, 7, 8], 0),
  (3, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 36),
  (3, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 18),
  (6, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 0),
  (3, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 0),
  (5, ![0, 3, 4, 5, 6, 1, 2, 7, 8], 0),
  (5, ![0, 4, 3, 5, 1, 6, 2, 7, 8], 0),
  (3, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 54),
  (3, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 126),
  (4, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 0),
  (4, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 0),
  (3, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 72),
  (5, ![0, 4, 5, 3, 1, 2, 6, 7, 8], 0),
  (3, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 90),
  (3, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 108),
  (2, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 0),
  (3, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 126),
  (4, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 0),
  (4, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 0),
  (3, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 72),
  (5, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 0),
  (3, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 90),
  (3, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 108),
  (2, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 0),
  (4, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 0),
  (3, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 36),
  (3, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 18),
  (6, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 0),
  (3, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 0),
  (5, ![0, 3, 5, 1, 6, 2, 4, 7, 8], 0),
  (5, ![0, 5, 3, 1, 2, 6, 4, 7, 8], 0),
  (3, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 54),
  (5, ![0, 4, 6, 5, 1, 3, 2, 7, 8], 0),
  (3, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 54),
  (3, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 0),
  (5, ![0, 3, 1, 5, 6, 4, 2, 7, 8], 0),
  (3, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 18),
  (6, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 0),
  (4, ![0, 6, 2, 4, 3, 5, 1, 7, 8], 0),
  (3, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 36),
  (3, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 108),
  (2, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 0),
  (5, ![0, 5, 1, 3, 2, 4, 6, 7, 8], 0),
  (3, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 90),
  (4, ![0, 6, 4, 2, 3, 1, 5, 7, 8], 0),
  (3, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 72),
  (3, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 126),
  (4, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 0),
  (5, ![0, 6, 4, 5, 3, 1, 2, 7, 8], 0),
  (3, ![0, 1, 5, 6, 4, 2, 3, 7, 8], 0),
  (3, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 54),
  (5, ![0, 1, 3, 5, 4, 6, 2, 7, 8], 0),
  (3, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 36),
  (4, ![0, 2, 6, 4, 5, 3, 1, 7, 8], 0),
  (6, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 0),
  (3, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 18),
  (3, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 90),
  (5, ![0, 1, 5, 3, 4, 2, 6, 7, 8], 0),
  (2, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 0),
  (3, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 108),
  (4, ![0, 4, 6, 2, 1, 3, 5, 7, 8], 0),
  (3, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 126),
  (3, ![0, 5, 1, 6, 2, 4, 3, 7, 8], 72),
  (4, ![0, 2, 1, 3, 5, 4, 6, 7, 8], 0),
  (3, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 72),
  (4, ![0, 2, 4, 6, 5, 1, 3, 7, 8], 0),
  (4, ![0, 4, 2, 6, 1, 5, 3, 7, 8], 0),
  (3, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 126),
  (2, ![0, 4, 5, 6, 1, 2, 3, 7, 8], 0),
  (3, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 108),
  (3, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 90),
  (5, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 0),
  (6, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 0),
  (3, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 18),
  (3, ![0, 5, 6, 1, 2, 3, 4, 7, 8], 36),
  (4, ![0, 2, 3, 1, 5, 6, 4, 7, 8], 0),
  (3, ![0, 1, 2, 6, 4, 5, 3, 7, 8], 54),
  (5, ![0, 1, 6, 2, 4, 3, 5, 7, 8], 0),
  (5, ![0, 6, 1, 2, 3, 4, 5, 7, 8], 0),
  (3, ![0, 1, 2, 3, 4, 5, 6, 7, 8], 0),
]

private def row (n : Fin 128) : Witness :=
  let (k, axes, origin) := transports[n.val]?.getD (0, id, 0)
  Witness.mk pairedHighs n k axes origin 0

private def blockIndex (b : Fin 16) (i : Fin 8) : Fin 128 :=
  ⟨b.val * 8 + i.val, by omega⟩

private def checkBlock (b : Fin 16) : Bool :=
  (List.finRange 8).all fun i => rowChecked false (row (blockIndex b i))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_0 : checkBlock 0 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_1 : checkBlock 1 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_2 : checkBlock 2 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_3 : checkBlock 3 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_4 : checkBlock 4 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_5 : checkBlock 5 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_6 : checkBlock 6 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_7 : checkBlock 7 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_8 : checkBlock 8 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_9 : checkBlock 9 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_10 : checkBlock 10 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_11 : checkBlock 11 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_12 : checkBlock 12 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_13 : checkBlock 13 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_14 : checkBlock 14 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check eight explicit coordinate transports with their reconstructed vertices.
private theorem checked_15 : checkBlock 15 = true := by decide +kernel

private theorem checked (b : Fin 16) : checkBlock b = true := by
  fin_cases b
  · exact checked_0
  · exact checked_1
  · exact checked_2
  · exact checked_3
  · exact checked_4
  · exact checked_5
  · exact checked_6
  · exact checked_7
  · exact checked_8
  · exact checked_9
  · exact checked_10
  · exact checked_11
  · exact checked_12
  · exact checked_13
  · exact checked_14
  · exact checked_15

private theorem row_checked (n : Fin 128) : rowChecked false (row n) = true := by
  let b : Fin 16 := ⟨n.val / 8, by omega⟩
  let i : Fin 8 := ⟨n.val % 8, Nat.mod_lt _ (by decide)⟩
  have he : blockIndex b i = n := by
    apply Fin.ext
    change n.val / 8 * 8 + n.val % 8 = n.val
    omega
  rw [← he]
  exact List.all_eq_true.mp (checked b) i (List.mem_finRange i)

set_option maxRecDepth 8192 in
/-- A 72-vertex Huang-balanced cubic component with a 20-vertex coordinate
half cannot be a closed component of a 258-vertex induced subcubic set. -/
theorem no_thin_component_of_extension {U C : Finset (Q 9)} (hU : U.card = 258)
    (hC : C.card = 72) (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20)
    (hsub : C ⊆ U) (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hdeg : ∀ x ∈ U, (U.filter ((hypercube 9).Adj x)).card ≤ 3) : False := by
  obtain ⟨g, σ, highs, signs, hg, hh, hm, hCeq⟩ :=
    exists_paired_cube_of_extension hU hC hr hb b hs hsub hclosed hdeg
  have hhigh : highs = pairedHighs := eq_pairedHighs_of_signing hh hm
  subst highs
  obtain ⟨e, he, hrep⟩ := row_preimages false (row signs) (row_checked signs)
  have hrep' : Q9ThinEdgeCertificates.support (Witness.representative (row signs)) ⊆
      (support false (cubeBitVec 9 ∘ pairedHighs) (signsFromMask signs)).map e.toEmbedding := hrep
  rw [← hCeq] at hrep'
  change _ ⊆ (C.image g.toEmbedding).map e.toEmbedding at hrep'
  rw [← Finset.map_eq_image g.toEmbedding C, Finset.map_map] at hrep'
  have h := card_le_of_map_representative U C (Witness.representative (row signs)) (g.trans e)
    (fun x y => (he (g x) (g y)).trans (image_adj_iff g σ hg x y)) hC hrep' hsub hclosed hdeg
  omega

#print axioms no_thin_component_of_extension

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinPairedCertificate
