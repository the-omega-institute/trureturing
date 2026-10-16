/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarConeSoundness
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarConeSoundness
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Complete support coverage, cofactor classification and original-ray projection. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SupportColumnZero
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SupportColumnOne
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SupportColumnTwo
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SupportColumnsThreeFour
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SupportColumnsFiveEight
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SupportColumnsNineFifteen
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open NonnegativeKernelCircuit NonnegativeKernelCofactor
open D5.S3.Arith.Lattices.CofactorKernel (cofactor augment kernel_cross_identity)
open UniformSpectralBound.SharedSpectral
noncomputable section

namespace ScalarCertificate

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem checked_tuple : ∀ (a : Fin 16) (e : Fin 4 → Fin 19),
    e ∈ fourTuples ⟨a.val, by omega⟩ → ∃ w, CaseValid e w := by
  classical
  intro a
  fin_cases a
  · intro e he
    change e ∈ fourTuples 0 at he
    rw [← align00] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block00 k).2, ?_⟩
    rw [← he]
    exact valid00 k
  · intro e he
    change e ∈ fourTuples 1 at he
    rw [← align01] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block01 k).2, ?_⟩
    rw [← he]
    exact valid01 k
  · intro e he
    change e ∈ fourTuples 2 at he
    rw [← align02] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block02 k).2, ?_⟩
    rw [← he]
    exact valid02 k
  · intro e he
    change e ∈ fourTuples 3 at he
    rw [← align03] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block03 k).2, ?_⟩
    rw [← he]
    exact valid03 k
  · intro e he
    change e ∈ fourTuples 4 at he
    rw [← align04] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block04 k).2, ?_⟩
    rw [← he]
    exact valid04 k
  · intro e he
    change e ∈ fourTuples 5 at he
    rw [← align05] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block05 k).2, ?_⟩
    rw [← he]
    exact valid05 k
  · intro e he
    change e ∈ fourTuples 6 at he
    rw [← align06] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block06 k).2, ?_⟩
    rw [← he]
    exact valid06 k
  · intro e he
    change e ∈ fourTuples 7 at he
    rw [← align07] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block07 k).2, ?_⟩
    rw [← he]
    exact valid07 k
  · intro e he
    change e ∈ fourTuples 8 at he
    rw [← align08] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block08 k).2, ?_⟩
    rw [← he]
    exact valid08 k
  · intro e he
    change e ∈ fourTuples 9 at he
    rw [← align09] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block09 k).2, ?_⟩
    rw [← he]
    exact valid09 k
  · intro e he
    change e ∈ fourTuples 10 at he
    rw [← align10] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block10 k).2, ?_⟩
    rw [← he]
    exact valid10 k
  · intro e he
    change e ∈ fourTuples 11 at he
    rw [← align11] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block11 k).2, ?_⟩
    rw [← he]
    exact valid11 k
  · intro e he
    change e ∈ fourTuples 12 at he
    rw [← align12] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block12 k).2, ?_⟩
    rw [← he]
    exact valid12 k
  · intro e he
    change e ∈ fourTuples 13 at he
    rw [← align13] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block13 k).2, ?_⟩
    rw [← he]
    exact valid13 k
  · intro e he
    change e ∈ fourTuples 14 at he
    rw [← align14] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block14 k).2, ?_⟩
    rw [← he]
    exact valid14 k
  · intro e he
    change e ∈ fourTuples 15 at he
    rw [← align15] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block15 k).2, ?_⟩
    rw [← he]
    exact valid15 k

/- Equality align00..align15 aligns every
 supplied witness with the tuple on which its arithmetic proposition is checked. -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem increasing_tuple_mem (e : Fin 4 → Fin 19) (he : StrictMono e) :
    e ∈ fourTuples (e 0) := by
  classical
  have hev : ![e 0,e 1,e 2,e 3] = e := by
    funext i
    fin_cases i <;> rfl
  simp only [fourTuples, List.mem_flatMap, List.mem_filter, List.mem_finRange,
    true_and, List.mem_map, decide_eq_true_eq]
  exact ⟨e 1, he (by decide +kernel), e 2, he (by decide +kernel), e 3, he (by decide +kernel), hev⟩

-- This is the only support coverage interface: actual powersetCard membership.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem local_coverage (S : Finset (Fin 19))
    (hS : S ∈ (Finset.univ : Finset (Fin 19)).powersetCard 4) :
    ∃ w, CaseValid (S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2) w := by
  classical
  let e : Fin 4 ↪o Fin 19 := S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2
  have h01 : (e 0).val < (e 1).val := e.strictMono (by decide +kernel)
  have h12 : (e 1).val < (e 2).val := e.strictMono (by decide +kernel)
  have h23 : (e 2).val < (e 3).val := e.strictMono (by decide +kernel)
  have h3 : (e 3).val < 19 := (e 3).isLt
  have h0 : (e 0).val < 16 := by omega
  exact checked_tuple ⟨(e 0).val, h0⟩ e (by
    simpa using increasing_tuple_mem e e.strictMono)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem extend4_slot (e : Fin 4 → Fin 19) (he : Function.Injective e)
    (c : Fin 4 → ℤ) (i : Fin 4) : extend4 e c (e i) = c i := by
  classical
  dsimp [extend4]
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    have hne : e k ≠ e i := fun h => hki (he h)
    simp [Pi.single_apply, hne, Ne.symm hne]
  · simp

-- Only one supplied id is used in the ray branch, never a search over 187 rays.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem classify_checked (e : Fin 4 → Fin 19) (he : Function.Injective e)
    (w : Witness) (hv : CaseValid e w) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1)
    (hn : ∀ j, 0 ≤ (ε • realCof e) j) (hne : ε • realCof e ≠ 0) :
    ∃ t : Fin 187, ∃ d : ℝ, 0 < d ∧
      ε • realCof e = d • (fun j => (zZ t j : ℝ)) := by
  classical
  have hslot (i : Fin 4) : realCof e (e i) = (cof4 e i : ℝ) := by
    dsimp [realCof]
    rw [extend4_slot e he]
  rcases w with ⟨p,n⟩ | (_ | ⟨negative,d,t⟩)
  · change 0 < cof4 e p ∧ cof4 e n < 0 at hv
    have hp : (0 : ℝ) < (cof4 e p : ℝ) := by exact_mod_cast hv.1
    have hm : (cof4 e n : ℝ) < 0 := by exact_mod_cast hv.2
    rcases hε with rfl | rfl
    · have h := hn (e n)
      change 0 ≤ (1 : ℝ) * realCof e (e n) at h
      rw [hslot] at h
      linarith
    · have h := hn (e p)
      change 0 ≤ (-1 : ℝ) * realCof e (e p) at h
      rw [hslot] at h
      linarith
  · change ∀ i, cof4 e i = 0 at hv
    exfalso
    apply hne
    funext j
    simp [realCof, extend4, hv]
  · change 0 < d ∧ ∀ j : Fin 19,
      (if negative then (-1 : ℤ) else 1) * extend4 e (cof4 e) j =
        (d : ℤ) * zZ t j at hv
    have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hv.1
    let s : ℝ := ((if negative then (-1 : ℤ) else 1) : ℤ)
    have hcast (j : Fin 19) : s * realCof e j = (d : ℝ) * (zZ t j : ℝ) := by
      dsimp [s, realCof]
      exact_mod_cast hv.2 j
    let j : Fin 19 := Fin.castAdd 3 (positiveSlot t)
    have hz : (0 : ℝ) < (zZ t j : ℝ) := by
      have h := gap_positive t
      have hzZ : 0 < zZ t j := by simpa [zZ, j] using h
      exact_mod_cast hzZ
    have hs : 0 < s * realCof e j := by
      rw [hcast]
      exact mul_pos hd hz
    have hn' : 0 ≤ ε * realCof e j := hn j
    have hforce : ε = s := by
      cases negative <;> rcases hε with rfl | rfl
      · norm_num [s]
      · norm_num [s] at hs
        linarith
      · norm_num [s] at hs
        linarith
      · norm_num [s]
    refine ⟨t, (d : ℝ), hd, ?_⟩
    funext k
    change ε * realCof e k = (d : ℝ) * (zZ t k : ℝ)
    rw [hforce]
    exact hcast k

-- The classification uses ordered supports with all three original rows.

private abbrev Support4 := {S : Finset (Fin 19) // S.card = 4}
set_option maxRecDepth 8192 in
def orderedCof : Support4 → (Fin 19 → ℝ) := fun S =>
  liftCof bR (Function.Embedding.refl (Fin 3))
    (S.val.orderEmbOfFin S.property).toEmbedding

-- Same row/column embeddings as the expected liftCof definition. The only
-- determinant rewrite is the actual pinned Matrix.det_fin_three formula.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem cofactor_cast (e : Fin 4 → Fin 19) (i : Fin 4) :
    cofactor (bR.submatrix id e) i = (cof4 e i : ℝ) := by
  classical
  fin_cases i <;>
    norm_num [cofactor, Matrix.det_fin_three, Matrix.submatrix,
      cof4, det3, bR, Fin.succAbove] <;>
    push_cast <;> ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem fullCof_cast (S : Support4) :
    orderedCof S = realCof (S.val.orderEmbOfFin S.property) := by
  classical
  let e : Fin 4 ↪o Fin 19 := S.val.orderEmbOfFin S.property
  funext j
  simp only [orderedCof, liftCof, realCof, extend4, Finset.sum_apply, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hdec : (fun a b : Fin 19 => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq (Fin 19)) := Subsingleton.elim _ _
  rw [hdec]
  change (Pi.single (e i) (cofactor (bR.submatrix id (fun k => e k)) i) : Fin 19 → ℝ) j =
    (((Pi.single (e i) (cof4 e i) : Fin 19 → ℤ) j : ℤ) : ℝ)
  by_cases hj : j = e i
  · subst j
    rw [Pi.single_eq_same, Pi.single_eq_same]
    exact cofactor_cast e i
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, Int.cast_zero]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem oriented_full_cofactor_in_catalog
    (S : Support4) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hn : ∀ j, 0 ≤ (ε • orderedCof S) j) (hne : ε • orderedCof S ≠ 0) :
    ∃ t : Fin 187, ∃ d : ℝ, 0 < d ∧
      ε • orderedCof S = d • (fun j => (zZ t j : ℝ)) := by
  classical
  have hS : S.val ∈ (Finset.univ : Finset (Fin 19)).powersetCard 4 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩
  obtain ⟨w, hw⟩ := local_coverage S.val hS
  rw [fullCof_cast] at hn hne ⊢
  exact classify_checked (S.val.orderEmbOfFin S.property)
    (S.val.orderEmbOfFin S.property).injective w hw ε hε hn hne

-- Exact original Fin16 gap equality is consumed at projection, not just cited.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem catalog_lift (t : Fin 187) :
    liftGap (fun j => (gZ t j : ℝ)) = fun j => (zZ t j : ℝ) := by
  classical
  funext j
  refine Fin.addCases (m := 16) (n := 3) (motive := fun q =>
    liftGap (fun k => (gZ t k : ℝ)) q = (zZ t q : ℝ)) ?_ ?_ j
  · intro k
    simp [liftGap, zZ]
  · intro r
    simp only [liftGap, zZ, Fin.append_right]
    rw [catalog_slack t]
    simp [aR, Matrix.mulVec, dotProduct]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem bR_mul (z : Fin 19 → ℝ) (r : Fin 3) :
    (bR *ᵥ z) r = (aR *ᵥ project z) r - z (Fin.natAdd 16 r) := by
  classical
  change (∑ j : Fin 19, bR r j * z j) = _
  rw [Fin.sum_univ_add (a := 16) (b := 3)]
  simp [bR, bZ, aR, project, Matrix.mulVec, dotProduct, ite_mul, sub_eq_add_neg]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem bR_full_span : Submodule.span ℝ (Set.range bR.col) = ⊤ := by
  classical
  rw [← Matrix.range_mulVecLin]
  apply LinearMap.range_eq_top.mpr
  intro y
  refine ⟨Fin.append (fun _ : Fin 16 => (0 : ℝ)) (fun r => -y r), ?_⟩
  change bR *ᵥ Fin.append (fun _ : Fin 16 => (0 : ℝ)) (fun r => -y r) = y
  funext r
  rw [bR_mul]
  simp [project, Matrix.mulVec, dotProduct]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem liftGap_kernel (g : Fin 16 → ℝ) :
    InKernel bR (liftGap g) ↔
      (∀ j, 0 ≤ g j) ∧ (∀ r, 0 ≤ (aR *ᵥ g) r) := by
  classical
  constructor
  · intro hz
    exact ⟨fun j => by simpa [liftGap] using hz.1 (Fin.castAdd 3 j),
      fun r => by simpa [liftGap] using hz.1 (Fin.natAdd 16 r)⟩
  · rintro ⟨hg,hAg⟩
    refine ⟨?_, ?_⟩
    · intro j
      refine Fin.addCases (m := 16) (n := 3) (motive := fun q => 0 ≤ liftGap g q) ?_ ?_ j
      · intro k
        simpa [liftGap] using hg k
      · intro r
        simpa [liftGap] using hAg r
    · intro r
      change (bR *ᵥ liftGap g) r = 0
      rw [bR_mul]
      simp [project, liftGap]

-- This equality is checked from the supplied Lean literals, at every original id.
-- In particular Fin 187's last id reduces to originalRay's sole default branch.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem originalGap_owner (t : Fin 187) :
    originalGap t = fun q => ((originalRay t).gap q : ℤ) := by
  classical
  fin_cases t <;> funext q <;> fin_cases q <;> rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem catalog_owner_alignment (t : Fin 187) :
    gZ t = fun q => ((originalRay t).gap q : ℤ) :=
  (catalog_alignment t).trans (originalGap_owner t)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem project_catalog_owner (t : Fin 187) :
    project (fun q => (zZ t q : ℝ)) =
      fun q => ((originalRay t).gap q : ℝ) := by
  classical
  rw [← catalog_lift]
  funext q
  change Fin.append (fun k => (gZ t k : ℝ)) (aR *ᵥ fun k => (gZ t k : ℝ))
    (Fin.castAdd 3 q) = ((originalRay t).gap q : ℝ)
  rw [Fin.append_left]
  exact_mod_cast congrFun (catalog_owner_alignment t) q

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem aR_eq_A : aR = A := by
  classical
  ext r q
  fin_cases r <;> fin_cases q <;> norm_num [aR, aZ, A]

end ScalarCertificate
end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
