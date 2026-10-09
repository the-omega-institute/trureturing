/- GID: D5/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound
   generality: I
   mirror-B: D5/B/S3/Quantum/FermionicCorrelationalBound/CompletedCorrelationalBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform fermionic estimates through unrenormalized cutoff limits. -/
/-
Admission witness: D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound.completed_result.
standardB_real: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.standardB_sector_support, CompletedCorrelationalBound.standardK_real.
standardK_real: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_energy.
realB_nonneg: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.realK_nonneg.
realK_nonneg: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_sector_bound.
realK_symm: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_sector_bound.
realB_column: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.realK_row.
realB_row: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.realK_row.
realK_row: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_row_le_pair_row.
doublePairs_count: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.doublePairs_sector.
doublePairs_sector: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_weighted_row_bound.
occupiedModes_removePair: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.removePair_count.
removePair_count: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.transition_particle_count.
transition_particle_count: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.standardB_sector_support.
standardB_sector_support: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finitePairOutput_lift.
mem_doublePairs: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_row_le_pair_row, CompletedCorrelationalBound.empty_not_double.
empty_not_double: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_row_le_pair_row.
actual_row_le_pair_row: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_weighted_row_bound.
actual_weighted_row_bound: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_sector_bound.
matrix_adjoint_energy: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_energy.
actual_energy: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_sector_bound.
actual_sector_bound: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countable_finite_corrected_bound.
mem_occupationSet: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.occupationSet_injective, CompletedCorrelationalBound.pairEmpty_set.
occupationSet_card: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteOccupation, CompletedCorrelationalBound.finite_pair_coordinate, CompletedCorrelationalBound.sectorOfCountable.
occupationSet_injective: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteOccupation_injective.
finiteOccupation_injective: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteEmbed, CompletedCorrelationalBound.finiteEmbed_apply, CompletedCorrelationalBound.finiteEmbed_norm, CompletedCorrelationalBound.finiteEmbed_outside.
finiteEmbed_norm: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countable_finite_corrected_bound.
countableCut_apply: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countableCut_tendsto, CompletedCorrelationalBound.finiteEmbed_restrict.
modesBelow_eventually: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countableCut_tendsto.
countableCut_tendsto: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteEmbedding_dense.
occupationSet_ofSet: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteOccupation_sectorOfCountable, CompletedCorrelationalBound.sectorOfCountable.
finiteOccupation_sectorOfCountable: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteEmbed_restrict, CompletedCorrelationalBound.finite_pair_sum_transport.
finiteOccupation_below: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteEmbed_outside, CompletedCorrelationalBound.finiteEmbed_restrict.
finiteEmbed_apply: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteEmbed_restrict, CompletedCorrelationalBound.finite_pair_coordinate, CompletedCorrelationalBound.finite_pair_sum_transport.
finiteEmbed_outside: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteEmbed_restrict, CompletedCorrelationalBound.finite_pair_outside, CompletedCorrelationalBound.finite_pair_sum_transport.
finiteEmbed_restrict: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteEmbedding_dense.
finiteEmbedding_dense: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countable_finite_corrected_bound.
occupiedModes_addPair: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.occupationSet_addPair.
occupationSet_addPair: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finite_pair_coordinate.
pairEmpty_set: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finite_pair_coordinate.
pair_matrix_row: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finite_pair_coordinate.
finite_pair_coordinate: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finite_pair_sum_transport.
countableBLCLM_apply: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countable_finite_corrected_bound.
lift_norm: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countable_finite_corrected_bound, CompletedCorrelationalBound.finitePairOutput_norm.
finitePairOutput_lift: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finitePairOutput_norm.
finitePairOutput_norm: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countable_finite_corrected_bound.
finite_pair_outside: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finite_pair_sum_transport.
finite_pair_sum_transport: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countable_finite_corrected_bound.
countable_finite_corrected_bound: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.coordinate_result.
assembly_of_countable_finite_bounds: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CompletedCorrelationalBound.coordinate_result.
coordinate_result: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CompletedCorrelationalBound.completed_result.
completed_result: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: SourceCorrelationalBound.source_cap_result.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount, statement_id: sha256:97804cfc85a668f345a5b3e2421ba02e5e6203f36590508faccac8726341bc0a.
  D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator, statement_id: sha256:d0e241c65c207456599a205d965adefde23f6764456a0c5a832a08a676fadfb3.
  D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC, statement_id: sha256:e5eb14acc0a2901b62190a83ed2543f27309f7f32708edd35fa0376362ebfe97.
Information-escape registration is paused.
-/
import D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding
noncomputable section
open scoped Classical BigOperators TensorProduct ComplexConjugate Matrix
namespace D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound
open D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
section
open scoped BigOperators Matrix Classical
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
def realB {L s : ℕ} (coeff : Fin L → ℝ) (x y : ((Fin (2*L+s) → Bool))) : ℝ :=
  ∑ i, if pairTransition i x y then coeff i else 0
def realK {L s : ℕ} (coeff : Fin L → ℝ) (x y : ((Fin (2*L+s) → Bool))) : ℝ :=
  dotProduct (fun z => realB coeff z x) (fun z => realB coeff z y)
private theorem standardB_real {L s : ℕ} (coeff : Fin L → ℝ) (x y : ((Fin (2*L+s) → Bool))) :
    standardB coeff x y = (realB coeff x y : ℂ) := by
  simp only [standardB,realB,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    pair_entry_transition,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp
theorem standardK_real {L s : ℕ} (coeff : Fin L → ℝ) (x y : ((Fin (2*L+s) → Bool))) :
    (((standardB (s := s) coeff)ᴴ * standardB coeff) :
      Matrix (((Fin (2*L+s) → Bool))) (((Fin (2*L+s) → Bool))) ℂ) x y = (realK coeff x y : ℂ) := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,standardB_real,Complex.star_def,
    Complex.conj_ofReal,realK,dotProduct,Complex.ofReal_sum,Complex.ofReal_mul]
private theorem realB_nonneg {L s : ℕ} (coeff : Fin L → ℝ) (hc : ∀ i, 0 ≤ coeff i)
    (x y : ((Fin (2*L+s) → Bool))) : 0 ≤ realB coeff x y := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hc i
  · exact le_refl _
theorem realK_nonneg {L s : ℕ} (coeff : Fin L → ℝ) (hc : ∀ i, 0 ≤ coeff i)
    (x y : ((Fin (2*L+s) → Bool))) : 0 ≤ realK coeff x y :=
  Finset.sum_nonneg fun z _ => mul_nonneg (realB_nonneg coeff hc z x)
    (realB_nonneg coeff hc z y)
theorem realK_symm {L s : ℕ} (coeff : Fin L → ℝ) (x y : ((Fin (2*L+s) → Bool))) :
    realK coeff x y = realK coeff y x := by
  simp only [realK,dotProduct,mul_comm]
private theorem realB_column {L s : ℕ} (coeff : Fin L → ℝ)
    (f : ((Fin (2*L+s) → Bool)) → ℝ) (y : ((Fin (2*L+s) → Bool))) :
    (∑ x : ((Fin (2*L+s) → Bool)), realB coeff x y * f x) =
      ∑ i, if pairFull i y then coeff i * f (removePair i y) else 0 := by
  simp only [realB,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [transition_remove]
  by_cases h : pairFull i y
  · simp [h,ite_mul]
  · simp [h]
private theorem realB_row {L s : ℕ} (coeff : Fin L → ℝ)
    (f : ((Fin (2*L+s) → Bool)) → ℝ) (x : ((Fin (2*L+s) → Bool))) :
    (∑ y : ((Fin (2*L+s) → Bool)), realB coeff x y * f y) =
      ∑ i, if pairEmpty i x then coeff i * f (addPair i x) else 0 := by
  simp only [realB,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [transition_add]
  by_cases h : pairEmpty i x
  · simp [h,ite_mul]
  · simp [h]
/-- Exact weighted-row formula of the actual Jordan-Wigner Gram matrix. -/
theorem realK_row {L s : ℕ} (coeff : Fin L → ℝ)
    (f : ((Fin (2*L+s) → Bool)) → ℝ) (x : ((Fin (2*L+s) → Bool))) :
    (∑ y : ((Fin (2*L+s) → Bool)), realK coeff x y * f y) =
      ∑ i, if pairFull i x then coeff i *
        (∑ j, if pairEmpty j (removePair i x) then
          coeff j * f (addPair j (removePair i x)) else 0) else 0 := by
  simp only [realK,dotProduct,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc,← Finset.mul_sum,realB_row]
  exact realB_column coeff _ x
end
section
open scoped BigOperators Classical
def occupiedModes {d : ℕ} (x : ((Fin d → Bool))) : Finset (Fin d) :=
  Finset.univ.filter (fun i => x i=true)
/-- Every occupied complete pair uses two disjoint occupied modes. -/
private theorem doublePairs_count {L s : ℕ} (x : ((Fin (2*L+s) → Bool))) :
    2*(doublePairs x).card ≤ occupationCount x := by
  classical
  let U := (doublePairs x).image (upMode (s := s))
  let V := (doublePairs x).image (downMode (s := s))
  have hU : U ⊆ occupiedModes x := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    have h := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1⟩
  have hV : V ⊆ occupiedModes x := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    have h := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2⟩
  have hUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro k hkU hkV
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hkU
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hkV
    exact up_down_ne i j (hi.trans hj.symm)
  have hcu : U.card = (doublePairs x).card := Finset.card_image_of_injective _ upMode_injective
  have hcv : V.card = (doublePairs x).card := Finset.card_image_of_injective _ downMode_injective
  have h := Finset.card_le_card (Finset.union_subset hU hV)
  rw [Finset.card_union_of_disjoint hUV,hcu,hcv] at h
  have hcount : occupationCount x = (occupiedModes x).card := by
    unfold occupationCount occupiedModes
    have ht (i : Fin (2*L+s)) : (x i).toNat = if x i = true then 1 else 0 := by cases x i <;> rfl
    simp_rw [ht]
    simp
  rw [hcount]
  omega
theorem doublePairs_sector {L s m : ℕ} (x : ({s : Fin (2*L+s) → Bool // occupationCount s = (2*m)})) :
    (doublePairs x.val).card ≤ m := by
  have h := doublePairs_count x.val
  rw [x.property] at h
  omega
end
section
open scoped BigOperators Classical Matrix
private theorem occupiedModes_removePair {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool))) :
    occupiedModes (removePair i x) = ((occupiedModes x).erase (upMode i)).erase (downMode i) := by
  ext k
  simp only [occupiedModes,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
  by_cases hu : k=upMode i
  · subst k; simp [removePair,up_down_ne]
  · by_cases hd : k=downMode i
    · subst k; simp [removePair,(up_down_ne i i).symm]
    · simp [removePair,Function.update_of_ne,hu,hd]
private theorem removePair_count {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool)))
    (h : pairFull i x) : occupationCount (removePair i x)=occupationCount x-2 := by
  have hu : upMode i ∈ occupiedModes x := by simp [occupiedModes,h.1]
  have hd : downMode i ∈ (occupiedModes x).erase (upMode i) := by
    simp [occupiedModes,(up_down_ne i i).symm,h.2]
  have hcount (y : Fin (2*L+s) → Bool) : occupationCount y = (occupiedModes y).card := by
    unfold occupationCount occupiedModes
    have ht (k : Fin (2*L+s)) : (y k).toNat = if y k = true then 1 else 0 := by cases y k <;> rfl
    simp_rw [ht]
    simp
  rw [hcount, hcount]
  rw [occupiedModes_removePair,Finset.card_erase_of_mem hd,Finset.card_erase_of_mem hu]
  omega
private theorem transition_particle_count {L s : ℕ} (i : Fin L) (x y : ((Fin (2*L+s) → Bool)))
    (h : pairTransition i x y) : occupationCount x=occupationCount y-2 := by
  have hr := (transition_remove i x y).mp h
  rw [hr.2]
  exact removePair_count i y hr.1
/-- An actual finite pair sum sends the N-sector into the (N-2)-sector. -/
theorem standardB_sector_support {L s N : ℕ} (coeff : Fin L → ℝ) (ψ : (EuclideanSpace ℂ ({s : Fin (2*L+s) → Bool // occupationCount s = N})))
    (x : ((Fin (2*L+s) → Bool))) (hx : occupationCount x ≠ N-2) :
    (Matrix.toEuclideanLin (standardB coeff)) (lift ψ) x=0 := by
  simp only [Matrix.toEuclideanLin_apply,WithLp.ofLp_toLp,Matrix.mulVec,dotProduct,standardB_real]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : occupationCount y=N
  · have hB : realB coeff x y=0 := by
      unfold realB
      apply Finset.sum_eq_zero
      intro i _
      have hi : ¬pairTransition i x y := by
        intro hp
        exact hx (hy ▸ transition_particle_count i x y hp)
      simp [hi]
    simp [hB]
  · simp [lift,hy]
end
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
section
open scoped BigOperators Matrix Classical
private theorem mem_doublePairs {L s : ℕ} (x : ((Fin (2*L+s) → Bool))) (i : Fin L) :
    i ∈ doublePairs x ↔ pairFull i x := by
  simp only [doublePairs,Finset.mem_filter,Finset.mem_univ,true_and,pairFull]
private theorem empty_not_double {L s : ℕ} (x : ((Fin (2*L+s) → Bool))) (i : Fin L)
    (h : pairEmpty i x) : i ∉ doublePairs x := by
  intro hi
  have hf := (mem_doublePairs x i).mp hi
  have he : (false:Bool)=true := h.1.symm.trans hf.1
  cases he
/-- Blocked singly occupied pairs can only decrease an actual weighted row. -/
private theorem actual_row_le_pair_row {L s : ℕ} (coeff : Fin L → ℝ) (hc : ∀ i, 0 ≤ coeff i)
    (a : ℝ) (ha : 0 ≤ a) (x : ((Fin (2*L+s) → Bool))) :
    (∑ y : ((Fin (2*L+s) → Bool)), realK coeff x y *
      comparisonVector a (fun i => coeff i^2) (doublePairs y)) ≤
      ∑ E : Finset (Fin L), pairKernel (fun i => coeff i^2) (doublePairs x) E *
        comparisonVector a (fun i => coeff i^2) E := by
  let p : Fin L → ℝ := fun i => coeff i^2
  let f := comparisonVector a p
  have hf (D : Finset (Fin L)) : 0 < f D :=
    comparisonVector_pos a p ha (fun i => sq_nonneg _) D
  have hs (i : Fin L) : Real.sqrt (coeff i^2)=coeff i := Real.sqrt_sq (hc i)
  rw [realK_row,pairKernel_row]
  simp_rw [doublePairs_add,doublePairs_remove]
  rw [← Fintype.sum_ite_mem (doublePairs x)]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : pairFull i x
  · have him := (mem_doublePairs x i).mpr hi
    simp only [if_pos hi,if_pos him,hs]
    apply mul_le_mul_of_nonneg_left _ (hc i)
    have hcomp : ((doublePairs x).erase i)ᶜ =
        Finset.univ.filter (fun j => j ∉ (doublePairs x).erase i) := by
      apply Finset.ext; intro j; simp; tauto
    rw [hcomp,Finset.sum_filter]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : pairEmpty j (removePair i x)
    · have hjn : j ∉ (doublePairs x).erase i := by
        rw [← doublePairs_remove]
        exact empty_not_double _ j hj
      simp only [if_pos hj,if_pos hjn,hs]
      exact le_refl _
    · rw [if_neg hj]
      split_ifs
      · exact le_refl _
      · exact mul_nonneg (hc j) (le_of_lt (hf _))
  · have hin : i ∉ doublePairs x := fun h => hi ((mem_doublePairs x i).mp h)
    simp only [if_neg hi,if_neg hin]
    exact le_refl _
private theorem actual_weighted_row_bound {L s : ℕ} (coeff : Fin L → ℝ)
    (hc : ∀ i, 0 ≤ coeff i) (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 ≤ α)
    (hpa : ∀ i, coeff i^2 ≤ α) (hsum : (∑ i, coeff i^2) ≤ 1)
    (hsmall : 2*(m : ℝ)*α ≤ 1) (x : ({s : Fin (2*L+s) → Bool // occupationCount s = (2*m)})) :
    (∑ y : ((Fin (2*L+s) → Bool)), realK coeff x.val y *
      comparisonVector ((m:ℝ)-1) (fun i => coeff i^2) (doublePairs y)) /
        comparisonVector ((m:ℝ)-1) (fun i => coeff i^2) (doublePairs x.val) ≤
      (m:ℝ)-(m:ℝ)*((m:ℝ)-1)*(∑ i, coeff i^4)+(5/2)*(m:ℝ)^3*α^2 := by
  have ha : 0 ≤ (m:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hm)
  have hf := comparisonVector_pos ((m:ℝ)-1) (fun i => coeff i^2) ha
    (fun i => sq_nonneg _) (doublePairs x.val)
  calc
    _ ≤ _ := div_le_div_of_nonneg_right
      (actual_row_le_pair_row coeff hc ((m:ℝ)-1) ha x.val) (le_of_lt hf)
    _ ≤ _ := by
      convert pairKernel_row_bound (fun i => coeff i^2) m hm α hα (fun i => sq_nonneg _)
        hpa hsum hsmall (doublePairs x.val) (doublePairs_sector x) using 1
      congr 3
      apply Finset.sum_congr rfl
      intro i _
      ring
end
section
open scoped BigOperators Matrix ComplexConjugate
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
/-- A matrix adjoint product has the usual energy interpretation. -/
private theorem matrix_adjoint_energy {d : ℕ} (B : FullOperator d) (Ψ : (EuclideanSpace ℂ (Fin d → Bool))) :
    (inner ℂ Ψ ((Matrix.toEuclideanLin (Bᴴ * B)) Ψ)).re =
      ‖(Matrix.toEuclideanLin B) Ψ‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  congr 1
  have hmul : (Matrix.toEuclideanLin (Bᴴ * B)) Ψ =
      (Matrix.toEuclideanLin Bᴴ) ((Matrix.toEuclideanLin B) Ψ) := by
    simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]
  rw [hmul]
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _
end
section
open scoped BigOperators Matrix Classical
private theorem actual_energy {L s : ℕ} (coeff : Fin L → ℝ) (Ψ : (EuclideanSpace ℂ (Fin (2*L+s) → Bool))) :
    ‖(Matrix.toEuclideanLin (standardB coeff)) Ψ‖^2 =
      (∑ x : ((Fin (2*L+s) → Bool)), ∑ y : ((Fin (2*L+s) → Bool)),
        (realK coeff x y : ℂ) * star (Ψ x) * Ψ y).re := by
  rw [← matrix_adjoint_energy]
  apply congrArg Complex.re
  simp only [EuclideanSpace.inner_eq_star_dotProduct,Matrix.toEuclideanLin_apply,
    WithLp.ofLp_toLp,Matrix.mulVec,dotProduct,Pi.star_apply,Finset.mul_sum,Finset.sum_mul,standardK_real]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring
/-- The finite B*B estimate on the actual fermionic N-sector, including spectators. -/
theorem actual_sector_bound {L s : ℕ} (coeff : Fin L → ℝ)
    (hc : ∀ i, 0 ≤ coeff i) (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 ≤ α)
    (hpa : ∀ i, coeff i^2 ≤ α) (hsum : (∑ i, coeff i^2) ≤ 1)
    (hsmall : 2*(m : ℝ)*α ≤ 1) (ψ : (EuclideanSpace ℂ ({s : Fin (2*L+s) → Bool // occupationCount s = (2*m)}))) :
    ‖(Matrix.toEuclideanLin (standardB coeff)) (lift ψ)‖^2 ≤
      ((m:ℝ)-(m:ℝ)*((m:ℝ)-1)*(∑ i, coeff i^4)+(5/2)*(m:ℝ)^3*α^2) * ‖lift ψ‖^2 := by
  let a : ℝ := (m:ℝ)-1
  let f (x : ((Fin (2*L+s) → Bool))) := comparisonVector a (fun i => coeff i^2) (doublePairs x)
  let C := (m:ℝ)-(m:ℝ)*((m:ℝ)-1)*(∑ i, coeff i^4)+(5/2)*(m:ℝ)^3*α^2
  have ha : 0 ≤ a := sub_nonneg.mpr (by exact_mod_cast hm)
  have hf (x) : 0 < f x := comparisonVector_pos a _ ha (fun i => sq_nonneg _) _
  rw [actual_energy]
  calc
    _ ≤ _ := weighted_schur (realK coeff) (realK_nonneg coeff hc) (realK_symm coeff) f hf (lift ψ)
    _ ≤ ∑ x : ((Fin (2*L+s) → Bool)), ‖lift ψ x‖^2 * C := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : occupationCount x=2*m
      · exact mul_le_mul_of_nonneg_left
          (actual_weighted_row_bound coeff hc m hm α hα hpa hsum hsmall ⟨x,hx⟩) (sq_nonneg _)
      · have hz : lift ψ x=0 := by simp [lift,hx]
        simp [hz]
    _ = C*‖lift ψ‖^2 := by
      rw [← Finset.sum_mul,PiLp.norm_sq_eq_of_L2]
      ring
end
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding
section
open scoped BigOperators Classical
def occupationSet {d : ℕ} (x : ((Fin d → Bool))) : Finset ℕ :=
  (occupiedModes x).map ⟨Fin.val,Fin.val_injective⟩
private theorem mem_occupationSet {d : ℕ} (x : ((Fin d → Bool))) (i : Fin d) :
    i.val ∈ occupationSet x ↔ x i=true := by
  simp only [occupationSet,occupiedModes,Finset.mem_map,Function.Embedding.coeFn_mk,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,hji⟩
    have he : j=i := Fin.ext hji
    simpa [he] using hj
  · intro hi
    exact ⟨i,hi,rfl⟩
private theorem occupationSet_card {d : ℕ} (x : ((Fin d → Bool))) :
    (occupationSet x).card=occupationCount x := by
  unfold occupationCount
  have ht (i : Fin d) : (x i).toNat = if x i = true then 1 else 0 := by cases x i <;> rfl
  simp_rw [ht]
  simp [occupationSet,occupiedModes]
private theorem occupationSet_injective (d : ℕ) : Function.Injective (@occupationSet d) := by
  intro x y h
  funext i
  have he : x i=true ↔ y i=true := by
    rw [← mem_occupationSet x i,← mem_occupationSet y i,h]
  cases hx : x i <;> cases hy : y i <;> simp_all
def finiteOccupation {d N : ℕ} (x : ({s : Fin d → Bool // occupationCount s = N})) : ({s : Finset ℕ // s.card = N}) :=
  ⟨occupationSet x.val,(occupationSet_card x.val).trans x.property⟩
private theorem finiteOccupation_injective (d N : ℕ) : Function.Injective (@finiteOccupation d N) := by
  intro x y h
  apply Subtype.ext
  exact occupationSet_injective d (congrArg Subtype.val h)
def finiteEmbed {d N : ℕ} (ψ : EuclideanSpace ℂ {s : Fin d → Bool // occupationCount s = N}) :
    lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2 :=
  coordinateRename ⟨finiteOccupation,finiteOccupation_injective d N⟩
    ((lpPiLpₗᵢ (fun _ : {s : Fin d → Bool // occupationCount s = N} => ℂ) ℂ).symm ψ)
theorem finiteEmbed_norm {d N : ℕ}
    (ψ : EuclideanSpace ℂ {s : Fin d → Bool // occupationCount s = N}) :
    ‖finiteEmbed ψ‖=‖ψ‖ := by
  rw [finiteEmbed,LinearIsometry.norm_map,LinearIsometryEquiv.norm_map]
def finiteRestrict {d N : ℕ} (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) : (EuclideanSpace ℂ ({s : Fin d → Bool // occupationCount s = N})) :=
  WithLp.toLp 2 (fun x => ψ (finiteOccupation x))
set_option backward.isDefEq.respectTransparency false in
end
section
open scoped BigOperators Classical Topology ENNReal
open Filter
def modesBelow (d : ℕ) (S : ({s : Finset ℕ // s.card = N})) : Prop := ∀ n ∈ S.val,n<d
private def countableCut (d N : ℕ) : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2) →L[ℂ] (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2) :=
  partialPullCLM (modesBelow d) Subtype.val Subtype.val_injective (fun _ => 1)
    (fun _ => by simp)
private theorem countableCut_apply (d N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (S : ({s : Finset ℕ // s.card = N})) :
    countableCut d N ψ S = if modesBelow d S then ψ S else 0 := by
  change partialPullRaw (modesBelow d) Subtype.val (fun _ => 1) ψ S = _
  unfold partialPullRaw
  split_ifs <;> simp
private theorem modesBelow_eventually (N : ℕ) (S : ({s : Finset ℕ // s.card = N})) :
    ∀ᶠ d : ℕ in atTop,modesBelow d S := by
  filter_upwards [eventually_ge_atTop (S.val.sup id+1)] with d hd
  intro n hn
  have h := Finset.le_sup (f := id) hn
  change n ≤ S.val.sup id at h
  omega
/-- Finite mode cutoffs converge in the completed exterior norm. -/
private theorem countableCut_tendsto (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    Tendsto (fun d : ℕ => countableCut d N ψ) atTop (𝓝 ψ) := by
  let f (d : ℕ) (S : ({s : Finset ℕ // s.card = N})) := ‖(countableCut d N ψ-ψ) S‖^2
  have hs : Summable (fun S : ({s : Finset ℕ // s.card = N}) => ‖ψ S‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp ψ).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)
  have hpt (S : ({s : Finset ℕ // s.card = N})) : Tendsto (fun d : ℕ => f d S) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [modesBelow_eventually N S] with d hd
    simp [f,lp.coeFn_sub,countableCut_apply,hd]
  have hdom : ∀ᶠ d : ℕ in atTop,∀ S,‖f d S‖ ≤ ‖ψ S‖^2 := by
    apply Filter.Eventually.of_forall
    intro d S
    by_cases hd : modesBelow d S
    · simp [f,lp.coeFn_sub,countableCut_apply,hd]
    · simp [f,lp.coeFn_sub,countableCut_apply,hd]
  have ht := tendsto_tsum_of_dominated_convergence hs hpt hdom
  have hn : Tendsto (fun d : ℕ => ‖countableCut d N ψ-ψ‖^2) atTop (𝓝 0) := by
    simpa only [f,← Real.rpow_two,← ENNReal.toReal_ofNat,
      ← lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal),tsum_zero] using ht
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  have hz : Tendsto (fun d : ℕ => ‖countableCut d N ψ-ψ‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hr
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hz
end
section
open scoped BigOperators Classical Topology
open Filter
def occupationOfSet (d : ℕ) (S : Finset ℕ) : ((Fin d → Bool)) := fun i => decide (i.val ∈ S)
private theorem occupationSet_ofSet (d : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S,n<d) :
    occupationSet (occupationOfSet d S)=S := by
  ext n
  constructor
  · intro hn
    obtain ⟨i,hi,hval⟩ := Finset.mem_map.mp hn
    have hh := (Finset.mem_filter.mp hi).2
    change decide (i.val∈S)=true at hh
    have hm := of_decide_eq_true hh
    simpa only [Function.Embedding.coeFn_mk] using hval ▸ hm
  · intro hn
    let i : Fin d := ⟨n,hS n hn⟩
    exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      simp [occupationOfSet,i,hn]⟩,rfl⟩
def sectorOfCountable (d N : ℕ) (S : ({s : Finset ℕ // s.card = N})) (hS : modesBelow d S) : ({s : Fin d → Bool // occupationCount s = N}) :=
  ⟨occupationOfSet d S.val,by
    rw [← occupationSet_card,occupationSet_ofSet d S.val hS]
    exact S.property⟩
theorem finiteOccupation_sectorOfCountable (d N : ℕ) (S : ({s : Finset ℕ // s.card = N})) (hS : modesBelow d S) :
    finiteOccupation (sectorOfCountable d N S hS)=S := by
  apply Subtype.ext
  exact occupationSet_ofSet d S.val hS
private theorem finiteOccupation_below {d N : ℕ} (x : ({s : Fin d → Bool // occupationCount s = N})) : modesBelow d (finiteOccupation x) := by
  intro n hn
  obtain ⟨i,_,hval⟩ := Finset.mem_map.mp hn
  simpa only [Function.Embedding.coeFn_mk] using hval ▸ i.isLt
theorem finiteEmbed_apply {d N : ℕ} (ψ : (EuclideanSpace ℂ ({s : Fin d → Bool // occupationCount s = N}))) (x : ({s : Fin d → Bool // occupationCount s = N})) :
    finiteEmbed ψ (finiteOccupation x)=ψ x := by
  exact coordinateRename_image ⟨finiteOccupation,finiteOccupation_injective d N⟩
    ((lpPiLpₗᵢ (fun _ : {s : Fin d → Bool // occupationCount s = N} => ℂ) ℂ).symm ψ) x
theorem finiteEmbed_outside {d N : ℕ} (ψ : (EuclideanSpace ℂ ({s : Fin d → Bool // occupationCount s = N}))) (S : ({s : Finset ℕ // s.card = N}))
    (hS : ¬modesBelow d S) : finiteEmbed ψ S=0 := by
  apply coordinateRename_outside
  rintro ⟨x,hx⟩
  exact hS (hx ▸ finiteOccupation_below x)
/-- The concrete finite mode embedding is precisely the canonical lp cutoff. -/
private theorem finiteEmbed_restrict (d N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    finiteEmbed (finiteRestrict (d := d) ψ) = countableCut d N ψ := by
  ext S
  by_cases hS : modesBelow d S
  · let x := sectorOfCountable d N S hS
    have hx : finiteOccupation x=S := finiteOccupation_sectorOfCountable d N S hS
    rw [← hx,finiteEmbed_apply,countableCut_apply,if_pos (finiteOccupation_below x)]
    rfl
  · rw [finiteEmbed_outside _ S hS,countableCut_apply,if_neg hS]
/-- Every countable sector vector is a norm limit of actual finite occupation vectors. -/
theorem finiteEmbedding_dense (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    Tendsto (fun d : ℕ => finiteEmbed (finiteRestrict (d := d) ψ)) atTop (𝓝 ψ) := by
  simpa only [finiteEmbed_restrict] using countableCut_tendsto N ψ
end
section
open scoped BigOperators Classical Matrix
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
private theorem occupiedModes_addPair {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool))) :
    occupiedModes (addPair i x)=insert (upMode i) (insert (downMode i) (occupiedModes x)) := by
  ext k
  simp only [occupiedModes,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  by_cases hu : k=upMode i
  · subst k; simp [addPair,up_down_ne]
  · by_cases hd : k=downMode i
    · subst k; simp [addPair,(up_down_ne i i).symm]
    · simp [addPair,Function.update_of_ne,hu,hd]
private theorem occupationSet_addPair {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool))) :
    occupationSet (addPair i x)=insert (2*i.val) (insert (2*i.val+1) (occupationSet x)) := by
  change (occupiedModes (addPair i x)).map ⟨Fin.val,Fin.val_injective⟩ = _
  rw [occupiedModes_addPair,Finset.map_insert,Finset.map_insert]
  rfl
private theorem pairEmpty_set {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool))) :
    pairEmpty i x ↔ 2*i.val ∉ occupationSet x ∧ 2*i.val+1 ∉ occupationSet x := by
  change (x (upMode i)=false ∧ x (downMode i)=false) ↔ _
  have hu := mem_occupationSet x (upMode (s := s) i)
  have hd := mem_occupationSet x (downMode (s := s) i)
  change (2*i.val ∈ occupationSet x ↔ x (upMode i)=true) at hu
  change (2*i.val+1 ∈ occupationSet x ↔ x (downMode i)=true) at hd
  rw [hu,hd]
  cases x (upMode i) <;> cases x (downMode i) <;> simp
private theorem pair_matrix_row {L s : ℕ} (i : Fin L) (Ψ : (EuclideanSpace ℂ (Fin (2*L+s) → Bool))) (x : ((Fin (2*L+s) → Bool))) :
    (Matrix.toEuclideanLin (fullC (downMode i)*fullC (upMode i))) Ψ x =
      if pairEmpty i x then Ψ (addPair i x) else 0 := by
  simp only [Matrix.toEuclideanLin_apply,WithLp.ofLp_toLp,Matrix.mulVec,dotProduct,
    pair_entry_transition,transition_add]
  by_cases he : pairEmpty i x
  · simp [he]
  · simp [he]
/-- Finite Jordan--Wigner contractions match the literal countable ordered-wedge coordinates. -/
theorem finite_pair_coordinate {L s N : ℕ} (i : Fin L) (ψ : (EuclideanSpace ℂ ({s : Fin (2*L+s) → Bool // occupationCount s = N})))
    (x : ({s : Fin (2*L+s) → Bool // occupationCount s = (N-2)})) :
    pairCoordinate (finiteEmbed ψ) (2*i.val) (2*i.val+1) (finiteOccupation x).val =
      (Matrix.toEuclideanLin (fullC (downMode i)*fullC (upMode i))) (lift ψ) x.val := by
  rw [pair_matrix_row]
  by_cases he : pairEmpty i x.val
  · have hset := (pairEmpty_set i x.val).mp he
    by_cases hn : occupationCount (addPair i x.val)=N
    · have hcard : (insert (2*i.val) (insert (2*i.val+1) (finiteOccupation x).val)).card=N := by
        change (insert (2*i.val) (insert (2*i.val+1) (occupationSet x.val))).card = N
        rw [← occupationSet_addPair,occupationSet_card]
        exact hn
      rw [countable_pair_sign (finiteEmbed ψ) i.val (finiteOccupation x).val hset.1 hset.2 hcard,
        if_pos he]
      let y : ({s : Fin (2*L+s) → Bool // occupationCount s = N}) := ⟨addPair i x.val,hn⟩
      have hy : (⟨insert (2*i.val) (insert (2*i.val+1) (finiteOccupation x).val),hcard⟩ : ({s : Finset ℕ // s.card = N}))=
          finiteOccupation y := by
        apply Subtype.ext
        exact (occupationSet_addPair i x.val).symm
      rw [hy,finiteEmbed_apply]
      simp [lift,hn,y]
    · have hcard : (insert (2*i.val) (insert (2*i.val+1) (finiteOccupation x).val)).card ≠ N := by
        change (insert (2*i.val) (insert (2*i.val+1) (occupationSet x.val))).card ≠ N
        rw [← occupationSet_addPair,occupationSet_card]
        exact hn
      have hp : ¬(2*i.val ≠ 2*i.val+1 ∧ 2*i.val ∉ (finiteOccupation x).val ∧
          2*i.val+1 ∉ (finiteOccupation x).val ∧
          (insert (2*i.val) (insert (2*i.val+1) (finiteOccupation x).val)).card=N) :=
        fun h => hcard h.2.2.2
      simp only [pairCoordinate,dif_neg hp,if_pos he,lift,dif_neg hn]
  · have hset : ¬(2*i.val ∉ (finiteOccupation x).val ∧ 2*i.val+1 ∉ (finiteOccupation x).val) :=
      fun h => he ((pairEmpty_set i x.val).mpr h)
    have hp : ¬(2*i.val ≠ 2*i.val+1 ∧ 2*i.val ∉ (finiteOccupation x).val ∧
        2*i.val+1 ∉ (finiteOccupation x).val ∧
        (insert (2*i.val) (insert (2*i.val+1) (finiteOccupation x).val)).card=N) :=
      fun h => hset ⟨h.2.1,h.2.2.1⟩
    simp only [pairCoordinate,dif_neg hp,if_neg he]
end
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
section
open scoped BigOperators Classical Topology
open Filter
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
def countableBLinear (coeff : ℕ → ℝ) (hq : Summable fun i => coeff i^2) (m : ℕ) :
    (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2) →ₗ[ℂ] (lp (fun _ : {s : Finset ℕ // s.card = (2*m-2)} => ℂ) 2) where
  toFun := countableB coeff m
  map_add' ψ χ := by
    simp only [countableB,map_add,smul_add]
    exact (pairSeries_summable coeff hq m ψ).tsum_add (pairSeries_summable coeff hq m χ)
  map_smul' a ψ := by
    simp only [countableB,map_smul]
    simp_rw [smul_comm (coeff _ : ℂ) a]
    exact (pairSeries_summable coeff hq m ψ).tsum_const_smul a
private def countableBLCLM (coeff : ℕ → ℝ) (m L : ℕ) :
    (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2) →L[ℂ] (lp (fun _ : {s : Finset ℕ // s.card = (2*m-2)} => ℂ) 2) :=
  ∑ i ∈ Finset.range L,(coeff i:ℂ) • pairContract (2*m) (2*i) (2*i+1)
private theorem countableBLCLM_apply (coeff : ℕ → ℝ) (m L : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) :
    countableBLCLM coeff m L ψ=countableBL coeff m L ψ := by
  simp only [countableBLCLM,countableBL,sum_apply,ContinuousLinearMap.smul_apply]
end
section
open scoped BigOperators Classical
private theorem lift_norm {d N : ℕ} (ψ : (EuclideanSpace ℂ ({s : Fin d → Bool // occupationCount s = N}))) : ‖lift ψ‖=‖ψ‖ := by
  have he := Fintype.sum_of_injective (Subtype.val : ({s : Fin d → Bool // occupationCount s = N}) → ((Fin d → Bool)))
    Subtype.val_injective (fun s : ({s : Fin d → Bool // occupationCount s = N}) => ‖ψ s‖^2)
    (fun x : ((Fin d → Bool)) => ‖lift ψ x‖^2) ?_ ?_
  · rw [← PiLp.norm_sq_eq_of_L2 (fun _ : ({s : Fin d → Bool // occupationCount s = N}) => ℂ) ψ,
      ← PiLp.norm_sq_eq_of_L2 (fun _ : ((Fin d → Bool)) => ℂ) (lift ψ)] at he
    nlinarith [norm_nonneg (lift ψ),norm_nonneg ψ]
  · intro x hx
    have hn : occupationCount x ≠ N := by
      intro h
      exact hx ⟨⟨x,h⟩,rfl⟩
    simp [lift,hn]
  · intro s
    simp [lift,s.property]
end
section
open scoped BigOperators Classical Topology Matrix
open Filter
private def finitePairOutput {L s N : ℕ} (coeff : Fin L → ℝ) (ψ : (EuclideanSpace ℂ ({s : Fin (2*L+s) → Bool // occupationCount s = N}))) :
    (EuclideanSpace ℂ ({s : Fin (2*L+s) → Bool // occupationCount s = (N-2)})) :=
  WithLp.toLp 2 (fun x => (Matrix.toEuclideanLin (standardB coeff)) (lift ψ) x.val)
private theorem finitePairOutput_lift {L s N : ℕ} (coeff : Fin L → ℝ) (ψ : (EuclideanSpace ℂ ({s : Fin (2*L+s) → Bool // occupationCount s = N}))) :
    lift (finitePairOutput coeff ψ) = (Matrix.toEuclideanLin (standardB coeff)) (lift ψ) := by
  ext x
  by_cases hx : occupationCount x=N-2
  · simp only [lift,dif_pos hx,finitePairOutput,WithLp.ofLp_toLp]
  · simp only [lift,dif_neg hx]
    exact (standardB_sector_support coeff ψ x hx).symm
private theorem finitePairOutput_norm {L s N : ℕ} (coeff : Fin L → ℝ) (ψ : (EuclideanSpace ℂ ({s : Fin (2*L+s) → Bool // occupationCount s = N}))) :
    ‖finitePairOutput coeff ψ‖=‖(Matrix.toEuclideanLin (standardB coeff)) (lift ψ)‖ := by
  rw [← finitePairOutput_lift,lift_norm]
private theorem finite_pair_outside {L s N : ℕ} (i : Fin L) (ψ : (EuclideanSpace ℂ ({s : Fin (2*L+s) → Bool // occupationCount s = N})))
    (R : ({s : Finset ℕ // s.card = (N-2)})) (hR : ¬modesBelow (2*L+s) R) :
    pairCoordinate (finiteEmbed ψ) (2*i.val) (2*i.val+1) R.val=0 := by
  unfold pairCoordinate
  split_ifs with h
  · let T : ({s : Finset ℕ // s.card = N}) := ⟨insert (2*i.val) (insert (2*i.val+1) R.val),h.2.2.2⟩
    have hT : ¬modesBelow (2*L+s) T := by
      intro ht
      apply hR
      intro n hn
      exact ht n (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn))
    rw [finiteEmbed_outside ψ T hT,mul_zero]
  · rfl
private theorem finite_pair_sum_transport {L s m : ℕ} (coeff : ℕ → ℝ)
    (ψ : (EuclideanSpace ℂ ({s : Fin (2*L+s) → Bool // occupationCount s = (2*m)}))) :
    countableBL coeff m L (finiteEmbed ψ) =
      finiteEmbed (finitePairOutput (fun i : Fin L => coeff i.val) ψ) := by
  ext R
  by_cases hR : modesBelow (2*L+s) R
  · let x := sectorOfCountable (2*L+s) (2*m-2) R hR
    have hx : finiteOccupation x=R := finiteOccupation_sectorOfCountable _ _ R hR
    rw [← hx,finiteEmbed_apply]
    change (countableBL coeff m L (finiteEmbed ψ)) (finiteOccupation x) = _
    simp only [countableBL,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    rw [← Fin.sum_univ_eq_sum_range]
    simp_rw [pairContract_apply,finite_pair_coordinate]
    change (∑ i : Fin L,(coeff i.val:ℂ) *
      (Matrix.toEuclideanLin (D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner.fullC (downMode i)*
        D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner.fullC (upMode i))) (lift ψ) x.val) = _
    simp only [finitePairOutput,WithLp.ofLp_toLp,standardB,map_sum,map_smul,
      LinearMap.sum_apply,LinearMap.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
  · rw [finiteEmbed_outside _ R hR]
    simp only [countableBL,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i hi
    rw [pairContract_apply]
    have hiL : i<L := Finset.mem_range.mp hi
    rw [finite_pair_outside ⟨i,hiL⟩ ψ R hR,mul_zero]
/-- The corrected finite bound holds on the complete countable sector at each pair cutoff. -/
theorem countable_finite_corrected_bound (m : ℕ) (hm : 1 ≤ m) (c : CanonicalSequence)
    (α : ℝ) (hpa : ∀ i,c.coeff i^2 ≤ α) (hsmall : 2*(m:ℝ)*α ≤ 1)
    (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) (L : ℕ) :
    ‖countableBL c.coeff m L ψ‖^2 ≤
      ((m:ℝ)-(m:ℝ)*((m:ℝ)-1)*(∑ i ∈ Finset.range L,c.coeff i^4)+(5/2)*(m:ℝ)^3*α^2)*‖ψ‖^2 := by
  have hα : 0 ≤ α := (sq_nonneg (c.coeff 0)).trans (hpa 0)
  have hd : Tendsto (fun s : ℕ => finiteEmbed (finiteRestrict (d := 2*L+s) ψ)) atTop (𝓝 ψ) := by
    have hadd : Tendsto (fun s : ℕ => 2*L+s) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat (2*L)
    exact (finiteEmbedding_dense (2*m) ψ).comp hadd
  have hleft := ((countableBLCLM c.coeff m L).continuous.tendsto ψ).comp hd
  have hn := hleft.norm.pow 2
  have hr := hd.norm.pow 2
  apply le_of_tendsto_of_tendsto' (by simpa only [countableBLCLM_apply] using hn)
    (tendsto_const_nhds.mul hr)
  intro s
  let v := finiteRestrict (d := 2*L+s) ψ
  have h := actual_sector_bound (fun i : Fin L => c.coeff i.val) (fun i => c.nonneg i.val)
    m hm α hα (fun i => hpa i.val) (by
      calc
        _ = ∑ i ∈ Finset.range L,c.coeff i^2 := Fin.sum_univ_eq_sum_range _ L
        _ ≤ 1 := finite_mass_le_one c L) hsmall v
  simp only [Function.comp_apply,countableBLCLM_apply]
  change ‖countableBL c.coeff m L (finiteEmbed v)‖^2 ≤ _
  rw [finite_pair_sum_transport,finiteEmbed_norm,finitePairOutput_norm]
  have hs4 : (∑ i : Fin L,c.coeff i.val^4) = ∑ i ∈ Finset.range L,c.coeff i^4 :=
    Fin.sum_univ_eq_sum_range (fun i => c.coeff i^4) L
  rw [hs4,lift_norm] at h
  simpa only [finiteEmbed_norm] using h
end
section
open scoped BigOperators Classical
/-- This isolates the remaining transport obligation; it is not a coordinate_result : coordinateClaim. -/
private theorem assembly_of_countable_finite_bounds
    (hfinite : ∀ (m : ℕ), 1 ≤ m → ∀ (c : CanonicalSequence) (α : ℝ),
      (∀ i,c.coeff i^2 ≤ α) → 2*(m:ℝ)*α ≤ 1 →
      ∀ ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2), ‖ψ‖=1 → ∀ L : ℕ,
        ‖countableBL c.coeff m L ψ‖^2 ≤
          (m:ℝ)-(m:ℝ)*((m:ℝ)-1)*(∑ i ∈ Finset.range L,c.coeff i^4)+(5/2)*(m:ℝ)^3*α^2) :
    coordinateClaim := by
  unfold coordinateClaim
  intro m hm c α hpa hsmall ψ hψ
  rw [countable_identity_2_4]
  exact norm_limit_chr3 c m α hpa (fun L => countableBL c.coeff m L ψ)
    (countableB c.coeff m ψ) (countableBL_tendsto c.coeff c.summable_sq m ψ)
    (hfinite m hm c α hpa hsmall ψ hψ)
end
section
open scoped BigOperators Classical
/-- CHR-3 on the completed adjacent-pair occupation carrier. -/
private theorem coordinate_result : coordinateClaim := by
  apply assembly_of_countable_finite_bounds
  intro m hm c α hpa hsmall ψ hψ L
  have h := countable_finite_corrected_bound m hm c α hpa hsmall ψ L
  simpa only [hψ,one_pow,mul_one] using h
end
section
open scoped BigOperators Classical
/-- The coordinateClaim uses the independently defined bounded RDM, on the countable occupation carrier. -/
def completedClaim : Prop := ∀ (m : ℕ), 1 ≤ m → ∀ (c : CanonicalSequence) (α : ℝ),
  (∀ i, c.coeff i^2 ≤ α) → 2*(m:ℝ)*α ≤ 1 →
  ∀ ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2), ‖ψ‖ = 1 →
  completedRayleigh (2*m) ψ (canonicalTensor c) ≤ (2*(m:ℝ))*
    (1-((m:ℝ)-1)*(∑' i,c.coeff i^4)+(5/8:ℝ)*(2*(m:ℝ)*α)^2)
theorem completed_result : completedClaim := by
  intro m hm c α hpa hsmall ψ hψ
  rw [completed_identity_2_4]
  have h := coordinate_result m hm c α hpa hsmall ψ hψ
  rwa [countable_identity_2_4] at h
end
end D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound
