/- GID: D5/S3/Arith/Lattices/GirardPlagneBoxLimit
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/GirardPlagneBoxLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Fixed-support box Davenport ratios converge in every positive dimension. -/

/-
admission_basis: open-problem-resolution (#17348; Proved)
Direct frozen dependencies: none; mathematical owners are pinned Mathlib.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17570.
The claim is definitionally equal to the preregistered statement; the explicit limit is delta d.
The admission basis names the settling result and no escape witness.
D: proof_shape: bind-only; escape_witness: none; consumers: result, D_lower_eventually_of_simplex, D_lower_eventually, D_upper_eventually, claim, girard_plagne_box_limit.
claim: proof_shape: bind-only; escape_witness: none; consumers: external statement.
finite_minimal_on_finset: proof_shape: bind-only; escape_witness: none; consumers: lengths_finite.
box_finite: proof_shape: bind-only; escape_witness: none; consumers: lengths_finite.
lengths_finite: proof_shape: bind-only; escape_witness: none; consumers: lengths_bddAbove.
lengths_bddAbove: proof_shape: bind-only; escape_witness: none; consumers: result, D_lower_eventually_of_simplex.
simplexVertices: proof_shape: bind-only; escape_witness: none; consumers: lengths_nonempty, simplexSequence_in_box, total_on_simplex, simplexSequence_support, simplexVertices_card, simplexSequence_apply, simplexSequence, simplexSequence_minimal.
simplexSequence: proof_shape: bind-only; escape_witness: none; consumers: lengths_nonempty, simplexSequence_in_box, _proof_1_2, simplexSequence_support, simplexSequence_apply, simplexSequence_minimal.
basisVertex_injective: proof_shape: bind-only; escape_witness: none; consumers: total_on_simplex, simplexVertices_card.
negVertex_notMem_image: proof_shape: bind-only; escape_witness: none; consumers: total_on_simplex, simplexVertices_card.
simplexVertices_card: proof_shape: bind-only; escape_witness: none; consumers: lengths_nonempty.
simplexSequence_apply: proof_shape: bind-only; escape_witness: none; consumers: simplexSequence_support, simplexSequence_minimal.
simplexSequence_support: proof_shape: bind-only; escape_witness: none; consumers: lengths_nonempty, simplexSequence_in_box, simplexSequence_minimal.
total_on_simplex: proof_shape: bind-only; escape_witness: none; consumers: simplexSequence_minimal.
simplexSequence_minimal: proof_shape: content; escape_witness: none; consumers: lengths_nonempty.
simplexSequence_in_box: proof_shape: bind-only; escape_witness: none; consumers: lengths_nonempty.
lengths_nonempty: proof_shape: content; escape_witness: none; consumers: result, D_upper_bound.
supportEmbedding: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, supportEmbedding_reconstruct, supportEmbedding_positive, _proof_1_2, _proof_1_1.
supportEmbedding_mem: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound, supportEmbedding_positive.
supportEmbedding_reconstruct: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound.
supportEmbedding_positive: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound.
lengths_upper_bound: proof_shape: content; escape_witness: none; consumers: D_upper_bound.
interiorSimplex: proof_shape: bind-only; escape_witness: none; consumers: interiorSimplex_bound, interiorSimplex_positive_kernel, D_lower_eventually, interiorSimplex_nonsingular.
interiorSimplex_det: proof_shape: bind-only; escape_witness: none; consumers: D_lower_eventually, interiorSimplex_nonsingular.
interiorSimplex_bound: proof_shape: bind-only; escape_witness: none; consumers: D_lower_eventually.
interiorSimplex_positive_kernel: proof_shape: content; escape_witness: none; consumers: D_lower_eventually.
interiorSimplex_nonsingular: proof_shape: bind-only; escape_witness: none; consumers: D_lower_eventually.
cofactor_smul: proof_shape: bind-only; escape_witness: none; consumers: normalized_pencil_cofactor_limit.
cofactor_map: proof_shape: bind-only; escape_witness: none; consumers: normalized_pencil_cofactor_limit.
continuous_augmented_det: proof_shape: bind-only; escape_witness: none; consumers: normalized_pencil_det_limit.
continuous_cofactor: proof_shape: bind-only; escape_witness: none; consumers: normalized_pencil_cofactor_limit.
normalized_pencil_matrix_limit: proof_shape: bind-only; escape_witness: none; consumers: normalized_pencil_det_limit, normalized_pencil_cofactor_limit.
normalized_pencil_det_limit: proof_shape: bind-only; escape_witness: none; consumers: exists_asymptotic_lower_family.
normalized_pencil_cofactor_limit: proof_shape: bind-only; escape_witness: none; consumers: exists_asymptotic_lower_family.
pencilScale: proof_shape: bind-only; escape_witness: none; consumers: pencilScale_limit, pencilScale_nonneg, pencilScale_budget, exists_asymptotic_lower_family.
pencilScale_nonneg: proof_shape: bind-only; escape_witness: none; consumers: exists_asymptotic_lower_family.
pencilScale_budget: proof_shape: bind-only; escape_witness: none; consumers: exists_asymptotic_lower_family.
pencilScale_limit: proof_shape: bind-only; escape_witness: none; consumers: exists_asymptotic_lower_family.
exists_asymptotic_lower_family: proof_shape: content; escape_witness: none; consumers: D_lower_eventually_of_simplex.
D_lower_eventually_of_simplex: proof_shape: content; escape_witness: none; consumers: D_lower_eventually.
D_upper_bound: proof_shape: content; escape_witness: none; consumers: D_upper_eventually.
lower_degree_ratio_limit: proof_shape: bind-only; escape_witness: none; consumers: D_upper_eventually.
D_upper_eventually: proof_shape: content; escape_witness: none; consumers: girard_plagne_box_limit.
D_lower_eventually: proof_shape: content; escape_witness: none; consumers: girard_plagne_box_limit.
girard_plagne_box_limit: proof_shape: content; escape_witness: none; consumers: result.
result: proof_shape: content; escape_witness: none; consumers: settling result.
-/

import D5.S3.Arith.Lattices.CubeSimplexDeterminant
import D5.S3.Arith.Lattices.PrimitivePencil
import D5.S3.Arith.Lattices.MinimalKernelPacking
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace D5.S3.Arith.Lattices.GirardPlagneBoxLimit
open D5.S3.Arith.Lattices.CofactorKernel D5.S3.Arith.Lattices.CubeSimplexDeterminant D5.S3.Arith.Lattices.PrimitivePencil D5.S3.Arith.Lattices.MinimalKernelPacking

/-- `D^{(k)}(⟦-m, m⟧^d)`, the maximal length of such a sequence. -/
def D (d m k : ℕ) : ℕ := sSup (lengths d m k)

def claim : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∀ m : ℕ, 1 ≤ m → (lengths d m (d + 1)).Nonempty ∧ BddAbove (lengths d m (d + 1))) ∧
    ∃ L : ℝ, Filter.Tendsto (fun m : ℕ => (D d m (d + 1) : ℝ) / (m : ℝ) ^ d) Filter.atTop (nhds L)

open scoped BigOperators

private theorem finite_minimal_on_finset {d : ℕ} (s : Finset (Fin d → ℤ)) :
    {f : (Fin d → ℤ) →₀ ℕ | IsMinimalZeroSum f ∧ f.support ⊆ s}.Finite := by
  classical
  let S : Set ((Fin d → ℤ) →₀ ℕ) := {f | IsMinimalZeroSum f ∧ f.support ⊆ s}
  let R : ((Fin d → ℤ) →₀ ℕ) → (s → ℕ) := fun f v => f v.val
  have zero_out (f : (Fin d → ℤ) →₀ ℕ) (hf : f ∈ S) (v : Fin d → ℤ)
      (hv : v ∉ s) : f v = 0 := by
    exact Finsupp.notMem_support_iff.mp (fun h => hv (hf.2 h))
  have R_inj : Set.InjOn R S := by
    intro f hf g hg hfg
    ext v
    by_cases hv : v ∈ s
    · exact congrFun hfg ⟨v, hv⟩
    · rw [zero_out f hf v hv, zero_out g hg v hv]
  have hanti : IsAntichain (· ≤ ·) (R '' S) := by
    intro a ha b hb hab hle
    rcases ha with ⟨f, hf, rfl⟩
    rcases hb with ⟨g, hg, rfl⟩
    have hfg : f ≤ g := by
      intro v
      by_cases hv : v ∈ s
      · exact hle ⟨v, hv⟩
      · rw [zero_out f hf v hv]
        exact Nat.zero_le _
    have heq : f = g := by
      by_contra hn
      exact hg.1.2.2 f hfg hf.1.1 hn hf.1.2.1
    exact hab (congrArg R heq)
  exact (WellQuasiOrderedLE.finite_of_isAntichain hanti).of_finite_image R_inj

private theorem box_finite (d m : ℕ) : ((fun d m => {v : Fin d → ℤ | ∀ i, |v i| ≤ (m : ℕ)}) d m).Finite := by
  apply (Set.Finite.pi fun _ => (Set.finite_Icc (- (m : ℤ)) (m : ℤ))).subset
  intro v hv i hi
  exact abs_le.mp (hv i)

private theorem lengths_finite (d m k : ℕ) : (lengths d m k).Finite := by
  classical
  let s := (box_finite d m).toFinset
  apply ((finite_minimal_on_finset s).image (Finsupp.degree (R := ℕ))).subset
  rintro L ⟨f, hf, hb, hc, rfl⟩
  refine ⟨f, ⟨hf, ?_⟩, rfl⟩
  intro v hv
  exact (Set.Finite.mem_toFinset _).mpr (hb hv)

private theorem lengths_bddAbove (d m k : ℕ) : BddAbove (lengths d m k) := by
  exact (lengths_finite d m k).bddAbove

open scoped BigOperators





private def simplexVertices (d : ℕ) : Finset (Fin d → ℤ) :=
  insert ((fun _ : Fin d => (-1 : ℤ))) (Finset.univ.image (fun i : Fin d => (Pi.single i (1 : ℤ) : Fin d → ℤ)))

private def simplexSequence (d : ℕ) : (Fin d → ℤ) →₀ ℕ :=
  Finsupp.indicator (simplexVertices d) (fun _ _ => 1)

private theorem basisVertex_injective {d : ℕ} : Function.Injective ((fun i : Fin d => Pi.single i (1 : ℤ))) := by
  simpa only [Function.comp_def, Finsupp.equivFunOnFinite_single] using
    ((Finsupp.equivFunOnFinite (α := Fin d) (M := ℤ)).injective.comp
      (Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)))

private theorem negVertex_notMem_image (d : ℕ) :
    (fun _ : Fin d => (-1 : ℤ)) ∉ Finset.univ.image ((fun i : Fin d => Pi.single i (1 : ℤ))) := by
  classical
  rintro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hh := congrFun he i
  norm_num [] at hh

private theorem simplexVertices_card (d : ℕ) : (simplexVertices d).card = d + 1 := by
  classical
  simp [simplexVertices, Finset.card_insert_of_notMem (negVertex_notMem_image d),
    Finset.card_image_of_injective _ basisVertex_injective]

private theorem simplexSequence_apply (d : ℕ) (v : Fin d → ℤ) :
    simplexSequence d v = if v ∈ simplexVertices d then 1 else 0 := by
  classical
  simp [simplexSequence, Finsupp.indicator_apply]

private theorem simplexSequence_support (d : ℕ) :
    (simplexSequence d).support = simplexVertices d := by
  classical
  ext v
  simp [Finsupp.mem_support_iff, simplexSequence_apply]

private theorem total_on_simplex {d : ℕ} (f : (Fin d → ℤ) →₀ ℕ)
    (hf : f.support ⊆ simplexVertices d) (i : Fin d) :
    (fun f : (Fin d → ℤ) →₀ ℕ => f.sum (fun v n => (n : ℤ) • v)) f i = (f ((fun i : Fin d => (Pi.single i (1 : ℤ) : Fin d → ℤ)) i) : ℤ) - f ((fun _ : Fin d => (-1 : ℤ))) := by
  classical
  have hsum : (fun f : (Fin d → ℤ) →₀ ℕ => f.sum (fun v n => (n : ℤ) • v)) f i = ∑ v ∈ simplexVertices d, (f v : ℤ) * v i := by
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_subset hf (fun v hv hvf => by
      simp [Finsupp.notMem_support_iff.mp hvf])
  rw [hsum, simplexVertices, Finset.sum_insert (negVertex_notMem_image d),
    Finset.sum_image (fun _ _ _ _ h => basisVertex_injective h)]
  simp [Pi.single_apply, eq_comm]
  ring

private theorem simplexSequence_minimal (d : ℕ) : IsMinimalZeroSum (simplexSequence d) := by
  classical
  have hn : simplexSequence d ((fun _ : Fin d => (-1 : ℤ))) = 1 := by
    simp [simplexSequence_apply, simplexVertices]
  have he (i : Fin d) : simplexSequence d ((fun i : Fin d => (Pi.single i (1 : ℤ) : Fin d → ℤ)) i) = 1 := by
    simp [simplexSequence_apply, simplexVertices]
  have hs : (simplexSequence d).support ⊆ simplexVertices d :=
    (simplexSequence_support d).le
  refine ⟨?_, ?_, ?_⟩
  · intro hh
    have hh' := DFunLike.congr_fun hh ((fun _ : Fin d => (-1 : ℤ)))
    simp [hn] at hh'
  · ext i
    rw [total_on_simplex _ hs, hn, he]
    simp
  · intro g hgf hgn hgne hgz
    have hgs : g.support ⊆ simplexVertices d := (Finsupp.support_mono hgf).trans hs
    have heq (i : Fin d) : g ((fun i : Fin d => (Pi.single i (1 : ℤ) : Fin d → ℤ)) i) = g ((fun _ : Fin d => (-1 : ℤ))) := by
      have hz := congrFun hgz i
      rw [total_on_simplex _ hgs] at hz
      exact_mod_cast (sub_eq_zero.mp hz)
    have hnle : g ((fun _ : Fin d => (-1 : ℤ))) ≤ 1 := by simpa [hn] using hgf ((fun _ : Fin d => (-1 : ℤ)))
    have hnne : g ((fun _ : Fin d => (-1 : ℤ))) ≠ 0 := by
      intro hh
      apply hgn
      ext v
      by_cases hv : v ∈ simplexVertices d
      · rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hh
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
          exact (heq i).trans hh
      · exact Finsupp.notMem_support_iff.mp (fun hg => hv (hgs hg))
    have hone : g ((fun _ : Fin d => (-1 : ℤ))) = 1 := by omega
    apply hgne
    ext v
    by_cases hv : v ∈ simplexVertices d
    · rw [simplexSequence_apply, if_pos hv]
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hone
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        exact (heq i).trans hone
    · rw [simplexSequence_apply, if_neg hv]
      exact Finsupp.notMem_support_iff.mp (fun hg => hv (hgs hg))

private theorem simplexSequence_in_box (d m : ℕ) (hm : 1 ≤ m) :
    (↑(simplexSequence d).support : Set (Fin d → ℤ)) ⊆ (fun d m => {v : Fin d → ℤ | ∀ i, |v i| ≤ (m : ℕ)}) d m := by
  classical
  intro v hv
  rw [simplexSequence_support] at hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · intro i
    simpa [] using (show (1 : ℤ) ≤ m by exact_mod_cast hm)
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    intro i
    by_cases hij : i = j
    · subst i
      simpa [Pi.single_apply] using (show (1 : ℤ) ≤ m by exact_mod_cast hm)
    · simp [Pi.single_apply, hij, Ne.symm hij]

private theorem lengths_nonempty (d m : ℕ) (hm : 1 ≤ m) :
    (lengths d m (d + 1)).Nonempty := by
  refine ⟨(Finsupp.degree (R := ℕ)) (simplexSequence d), simplexSequence d, simplexSequence_minimal d,
    simplexSequence_in_box d m hm, ?_, rfl⟩
  rw [simplexSequence_support, simplexVertices_card]

open scoped BigOperators
open Matrix

private def supportEmbedding {d k : ℕ} (f : (Fin d → ℤ) →₀ ℕ) (hf : f.support.card=k) :
    Fin k ↪ (Fin d → ℤ) :=
  (f.support.equivFinOfCardEq hf).symm.toEmbedding.trans (Function.Embedding.subtype _)

private theorem supportEmbedding_mem {d k : ℕ} (f : (Fin d → ℤ) →₀ ℕ)
    (hf : f.support.card=k) (j : Fin k) : supportEmbedding f hf j ∈ f.support := by
  exact ((f.support.equivFinOfCardEq hf).symm j).property

private theorem supportEmbedding_reconstruct {d k : ℕ} (f : (Fin d → ℤ) →₀ ℕ)
    (hf : f.support.card=k) : fromWeights (supportEmbedding f hf)
      (fun j => f (supportEmbedding f hf j))=f := by
  apply fromWeights_restrict
  intro v hv
  refine ⟨f.support.equivFinOfCardEq hf ⟨v,hv⟩, ?_⟩
  simp [supportEmbedding]

private theorem supportEmbedding_positive {d k : ℕ} (f : (Fin d → ℤ) →₀ ℕ)
    (hf : f.support.card=k) (j : Fin k) : 0 < f (supportEmbedding f hf j) := by
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (supportEmbedding_mem f hf j))

private theorem lengths_upper_bound {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    {L : ℕ} (hL : L ∈ lengths d m (d+1)) :
    L ≤ max (delta d * m^d) ((2*(d+1)*m+1)^(d-1)*(d+1)) := by
  classical
  obtain ⟨f,hmin,hbox,hcard,hlen⟩ := hL
  change (Finsupp.degree (R := ℕ)) f = L at hlen
  let v := supportEmbedding f hcard
  let x : Fin (d+1) → ℕ := fun j => f (v j)
  have hrec : fromWeights v x=f := supportEmbedding_reconstruct f hcard
  have hp : ∀ j, 0<x j := supportEmbedding_positive f hcard
  have hmn : IsMinimalZeroSum (fromWeights v x) := hrec.symm ▸ hmin
  have hbound : ∀ i j, |(Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose i j| ≤ m := by
    intro i j
    exact hbox (supportEmbedding_mem f hcard j) i
  have hx : (Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose *ᵥ (fun j => (x j : ℤ))=0 := by
    rw [← total_fromWeights_eq_mulVec, hrec]
    exact hmin.2.1
  have hsum : 0<∑ j,x j := Finset.sum_pos (fun j _ => hp j) Finset.univ_nonempty
  have hlen' : ∑ j,x j=L := by rw [← length_fromWeights, hrec, hlen]
  by_cases hr : Function.Injective (fun z : Fin d → ℤ => ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose).transpose *ᵥ z)
  · have hs : ∑ j,(x j : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hsum)
    have hdet := augmented_det_ne_zero_of_full_rank_positive ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) hr _ hx hs
    have hid := sequence_cofactor_length v x hp hmn hdet
    have hgd : 0 < Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)) := by
      have hg := show (0 : ℤ) ≤ Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)) from by
        rw [← Finset.normalize_gcd, ← Int.abs_eq_normalize]
        exact abs_nonneg _
      by_contra hn
      have hz : Finset.univ.gcd (cofactor ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose))=0 := by omega
      rw [hz,mul_zero] at hid
      exact hdet (abs_eq_zero.mp hid)
    have hle : (L : ℤ) ≤ (delta d : ℤ)*(m : ℤ)^d := by
      have hll : (L : ℤ) ≤ |(augment ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose)).det| := by
        rw [hid, hrec, hlen]
        nlinarith [show (0 : ℤ) ≤ L from Int.natCast_nonneg L]
      exact hll.trans (augmented_det_integer_box_bound hm ((Matrix.of (v : Fin (d+1) → Fin d → ℤ)).transpose) hbound)
    have hn : L ≤ delta d*m^d := by exact_mod_cast hle
    exact hn.trans (le_max_left _ _)
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    have hb := minimal_kernel_rank_deficient_bound ((Matrix.of (v : Fin (r+1+1) → Fin (r+1) → ℤ)).transpose) hbound hr x hsum hx
      (fromWeights_minimal_to_vector v x hmn)
    rw [hlen'] at hb
    exact hb.trans (le_max_right _ _)

open scoped BigOperators
open Matrix
set_option maxRecDepth 2000

private def interiorSimplex {d : ℕ} (V : Matrix (Fin d) (Fin (d+1)) ℤ) (n : ℕ) :
    Matrix (Fin d) (Fin (d+1)) ℤ :=
  Matrix.of (fun i j => (n : ℤ)*(d+1)*V i j - ∑ l, V i l)

private theorem interiorSimplex_det {d : ℕ} (V : Matrix (Fin d) (Fin (d+1)) ℤ) (n : ℕ) :
    (augment (interiorSimplex V n)).det = ((n : ℤ)*(d+1))^d*(augment V).det := by
  exact augmented_det_affine ((n : ℤ)*(d+1)) (fun i => -∑ l,V i l) V

private theorem interiorSimplex_bound {d : ℕ} (V : Matrix (Fin d) (Fin (d+1)) ℤ)
  (hV : ∀ i j, |V i j| ≤ 1) (n : ℕ) (i : Fin d) (j : Fin (d+1)) :
  |interiorSimplex V n i j| ≤ ((n+1)*(d+1) : ℕ) := by
  have hn : (0 : ℤ) ≤ (n : ℤ)*(d+1) := by positivity
  have hs : |∑ l,V i l| ≤ d+1 := by
    calc
      |∑ l,V i l| ≤ ∑ l,|V i l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin (d+1), (1 : ℤ) := Finset.sum_le_sum (fun l _ => hV i l)
      _ = d+1 := by simp
  calc
    |interiorSimplex V n i j| ≤ |(n : ℤ)*(d+1)*V i j|+|∑ l,V i l| := by
        simpa only [interiorSimplex, Matrix.of_apply, sub_zero, zero_sub, abs_neg] using (abs_sub_le ((n : ℤ)*(d+1)*V i j) 0 (∑ l,V i l))
    _ = (n : ℤ)*(d+1)*|V i j|+|∑ l,V i l| := by rw [abs_mul,abs_of_nonneg hn]
    _ ≤ (n : ℤ)*(d+1)*1+(d+1) := add_le_add (mul_le_mul_of_nonneg_left (hV i j) hn) hs
    _ = ((n+1)*(d+1) : ℕ) := by push_cast; ring

private theorem interiorSimplex_positive_kernel {d : ℕ}
    (V : Matrix (Fin d) (Fin (d+1)) ℤ)
    (hdet : (augment V).det ≠ 0)
    (hcof : ∀ j, 0 ≤ (augment V).det*cofactor V j)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : Fin (d+1) → ℤ, (∀ j, 0<x j) ∧ interiorSimplex V n *ᵥ x=0 := by
  let C : ℤ := (augment V).det^2
  let c : Fin (d+1) → ℤ := fun j => (augment V).det*cofactor V j
  have hC : 0<C := sq_pos_of_ne_zero hdet
  have hcs : ∑ j,c j=C := by
    simp only [c, ← Finset.mul_sum, sum_cofactor_eq_det, C, pow_two]
  have hck : V *ᵥ c=0 := by
    change V *ᵥ ((augment V).det • cofactor V)=0
    rw [Matrix.mulVec_smul, cofactor_mulVec_eq_zero, smul_zero]
  let x : Fin (d+1) → ℤ := fun j => (d+1)*((n : ℤ)-1)*c j+C
  have hp : ∀ j,0<x j := by
    intro j
    have hnj : (0 : ℤ) ≤ (d+1)*((n : ℤ)-1) := by
      have hni : (2 : ℤ) ≤ n := by exact_mod_cast hn
      exact mul_nonneg (by omega) (by omega)
    exact lt_of_lt_of_le hC (le_add_of_nonneg_left (mul_nonneg hnj (hcof j)))
  have hxs : ∑ j,x j=(n : ℤ)*(d+1)*C := by
    simp only [x,Finset.sum_add_distrib,← Finset.mul_sum,hcs,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    ring
  refine ⟨x,hp,?_⟩
  funext i
  have hki : ∑ j,V i j*c j=0 := congrFun hck i
  change ∑ j,((n : ℤ)*(d+1)*V i j-∑ l,V i l)*x j=0
  calc
    (∑ j,((n : ℤ)*(d+1)*V i j-∑ l,V i l)*x j) =
        (n : ℤ)*(d+1)*(∑ j,V i j*x j)-(∑ l,V i l)*(∑ j,x j) := by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = 0 := by
      have hvx : ∑ j,V i j*x j=C*(∑ j,V i j) := by
        calc
          (∑ j,V i j*x j) = (d+1)*((n : ℤ)-1)*(∑ j,V i j*c j)+C*(∑ j,V i j) := by
            simp only [Finset.mul_sum,← Finset.sum_add_distrib,x]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = C*(∑ j,V i j) := by rw [hki]; ring
      rw [hvx,hxs]
      ring

private theorem interiorSimplex_nonsingular {d : ℕ}
    (V : Matrix (Fin d) (Fin (d+1)) ℤ) (hdet : (augment V).det ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) : (augment (interiorSimplex V n)).det ≠ 0 := by
  rw [interiorSimplex_det]
  apply mul_ne_zero _ hdet
  apply pow_ne_zero
  apply mul_ne_zero
  · exact_mod_cast (by omega : n ≠ 0)
  · omega

open scoped BigOperators
open Matrix Filter Topology

private theorem cofactor_smul {R : Type*} [CommRing R] {d : ℕ}
    (c : R) (M : Matrix (Fin d) (Fin (d+1)) R) (j : Fin (d+1)) :
    cofactor (c • M) j=c^d*cofactor M j := by
  have he : (c • M).submatrix id j.succAbove=c • (M.submatrix id j.succAbove) := rfl
  simp only [cofactor,he,Matrix.det_smul,Fintype.card_fin]
  ring

private theorem cofactor_map {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}
    (f : R →+* S) (M : Matrix (Fin d) (Fin (d+1)) R) (j : Fin (d+1)) :
    cofactor (M.map f) j=f (cofactor M j) := by
  simp only [cofactor,map_mul,map_pow,map_neg,map_one]
  congr 1
  exact (f.map_det (M.submatrix id j.succAbove)).symm

private theorem continuous_augmented_det {d : ℕ} :
    Continuous (fun M : Matrix (Fin d) (Fin (d+1)) ℝ => (augment M).det) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact continuous_const
  · exact (continuous_apply i)

private theorem continuous_cofactor {d : ℕ} (j : Fin (d+1)) :
    Continuous (fun M : Matrix (Fin d) (Fin (d+1)) ℝ => cofactor M j) := by
  unfold cofactor
  apply Continuous.const_mul
  apply Continuous.matrix_det
  exact continuous_pi (fun i => continuous_pi (fun k => (continuous_apply (j.succAbove k)).comp (continuous_apply i)))

private theorem normalized_pencil_matrix_limit {d : ℕ}
    (A B : Matrix (Fin d) (Fin (d+1)) ℤ) (t : ℕ → ℤ) (c : ℝ)
    (ht : Tendsto (fun m : ℕ => (t m : ℝ)/(m : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun m : ℕ => (m : ℝ)⁻¹ • ((t m • A+B).map (Int.castRingHom ℝ)))
      atTop (𝓝 (c • A.map (Int.castRingHom ℝ))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hh := (ht.mul_const (A i j : ℝ)).add
    ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (B i j : ℝ))
  simpa [Matrix.smul_apply,Matrix.map_apply,Matrix.add_apply,Int.cast_add,
    Int.cast_mul,smul_eq_mul,div_eq_mul_inv,mul_add,add_mul,mul_comm,mul_left_comm,mul_assoc] using hh

private theorem normalized_pencil_det_limit {d : ℕ}
  (A B : Matrix (Fin d) (Fin (d+1)) ℤ) (t : ℕ → ℤ) (c : ℝ)
  (ht : Tendsto (fun m : ℕ => (t m : ℝ)/(m : ℝ)) atTop (𝓝 c)) :
  Tendsto (fun m : ℕ => ((augment (t m • A+B)).det : ℝ)/(m : ℝ)^d)
    atTop (𝓝 (c^d*((augment A).det : ℝ))) := by
  have hh := continuous_augmented_det.tendsto _ |>.comp (normalized_pencil_matrix_limit A B t c ht)
  change Tendsto (fun m : ℕ => (augment ((m : ℝ)⁻¹ • ((t m • A+B).map (Int.castRingHom ℝ)))).det) atTop
    (𝓝 ((augment (c • A.map (Int.castRingHom ℝ))).det)) at hh
  simp only [augmented_det_smul,augment_map] at hh
  change Tendsto (fun m : ℕ => (m : ℝ)⁻¹^d*
    (((augment (t m • A+B)).map (fun z : ℤ => (z : ℝ))).det)) atTop
    (𝓝 (c^d*((augment A).map (fun z : ℤ => (z : ℝ))).det)) at hh
  simp only [← Int.cast_det,inv_pow] at hh
  simpa only [div_eq_mul_inv,mul_comm, Int.coe_castRingHom] using hh

private theorem normalized_pencil_cofactor_limit {d : ℕ}
  (A B : Matrix (Fin d) (Fin (d+1)) ℤ) (t : ℕ → ℤ) (c : ℝ)
  (ht : Tendsto (fun m : ℕ => (t m : ℝ)/(m : ℝ)) atTop (𝓝 c)) (j : Fin (d+1)) :
  Tendsto (fun m : ℕ => ((cofactor (t m • A+B) j : ℤ) : ℝ)/(m : ℝ)^d)
    atTop (𝓝 (c^d*((cofactor A j : ℤ) : ℝ))) := by
  have hh := (continuous_cofactor j).tendsto _ |>.comp (normalized_pencil_matrix_limit A B t c ht)
  change Tendsto (fun m : ℕ => cofactor ((m : ℝ)⁻¹ • ((t m • A+B).map (Int.castRingHom ℝ))) j) atTop
    (𝓝 (cofactor (c • A.map (Int.castRingHom ℝ)) j)) at hh
  simp only [cofactor_smul,cofactor_map,inv_pow] at hh
  simpa only [div_eq_mul_inv,mul_comm, Int.coe_castRingHom] using hh

open scoped BigOperators
open Filter Topology

private def pencilScale (q b m : ℕ) : ℤ := (m/q : ℕ)-b

private theorem pencilScale_nonneg {q b m : ℕ} (hq : 0<q) (hm : q*b≤m) :
    0≤pencilScale q b m := by
  have he : b≤m/q := (Nat.le_div_iff_mul_le hq).mpr (by simpa [mul_comm] using hm)
  change (0 : ℤ) ≤ (m/q : ℕ)-b
  exact sub_nonneg.mpr (by exact_mod_cast he)

private theorem pencilScale_budget {q b m : ℕ} (hq : 0<q) :
    pencilScale q b m*q+b≤m := by
  have hdiv : (m/q : ℕ)*q≤m := Nat.div_mul_le_self m q
  have hq' : (1 : ℤ)≤q := by exact_mod_cast hq
  have hb : (0 : ℤ)≤b := Int.natCast_nonneg b
  have hh : ((m/q : ℕ) : ℤ)*q≤m := by exact_mod_cast hdiv
  change (((m/q : ℕ) : ℤ)-b)*q+b≤m
  nlinarith

private theorem pencilScale_limit {q : ℕ} (hq : 0<q) (b : ℕ) :
    Tendsto (fun m : ℕ => (pencilScale q b m : ℝ)/(m : ℝ)) atTop (𝓝 ((q : ℝ)⁻¹)) := by
  have hq' : (q : ℝ)≠0 := by exact_mod_cast (ne_of_gt hq)
  have hdiv : Tendsto (fun m : ℕ => ((m/q : ℕ) : ℝ)/(m : ℝ)) atTop (𝓝 ((q : ℝ)⁻¹)) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_mod_div_atTop_nhds_zero_nat hq)).div_const (q : ℝ)
    simp only [sub_zero,one_div] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm' : (m : ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
    have he : (q : ℝ)*((m/q : ℕ) : ℝ)+((m%q : ℕ) : ℝ)=(m : ℝ) := by
      exact_mod_cast (Nat.div_add_mod m q)
    field_simp
    nlinarith
  have hb := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (b : ℝ)
  simpa only [pencilScale,Int.cast_sub,Int.cast_natCast,sub_div,sub_zero] using hdiv.sub hb

open scoped BigOperators
open Matrix Filter Topology

private theorem exists_asymptotic_lower_family {d q : ℕ} (hq : 0<q)
    (A : Matrix (Fin d) (Fin (d+1)) ℤ) (hA : ∀ i j,|A i j|≤q)
    (hdet : (augment A).det≠0)
    (x : Fin (d+1) → ℤ) (hp : ∀ j,0<x j) (hx : A *ᵥ x=0) :
    ∃ F : ℕ → ℕ,
      (∀ᶠ m : ℕ in atTop,F m∈lengths d m (d+1)) ∧
      Tendsto (fun m : ℕ => (F m : ℝ)/(m : ℝ)^d) atTop
        (𝓝 (|(augment A).det|/(q : ℝ)^d)) := by
  classical
  obtain ⟨B,hB⟩ := primitive_pencil_perturbation A (transpose_injective_of_augmented_det A hdet)
  obtain ⟨s,hs,hsp⟩ := positive_kernel_orientation A hdet x hp hx
  let b : ℕ := Finset.univ.sup (fun p : Fin d × Fin (d+1) => (B p.1 p.2).natAbs)
  have hb : ∀ i j,|B i j|≤(b : ℤ) := by
    intro i j
    have he : (B i j).natAbs≤b := Finset.le_sup
      (f := fun p : Fin d × Fin (d+1) => (B p.1 p.2).natAbs) (Finset.mem_univ (i,j))
    simpa only [Int.natCast_natAbs] using (show ((B i j).natAbs : ℤ)≤b by exact_mod_cast he)
  let t : ℕ → ℤ := pencilScale q b
  let M : ℕ → Matrix (Fin d) (Fin (d+1)) ℤ := fun m => t m • A+B
  have ht := pencilScale_limit hq b
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hcp : ∀ᶠ m : ℕ in atTop,∀ j,0<s*cofactor (M m) j := by
    apply Filter.eventually_all.mpr
    intro j
    have hh := (normalized_pencil_cofactor_limit A B t (q : ℝ)⁻¹ ht j).const_mul (s : ℝ)
    have hlimpos : (0 : ℝ)<(s : ℝ)*((q : ℝ)⁻¹^d*((cofactor A j : ℤ) : ℝ)) := by
      have hhsp : (0 : ℝ)<(s : ℝ)*((cofactor A j : ℤ) : ℝ) := by exact_mod_cast hsp j
      have hqp : (0 : ℝ)<(q : ℝ)⁻¹^d := pow_pos (inv_pos.mpr hqR) _
      nlinarith [mul_pos hqp hhsp]
    filter_upwards [hh.eventually_const_lt hlimpos,eventually_ge_atTop (1 : ℕ)] with m hm hm1
    have hmpos : (0 : ℝ)<(m : ℝ)^d := pow_pos (by exact_mod_cast hm1) _
    have hh' : (0 : ℝ)<(s : ℝ)*((cofactor (M m) j : ℤ) : ℝ)/(m : ℝ)^d := by
      simpa only [M,mul_div_assoc] using hm
    have hpR := (div_pos_iff_of_pos_right hmpos).mp hh'
    exact_mod_cast hpR
  have hmem : ∀ᶠ m : ℕ in atTop,(augment (M m)).det.natAbs∈lengths d m (d+1) := by
    filter_upwards [hcp,eventually_ge_atTop (q*b)] with m hpm hm
    have htm : 0≤t m := pencilScale_nonneg hq hm
    have hMb : ∀ i j,|M m i j|≤m := by
      intro i j
      change |t m*A i j+B i j|≤m
      calc
        |t m*A i j+B i j|≤|t m*A i j|+|B i j| := abs_add_le _ _
        _ = t m*|A i j|+|B i j| := by rw [abs_mul,abs_of_nonneg htm]
        _ ≤ t m*q+b := add_le_add (mul_le_mul_of_nonneg_left (hA i j) htm) (hb i j)
        _ ≤ m := pencilScale_budget hq
    exact primitive_cofactor_admissible (M m) hMb
      (augmented_det_ne_zero_of_oriented_cofactors (M m) s hpm) s hs hpm (hB (t m))
  refine ⟨fun m => (augment (M m)).det.natAbs,hmem,?_⟩
  have hlim := (normalized_pencil_det_limit A B t (q : ℝ)⁻¹ ht).abs
  have hqpow : 0≤(q : ℝ)⁻¹^d := pow_nonneg (inv_nonneg.mpr hqR.le) _
  simpa only [Nat.cast_natAbs,Int.cast_abs,abs_div,abs_inv,abs_pow,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),abs_mul,abs_of_nonneg hqpow,
    div_eq_mul_inv,inv_pow,mul_comm,M] using hlim

private theorem D_lower_eventually_of_simplex {d q : ℕ} (hq : 0<q)
    (A : Matrix (Fin d) (Fin (d+1)) ℤ) (hA : ∀ i j,|A i j|≤q)
    (hdet : (augment A).det≠0)
    (x : Fin (d+1) → ℤ) (hp : ∀ j,0<x j) (hx : A *ᵥ x=0)
    (a : ℝ) (ha : a < |(augment A).det|/(q : ℝ)^d) :
    ∀ᶠ m : ℕ in atTop,a<(D d m (d+1) : ℝ)/(m : ℝ)^d := by
  obtain ⟨F,hF,hlim⟩ := exists_asymptotic_lower_family hq A hA hdet x hp hx
  filter_upwards [hF,hlim.eventually_const_lt ha,eventually_ge_atTop (1 : ℕ)] with m hm hma hm1
  have hle : F m≤D d m (d+1) := le_csSup (lengths_bddAbove d m (d+1)) hm
  have hleR : (F m : ℝ)≤D d m (d+1) := by exact_mod_cast hle
  exact lt_of_lt_of_le hma (div_le_div_of_nonneg_right hleR (pow_nonneg (Nat.cast_nonneg _) _))

open scoped BigOperators
open Filter Topology

private theorem D_upper_bound {d m : ℕ} (hd : 1≤d) (hm : 1≤m) :
    D d m (d+1) ≤ max (delta d*m^d) ((2*(d+1)*m+1)^(d-1)*(d+1)) := by
  exact csSup_le (lengths_nonempty d m hm) (fun _ h => lengths_upper_bound hd hm h)

private theorem lower_degree_ratio_limit {d : ℕ} (hd : 1≤d) :
  Tendsto (fun m : ℕ => (((2*(d+1)*m+1)^(d-1)*(d+1) : ℕ) : ℝ)/(m : ℝ)^d)
    atTop (𝓝 0) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  have hi := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hh := ((((tendsto_const_nhds (x := (2*((r+1 : ℕ)+1) : ℝ))).add hi).pow r).mul_const
    (((r+1 : ℕ)+1) : ℝ)).mul hi
  simp only [add_zero,mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hm' : (m : ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
  simp only [Nat.succ_sub_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_succ]
  have he : (2*((r : ℝ)+1+1)+(m : ℝ)⁻¹)^r =
      (2*((r : ℝ)+1+1)*(m : ℝ)+1)^r/(m : ℝ)^r := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [he,pow_succ]
  field_simp
  <;> ring

private theorem D_upper_eventually {d : ℕ} (hd : 1≤d) (b : ℝ) (hb : (delta d : ℝ)<b) :
    ∀ᶠ m : ℕ in atTop, (D d m (d+1) : ℝ)/(m : ℝ)^d<b := by
  have hdz : (0 : ℝ)≤delta d := Nat.cast_nonneg _
  have hbl : 0<b := lt_of_le_of_lt hdz hb
  have hsmall := (tendsto_order.mp (lower_degree_ratio_limit hd)).2 b hbl
  filter_upwards [eventually_ge_atTop (1 : ℕ),hsmall] with m hm hs
  have hpow : (0 : ℝ)<(m : ℝ)^d := pow_pos (by exact_mod_cast hm) _
  have hu := D_upper_bound hd hm
  have huc : (D d m (d+1) : ℝ) ≤ max
      ((delta d : ℝ)*(m : ℝ)^d)
      (((2*(d+1)*m+1)^(d-1)*(d+1) : ℕ) : ℝ) := by exact_mod_cast hu
  apply (div_lt_iff₀ hpow).mpr
  apply lt_of_le_of_lt huc
  apply max_lt
  · exact mul_lt_mul_of_pos_right hb hpow
  · exact (div_lt_iff₀ hpow).mp hs

open scoped BigOperators
open Matrix Filter Topology

private theorem D_lower_eventually {d : ℕ} (hd : 1≤d) (a : ℝ) (ha : a<(delta d : ℝ)) :
    ∀ᶠ m : ℕ in atTop,a<(D d m (d+1) : ℝ)/(m : ℝ)^d := by
  obtain ⟨V,hV,hmax,hVdet,hcof⟩ := exists_maximizing_sign_simplex d
  have hnear : Tendsto (fun n : ℕ => (delta d : ℝ)*((n : ℝ)/(n+1))^d)
      atTop (𝓝 (delta d : ℝ)) := by
    simpa only [one_pow,mul_one] using
      ((tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).pow d).const_mul (delta d : ℝ)
  obtain ⟨n,hn2,han⟩ := ((eventually_ge_atTop (2 : ℕ)).and (hnear.eventually_const_lt ha)).exists
  let A := interiorSimplex V n
  let q := (n+1)*(d+1)
  have hq : 0<q := by dsimp [q]; positivity
  have hAdet : (augment A).det≠0 := interiorSimplex_nonsingular V hVdet n (by omega)
  obtain ⟨x,hxp,hx⟩ := interiorSimplex_positive_kernel V hVdet hcof n hn2
  have hratio : |((augment A).det : ℝ)|/(q : ℝ)^d =
      (delta d : ℝ)*((n : ℝ)/(n+1))^d := by
    have he : ((augment A).det : ℝ)=((n : ℝ)*(d+1))^d*((augment V).det : ℝ) := by
      exact_mod_cast interiorSimplex_det V n
    have hmaxR : |((augment V).det : ℝ)|=(delta d : ℝ) := by exact_mod_cast hmax
    rw [he,abs_mul,abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ)≤(n : ℝ)*(d+1)) _),hmaxR]
    simp only [q,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [mul_pow,div_pow,mul_pow]
    have hk : ((d : ℝ)+1)^d≠0 := pow_ne_zero _ (by positivity)
    field_simp
  apply D_lower_eventually_of_simplex hq A (interiorSimplex_bound V hV n) hAdet x hxp hx a
  rw [Int.cast_abs,hratio]
  exact han

theorem girard_plagne_box_limit (d : ℕ) (hd : 1≤d) :
    Tendsto (fun m : ℕ => (D d m (d+1) : ℝ)/(m : ℝ)^d) atTop (𝓝 (delta d : ℝ)) := by
  exact tendsto_order.mpr ⟨D_lower_eventually hd,D_upper_eventually hd⟩

theorem result : claim := by
  intro d hd
  exact ⟨fun m hm => ⟨lengths_nonempty d m hm,lengths_bddAbove d m (d+1)⟩,
    (delta d : ℝ),girard_plagne_box_limit d hd⟩

end D5.S3.Arith.Lattices.GirardPlagneBoxLimit
