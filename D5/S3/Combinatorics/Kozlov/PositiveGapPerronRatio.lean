/- GID: D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Kozlov/PositiveGapPerronRatio
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs]
   utility: none
   digest: The proper Kozlov transfer has strictly smaller Perron root than the lattice transfer at every positive gap for n at least four. -/

/-
positive_gap_perron_root_ratio
proof_shape: content
escape_witness: strict_counted_entry gives a strict count in row 1, column 3.
  The normalized lattice vector with one triple and only two pairs belongs to the
  lattice filter in this entry. Downward closure excludes it from the proper filter.
admission_basis: open-problem-resolution (#33426, Proved)
Direct frozen dependencies:
- D5/S3/Combinatorics/Kozlov/ProperModel (FVector, SnF, top, indeg and downward closure)
  sha256:93a1f926aa232bd11b51489167ac57fcc532305a4115419a30a24aa23b3e0d38
- D5/S3/Combinatorics/Kozlov/ChainedCount (properVectors, topState and the full skeletons)
  sha256:ebf764631fa95fdcc469ed64d9704179e1179076a7b92c16dafbbb7943c6bc60
- D5/S3/Combinatorics/Kozlov/ConvexHull (the normalized chain and the literal hull equality)
  sha256:4619f7ffafacff463a36eb6a3ae6170ddfb36a11ad87cd25e6414ee547303fac
- D5/S3/Combinatorics/Kozlov/LatticeCount (latticeVectors and skeleton membership)
  sha256:535a52d25de00a63dfb4bf27384657866c1bf1fbc666a93b4a950e837a7ebc9d
- D5/S3/Combinatorics/Kozlov/TransferCount (TG)
  sha256:fd8c0c3e38e39a151966a0b3d95ccbb6c288303fc32b5c52043728f19eb958e1
- D5/S3/Combinatorics/Graph/Pressure/WeightedWalks (Network.exists_perron and its eigenvector and complex-radius data)
  sha256:350d63251ff46e979a3ae8ca9c005ee248c618f91c2944e43d82fc4b2311692d
- Matrix.Irreducible.exists_pos_entry supplies the nonempty support of the network.
  It is a retained supplier declaration used alongside the graph Perron theorem.
-/

import D5.S3.Combinatorics.Kozlov.LatticeCount
import D5.S3.Combinatorics.Graph.Pressure.WeightedWalks
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

set_option autoImplicit false

open D5.S3.Combinatorics.Graph.Pressure
open scoped Matrix ENNReal

namespace D5.S3.Combinatorics.Kozlov

noncomputable section

/-- The predecessor's top degree must be less than the incoming first deficiency plus the gap. -/
def positiveGapCondition {n : ℕ} (δ : ℕ) (i : Fin n) (f : FVector n) : Prop :=
  i.val + 1 < indeg f + δ

instance {n : ℕ} (δ : ℕ) (i : Fin n) (f : FVector n) :
    Decidable (positiveGapCondition δ i f) :=
  inferInstanceAs (Decidable (_ < _ : Prop))

/-- The full proper transfer, with the left summand indexing degrees minus one and zero
and the right summand indexing degrees one through n. -/
def properPositiveGapTransfer (n δ : ℕ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℕ :=
  let degree : Fin 2 ⊕ Fin n → ℤ := Sum.elim (fun i => (i.val : ℤ) - 1)
    (fun i => (i.val : ℤ) + 1)
  Matrix.of fun i j =>
    ((properVectors n).filter
      (fun f => top f = degree j ∧ degree i < (indeg f : ℤ) + (δ : ℤ))).card

/-- The lattice transfer, whose top degrees run from one through n. -/
def latticePositiveGapTransfer (n δ : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j =>
    let hn : 1 ≤ n := by have := i.isLt; omega
    TG (latticeVectors hn) (topState hn) (positiveGapCondition δ) i j

/-- A normalized integer vector with a triple and only two pairs. -/
private def latticeHole (n : ℕ) : FVector n := fun j =>
  match j.val with
  | 0 => 1
  | 1 => n
  | 2 => 2
  | 3 => 1
  | _ => 0

private theorem latticeHole_vanish {n : ℕ} (j : Fin (n + 1)) (hj : 4 ≤ j.val) :
    latticeHole n j = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
  have hk' : j.val = k + 4 := hk.trans (Nat.add_comm 4 k)
  simp [latticeHole, hk']

private theorem choose_two_lower_bound {n : ℕ} (hn : 4 ≤ n) :
    6 ≤ n.choose 2 := by
  rw [show 6 = (4 : ℕ).choose 2 by decide]
  exact Nat.choose_le_choose 2 hn

private theorem latticeHole_normalized {n : ℕ} (hn : 4 ≤ n) :
    Normalized (show 1 ≤ n by omega) 1 (realVector (latticeHole n)) := by
  have hc₂ : (2 : ℝ) ≤ n.choose 2 := by
    exact_mod_cast (show 2 ≤ n.choose 2 from le_trans (by decide) (choose_two_lower_bound hn))
  have hc₂pos : (0 : ℝ) < n.choose 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hc₂
  have hc₃pos : (0 : ℝ) < n.choose 3 := by
    exact_mod_cast (Nat.choose_pos (by omega : 3 ≤ n))
  have cross : n.choose 2 ≤ 2 * n.choose 3 := by
    have hrec : n.choose 3 * 3 = n.choose 2 * (n - 2) :=
      Nat.choose_succ_right_eq n 2
    have hl := Nat.mul_le_mul_left (n.choose 2) (show 2 ≤ n - 2 by omega)
    omega
  have crossReal : (n.choose 2 : ℝ) ≤ 2 * (n.choose 3 : ℝ) := by exact_mod_cast cross
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨by simp [realVector, latticeHole], by simp [realVector, latticeHole, firstDegree], ?_,
    fun j => Nat.cast_nonneg (latticeHole n j)⟩
  rw [Fin.antitone_iff_succ_le]
  intro i
  simp only [realVector, cap, Fin.val_succ, Fin.val_castSucc]
  by_cases hi0 : i.val = 0
  · simp [latticeHole, hi0, hn0]
  by_cases hi1 : i.val = 1
  · simpa [latticeHole, hi1, hn0] using
      (div_le_iff₀ hc₂pos).2 (by simpa using hc₂)
  by_cases hi2 : i.val = 2
  · simpa [latticeHole, hi2] using
      (div_le_div_iff₀ hc₃pos hc₂pos).2 (by simpa using crossReal : (1 : ℝ) *
        (n.choose 2 : ℝ) ≤ 2 * (n.choose 3 : ℝ))
  have hz := latticeHole_vanish i.succ (by
    change 4 ≤ i.val + 1
    omega)
  rw [hz, Nat.cast_zero, zero_div]
  positivity

/-- Every complex with a three-element face already has at least three two-element faces. -/
private theorem latticeHole_not_proper {n : ℕ} (hn : 4 ≤ n) : latticeHole n ∉ properVectors n := by
  intro h
  obtain ⟨D, hD, hDvec⟩ := mem_properVectors.mp h
  have hDcomplex : IsComplex D := hD
  have htwo : fEntry D 2 = 2 := by
    simpa [fVector, latticeHole] using congrFun hDvec (⟨2, by omega⟩ : Fin (n + 1))
  have hthree : fEntry D 3 = 1 := by
    simpa [fVector, latticeHole] using congrFun hDvec (⟨3, by omega⟩ : Fin (n + 1))
  have hpos : 0 < (D.filter (fun s => s.card = 3)).card := by
    change 0 < fEntry D 3
    rw [hthree]
    decide
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  obtain ⟨htD, htcard⟩ := Finset.mem_filter.mp ht
  have hsub : t.powersetCard 2 ⊆ D.filter (fun s => s.card = 2) := by
    intro s hs
    obtain ⟨hst, hscard⟩ := Finset.mem_powersetCard.mp hs
    exact Finset.mem_filter.mpr ⟨hDcomplex.down htD hst, hscard⟩
  have hcard : (t.powersetCard 2).card ≤ fEntry D 2 := Finset.card_le_card hsub
  rw [Finset.card_powersetCard, htcard, htwo] at hcard
  norm_num at hcard

private theorem latticeHole_top {n : ℕ} (hn : 4 ≤ n) : top (latticeHole n) = 3 := by
  have hpos : 0 < latticeHole n ⟨3, by omega⟩ := by
    change 0 < 1
    decide
  have hge := le_top_of_pos hpos
  have hlt := top_lt_of_vanish (s := latticeHole n) latticeHole_vanish
  change (3 : ℤ) ≤ top (latticeHole n) at hge
  omega

private theorem latticeHole_indeg {n : ℕ} (hn : 4 ≤ n) : indeg (latticeHole n) = 2 := by
  have hdef : latticeHole n ⟨2, by omega⟩ < cap (⟨2, by omega⟩ : Fin (n + 1)) := by
    change 2 < n.choose 2
    exact lt_of_lt_of_le (by decide) (choose_two_lower_bound hn)
  have hle := indeg_le_of_lt_cap hdef
  have hfull : 1 < indeg (latticeHole n) := by
    apply (lt_indeg_iff (⟨1, by omega⟩ : Fin (n + 1))
      (normalized_one_bounded _ (latticeHole_normalized hn))).2
    intro j hj
    have hval : j.val ≤ 1 := hj
    have hc : j.val = 0 ∨ j.val = 1 := by omega
    rcases hc with h | h <;> simp [latticeHole, cap, h]
  change indeg (latticeHole n) ≤ 2 at hle
  omega

private theorem proper_subset_lattice {n : ℕ} (hn : 1 ≤ n) :
    properVectors n ⊆ latticeVectors hn := by
  intro f hf
  apply (mem_latticeVectors hn).2
  apply (lymChain_iff_normalized hn).1
  rw [← hull_eq_lymChain hn]
  exact subset_convexHull ℝ _ ⟨f, mem_properVectors.mp hf, rfl⟩

private theorem strict_counted_entry {n δ : ℕ} (hn : 4 ≤ n) (hδ : 1 ≤ δ) :
    let hn' : 1 ≤ n := by omega
    let row : Fin n := ⟨0, by omega⟩
    let col : Fin n := ⟨2, by omega⟩
    TG (properVectors n) (topState hn') (positiveGapCondition δ) row col <
      TG (latticeVectors hn') (topState hn') (positiveGapCondition δ) row col := by
  dsimp only
  let hn' : 1 ≤ n := by omega
  let row : Fin n := ⟨0, by omega⟩
  let col : Fin n := ⟨2, by omega⟩
  change TG (properVectors n) (topState hn') (positiveGapCondition δ) row col <
    TG (latticeVectors hn') (topState hn') (positiveGapCondition δ) row col
  simp only [TG, Matrix.of_apply]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset_filter _ (proper_subset_lattice hn'), ?_⟩
  intro heq
  have hstate : topState hn' (latticeHole n) = col := by
    have hv := topState_val hn' (normalized_one_fixed hn' (latticeHole_normalized hn))
    rw [latticeHole_top hn] at hv
    apply Fin.ext
    change (topState hn' (latticeHole n)).val = 2
    omega
  have hgap : positiveGapCondition δ row (latticeHole n) := by
    change 1 < indeg (latticeHole n) + δ
    rw [latticeHole_indeg hn]
    omega
  have hm : latticeHole n ∈ (latticeVectors hn').filter
      (fun f => topState hn' f = col ∧ positiveGapCondition δ row f) :=
    Finset.mem_filter.mpr ⟨(mem_latticeVectors _).2 (latticeHole_normalized hn), hstate, hgap⟩
  rw [← heq] at hm
  exact latticeHole_not_proper hn (Finset.mem_filter.mp hm).1

private theorem counted_irreducible {n δ : ℕ} (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (X : Finset (FVector n))
    (hs : ∀ k : Fin n, skeleton n (k.val + 1) ∈ X) :
    ((TG X (topState hn) (positiveGapCondition δ)).map
      (fun k : ℕ => (k : ℝ))).IsIrreducible := by
  let M := (TG X (topState hn) (positiveGapCondition δ)).map (fun k : ℕ => (k : ℝ))
  let : Quiver (Fin n) := Matrix.toQuiver M
  have edge (i j : Fin n) (hij : i.val ≤ j.val + 1) : i ⟶ j := by
    apply PLift.up
    change (0 : ℝ) < ((TG X (topState hn) (positiveGapCondition δ)) i j : ℝ)
    apply Nat.cast_pos.mpr
    change 0 < (X.filter _).card
    apply Finset.card_pos.mpr
    refine ⟨skeleton n (j.val + 1), Finset.mem_filter.mpr ⟨hs j, ?_, ?_⟩⟩
    · have ht := top_skeleton (⟨j.val + 1, by omega⟩ : Fin (n + 1))
      apply Fin.ext
      change (top (skeleton n (j.val + 1))).toNat - 1 = j.val
      rw [ht]
      simp
    · have hfull := skeleton_mem_SnF (n := n) (k := j.val + 1) (by omega)
      have hdeg : j.val + 1 < indeg (skeleton n (j.val + 1)) := by
        apply (lt_indeg_iff (⟨j.val + 1, by omega⟩ : Fin (n + 1)) (SnF_bounded hfull)).2
        intro k hk
        change k.val ≤ j.val + 1 at hk
        simp [skeleton, hk]
      change i.val + 1 < indeg (skeleton n (j.val + 1)) + δ
      omega
  have reach (k : ℕ) (i j : Fin n) (hi : i.val = k) : Nonempty (Quiver.Path i j) := by
    induction k using Nat.strong_induction_on generalizing i with
    | h k ih =>
      by_cases hij : i.val ≤ j.val + 1
      · exact ⟨(edge i j hij).toPath⟩
      · let prev : Fin n := ⟨i.val - 1, by omega⟩
        obtain ⟨p⟩ := ih prev.val (by dsimp [prev]; omega) prev rfl
        exact ⟨(edge i prev (by dsimp [prev]; omega)).toPath.comp p⟩
  have connected : Quiver.IsStronglyConnected (Fin n) := fun i j => reach i.val i j rfl
  let first : Fin n := ⟨0, hn⟩
  exact ⟨fun i j => Nat.cast_nonneg _, connected.isSStronglyConnected_of_hom
    (edge first first (by omega))⟩

private theorem proper_radius_eq_block {n δ : ℕ} (hn : 1 ≤ n) :
    spectralRadius ℂ ((properPositiveGapTransfer n δ).map (fun k : ℕ => (k : ℂ))) =
      spectralRadius ℂ ((TG (properVectors n) (topState hn) (positiveGapCondition δ)).map
        (fun k : ℕ => (k : ℂ))) := by
  let F := (properPositiveGapTransfer n δ).map (fun k : ℕ => (k : ℂ))
  let A := (TG (properVectors n) (topState hn) (positiveGapCondition δ)).map
    (fun k : ℕ => (k : ℂ))
  let C : Matrix (Fin 2) (Fin n) ℂ := Matrix.of fun i j => F (Sum.inl i) (Sum.inr j)
  have hzero (i : Fin 2 ⊕ Fin n) (j : Fin 2) : F i (Sum.inl j) = 0 := by
    have hfilter : (properVectors n).filter (fun f => top f = (j.val : ℤ) - 1 ∧
        Sum.elim (fun i : Fin 2 => (i.val : ℤ) - 1) (fun i : Fin n => (i.val : ℤ) + 1) i <
          (indeg f : ℤ) + (δ : ℤ)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro f hf
      obtain ⟨hf, ht, _⟩ := Finset.mem_filter.mp hf
      have hv := topState_val hn (SnF_fixed hn (mem_properVectors.mp hf))
      omega
    change (↑((properVectors n).filter (fun f => top f = (j.val : ℤ) - 1 ∧
      Sum.elim (fun i : Fin 2 => (i.val : ℤ) - 1) (fun i : Fin n => (i.val : ℤ) + 1) i <
        (indeg f : ℤ) + (δ : ℤ))).card : ℂ) = 0
    rw [hfilter]
    simp
  have hblock : F = Matrix.fromBlocks 0 C 0 A := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simpa using hzero (Sum.inl i) j
    · rfl
    · simpa using hzero (Sum.inr i) j
    · change (↑((properVectors n).filter _).card : ℂ) = ↑((properVectors n).filter _).card
      congr 2
      apply Finset.filter_congr
      intro f hf
      have hv := topState_val hn (SnF_fixed hn (mem_properVectors.mp hf))
      change (top f = (j.val : ℤ) + 1 ∧ (i.val : ℤ) + 1 < (indeg f : ℤ) + (δ : ℤ)) ↔
        (topState hn f = j ∧ i.val + 1 < indeg f + δ)
      have ht : top f = (j.val : ℤ) + 1 ↔ topState hn f = j := by
        rw [← hv, ← Fin.val_inj]
        omega
      rw [ht]
      omega
  have hchar : F.charpoly = Polynomial.X ^ 2 * A.charpoly := by
    rw [hblock, Matrix.charpoly_fromBlocks_zero₂₁, Matrix.charpoly_zero, Fintype.card_fin]
  have hspec (z : ℂ) : z ∈ spectrum ℂ F ↔ z = 0 ∨ z ∈ spectrum ℂ A := by
    simp [Matrix.mem_spectrum_iff_isRoot_charpoly, hchar, Polynomial.IsRoot, mul_eq_zero]
  change spectralRadius ℂ F = spectralRadius ℂ A
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital]
  apply le_antisymm
  · refine iSup₂_le fun z hz => ?_
    rcases (hspec z).1 hz with rfl | hz
    · simp
    · exact le_iSup₂_of_le z hz le_rfl
  · refine iSup₂_le fun z hz => ?_
    exact le_iSup₂_of_le z ((hspec z).2 (Or.inr hz)) le_rfl

/-- Snellman's positive-gap Perron-root inequality on the full proper and lattice transfers. -/
theorem positive_gap_perron_root_ratio (n δ : ℕ) (hn : 4 ≤ n) (hδ : 1 ≤ δ) :
    let P := properPositiveGapTransfer n δ
    let L := latticePositiveGapTransfer n δ
    let ρP := spectralRadius ℂ (P.map (fun k : ℕ => (k : ℂ)))
    let ρL := spectralRadius ℂ (L.map (fun k : ℕ => (k : ℂ)))
    0 < ρP ∧ 0 < ρL ∧ ρP < ρL ∧ 0 < ρL.toReal ∧ ρP.toReal / ρL.toReal < 1 := by
  let hp : 1 ≤ n := by omega
  let P := TG (properVectors n) (topState hp) (positiveGapCondition δ)
  let L := TG (latticeVectors hp) (topState hp) (positiveGapCondition δ)
  let A := P.map (fun k : ℕ => (k : ℝ))
  let B := L.map (fun k : ℕ => (k : ℝ))
  have hA : A.IsIrreducible := counted_irreducible hp hδ _
    (fun j => mem_properVectors.mpr (skeleton_mem_SnF (by omega : 1 ≤ j.val + 1)))
  have hB : B.IsIrreducible := counted_irreducible hp hδ _
    (fun j => skeleton_mem_latticeVectors hp (by omega : 1 ≤ j.val + 1))
  have : Nonempty (Fin n) := ⟨⟨0, hp⟩⟩
  classical
  -- The positive-count support at inverse temperature one realizes the real matrix.
  have perron (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsIrreducible) :
      ∃ (r : ℝ) (v : Fin n → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M *ᵥ v = r • v ∧
        spectralRadius ℂ (M.map (algebraMap ℝ ℂ)) = ENNReal.ofReal r := by
    let G : Network (Fin n) :=
      { edge := fun i j => 0 < M i j
        connected := by
          let : Quiver (Fin n) := Matrix.toQuiver M
          exact hM.connected.isStronglyConnected
        hasEdge := Matrix.Irreducible.exists_pos_entry hM }
    let c : Fin n → Fin n → ℝ := fun i j => -Real.log (M i j)
    have hw : G.W c 1 = M := by
      ext i j
      by_cases h : 0 < M i j
      · simp [Network.W, G, c, h, Real.exp_log h]
      · have hz : M i j = 0 := le_antisymm (le_of_not_gt h) (hM.nonneg i j)
        simp [Network.W, G, hz]
    obtain ⟨p⟩ := G.exists_perron c 1
    exact ⟨p.root, p.right, p.root_pos, p.right_pos, hw ▸ p.eigen, hw ▸ p.radius⟩
  obtain ⟨α, v, hα, hv, hav, har⟩ := perron A hA
  obtain ⟨β, u, hβ, hu, hbu, hbr⟩ := perron Bᵀ hB.transpose
  have hbRadius : spectralRadius ℂ (B.map (algebraMap ℝ ℂ)) = ENNReal.ofReal β := by
    rw [← hbr, Matrix.transpose_map, spectralRadius_eq_of_unital, spectralRadius_eq_of_unital,
      Matrix.spectrum_transpose]
  -- Every counted proper vector is counted on the lattice side in the same entry.
  have hle (i j : Fin n) : A i j ≤ B i j := by
    apply Nat.cast_le.mpr
    exact Finset.card_le_card (Finset.filter_subset_filter _ (proper_subset_lattice hp))
  let row : Fin n := ⟨0, by omega⟩
  let col : Fin n := ⟨2, by omega⟩
  have hlt : A row col < B row col := Nat.cast_lt.mpr (strict_counted_entry hn hδ)
  have hs (i j : Fin n) : 0 ≤ (B - A) i j * v j :=
    mul_nonneg (sub_nonneg.mpr (hle i j)) (hv j).le
  have hsum : 0 < u ⬝ᵥ ((B - A) *ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec]
    apply Finset.sum_pos' (fun i _ => mul_nonneg (hu i).le (Finset.sum_nonneg (fun j _ => hs i j)))
    refine ⟨row, Finset.mem_univ _, mul_pos (hu row) ?_⟩
    exact Finset.sum_pos' (fun j _ => hs row j)
      ⟨col, Finset.mem_univ _, mul_pos (sub_pos.mpr hlt) (hv col)⟩
  rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.dotProduct_transpose_mulVec,
    hbu, hav, dotProduct_smul, dotProduct_smul, dotProduct_comm v u] at hsum
  have huv : 0 < u ⬝ᵥ v := by
    exact Finset.sum_pos' (fun i _ => (mul_pos (hu i) (hv i)).le)
      ⟨row, Finset.mem_univ _, mul_pos (hu row) (hv row)⟩
  have hab : α < β := by
    apply lt_of_mul_lt_mul_right _ huv.le
    exact sub_pos.mp hsum
  have cast_counts (N : Matrix (Fin n) (Fin n) ℕ) :
      (N.map (fun k : ℕ => (k : ℝ))).map (algebraMap ℝ ℂ) =
        N.map (fun k : ℕ => (k : ℂ)) := by
    ext i j
    simp
  rw [show A.map (algebraMap ℝ ℂ) = P.map (fun k : ℕ => (k : ℂ)) from cast_counts P] at har
  rw [show B.map (algebraMap ℝ ℂ) = L.map (fun k : ℕ => (k : ℂ)) from cast_counts L] at hbRadius
  change 0 < spectralRadius ℂ ((properPositiveGapTransfer n δ).map _) ∧
    0 < spectralRadius ℂ (L.map _) ∧
    spectralRadius ℂ ((properPositiveGapTransfer n δ).map _) < spectralRadius ℂ (L.map _) ∧
    0 < (spectralRadius ℂ (L.map _)).toReal ∧
    (spectralRadius ℂ ((properPositiveGapTransfer n δ).map _)).toReal /
      (spectralRadius ℂ (L.map _)).toReal < 1
  rw [proper_radius_eq_block hp, har, hbRadius]
  rw [ENNReal.toReal_ofReal hα.le, ENNReal.toReal_ofReal hβ.le]
  exact ⟨ENNReal.ofReal_pos.mpr hα, ENNReal.ofReal_pos.mpr hβ,
    (ENNReal.ofReal_lt_ofReal_iff hβ).2 hab, hβ, (div_lt_one hβ).2 hab⟩

end

end D5.S3.Combinatorics.Kozlov
