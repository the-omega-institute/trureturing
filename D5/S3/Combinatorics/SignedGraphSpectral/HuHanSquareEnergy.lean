/- GID: D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy
   generality: E
   mirror-B: D5/B/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.HermitianFunctionalCalculus, mathlib/module/Mathlib.Analysis.InnerProductSpace.GramMatrix]
   utility: none
   digest: Both endpoint equalities for signed positive square energy distinguish trees and switchings of uniformly signed complete graphs. -/

import D5.S3.Combinatorics.SignedGraphSpectral.MO479815
import D5.S3.Combinatorics.SignedGraphSpectral.NormalizedCliqueBlocks
import D5.S3.Weil.ZetaLinear.HermitianPosPart
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
Both clauses of Hu–Han Problem 6.1, arXiv:2608.18492v1, preregistered in #33287.
The statement classifies equality at the two extremal values of positive square energy.
Hu–Han provide the conservation identity and the sharp bounds. The matrix
decomposition follows Hu–Liu–Wang, arXiv:2608.17329v1, Proposition 4.3.
The signed classification uses the zero-sum extensions and the commutation of
the signed adjacency with its positive part to exclude attached clique blocks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy

/-! ### Spectral conservation under reversal of all signs -/

section

open Matrix Finset RHLinalg
open scoped BigOperators

open D5.S3.Combinatorics.SignedGraphSpectral.MO479815 (signedAdj signed_hermitian)

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The sum of squares of all positive eigenvalue occurrences. -/
def sPlus (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) : ℝ :=
  ∑ i : Fin n, if 0 < (signed_hermitian G σ).eigenvalues i
    then ((signed_hermitian G σ).eigenvalues i) ^ 2 else 0

private theorem signedAdj_complement (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    signedAdj G (fun e => !(σ e)) = -signedAdj G σ := by
  ext i j
  by_cases hij : G.Adj i j
  · cases hs : σ s(i,j) <;> simp [signedAdj, hij, hs]
  · simp [signedAdj, hij]

private lemma sPlus_trace_cfc (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    sPlus G σ = trace (cfc (fun x : ℝ => (x⁺) ^ 2) (signedAdj G σ)) := by
  have hA := signed_hermitian G σ
  rw [hA.cfc_eq]
  change sPlus G σ = trace (specMap hA (fun x : ℝ => (x⁺) ^ 2))
  rw [show trace (specMap hA (fun x : ℝ => (x⁺) ^ 2)) =
      ∑ i, ((hA.eigenvalues i)⁺) ^ 2 by
    simpa only [rtrace, RCLike.re_to_real] using rtrace_specMap hA (fun x => (x⁺) ^ 2)]
  apply sum_congr rfl
  intro i _
  by_cases hi : 0 < hA.eigenvalues i
  · simp [hi, posPart_eq_self.mpr hi.le]
  · simp [hi, posPart_eq_zero.mpr (le_of_not_gt hi)]

private lemma trace_signedAdj_sq (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    trace (signedAdj G σ * signedAdj G σ) = 2 * (G.edgeFinset.card : ℝ) := by
  have hdiag (i : Fin n) :
      (signedAdj G σ * signedAdj G σ) i i = (G.adjMatrix ℝ * G.adjMatrix ℝ) i i := by
    simp only [Matrix.mul_apply]
    apply sum_congr rfl
    intro j _
    by_cases hij : G.Adj i j
    · have hji := hij.symm
      cases hs : σ s(i,j) <;>
        simp [signedAdj, SimpleGraph.adjMatrix, hij, hji, ← Sym2.eq_swap (a := i), hs]
    · have hji : ¬ G.Adj j i := fun h => hij h.symm
      simp [signedAdj, SimpleGraph.adjMatrix, hij, hji]
  simp only [trace, diag_apply, hdiag, G.adjMatrix_mul_self_apply_self]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

/-- Hu–Han's conservation identity, including empty and disconnected graphs. -/
private theorem sPlus_add_complement (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    sPlus G σ + sPlus G (fun e => !(σ e)) = 2 * (G.edgeFinset.card : ℝ) := by
  have hA := signed_hermitian G σ
  rw [sPlus_trace_cfc, sPlus_trace_cfc, signedAdj_complement,
    ← cfc_comp_neg (hf := by fun_prop) (ha := hA.isSelfAdjoint)]
  rw [hA.cfc_eq, hA.cfc_eq]
  change trace (specMap hA (fun x : ℝ => (x⁺) ^ 2)) +
    trace (specMap hA (fun x : ℝ => ((-x)⁺) ^ 2)) = _
  have htrace (f : ℝ → ℝ) : trace (specMap hA f) = ∑ i, f (hA.eigenvalues i) := by
    simpa only [rtrace, RCLike.re_to_real] using rtrace_specMap hA f
  have hsquare : signedAdj G σ * signedAdj G σ = specMap hA (id * id) := by
    rw [specMap_mul, specMap_id]
  rw [htrace, htrace, ← sum_add_distrib, ← trace_signedAdj_sq G σ, hsquare, htrace]
  apply sum_congr rfl
  intro i _
  change ((hA.eigenvalues i)⁺) ^ 2 + ((-hA.eigenvalues i)⁺) ^ 2 =
    hA.eigenvalues i * hA.eigenvalues i
  rcases le_total 0 (hA.eigenvalues i) with hi | hi
  · simp [posPart_eq_self.mpr hi, posPart_eq_zero.mpr (neg_nonpos.mpr hi), pow_two]
  · simp [posPart_eq_zero.mpr hi, posPart_eq_self.mpr (neg_nonneg.mpr hi), pow_two]

end

/-! ### Signed spectral equality and attainment -/

open DNN (blockWeight)

section

open Matrix Finset RHLinalg
open scoped Matrix BigOperators

open D5.S3.Combinatorics.SignedGraphSpectral.MO479815 (signedAdj signed_hermitian)

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

private abbrev positivePart (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  hermPosPart (signed_hermitian G σ)

def endpoint (G : SimpleGraph (Fin n)) : ℝ :=
  2 * (G.edgeFinset.card : ℝ) - (n : ℝ) + 1

private def indicator (B : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ B then 1 else 0

private def difference (u v : Fin n) : Fin n → ℝ :=
  Pi.single u 1 - Pi.single v 1

/-- One term per unordered off-diagonal nonedge, indexed by its increasing pair. -/
private def nonedges (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) :=
  univ.filter fun p => p.1 < p.2 ∧ ¬ G.Adj p.1 p.2

private def foldNonedges (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  X ⊙ X + ∑ p ∈ nonedges G, (X p.1 p.2) ^ 2 •
    vecMulVec (difference p.1 p.2) (difference p.1 p.2)

/-- The normalized block conclusion, supplied as a premise for the signed rigidity step.
The graph-theoretic fields give complete blocks and an exact edge partition. -/
private structure NormalizedBlocks (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ)
    (blocks : Finset (Finset (Fin n))) : Prop where
  size : ∀ B ∈ blocks, 2 ≤ B.card
  clique : ∀ B ∈ blocks, G.IsClique (B : Set (Fin n))
  edge : ∀ u v, G.Adj u v → ∃! B, B ∈ blocks ∧ u ∈ B ∧ v ∈ B
  fold_eq : foldNonedges G X =
    ∑ B ∈ blocks, (blockWeight B) ^ 2 • vecMulVec (indicator B) (indicator B)

private def quadratic (M : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : ℝ :=
  h ⬝ᵥ (M *ᵥ h)

private lemma quadratic_add (M N : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    quadratic (M + N) h = quadratic M h + quadratic N h := by
  simp only [quadratic, add_mulVec, dotProduct_add]

private lemma quadratic_sum {α : Type*} (s : Finset α)
    (M : α → Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    quadratic (∑ a ∈ s, M a) h = ∑ a ∈ s, quadratic (M a) h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadratic]
  | insert a s ha ih => simp only [sum_insert ha, quadratic_add, ih]

private lemma quadratic_rankOne (c : ℝ) (d h : Fin n → ℝ) :
    quadratic (c • vecMulVec d d) h = c * (h ⬝ᵥ d) ^ 2 := by
  simp only [quadratic, smul_mulVec, dotProduct_smul, vecMulVec_mulVec,
    op_smul_eq_smul, smul_eq_mul, ← dotProduct_comm h d, pow_two]

private lemma dot_indicator (B : Finset (Fin n)) (h : Fin n → ℝ) :
    h ⬝ᵥ indicator B = ∑ i ∈ B, h i := by
  simp [dotProduct, indicator]

private lemma dot_difference (u v : Fin n) (h : Fin n → ℝ) :
    h ⬝ᵥ difference u v = h u - h v := by
  simp [difference, dotProduct_sub]

private lemma fold_quadratic (G : SimpleGraph (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) :
    quadratic (foldNonedges G X) h =
      quadratic (X ⊙ X) h + ∑ p ∈ nonedges G, (X p.1 p.2) ^ 2 * (h p.1 - h p.2) ^ 2 := by
  simp only [foldNonedges, quadratic_add, quadratic_sum, quadratic_rankOne, dot_difference]

private lemma NormalizedBlocks.quadratic_eq {G : SimpleGraph (Fin n)}
    {X : Matrix (Fin n) (Fin n) ℝ} {blocks : Finset (Finset (Fin n))}
    (D : NormalizedBlocks G X blocks) (h : Fin n → ℝ) :
    quadratic (foldNonedges G X) h =
      ∑ B ∈ blocks, (blockWeight B) ^ 2 * (∑ i ∈ B, h i) ^ 2 := by
  rw [D.fold_eq]
  simp only [quadratic_sum, quadratic_rankOne, dot_indicator]

/-- A blockwise zero-sum vector that distinguishes two nonadjacent vertices forces
their entry of the actual signed positive part to vanish. -/
private theorem nonedge_zero_of_blockwise_zero_sum (G : SimpleGraph (Fin n))
    (σ : Sym2 (Fin n) → Bool) {blocks : Finset (Finset (Fin n))}
    (D : NormalizedBlocks G (positivePart G σ) blocks)
    (h : Fin n → ℝ) (hZero : ∀ B ∈ blocks, ∑ i ∈ B, h i = 0)
    {u v : Fin n} (hn : ¬ G.Adj u v) (hSep : h u ≠ h v) :
    positivePart G σ u v = 0 := by
  let X := positivePart G σ
  have hPSD : X.PosSemidef := hermPosPart_posSemidef _
  have hm : 0 ≤ quadratic (X ⊙ X) h := by
    simpa [quadratic] using (hPSD.hadamard hPSD).dotProduct_mulVec_nonneg h
  have hFold : quadratic (foldNonedges G X) h = 0 := by
    rw [D.quadratic_eq h]
    exact sum_eq_zero fun B hB => by simp [hZero B hB]
  rw [fold_quadratic] at hFold
  have hNonneg (p : Fin n × Fin n) (_ : p ∈ nonedges G) :
      0 ≤ (X p.1 p.2) ^ 2 * (h p.1 - h p.2) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hSum : (∑ p ∈ nonedges G, (X p.1 p.2) ^ 2 * (h p.1 - h p.2) ^ 2) = 0 := by
    have := sum_nonneg hNonneg
    linarith
  have hEntry {i j : Fin n} (hij : i < j) (ha : ¬ G.Adj i j) (hd : h i ≠ h j) :
      X i j = 0 := by
    have hp : (i,j) ∈ nonedges G := by simp [nonedges, hij, ha]
    have hz := (sum_eq_zero_iff_of_nonneg hNonneg).mp hSum (i,j) hp
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ (sub_ne_zero.mpr hd)))
  rcases lt_trichotomy u v with huv | huv | huv
  · exact hEntry huv hn hSep
  · exact (hSep (congrArg h huv)).elim
  · change X u v = 0
    rw [← hPSD.isHermitian.isSymm.apply u v]
    exact hEntry huv (fun ha => hn ha.symm) hSep.symm

private lemma weight_pos {B : Finset (Fin n)} (hB : 2 ≤ B.card) :
    0 < blockWeight B := by
  have h : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
  exact div_pos (by linarith) (by linarith)

private lemma weight_lt_one {B : Finset (Fin n)} (hB : 2 ≤ B.card) :
    blockWeight B < 1 := by
  have h : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
  unfold blockWeight
  rw [div_lt_iff₀ (by linarith : 0 < (B.card : ℝ)), one_mul]
  linarith

private lemma fold_on_edge {G : SimpleGraph (Fin n)} (X : Matrix (Fin n) (Fin n) ℝ)
    {u v : Fin n} (huv : G.Adj u v) : foldNonedges G X u v = (X u v) ^ 2 := by
  simp only [foldNonedges, Matrix.add_apply, Matrix.sum_apply, hadamard_apply, pow_two]
  suffices (∑ p ∈ nonedges G,
      (((X p.1 p.2) * (X p.1 p.2)) •
        vecMulVec (difference p.1 p.2) (difference p.1 p.2)) u v) = 0 by
    rw [this, add_zero]
  apply sum_eq_zero
  intro p hp
  have hab : ¬ G.Adj p.1 p.2 := ((mem_filter.mp hp).2).2
  by_cases hu : u = p.1 ∨ u = p.2
  · have hv : v ≠ p.1 ∧ v ≠ p.2 := by
      rcases hu with rfl | rfl
      · exact ⟨Ne.symm huv.ne, fun h => hab (h ▸ huv)⟩
      · exact ⟨fun h => hab (h ▸ huv.symm), Ne.symm huv.ne⟩
    simp [difference, vecMulVec_apply, Pi.single_apply, Ne.symm hv.1, Ne.symm hv.2]
  · push Not at hu
    simp [difference, vecMulVec_apply, Pi.single_apply, Ne.symm hu.1, Ne.symm hu.2]

private lemma correction_offdiag_of_lt {G : SimpleGraph (Fin n)}
    (X : Matrix (Fin n) (Fin n) ℝ) {u v : Fin n} (huv : u < v)
    {p : Fin n × Fin n} (hp : p ∈ nonedges G) :
    (((X p.1 p.2) ^ 2) • vecMulVec (difference p.1 p.2) (difference p.1 p.2)) u v =
      if p = (u,v) then -(X u v) ^ 2 else 0 := by
  have hpLt : p.1 < p.2 := ((mem_filter.mp hp).2).1
  by_cases hu : u = p.1
  · by_cases hv : v = p.2
    · have hPair : p = (u,v) := Prod.ext hu.symm hv.symm
      subst p
      simp [difference, vecMulVec_apply, huv.ne, huv.ne.symm]
    · have hv' : v ≠ p.1 := fun e => huv.ne (hu.trans e.symm)
      have hPair : p ≠ (u,v) := fun e => hv (congrArg Prod.snd e).symm
      simp [difference, vecMulVec_apply, hv, hv', hPair]
  · have hPair : p ≠ (u,v) := fun e => hu (congrArg Prod.fst e).symm
    by_cases hu' : u = p.2
    · have hv : v ≠ p.1 := by
        intro e
        exact lt_asymm hpLt (hu' ▸ e ▸ huv)
      have hv' : v ≠ p.2 := fun e => huv.ne (hu'.trans e.symm)
      simp [difference, vecMulVec_apply, hv, hv', hPair]
    · simp [difference, vecMulVec_apply, hu, hu', hPair]

private lemma fold_posSemidef (G : SimpleGraph (Fin n)) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) : (foldNonedges G X).PosSemidef := by
  apply (hX.hadamard hX).add
  apply Matrix.posSemidef_sum
  intro p _
  have hp : (vecMulVec (difference p.1 p.2) (difference p.1 p.2)).PosSemidef := by
    simpa using (Matrix.posSemidef_vecMulVec_self_star (difference p.1 p.2))
  exact hp.smul (sq_nonneg _)

private lemma fold_nonedge_zero {G : SimpleGraph (Fin n)} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) {u v : Fin n} (huv : u ≠ v) (ha : ¬ G.Adj u v) :
    foldNonedges G X u v = 0 := by
  have hOrdered (i j : Fin n) (hij : i < j) (hn : ¬ G.Adj i j) :
      foldNonedges G X i j = 0 := by
    have hp : (i,j) ∈ nonedges G := by simp [nonedges, hij, hn]
    simp only [foldNonedges, Matrix.add_apply, Matrix.sum_apply, hadamard_apply]
    have hsum := sum_congr (s₁ := nonedges G) rfl
      (fun p hp => correction_offdiag_of_lt X hij hp)
    rw [hsum, sum_eq_single_of_mem (i,j) hp (fun p _ hne => ite_eq_right hne), ite_eq_left rfl]
    ring
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact hOrdered u v hlt ha
  · rw [← (fold_posSemidef G hX).isHermitian.isSymm.apply u v]
    exact hOrdered v u hgt (fun h => ha h.symm)

/-- The actual graph fold of a PSD matrix is supported DNN, the input to the Gram cut split. -/
private theorem foldNonedges_supportedDNN (G : SimpleGraph (Fin n))
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) :
    Gram.SupportedDNN G (foldNonedges G X) := by
  refine ⟨fold_posSemidef G hX, fun u v => ?_, fun huv ha => fold_nonedge_zero hX huv ha⟩
  rcases eq_or_ne u v with rfl | huv
  · exact (fold_posSemidef G hX).diag_nonneg
  · by_cases ha : G.Adj u v
    · rw [fold_on_edge X ha]
      exact sq_nonneg _
    · rw [fold_nonedge_zero hX huv ha]

private lemma abs_entry_of_block_edge {G : SimpleGraph (Fin n)}
    {X : Matrix (Fin n) (Fin n) ℝ} {blocks : Finset (Finset (Fin n))}
    (D : NormalizedBlocks G X blocks) {B : Finset (Fin n)} (hB : B ∈ blocks)
    {u v : Fin n} (huv : G.Adj u v) (hu : u ∈ B) (hv : v ∈ B) :
    |X u v| = blockWeight B := by
  obtain ⟨C, _, hUnique⟩ := D.edge u v huv
  have hUniqueB (J : Finset (Fin n)) (hJ : J ∈ blocks) (hJu : u ∈ J) (hJv : v ∈ J) :
      J = B := (hUnique J ⟨hJ, hJu, hJv⟩).trans (hUnique B ⟨hB, hu, hv⟩).symm
  have hEq := congrFun (congrFun D.fold_eq u) v
  rw [fold_on_edge X huv] at hEq
  simp only [Matrix.sum_apply] at hEq
  rw [sum_eq_single_of_mem B hB (fun J hJ hne => by
    by_cases hJu : u ∈ J
    · have hJv : v ∉ J := fun h => hne (hUniqueB J hJ hJu h)
      simp [vecMulVec_apply, indicator, hJv]
    · simp [vecMulVec_apply, indicator, hJu])] at hEq
  simp [vecMulVec_apply, indicator, hu, hv] at hEq
  exact ((sq_eq_sq_iff_abs_eq_abs _ _).mp hEq).trans (abs_of_pos (weight_pos (D.size B hB)))

private lemma sum_adj_blockWeight {G : SimpleGraph (Fin n)}
    {B : Finset (Fin n)} (hB : G.IsClique (B : Set (Fin n))) (hSize : 2 ≤ B.card) :
    (∑ u : Fin n, ∑ v : Fin n,
        if G.Adj u v ∧ u ∈ B ∧ v ∈ B then blockWeight B else 0) =
      (blockWeight B) ^ 2 * (∑ _i ∈ B, (1 : ℝ)) ^ 2 := by
  have hcount (u : Fin n) :
      (∑ v : Fin n, if G.Adj u v ∧ u ∈ B ∧ v ∈ B then blockWeight B else 0) =
        if u ∈ B then (((B.card : ℝ) - 1) * blockWeight B) else 0 := by
    by_cases hu : u ∈ B
    · have hfilter : (univ : Finset (Fin n)).filter (fun v => G.Adj u v ∧ u ∈ B ∧ v ∈ B)
          = B.erase u := by
        ext v
        simp only [mem_filter, mem_univ, true_and, mem_erase, hu]
        exact ⟨fun h => ⟨h.1.ne.symm, h.2⟩, fun h => ⟨hB hu h.2 h.1.symm, h.2⟩⟩
      rw [← sum_filter, hfilter, ite_eq_left hu, sum_const, nsmul_eq_mul, card_erase_of_mem hu,
        Nat.cast_sub (by omega : 1 ≤ B.card), Nat.cast_one]
    · simp [hu]
  have hcard : (0 : ℝ) < B.card := by exact_mod_cast (show 0 < B.card by omega)
  simp_rw [hcount]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  simp only [sum_const, nsmul_eq_mul, mul_one, blockWeight]
  field_simp

private lemma abs_sum_eq_fold_mass {G : SimpleGraph (Fin n)}
    {X : Matrix (Fin n) (Fin n) ℝ} {blocks : Finset (Finset (Fin n))}
    (D : NormalizedBlocks G X blocks) :
    (∑ u : Fin n, ∑ v : Fin n, if G.Adj u v then |X u v| else 0) =
      quadratic (foldNonedges G X) (fun _ => 1) := by
  have hTerm (u v : Fin n) :
      (if G.Adj u v then |X u v| else 0) =
        ∑ B ∈ blocks, if G.Adj u v ∧ u ∈ B ∧ v ∈ B then blockWeight B else 0 := by
    by_cases ha : G.Adj u v
    · obtain ⟨B, ⟨hB, hu, hv⟩, hUnique⟩ := D.edge u v ha
      rw [sum_eq_single_of_mem B hB (fun C hC hne => by
        rw [ite_eq_right (fun hc => hne (hUnique C ⟨hC, hc.2.1, hc.2.2⟩))])]
      simpa [ha, hu, hv] using abs_entry_of_block_edge D hB ha hu hv
    · simp [ha]
  simp_rw [hTerm]
  rw [D.quadratic_eq]
  calc
    _ = ∑ u : Fin n, ∑ B ∈ blocks, ∑ v : Fin n,
        if G.Adj u v ∧ u ∈ B ∧ v ∈ B then blockWeight B else 0 := by
      exact sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ B ∈ blocks, ∑ u : Fin n, ∑ v : Fin n,
        if G.Adj u v ∧ u ∈ B ∧ v ∈ B then blockWeight B else 0 := Finset.sum_comm
    _ = _ := sum_congr rfl fun B hB => sum_adj_blockWeight (D.clique B hB) (D.size B hB)

private lemma mul_positivePart (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    signedAdj G σ * positivePart G σ = positivePart G σ * positivePart G σ := by
  let hA := signed_hermitian G σ
  calc
    signedAdj G σ * positivePart G σ =
        (hermPosPart hA - hermNegPart hA) * hermPosPart hA :=
      congrArg (· * hermPosPart hA) (hermPosPart_sub_hermNegPart hA).symm
    _ = positivePart G σ * positivePart G σ := by
      rw [sub_mul, hermNegPart_mul_hermPosPart, sub_zero]

private lemma sPlus_eq_trace_sq (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    sPlus G σ = trace (positivePart G σ * positivePart G σ) := by
  let hA := signed_hermitian G σ
  have hX := (hermPosPart_posSemidef hA).isHermitian
  have hf : frobSq (positivePart G σ) = trace (positivePart G σ * positivePart G σ) := by
    rw [frobSq, hX.eq, RCLike.re_to_real]
  rw [← hf, frobSq_hermPosPart hA]
  apply sum_congr rfl
  intro i _
  by_cases hi : 0 < hA.eigenvalues i
  · simp [hi, posPart_eq_self.mpr hi.le]
  · simp [hi, posPart_eq_zero.mpr (le_of_not_gt hi)]

private lemma fold_mass_eq_energy (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    quadratic (foldNonedges G (positivePart G σ)) (fun _ => 1) = sPlus G σ := by
  have hX : (positivePart G σ).IsSymm :=
    (hermPosPart_posSemidef (signed_hermitian G σ)).isHermitian.isSymm
  rw [fold_quadratic, sPlus_eq_trace_sq]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sum_const_zero, add_zero, quadratic, dotProduct, mulVec, one_mul, mul_one,
    hadamard_apply, trace, diag_apply, Matrix.mul_apply]
  exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by rw [hX.apply u v]

/-- The folded positive part has exactly the normalized mass at the upper endpoint. -/
private theorem folded_positivePart_mass_at_endpoint (G : SimpleGraph (Fin n))
    (σ : Sym2 (Fin n) → Bool) (hUpper : sPlus G σ = endpoint G) :
    Gram.mass (foldNonedges G (positivePart G σ)) = endpoint G := by
  have hEq (M : Matrix (Fin n) (Fin n) ℝ) :
      Gram.mass M = quadratic M (fun _ => 1) := by
    simp [Gram.mass, quadratic, dotProduct, mulVec]
  exact (hEq _).trans ((fold_mass_eq_energy G σ).trans hUpper)

/-- The normalized fold supplies the exact absolute edge sum. At the upper endpoint,
the signed trace and absolute edge sum coincide, forcing each edge sign separately. -/
private theorem edge_sign_of_normalized_fold (G : SimpleGraph (Fin n))
    (σ : Sym2 (Fin n) → Bool) {blocks : Finset (Finset (Fin n))}
    (hUpper : sPlus G σ = endpoint G)
    (D : NormalizedBlocks G (positivePart G σ) blocks) {u v : Fin n} (huv : G.Adj u v) :
    signedAdj G σ u v * positivePart G σ u v = |positivePart G σ u v| := by
  let A := signedAdj G σ
  let X := positivePart G σ
  have hX : X.IsSymm := (hermPosPart_posSemidef (signed_hermitian G σ)).isHermitian.isSymm
  have hAbs : (∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then |X i j| else 0) = endpoint G :=
    (abs_sum_eq_fold_mass D).trans ((fold_mass_eq_energy G σ).trans hUpper)
  have hSigned : (∑ i : Fin n, ∑ j : Fin n, A i j * X i j) = endpoint G := by
    have ht : trace (A * X) = endpoint G := by
      rw [mul_positivePart G σ, ← sPlus_eq_trace_sq, hUpper]
    rw [← ht]
    simp only [trace, diag_apply, Matrix.mul_apply]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hX.apply i j]
  have hLe (i j : Fin n) : A i j * X i j ≤ if G.Adj i j then |X i j| else 0 := by
    by_cases ha : G.Adj i j
    · cases hs : σ s(i,j)
      · simpa [A, signedAdj, ha, hs] using neg_le_abs (X i j)
      · simpa [A, signedAdj, ha, hs] using le_abs_self (X i j)
    · simp [A, signedAdj, ha]
  have hRows := (sum_eq_sum_iff_of_le (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
    sum_le_sum (fun j _ => hLe i j))).mp (hSigned.trans hAbs.symm)
  have hEntry := (sum_eq_sum_iff_of_le (fun j (_ : j ∈ (univ : Finset (Fin n))) =>
    hLe u j)).mp (hRows u (mem_univ u)) v (mem_univ v)
  simpa [huv, A, X] using hEntry

private lemma block_edge_entry (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    {blocks : Finset (Finset (Fin n))} (hUpper : sPlus G σ = endpoint G)
    (D : NormalizedBlocks G (positivePart G σ) blocks)
    {B : Finset (Fin n)} (hB : B ∈ blocks) {u v : Fin n}
    (huv : G.Adj u v) (hu : u ∈ B) (hv : v ∈ B) :
    positivePart G σ u v = blockWeight B * signedAdj G σ u v := by
  have h := edge_sign_of_normalized_fold G σ hUpper D huv
  rw [abs_entry_of_block_edge D hB huv hu hv] at h
  cases hs : σ s(u,v) <;> simp [signedAdj, huv, hs] at h ⊢ <;> linarith

open Gram
open DNN (budget budget_eq budget_nonneg edgeMass_eq_sum
  edgeMass_nonneg sum_adj sum_darts supported_bound Normalized)

/-- The spectral upper equality supplies both scalars required by the DNN decomposition. -/
private theorem positivePart_fold_normalized (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (hG : G.Connected) (hUpper : sPlus G σ = endpoint G) :
    Normalized G (foldNonedges G (positivePart G σ))
      (foldNonedges_supportedDNN G (hermPosPart_posSemidef (signed_hermitian G σ))) := by
  classical
  let X := positivePart G σ
  let M := foldNonedges G X
  have hX : X.PosSemidef := hermPosPart_posSemidef (signed_hermitian G σ)
  have hM : SupportedDNN G M := foldNonedges_supportedDNN G hX
  have hBudget : budget G = endpoint G := by
    rw [budget_eq]
    simp [endpoint]
  have hT : mass M = budget G :=
    (folded_positivePart_mass_at_endpoint G σ hUpper).trans hBudget.symm
  have hBound := supported_bound G M hM hG
  change (2 * edgeMass G M hM.symm) ^ 2 ≤ budget G * mass M at hBound
  have hq := budget_nonneg hG
  rw [hT, ← pow_two] at hBound
  have hUpperS := (sq_le_sq₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (edgeMass_nonneg G M hM.symm))
    hq).mp hBound
  have hTrace : trace (signedAdj G σ * X) = endpoint G := by
    rw [show X = positivePart G σ by rfl, mul_positivePart, ← sPlus_eq_trace_sq, hUpper]
  have hSigned : (∑ i : Fin n, ∑ j : Fin n, signedAdj G σ i j * X i j) = endpoint G := by
    rw [← hTrace]
    simp only [trace, diag_apply, Matrix.mul_apply]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hX.isHermitian.isSymm.apply i j]
  have hAbs :
      (∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then |X i j| else 0) =
        2 * edgeMass G M hM.symm := by
    rw [sum_adj G (fun i j => |X i j|), edgeMass_eq_sum, ← sum_darts]
    exact sum_congr rfl fun d _ => by
      change |X d.fst d.snd| = Real.sqrt (M d.fst d.snd)
      rw [show M d.fst d.snd = (X d.fst d.snd) ^ 2 from fold_on_edge _ d.adj,
        Real.sqrt_sq_eq_abs]
  have hLowerS : endpoint G ≤ 2 * edgeMass G M hM.symm := by
    rw [← hSigned, ← hAbs]
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
    by_cases h : G.Adj i j
    · cases hs : σ s(i,j)
      · simpa [signedAdj, h, hs] using neg_le_abs (X i j)
      · simpa [signedAdj, h, hs] using le_abs_self (X i j)
    · simp [signedAdj, h]
  exact ⟨hT, le_antisymm hUpperS (hBudget ▸ hLowerS)⟩

open DNN (RootExtension ExtensionsOn BlockDecomposition
  normalized_decomposition_with_extensions)

private theorem normalizedBlocks_of_decomposition {G : SimpleGraph (Fin n)}
    {X : Matrix (Fin n) (Fin n) ℝ} {blocks : Finset (Finset (Fin n))}
    (D : BlockDecomposition G (foldNonedges G X) blocks) : NormalizedBlocks G X blocks := by
  refine ⟨D.size, D.clique, D.edge, ?_⟩
  rw [D.matrix_eq]
  apply sum_congr rfl
  intro B _
  ext i j
  by_cases hi : i ∈ B <;> by_cases hj : j ∈ B <;>
    simp [DNN.blockMatrix, blockWeight, indicator,
      vecMulVec_apply, hi, hj]

private theorem cross_fiber_nonedge_zero (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    {blocks : Finset (Finset (Fin n))} (D : NormalizedBlocks G (positivePart G σ) blocks)
    {B : Finset (Fin n)} (hSize : 3 ≤ B.card) {p : Fin n → Fin n} {a : Fin n → ℝ}
    (E : RootExtension G blocks univ B p a) {i j : Fin n} (hij : p i ≠ p j)
    (hn : ¬ G.Adj i j) : positivePart G σ i j = 0 := by
  have hcard : ({p i, p j} : Finset (Fin n)).card < B.card := by
    rw [card_insert_of_notMem (by simpa using hij), card_singleton]
    omega
  obtain ⟨k, hk, hkn⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hki : k ≠ p i := fun h => hkn (by simp [h])
  have hkj : k ≠ p j := fun h => hkn (by simp [h])
  let x := difference (p i) k
  have hx : (∑ l ∈ B, x l) = 0 := by
    simp [x, difference, Pi.sub_apply, sum_sub_distrib, Pi.single_apply,
      E.lands i (mem_univ i), hk]
  have hxpi : x (p i) = 1 := by simp [x, difference, hki.symm]
  have hxpj : x (p j) = 0 := by
    simp [x, difference, hij.symm, hkj.symm]
  apply nonedge_zero_of_blockwise_zero_sum G σ D (fun l => a l * x (p l))
    (E.zero_sum x hx) hn
  rw [hxpi, hxpj, mul_one, mul_zero]
  exact E.nonzero i (mem_univ i)

private theorem signedAdj_mul_positivePart_comm (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    signedAdj G σ * positivePart G σ = positivePart G σ * signedAdj G σ := by
  let hA := signed_hermitian G σ
  calc
    signedAdj G σ * positivePart G σ = positivePart G σ * positivePart G σ :=
      mul_positivePart G σ
    _ = hermPosPart hA * (hermPosPart hA - hermNegPart hA) := by
      rw [mul_sub, hermPosPart_mul_hermNegPart, sub_zero]
    _ = positivePart G σ * signedAdj G σ := by rw [hermPosPart_sub_hermNegPart]

/-- For a large block, the cut extension forces the actual X to vanish between
distinct fibers away from the root edges. The bridge case uses AX=XA and
the unequal weights. The identity AX=X² excludes any remaining attachment. -/
private theorem no_attachment_to_large_block (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    {blocks : Finset (Finset (Fin n))} (hUpper : sPlus G σ = endpoint G)
    (D : NormalizedBlocks G (positivePart G σ) blocks) {B : Finset (Fin n)}
    (hB : B ∈ blocks) (hSize : 3 ≤ B.card)
    {p : Fin n → Fin n} {a : Fin n → ℝ} (E : RootExtension G blocks univ B p a)
    {v w : Fin n} (hv : v ∈ B) (hw : w ∉ B) (hvw : G.Adj v w) : False := by
  let A := signedAdj G σ
  let X := positivePart G σ
  have edge {i j : Fin n} (ha : G.Adj i j) (hne : p i ≠ p j) : i ∈ B ∧ j ∈ B :=
    E.edge i (mem_univ i) j (mem_univ j) ha hne
  have zero {i j : Fin n} (hne : p i ≠ p j) (hout : i ∉ B ∨ j ∉ B) : X i j = 0 :=
    cross_fiber_nonedge_zero G σ D hSize E hne fun ha =>
      hout.elim (fun h => h (edge ha hne).1) (fun h => h (edge ha hne).2)
  have hpv : p v = v := E.fixes v hv
  have hpw : p w = v := by
    rw [← hpv]
    by_contra! h
    exact hw (edge hvw h.symm).2
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp (by omega : 1 < B.card)
  obtain ⟨x, hx, hxv⟩ : ∃ x ∈ B, x ≠ v := by
    by_cases hiv : i = v
    · exact ⟨j, hj, fun h => hij (hiv.trans h.symm)⟩
    · exact ⟨i, hi, hiv⟩
  have hpx := E.fixes x hx
  have hxa : G.Adj x v := D.clique B hB hx hv hxv
  have hxw : p x ≠ p w := by simpa only [hpx, hpw] using hxv
  have hAX : (A * X) x w = A x v * X v w := by
    rw [Matrix.mul_apply]
    refine sum_eq_single_of_mem v (mem_univ v) fun j _ hjv => ?_
    by_cases hp : p j = p w
    · have hn : ¬ G.Adj x j := by
        intro h
        have hj := (edge h (by simpa only [hp] using hxw)).2
        exact hjv ((E.fixes j hj).symm.trans (hp.trans hpw))
      simp [A, signedAdj, hn]
    · rw [zero hp (Or.inr hw), mul_zero]
  obtain ⟨C, ⟨hC, hvC, hwC⟩, _⟩ := D.edge v w hvw
  have hBxv : X x v = blockWeight B * A x v := block_edge_entry G σ hUpper D hB hxa hx hv
  have hCvw : X v w = blockWeight C * A v w := block_edge_entry G σ hUpper D hC hvw hvC hwC
  have hAxv : A x v ≠ 0 := by cases hs : σ s(x,v) <;> simp [A, signedAdj, hxa, hs]
  have hAvw : A v w ≠ 0 := by cases hs : σ s(v,w) <;> simp [A, signedAdj, hvw, hs]
  by_cases hTwo : C.card = 2
  · have hXA : (X * A) x w = X x v * A v w := by
      rw [Matrix.mul_apply]
      refine sum_eq_single_of_mem v (mem_univ v) fun j _ hjv => ?_
      by_cases hp : p j = p w
      · have hj : j ∉ B := fun h => hjv ((E.fixes j h).symm.trans (hp.trans hpw))
        rw [zero (by simpa only [hp] using hxw) (Or.inr hj), zero_mul]
      · have hn : ¬ G.Adj j w := fun h => hw (edge h hp).2
        simp [A, signedAdj, hn]
    have hProducts : A x v * X v w = X x v * A v w :=
      hAX.symm.trans ((congrFun (congrFun (signedAdj_mul_positivePart_comm G σ) x) w).trans hXA)
    rw [hCvw, hBxv] at hProducts
    have hWeights : blockWeight C = blockWeight B := by
      apply mul_right_cancel₀ (mul_ne_zero hAxv hAvw)
      calc
        blockWeight C * (A x v * A v w) = A x v * (blockWeight C * A v w) := by ring
        _ = blockWeight B * A x v * A v w := hProducts
        _ = blockWeight B * (A x v * A v w) := by ring
    have hHalf : blockWeight C = 1 / 2 := by norm_num [blockWeight, hTwo]
    have hCard : (3 : ℝ) ≤ B.card := by exact_mod_cast hSize
    have hBgt : 1 / 2 < blockWeight B := by
      unfold blockWeight
      rw [lt_div_iff₀ (by linarith : 0 < (B.card : ℝ))]
      linarith
    exact (ne_of_gt hBgt) (hWeights.symm.trans hHalf)
  · have hXX : (X * X) x w = X x v * X v w := by
      rw [Matrix.mul_apply]
      refine sum_eq_single_of_mem v (mem_univ v) fun j _ hjv => ?_
      by_cases hp : p j = p w
      · have hj : j ∉ B := fun h => hjv ((E.fixes j h).symm.trans (hp.trans hpw))
        rw [zero (by simpa only [hp] using hxw) (Or.inr hj), zero_mul]
      · rw [zero hp (Or.inr hw), mul_zero]
    have hProducts : A x v * X v w = X x v * X v w :=
      hAX.symm.trans ((congrFun (congrFun (mul_positivePart G σ) x) w).trans hXX)
    have hXvw : X v w ≠ 0 := hCvw ▸ mul_ne_zero (weight_pos (D.size C hC)).ne' hAvw
    have hEq : A x v = X x v := mul_right_cancel₀ hXvw hProducts
    rw [hBxv] at hEq
    exact (ne_of_gt (weight_lt_one (D.size B hB)))
      (mul_right_cancel₀ hAxv (by simpa only [one_mul] using hEq))

private theorem closed_block_eq_univ {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {B : Finset (Fin n)} (hB : B.Nonempty)
    (hClosed : ∀ v ∈ B, ∀ w, G.Adj v w → w ∈ B) : B = univ := by
  obtain ⟨v, hv⟩ := hB
  have walk_mem {i j : Fin n} (W : G.Walk i j) : i ∈ B → j ∈ B := by
    induction W with
    | nil => exact id
    | cons h _ ih => exact fun hi => ih (hClosed _ hi _ h)
  apply eq_univ_of_forall
  intro w
  obtain ⟨W⟩ := hG.preconnected v w
  exact walk_mem W hv

/-- Upper equality forces the original connected signed graph to be a tree or a
complete graph. The singleton is included in the tree case. -/
private theorem tree_or_complete_of_upper (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (hG : G.Connected) (hUpper : sPlus G σ = endpoint G) : G.IsTree ∨ G = ⊤ := by
  obtain ⟨blocks, D, e, small⟩ := normalized_decomposition_with_extensions G _ _ hG
    (positivePart_fold_normalized G σ hG hUpper)
  by_cases h : ∀ B ∈ blocks, B.card = 2
  · exact Or.inl (small h)
  · push Not at h
    obtain ⟨B, hB, hne⟩ := h
    have hs := D.size B hB
    have hSize : 3 ≤ B.card := by omega
    obtain ⟨p, a, E⟩ := e.rooted B hB
    have hUniv := closed_block_eq_univ hG (card_pos.mp (by omega : 0 < B.card))
      (fun v hv w hvw => by
        by_contra hw
        exact no_attachment_to_large_block G σ hUpper (normalizedBlocks_of_decomposition D)
          hB hSize E hv hw hvw)
    refine Or.inr ?_
    ext i j
    refine ⟨fun h => h.ne, fun h => ?_⟩
    exact D.clique B hB (by simp [hUniv]) (by simp [hUniv]) h

open DNN (BlockDecomposition normalized_decomposition_with_extensions)

/-- The actual signing is obtained by switching a uniform positive signing. -/
def Balanced (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) : Prop :=
  ∃ θ : Fin n → ℝ, (∀ i, θ i = 1 ∨ θ i = -1) ∧
    ∀ i j, G.Adj i j → signedAdj G σ i j = θ i * θ j

/-- The actual signing is obtained by switching a uniform negative signing. -/
def Antibalanced (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) : Prop :=
  ∃ θ : Fin n → ℝ, (∀ i, θ i = 1 ∨ θ i = -1) ∧
    ∀ i j, G.Adj i j → signedAdj G σ i j = -(θ i * θ j)

private theorem signedAdj_sign {G : SimpleGraph (Fin n)} (σ : Sym2 (Fin n) → Bool)
    {i j : Fin n} (h : G.Adj i j) :
    signedAdj G σ i j = 1 ∨ signedAdj G σ i j = -1 := by
  cases hs : σ s(i,j) <;> simp [signedAdj, h, hs]

private theorem sign_sq {r : ℝ} (h : r = 1 ∨ r = -1) : r ^ 2 = 1 := by
  rcases h with rfl | rfl <;> norm_num

private theorem top_fold_eq_hadamard (X : Matrix (Fin n) (Fin n) ℝ) :
    foldNonedges ⊤ X = X ⊙ X := by
  have empty_of_complete (G : SimpleGraph (Fin n))
      (hG : ∀ i j, i ≠ j → G.Adj i j) : nonedges G = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨i, j⟩ h
    have hh := (mem_filter.mp h).2
    exact hh.2 (hG i j (ne_of_lt hh.1))
  have h := empty_of_complete (⊤ : SimpleGraph (Fin n)) (fun _ _ h => h)
  simp [foldNonedges, h]

private theorem top_fold_of_upper (σ : Sym2 (Fin n) → Bool)
    (hG : (⊤ : SimpleGraph (Fin n)).Connected) (hn : 2 ≤ n)
    (hUpper : sPlus ⊤ σ = endpoint (⊤ : SimpleGraph (Fin n))) :
    NormalizedBlocks ⊤ (positivePart ⊤ σ) {univ} := by
  obtain ⟨blocks, D, _, _⟩ := normalized_decomposition_with_extensions _ _ _ hG
    (positivePart_fold_normalized ⊤ σ hG hUpper)
  have hs : 2 ≤ (univ : Finset (Fin n)).card := by simpa using hn
  have hu : (univ : Finset (Fin n)) ∈ blocks := by
    obtain ⟨B, hB, hsub⟩ := D.clique_cover univ (fun _ _ _ _ h => h) hs
    rwa [eq_univ_of_forall (fun i => hsub (mem_univ i))] at hB
  have hblocks : blocks = {univ} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨hu, ?_⟩
    intro B hB
    have hmax := (D.mem_iff_maximal B).mp hB
    exact (hmax.2.2 univ (fun _ _ _ _ h => h) (subset_univ B)).symm
  rw [← hblocks]
  exact normalizedBlocks_of_decomposition D

/-- On a complete graph at the upper endpoint the actual positive spectral
part is rank one, with a spanning sign vector and the normalized clique weight. -/
private theorem top_positivePart_rank_one_of_upper (σ : Sym2 (Fin n) → Bool)
    (hG : (⊤ : SimpleGraph (Fin n)).Connected) (hn : 2 ≤ n)
    (hUpper : sPlus ⊤ σ = endpoint (⊤ : SimpleGraph (Fin n))) :
    ∃ θ : Fin n → ℝ, (∀ i, θ i = 1 ∨ θ i = -1) ∧
      positivePart ⊤ σ = blockWeight (univ : Finset (Fin n)) • vecMulVec θ θ ∧
      ∀ i j, (⊤ : SimpleGraph (Fin n)).Adj i j → signedAdj ⊤ σ i j = θ i * θ j := by
  let X := positivePart ⊤ σ
  let w := blockWeight (univ : Finset (Fin n))
  have D := top_fold_of_upper σ hG hn hUpper
  have hp : 0 < w := weight_pos (D.size _ (mem_singleton_self _))
  have hPSD : X.PosSemidef := hermPosPart_posSemidef _
  have hSym := hPSD.isHermitian.isSymm
  have hFold := D.fold_eq
  rw [top_fold_eq_hadamard] at hFold
  have hd (i : Fin n) : X i i = w := by
    have he := congrFun (congrFun hFold i) i
    have he' : X i i * X i i = w ^ 2 := by
      simpa [X, w, indicator, vecMulVec_apply, hadamard_apply] using he
    have hh : 0 ≤ X i i := hPSD.diag_nonneg
    have hf : (X i i - w) * (X i i + w) = 0 := by nlinarith only [he']
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (by positivity))
  have he (i j : Fin n) (h : i ≠ j) : X i j = w * signedAdj ⊤ σ i j :=
    block_edge_entry ⊤ σ hUpper D (mem_singleton_self _) h (mem_univ _) (mem_univ _)
  let r : Fin n := ⟨0, by omega⟩
  let θ : Fin n → ℝ := fun i => if i = r then 1 else signedAdj ⊤ σ i r
  have hθ (i : Fin n) : θ i = 1 ∨ θ i = -1 := by
    by_cases hi : i = r
    · simp [θ, hi]
    · simpa [θ, hi] using signedAdj_sign σ (G := (⊤ : SimpleGraph (Fin n))) hi
  have hcol (i : Fin n) : X i r = w * θ i := by
    by_cases hi : i = r
    · subst i
      simpa [θ] using hd r
    · simpa [θ, hi] using he i r hi
  have hKernel (i j : Fin n) : X j i = θ i * X j r := by
    let z : Fin n → ℝ := Pi.single i 1 - Pi.single r (θ i)
    have hz : star z ⬝ᵥ X *ᵥ z = 0 := by
      have hstar : star z = z := by ext j; simp
      rw [hstar]
      simp only [z, mulVec_sub, sub_dotProduct, dotProduct_sub, single_dotProduct,
        mulVec_single, Pi.smul_apply, Matrix.col_apply, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, one_mul]
      rw [hd i, hd r, hSym.apply i r, hcol i]
      nlinarith only [congrArg (w * ·) (sign_sq (hθ i))]
    have hj := congrFun (hPSD.dotProduct_mulVec_zero_iff.mp hz) j
    simp only [z, mulVec_sub, mulVec_single, Pi.sub_apply, Pi.smul_apply, Matrix.col_apply,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_one, Pi.zero_apply] at hj
    exact (sub_eq_zero.mp hj).trans (mul_comm _ _)
  have hentry (i j : Fin n) : X i j = w * (θ i * θ j) := by
    rw [hKernel j i, hcol i]
    ring
  refine ⟨θ, hθ, ?_, ?_⟩
  · ext i j
    simpa [X, w, vecMulVec_apply] using hentry i j
  · intro i j hij
    exact mul_left_cancel₀ hp.ne' ((he i j hij).symm.trans (hentry i j))

private theorem balanced_of_complete_upper (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (hG : G.Connected) (hTop : G = ⊤) (hUpper : sPlus G σ = endpoint G) :
    Balanced G σ := by
  subst G
  by_cases hn : 2 ≤ n
  · obtain ⟨θ, hθ, _, hsign⟩ := top_positivePart_rank_one_of_upper σ hG hn hUpper
    exact ⟨θ, hθ, hsign⟩
  · have hs : Subsingleton (Fin n) := Fintype.card_le_one_iff_subsingleton.mp (by simpa using
      (show n ≤ 1 by omega))
    exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun i j h => (h.ne (hs.elim i j)).elim⟩

open scoped MatrixOrder NonUnitalContinuousFunctionalCalculus

private theorem endpoint_eq_budget (G : SimpleGraph (Fin n)) :
    endpoint G = DNN.budget G := by
  rw [DNN.budget_eq]
  simp [endpoint]

/-- A bipartition gives an explicit matrix similarity between any real signed
adjacency on the graph and its negative. The full spectrum agrees with multiplicity. -/
private theorem sPlus_eq_reversed_of_bipartite (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (hG : G.IsBipartite) :
    sPlus G σ = sPlus G (fun e => !(σ e)) := by
  obtain ⟨c, hc⟩ := hG
  let θ : Fin n → ℝ := fun i => if c i = 0 then 1 else -1
  let D := Matrix.diagonal θ
  let A := signedAdj G σ
  have hdiag : D * D = 1 := by
    change diagonal θ * diagonal θ = 1
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    by_cases h : c i = 0 <;> simp [θ, h]
  have hneg : D * A * D = -A := by
    ext i j
    change ((diagonal θ * A) * diagonal θ) i j = -A i j
    rw [mul_diagonal, diagonal_mul]
    by_cases h : G.Adj i j
    · have hcol : c i ≠ c j := hc h
      have hi : c i = 0 ∨ c i = 1 := by omega
      have hj : c j = 0 ∨ c j = 1 := by omega
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact (hcol (hi.trans hj.symm)).elim
      · simp [θ, hi, hj]
      · simp [θ, hi, hj]
      · exact (hcol (hi.trans hj.symm)).elim
    · simp [A, signedAdj, h]
  have hchar : (signedAdj G (fun e => !(σ e))).charpoly = A.charpoly := by
    rw [signedAdj_complement, ← show D * A * D = -(signedAdj G σ) from hneg,
      charpoly_mul_comm (D * A) D, ← mul_assoc, hdiag, one_mul]
  have hspec := (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
    (hA := signed_hermitian G (fun e => !(σ e))) (hB := signed_hermitian G σ)).mpr hchar
  unfold sPlus
  rw [hspec]

private theorem tree_attains_upper (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (hG : G.IsTree) : sPlus G σ = endpoint G := by
  have hs := sPlus_eq_reversed_of_bipartite G σ hG.isBipartite
  have hCon := sPlus_add_complement G σ
  have hb := DNN.budget_eq_card_sub_one_of_tree hG
  rw [DNN.budget_eq] at hb
  simp only [Fintype.card_fin] at hb
  unfold endpoint
  linarith

private theorem hermPosPart_eq_cfc_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    hermPosPart hA = A⁺ := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc (hf := by fun_prop) (hf0 := by simp), hA.cfc_eq]
  rfl

private theorem vecMulVec_sign_product (θ : Fin n → ℝ) (hθ : ∀ i, θ i = 1 ∨ θ i = -1) :
    vecMulVec θ θ * vecMulVec θ θ = (n : ℝ) • vecMulVec θ θ := by
  have hdot : θ ⬝ᵥ θ = (n : ℝ) := by
    simp only [dotProduct, ← pow_two, fun i => sign_sq (hθ i), sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [vecMulVec_mul_vecMulVec, hdot]
  ext i j
  simp [vecMulVec_apply, mul_left_comm]

/-- A balanced complete signing attains the upper endpoint. The positive spectral
part is the rank-one sign projection times its sole possibly positive eigenvalue. -/
private theorem balanced_complete_attains_upper (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (hG : G.Connected) (hTop : G = ⊤) (hb : Balanced G σ) :
    sPlus G σ = endpoint G := by
  obtain ⟨θ, hθ, hsigned⟩ := hb
  have hne := hG.nonempty
  have hn : 1 ≤ n := Nat.succ_le_of_lt (by
    simpa only [Fintype.card_fin] using (Fintype.card_pos (α := Fin n)))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  let A := signedAdj G σ
  let R := vecMulVec θ θ
  let P : Matrix (Fin n) (Fin n) ℝ := (n : ℝ)⁻¹ • R
  let Q : Matrix (Fin n) (Fin n) ℝ := 1 - P
  let U : Matrix (Fin n) (Fin n) ℝ := ((n : ℝ) - 1) • P
  have hA : A = R - 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A, R, signedAdj, vecMulVec_apply, ← pow_two, sign_sq (hθ i)]
    · have h : G.Adj i j := by simpa [hTop] using hij
      simp [A, R, hsigned i j h, vecMulVec_apply, Matrix.one_apply_ne hij]
  have hR : R.PosSemidef := by
    simpa [R] using (Matrix.posSemidef_vecMulVec_self_star θ)
  have hP : P.PosSemidef := hR.smul (inv_nonneg.mpr (by linarith))
  have hnP : (n : ℝ) • P = R := by simp [P, smul_smul, hn0]
  have hPP : P * P = P := by
    calc
      P * P = ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) • (R * R) := by
        simp only [P, smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = P := by
        rw [show R * R = (n : ℝ) • R from vecMulVec_sign_product θ hθ]
        simp [P, smul_smul, hn0]
  have hQQ : Q * Q = Q := by
    calc
      Q * Q = 1 - P - P + P * P := by dsimp [Q]; noncomm_ring
      _ = Q := by rw [hPP]; dsimp [Q]; abel
  have hQh : Q.IsHermitian := isHermitian_one.sub hP.isHermitian
  have hQ : Q.PosSemidef := by
    simpa only [hQh.eq, hQQ] using Matrix.posSemidef_conjTranspose_mul_self Q
  have hU : U.PosSemidef := hP.smul (sub_nonneg.mpr hnR)
  have hPQ : P * Q = 0 := by simp [Q, mul_sub, hPP]
  have hUQ : U * Q = 0 := by simp [U, hPQ]
  have hdecomp : A = U - Q := by
    rw [hA, ← hnP]
    dsimp [U, Q]
    rw [sub_smul, one_smul]
    abel
  have hPos : positivePart G σ = U := by
    change hermPosPart (signed_hermitian G σ) = U
    rw [hermPosPart_eq_cfc_pos]
    exact (CFC.posPart_negPart_unique hdecomp hUQ hU.nonneg hQ.nonneg).1
  have htr : trace P = 1 := by
    simp [trace, P, R, diag_apply, Matrix.smul_apply, vecMulVec_apply, ← pow_two,
      fun i => sign_sq (hθ i), hn0]
  have hU2 : U * U = (((n : ℝ) - 1) ^ 2) • P := by
    simp only [U, smul_mul_assoc, mul_smul_comm, smul_smul, hPP, pow_two]
  have hbTop := DNN.budget_top (V := Fin n) (by simpa using hn)
  rw [sPlus_eq_trace_sq, hPos, hU2, trace_smul, htr, smul_eq_mul, mul_one, endpoint_eq_budget,
    hTop]
  simpa using hbTop.symm

private theorem balanced_reversed_iff (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    Balanced G (fun e => !(σ e)) ↔ Antibalanced G σ := by
  unfold Balanced Antibalanced
  rw [signedAdj_complement]
  simp only [Matrix.neg_apply, neg_eq_iff_eq_neg]

/-- Hu–Han Problem 6.1, upper equality, using all eigenvalue occurrences of the
actual signed adjacency and including the singleton. -/
private theorem upper_equality_iff (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (hG : G.Connected) :
    sPlus G σ = endpoint G ↔ G.IsTree ∨ (G = ⊤ ∧ Balanced G σ) := by
  constructor
  · intro h
    rcases tree_or_complete_of_upper G σ hG h with ht | hc
    · exact Or.inl ht
    · exact Or.inr ⟨hc, balanced_of_complete_upper G σ hG hc h⟩
  · rintro (ht | ⟨hc, hb⟩)
    · exact tree_attains_upper G σ ht
    · exact balanced_complete_attains_upper G σ hG hc hb

/-- Hu–Han Problem 6.1, lower equality, by sign reversal and the signed
conservation identity with the same multiplicity convention. -/
private theorem lower_equality_iff (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (hG : G.Connected) :
    sPlus G σ = (n : ℝ) - 1 ↔ G.IsTree ∨ (G = ⊤ ∧ Antibalanced G σ) := by
  have hc := sPlus_add_complement G σ
  have h : sPlus G σ = (n : ℝ) - 1 ↔ sPlus G (fun e => !(σ e)) = endpoint G := by
    unfold endpoint
    constructor <;> intro h <;> linarith
  rw [h, upper_equality_iff G (fun e => !(σ e)) hG, balanced_reversed_iff]

end

/-- Hu–Han Problem 6.1. Every finite connected signed simple graph attains the
upper endpoint exactly when it is a tree or a balanced complete graph, and
the lower endpoint exactly when it is a tree or an antibalanced complete graph. -/
theorem result {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (hG : G.Connected) :
    (sPlus G σ = endpoint G ↔ G.IsTree ∨ (G = ⊤ ∧ Balanced G σ)) ∧
    (sPlus G σ = (n : ℝ) - 1 ↔ G.IsTree ∨ (G = ⊤ ∧ Antibalanced G σ)) :=
  ⟨upper_equality_iff G σ hG, lower_equality_iff G σ hG⟩

end D5.S3.Combinatorics.SignedGraphSpectral.HuHanSquareEnergy
