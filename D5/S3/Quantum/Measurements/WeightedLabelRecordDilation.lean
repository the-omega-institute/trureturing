/- GID: D5/S3/Quantum/Measurements/WeightedLabelRecordDilation
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/WeightedLabelRecordDilation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp average success of finite label records with a fixed pure environment. -/

import D5.S3.Quantum.Measurements.FiniteLabelRecordDilation
import D5.S3.Quantum.PureState.PhaseRecordSpectralMemory
import D5.S3.Weil.ZetaLinear.VonNeumann
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The largest environment-sized blocks of the labelwise sorted priors give the
optimal success for one full-input isometry and a memory POVM. -/

open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix Finset
open scoped Polynomial Classical

namespace D5.S3.Quantum.Measurements.WeightedLabelRecordDilation

open FiniteLabelRecordDilation
open _root_.PhaseRecordSpectralMemory

noncomputable section

variable {B J : Type*} [Fintype B] [DecidableEq B] [Fintype J]
variable {d e : ℕ}

/-- The average success after discarding the environment of the full-input isometry. -/
def averageSuccess (c : B → J) (p : B → ℝ) (V : Matrix (Fin d × Fin e) B ℂ)
    (E : J → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ b, p b * (E (c b) * reducedColumn V b).trace.re

private def paddedIndex (N : ℕ) (hN : Fintype.card B ≤ N) :
    Fin N ≃ B ⊕ Fin (N - Fintype.card B) :=
  Fintype.equivOfCardEq (by simp [Nat.add_sub_of_le hN])

private def decreasing {n : ℕ} (a : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (α := ℝᵒᵈ) a

private theorem decreasing_antitone {n : ℕ} (a : Fin n → ℝ) :
    Antitone (a ∘ decreasing a) :=
  Tuple.monotone_sort (α := ℝᵒᵈ) a

private def labelWeight (c : B → J) (p : B → ℝ) (j : J) (b : B) : ℝ :=
  if c b = j then p b else 0

private def paddedWeight (c : B → J) (p : B → ℝ) (hN : Fintype.card B ≤ d * e) (j : J) :
    Fin (d * e) → ℝ :=
  Sum.elim (labelWeight c p j) (fun _ => 0) ∘ paddedIndex (d * e) hN

private def sortedIndex (c : B → J) (p : B → ℝ) (hN : Fintype.card B ≤ d * e) (j : J) :
    Fin (d * e) ≃ B ⊕ Fin (d * e - Fintype.card B) :=
  (decreasing (paddedWeight c p hN j)).trans (paddedIndex (d * e) hN)

private def sortedWeight (c : B → J) (p : B → ℝ) (hN : Fintype.card B ≤ d * e) (j : J) :
    Fin (d * e) → ℝ :=
  paddedWeight c p hN j ∘ decreasing (paddedWeight c p hN j)

/-- The sum of the (e) consecutive priors in a row of the decreasing padded label list. -/
def blockMass (c : B → J) (p : B → ℝ) (hN : Fintype.card B ≤ d * e)
    (j : J) (m : Fin d) : ℝ :=
  ∑ t : Fin e, sortedWeight c p hN j (finProdFinEquiv (m, t))

private def topSet {I : Type*} [Fintype I] (w : I → ℝ) (n : ℕ) : Finset I :=
  let base := (Fintype.equivFin I).symm
  univ.map ((Fin.castLEEmb (min_le_right n (Fintype.card I))).trans
    ((decreasing (w ∘ base)).trans base).toEmbedding)

private theorem card_topSet {I : Type*} [Fintype I] (w : I → ℝ) (n : ℕ) :
    (topSet w n).card = min n (Fintype.card I) := by
  simp [topSet]

private theorem topSet_top {I : Type*} [Fintype I] (w : I → ℝ) (n : ℕ) :
    ∀ i ∈ topSet w n, ∀ j ∉ topSet w n, w j ≤ w i := by
  intro i hi j hj
  let base := (Fintype.equivFin I).symm
  let ord := (decreasing (w ∘ base)).trans base
  obtain ⟨k, _, rfl⟩ := mem_map.mp hi
  have hj' : min n (Fintype.card I) ≤ (ord.symm j).val := by
    by_contra! h
    apply hj
    exact mem_map.mpr ⟨⟨_, h⟩, mem_univ _, ord.apply_symm_apply j⟩
  have hle : Fin.castLE (min_le_right n (Fintype.card I)) k ≤ ord.symm j := k.isLt.le.trans hj'
  change w j ≤ w (ord (Fin.castLE (min_le_right _ _) k))
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    (show Antitone (w ∘ ord) from decreasing_antitone (w ∘ base)) hle

/-- Sum of the (d) largest block masses across all labels. -/
def optimalSuccess (c : B → J) (p : B → ℝ) (hN : Fintype.card B ≤ d * e) : ℝ :=
  let w := fun a : J × Fin d => blockMass c p hN a.1 a.2
  ∑ a ∈ topSet w d, w a

private theorem sortedWeight_nonneg (c : B → J) (p : B → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hN : Fintype.card B ≤ d * e) (j : J) (k : Fin (d * e)) :
    0 ≤ sortedWeight c p hN j k := by
  change 0 ≤ Sum.elim _ _ (sortedIndex c p hN j k)
  cases sortedIndex c p hN j k <;> simp [labelWeight, apply_ite, hp]

private theorem eigenvalues_of_sorted_charpoly {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f)
    (card : Fintype.card I = n)
    (h : A.charpoly = (diagonal fun k => (f k : ℂ)).charpoly) :
    ∀ i : Fin (Fintype.card I), hA.eigenvalues₀ i = f (Fin.cast card i) := by
  have he := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [h, Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => Polynomial.X_sub_C_ne_zero _)] at he
  simp only [Polynomial.roots_X_sub_C, Multiset.sum_map_singleton, Multiset.bind_singleton, ← Multiset.map_map,
    Function.comp_def, RCLike.ofReal_re, Complex.ofReal_re, Fin.univ_val_map,
    Multiset.map_coe, List.map_ofFn, Multiset.coe_sort] at he
  change (List.ofFn f).mergeSort (fun a b => decide (a ≥ b)) = _ at he
  have hSort : (List.ofFn f).mergeSort (fun a b => decide (a ≥ b)) = List.ofFn f := by
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hf.sortedGE_ofFn
  rw [hSort] at he
  intro i
  have hi : i.val < (List.ofFn hA.eigenvalues₀).length := by simpa using i.isLt
  have hj : i.val < (List.ofFn f).length := by simpa [← card] using i.isLt
  have hget := congrArg (fun l : List ℝ => l[i.val]?) he
  rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hi] at hget
  have eq := (Option.some.inj hget).symm
  simp only [List.getElem_ofFn] at eq
  exact eq

private theorem weighted_charpoly (c : B → J) (p : B → ℝ)
    (hN : Fintype.card B ≤ d * e) (j : J)
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1) :
    (V * diagonal (fun b => (labelWeight c p j b : ℂ)) * Vᴴ).charpoly =
      (diagonal fun k => (sortedWeight c p hN j k : ℂ)).charpoly := by
  let D := diagonal (fun b => (labelWeight c p j b : ℂ))
  change (V * D * Vᴴ).charpoly = _
  rw [Matrix.charpoly_mul_comm_of_le _ _ (by simpa using hN), ← Matrix.mul_assoc, hV, one_mul,
    Matrix.charpoly_diagonal, Matrix.charpoly_diagonal]
  let f : B ⊕ Fin (d * e - Fintype.card B) → ℂ[X] :=
    fun b => Polynomial.X - Polynomial.C (↑(Sum.elim (labelWeight c p j) (fun _ => 0) b) : ℂ)
  change _ = ∏ k, f (sortedIndex c p hN j k)
  rw [(sortedIndex c p hN j).prod_comp, Fintype.prod_sum_type]
  simp [f, D, mul_comm]

private def eigOrder (d : ℕ) : Fin d ≃ Fin d :=
  (finCongr (Fintype.card_fin d).symm).trans (Fintype.equivOfCardEq (Fintype.card_fin _))

private def eig {E : Matrix (Fin d) (Fin d) ℂ} (h : E.IsHermitian) : Fin d → ℝ :=
  fun i => h.eigenvalues₀ (Fin.cast (Fintype.card_fin d).symm i)

private theorem eig_eq {E : Matrix (Fin d) (Fin d) ℂ} (h : E.IsHermitian) (i : Fin d) :
    eig h i = h.eigenvalues (eigOrder d i) := by
  simp [eig, eigOrder, Matrix.IsHermitian.eigenvalues]

private theorem eig_antitone {E : Matrix (Fin d) (Fin d) ℂ} (h : E.IsHermitian) :
    Antitone (eig h) :=
  fun _ _ hab => h.eigenvalues₀_antitone hab

private theorem eig_nonneg {E : Matrix (Fin d) (Fin d) ℂ} (h : E.PosSemidef) (i : Fin d) :
    0 ≤ eig h.isHermitian i := by
  rw [eig_eq]
  exact h.eigenvalues_nonneg _

private theorem lift_charpoly (E : Matrix (Fin d) (Fin d) ℂ) (hE : E.IsHermitian) (e : ℕ) :
    (E ⊗ₖ (1 : Matrix (Fin e) (Fin e) ℂ)).charpoly =
      (diagonal fun i : Fin (d * e) => (eig hE (finProdFinEquiv.symm i).1 : ℂ)).charpoly := by
  let u : Matrix (Fin d) (Fin d) ℂ := hE.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℂ := diagonal (RCLike.ofReal ∘ hE.eigenvalues)
  let I : Matrix (Fin e) (Fin e) ℂ := 1
  have hu : uᴴ * u = 1 := Unitary.coe_star_mul_self hE.eigenvectorUnitary
  have hD : E = u * D * uᴴ := by
    simpa [u, D, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hE.spectral_theorem
  calc
    (E ⊗ₖ I).charpoly = ((u ⊗ₖ I) * (D ⊗ₖ I) * (uᴴ ⊗ₖ I)).charpoly := by
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, ← hD]
      simp [I]
    _ = (D ⊗ₖ I).charpoly := by
      rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← mul_kronecker_mul, hu,
        show I * I = I by simp [I], Matrix.one_kronecker_one, one_mul]
    _ = _ := by
      have hdiag : D ⊗ₖ I = diagonal (fun a : Fin d × Fin e => (hE.eigenvalues a.1 : ℂ)) := by
        change diagonal (fun i => (hE.eigenvalues i : ℂ)) ⊗ₖ I = _
        simpa only [I, Matrix.diagonal_one, mul_one] using
          (diagonal_kronecker_diagonal (fun i => (hE.eigenvalues i : ℂ))
            (fun _ : Fin e => (1 : ℂ)))
      rw [hdiag, Matrix.charpoly_diagonal, Matrix.charpoly_diagonal]
      rw [← finProdFinEquiv.prod_comp (fun i : Fin (d * e) =>
        Polynomial.X - Polynomial.C (eig hE (finProdFinEquiv.symm i).1 : ℂ))]
      simp_rw [Equiv.symm_apply_apply, eig_eq]
      exact ((eigOrder d).prodCongr (Equiv.refl (Fin e))).prod_comp _ |>.symm

private theorem lift_eig_antitone {E : Matrix (Fin d) (Fin d) ℂ} (hE : E.IsHermitian) :
    Antitone (fun i : Fin (d * e) => eig hE (finProdFinEquiv.symm i).1) := by
  intro a b hab
  apply eig_antitone
  exact Nat.div_le_div_right hab

private theorem trace_lift_column (V : Matrix (Fin d × Fin e) B ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (b : B) :
    ((Vᴴ * (A ⊗ₖ (1 : Matrix (Fin e) (Fin e) ℂ))) * V) b b =
      (A * reducedColumn V b).trace := by
  rw [Matrix.mul_assoc, trace_mul_reducedColumn]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, dotProduct, Pi.star_apply,
    Matrix.mulVec, FiniteLabelRecordDilation.slice, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_comm

private theorem class_success_le (c : B → J) (p : B → ℝ)
    (hN : Fintype.card B ≤ d * e) (j : J)
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1)
    (E : Matrix (Fin d) (Fin d) ℂ) (hE : E.PosSemidef) :
    (∑ b, labelWeight c p j b * (E * reducedColumn V b).trace.re) ≤
      ∑ m, blockMass c p hN j m * eig hE.isHermitian m := by
  let D : Matrix B B ℂ := diagonal fun b => (labelWeight c p j b : ℂ)
  let A := V * D * Vᴴ
  let K := E ⊗ₖ (1 : Matrix (Fin e) (Fin e) ℂ)
  have hA : A.IsHermitian := by
    change Aᴴ = A
    simp only [A, conjTranspose_mul, conjTranspose_conjTranspose]
    have hD : Dᴴ = D := by
      apply Matrix.isHermitian_diagonal_iff.mpr
      intro i
      rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
    rw [hD, Matrix.mul_assoc]
  have hK : K.IsHermitian := by
    change Kᴴ = K
    simp only [K, conjTranspose_kronecker, hE.isHermitian.eq, conjTranspose_one]
  have htrace : (K * A).trace.re =
      ∑ b, labelWeight c p j b * (E * reducedColumn V b).trace.re := by
    rw [show K * A = (K * V * D) * Vᴴ by simp [A, Matrix.mul_assoc], trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp [D, K, trace, Matrix.diag, mul_diagonal, trace_lift_column, Complex.mul_re, mul_comm]
  have inequality := RHLinalg.vonNeumann_trace_ineq hK hA
  change (K * A).trace.re ≤ _ at inequality
  rw [htrace] at inequality
  have hCard : Fintype.card (Fin d × Fin e) = d * e := by simp
  have hEvA := eigenvalues_of_sorted_charpoly hA _ (decreasing_antitone _)
    hCard (weighted_charpoly c p hN j V hV)
  have hEvK := eigenvalues_of_sorted_charpoly hK _ (lift_eig_antitone hE.isHermitian)
    hCard (lift_charpoly E hE.isHermitian e)
  simp_rw [hEvA, hEvK] at inequality
  let f := fun k : Fin (d * e) =>
    eig hE.isHermitian (finProdFinEquiv.symm k).1 * sortedWeight c p hN j k
  have hs : (∑ i : Fin (Fintype.card (Fin d × Fin e)), f (finCongr hCard i)) = ∑ k, f k :=
    (finCongr hCard).sum_comp f
  change _ ≤ ∑ i, f (finCongr hCard i) at inequality
  rw [hs] at inequality
  have hp : (∑ k, f k) = ∑ m, blockMass c p hN j m * eig hE.isHermitian m := by
    rw [← finProdFinEquiv.sum_comp f, Fintype.sum_prod_type]
    simp only [f, Equiv.symm_apply_apply, blockMass, Finset.sum_mul, mul_comm, Finset.mul_sum]
  exact inequality.trans_eq hp

private theorem effect_le_one (E : J → Matrix (Fin d) (Fin d) ℂ)
    (hE : ∀ j, (E j).PosSemidef) (hSum : ∑ j, E j = 1) (j : J) :
    E j ≤ 1 := by
  rw [← hSum]
  exact Finset.single_le_sum (fun k _ => (hE k).nonneg) (Finset.mem_univ j)

private theorem eig_eq_quadratic {E : Matrix (Fin d) (Fin d) ℂ} (h : E.IsHermitian) (i : Fin d) :
    eig h i =
      let v := ⇑(h.eigenvectorBasis (eigOrder d i))
      (star v ⬝ᵥ (E *ᵥ v)).re :=
  (eig_eq h i).trans (h.eigenvalues_eq _)

private theorem eig_le_one {E : Matrix (Fin d) (Fin d) ℂ} (h : E.IsHermitian)
    (hLe : E ≤ 1) (i : Fin d) : eig h i ≤ 1 := by
  rw [eig_eq_quadratic]
  dsimp only
  let k := eigOrder d i
  let v := ⇑(h.eigenvectorBasis k)
  change (star v ⬝ᵥ (E *ᵥ v)).re ≤ 1
  have hNorm : star v ⬝ᵥ v = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      h.eigenvectorBasis.orthonormal.1 k]
    simp
  have ht := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hLe).dotProduct_mulVec_nonneg v)).1
  simpa only [Matrix.sub_mulVec, one_mulVec, dotProduct_sub, hNorm, Complex.sub_re,
    Complex.one_re, sub_nonneg] using ht

private theorem sum_eig {E : Matrix (Fin d) (Fin d) ℂ} (h : E.IsHermitian) :
    ∑ i, eig h i = E.trace.re := by
  rw [h.trace_eq_sum_eigenvalues, ← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply, Complex.ofReal_re, eig_eq]
  exact (eigOrder d).sum_comp _

private theorem success_le [Nonempty J] (c : B → J) (p : B → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hN : Fintype.card B ≤ d * e)
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1)
    (E : J → Matrix (Fin d) (Fin d) ℂ)
    (hE : ∀ j, (E j).PosSemidef) (hSum : ∑ j, E j = 1) :
    averageSuccess c p V E ≤ optimalSuccess c p hN := by
  let w := fun a : J × Fin d => blockMass c p hN a.1 a.2
  let lam := fun a : J × Fin d => eig (hE a.1).isHermitian a.2
  have hMass : ∑ a, lam a = (d : ℝ) := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ j, Complex.reCLM (E j).trace :=
        Finset.sum_congr rfl fun j _ => sum_eig (hE j).isHermitian
      _ = _ := by
        rw [← map_sum, ← Matrix.trace_sum, hSum, Matrix.trace_one]
        simp
  calc
    averageSuccess c p V E =
        ∑ j, ∑ b, labelWeight c p j b * (E j * reducedColumn V b).trace.re := by
      rw [Finset.sum_comm]
      simp [averageSuccess, labelWeight, ite_mul]
    _ ≤ ∑ j, ∑ m, blockMass c p hN j m * eig (hE j).isHermitian m :=
      Finset.sum_le_sum fun j _ => class_success_le c p hN j V hV (E j) (hE j)
    _ = ∑ a, w a * lam a := (Fintype.sum_prod_type (fun a => w a * lam a)).symm
    _ ≤ optimalSuccess c p hN :=
      weighted_sum_le_top w lam d _ (card_topSet w d) (topSet_top w d)
        (fun a => Finset.sum_nonneg fun t _ => sortedWeight_nonneg c p hp hN a.1 _)
        (fun a => eig_nonneg (hE a.1) a.2)
        (fun a => eig_le_one (hE a.1).isHermitian (effect_le_one E hE hSum a.1) a.2)
        hMass.le

private def position (c : B → J) (p : B → ℝ) (hN : Fintype.card B ≤ d * e) (j : J)
    (b : B) : Fin d × Fin e :=
  finProdFinEquiv.symm ((sortedIndex c p hN j).symm (.inl b))

private theorem position_injective (c : B → J) (p : B → ℝ)
    (hN : Fintype.card B ≤ d * e) (j : J) :
    Function.Injective (position c p hN j) :=
  finProdFinEquiv.symm.injective.comp ((sortedIndex c p hN j).symm.injective.comp Sum.inl_injective)

private theorem selected_mass (c : B → J) (p : B → ℝ) (hN : Fintype.card B ≤ d * e)
    (T : Finset (J × Fin d)) :
    (∑ a ∈ T, blockMass c p hN a.1 a.2) =
      ∑ b, if (c b, (position c p hN (c b) b).1) ∈ T then p b else 0 := by
  have hs : (∑ a ∈ T, blockMass c p hN a.1 a.2) =
      ∑ a : J × Fin d, if a ∈ T then blockMass c p hN a.1 a.2 else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [hs, Fintype.sum_prod_type]
  calc
    _ = ∑ j, ∑ k : Fin (d * e), if (j, (finProdFinEquiv.symm k).1) ∈ T
        then sortedWeight c p hN j k else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
      simp only [Equiv.symm_apply_apply, blockMass]
      exact Finset.sum_congr rfl fun m _ => by split <;> simp_all
    _ = ∑ j, ∑ b, if (j, (position c p hN j b).1) ∈ T then labelWeight c p j b else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← (sortedIndex c p hN j).symm.sum_comp, Fintype.sum_sum_type]
      have h (k : B ⊕ Fin (d * e - Fintype.card B)) :
          sortedWeight c p hN j ((sortedIndex c p hN j).symm k) =
            Sum.elim (labelWeight c p j) (fun _ => 0) k :=
        congrArg (Sum.elim (labelWeight c p j) (fun _ => 0))
          ((sortedIndex c p hN j).apply_symm_apply k)
      simp [h, position]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_eq_single (c b)]
      · simp [labelWeight]
      · intro j _ hj
        simp [labelWeight, Ne.symm hj]
      · simp

private theorem product_encoder (g : B ↪ Fin d × Fin e) :
    let V : Matrix (Fin d × Fin e) B ℂ := fun k b => if k = g b then 1 else 0
    Vᴴ * V = 1 := by
  let I : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ := 1
  change (I.submatrix id g)ᴴ * I.submatrix id g = 1
  rw [Matrix.conjTranspose_submatrix, show Iᴴ = I by simp [I], ← Matrix.submatrix_mul I I g id g Function.bijective_id]
  simpa [I] using Matrix.submatrix_one_embedding (α := ℂ) g

private theorem product_readout (g : B ↪ Fin d × Fin e) (r : Fin d → J) (b : B) (j : J) :
    let V : Matrix (Fin d × Fin e) B ℂ := fun k b => if k = g b then 1 else 0
    let E : Matrix (Fin d) (Fin d) ℂ := diagonal fun m => if r m = j then 1 else 0
    (E * reducedColumn V b).trace = if r (g b).1 = j then 1 else 0 := by
  intro V E
  rw [trace_mul_reducedColumn, Finset.sum_eq_single (g b).2]
  · simp only [E, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
    rw [Finset.sum_eq_single (g b).1]
    · have h : slice V b (g b).2 (g b).1 = 1 := ite_eq_left rfl
      simp [h]
    · intro m _ hm
      have h : slice V b (g b).2 m = 0 := ite_eq_right (fun h => hm (congrArg Prod.fst h))
      simp [h]
    · simp
  · intro t _ ht
    have h : slice V b t = 0 := by
      funext m
      exact ite_eq_right (fun h => ht (congrArg Prod.snd h))
    simp [h]
  · simp

private theorem attain [Nonempty J] (c : B → J) (p : B → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hN : Fintype.card B ≤ d * e) :
    ∃ (g : B ↪ Fin d × Fin e) (r : Fin d → J),
      let V : Matrix (Fin d × Fin e) B ℂ := fun k b => if k = g b then 1 else 0
      let E (j : J) : Matrix (Fin d) (Fin d) ℂ := diagonal fun m => if r m = j then 1 else 0
      Vᴴ * V = 1 ∧ (∀ j, (E j).PosSemidef) ∧ (∑ j, E j) = 1 ∧
        (∀ i j, E i * E j = if i = j then E i else 0) ∧
        averageSuccess c p V E = optimalSuccess c p hN := by
  let w := fun a : J × Fin d => blockMass c p hN a.1 a.2
  let T := topSet w d
  have hT : T.card = d := by
    rw [card_topSet, min_eq_left]
    calc
      d = 1 * d := (one_mul d).symm
      _ ≤ Fintype.card J * d := Nat.mul_le_mul_right _ Fintype.card_pos
      _ = _ := by simp
  let row : T ≃ Fin d := Finset.equivFinOfCardEq hT
  let P : Set B := {b | (c b, (position c p hN (c b) b).1) ∈ T}
  let pack : P ↪ Fin d × Fin e :=
    ⟨fun b => (row ⟨_, b.property⟩, (position c p hN (c b) b).2), by
      intro b b' h
      have hrow := congrArg Subtype.val (row.injective (congrArg Prod.fst h))
      have hc : c b.1 = c b'.1 := congrArg Prod.fst hrow
      apply Subtype.ext
      apply position_injective c p hN (c b.1)
      exact Prod.ext (by simpa only [← hc] using congrArg Prod.snd hrow)
        (by simpa only [← hc] using congrArg Prod.snd h)⟩
  obtain ⟨g, hg⟩ := extend_into_joint_basis P pack (by simpa using hN)
  let r : Fin d → J := fun m => (row.symm m).1.1
  let V : Matrix (Fin d × Fin e) B ℂ := fun k b => if k = g b then 1 else 0
  let E (j : J) : Matrix (Fin d) (Fin d) ℂ := diagonal fun m => if r m = j then 1 else 0
  have hV : Vᴴ * V = 1 := product_encoder g
  have hE (j : J) : (E j).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro m
    split <;> simp
  have hSum : ∑ j, E j = 1 := by
    ext m n
    by_cases h : m = n
    · subst n
      simp only [Matrix.sum_apply, E, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      simpa only [eq_comm] using (Finset.sum_ite_eq (s := Finset.univ) (a := r m)
        (b := fun _ => (1 : ℂ))).trans (ite_eq_left (Finset.mem_univ _))
    · simp [E, Matrix.sum_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  refine ⟨g, r, hV, hE, hSum, ?_, le_antisymm (success_le c p hp hN V hV E hE hSum) ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, Matrix.diagonal_mul_diagonal]
      congr 1
      funext m
      split <;> simp_all
    · rw [ite_eq_right hij, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
      congr 1
      funext m
      by_cases h : r m = i
      · simp [h, hij]
      · simp [h]
  · change (∑ a ∈ T, w a) ≤ averageSuccess c p V E
    rw [selected_mass]
    apply Finset.sum_le_sum
    intro b _
    change (if b ∈ P then p b else 0) ≤ p b * (E (c b) * reducedColumn V b).trace.re
    have hRead : (E (c b) * reducedColumn V b).trace =
        if r (g b).1 = c b then 1 else 0 := product_readout g r b (c b)
    rw [hRead]
    by_cases hb : b ∈ P
    · have hr : r (g b).1 = c b := by
        rw [hg ⟨b, hb⟩]
        change (row.symm (row ⟨_, hb⟩)).1.1 = _
        rw [Equiv.symm_apply_apply]
      simp [hb, hr]
    · split_ifs with hr <;> simp [hb, hp]

private theorem trace_effect_nonneg (V : Matrix (Fin d × Fin e) B ℂ) (b : B)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    0 ≤ (A * reducedColumn V b).trace := by
  rw [trace_mul_reducedColumn]
  exact Finset.sum_nonneg fun t _ => hA.dotProduct_mulVec_nonneg _

private theorem trace_effect_le_one (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1)
    (b : B) {A : Matrix (Fin d) (Fin d) ℂ} (hA : A ≤ 1) :
    (A * reducedColumn V b).trace ≤ 1 := by
  have h := trace_effect_nonneg V b (Matrix.le_iff.mp hA)
  rwa [sub_mul, trace_sub, one_mul, reducedColumn_trace V hV, sub_nonneg] at h

private theorem success_one_iff [Nonempty J] (c : B → J) (p : B → ℝ)
    (hp : ∀ b, 0 ≤ p b) (hpSum : ∑ b, p b = 1) (he : 0 < e)
    (hN : Fintype.card B ≤ d * e) :
    optimalSuccess c p hN = 1 ↔
      memorySlots (fun b : {b : B | 0 < p b} => c b.1) e ≤ d := by
  let P : Set B := {b | 0 < p b}
  let label : P → J := fun b => c b.1
  have hLe (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1)
      (E : J → Matrix (Fin d) (Fin d) ℂ) (hE : ∀ j, (E j).PosSemidef)
      (hSum : ∑ j, E j = 1) (b : B) : (E (c b) * reducedColumn V b).trace.re ≤ 1 := by
    have h := trace_effect_le_one V hV b (effect_le_one E hE hSum (c b))
    exact h.1
  obtain ⟨g, r, hV, hE, hSum, _, hOpt⟩ := attain c p hp hN
  let V : Matrix (Fin d × Fin e) B ℂ := fun k b => if k = g b then 1 else 0
  let E (j : J) : Matrix (Fin d) (Fin d) ℂ := diagonal fun m => if r m = j then 1 else 0
  change averageSuccess c p V E = optimalSuccess c p hN at hOpt
  constructor
  · intro h
    rw [← hOpt] at h
    have hz : (∑ b, p b * (1 - (E (c b) * reducedColumn V b).trace.re)) = 0 := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hpSum]
      exact sub_eq_zero.mpr h.symm
    have hread (b : P) : (E (label b) * reducedColumn V b).trace = 1 := by
      have hProd := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
        mul_nonneg (hp b) (sub_nonneg.mpr (hLe V hV E hE hSum b)))).mp hz b.1 (mem_univ _)
      have hr := sub_eq_zero.mp ((mul_eq_zero.mp hProd).resolve_left (ne_of_gt b.property))
      have hi := (Complex.nonneg_iff.mp (trace_effect_nonneg V b.1 (hE (label b)))).2
      exact Complex.ext hr.symm (by simpa using hi.symm)
    let E' : Option J → Matrix (Fin d) (Fin d) ℂ := fun j => j.elim 0 E
    have hPerfect : HasPerfectLabelRecord label d e :=
      ⟨V, E', hV, (by
          intro j
          cases j with
          | none => exact Matrix.PosSemidef.zero
          | some j => exact hE j),
        (by simpa [E', Fintype.sum_option] using hSum), hread⟩
    exact ((perfectLabelRecord_iff label he).mp hPerfect).2
  · intro hSlots
    obtain ⟨V₀, E₀, hV₀, hE₀, hSum₀, hRead₀⟩ :=
      (perfectLabelRecord_iff label he).mpr ⟨hN, hSlots⟩
    let j₀ : J := Classical.choice ‹Nonempty J›
    let F (j : J) := E₀ (some j) + if j = j₀ then E₀ none else 0
    have hF (j : J) : (F j).PosSemidef := by
      apply (hE₀ (some j)).add
      split
      · exact hE₀ none
      · exact Matrix.PosSemidef.zero
    have hFSum : ∑ j, F j = 1 := by
      rw [Fintype.sum_option] at hSum₀
      simpa [F, Finset.sum_add_distrib, add_comm] using hSum₀
    have hScore : averageSuccess c p V₀ F = 1 := by
      rw [← hpSum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : 0 < p b
      · have hr := hRead₀ (⟨b, hb⟩ : P)
        change (E₀ (some (c b)) * reducedColumn V₀ b).trace = 1 at hr
        have hExtra : (if c b = j₀ then E₀ none else 0).PosSemidef := by
          split
          · exact hE₀ none
          · exact Matrix.PosSemidef.zero
        have hLow : 1 ≤ (F (c b) * reducedColumn V₀ b).trace.re := by
          have h := (Complex.nonneg_iff.mp (trace_effect_nonneg V₀ b hExtra)).1
          simpa [F, add_mul, trace_add, hr] using h
        rw [le_antisymm (hLe V₀ hV₀ F hF hFSum b) hLow, mul_one]
      · simp [le_antisymm (le_of_not_gt hb) (hp b)]
    apply le_antisymm _ (hScore ▸ success_le c p hp hN V₀ hV₀ F hF hFSum)
    rw [← hOpt, ← hpSum]
    exact Finset.sum_le_sum fun b _ => mul_le_of_le_one_right (hp b) (hLe V hV E hE hSum b)

/-- The exact weighted optimum, attained by distinct product cells and an
orthogonal projective coarse-graining of the memory coordinates. -/
theorem weightedLabelRecord_optimum [Nonempty J] (c : B → J) (p : B → ℝ)
    (hp : ∀ b, 0 ≤ p b) (hpSum : ∑ b, p b = 1) (he : 0 < e)
    (hN : Fintype.card B ≤ d * e) :
    (∀ (V : Matrix (Fin d × Fin e) B ℂ) (E : J → Matrix (Fin d) (Fin d) ℂ),
      Vᴴ * V = 1 → (∀ j, (E j).PosSemidef) → (∑ j, E j) = 1 →
        averageSuccess c p V E ≤ optimalSuccess c p hN) ∧
    (∃ (g : B ↪ Fin d × Fin e) (r : Fin d → J),
      let V : Matrix (Fin d × Fin e) B ℂ := fun k b => if k = g b then 1 else 0
      let E (j : J) : Matrix (Fin d) (Fin d) ℂ := diagonal fun m => if r m = j then 1 else 0
      Vᴴ * V = 1 ∧ (∀ j, (E j).PosSemidef) ∧ (∑ j, E j) = 1 ∧
        (∀ i j, E i * E j = if i = j then E i else 0) ∧
        averageSuccess c p V E = optimalSuccess c p hN) ∧
    (optimalSuccess c p hN = 1 ↔ memorySlots (fun b : {b : B | 0 < p b} => c b.1) e ≤ d) :=
  ⟨fun V E hV hE hSum => success_le c p hp hN V hV E hE hSum,
    attain c p hp hN, success_one_iff c p hp hpSum he hN⟩

#print axioms weightedLabelRecord_optimum

end
end D5.S3.Quantum.Measurements.WeightedLabelRecordDilation
