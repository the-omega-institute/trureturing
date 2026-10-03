/- GID: D5/S3/Observer/Linear/GradedCongruenceSpectrum
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GradedCongruenceSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform graded asymptotics for the actual canonical spectrum of a positive normalized congruence. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open scoped BigOperators Polynomial
namespace D5.S3.Observer.Linear

/--
Source-bound abstract interface for the normalized-congruence spectrum step.
The complete theorem-local telescope derives coefficient powers from the actual
principal minors, identifies them with the same matrix's canonical decreasing
`eigenvalues₀`, and cancels adjacent positive prefix products. The physical
Gramian and moment applications remain separate source bridges.
-/
theorem graded_congruence_spectrum {n : ℕ} (H : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℕ)
    (hw : Monotone w)
    (hH : Filter.Tendsto H (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds H₀))
    (hH₀ : H₀.PosDef)
    (hGpos : ∀ T, 0 < T →
      (Matrix.diagonal (fun i : Fin n => T ^ w i * Real.sqrt T) * H T *
        Matrix.diagonal (fun i : Fin n => T ^ w i * Real.sqrt T)).PosDef) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ T i (hT : 0 < T), T < δ →
        c * T ^ (2 * w i + 1) ≤
            (hGpos T hT).isHermitian.eigenvalues₀ ((Fin.castOrderIso (Fintype.card_fin n)).symm i) ∧
        (hGpos T hT).isHermitian.eigenvalues₀ ((Fin.castOrderIso (Fintype.card_fin n)).symm i) ≤ C * T ^ (2 * w i + 1) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, by simp⟩
  let q : Fin n → ℕ := fun i => 2 * w i + 1
  let d : ℝ → Fin n → ℝ := fun T i => T ^ w i * Real.sqrt T
  let G : ℝ → Matrix (Fin n) (Fin n) ℝ := fun T =>
    Matrix.diagonal (d T) * H T * Matrix.diagonal (d T)
  have hminor : ∃ δ : ℝ, 0 < δ ∧ ∀ T, 0 < T → T < δ →
      ∀ s : Finset (Fin n),
        (Matrix.det (H₀.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n))) / 2 <
          Matrix.det ((H T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) ∧
        Matrix.det ((H T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) <
          |Matrix.det (H₀.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n))| + 1 := by
    have hev : ∀ s : Finset (Fin n), ∀ᶠ T in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Matrix.det (H₀.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n))) / 2 <
            Matrix.det ((H T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) ∧
          Matrix.det ((H T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) <
            |Matrix.det (H₀.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n))| + 1 := by
      intro s
      let e : s → Fin n := Subtype.val
      have he : Function.Injective e := Subtype.val_injective
      have hd : 0 < (H₀.submatrix e e).det := (hH₀.submatrix he).det_pos
      have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => (M.submatrix e e).det) :=
        (continuous_id.matrix_submatrix e e).matrix_det
      have hl : Filter.Tendsto (fun T => ((H T).submatrix e e).det)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((H₀.submatrix e e).det)) :=
        hc.tendsto _ |>.comp hH
      have hn : Set.Ioo ((H₀.submatrix e e).det / 2)
          (|(H₀.submatrix e e).det| + 1) ∈ nhds ((H₀.submatrix e e).det) := by
        apply IsOpen.mem_nhds isOpen_Ioo
        constructor
        · linarith
        · exact lt_of_le_of_lt (le_abs_self _) (lt_add_of_pos_right _ zero_lt_one)
      simpa [e] using hl.eventually hn
    have hall := Filter.eventually_all.2 hev
    rcases Metric.mem_nhdsWithin_iff.mp hall with ⟨ε, hε, hball⟩
    refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
    intro T hT hTδ s
    apply hball
    constructor
    · have hTε : T < ε := lt_of_lt_of_le hTδ (min_le_left ε 1)
      simpa [Real.dist_eq, abs_of_pos hT] using hTε
    · exact hT
  rcases hminor with ⟨δ₀, hδ₀, hminor⟩
  let U : ℝ := max 1 (∑ s : Finset (Fin n),
      (|(Matrix.det (H₀.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)))| + 1))
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcommon : 0 < min δ₀ 1 := lt_min hδ₀ zero_lt_one
  let all : Finset (Finset (Fin n)) := Finset.univ
  let vals : Finset ℝ := all.image (fun s : Finset (Fin n) =>
    (Matrix.det (H₀.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n))) / 2)
  have hall : all.Nonempty := by exact ⟨∅, Finset.mem_univ _⟩
  have hvals : vals.Nonempty := by
    rcases hall with ⟨s, hs⟩
    exact ⟨_, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩
  let m₀ : ℝ := vals.min' hvals
  have hm₀pos : 0 < m₀ := by
    have hm := Finset.min'_mem vals hvals
    rcases Finset.mem_image.mp hm with ⟨s, hs, heq⟩
    change 0 < vals.min' hvals
    rw [← heq]
    have hd := (hH₀.submatrix (e := (Subtype.val : s → Fin n)) Subtype.val_injective).det_pos
    linarith
  have hm₀le : ∀ s : Finset (Fin n), m₀ ≤
      (Matrix.det (H₀.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n))) / 2 := by
    intro s
    exact Finset.min'_le vals _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)
  have hdetbounds : ∀ (T : ℝ) (s : Finset (Fin n)), 0 < T → T < min δ₀ 1 →
      0 < Matrix.det ((H T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) ∧
      Matrix.det ((H T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) ≤ U := by
    intro T s hT hTδ
    have hm := hminor T hT (lt_of_lt_of_le hTδ (min_le_left δ₀ 1)) s
    constructor
    · have hd0 := hm₀le s
      linarith
    · have hsum : |Matrix.det (H₀.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n))| + 1 ≤
          ∑ t : Finset (Fin n), (|Matrix.det (H₀.submatrix (Subtype.val : t → Fin n) (Subtype.val : t → Fin n))| + 1) := by
        change |Matrix.det (H₀.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n))| + 1 ≤
          (Finset.univ : Finset (Finset (Fin n))).sum (fun t =>
            |Matrix.det (H₀.submatrix (Subtype.val : t → Fin n) (Subtype.val : t → Fin n))| + 1)
        exact Finset.single_le_sum
          (f := fun t : Finset (Fin n) =>
            |Matrix.det (H₀.submatrix (Subtype.val : t → Fin n) (Subtype.val : t → Fin n))| + 1)
          (s := (Finset.univ : Finset (Finset (Fin n))))
          (fun t ht => by positivity) (Finset.mem_univ s)
      change Matrix.det ((H T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) ≤
        max 1 (∑ t : Finset (Fin n), (|Matrix.det (H₀.submatrix (Subtype.val : t → Fin n) (Subtype.val : t → Fin n))| + 1))
      exact le_trans (le_of_lt hm.2) (le_trans hsum (le_max_right _ _))
  have hKpos : 0 < (Fintype.card (Finset (Fin n)) : ℝ) := by positivity
  have hcoeff_bounds : ∃ m M δ : ℝ, 0 < m ∧ 0 < M ∧ 0 < δ ∧
      ∀ (T : ℝ) (k : Fin (n+1)), 0 < T → T < δ →
        m * T ^ (∑ j : Fin k, q (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) ≤
          (((1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
              (Polynomial.X : Polynomial ℝ) • (G T).map Polynomial.C).det).coeff k.val ∧
        (((1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
              (Polynomial.X : Polynomial ℝ) • (G T).map Polynomial.C).det).coeff k.val ≤
          M * T ^ (∑ j : Fin k, q (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) := by
    refine ⟨m₀, (Fintype.card (Finset (Fin n)) : ℝ) * U, min δ₀ 1, hm₀pos,
      mul_pos hKpos hU, hcommon, ?_⟩
    intro T k hT hTδ
    let hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    let s₀ : Finset (Fin n) := (Finset.univ.map (Fin.castLEOrderEmb hk).toEmbedding)
    have hs₀ : s₀.card = k.val := by simp [s₀]
    have hcoeff := Matrix.coeff_det_one_add_X_smul_eq_sum_minors (G T) k.val
    rw [hcoeff]
    have hterm : ∀ s ∈ Finset.powersetCard k.val (Finset.univ : Finset (Fin n)),
        0 ≤ (((G T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det) := by
      intro s hs
      let e : s → Fin n := Subtype.val
      let dd : Fin n → ℝ := d T
      have hscale : ((G T).submatrix e e).det =
          (∏ i : s, dd (e i)) ^ 2 * ((H T).submatrix e e).det := by
        rw [show G T = (Matrix.diagonal dd * H T) * Matrix.diagonal dd by rfl]
        have hr : (((Matrix.diagonal dd * H T) * Matrix.diagonal dd).submatrix e e) =
            (Matrix.diagonal (dd ∘ e) * (H T).submatrix e e) * Matrix.diagonal (dd ∘ e) := by
          ext i j; simp [Matrix.mul_diagonal, e]
        rw [hr, Matrix.det_mul, Matrix.det_mul]
        simp only [Matrix.det_diagonal]
        simp [Function.comp_def, e]
        ring
      rw [hscale]
      have hdetpos := (hdetbounds T s hT hTδ).1
      positivity
    have hfirst : s₀ ∈ Finset.powersetCard k.val (Finset.univ : Finset (Fin n)) := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨by simp [s₀], hs₀⟩
    have hfirstpos := hterm s₀ hfirst
    have hscale : ∀ s : Finset (Fin n),
        (((G T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det) =
          T ^ (∑ i ∈ s, q i) * ((H T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det := by
      intro s
      let e : s → Fin n := Subtype.val
      let dd : Fin n → ℝ := d T
      have hright : (((Matrix.diagonal dd * H T) * Matrix.diagonal dd).submatrix e e) =
          (Matrix.diagonal (dd ∘ e) * (H T).submatrix e e) * Matrix.diagonal (dd ∘ e) := by
        ext i j; simp [Matrix.mul_diagonal, e]
      rw [show G T = (Matrix.diagonal dd * H T) * Matrix.diagonal dd by rfl, hright,
        Matrix.det_mul, Matrix.det_mul]
      simp only [Matrix.det_diagonal]
      have hpow : (∏ i : s, (T ^ w i.1 * Real.sqrt T)) ^ 2 = T ^ (∑ i ∈ s, q i) := by
        rw [Finset.prod_mul_distrib, mul_pow]
        have hp : (∏ i : s, T ^ (w i.1)) ^ 2 = T ^ (∑ i ∈ s, 2 * w i) := by
          rw [← Finset.prod_pow]
          simp only [← pow_mul]
          rw [Finset.prod_pow_eq_pow_sum]
          congr 1
          simpa [Nat.mul_comm] using (Finset.sum_attach s (fun x => w x * 2))
        rw [hp]
        rw [← Finset.prod_pow]
        simp_rw [Real.sq_sqrt (le_of_lt hT)]
        rw [Finset.prod_const]
        rw [← pow_add]
        congr 1
        simp [q, Finset.sum_add_distrib, Nat.mul_comm]
      calc
        (∏ i ∈ s.attach, (d T i)) * ((H T).submatrix e e).det * ∏ i ∈ s.attach, (d T i) =
            (∏ i : s, (T ^ w i.1 * Real.sqrt T)) ^ 2 * ((H T).submatrix e e).det := by
              simp [d, e]; ring
        _ = T ^ (∑ i ∈ s, q i) * ((H T).submatrix e e).det := by rw [hpow]
    have hfirstscale := hscale s₀
    have hfirstlower : m₀ * T ^ (∑ j : Fin k, q (Fin.castLE hk j)) ≤
        ((G T).submatrix (Subtype.val : s₀ → Fin n) (Subtype.val : s₀ → Fin n)).det := by
      have hm_actual : m₀ ≤
          (Matrix.det ((H T).submatrix (Subtype.val : s₀ → Fin n) (Subtype.val : s₀ → Fin n))) := by
        have hm0 := hm₀le s₀
        have hlim := hminor T hT (lt_of_lt_of_le hTδ (min_le_left δ₀ 1)) s₀
        exact le_of_lt (lt_of_le_of_lt hm0 hlim.1)
      have hsum_eq : (∑ i ∈ s₀, q i) = ∑ j : Fin k, q (Fin.castLE hk j) := by
        rw [show s₀ = Finset.univ.map (Fin.castLEOrderEmb hk).toEmbedding by rfl]
        rw [Finset.sum_map]
        rfl
      calc
        m₀ * T ^ (∑ j : Fin k, q (Fin.castLE hk j)) =
            T ^ (∑ j : Fin k, q (Fin.castLE hk j)) * m₀ := by ring
        _ ≤ T ^ (∑ j : Fin k, q (Fin.castLE hk j)) *
            Matrix.det ((H T).submatrix (Subtype.val : s₀ → Fin n) (Subtype.val : s₀ → Fin n)) :=
          mul_le_mul_of_nonneg_left hm_actual (by positivity)
        _ = ((G T).submatrix (Subtype.val : s₀ → Fin n) (Subtype.val : s₀ → Fin n)).det := by
          rw [hfirstscale, hsum_eq]
    have hcoeflower : m₀ * T ^ (∑ j : Fin k, q (Fin.castLE hk j)) ≤
        ∑ s ∈ Finset.powersetCard k.val (Finset.univ : Finset (Fin n)),
          (((G T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det) := by
      exact le_trans hfirstlower (Finset.single_le_sum (fun s hs => hterm s hs) hfirst)
    have htermupper : ∀ s ∈ Finset.powersetCard k.val (Finset.univ : Finset (Fin n)),
        (((G T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det) ≤
          U * T ^ (∑ j : Fin k, q (Fin.castLE hk j)) := by
      intro s hs
      have hscard : s.card = k.val := (Finset.mem_powersetCard.mp hs).2
      have hgrade : (∑ j : Fin k, q (Fin.castLE hk j)) ≤ ∑ i ∈ s, q i := by
        let f : Fin k ↪o Fin n := s.orderEmbOfFin hscard
        have hf : ∀ j : Fin k, (j : ℕ) ≤ (f j : ℕ) := by
          intro j
          have hf_nat : ∀ r (hr : r < k.val), r ≤ (f ⟨r, hr⟩ : ℕ) := by
            intro r hr
            induction r with
            | zero => exact Nat.zero_le _
            | succ r ih =>
                have hr' : r < k.val := Nat.lt_of_succ_lt hr
                have hlt : f ⟨r, hr'⟩ < f ⟨r + 1, hr⟩ := by
                  apply f.strictMono
                  exact Fin.mk_lt_mk.mpr (by omega)
                have hi := ih hr'
                omega
          exact hf_nat j.val j.isLt
        have hwf : ∀ j : Fin k, w (Fin.castLE hk j) ≤ w (f j) := by
          intro j
          exact hw (hf j)
        rw [← Finset.map_orderEmbOfFin_univ s hscard]
        rw [Finset.sum_map]
        apply Finset.sum_le_sum
        intro j hj
        exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hwf j)) 1
      have hpow : T ^ (∑ i ∈ s, q i) ≤ T ^ (∑ j : Fin k, q (Fin.castLE hk j)) :=
        pow_le_pow_of_le_one (le_of_lt hT) (le_trans (le_of_lt hTδ) (min_le_right _ _)) hgrade
      rw [hscale s]
      calc
        T ^ (∑ i ∈ s, q i) * Matrix.det ((H T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) ≤
            T ^ (∑ i ∈ s, q i) * U :=
          mul_le_mul_of_nonneg_left (hdetbounds T s hT hTδ).2 (by positivity)
        _ ≤ T ^ (∑ j : Fin k, q (Fin.castLE hk j)) * U :=
          mul_le_mul_of_nonneg_right hpow hU.le
        _ = U * T ^ (∑ j : Fin k, q (Fin.castLE hk j)) := by ring
    have hcoefupper :
        ∑ s ∈ Finset.powersetCard k.val (Finset.univ : Finset (Fin n)),
          (((G T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det) ≤
          (Fintype.card (Finset (Fin n)) : ℝ) * U *
            T ^ (∑ j : Fin k, q (Fin.castLE hk j)) := by
      calc
        _ ≤ ∑ s ∈ Finset.powersetCard k.val (Finset.univ : Finset (Fin n)),
            U * T ^ (∑ j : Fin k, q (Fin.castLE hk j)) := by
              apply Finset.sum_le_sum
              intro s hs
              exact htermupper s hs
        _ = (Finset.powersetCard k.val (Finset.univ : Finset (Fin n))).card *
              (U * T ^ (∑ j : Fin k, q (Fin.castLE hk j))) := by simp
        _ ≤ (Fintype.card (Finset (Fin n)) : ℝ) *
              (U * T ^ (∑ j : Fin k, q (Fin.castLE hk j))) := by
              gcongr
              exact Finset.card_le_univ (Finset.univ.powersetCard k.val : Finset (Finset (Fin n)))
        _ = (Fintype.card (Finset (Fin n)) : ℝ) * U *
              T ^ (∑ j : Fin k, q (Fin.castLE hk j)) := by ring
    constructor
    · exact hcoeflower
    · exact hcoefupper
  have hbridge : ∀ (T : ℝ) (hT : 0 < T) (k : Fin (n+1)),
      (((1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
          (Polynomial.X : Polynomial ℝ) • (G T).map Polynomial.C).det).coeff k.val =
        ∑ s ∈ Finset.univ.powersetCard k.val,
          ∏ i : s, (hGpos T hT).isHermitian.eigenvalues₀
            ((Fin.castOrderIso (Fintype.card_fin n)).symm i.1) := by
    intro T hT k
    let hG : Matrix.IsHermitian (G T) := (hGpos T hT).isHermitian
    let q : Fin (Fintype.card (Fin n)) ≃o Fin n :=
      Fin.castOrderIso (Fintype.card_fin n)
    let e : Fin n ≃ Fin (Fintype.card (Fin n)) :=
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
    let qinv : Fin n ≃ Fin (Fintype.card (Fin n)) := q.symm.toEquiv
    let D : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.diagonal (fun i => hG.eigenvalues₀ (qinv i))
    have hchar : (G T).charpoly = D.charpoly := by
      rw [hG.charpoly_eq, Matrix.charpoly_diagonal]
      have he := Equiv.prod_comp e (fun j : Fin (Fintype.card (Fin n)) =>
        (Polynomial.X - Polynomial.C (hG.eigenvalues₀ j)))
      have hq := Equiv.prod_comp qinv (fun j : Fin (Fintype.card (Fin n)) =>
        (Polynomial.X - Polynomial.C (hG.eigenvalues₀ j)))
      simpa [Matrix.IsHermitian.eigenvalues, D, qinv, e] using he.trans hq.symm
    have hminorD : ∀ s : Finset (Fin n),
        (D.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det =
          ∏ i : s, hG.eigenvalues₀ (qinv i.1) := by
      intro s
      change Matrix.det ((Matrix.diagonal (fun i => hG.eigenvalues₀ (qinv i))).submatrix
        (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) = _
      rw [Matrix.submatrix_diagonal _ _ Subtype.val_injective, Matrix.det_diagonal]
      rfl
    have hsigned :
        (-1 : ℝ)^k.val * (∑ s ∈ Finset.univ.powersetCard k.val,
          ((G T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det) =
        (-1 : ℝ)^k.val * (∑ s ∈ Finset.univ.powersetCard k.val,
          ∏ i : s, hG.eigenvalues₀ (qinv i.1)) := by
      calc
        _ = (G T).charpoly.coeff (Fintype.card (Fin n) - k.val) :=
          (Matrix.charpoly_coeff_eq_sum_minors (G T) k.val (by simpa using (Nat.le_of_lt_succ k.isLt))).symm
        _ = D.charpoly.coeff (Fintype.card (Fin n) - k.val) := by rw [hchar]
        _ = (-1 : ℝ)^k.val * (∑ s ∈ Finset.univ.powersetCard k.val,
            (D.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det) :=
          Matrix.charpoly_coeff_eq_sum_minors D k.val (by simpa using (Nat.le_of_lt_succ k.isLt))
        _ = _ := by simp_rw [hminorD]
    have hsums :
        (∑ s ∈ Finset.univ.powersetCard k.val,
          ((G T).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det) =
        ∑ s ∈ Finset.univ.powersetCard k.val,
          ∏ i : s, hG.eigenvalues₀ (qinv i.1) := by
      exact (mul_left_cancel₀ (pow_ne_zero k.val (by norm_num)) hsigned)
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    simpa [hG, q, qinv] using hsums
  have hprefix : ∀ (T : ℝ) (hT : 0 < T) (k : Fin (n+1)),
      (∏ j : Fin k, (hGpos T hT).isHermitian.eigenvalues₀
        ((Fin.castOrderIso (Fintype.card_fin n)).symm (Fin.castLE (Nat.le_of_lt_succ k.isLt) j))) ≤
        (((1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
          (Polynomial.X : Polynomial ℝ) • (G T).map Polynomial.C).det).coeff k.val ∧
      (((1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
          (Polynomial.X : Polynomial ℝ) • (G T).map Polynomial.C).det).coeff k.val ≤
        (Fintype.card (Finset (Fin n)) : ℝ) *
          (∏ j : Fin k, (hGpos T hT).isHermitian.eigenvalues₀
            ((Fin.castOrderIso (Fintype.card_fin n)).symm (Fin.castLE (Nat.le_of_lt_succ k.isLt) j))) := by
    intro T hT k
    let hG : Matrix.IsHermitian (G T) := (hGpos T hT).isHermitian
    let q : Fin (Fintype.card (Fin n)) ≃o Fin n :=
      Fin.castOrderIso (Fintype.card_fin n)
    let vals : Fin n → ℝ := fun i => hG.eigenvalues₀ (q.symm i)
    have hvals : ∀ i, 0 ≤ vals i := by
      intro i
      let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
        Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
      have hp := (hGpos T hT).isHermitian.posDef_iff_eigenvalues_pos.mp (hGpos T hT) (e (q.symm i))
      have hp0 : 0 < hG.eigenvalues₀ (q.symm i) := by
        simpa [Matrix.IsHermitian.eigenvalues, e] using hp
      exact hp0.le
    have hanti : Antitone vals := by
      intro a b hab
      exact hG.eigenvalues₀_antitone (q.symm.monotone hab)
    have hsand : ∀ s : Finset (Fin n), s.card = k.val →
        (∏ i ∈ s, vals i) ≤ ∏ j : Fin k, vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
      intro s hs
      let f : Fin k ↪o Fin n := s.orderEmbOfFin hs
      have hf : ∀ j : Fin k, (j : ℕ) ≤ (f j : ℕ) := by
        intro j
        have hf_nat : ∀ r (hr : r < k.val), r ≤ (f ⟨r, hr⟩ : ℕ) := by
          intro r hr
          induction r with
          | zero => exact Nat.zero_le _
          | succ r ih =>
              have hr' : r < k.val := Nat.lt_of_succ_lt hr
              have hlt : f ⟨r, hr'⟩ < f ⟨r + 1, hr⟩ := by
                apply f.strictMono
                exact Fin.mk_lt_mk.mpr (by omega)
              have hi := ih hr'
              omega
        exact hf_nat j.val j.isLt
      have hp : ∀ j : Fin k, vals (f j) ≤ vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
        intro j
        apply hanti
        exact hf j
      rw [← Finset.map_orderEmbOfFin_univ s hs]
      rw [Finset.prod_map]
      exact Finset.prod_le_prod (fun j _ => hvals (f j)) (fun j _ => hp j)
    have hsand' : ∀ s : Finset (Fin n), s.card = k.val →
        (∏ i : s, vals i.1) ≤ ∏ j : Fin k, vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
      intro s hs
      rw [Finset.univ_eq_attach s, Finset.prod_attach]
      exact hsand s hs
    have heq :
        (((1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
          (Polynomial.X : Polynomial ℝ) • (G T).map Polynomial.C).det).coeff k.val =
          ∑ s ∈ Finset.univ.powersetCard k.val,
            ∏ i : s, vals i.1 := by
      simpa [vals, q, hG] using hbridge T hT k
    have hnonneg : ∀ s ∈ Finset.univ.powersetCard k.val,
        0 ≤ ∏ i : s, vals i.1 := by
      intro s hs
      exact Finset.prod_nonneg (fun i _ => hvals i.1)
    let s₀ : Finset (Fin n) := Finset.univ.map
      (Fin.castLEOrderEmb (Nat.le_of_lt_succ k.isLt)).toEmbedding
    have hs₀ : s₀.card = k.val := by simp [s₀]
    have hmem₀ : s₀ ∈ Finset.univ.powersetCard k.val := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨by simp [s₀], hs₀⟩
    have hprod₀ : (∏ i : s₀, vals i.1) =
        ∏ j : Fin k, vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
      rw [Finset.univ_eq_attach s₀]
      rw [Finset.prod_attach]
      rw [show s₀ = Finset.univ.map (Fin.castLEOrderEmb (Nat.le_of_lt_succ k.isLt)).toEmbedding by rfl]
      rw [Finset.prod_map]
      rfl
    have hlower :
        (∏ j : Fin k, vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) ≤
          ∑ s ∈ Finset.univ.powersetCard k.val, ∏ i : s, vals i.1 := by
      rw [← hprod₀]
      exact Finset.single_le_sum hnonneg hmem₀
    have hupper :
        (∑ s ∈ Finset.univ.powersetCard k.val, ∏ i : s, vals i.1) ≤
          (Fintype.card (Finset (Fin n)) : ℝ) *
            (∏ j : Fin k, vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) := by
      calc
        _ ≤ ∑ s ∈ Finset.univ.powersetCard k.val,
            (∏ j : Fin k, vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) := by
              apply Finset.sum_le_sum
              intro s hs
              exact hsand' s (Finset.mem_powersetCard.mp hs).2
        _ = ((Finset.univ.powersetCard k.val).card : ℝ) *
            (∏ j : Fin k, vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              rfl
        _ ≤ (Fintype.card (Finset (Fin n)) : ℝ) *
            (∏ j : Fin k, vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) := by
              have hc_nat :
                  (Finset.powersetCard k.val (Finset.univ : Finset (Fin n))).card ≤
                    Fintype.card (Finset (Fin n)) := by
                exact Finset.card_le_univ (Finset.powersetCard k.val (Finset.univ : Finset (Fin n)))
              have hc : ((Finset.powersetCard k.val (Finset.univ : Finset (Fin n))).card : ℝ) ≤
                  (Fintype.card (Finset (Fin n)) : ℝ) := by
                exact_mod_cast hc_nat
              have hp : 0 ≤ ∏ j : Fin k, vals (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) :=
                Finset.prod_nonneg (fun j _ => hvals _)
              convert mul_le_mul_of_nonneg_right hc hp using 1
    exact ⟨by simpa [heq, vals, q, hG] using hlower,
      by simpa [heq, vals, q, hG] using hupper⟩
  rcases hcoeff_bounds with ⟨m₁, M₁, δ₁, hm₁, hM₁, hδ₁, hcb⟩
  let K : ℝ := (Fintype.card (Finset (Fin n)) : ℝ)
  have hK : 0 < K := by dsimp [K]; exact_mod_cast hKpos
  let c : ℝ := m₁ / (K * M₁)
  let C : ℝ := K * M₁ / m₁
  have hc : 0 < c := div_pos hm₁ (mul_pos hK hM₁)
  have hC : 0 < C := div_pos (mul_pos hK hM₁) hm₁
  refine ⟨c, C, min δ₁ 1, hc, hC, lt_min hδ₁ zero_lt_one, ?_⟩
  intro T i hT hTδ
  let hG : Matrix.IsHermitian (G T) := (hGpos T hT).isHermitian
  let lam : Fin n → ℝ := fun j => hG.eigenvalues₀
    ((Fin.castOrderIso (Fintype.card_fin n)).symm j)
  let P : Fin (n+1) → ℝ := fun k =>
    ∏ j : Fin k, lam (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
  let A : Fin (n+1) → ℕ := fun k =>
    ∑ j : Fin k, q (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
  have hlam : ∀ j, 0 < lam j := by
    intro j
    let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
      Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
    have hp := (hGpos T hT).isHermitian.posDef_iff_eigenvalues_pos.mp (hGpos T hT) (e ((Fin.castOrderIso (Fintype.card_fin n)).symm j))
    simpa [lam, Matrix.IsHermitian.eigenvalues, e, hG] using hp
  have hPlow : ∀ k : Fin (n+1), (m₁ / K) * T ^ A k ≤ P k := by
    intro k
    have hmul : m₁ * T ^ A k ≤ K * P k := by
      calc
        m₁ * T ^ A k ≤
            (((1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
              (Polynomial.X : Polynomial ℝ) • (G T).map Polynomial.C).det).coeff k.val :=
          (hcb T k hT (lt_of_lt_of_le hTδ (min_le_left δ₁ 1))).1
        _ ≤ K * P k := by
          simpa [K, P, A, lam, hG] using (hprefix T hT k).2
    have hmul' : ((m₁ / K) * T ^ A k) * K ≤ P k * K := by
      calc
        ((m₁ / K) * T ^ A k) * K = m₁ * T ^ A k := by field_simp [ne_of_gt hK]
        _ ≤ K * P k := hmul
        _ = P k * K := by ring
    exact le_of_mul_le_mul_right hmul' hK
  have hPhigh : ∀ k : Fin (n+1), P k ≤ M₁ * T ^ A k := by
    intro k
    calc
      P k ≤ (((1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) +
          (Polynomial.X : Polynomial ℝ) • (G T).map Polynomial.C).det).coeff k.val := by
        simpa [P, A, lam, hG] using (hprefix T hT k).1
      _ ≤ M₁ * T ^ A k :=
        (hcb T k hT (lt_of_lt_of_le hTδ (min_le_left δ₁ 1))).2
  have hPpos : ∀ k, 0 < P k := by
    intro k
    exact lt_of_lt_of_le (mul_pos (div_pos hm₁ hK) (pow_pos hT _)) (hPlow k)
  have hratio : P (Fin.succ i) = P (Fin.castSucc i) * lam i := by
    let f : Fin (i.val + 1) → ℝ := fun j =>
      lam (Fin.castLE (Nat.le_of_lt_succ (Fin.succ i).isLt) j)
    have hp := Fin.prod_univ_castSucc f
    dsimp [f] at hp
    have hlast : Fin.castLE (Nat.le_of_lt_succ (Fin.succ i).isLt) (Fin.last i) = i := by
      apply Fin.ext
      rfl
    rw [hlast] at hp
    simpa [P, mul_comm] using hp
  have hsumratio : A (Fin.succ i) = A (Fin.castSucc i) + q i := by
    let f : Fin (i.val + 1) → ℕ := fun j =>
      q (Fin.castLE (Nat.le_of_lt_succ (Fin.succ i).isLt) j)
    have hs := Fin.sum_univ_castSucc f
    dsimp [f] at hs
    have hlast : Fin.castLE (Nat.le_of_lt_succ (Fin.succ i).isLt) (Fin.last i) = i := by
      apply Fin.ext
      rfl
    rw [hlast] at hs
    simpa [A, add_comm] using hs
  have hx : 0 < T ^ A (Fin.castSucc i) := pow_pos hT _
  have hlow_next := hPlow (Fin.succ i)
  have hhigh_prev := hPhigh (Fin.castSucc i)
  have hlow_prev := hPlow (Fin.castSucc i)
  have hhigh_next := hPhigh (Fin.succ i)
  rw [hsumratio, pow_add, hratio] at hlow_next hhigh_next
  have hlow_mul : (m₁ / K) * T ^ q i ≤ M₁ * lam i := by
    exact le_of_mul_le_mul_left (a := T ^ A (Fin.castSucc i)) (by
      calc
        T ^ A (Fin.castSucc i) * ((m₁ / K) * T ^ q i) =
            (m₁ / K) * (T ^ A (Fin.castSucc i) * T ^ q i) := by ring
        _ ≤ P (Fin.castSucc i) * lam i := hlow_next
        _ ≤ (M₁ * T ^ A (Fin.castSucc i)) * lam i :=
          mul_le_mul_of_nonneg_right hhigh_prev (hlam i).le
        _ = T ^ A (Fin.castSucc i) * (M₁ * lam i) := by ring) hx
  have hhigh_mul : (m₁ / K) * lam i ≤ M₁ * T ^ q i := by
    exact le_of_mul_le_mul_left (a := T ^ A (Fin.castSucc i)) (by
      calc
        T ^ A (Fin.castSucc i) * ((m₁ / K) * lam i) =
            ((m₁ / K) * T ^ A (Fin.castSucc i)) * lam i := by ring
        _ ≤ P (Fin.castSucc i) * lam i :=
          mul_le_mul_of_nonneg_right hlow_prev (hlam i).le
        _ ≤ M₁ * (T ^ A (Fin.castSucc i) * T ^ q i) := hhigh_next
        _ = T ^ A (Fin.castSucc i) * (M₁ * T ^ q i) := by ring) hx
  have hcM : c * M₁ = m₁ / K := by
    dsimp [c]
    field_simp
  have hCa : C * (m₁ / K) = M₁ := by
    dsimp [C]
    field_simp
  have hlow : c * T ^ q i ≤ lam i := by
    exact le_of_mul_le_mul_right (a := M₁) (by
      calc
        (c * T ^ q i) * M₁ = (m₁ / K) * T ^ q i := by rw [mul_right_comm, hcM]
        _ ≤ M₁ * lam i := hlow_mul
        _ = lam i * M₁ := mul_comm _ _) hM₁
  have hhigh : lam i ≤ C * T ^ q i := by
    exact le_of_mul_le_mul_right (a := m₁ / K) (by
      calc
        lam i * (m₁ / K) = (m₁ / K) * lam i := mul_comm _ _
        _ ≤ M₁ * T ^ q i := hhigh_mul
        _ = (C * T ^ q i) * (m₁ / K) := by rw [mul_right_comm, hCa]) (div_pos hm₁ hK)
  exact ⟨by simpa [lam, hG, q] using hlow, by simpa [lam, hG, q] using hhigh⟩
end D5.S3.Observer.Linear
