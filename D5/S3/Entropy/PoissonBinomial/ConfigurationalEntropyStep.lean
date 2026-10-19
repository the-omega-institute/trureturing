/- GID: D5/S3/Entropy/PoissonBinomial/ConfigurationalEntropyStep
   generality: G
   mirror-B: D5/B/S3/Entropy/PoissonBinomial/ConfigurationalEntropyStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entropy monotonicity for a transfer of Bernoulli coordinates. -/

import D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure
import D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds
import D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity

/-! Pairwise smoothing of the configurational entropy. -/

noncomputable section
namespace D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
open scoped BigOperators Topology
open D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds
open D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector (transfer)

private lemma pbRest_tail {M : ℕ} (x : Fin M → ℝ) {i j : Fin M}
    (hij : i ≠ j) {k : ℕ} (hk : M < k + 2) : pbRest x i j k = 0 := by
  classical
  unfold pbRest pb
  apply Finset.sum_eq_zero
  intro A hA
  have hcard : A.card = k := (Finset.mem_filter.mp hA).2
  have hmem : i ∈ A ∨ j ∈ A := by
    by_contra h
    push Not at h
    have hbound := Finset.card_le_univ (insert i (insert j A))
    rw [Finset.card_insert_of_notMem (by simp [hij, h.1]),
      Finset.card_insert_of_notMem h.2] at hbound
    simp only [Fintype.card_fin] at hbound
    omega
  rcases hmem with hi | hj
  · have hz : (∏ l ∈ A, Function.update (Function.update x i 0) j 0 l) = 0 :=
      Finset.prod_eq_zero hi (by simp [hij])
    rw [hz, zero_mul]
  · have hz : (∏ l ∈ A, Function.update (Function.update x i 0) j 0 l) = 0 :=
      Finset.prod_eq_zero hj (by simp)
    rw [hz, zero_mul]

private lemma pbRest_sum {n : ℕ} (x : Fin (n + 2) → ℝ) {i j : Fin (n + 2)}
    (hij : i ≠ j) : ∑ k : Fin (n + 1), pbRest x i j k = 1 := by
  rw [Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ k ∈ Finset.range (n + 2 + 1), pbRest x i j k := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hkn
      exact pbRest_tail x hij (by
        have := Finset.mem_range.mp hk
        have := (Finset.mem_range.not.mp hkn)
        omega)
    _ = 1 := pb_sum_one _

private lemma shift_sum {n : ℕ} (f : ℕ → ℝ) (hf : ∀ k, n ≤ k → f k = 0)
    (k a : ℕ) : (∑ l : Fin n, if k = l.val + a then f l else 0) =
      if a ≤ k then f (k - a) else 0 := by
  classical
  by_cases ha : a ≤ k
  · rw [ite_eq_left ha]
    by_cases hn : k - a < n
    · let l : Fin n := ⟨k - a, hn⟩
      rw [Finset.sum_eq_single l]
      · simp [l, Nat.sub_add_cancel ha]
      · intro b _ hbl
        rw [ite_eq_right]
        intro he
        apply hbl
        apply Fin.ext
        dsimp [l]
        omega
      · simp
    · rw [hf _ (by omega)]
      apply Finset.sum_eq_zero
      intro b _
      rw [ite_eq_right (by have := b.isLt; omega)]
  · rw [ite_eq_right ha]
    apply Finset.sum_eq_zero
    intro b _
    rw [ite_eq_right (by omega)]

private lemma threePointMass_rest {n : ℕ} (x : Fin (n + 2) → ℝ)
    {i j : Fin (n + 2)} (hij : i ≠ j) (v0 v1 v2 t : ℝ) (k : Fin (n + 3)) :
    threePointMass (fun l : Fin (n + 1) => pbRest x i j l) v0 v1 v2 t k =
      (v0 + t) * pbRest x i j k +
      (v1 - 2 * t) * (if 1 ≤ k.val then pbRest x i j (k.val - 1) else 0) +
      (v2 + t) * (if 2 ≤ k.val then pbRest x i j (k.val - 2) else 0) := by
  have ht (l) (hl : n + 1 ≤ l) := pbRest_tail x hij (k := l) (by omega)
  unfold threePointMass
  simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_succ]
  have h0 := shift_sum _ ht k 0
  have h1 := shift_sum _ ht k 1
  have h2 := shift_sum _ ht k 2
  simp only [Nat.add_zero, Nat.zero_le, Nat.sub_zero, ite_true] at h0
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [h0, h1, h2]

/-- Polynomial dependence of each Bernoulli-sum mass on its coordinates. -/
@[fun_prop] private theorem continuous_pb {M : ℕ} (k : ℕ) :
    Continuous (fun x : Fin M → ℝ => pb x k) := by
  classical
  unfold pb
  fun_prop

/-- Continuity includes the zero and one boundary coordinates. -/
@[fun_prop] theorem continuous_F {M : ℕ} : Continuous (F (M := M)) := by
  unfold F
  fun_prop

private lemma pbRest_pair {M : ℕ} (x : Fin M → ℝ) (i j : Fin M) (t : ℝ) :
    pbRest (transfer x i j t) i j = pbRest x i j := by
  classical
  unfold pbRest
  apply congrArg pb
  ext l
  by_cases hlj : l = j
  · subst l; simp
  · by_cases hli : l = i
    · subst l; simp [hlj]
    · simp [transfer, hlj, hli]

private lemma sum_pair {M : ℕ} (f : Fin M → ℝ) {i j : Fin M} (hij : i ≠ j) :
    ∑ l, f l = f i + f j + ∑ l ∈ (Finset.univ.erase i).erase j, f l := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  ring

private lemma pair_entropy_hasDerivAt {M : ℕ} (x : Fin M → ℝ)
    {i j : Fin M} (hij : i ≠ j) (hx : ∀ l, x l ∈ Set.Ioo 0 1) :
    HasDerivAt (fun t => ∑ l, Real.binEntropy (transfer x i j t l))
      (Real.log (1 - x j) - Real.log (x j) -
        (Real.log (1 - x i) - Real.log (x i))) 0 := by
  classical
  have he : (fun t => ∑ l, Real.binEntropy (transfer x i j t l)) =
      fun t => Real.binEntropy (x i - t) + Real.binEntropy (x j + t) +
        ∑ l ∈ (Finset.univ.erase i).erase j, Real.binEntropy (x l) := by
    ext t
    rw [sum_pair _ hij]
    simp only [transfer, Function.update_self, Function.update_of_ne hij]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    have hlj := (Finset.mem_erase.mp hl).1
    have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    simp [Function.update_of_ne hlj, Function.update_of_ne hli]
  rw [he]
  have hi0 : HasDerivAt Real.binEntropy (Real.log (1 - x i) - Real.log (x i))
      (x i - (0 : ℝ)) := by
    simpa using Real.hasDerivAt_binEntropy (hx i).1.ne' (ne_of_lt (hx i).2)
  have hj0 : HasDerivAt Real.binEntropy (Real.log (1 - x j) - Real.log (x j))
      (x j + (0 : ℝ)) := by
    simpa using Real.hasDerivAt_binEntropy (hx j).1.ne' (ne_of_lt (hx j).2)
  have hi := hi0.comp 0 ((hasDerivAt_id (0 : ℝ)).const_sub (x i))
  have hj := hj0.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add (x j))
  convert (hi.add hj).add_const (∑ l ∈ (Finset.univ.erase i).erase j,
    Real.binEntropy (x l)) using 1 <;> simp [Function.comp_def] <;> ring

private lemma pair_hasDerivAt_nonneg {n : ℕ} (x : Fin (n + 2) → ℝ)
    {i j : Fin (n + 2)} (hij : i ≠ j) (hx : ∀ l, x l ∈ Set.Ioo 0 1)
    (hpq : x j ≤ x i) :
    ∃ D, HasDerivAt (fun t => F (transfer x i j t)) D 0 ∧ 0 ≤ D := by
  classical
  let p := x i
  let q := x j
  let v0 := (1 - p) * (1 - q)
  let v1 := p * (1 - q) + q * (1 - p)
  let v2 := p * q
  let r := fun l : Fin (n + 1) => pbRest x i j l
  have hp : p ∈ Set.Ioo (0 : ℝ) 1 := hx i
  have hq : q ∈ Set.Ioo (0 : ℝ) 1 := hx j
  have h0 : 0 < v0 := mul_pos (sub_pos.mpr hp.2) (sub_pos.mpr hq.2)
  have h1 : 0 < v1 := add_pos (mul_pos hp.1 (sub_pos.mpr hq.2))
    (mul_pos hq.1 (sub_pos.mpr hp.2))
  have h2 : 0 < v2 := mul_pos hp.1 hq.1
  have hr : ∀ l, 0 ≤ r l := by
    intro l
    apply pb_nonneg
    intro a
    by_cases haj : a = j <;> by_cases hai : a = i <;>
      simp [Function.update_apply, haj, hai, (hx a).1.le, (hx a).2.le]
  have hdir := three_point_entropy_direction_bound r hr (pbRest_sum x hij)
    v0 v1 v2 h0 h1 h2 (by dsimp [v0, v1, v2]; ring)
  let d := ∑ l, r l * (2 * Real.log (threePointMass r v0 v1 v2 0 ((l.castAdd 1).succ)) -
    Real.log (threePointMass r v0 v1 v2 0 (l.castAdd 2)) -
    Real.log (threePointMass r v0 v1 v2 0 l.succ.succ))
  change HasDerivAt _ d 0 ∧ d ≤ -Real.log (v0 * v2) at hdir
  let τ := fun t : ℝ => (p - t) * (q + t) - p * q
  have ht : HasDerivAt τ (p - q) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_sub p).mul
      ((hasDerivAt_id (0 : ℝ)).const_add q)).sub_const (p * q) using 1 <;>
      simp [τ] <;> ring
  have he (t : ℝ) (k : Fin (n + 3)) :
      pb (transfer x i j t) k = threePointMass r v0 v1 v2 (τ t) k := by
    rw [pb_remove_two _ hij, pbRest_pair]
    rw [show r = fun l : Fin (n + 1) => pbRest x i j l from rfl,
      threePointMass_rest x hij]
    simp only [transfer, Function.update_self, Function.update_of_ne hij]
    dsimp [v0, v1, v2, τ, p, q]
    ring
  have hD : HasDerivAt (fun u => ∑ k, Real.negMulLog (threePointMass r v0 v1 v2 u k))
      d (τ 0) := by simpa [τ] using hdir.1
  have hH := hD.comp 0 ht
  have hH' : HasDerivAt
      (fun t => ∑ k ∈ Finset.range (n + 2 + 1), Real.negMulLog (pb (transfer x i j t) k))
      (d * (p - q)) 0 := by
    convert hH using 1
    ext t
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    rw [he]
  have hF := (pair_entropy_hasDerivAt x hij hx).sub hH'
  refine ⟨_, hF, ?_⟩
  change 0 ≤ (Real.log (1 - q) - Real.log q -
    (Real.log (1 - p) - Real.log p)) - d * (p - q)
  let A := p * (1 - q)
  let B := q * (1 - p)
  have hA : 0 < A := mul_pos hp.1 (sub_pos.mpr hq.2)
  have hB : 0 < B := mul_pos hq.1 (sub_pos.mpr hp.2)
  have hlog : Real.log (1 - q) - Real.log q -
      (Real.log (1 - p) - Real.log p) = Real.log A - Real.log B := by
    rw [Real.log_mul hp.1.ne' (sub_pos.mpr hq.2).ne',
      Real.log_mul hq.1.ne' (sub_pos.mpr hp.2).ne']
    ring
  rw [hlog]
  rcases hpq.eq_or_lt with heq | hlt
  · have heqp : p = q := heq.symm
    simp [heqp, A, B]
  · have hBA : B < A := by dsimp [A, B]; nlinarith
    have hA1 : A < 1 := by dsimp [A]; nlinarith [mul_pos hp.1 hq.1]
    have hbound := (neg_log_product_lt_div hB hBA hA1).le.trans
      (log_divided_difference_lower hB hBA hA1)
    have hprod : v0 * v2 = A * B := by dsimp [v0, v2, A, B]; ring
    rw [hprod] at hdir
    have hd : d ≤ (Real.log A - Real.log B) / (A - B) := hdir.2.trans hbound
    have hd' := (le_div_iff₀ (sub_pos.mpr hBA)).mp hd
    have he : A - B = p - q := by dsimp [A, B]; ring
    rw [he] at hd'
    linarith

private lemma pair_interior {M : ℕ} (x : Fin M → ℝ) {i j : Fin M}
    (hij : i ≠ j) (hx : ∀ l, x l ∈ Set.Ioo 0 1) {s : ℝ}
    (hs : s ∈ Set.Icc 0 ((x i - x j) / 2)) :
    ∀ l, transfer x i j s l ∈ Set.Ioo 0 1 := by
  intro l
  by_cases hlj : l = j
  · subst l
    simp only [transfer, Function.update_self]
    constructor <;> nlinarith [(hx i).1, (hx i).2, (hx j).1, (hx j).2, hs.1, hs.2]
  · by_cases hli : l = i
    · subst l
      simp only [transfer, Function.update_of_ne hij, Function.update_self]
      constructor <;> nlinarith [(hx i).1, (hx i).2, (hx j).1, (hx j).2, hs.1, hs.2]
    · simpa [transfer, Function.update_of_ne hlj, Function.update_of_ne hli] using hx l

private lemma pair_add {M : ℕ} (x : Fin M → ℝ) {i j : Fin M}
    (hij : i ≠ j) (s t : ℝ) :
    transfer (transfer x i j s) i j t = transfer x i j (s + t) := by
  classical
  ext l
  by_cases hlj : l = j <;> by_cases hli : l = i <;>
    simp [transfer, hlj, hli, hij] <;> ring

private lemma pair_monotone {M : ℕ} (x : Fin M → ℝ) {i j : Fin M}
    (hij : i ≠ j) (hx : ∀ l, x l ∈ Set.Ioo 0 1) :
    MonotoneOn (fun s => F (transfer x i j s)) (Set.Icc 0 ((x i - x j) / 2)) := by
  classical
  have hdim : 2 ≤ M := by
    have hh := Finset.card_le_univ ({i, j} : Finset (Fin M))
    simpa [hij] using hh
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hdim
  have hM : M = n + 2 := by omega
  clear hn
  subst M
  have hd (s : ℝ) (hs : s ∈ Set.Icc 0 ((x i - x j) / 2)) :
      ∃ D, HasDerivAt (fun t => F (transfer x i j t)) D s ∧ 0 ≤ D := by
    have horder : transfer x i j s j ≤ transfer x i j s i := by
      simp only [transfer, Function.update_self, Function.update_of_ne hij]
      linarith [hs.2]
    obtain ⟨D, hD, hDn⟩ := pair_hasDerivAt_nonneg (n := n) (transfer x i j s) (i := i) (j := j) hij
      (pair_interior x hij hx hs) horder
    have hD' : HasDerivAt (fun t => F (transfer (transfer x i j s) i j t)) D (s - s) := by
      simpa only [sub_self] using hD
    have hh := hD'.comp s (h := fun t : ℝ => t - s) ((hasDerivAt_id s).sub_const s)
    refine ⟨D, ?_, hDn⟩
    have he (t : ℝ) : transfer (transfer x i j s) i j (t - s) = transfer x i j t := by
      rw [pair_add x hij]
      congr 1
      ring
    simpa only [Function.comp_def, mul_one, he] using hh
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact (continuous_F.comp (by unfold transfer; fun_prop)).continuousOn
  · intro s hs
    have hs' : s ∈ Set.Icc 0 ((x i - x j) / 2) := interior_subset hs
    exact (hd s hs').choose_spec.1.differentiableAt.differentiableWithinAt
  · intro s hs
    obtain ⟨D, hD, hn⟩ := hd s (interior_subset hs)
    simpa only [hD.deriv] using hn

private lemma F_perm {M : ℕ} (x : Fin M → ℝ) (σ : Equiv.Perm (Fin M)) :
    F (x ∘ σ) = F x := by
  unfold F
  simp only [pb_perm]
  congr 1
  exact Equiv.sum_comp σ (fun l => Real.binEntropy (x l))

private lemma pair_reflect {M : ℕ} (x : Fin M → ℝ) {i j : Fin M}
    (hij : i ≠ j) (s : ℝ) :
    transfer x i j (x i - x j - s) = transfer x i j s ∘ Equiv.swap i j := by
  classical
  ext l
  by_cases hli : l = i
  · subst l
    simp [transfer, hij]
    ring
  · by_cases hlj : l = j
    · subst l
      simp [transfer, hij, hij.symm]
      ring
    · simp [transfer, Equiv.swap_apply_of_ne_of_ne hli hlj, hli, hlj]

private lemma pair_le {M : ℕ} (x : Fin M → ℝ) {i j : Fin M}
    (hij : i ≠ j) (hx : ∀ l, x l ∈ Set.Ioo 0 1) {s : ℝ}
    (hs : s ∈ Set.Icc 0 (x i - x j)) : F x ≤ F (transfer x i j s) := by
  have hzero : transfer x i j 0 = x := by
    simp [transfer]
  by_cases hhalf : s ≤ (x i - x j) / 2
  · simpa only [hzero] using
      pair_monotone x hij hx ⟨le_rfl, by linarith [hs.1, hs.2]⟩ ⟨hs.1, hhalf⟩ hs.1
  · have hsmall : x i - x j - s ∈ Set.Icc 0 ((x i - x j) / 2) := by
      constructor <;> linarith [hs.1, hs.2]
    have hh := pair_monotone x hij hx ⟨le_rfl, by linarith [hs.1, hs.2]⟩
      hsmall hsmall.1
    dsimp only at hh
    rw [hzero, pair_reflect x hij s, F_perm] at hh
    exact hh

/-- An interior T-transform cannot decrease configurational entropy. -/
theorem F_le_interiorT {M : ℕ} (x y : Fin M → ℝ) (ht : InteriorT x y) :
    F x ≤ F y := by
  classical
  obtain ⟨⟨i, j, t, ht0, ht1, rfl⟩, hx, _⟩ := ht
  by_cases hij : i = j
  · subst j
    have he : (1 - t) • x + t • (x ∘ Equiv.swap i i) = x := by
      simp [← add_smul]
    rw [he]
  · have aux (a b : Fin M) (hab : a ≠ b) (horder : x b ≤ x a) :
        F x ≤ F ((1 - t) • x + t • (x ∘ Equiv.swap a b)) := by
      have he : (1 - t) • x + t • (x ∘ Equiv.swap a b) =
          transfer x a b (t * (x a - x b)) := by
        rw [D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Pair.mixPair_eq_pairLine
          x a b hab t]
        ext l
        by_cases hla : l = a <;> by_cases hlb : l = b <;>
          simp_all [D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Pair.pairLine,
            transfer, Pi.single_apply, sub_eq_add_neg]
      rw [he]
      exact pair_le x hab hx ⟨mul_nonneg ht0 (sub_nonneg.mpr horder),
        by nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr horder)]⟩
    rcases le_total (x j) (x i) with h | h
    · exact aux i j hij h
    · simpa only [Equiv.swap_comm] using aux j i (Ne.symm hij) h

end D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
