/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-time CZX evolution as a cyclic ordered transfer product. -/

import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation

/-! The weighted gauge sector of the CZX evolution and its ordered transfer formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer

open CZXParentLindbladianAveraging CZXParentLindbladianWindowChannel
open CZXParentLindbladianSteadyState CZXParentLindbladianAnnealedGrowth
open D5.S3.Quantum.Foundation
open Matrix
open scoped ComplexConjugate

private abbrev Config (n : ℕ) := Fin n → Fin 2
private abbrev Operator (n : ℕ) := Matrix (Config n) (Config n) ℂ
private abbrev Superoperator (n : ℕ) := Matrix (Config n × Config n) (Config n × Config n) ℂ

private lemma middle_sites_ne (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    site i 1 ≠ site i 2 := fun h =>
  (by decide : (1 : Fin 4) ≠ 2) ((site_injective n hn i 1 2).mp h)

private def exchangeMiddle (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    (Config n × (Fin 2 × Fin 2)) ≃ (Config n × (Fin 2 × Fin 2)) := by
  let exchange : Config n × (Fin 2 × Fin 2) → Config n × (Fin 2 × Fin 2) :=
    fun z => (middleUpdate i z.1 z.2.1 z.2.2, z.1 (site i 1), z.1 (site i 2))
  have hinv : Function.Involutive exchange := by
    rintro ⟨x, b, c⟩
    have hne := middle_sites_ne n hn i
    have hb : middleUpdate i x b c (site i 1) = b := by simp [middleUpdate, hne]
    have hc : middleUpdate i x b c (site i 2) = c := by simp [middleUpdate]
    have hx : middleUpdate i (middleUpdate i x b c) (x (site i 1)) (x (site i 2)) = x := by
      funext j
      by_cases h₂ : j = site i 2
      · simp [middleUpdate, h₂]
      by_cases h₁ : j = site i 1
      · simp [middleUpdate, h₁, hne]
      · simp [middleUpdate, h₂, h₁]
    change (middleUpdate i (middleUpdate i x b c) (x (site i 1)) (x (site i 2)),
      middleUpdate i x b c (site i 1), middleUpdate i x b c (site i 2)) = _
    rw [hx, hb, hc]
  exact ⟨exchange, exchange, hinv, hinv⟩

private noncomputable def coeff (n : ℕ) (δ : Config n) (φ : Config n → ℂ) : Operator n :=
  ∑ x, φ x • gaugedUnit n δ x

private lemma window_coeff (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (δ : Config n) (hδ : goodWindow i δ) (φ : Config n → ℂ) :
    windowChannel n i (coeff n δ φ) =
      coeff n δ (avg n {site i 1, site i 2} φ) := by
  classical
  let G := gaugedUnit n δ
  let r : ℂ := (4 : ℂ)⁻¹
  have hf : (∑ x : Config n, ∑ b : Fin 2, ∑ c : Fin 2,
      φ x • G (middleUpdate i x b c)) =
      ∑ x : Config n, ∑ b : Fin 2, ∑ c : Fin 2, φ (middleUpdate i x b c) • G x := by
    simp only [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (exchangeMiddle n hn i).symm
    rintro ⟨x, b, c⟩
    change φ x • G (middleUpdate i x b c) =
      φ (middleUpdate i (middleUpdate i x b c) (x (site i 1)) (x (site i 2))) •
        G (middleUpdate i x b c)
    congr 1
    exact congrArg φ (congrArg Prod.fst ((exchangeMiddle n hn i).left_inv (x, b, c))).symm
  change windowLM n i (∑ x, φ x • G x) = ∑ x, (avg n {site i 1, site i 2} φ) x • G x
  have hchannel (x : Config n) : windowLM n i (G x) =
      r • ∑ b : Fin 2, ∑ c : Fin 2, G (middleUpdate i x b c) := by
    change windowChannel n i (gaugedUnit n δ x) =
      (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2, gaugedUnit n δ (middleUpdate i x b c)
    simpa only [hδ, ite_true] using gauged_window_sector n hn i δ x
  have havg (x : Config n) : (avg n {site i 1, site i 2} φ) x =
      r • ∑ b : Fin 2, ∑ c : Fin 2, φ (middleUpdate i x b c) :=
    avg_pair_apply n _ _ (middle_sites_ne n hn i) φ x
  calc
    _ = r • ∑ x : Config n, ∑ b : Fin 2, ∑ c : Fin 2, φ x • G (middleUpdate i x b c) := by
      simp only [map_sum, map_smul, hchannel, smul_comm (φ _) r, Finset.smul_sum]
    _ = r • ∑ x : Config n, ∑ b : Fin 2, ∑ c : Fin 2, φ (middleUpdate i x b c) • G x :=
      congrArg (r • ·) hf
    _ = _ := by
      simp only [havg, smul_assoc, Finset.sum_smul, Finset.smul_sum]

private def evenStart (m : ℕ) (k : Fin m) : Fin (2 * m) :=
  ⟨2 * k.val, by have := k.isLt; omega⟩

private lemma evenStart_injective (m : ℕ) : Function.Injective (evenStart m) := by
  intro i j h
  have hv := congrArg Fin.val h
  change 2 * i.val = 2 * j.val at hv
  exact Fin.ext (by omega)

private noncomputable def windowFactor (n : ℕ) (ρ : ℝ) (i : Fin n) : Superoperator n :=
  (ρ : ℂ) • (1 : Superoperator n) + (1 - (ρ : ℂ)) • windowSuperoperator n i

private lemma exp_windows (n : ℕ) (hn : 4 ≤ n) (he : Even n) (t : ℝ)
    (is : List (Fin n)) (h : ∀ i ∈ is, i.val % 2 = 0) :
    NormedSpace.exp ((t : ℂ) • (is.map (fun i => windowSuperoperator n i - 1)).sum) =
      (is.map (windowFactor n (Real.exp (-t)))).prod := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hi := h i (by simp)
    have his (j : Fin n) (hj : j ∈ is) := h j (List.mem_cons_of_mem _ hj)
    have hcomm : Commute (windowSuperoperator n i - 1)
        (is.map (fun j => windowSuperoperator n j - 1)).sum := by
      apply Commute.list_sum_right
      intro p hp
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      exact (((window_commute n he hn i j hi (his j hj)).sub_right
        (Commute.one_right _)).sub_left (Commute.one_left _))
    simp only [List.map_cons, List.sum_cons, smul_add, List.prod_cons]
    rw [Matrix.exp_add_of_commute _ _ (hcomm.smul_left (t : ℂ) |>.smul_right (t : ℂ)),
      exponential_idempotent _ (window_idempotent n hn i), ih his]
    rfl

private lemma exp_even_windows (m : ℕ) (hm : 2 ≤ m) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • parentLindbladian (2 * m)) =
      (List.ofFn fun k : Fin m => windowFactor (2 * m) (Real.exp (-t)) (evenStart m k)).prod := by
  classical
  let starts := List.ofFn (evenStart m)
  have hmem (i : Fin (2 * m)) : i ∈ starts ↔ i.val % 2 = 0 := by
    change i ∈ List.ofFn (evenStart m) ↔ _
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨k, rfl⟩
      change (2 * k.val) % 2 = 0
      omega
    · intro hi
      refine ⟨⟨i.val / 2, by have := i.isLt; omega⟩, Fin.ext ?_⟩
      change 2 * (i.val / 2) = i.val
      omega
  have hnodup : starts.Nodup := List.nodup_ofFn_ofInjective (evenStart_injective m)
  have hsets : starts.toFinset = Finset.univ.filter (fun i : Fin (2 * m) => i.val % 2 = 0) := by
    ext i
    simpa only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hmem i
  have hsum : (starts.map (fun i => windowSuperoperator (2 * m) i - 1)).sum =
      parentLindbladian (2 * m) := by
    rw [← List.sum_toFinset _ hnodup, hsets]
    rfl
  have hw := exp_windows (2 * m) (by omega) ⟨m, by omega⟩ t starts (fun i => (hmem i).mp)
  rw [hsum] at hw
  simpa only [starts, List.map_ofFn, Function.comp_def] using hw

private noncomputable def refresh (n : ℕ) (ρ : ℝ) (i : Fin n) (φ : Config n → ℂ) :
    Config n → ℂ :=
  (ρ : ℂ) • φ + (1 - (ρ : ℂ)) • avg n {site i 1, site i 2} φ

private lemma coeff_linear (n : ℕ) (δ : Config n) (a b : ℂ) (φ ψ : Config n → ℂ) :
    coeff n δ (a • φ + b • ψ) = a • coeff n δ φ + b • coeff n δ ψ := by
  simp only [coeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

private lemma window_one (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    windowChannel n i 1 = 1 := by
  have hc : coeff n (fun _ => 0) (fun _ => 1) = 1 := by
    simpa only [coeff, one_smul] using sum_gauged_zero n
  rw [← hc, window_coeff n hn i _ (by intro k; rfl)]
  congr 1
  funext x
  rw [avg_pair_apply n _ _ (middle_sites_ne n hn i)]
  norm_num [Fin.sum_univ_two]

private abbrev flatten {n : ℕ} (A : Operator n) : Config n × Config n → ℂ :=
  fun p => A p.1 p.2

private lemma windowFactor_mulVec (n : ℕ) (hn : 4 ≤ n) (ρ : ℝ) (i : Fin n) (a : ℂ)
    (φ : Config n → ℂ) :
    (windowFactor n ρ i).mulVec (flatten (a • 1 + coeff n (fun _ => 1) φ)) =
      flatten (a • 1 + coeff n (fun _ => 1) (refresh n ρ i φ)) := by
  funext p
  rcases p with ⟨x, y⟩
  simp only [windowFactor, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Pi.smul_apply, window_superoperator_action]
  have hwindow : windowChannel n i (a • 1 + coeff n (fun _ => 1) φ) =
      a • 1 + coeff n (fun _ => 1) (avg n {site i 1, site i 2} φ) := by
    change windowLM n i _ = _
    rw [map_add, map_smul]
    change a • windowChannel n i 1 + windowChannel n i (coeff n (fun _ => 1) φ) = _
    rw [window_one n hn i, window_coeff n hn i _ (by intro k; rfl)]
  rw [hwindow, refresh, coeff_linear]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private lemma evolution_coeff (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (a : ℂ)
    (φ : Config (2 * m) → ℂ) :
    evolution (2 * m) t (a • 1 + coeff (2 * m) (fun _ => 1) φ) =
      a • 1 + coeff (2 * m) (fun _ => 1)
        ((List.ofFn fun k : Fin m => refresh (2 * m) (Real.exp (-t)) (evenStart m k)).foldr
          (fun f g => f g) φ) := by
  let ρ := Real.exp (-t)
  have h (is : List (Fin (2 * m))) :
      ((is.map (windowFactor (2 * m) ρ)).prod).mulVec
          (flatten (a • 1 + coeff (2 * m) (fun _ => 1) φ)) =
        flatten (a • 1 + coeff (2 * m) (fun _ => 1)
          ((is.map (refresh (2 * m) ρ)).foldr (fun f g => f g) φ)) := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons, List.prod_cons, List.foldr_cons]
      rw [← Matrix.mulVec_mulVec, ih, windowFactor_mulVec (2 * m) (by omega)]
  ext x y
  change (NormedSpace.exp ((t : ℂ) • parentLindbladian (2 * m))).mulVec _ (x, y) = _
  rw [exp_even_windows m hm t]
  simpa only [List.map_ofFn, Function.comp_def, flatten, ρ] using
    congrFun (h (List.ofFn (evenStart m))) (x, y)

private def blockSite (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  finProdFinEquiv.trans ((finCongr (Nat.mul_comm m 2)).trans (finRotate (2 * m)))

private lemma blockSite_eq (m : ℕ) (k : Fin m) (b : Fin 2) :
    blockSite m (k, b) = site (evenStart m k) (1 + b.val) := by
  let : NeZero (2 * m) := ⟨by have := k.isLt; omega⟩
  apply Fin.ext
  simp only [blockSite, Equiv.trans_apply, finRotate_apply, Fin.val_add,
    finCongr_apply, Fin.val_cast]
  change (b.val + 2 * k.val + (1 : Fin (2 * m)).val) % (2 * m) =
    (2 * k.val + (1 + b.val)) % (2 * m)
  have hm : 1 < 2 * m := by have := k.isLt; omega
  rw [Fin.val_one', Nat.mod_eq_of_lt hm]
  congr 1
  omega

/-- The two middle sites of every even-start window, in increasing start order. -/
def blocks (m : ℕ) : (Fin (2 * m) → Fin 2) ≃ (Fin m → Letter) :=
  (((blockSite m).symm.arrowCongr (Equiv.refl (Fin 2))).trans
    (Equiv.curry (Fin m) (Fin 2) (Fin 2))).trans
      (Equiv.piCongrRight fun _ => finTwoArrowEquiv (Fin 2))

private lemma blocks_apply (m : ℕ) (x : Config (2 * m)) (k : Fin m) :
    blocks m x k = (x (site (evenStart m k) 1), x (site (evenStart m k) 2)) := by
  change (x (blockSite m (k, 0)), x (blockSite m (k, 1))) = _
  rw [blockSite_eq, blockSite_eq]
  rfl

private lemma blocks_middleUpdate (m : ℕ) (x : Config (2 * m)) (k : Fin m) (c : Letter) :
    blocks m (middleUpdate (evenStart m k) x c.1 c.2) =
      Function.update (blocks m x) k c := by
  classical
  have hsite (j k : Fin m) (b d : Fin 2) (h : j ≠ k ∨ b ≠ d) :
      blockSite m (j, b) ≠ blockSite m (k, d) := by
    intro he
    have hp := (blockSite m).injective he
    exact h.elim (fun hn => hn (congrArg Prod.fst hp)) (fun hn => hn (congrArg Prod.snd hp))
  have h₀ (j : Fin m) : blockSite m (j, 0) = site (evenStart m j) 1 := blockSite_eq m j 0
  have h₁ (j : Fin m) : blockSite m (j, 1) = site (evenStart m j) 2 := blockSite_eq m j 1
  funext j
  rw [blocks_apply, middleUpdate, ← h₀, ← h₁, ← h₀, ← h₁]
  by_cases hj : j = k
  · subst j
    simp [hsite k k 0 1 (Or.inr (by decide))]
  · rw [Function.update_of_ne hj, blocks_apply, ← h₀, ← h₁]
    simp [hsite j k 0 0 (Or.inl hj), hsite j k 0 1 (Or.inl hj),
      hsite j k 1 0 (Or.inl hj), hsite j k 1 1 (Or.inl hj)]

private noncomputable def weight (ρ : ℝ) (a c : Letter) : ℝ :=
  ρ * (if c = a then 1 else 0) + (1 - ρ) / 4

private noncomputable def kernel (ρ : ℝ) : Matrix Letter Letter ℂ :=
  fun a c => (weight ρ a c : ℂ)

private abbrev BlockWord (m : ℕ) := Fin m → Letter

private def tensorKernel {m : ℕ} (M : Fin m → Matrix Letter Letter ℂ) :
    Matrix (BlockWord m) (BlockWord m) ℂ :=
  fun w z => ∏ k, M k (w k) (z k)

private lemma tensorKernel_one (m : ℕ) : tensorKernel (1 : Fin m → Matrix Letter Letter ℂ) = 1 := by
  classical
  ext w z
  by_cases h : w = z
  · subst z
    simp [tensorKernel]
  · rw [Matrix.one_apply_ne h]
    obtain ⟨k, hk⟩ : ∃ k, w k ≠ z k := by
      by_contra! hh
      exact h (funext hh)
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact Matrix.one_apply_ne hk

private lemma tensorKernel_mul {m : ℕ} (M N : Fin m → Matrix Letter Letter ℂ) :
    tensorKernel M * tensorKernel N = tensorKernel (M * N) := by
  classical
  ext w z
  simp only [Matrix.mul_apply, tensorKernel, Pi.mul_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun _ _ => (Finset.prod_mul_distrib).symm

private lemma tensorKernel_single_entry {m : ℕ} (k : Fin m)
    (K : Matrix Letter Letter ℂ) (w z : BlockWord m) :
    tensorKernel (Function.update 1 k K) w z =
      if z = Function.update w k (z k) then K (w k) (z k) else 0 := by
  classical
  by_cases hz : z = Function.update w k (z k)
  · rw [ite_eq_left hz]
    change (∏ j, Function.update
      (1 : Fin m → Matrix Letter Letter ℂ) k K j (w j) (z j)) = _
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Function.update_self]
    suffices he : (∏ j ∈ Finset.univ.erase k, Function.update
        (1 : Fin m → Matrix Letter Letter ℂ) k K j (w j) (z j)) = 1 by
      rw [he, one_mul]
    apply Finset.prod_eq_one
    intro j hj
    have hne := (Finset.mem_erase.mp hj).1
    have he := congrFun hz j
    simp only [Function.update_of_ne hne] at he
    simp [Function.update_of_ne hne, he]
  · rw [ite_eq_right hz]
    have hne : ∃ j, j ≠ k ∧ w j ≠ z j := by
      by_contra! h
      apply hz
      funext j
      by_cases hj : j = k
      · subst j
        simp
      · rw [Function.update_of_ne hj, h j hj]
    obtain ⟨j, hj, hj'⟩ := hne
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [Function.update_of_ne hj]
    change (1 : Matrix Letter Letter ℂ) (w j) (z j) = 0
    exact Matrix.one_apply_ne hj'

private lemma tensorKernel_single_mulVec {m : ℕ} (k : Fin m)
    (K : Matrix Letter Letter ℂ) (φ : BlockWord m → ℂ) (w : BlockWord m) :
    (tensorKernel (Function.update 1 k K)).mulVec φ w =
      ∑ c, K (w k) c * φ (Function.update w k c) := by
  classical
  change (∑ z, tensorKernel (Function.update 1 k K) w z * φ z) = _
  simp only [tensorKernel_single_entry, ite_mul, zero_mul]
  calc
    _ = ∑ z : BlockWord m, ∑ c : Letter,
        if z = Function.update w k c then K (w k) c * φ z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_eq_single (z k)]
      · intro c _ hc
        apply ite_eq_right
        intro he
        apply hc
        simpa using (congrFun he k).symm
      · simp
    _ = _ := by rw [Finset.sum_comm]; simp

private lemma refresh_blocks (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (k : Fin m)
    (φ : Config (2 * m) → ℂ) (w : BlockWord m) :
    refresh (2 * m) ρ (evenStart m k) φ ((blocks m).symm w) =
      (tensorKernel (Function.update 1 k (kernel ρ))).mulVec (φ ∘ (blocks m).symm) w := by
  classical
  let x := (blocks m).symm w
  have hupdate (c : Letter) :
      (blocks m).symm (Function.update w k c) =
        middleUpdate (evenStart m k) x c.1 c.2 := by
    apply (blocks m).injective
    rw [Equiv.apply_symm_apply, blocks_middleUpdate, Equiv.apply_symm_apply]
  rw [tensorKernel_single_mulVec]
  simp only [Function.comp_apply]
  have hw (c : Letter) : kernel ρ (w k) c =
      (if c = w k then (ρ : ℂ) else 0) + (1 - (ρ : ℂ)) / 4 := by
    by_cases h : c = w k <;> simp [kernel, weight, h]
  have havg : (avg (2 * m) {site (evenStart m k) 1, site (evenStart m k) 2} φ) x =
      (4 : ℂ)⁻¹ * ∑ c : Letter, φ (middleUpdate (evenStart m k) x c.1 c.2) := by
    rw [avg_pair_apply _ _ _ (middle_sites_ne (2 * m) (by omega) _), Fintype.sum_prod_type]
    rfl
  change (ρ : ℂ) * φ x + (1 - (ρ : ℂ)) *
    (avg (2 * m) {site (evenStart m k) 1, site (evenStart m k) 2} φ) x = _
  rw [havg]
  simp only [hw, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ← Finset.mul_sum, hupdate]
  have hx := hupdate (w k)
  rw [Function.update_eq_self] at hx
  rw [← hx]
  ring

private lemma refresh_kernel (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ)
    (φ : Config (2 * m) → ℂ) (x : Config (2 * m)) :
    ((List.ofFn fun k : Fin m => refresh (2 * m) ρ (evenStart m k)).foldr
        (fun f g => f g) φ) x =
      ∑ z : BlockWord m, (∏ k : Fin m, (weight ρ (blocks m x k) (z k) : ℂ)) *
        φ ((blocks m).symm z) := by
  let localFamily (k : Fin m) := Function.update
    (1 : Fin m → Matrix Letter Letter ℂ) k (kernel ρ)
  have hfold (ks : List (Fin m)) :
      (((ks.map fun k => refresh (2 * m) ρ (evenStart m k)).foldr (fun f g => f g) φ) ∘
          (blocks m).symm) =
        (tensorKernel (ks.map localFamily).prod).mulVec (φ ∘ (blocks m).symm) := by
    induction ks with
    | nil => simp [tensorKernel_one]
    | cons k ks ih =>
      simp only [List.map_cons, List.foldr_cons, List.prod_cons]
      funext w
      rw [Function.comp_apply, refresh_blocks m hm, ih, Matrix.mulVec_mulVec, tensorKernel_mul]
  have hfamily (ks : List (Fin m)) (hn : ks.Nodup) (k : Fin m) :
      (ks.map localFamily).prod k = if k ∈ ks then kernel ρ else 1 := by
    induction ks with
    | nil => rfl
    | cons j ks ih =>
      obtain ⟨hj, hks⟩ := List.nodup_cons.mp hn
      simp only [List.map_cons, List.prod_cons, Pi.mul_apply, ih hks]
      by_cases hk : k = j
      · subst k
        simp [localFamily, hj]
      · simp [localFamily, hk]
  have hall : ((List.finRange m).map localFamily).prod = fun _ => kernel ρ := by
    funext k
    rw [hfamily _ (List.nodup_finRange m), ite_eq_left (List.mem_finRange k)]
  have h := congrFun (hfold (List.finRange m)) (blocks m x)
  rw [hall] at h
  simpa [Function.comp_def, List.finRange, List.map_ofFn, tensorKernel, kernel,
    Matrix.mulVec, dotProduct] using h

private def phase (n : ℕ) (x : Config n) : ℝ :=
  (-1 : ℝ) ^ ∑ j : Fin n, (x j).val * (x (site j 1)).val

private lemma middle_edge (m : ℕ) (k : Fin m) :
    site (site (evenStart m k) 1) 1 = site (evenStart m k) 2 := by
  apply Fin.ext
  change (((2 * k.val + 1) % (2 * m)) + 1) % (2 * m) = (2 * k.val + 2) % (2 * m)
  rw [Nat.mod_add_mod]

private lemma block_edge (m : ℕ) (k : Fin m) :
    site (site (evenStart m k) 2) 1 = site (evenStart m (finRotate m k)) 1 := by
  let : NeZero m := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt k.isLt)⟩
  apply Fin.ext
  rw [finRotate_apply]
  change (((2 * k.val + 2) % (2 * m)) + 1) % (2 * m) =
    (2 * (k + 1).val + 1) % (2 * m)
  rw [Nat.mod_add_mod, Fin.val_add, Fin.val_one', Nat.add_mod_mod,
    ← Nat.mul_mod_mul_left, Nat.mod_add_mod]
  congr 1

private lemma phase_blocks (m : ℕ) (x : Config (2 * m)) :
    phase (2 * m) x = ∏ k : Fin m,
      (-1 : ℝ) ^ ((blocks m x k).2.val *
        ((blocks m x k).1.val + (blocks m x (finRotate m k)).1.val)) := by
  unfold phase
  rw [← (blockSite m).sum_comp, Fintype.sum_prod_type, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro k _
  congr 1
  rw [Fin.sum_univ_two, blockSite_eq, blockSite_eq]
  change (x (site (evenStart m k) 1)).val * (x (site (site (evenStart m k) 1) 1)).val +
    (x (site (evenStart m k) 2)).val * (x (site (site (evenStart m k) 2) 1)).val = _
  simp only [blocks_apply, middle_edge, block_edge]
  ring

private noncomputable def transfer (ρ : ℝ) (a : Letter) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun u u' => ∑ v : Fin 2, weight ρ a (u, v) * (-1 : ℝ) ^ (v.val * (u.val + u'.val))

private lemma transfer_twice (ρ : ℝ) (a : Letter) (u u' : Fin 2) :
    2 * transfer ρ a u u' = letter ρ a u u' := by
  obtain ⟨a, b⟩ := a
  fin_cases a <;> fin_cases b <;> fin_cases u <;> fin_cases u' <;>
    norm_num [transfer, weight, letter, Fin.sum_univ_two, Matrix.cons_val',
      Matrix.cons_val_fin_one] <;> ring

private lemma ordered_path (k : ℕ) (A : Fin (k + 1) → Matrix (Fin 2) (Fin 2) ℝ)
    (a b : Fin 2) :
    (List.ofFn A).prod a b =
      ∑ x : Fin k → Fin 2, ∏ j : Fin (k + 1),
        A j (Fin.cons (α := fun _ => Fin 2) a x j) (Fin.snoc (α := fun _ => Fin 2) x b j) := by
  induction k generalizing a b with
  | zero =>
    rw [Fintype.sum_unique, Fin.prod_univ_succ]
    simp [List.ofFn_succ, Fin.snoc_zero]
  | succ k ih =>
    rw [List.ofFn_succ', List.prod_concat, Matrix.mul_apply]
    simp_rw [ih (fun i => A i.castSucc), Finset.sum_mul]
    rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin 2)).sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro x _
    change _ = ∏ j : Fin (k + 2),
      A j (Fin.cons (α := fun _ => Fin 2) a (Fin.snoc (α := fun _ => Fin 2) x c) j)
        (Fin.snoc (α := fun _ => Fin 2) (Fin.snoc (α := fun _ => Fin 2) x c) b j)
    conv_rhs => rw [Fin.prod_univ_castSucc, Fin.cons_snoc_eq_snoc_cons]
    simp only [Fin.snoc_last, Fin.snoc_castSucc]

private lemma ordered_cycle (m : ℕ) (hm : 0 < m)
    (A : Fin m → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (List.ofFn A).prod =
      ∑ x : Fin m → Fin 2, ∏ j : Fin m, A j (x j) (x (finRotate m j)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [Matrix.trace, Matrix.diag_apply, ordered_path]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 2)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  change Fin.snoc (α := fun _ => Fin 2) x a j =
    Fin.cons (α := fun _ => Fin 2) a x (finRotate (k + 1) j)
  cases j using Fin.lastCases with
  | last => rw [finRotate_last, Fin.cons_zero, Fin.snoc_last]
  | cast j =>
    have hs : finRotate (k + 1) j.castSucc = j.succ :=
      finRotate_of_lt (by exact j.isLt)
    rw [hs, Fin.cons_succ, Fin.snoc_castSucc]

private lemma word_order (ρ : ℝ) (m : ℕ) (w : BlockWord m) :
    (List.ofFn fun k => letter ρ (w k)).prod = word ρ m w := by
  induction m with
  | zero => simp [word]
  | succ m ih =>
    rw [List.ofFn_succ', List.prod_concat, word, ← ih (Fin.init w)]
    rfl

private lemma transfer_sum (ρ : ℝ) (m : ℕ) (hm : 0 < m) (w : BlockWord m) :
    (∑ z : BlockWord m,
      ∏ k : Fin m, weight ρ (w k) (z k) *
        (-1 : ℝ) ^ ((z k).2.val * ((z k).1.val + (z (finRotate m k)).1.val))) =
      (2 : ℝ)⁻¹ ^ m * Matrix.trace (word ρ m w) := by
  let e := (Equiv.arrowProdEquivProdArrow (Fin m)
    (fun _ => Fin 2) (fun _ => Fin 2)).symm
  rw [← e.sum_comp, Fintype.sum_prod_type]
  change (∑ u : Fin m → Fin 2, ∑ v : Fin m → Fin 2, ∏ k : Fin m,
    weight ρ (w k) (u k, v k) * (-1 : ℝ) ^ ((v k).val *
      ((u k).val + (u (finRotate m k)).val))) = _
  have hsum (u : Fin m → Fin 2) :
      (∑ v : Fin m → Fin 2, ∏ k : Fin m, weight ρ (w k) (u k, v k) *
        (-1 : ℝ) ^ ((v k).val * ((u k).val + (u (finRotate m k)).val))) =
        ∏ k : Fin m, transfer ρ (w k) (u k) (u (finRotate m k)) :=
    (Fintype.prod_sum (κ := fun _ : Fin m => Fin 2) (fun k v =>
      weight ρ (w k) (u k, v) * (-1 : ℝ) ^ (v.val * ((u k).val + (u (finRotate m k)).val)))).symm
  simp only [hsum]
  rw [← word_order, ordered_cycle m hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have h (k : Fin m) : transfer ρ (w k) (u k) (u (finRotate m k)) =
      (2 : ℝ)⁻¹ * letter ρ (w k) (u k) (u (finRotate m k)) := by
    rw [← transfer_twice]
    ring
  simp only [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma refresh_phase (m : ℕ) (hm : 2 ≤ m) (ρ : ℝ) (x : Config (2 * m)) :
    ((List.ofFn fun k : Fin m => refresh (2 * m) ρ (evenStart m k)).foldr
      (fun f g => f g) (fun x => (phase (2 * m) x : ℂ))) x =
      (((2 : ℝ)⁻¹ ^ m * Matrix.trace (word ρ m (blocks m x))) : ℂ) := by
  rw [refresh_kernel m hm]
  trans ((∑ z : BlockWord m, ∏ k : Fin m, weight ρ (blocks m x k) (z k) *
    (-1 : ℝ) ^ ((z k).2.val * ((z k).1.val + (z (finRotate m k)).1.val))) : ℂ)
  · push_cast
    apply Finset.sum_congr rfl
    intro z _
    rw [phase_blocks, Equiv.apply_symm_apply]
    push_cast
    rw [Finset.prod_mul_distrib]
  · have h := congrArg (fun r : ℝ => (r : ℂ)) (transfer_sum ρ m (by omega) (blocks m x))
    push_cast [Complex.ofReal_neg] at h ⊢
    exact h

private lemma phase_cast (n : ℕ) (x : Config n) :
    (phase n x : ℂ) = sectorGauge n (fun _ => 1) x := by
  rw [sectorGauge_const]
  simp [phase, CZXParentLindbladianWindowChannel.gauge]

private lemma coeff_phase (n : ℕ) :
    coeff n (fun _ => 1) (fun x => (phase n x : ℂ)) = tensorX n := by
  classical
  have h (x : Config n) : (phase n x : ℂ) • gaugedUnit n (fun _ => 1) x =
      Matrix.single (x + (fun _ => 1)) x 1 := by
    rw [phase_cast]
    change _ • (_ • _) = _
    rw [smul_smul, sectorGauge_mul_self, one_smul]
  ext u v
  simp only [coeff, h, Matrix.sum_apply]
  rw [Finset.sum_eq_single v]
  · have hv : v + (fun _ => 1) = fun j => v j + 1 := rfl
    rw [hv]
    simp [tensorX, Matrix.single_apply, eq_comm]
  · intro x _ hx
    simp [hx]
  · simp

private lemma coeff_diagonal (m : ℕ) (φ : Config (2 * m) → ℂ) :
    coeff (2 * m) (fun _ => 1) φ = czxUnitary (2 * m) * Matrix.diagonal φ := by
  rw [← sum_gauged_one _ ⟨m, by omega⟩, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ext u v
  rw [Matrix.mul_diagonal]
  by_cases h : v = x
  · subst v
    simp [Matrix.smul_apply, smul_eq_mul, mul_comm]
  · simp [gaugedUnit, Matrix.smul_apply, smul_eq_mul, Ne.symm h]

private lemma evolution_smul (n : ℕ) (t : ℝ) (c : ℂ) (B : Operator n) :
    evolution n t (c • B) = c • evolution n t B := by
  ext x y
  change (NormedSpace.exp ((t : ℂ) • parentLindbladian n)).mulVec (c • flatten B) (x, y) =
    c * (NormedSpace.exp ((t : ℂ) • parentLindbladian n)).mulVec (flatten B) (x, y)
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

/-- The normalized initial operator proportional to the identity plus the global spin flip. -/
noncomputable def initial (m : ℕ) : Matrix (Fin (2 * m) → Fin 2) (Fin (2 * m) → Fin 2) ℂ :=
  ((4 : ℂ) ^ m)⁻¹ • (1 + tensorX (2 * m))

/-- The stationary operator in the CZX symmetry sector. -/
noncomputable def stationary (m : ℕ) : Matrix (Fin (2 * m) → Fin 2) (Fin (2 * m) → Fin 2) ℂ :=
  ((4 : ℂ) ^ m)⁻¹ • (1 + (2 * ((2 : ℂ) ^ m)⁻¹) • czxUnitary (2 * m))

/-- The canonical trace distance from the evolved initial operator to the stationary operator. -/
noncomputable def delta (m : ℕ) (t : ℝ) : ℝ :=
  FiniteTraceDistance.traceNorm (evolution (2 * m) t (initial m) - stationary m) / 2

/-- Exact finite-time evolution on an even ring of at least four sites. -/
theorem evolved_initial_transfer (m : ℕ) (hm : 2 ≤ m) (t : ℝ) :
    evolution (2 * m) t (initial m) = ((4 : ℂ) ^ m)⁻¹ •
      (1 + czxUnitary (2 * m) * Matrix.diagonal (fun x =>
        (((2 : ℝ)⁻¹ ^ m * Matrix.trace (word (Real.exp (-t)) m (blocks m x))) : ℂ))) := by
  rw [initial, evolution_smul, ← coeff_phase]
  have h := evolution_coeff m hm t 1 (fun x => (phase (2 * m) x : ℂ))
  simp only [one_smul] at h
  rw [h, coeff_diagonal]
  congr 4
  funext x
  exact refresh_phase m hm _ x

private lemma czx_gram (n : ℕ) :
    (czxUnitary n)ᴴ * czxUnitary n = 1 := by
  have hz : (cz n)ᴴ * cz n = 1 := by
    unfold cz
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext x
    simp only [Pi.star_apply, star_pow, star_neg, star_one,
      ← mul_pow, neg_mul_neg, one_mul, one_pow]
  have hx : (tensorX n)ᴴ * tensorX n = 1 :=
    mul_eq_one_comm.mp (tensor_x_unitary n)
  change (cz n * tensorX n)ᴴ * (cz n * tensorX n) = _
  rw [Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc (cz n)ᴴ, hz, one_mul, hx]

open scoped MatrixOrder in
private lemma traceNorm_diagonal_sector (n : ℕ) (f : Config n → ℝ) :
    FiniteTraceDistance.traceNorm (czxUnitary n * Matrix.diagonal (fun x => (f x : ℂ))) =
      ∑ x, |f x| := by
  have hgram :
      (czxUnitary n * Matrix.diagonal (fun x => (f x : ℂ)))ᴴ *
        (czxUnitary n * Matrix.diagonal (fun x => (f x : ℂ))) =
        Matrix.diagonal (fun x => ((f x ^ 2 : ℝ) : ℂ)) := by
    rw [Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc (czxUnitary n)ᴴ, czx_gram, one_mul,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    simp [pow_two]
  unfold FiniteTraceDistance.traceNorm
  rw [hgram, FuchsLogarithmBasisRefutation.sqrt_diag _ (fun _ => sq_nonneg _),
    Matrix.trace_diagonal]
  simp only [Real.sqrt_sq_eq_abs, map_sum]
  rfl

private lemma delta_ordered_identity (m : ℕ) (hm : 2 ≤ m) (t : ℝ) :
    delta m t = (2 : ℝ)⁻¹ ^ m / 2 * ((4 : ℝ)⁻¹ ^ m *
      ∑ w : BlockWord m, |Matrix.trace (word (Real.exp (-t)) m w) - 2|) := by
  let T : BlockWord m → ℝ := fun w => Matrix.trace (word (Real.exp (-t)) m w)
  let f : Config (2 * m) → ℝ := fun x =>
    (4 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ m * (T (blocks m x) - 2)
  have hd : evolution (2 * m) t (initial m) - stationary m =
      czxUnitary (2 * m) * Matrix.diagonal (fun x => (f x : ℂ)) := by
    let c : ℂ := 2 * ((2 : ℂ) ^ m)⁻¹
    have hconst : c • czxUnitary (2 * m) =
        czxUnitary (2 * m) * Matrix.diagonal (fun _ => c) := by
      have hc : (fun _ : Config (2 * m) => c) = c • (1 : Config (2 * m) → ℂ) := by
        funext x
        simp
      rw [hc, Matrix.diagonal_smul]
      change _ = czxUnitary (2 * m) * (c • Matrix.diagonal (fun _ => (1 : ℂ)))
      rw [Matrix.diagonal_one, Matrix.mul_smul, mul_one]
    rw [evolved_initial_transfer m hm t, stationary, ← smul_sub, add_sub_add_left_eq_sub,
      hconst, ← Matrix.mul_sub, ← Matrix.mul_smul, Matrix.diagonal_sub, ← Matrix.diagonal_smul]
    apply congrArg (fun d => czxUnitary (2 * m) * Matrix.diagonal d)
    funext x
    simp only [c, f, T, Pi.smul_apply, smul_eq_mul]
    push_cast
    simp only [inv_pow]
    ring
  rw [delta, hd, traceNorm_diagonal_sector]
  simp only [f, abs_mul, abs_pow, abs_inv, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← Finset.mul_sum]
  rw [(blocks m).sum_comp (fun w => |T w - 2|)]
  unfold T
  ring

private lemma centered_trace_le (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1) (m : ℕ) :
    (4 : ℝ)⁻¹ ^ m * (∑ w : BlockWord m, |Matrix.trace (word ρ m w) - 2|) ≤
      4 * growthFactor ρ ^ m := by
  let T := word ρ m
  let d := (4 : ℝ)⁻¹ ^ m
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hdiag (i : Fin 2) :
      d * (∑ w : BlockWord m, |T w i i|) ≤ growthFactor ρ ^ m := by
    let v : Row := PiLp.single 2 i 1
    have hv : ‖v‖ = 1 := by simp [v, PiLp.norm_single]
    calc
      _ ≤ average ρ m v := by
        apply mul_le_mul_of_nonneg_left _ hd
        apply Finset.sum_le_sum
        intro w _
        have hrow : rowAction v (T w) i = T w i i := by
          simp [rowAction, v, T]
        rw [← hrow, ← Real.norm_eq_abs]
        exact PiLp.norm_apply_le _ _
      _ ≤ _ := by simpa only [hv, mul_one] using (annealed_growth ρ hρ hρ₁ m v).2.2.2.2
  have hcard : Fintype.card (BlockWord m) = 4 ^ m := by
    simp [BlockWord, Letter, Fintype.card_prod]
  have hconst : d * (∑ _ : BlockWord m, (2 : ℝ)) = 2 := by
    simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat, d, inv_pow]
    field_simp
  have hq := (annealed_growth ρ hρ hρ₁ m (0 : Row)).2.2.2.1
  have hpow : 1 ≤ growthFactor ρ ^ m := one_le_pow₀ hq.le
  calc
    _ ≤ d * (∑ w : BlockWord m, (|T w 0 0| + |T w 1 1| + 2)) := by
      apply mul_le_mul_of_nonneg_left _ hd
      apply Finset.sum_le_sum
      intro w _
      change |Matrix.trace (T w) - 2| ≤ _
      have ht : Matrix.trace (T w) = T w 0 0 + T w 1 1 := by
        simp [Matrix.trace, Fin.sum_univ_two]
      rw [ht, sub_eq_add_neg]
      calc
        _ ≤ |T w 0 0 + T w 1 1| + |-(2 : ℝ)| := abs_add_le ..
        _ ≤ _ := by
          rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          exact add_le_add_left (abs_add_le _ _) _
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add, hconst]
      linarith [hdiag 0, hdiag 1]

/-- At positive fixed time the canonical trace distance decays exponentially in the half-size. -/
theorem fixed_time_delta_upper (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : 0 < t) :
    delta m t ≤ 2 * (growthFactor (Real.exp (-t)) / 2) ^ m := by
  rw [delta_ordered_identity m hm t]
  have h := centered_trace_le (Real.exp (-t)) (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)) m
  calc
    _ ≤ (2 : ℝ)⁻¹ ^ m / 2 * (4 * growthFactor (Real.exp (-t)) ^ m) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring

end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer
