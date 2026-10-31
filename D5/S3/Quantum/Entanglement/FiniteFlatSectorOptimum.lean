/- GID: D5/S3/Quantum/Entanglement/FiniteFlatSectorOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteFlatSectorOptimum
   mirror-E: none(waiver:finite-physical-channel-construction)
   anchors: []
   utility: none
   digest: The original compact flat sector encodings and their common local-channel optimum. -/

import D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
import D5.S3.Quantum.Entanglement.ExponentialSectorKernel
import D5.S3.Quantum.Reduction.CoherentFlagPort
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace D5.S3.Quantum.Entanglement.FiniteFlatSectorOptimum

open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker

variable {Sector : Type u} [Fintype Sector] [DecidableEq Sector]

/-- A finite common ambient list; each physical flat residual uses its initial segment. -/
def flatSpectrum (J m : ℕ) (j : Fin J) : ℝ :=
  if j.val < m then (m : ℝ)⁻¹ else 0

private theorem initial_segment_sum (J m : ℕ) (hmJ : m ≤ J) (c : ℝ) :
    (∑ j : Fin J, if j.val < m then c else 0) = (m : ℝ) * c := by
  induction J with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero hmJ
    subst m
    simp
  | succ J ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases hm : m ≤ J
    · rw [ih hm, if_neg (by omega)]
      ring
    · have hm : m = J + 1 := by omega
      subst m
      have hall : (∑ j : Fin J, if j.val < J + 1 then c else 0) = (J : ℝ) * c := by
        simp [show ∀ j : Fin J, j.val < J + 1 from fun j => by omega]
      rw [hall, if_pos (by omega)]
      push_cast
      ring

private theorem flat_spectrum_sum (J m : ℕ) (hm : 0 < m) (hmJ : m ≤ J) :
    (∑ j, flatSpectrum J m j) = 1 := by
  unfold flatSpectrum
  rw [initial_segment_sum J m hmJ]
  exact mul_inv_cancel₀ (by exact_mod_cast hm.ne')

private theorem flat_spectrum_antitone (J m : ℕ) : Antitone (flatSpectrum J m) := by
  intro i j hij
  unfold flatSpectrum
  split_ifs <;> first | positivity | omega | rfl

private theorem flat_gram (J m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmJ : m ≤ J) (hnJ : n ≤ J) :
    (∑ j, Real.sqrt (flatSpectrum J m j) * Real.sqrt (flatSpectrum J n j)) =
      Real.sqrt ((min m n : ℕ) / (max m n : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm (j : Fin J) :
      Real.sqrt (flatSpectrum J m j) * Real.sqrt (flatSpectrum J n j) =
        if j.val < min m n then Real.sqrt ((m : ℝ)⁻¹) * Real.sqrt ((n : ℝ)⁻¹)
        else 0 := by
    simp only [flatSpectrum, lt_min_iff]
    split_ifs <;> simp_all
  simp_rw [hterm]
  rw [initial_segment_sum J (min m n) (min_le_left _ _ |>.trans hmJ)]
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rcases le_total m n with h | h
  · rw [min_eq_left h, max_eq_right h]
    have hs := Real.sq_sqrt (show 0 ≤ (m : ℝ)⁻¹ by positivity)
    have ht := Real.sq_sqrt (show 0 ≤ (n : ℝ)⁻¹ by positivity)
    rw [mul_pow, mul_pow, hs, ht]
    field_simp
  · rw [min_eq_right h, max_eq_left h]
    have hs := Real.sq_sqrt (show 0 ≤ (m : ℝ)⁻¹ by positivity)
    have ht := Real.sq_sqrt (show 0 ≤ (n : ℝ)⁻¹ by positivity)
    rw [mul_pow, mul_pow, hs, ht]
    field_simp

private theorem flat_gram_log (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Real.sqrt ((min m n : ℕ) / (max m n : ℝ)) =
      Real.exp (-|Real.log (m : ℝ) - Real.log (n : ℝ)| / 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (Real.exp_pos _).le).mpr
  rw [← Real.exp_nat_mul]
  rcases le_total m n with h | h
  · have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hm0 (by exact_mod_cast h)
    rw [min_eq_left h, max_eq_right h, abs_of_nonpos (sub_nonpos.mpr hlog)]
    rw [show (2 : ℝ) * (-(-(Real.log (m : ℝ) - Real.log (n : ℝ))) / 2) =
      Real.log (m : ℝ) - Real.log (n : ℝ) by ring]
    rw [Real.exp_sub, Real.exp_log hm0, Real.exp_log hn0]
  · have hlog : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log hn0 (by exact_mod_cast h)
    rw [min_eq_right h, max_eq_left h, abs_of_nonneg (sub_nonneg.mpr hlog)]
    rw [show (2 : ℝ) * (-(Real.log (m : ℝ) - Real.log (n : ℝ)) / 2) =
      Real.log (n : ℝ) - Real.log (m : ℝ) by ring]
    rw [Real.exp_sub, Real.exp_log hn0, Real.exp_log hm0]

/-- Push forward actual sector probabilities by summing over each fiber. -/
def aggregate {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (p : A → ℝ) (b : B) : ℝ :=
  ∑ a, if f a = b then p a else 0

private theorem aggregate_sum {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) (p : A → ℝ) (g : B → ℝ) :
    (∑ b, aggregate f p b * g b) = ∑ a, p a * g (f a) := by
  classical
  simp only [aggregate, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

private theorem aggregate_simplex {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A) :
    aggregate f p ∈ stdSimplex ℝ B := by
  constructor
  · intro b
    exact Finset.sum_nonneg fun a _ => by
      dsimp [aggregate]
      split_ifs <;> first | exact hp.1 a | exact le_rfl
  · simpa using (aggregate_sum f p (fun _ => 1)).trans (by simpa using hp.2)

private theorem aggregate_energy {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) (p : A → ℝ) (K : B → B → ℝ) :
    (∑ b, ∑ c, aggregate f p b * aggregate f p c * K b c) =
      ∑ a, ∑ a', p a * p a' * K (f a) (f a') := by
  have hinner (b : B) :
      (∑ c, aggregate f p c * K b c) = ∑ a, p a * K b (f a) :=
    aggregate_sum f p (K b)
  calc
    _ = ∑ b, aggregate f p b * (∑ c, aggregate f p c * K b c) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ a, p a * (∑ c, aggregate f p c * K (f a) c) :=
      aggregate_sum f p _
    _ = _ := by
      simp_rw [hinner, Finset.mul_sum, mul_assoc]

private theorem aggregate_section {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) (g : B → A)
    (hg : Function.RightInverse g f) (q : B → ℝ) :
    aggregate f (aggregate g q) = q := by
  ext b
  have hterm (a : A) :
      (if f a = b then aggregate g q a else 0) =
      ∑ c, if g c = a then (if f a = b then q c else 0) else 0 := by
    by_cases h : f a = b <;> simp [aggregate, h]
  simp only [aggregate, hterm]
  rw [Finset.sum_comm]
  have hcollapse (c : B) :
      (∑ a, if g c = a then (if f a = b then q c else 0) else 0) =
      if c = b then q c else 0 := by
    simp [hg c]
  simp_rw [hcollapse]
  simp

private theorem sorted_rank_quotient [Nonempty Sector] (m : Sector → ℕ) :
    ∃ n : ℕ, ∃ a : Fin (n + 1) → ℕ, ∃ f : Sector → Fin (n + 1),
      StrictMono a ∧ Function.Surjective f ∧ (∀ s, a (f s) = m s) := by
  classical
  let ranks : Finset ℕ := Finset.univ.image m
  have hpos : 0 < ranks.card := by
    apply Finset.card_pos.mpr
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let n := ranks.card - 1
  have hc : ranks.card = n + 1 := by dsimp [n]; omega
  let e : Fin (n + 1) ≃o ranks := ranks.orderIsoOfFin hc
  let a : Fin (n + 1) → ℕ := fun i => (e i).val
  let f : Sector → Fin (n + 1) := fun s =>
    e.symm ⟨m s, Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩⟩
  have haf (s : Sector) : a (f s) = m s := by
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hf : Function.Surjective f := by
    intro i
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp (e i).property
    refine ⟨s, e.injective ?_⟩
    apply Subtype.ext
    exact (haf s).trans hs
  refine ⟨n, a, f, ?_, hf, haf⟩
  intro i j hij
  exact e.strictMono hij

private theorem exponential_quotient_minimum [Nonempty Sector]
    (m : Sector → ℕ) (hm : ∀ s, 0 < m s) :
    ∃ n : ℕ, ∃ a : Fin (n + 1) → ℕ, ∃ f : Sector → Fin (n + 1),
    ∃ loss : ℕ → ℝ,
      StrictMono a ∧ Function.Surjective f ∧ (∀ s, a (f s) = m s) ∧
      Monotone loss ∧ (∀ i : Fin (n + 1), loss i = Real.log (a i : ℝ)) ∧
      (∃ p ∈ stdSimplex ℝ Sector,
        (∑ s, ∑ t, p s * p t *
          Real.exp (-|Real.log (m s : ℝ) - Real.log (m t : ℝ)| / 2)) =
            1 / ExponentialSectorKernel.normalizer n loss) ∧
      (∀ p ∈ stdSimplex ℝ Sector,
        1 / ExponentialSectorKernel.normalizer n loss ≤
          ∑ s, ∑ t, p s * p t *
            Real.exp (-|Real.log (m s : ℝ) - Real.log (m t : ℝ)| / 2)) ∧
      ExponentialSectorKernel.normalizer n loss = 1 +
        ∑ i : Fin n, Real.tanh ((loss (i + 1) - loss i) / 4) := by
  classical
  obtain ⟨n, a, f, ha, hf, haf⟩ := sorted_rank_quotient m
  have ha0 (i : Fin (n + 1)) : 0 < a i := by
    obtain ⟨s, rfl⟩ := hf i
    rw [haf]
    exact hm s
  let loss : ℕ → ℝ := fun i => Real.log (a ⟨min i n, by omega⟩ : ℝ)
  have hloss (i : Fin (n + 1)) : loss i = Real.log (a i : ℝ) := by
    congr 2
    apply congrArg a
    apply Fin.ext
    exact min_eq_left (by omega)
  have hmono : Monotone loss := by
    intro i j hij
    apply Real.log_le_log (by exact_mod_cast ha0 ⟨min i n, by omega⟩)
    exact_mod_cast ha.monotone (show (⟨min i n, by omega⟩ : Fin (n + 1)) ≤
      ⟨min j n, by omega⟩ from min_le_min_right n hij)
  have hk (s t : Sector) :
      ExponentialSectorKernel.kernel loss (f s) (f t) =
        Real.exp (-|Real.log (m s : ℝ) - Real.log (m t : ℝ)| / 2) := by
    simp only [ExponentialSectorKernel.kernel, hloss, haf]
  obtain ⟨_, _, _, _, hZ, hq, henergy, hminimum, htotal, _⟩ :=
    ExponentialSectorKernel.result loss hmono n
  let q : Fin (n + 1) → ℝ := fun i =>
    ExponentialSectorKernel.equilibriumWeight n loss i /
      ExponentialSectorKernel.normalizer n loss
  choose g hg using hf
  let p := aggregate g q
  have hp : p ∈ stdSimplex ℝ Sector := aggregate_simplex g q hq
  have hpq : aggregate f p = q := aggregate_section f g hg q
  refine ⟨n, a, f, loss, ha, hf, haf, hmono, hloss, ?_, ?_, htotal⟩
  · refine ⟨p, hp, ?_⟩
    rw [← henergy]
    dsimp [ExponentialSectorKernel.energy]
    rw [← hpq, aggregate_energy]
    simp_rw [hk]
  · intro p hp
    have h := hminimum (aggregate f p) (aggregate_simplex f p hp)
    dsimp [ExponentialSectorKernel.energy] at h
    rw [aggregate_energy] at h
    simpa only [hk] using h

private def raw {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (C : QuantumChannel A B) :
    Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ :=
  CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    (C.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)

private theorem raw_comp {A B C : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (D : QuantumChannel B C) (E : QuantumChannel A B) (X : Matrix A A ℂ) :
    raw (D.comp E) X = raw D (raw E X) := by
  simp only [raw, LinearMap.comp_apply, QuantumChannel.comp_apply,
    Equiv.apply_symm_apply]

private theorem raw_expand {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (C : QuantumChannel A B) (X : Matrix A A ℂ) :
    raw C X = ∑ i, ∑ j, X i j • raw C (Matrix.single i j 1) := by
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single X
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul]

private def tensorMap {A B C D : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (L : QuantumChannel A C) (R : QuantumChannel B D) :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (C × D) (C × D) ℂ where
  toFun := tensorRawAction L R
  map_add' X Y := by
    ext p q
    simp only [tensorRawAction, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext p q
    simp only [tensorRawAction, Matrix.smul_apply, smul_eq_mul, mul_assoc,
      Finset.mul_sum]

private theorem tensor_kronecker {A B C D : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (L : QuantumChannel A C) (R : QuantumChannel B D)
    (X : Matrix A A ℂ) (Y : Matrix B B ℂ) :
    tensorRawAction L R (X ⊗ₖ Y) = raw L X ⊗ₖ raw R Y := by
  rw [raw_expand L X, raw_expand R Y]
  ext p q
  simp only [tensorRawAction, Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change X i j * Y k l * raw L (Matrix.single i j 1) p.1 q.1 *
      raw R (Matrix.single k l 1) p.2 q.2 = _
  ring

private theorem tensor_comp {A B C D E F : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (L : QuantumChannel A C) (R : QuantumChannel B D)
    (L' : QuantumChannel C E) (R' : QuantumChannel D F)
    (X : Matrix (A × B) (A × B) ℂ) :
    tensorRawAction (L'.comp L) (R'.comp R) X =
      tensorRawAction L' R' (tensorRawAction L R X) := by
  let P := tensorMap (L'.comp L) (R'.comp R)
  let Q := (tensorMap L' R').comp (tensorMap L R)
  have hsingle (i j : A × B) : P (Matrix.single i j 1) = Q (Matrix.single i j 1) := by
    have hs : Matrix.single i j (1 : ℂ) =
        Matrix.single i.1 j.1 (1 : ℂ) ⊗ₖ Matrix.single i.2 j.2 (1 : ℂ) := by
      rw [Matrix.single_kronecker_single, one_mul]
    change tensorRawAction (L'.comp L) (R'.comp R) _ =
      tensorRawAction L' R' (tensorRawAction L R _)
    rw [hs, tensor_kronecker, tensor_kronecker, tensor_kronecker,
      raw_comp, raw_comp]
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single X
  change P X = Q X
  rw [hX]
  simp only [map_sum, map_smul, hsingle]

private theorem isometry_channel {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (U : Matrix B A ℂ) (hU : Uᴴ * U = 1) :
    ∃ E : QuantumChannel A B, ∀ X : Matrix A A ℂ, raw E X = U * X * Uᴴ := by
  obtain ⟨E, hE⟩ := finite_kraus_quantum_channel (fun _ : Unit => U)
    (by simpa only [Fintype.sum_unique] using hU)
  exact ⟨E, fun X => by simpa only [Fintype.sum_unique] using hE X⟩

private theorem isometry_retraction {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Nonempty A]
    (U : Matrix B A ℂ) (hU : Uᴴ * U = 1) :
    ∃ E : QuantumChannel A B, ∃ R : QuantumChannel B A,
      (∀ X, raw E X = U * X * Uᴴ) ∧ (∀ X, raw R (raw E X) = X) := by
  classical
  let a₀ : A := Classical.choice inferInstance
  let u : Unit → A → ℂ := fun _ a => if a = a₀ then 1 else 0
  have hu : (∑ k, star (u k) ⬝ᵥ u k) = 1 := by
    simp [u, dotProduct, Pi.star_apply]
  obtain ⟨_, R, hR⟩ := D5.S3.Quantum.Reduction.CoherentFlagPort.padded_decoder_cptp
    U 1 hU (by simp) (by simp) u hu
  obtain ⟨E, hE⟩ := isometry_channel U hU
  refine ⟨E, R, hE, ?_⟩
  intro X
  rw [hE]
  change CStarMatrix.ofMatrix.symm
    (R.toCompletelyPositiveMap (CStarMatrix.ofMatrix (U * X * Uᴴ))) = X
  rw [hR]
  have hzero : (1 - U * Uᴴ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have htrace : Matrix.trace ((1 - U * Uᴴ) * (U * X * Uᴴ)) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hzero, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.trace_zero]
  rw [htrace, zero_smul, add_zero]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one]

/-- The compact coordinate `a + d s * b` is split before the residual is padded. -/
private def compactSplit (r d m : Sector → ℕ) (hr : ∀ s, r s = d s * m s) :
    TargetLocal r ≃ (Σ s, Fin (d s) × Fin (m s)) :=
  Equiv.sigmaCongrRight fun s =>
    ((finCongr ((hr s).trans (Nat.mul_comm _ _))).trans finProdFinEquiv.symm).trans
      (Equiv.prodComm _ _)

private def residualInclusion (d m : Sector → ℕ) (J : ℕ) (hmJ : ∀ s, m s ≤ J) :
    (Σ s, Fin (d s) × Fin (m s)) ↪ SourceLocal (Coord := Fin J) d where
  toFun x := ⟨x.1, (x.2.1, ⟨x.2.2.val, x.2.2.isLt.trans_le (hmJ x.1)⟩)⟩
  inj' := by
    rintro ⟨s, a, b⟩ ⟨t, c, e⟩ h
    have hst : s = t := congrArg Sigma.fst h
    subst t
    have hp : (a, (⟨b.val, b.isLt.trans_le (hmJ s)⟩ : Fin J)) =
        (c, (⟨e.val, e.isLt.trans_le (hmJ s)⟩ : Fin J)) := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
    have ha : a = c := congrArg Prod.fst hp
    have hb : b = e := Fin.ext (congrArg (fun z => z.2.val) hp)
    subst c
    subst e
    rfl

private def compactEmbedding (r d m : Sector → ℕ) (J : ℕ)
    (hr : ∀ s, r s = d s * m s) (hmJ : ∀ s, m s ≤ J) :
    TargetLocal r ↪ SourceLocal (Coord := Fin J) d :=
  (compactSplit r d m hr).toEmbedding.trans (residualInclusion d m J hmJ)

private theorem compact_embedding_sector (r d m : Sector → ℕ) (J : ℕ)
    (hr : ∀ s, r s = d s * m s) (hmJ : ∀ s, m s ≤ J) (x : TargetLocal r) :
    (compactEmbedding r d m J hr hmJ x).1 = x.1 := rfl

private theorem compact_embedding_range (r d m : Sector → ℕ) (J : ℕ)
    (hr : ∀ s, r s = d s * m s) (hmJ : ∀ s, m s ≤ J)
    (y : SourceLocal (Coord := Fin J) d) :
    (∃ x, compactEmbedding r d m J hr hmJ x = y) ↔ y.2.2.val < m y.1 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (compactSplit r d m hr x).2.2.isLt
  · intro hy
    let z : Σ s, Fin (d s) × Fin (m s) := ⟨y.1, (y.2.1, ⟨y.2.2.val, hy⟩)⟩
    refine ⟨(compactSplit r d m hr).symm z, ?_⟩
    change residualInclusion d m J hmJ
      (compactSplit r d m hr ((compactSplit r d m hr).symm z)) = y
    rw [Equiv.apply_symm_apply]
    rfl

/-- A zero-one placement matrix preserves all coherences, including between sectors. -/
private def placement {A B : Type u} [DecidableEq B] (f : A ↪ B) : Matrix B A ℂ :=
  fun b a => if f a = b then 1 else 0

private theorem placement_isometry {A B : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (f : A ↪ B) :
    (placement f)ᴴ * placement f = 1 := by
  ext a c
  simp [placement, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    ite_mul, mul_ite, f.injective.eq_iff, eq_comm]

private theorem placement_tensor {A B : Type u}
    [DecidableEq B] (f : A ↪ B) :
    placement f ⊗ₖ placement f = placement (f.prodMap f) := by
  ext b a
  simp [placement, Matrix.kroneckerMap_apply, Prod.ext_iff, ite_and]

private theorem placement_mul_image {A B C : Type u}
    [Fintype A] [DecidableEq B] (f : A ↪ B) (X : Matrix A C ℂ) (a : A) (c : C) :
    (placement f * X) (f a) c = X a c := by
  classical
  simp [placement, Matrix.mul_apply, f.injective.eq_iff, ite_mul]

private theorem placement_mul_outside {A B C : Type u}
    [Fintype A] [DecidableEq B] (f : A ↪ B) (X : Matrix A C ℂ) (b : B) (c : C)
    (hb : ¬ ∃ a, f a = b) : (placement f * X) b c = 0 := by
  have hne (a : A) : f a ≠ b := fun h => hb ⟨a, h⟩
  simp [placement, Matrix.mul_apply, hne]

private theorem compact_flat_coefficient (r d m : Sector → ℕ) (J : ℕ)
    (hr : ∀ s, r s = d s * m s) (hmJ : ∀ s, m s ≤ J)
    (x y : TargetLocal r) (s : Sector) :
    sourceEncoding d (fun s => flatSpectrum J (m s))
        (compactEmbedding r d m J hr hmJ x, compactEmbedding r d m J hr hmJ y) s =
      targetEncoding r (x, y) s := by
  let f := compactEmbedding r d m J hr hmJ
  have hsupport : (f x).2.2.val < m x.1 :=
    (compact_embedding_range r d m J hr hmJ (f x)).mp ⟨x, rfl⟩
  have hscalar : (m x.1 : ℝ)⁻¹ / (d x.1 : ℝ) = (r x.1 : ℝ)⁻¹ := by
    simp [hr, div_eq_mul_inv, mul_comm]
  change (if f x = f y ∧ x.1 = s then
      (Real.sqrt (flatSpectrum J (m x.1) (f x).2.2 / (d x.1 : ℝ)) : ℂ)
    else 0) = targetEncoding r (x, y) s
  simp only [f.injective.eq_iff, targetEncoding]
  by_cases h : x = y ∧ x.1 = s
  · simp only [if_pos h, flatSpectrum, if_pos hsupport, hscalar]
  · simp only [if_neg h]

/-- This is equality of the full source isometries, rather than only their basis densities. -/
private theorem compact_flat_encoding (r d m : Sector → ℕ) (J : ℕ)
    (hr : ∀ s, r s = d s * m s) (hmJ : ∀ s, m s ≤ J) :
    (placement (compactEmbedding r d m J hr hmJ) ⊗ₖ
      placement (compactEmbedding r d m J hr hmJ)) * targetEncoding r =
      sourceEncoding d (fun s => flatSpectrum J (m s)) := by
  let f := compactEmbedding r d m J hr hmJ
  rw [placement_tensor]
  ext y s
  by_cases hy : ∃ x, (f.prodMap f) x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [placement_mul_image]
    exact (compact_flat_coefficient r d m J hr hmJ x.1 x.2 s).symm
  · rw [placement_mul_outside _ _ _ _ hy]
    symm
    by_cases hdiag : y.1 = y.2
    · have hout : ¬ y.1.2.2.val < m y.1.1 := by
        intro hin
        obtain ⟨a, ha⟩ := (compact_embedding_range r d m J hr hmJ y.1).mpr hin
        exact hy ⟨(a, a), Prod.ext ha (ha.trans hdiag)⟩
      simp [sourceEncoding, flatSpectrum, hout]
    · simp [sourceEncoding, hdiag]

end D5.S3.Quantum.Entanglement.FiniteFlatSectorOptimum
