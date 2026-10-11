/- GID: D5/S3/Quantum/Dynamics/FinitePureOrbitExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/FinitePureOrbitExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dimension potential and invariant word spaces for finite pure orbit extension. -/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Matrix.Dual

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.FinitePureOrbitExtension

open Module Finset
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel

/-- A rank-one sum of outer products has one common direction. -/
private theorem rank_one_sum_collinear {a κ : Type*} [Fintype a] [DecidableEq a] [Fintype κ]
    (φ : a → ℂ) (v : κ → a → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hv : ∑ u, vecMulVec (v u) (star (v u)) = vecMulVec φ (star φ)) :
    (∀ u, v u = (star φ ⬝ᵥ v u) • φ) ∧
      ∑ u, star (star φ ⬝ᵥ v u) * (star φ ⬝ᵥ v u) = 1 := by
  classical
  let Z : Matrix a κ ℂ := fun i u => v u i
  let P := vecMulVec φ (star φ)
  have hZ : Z * Z.conjTranspose = P := by
    calc
      Z * Z.conjTranspose = ∑ u, vecMulVec (v u) (star (v u)) := by
        ext i j
        change (∑ u, v u i * star (v u j)) = _
        simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply]
      _ = P := hv
  have hproj : (1 - P) * P = 0 := by
    simp [P, Matrix.sub_mul, vecMulVec_mul_vecMulVec, hφ]
  have hz : (1 - P) * Z = 0 := by
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Z, hZ,
      ← Matrix.mul_assoc, hproj, Matrix.zero_mul]
    simp
  have hfix : Z = P * Z := by
    simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] using hz
  have hcol (u : κ) : v u = (star φ ⬝ᵥ v u) • φ := by
    funext i
    have hi := congrFun₂ hfix i u
    change v u i = ∑ j, (φ i * star (φ j)) * v u j at hi
    simpa [dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hi
  refine ⟨hcol, ?_⟩
  have ht := congrArg Matrix.trace hv
  rw [trace_sum, trace_vecMulVec, dotProduct_comm, hφ] at ht
  have hunit : φ ⬝ᵥ star φ = 1 := (dotProduct_comm _ _).trans hφ
  simp_rw [trace_vecMulVec] at ht
  conv at ht => lhs; arg 2; ext u; rw [hcol u]
  simpa only [star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hunit, mul_one, one_mul, mul_comm] using ht

private theorem unit_of_state_eq {a : Type*} [Fintype a] [DecidableEq a]
    (ρ : DensityState a) (v : a → ℂ)
    (hv : ρ.1 = CStarMatrix.ofMatrix (vecMulVec v (star v))) :
    star v ⬝ᵥ v = 1 := by
  have ht := ρ.2.2
  rw [hv] at ht
  exact (dotProduct_comm _ _).trans ((trace_vecMulVec _ _).symm.trans ht)

/-- Pure channel output supplies normalized coefficients for the same Kraus table. -/
private theorem kraus_collinear_of_pure_output {d : ℕ} {κ : Type*} [Fintype κ]
    (channel : QuantumChannel (Fin d) (Fin d))
    (K : κ → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ u, K u * X * (K u).conjTranspose)
    (ψ φ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hout : (channel.mapState (pureState ψ hψ)).1 =
      CStarMatrix.ofMatrix (vecMulVec φ (star φ))) :
    ∃ c : κ → ℂ,
      (∀ u, (K u) *ᵥ ψ = c u • φ) ∧
      ∑ u, star (c u) * c u = 1 := by
  have hφ := unit_of_state_eq _ φ hout
  have hsum : ∑ u, vecMulVec (K u *ᵥ ψ) (star (K u *ᵥ ψ)) =
      vecMulVec φ (star φ) := by
    have h := hK (vecMulVec ψ (star ψ))
    have ho := congrArg CStarMatrix.ofMatrix.symm hout
    change CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (vecMulVec ψ (star ψ)))) =
        vecMulVec φ (star φ) at ho
    rw [h] at ho
    simpa only [mul_vecMulVec, vecMulVec_mul, star_mulVec] using ho
  exact ⟨fun u => star φ ⬝ᵥ (K u *ᵥ ψ), rank_one_sum_collinear φ _ hφ hsum⟩

private theorem mass_cast {a : Type*} [Fintype a] (v : a → ℂ) :
    ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, dotProduct,
    Pi.star_apply, Complex.star_def]

private theorem mass_pos {a : Type*} [Fintype a] (v : a → ℂ) (hv : v ≠ 0) :
    0 < ∑ i, Complex.normSq (v i) := by
  have h := (dotProduct_star_self_pos_iff (v := v)).mpr hv
  rw [← mass_cast] at h
  exact_mod_cast h

private theorem normalization_weight {a : Type*} [Fintype a] (v : a → ℂ) :
    star ((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) *
        ((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)⁻¹ := by
  rw [star_inv₀]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (v i)))]

private theorem normalized_unit {a : Type*} [Fintype a] (v : a → ℂ) (hv : v ≠ 0) :
    star (((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) • v) ⬝ᵥ
      (((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) • v) = 1 := by
  rw [star_smul, smul_dotProduct, dotProduct_smul]
  change star _ * (_ * (star v ⬝ᵥ v)) = 1
  rw [← mul_assoc, normalization_weight, ← mass_cast]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (mass_pos v hv)))

/-- A nonzero direction normalized by its Euclidean squared mass. -/
def directionState {a : Type*} [Fintype a] [DecidableEq a]
    (v : a → ℂ) (hv : v ≠ 0) : DensityState a :=
  pureState (((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) • v)
    (normalized_unit v hv)

private theorem directionState_value {a : Type*} [Fintype a] [DecidableEq a]
    (v : a → ℂ) (hv : v ≠ 0) :
    (directionState v hv).1 =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)⁻¹ •
        CStarMatrix.ofMatrix (vecMulVec v (star v)) := by
  change CStarMatrix.ofMatrix (vecMulVec (_ • v) (star (_ • v))) = _
  rw [star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, mul_comm,
    normalization_weight]
  rfl

/-- Collinear Kraus images give an exact transition between normalized directions.
Trace preservation supplies the scale; the linear motion need not preserve norms. -/
theorem map_directionState_of_collinear {d : ℕ} {κ : Type*} [Fintype κ]
    (channel : QuantumChannel (Fin d) (Fin d))
    (K : κ → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ u, K u * X * (K u).conjTranspose)
    (v w : Fin d → ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (μ : κ → ℂ)
    (hcol : ∀ u, K u *ᵥ v = μ u • w) :
    channel.mapState (directionState v hv) = directionState w hw := by
  let a : ℂ := ∑ u, μ u * star (μ u)
  have hraw : channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (vecMulVec v (star v))) =
      a • CStarMatrix.ofMatrix (vecMulVec w (star w)) := by
    have h := hK (vecMulVec v (star v))
    apply CStarMatrix.ofMatrix.symm.injective
    change CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (vecMulVec v (star v)))) =
        a • vecMulVec w (star w)
    rw [h]
    simp_rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hcol,
      star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul]
    exact (Finset.sum_smul ..).symm
  let b := ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)⁻¹ * a
  have hb : (channel.mapState (directionState v hv)).1 =
      b • CStarMatrix.ofMatrix (vecMulVec w (star w)) := by
    rw [QuantumChannel.mapState_value, directionState_value, map_smul, hraw, smul_smul]
  have ht : b * ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) = 1 := by
    have h := (channel.mapState (directionState v hv)).2.2
    rw [hb] at h
    change Matrix.trace (b • vecMulVec w (star w)) = 1 at h
    simpa only [trace_smul, trace_vecMulVec, dotProduct_comm w,
      ← mass_cast, smul_eq_mul] using h
  have hc : b = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ)⁻¹ := by
    have hn := Complex.ofReal_ne_zero.mpr (ne_of_gt (mass_pos w hw))
    simpa using (eq_div_of_mul_eq hn ht)
  apply Subtype.ext
  rw [hb, hc, directionState_value]

/-- A finite pure history admits one linear orbit with the same Kraus directions.
The coefficients selecting the linear map work simultaneously at every prefix time. -/
theorem linear_lift_of_pure_prefix {d N : ℕ} {κ : Type*} [Fintype κ]
    (channel : QuantumChannel (Fin d) (Fin d))
    (K : κ → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ u, K u * X * (K u).conjTranspose)
    (ρ : ℕ → DensityState (Fin d))
    (hstep : ∀ n < N, ρ (n + 1) = channel.mapState (ρ n))
    (hpure : ∀ n ≤ N, IsPure (ρ n)) :
    ∃ (A : Module.End ℂ (Fin d → ℂ)) (x : Fin d → ℂ),
      (∃ hx : x ≠ 0, directionState x hx = ρ 0) ∧
      (∀ n ≤ N, (A ^ n) x ≠ 0) ∧
      ∀ n < N, ∃ μ : κ → ℂ,
        ∀ u, K u *ᵥ ((A ^ n) x) =
          μ u • ((A ^ (n + 1)) x) := by
  classical
  let ψ (n : ℕ) : Fin d → ℂ := if h : n ≤ N then (hpure n h).choose else 0
  have hψ (n : ℕ) (hn : n ≤ N) :
      (ρ n).1 = CStarMatrix.ofMatrix (vecMulVec (ψ n) (star (ψ n))) := by
    simpa only [ψ, dif_pos hn] using (hpure n hn).choose_spec
  have hu (n : ℕ) (hn : n ≤ N) : star (ψ n) ⬝ᵥ ψ n = 1 :=
    unit_of_state_eq _ _ (hψ n hn)
  have hnz (n : ℕ) (hn : n ≤ N) : ψ n ≠ 0 := by
    intro hz
    simpa [hz] using hu n hn
  have hc (n : Fin N) : ∃ c : κ → ℂ,
      (∀ u, K u *ᵥ ψ n =
        c u • ψ (n + 1)) ∧ ∑ u, star (c u) * c u = 1 := by
    apply kraus_collinear_of_pure_output channel K hK _ _ (hu n n.isLt.le)
    have heq : pureState (ψ n) (hu n n.isLt.le) = ρ n :=
      Subtype.ext (hψ n n.isLt.le).symm
    rw [heq, ← hstep n n.isLt]
    exact hψ (n + 1) n.isLt
  choose c hcol hweight using hc
  obtain ⟨h, hh⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun n : Fin N => dotProductEquiv ℂ κ (c n)) (by
      intro n
      refine ⟨star (c n), ?_⟩
      change c n ⬝ᵥ star (c n) ≠ 0
      rw [dotProduct_comm]
      exact (hweight n).trans_ne one_ne_zero)
  let A : Module.End ℂ (Fin d → ℂ) :=
    ∑ u, h u • (K u).mulVecLin
  have hact (n : Fin N) : A (ψ n) = (c n ⬝ᵥ h) • ψ (n + 1) := by
    simp only [A, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply, hcol,
      smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    exact dotProduct_comm _ _
  have horbit : ∀ n ≤ N, ∃ a : ℂ, a ≠ 0 ∧ (A ^ n) (ψ 0) = a • ψ n := by
    intro n
    induction n with
    | zero => intro _; exact ⟨1, one_ne_zero, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨a, ha, heq⟩ := ih (by omega)
      let i : Fin N := ⟨n, hn⟩
      refine ⟨a * (c i ⬝ᵥ h), mul_ne_zero ha (hh i), ?_⟩
      rw [pow_succ', Module.End.mul_apply, heq, map_smul, hact i, smul_smul]
  refine ⟨A, ψ 0, ?_, ?_, ?_⟩
  · refine ⟨hnz 0 (Nat.zero_le _), ?_⟩
    apply Subtype.ext
    rw [directionState_value, mass_cast, hu 0 (Nat.zero_le _), inv_one, one_smul]
    exact (hψ 0 (Nat.zero_le _)).symm
  · intro n hn
    obtain ⟨a, ha, heq⟩ := horbit n hn
    rw [heq]
    exact smul_ne_zero ha (hnz n hn)
  · intro n hn
    let i : Fin N := ⟨n, hn⟩
    obtain ⟨a, ha, heq⟩ := horbit n hn.le
    refine ⟨fun u => c i u / (c i ⬝ᵥ h), ?_⟩
    intro u
    rw [pow_succ', Module.End.mul_apply, heq, map_smul, hact i,
      Matrix.mulVec_smul, hcol i, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp [show c i ⬝ᵥ h ≠ 0 from hh i]

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype ι]

/-- The nonnegative contribution of a word space, with zero spaces contributing zero. -/
def spacePotential (P : Submodule K V) : ℕ := 2 * finrank K P - 1

/-- Directions following a fixed finite word of subspaces. -/
def wordSpace (A : V ≃ₗ[K] V) (S : ι → Submodule K V) {n : ℕ}
    (w : Fin n → ι) : Submodule K V :=
  ⨅ j : Fin n, (S (w j)).comap ((A ^ (j : ℕ)).toLinearMap)

/-- Sum over all words; zero word spaces contribute zero. -/
def wordPotential (A : V ≃ₗ[K] V) (S : ι → Submodule K V) (n : ℕ) : ℕ :=
  ∑ w : Fin n → ι, spacePotential (wordSpace A S w)

private theorem sum_finrank_le (P : Submodule K V) (Q : ι → Submodule K V)
    (hQ : iSupIndep Q) (hle : ∀ i, Q i ≤ P) :
    ∑ i, finrank K (Q i) ≤ finrank K P := by
  classical
  have hf : Function.Injective (DirectSum.coeLinearMap Q) := hQ.dfinsupp_lsum_injective
  rw [← Module.finrank_directSum, ← LinearMap.finrank_range_of_inj hf,
    DirectSum.range_coeLinearMap]
  exact Submodule.finrank_mono (iSup_le hle)

omit [Fintype ι] in
private theorem sum_weight_le (s : Finset ι) (a : ι → ℕ) :
    (∑ i ∈ s, (2 * a i - 1)) ≤ 2 * (∑ i ∈ s, a i) - 1 := by
  exact Finset.le_sum_of_subadditive (N := OrderDual ℕ) (fun n : ℕ => (2 * n - 1 : ℕ))
    (by decide) (by intro a b; change 2 * a - 1 + (2 * b - 1) ≤ 2 * (a + b) - 1; omega) s a

omit [Fintype ι] in
private theorem sum_weight_lt (s : Finset ι) (a : ι → ℕ) (q : ℕ)
    (hq : 0 < q) (hs : ∑ i ∈ s, a i ≤ q) (ha : ∀ i ∈ s, a i < q) :
    (∑ i ∈ s, (2 * a i - 1)) < 2 * q - 1 := by
  classical
  have hb := sum_weight_le s a
  by_cases hlt : ∑ i ∈ s, a i < q
  · omega
  have heq : ∑ i ∈ s, a i = q := by omega
  obtain ⟨i, hi, hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => Nat.zero_le (a i))).mp
    (show 0 < ∑ i ∈ s, a i by omega)
  have hrest := sum_weight_le (s.erase i) a
  have hsum := Finset.sum_erase_add s a hi
  have hweights := Finset.sum_erase_add s (fun j => 2 * a j - 1) hi
  have hai := ha i hi
  omega

private theorem refinement_le (P : Submodule K V) (Q : ι → Submodule K V)
    (hQ : iSupIndep Q) (hle : ∀ i, Q i ≤ P) :
    (∑ i, spacePotential (Q i)) ≤ spacePotential P := by
  have hdim := sum_finrank_le P Q hQ hle
  have hw := sum_weight_le univ (fun i => finrank K (Q i))
  unfold spacePotential
  omega

private theorem refinement_lt (P : Submodule K V) (Q : ι → Submodule K V)
    (hQ : iSupIndep Q) (hle : ∀ i, Q i ≤ P) (hP : P ≠ ⊥)
    (hne : ∀ i, Q i ≠ P) :
    (∑ i, spacePotential (Q i)) < spacePotential P := by
  apply sum_weight_lt univ (fun i => finrank K (Q i)) (finrank K P)
  · exact Nat.pos_of_ne_zero (fun hz => hP (Submodule.finrank_eq_zero.mp hz))
  · exact sum_finrank_le P Q hQ hle
  · intro i _
    exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hle i) (hne i))

omit [FiniteDimensional K V] [Fintype ι] in
private theorem wordSpace_snoc (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    {n : ℕ} (w : Fin n → ι) (i : ι) :
    wordSpace A S (Fin.snoc w i) =
      wordSpace A S w ⊓ (S i).comap (A ^ n).toLinearMap := by
  ext x
  simp only [wordSpace, Submodule.mem_iInf, Submodule.mem_inf, Submodule.mem_comap]
  constructor
  · intro hx
    exact ⟨fun j => by simpa using hx j.castSucc, by simpa using hx (Fin.last n)⟩
  · rintro ⟨hx, hi⟩ j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa using hi
    · simpa using hx k

omit [FiniteDimensional K V] [Fintype ι] in
private theorem pullback_independent (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (hS : iSupIndep S) (n : ℕ) :
    iSupIndep (fun i => (S i).comap (A ^ n).toLinearMap) :=
  hS.map_orderIso (Submodule.orderIsoMapComap (A ^ n)).symm

omit [FiniteDimensional K V] in
private theorem wordPotential_succ (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (n : ℕ) :
    wordPotential A S (n + 1) =
      ∑ w : Fin n → ι, ∑ i : ι,
        spacePotential (wordSpace A S w ⊓ (S i).comap (A ^ n).toLinearMap) := by
  rw [wordPotential, ← (Fin.snocEquiv (fun _ : Fin (n + 1) => ι)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ i : ι, ∑ w : Fin n → ι, spacePotential (wordSpace A S (Fin.snoc w i))) = _
  simp_rw [wordSpace_snoc]
  exact Finset.sum_comm

private theorem wordPotential_le (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (hS : iSupIndep S) (n : ℕ) :
    wordPotential A S (n + 1) ≤ wordPotential A S n := by
  rw [wordPotential_succ, wordPotential]
  apply Finset.sum_le_sum
  intro w _
  exact refinement_le _ _ ((pullback_independent A S hS n).mono (fun _ => inf_le_right))
    (fun _ => inf_le_left)

private theorem unchanged_extension (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (hS : iSupIndep S) {n : ℕ}
    (heq : wordPotential A S (n + 1) = wordPotential A S n)
    (w : Fin n → ι) (hw : wordSpace A S w ≠ ⊥) :
    ∃ i, wordSpace A S (Fin.snoc w i) = wordSpace A S w := by
  classical
  by_contra! h
  have hstrict : (∑ i : ι,
      spacePotential (wordSpace A S w ⊓ (S i).comap (A ^ n).toLinearMap)) <
        spacePotential (wordSpace A S w) := by
    apply refinement_lt _ _ ((pullback_independent A S hS n).mono (fun _ => inf_le_right))
      (fun _ => inf_le_left) hw
    intro i
    simpa only [wordSpace_snoc] using h i
  have hlt : wordPotential A S (n + 1) < wordPotential A S n := by
    rw [wordPotential_succ, wordPotential]
    apply Finset.sum_lt_sum
    · intro v _
      exact refinement_le _ _
        ((pullback_independent A S hS n).mono (fun _ => inf_le_right))
        (fun _ => inf_le_left)
    · exact ⟨w, mem_univ _, hstrict⟩
  omega

private theorem stable_word_forward (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (hS : iSupIndep S) {n : ℕ}
    (heq : wordPotential A S (n + 1) = wordPotential A S n)
    {x : V} (hx : x ≠ 0) (hw : ∃ w : Fin n → ι, x ∈ wordSpace A S w) :
    ∃ w : Fin n → ι, A x ∈ wordSpace A S w := by
  obtain ⟨w, hw⟩ := hw
  have hne : wordSpace A S w ≠ ⊥ := (wordSpace A S w).ne_bot_iff.mpr ⟨x, hw, hx⟩
  obtain ⟨i, hi⟩ := unchanged_extension A S hS heq w hne
  have hext : x ∈ wordSpace A S (Fin.snoc w i) := hi.symm ▸ hw
  let wext : Fin (n + 1) → ι := Fin.snoc w i
  refine ⟨fun j : Fin n => wext j.succ, ?_⟩
  simp only [wordSpace, Submodule.mem_iInf, Submodule.mem_comap] at hext ⊢
  intro j
  have hj := hext j.succ
  simpa [pow_succ, LinearEquiv.mul_apply, wext] using hj

private theorem stable_word_orbit (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (hS : iSupIndep S) {n : ℕ} (hn : 0 < n)
    (heq : wordPotential A S (n + 1) = wordPotential A S n)
    {x : V} (hx : x ≠ 0) (hw : ∃ w : Fin n → ι, x ∈ wordSpace A S w) :
    ∀ k : ℕ, ∃ i, (A ^ k) x ∈ S i := by
  have hwords : ∀ k : ℕ, ∃ w : Fin n → ι, (A ^ k) x ∈ wordSpace A S w := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      have hne : (A ^ k) x ≠ 0 := (A ^ k).map_ne_zero_iff.mpr hx
      simpa [pow_succ', LinearEquiv.mul_apply] using
        stable_word_forward A S hS heq hne ih
  intro k
  obtain ⟨w, hw⟩ := hwords k
  refine ⟨w ⟨0, hn⟩, ?_⟩
  simp only [wordSpace, Submodule.mem_iInf, Submodule.mem_comap] at hw
  simpa using hw ⟨0, hn⟩

omit [FiniteDimensional K V] [Fintype ι] in
private theorem prefix_word (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (x : V) (n : ℕ) (h : ∀ j < n, ∃ i, (A ^ j) x ∈ S i) :
    ∃ w : Fin n → ι, x ∈ wordSpace A S w := by
  classical
  choose w hw using fun j : Fin n => h j j.isLt
  refine ⟨w, ?_⟩
  simp only [wordSpace, Submodule.mem_iInf, Submodule.mem_comap]
  intro j
  exact hw j

private theorem positive_wordPotential (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    {x : V} (hx : x ≠ 0) {n : ℕ} (hw : ∃ w : Fin n → ι, x ∈ wordSpace A S w) :
    0 < wordPotential A S n := by
  obtain ⟨w, hw⟩ := hw
  have hne : wordSpace A S w ≠ ⊥ := (wordSpace A S w).ne_bot_iff.mpr ⟨x, hw, hx⟩
  have hd : 0 < finrank K (wordSpace A S w) :=
    Nat.pos_of_ne_zero (fun hz => hne (Submodule.finrank_eq_zero.mp hz))
  have hle : spacePotential (wordSpace A S w) ≤ wordPotential A S n := by
    exact Finset.single_le_sum (f := fun v => spacePotential (wordSpace A S v))
      (fun _ _ => Nat.zero_le _) (mem_univ w)
  unfold spacePotential at hle
  omega

omit [FiniteDimensional K V] in
private theorem wordPotential_one (A : V ≃ₗ[K] V) (S : ι → Submodule K V) :
    wordPotential A S 1 = ∑ i, spacePotential (S i) := by
  unfold wordPotential
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι)
  intro w
  simp [wordSpace, Equiv.funUnique, Equiv.piUnique]

private theorem initial_potential_bound (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (hS : iSupIndep S) (hne : ∀ i, S i ≠ ⊥) (hcard : 2 ≤ Fintype.card ι) :
    wordPotential A S 1 ≤ 2 * finrank K V - 2 := by
  have hdim := sum_finrank_le (⊤ : Submodule K V) S hS (fun _ => le_top)
  simp only [finrank_top] at hdim
  have hpos (i : ι) : 1 ≤ 2 * finrank K (S i) := by
    have hi : 0 < finrank K (S i) :=
      Nat.pos_of_ne_zero (fun hz => hne i (Submodule.finrank_eq_zero.mp hz))
    omega
  rw [wordPotential_one]
  unfold spacePotential
  rw [Finset.sum_tsub_distrib univ (fun i _ => hpos i), ← Finset.mul_sum]
  simp only [sum_const, card_univ, smul_eq_mul, mul_one]
  omega

/-- An invertible linear orbit which stays in a finite independent family of nonzero
subspaces for `2 dim(V) - 1` steps stays there forever. The word-space potential
stabilizes strictly before that prefix is exhausted. No orthogonality is assumed. -/
theorem pure_prefix_potential_stabilizes (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (hS : iSupIndep S) (hne : ∀ i, S i ≠ ⊥) (hcard : 2 ≤ Fintype.card ι)
    (x : V) (hx : x ≠ 0)
    (hprefix : ∀ j < 2 * finrank K V - 1, ∃ i, (A ^ j) x ∈ S i) :
    (∃ L, 1 ≤ L ∧ L < 2 * finrank K V - 1 ∧
      wordPotential A S (L + 1) = wordPotential A S L) ∧
    ∀ k : ℕ, ∃ i, (A ^ k) x ∈ S i := by
  classical
  let N := 2 * finrank K V - 1
  have hNpos : 0 < N := by
    have hd : 0 < finrank K V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx⟩
    omega
  have hlast : 0 < wordPotential A S N :=
    positive_wordPotential A S hx (prefix_word A S x N hprefix)
  have hbound := initial_potential_bound A S hS hne hcard
  have hstable : ∃ L, 1 ≤ L ∧ L < N ∧
      wordPotential A S (L + 1) = wordPotential A S L := by
    by_contra! h
    have hdrop : AntitoneOn (fun k => wordPotential A S (k + 1) + k) (Set.Iio N) := by
      apply antitoneOn_of_succ_le Set.ordConnected_Iio
      intro k _ _ hk
      change k + 1 < N at hk
      change wordPotential A S (k + 1 + 1) + (k + 1) ≤ wordPotential A S (k + 1) + k
      have hle := wordPotential_le A S hS (k + 1)
      have hne' := h (k + 1) (by omega) hk
      omega
    have hfinal := hdrop (show 0 ∈ Set.Iio N from hNpos)
      (show N - 1 ∈ Set.Iio N by change N - 1 < N; omega) (Nat.zero_le _)
    simp only [zero_add, add_zero] at hfinal
    have hindex : N - 1 + 1 = N := by omega
    rw [hindex] at hfinal
    dsimp [N] at *
    omega
  refine ⟨hstable, ?_⟩
  obtain ⟨L, hL, hLN, hLeq⟩ := hstable
  apply stable_word_orbit A S hS hL hLeq hx
  exact prefix_word A S x L (fun j hj => hprefix j (lt_trans hj hLN))

private theorem krylov_independent (A : Module.End K V) (x : V) (n : ℕ)
    (h : ∀ j < n, (A ^ j) x ∉
      Submodule.span K (Set.range (fun i : Fin j => (A ^ (i : ℕ)) x))) :
    LinearIndependent K (fun i : Fin n => (A ^ (i : ℕ)) x) := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
    have heq : (fun i : Fin (n + 1) => (A ^ (i : ℕ)) x) =
        Fin.snoc (fun i : Fin n => (A ^ (i : ℕ)) x) ((A ^ n) x) := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [heq]
    exact (ih (fun j hj => h j (by omega))).finSnoc (h n (by omega))

/-- The first Krylov dependence produces a cyclic invertible tail, with its
transient length and tail dimension controlled jointly by the ambient dimension. -/
private theorem krylov_invertible_tail (A : Module.End K V) (x : V)
    (hnz : ∀ n ≤ finrank K V, (A ^ n) x ≠ 0) :
    ∃ (t r : ℕ) (hr : 0 < r) (R : Submodule K V)
      (b : Basis (Fin r) K R) (E : R ≃ₗ[K] R),
      t + r ≤ finrank K V ∧
      (∀ j : Fin r, (b j : V) = (A ^ (t + j)) x) ∧
      (∀ z : R, (E z : V) = A z) ∧
      ∀ k : ℕ, ((E ^ k) (b ⟨0, hr⟩) : V) = (A ^ (t + k)) x := by
  classical
  have hex : ∃ m : ℕ, (A ^ m) x ∈
      Submodule.span K (Set.range (fun i : Fin m => (A ^ (i : ℕ)) x)) := by
    by_contra! h
    have hi := krylov_independent A x (finrank K V + 1) (fun j _ => h j)
    have hc := hi.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hc
    omega
  let m := Nat.find hex
  have hdep := Nat.find_spec hex
  have hli : LinearIndependent K (fun i : Fin m => (A ^ (i : ℕ)) x) :=
    krylov_independent A x m (fun j hj => Nat.find_min hex hj)
  have hm : m ≤ finrank K V := by simpa only [Fintype.card_fin] using hli.fintype_card_le_finrank
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hdep
  have hcoeff : ∃ j : Fin m, a j ≠ 0 := by
    by_contra! h
    have hz : (A ^ m) x = 0 := by simpa [h] using ha.symm
    exact hnz m hm hz
  have hfirst : ∃ t : ℕ, ∃ ht : t < m, a ⟨t, ht⟩ ≠ 0 := by
    obtain ⟨i, hi⟩ := hcoeff
    exact ⟨i, i.isLt, hi⟩
  let t := Nat.find hfirst
  obtain ⟨ht, hat⟩ := Nat.find_spec hfirst
  have hbefore (i : Fin m) (hi : (i : ℕ) < t) : a i = 0 := by
    by_contra hai
    exact Nat.find_min hfirst hi ⟨i.isLt, hai⟩
  let r := m - t
  have hr : 0 < r := by dsimp [r]; omega
  let v : Fin r → V := fun j => (A ^ (t + j)) x
  have hv : LinearIndependent K v := by
    apply hli.comp (fun j : Fin r => (⟨t + j, by dsimp [r] at *; omega⟩ : Fin m))
    intro i j heq
    apply Fin.ext
    have := congrArg Fin.val heq
    dsimp at this
    omega
  let R := Submodule.span K (Set.range v)
  let b : Basis (Fin r) K R := Basis.span hv
  have hmem (i : ℕ) (hi : t ≤ i) (him : i < m) : (A ^ i) x ∈ R := by
    have heq : i = t + (i - t) := by omega
    rw [heq]
    exact Submodule.subset_span ⟨⟨i - t, by dsimp [r]; omega⟩, rfl⟩
  have hmR : (A ^ m) x ∈ R := by
    rw [← ha]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : (i : ℕ) < t
    · rw [hbefore i hi, zero_smul]; exact R.zero_mem
    · exact R.smul_mem _ (hmem i (by omega) i.isLt)
  have hAR : ∀ z ∈ R, A z ∈ R := by
    change R ≤ R.comap A
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    change A ((A ^ (t + j)) x) ∈ R
    rw [← Module.End.mul_apply, ← pow_succ']
    by_cases hj : t + j + 1 < m
    · exact hmem _ (by omega) hj
    · have heq : t + j + 1 = m := by have := j.isLt; dsimp [r] at this; omega
      simpa only [heq] using hmR
  have hpre (i : ℕ) (hti : t < i) (him : i ≤ m) : (A ^ i) x ∈ R.map A := by
    refine Submodule.mem_map.mpr ⟨(A ^ (i - 1)) x, hmem _ (by omega) (by omega), ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ']
    congr 2
    omega
  have htR : (A ^ t) x ∈ R.map A := by
    let i : Fin m := ⟨t, ht⟩
    have hrest : (∑ j ∈ Finset.univ.erase i, a j • (A ^ (j : ℕ)) x) ∈ R.map A := by
      apply Submodule.sum_mem
      intro j hj
      by_cases hjt : (j : ℕ) < t
      · rw [hbefore j hjt, zero_smul]; exact (R.map A).zero_mem
      · apply (R.map A).smul_mem
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        exact hpre j (by
          have hne : (j : ℕ) ≠ t := fun e => hji (Fin.ext e)
          omega) j.isLt.le
    have hsum := Finset.sum_erase_add Finset.univ (fun j : Fin m => a j • (A ^ (j : ℕ)) x)
      (Finset.mem_univ i)
    rw [ha] at hsum
    have hc : a i • (A ^ t) x ∈ R.map A := by
      have heq : a i • (A ^ t) x = (A ^ m) x -
          ∑ j ∈ Finset.univ.erase i, a j • (A ^ (j : ℕ)) x := by
        exact eq_sub_of_add_eq' hsum
      rw [heq]
      exact (R.map A).sub_mem (hpre m ht (le_refl _)) hrest
    exact ((R.map A).smul_mem_iff hat).mp hc
  have hsur : R ≤ R.map A := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    by_cases hj : (j : ℕ) = 0
    · simpa [v, hj] using htR
    · exact hpre (t + j) (by omega) (by have := j.isLt; dsimp [r] at this; omega)
  let f : R →ₗ[K] R := A.restrict hAR
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp (hsur y.property)
    exact ⟨⟨z, hz⟩, Subtype.ext heq⟩
  let E : R ≃ₗ[K] R := LinearEquiv.ofBijective f ⟨LinearMap.injective_iff_surjective.mpr hf, hf⟩
  have hb (j : Fin r) : (b j : V) = (A ^ (t + j)) x := Basis.coe_span_apply hv j
  have hE (z : R) : (E z : V) = A z := rfl
  refine ⟨t, r, hr, R, b, E, by dsimp [r]; omega, hb, hE, ?_⟩
  intro k
  induction k with
  | zero => simpa using hb ⟨0, hr⟩
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, hE, ih]
    rw [show t + (k + 1) = (t + k) + 1 by omega, pow_succ', Module.End.mul_apply]

private theorem coefficient_blocks {κ : Type*}
    (R : Submodule K V) (b : Basis ι K R) (E : R ≃ₗ[K] R)
    (T : κ → Module.End K V) (lam : ι → κ → K)
    (hlam : ∀ j u, T u (b j : V) = lam j u • (E (b j) : V)) :
    ∃ S : Set.range lam → Submodule K R,
      iSupIndep S ∧ (∀ i, S i ≠ ⊥) ∧ iSup S = ⊤ ∧
      ∀ z : R, z ≠ 0 →
        ((∃ i, z ∈ S i) ↔ ∃ μ : κ → K, ∀ u, T u (z : V) = μ u • (E z : V)) := by
  classical
  let S : Set.range lam → Submodule K R := fun η =>
    Submodule.span K (b '' {j | lam j = η.val})
  have hind : iSupIndep S := by
    apply iSupIndep_def.mpr
    intro η
    have hd := b.linearIndependent.disjoint_span_image
      (s := {j | lam j = η.val}) (t := {j | lam j ≠ η.val})
      (Set.disjoint_left.mpr (fun _ h h' => h' h))
    apply hd.mono_right
    apply iSup_le
    intro ζ
    apply iSup_le
    intro hζη
    apply Submodule.span_mono
    apply Set.image_mono
    intro j hj
    exact fun h => hζη (Subtype.ext (hj.symm.trans h))
  have hne (η : Set.range lam) : S η ≠ ⊥ := by
    obtain ⟨j, hj⟩ := η.property
    intro hz
    have hm : b j ∈ S η := Submodule.subset_span ⟨j, hj, rfl⟩
    rw [hz] at hm
    exact b.ne_zero j hm
  have htop : iSup S = ⊤ := by
    apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
    intro j
    apply (le_iSup S (⟨lam j, ⟨j, rfl⟩⟩ : Set.range lam))
    exact Submodule.subset_span ⟨j, rfl, rfl⟩
  let F : R →ₗ[K] V := R.subtype.comp E.toLinearMap
  let U (u : κ) : R →ₗ[K] V := (T u).comp R.subtype
  have hgen (j : ι) (u : κ) : U u (b j) = lam j u • F (b j) := hlam j u
  have hblock (η : Set.range lam) (z : R) (hz : z ∈ S η) (u : κ) :
      U u z = η.val u • F z := by
    apply LinearMap.eqOn_span (f := U u) (g := η.val u • F) ?_ hz
    rintro _ ⟨j, hj, rfl⟩
    change U u (b j) = η.val u • F (b j)
    rw [hgen, hj]
  have hFli : LinearIndependent K (fun j => F (b j)) :=
    b.linearIndependent.map' F (LinearMap.ker_eq_bot.mpr
      (R.subtype_injective.comp E.injective))
  refine ⟨S, hind, hne, htop, ?_⟩
  intro z hz
  constructor
  · rintro ⟨η, hη⟩
    exact ⟨η.val, hblock η z hη⟩
  · rintro ⟨μ, hμ⟩
    have heq (u : κ) :
        (∑ j, (b.repr z j * lam j u) • F (b j)) =
          ∑ j, (b.repr z j * μ u) • F (b j) := by
      calc
        _ = U u (∑ j, b.repr z j • b j) := by
          simp only [map_sum, map_smul, hgen, smul_smul]
        _ = μ u • F (∑ j, b.repr z j • b j) := by
          rw [b.sum_repr]
          exact hμ u
        _ = _ := by simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]
    have hcoords (j : ι) (hj : b.repr z j ≠ 0) : lam j = μ := by
      funext u
      exact mul_left_cancel₀ hj (Fintype.linearIndependent_iffₛ.mp hFli _ _ (heq u) j)
    obtain ⟨j, hj⟩ : ∃ j, b.repr z j ≠ 0 := by
      by_contra! h
      apply hz
      apply b.repr.injective
      ext j
      simpa using h j
    let η : Set.range lam := ⟨lam j, ⟨j, rfl⟩⟩
    refine ⟨η, b.mem_span_image.mpr ?_⟩
    intro i hi
    exact (hcoords i (Finsupp.mem_support_iff.mp hi)).trans (hcoords j hj).symm

private theorem collinear_orbit_extension {κ : Type*}
    (A : Module.End K V) (T : κ → Module.End K V) (x : V)
    (hnz : ∀ n ≤ 2 * finrank K V - 1, (A ^ n) x ≠ 0)
    (hcol : ∀ n < 2 * finrank K V - 1, ∃ μ : κ → K,
      ∀ u, T u ((A ^ n) x) = μ u • ((A ^ (n + 1)) x)) :
    ∀ n : ℕ, (A ^ n) x ≠ 0 ∧
      ∃ μ : κ → K, ∀ u, T u ((A ^ n) x) = μ u • ((A ^ (n + 1)) x) := by
  classical
  have hx : x ≠ 0 := by simpa using hnz 0 (Nat.zero_le _)
  have hd : 0 < finrank K V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx⟩
  have hdN : finrank K V ≤ 2 * finrank K V - 1 := by omega
  obtain ⟨t, r, hr, R, b, E, htr, hb, hE, hpow⟩ :=
    krylov_invertible_tail A x (fun n hn => hnz n (hn.trans hdN))
  have hbcol (j : Fin r) : ∃ μ : κ → K, ∀ u, T u (b j : V) = μ u • (E (b j) : V) := by
    obtain ⟨μ, hμ⟩ := hcol (t + j) (by have := j.isLt; omega)
    refine ⟨μ, ?_⟩
    intro u
    rw [hE, hb]
    simpa only [pow_succ', Module.End.mul_apply] using hμ u
  choose lam hlam using hbcol
  obtain ⟨S, hS, hSne, hStop, hiff⟩ := coefficient_blocks R b E T lam hlam
  letI : Fintype (Set.range lam) := Fintype.ofFinite _
  let z := b ⟨0, hr⟩
  have hz : z ≠ 0 := b.ne_zero _
  have hzpow (k : ℕ) : (E ^ k) z ≠ 0 := (E ^ k).map_ne_zero_iff.mpr hz
  have hnonzero (k : ℕ) : (A ^ (t + k)) x ≠ 0 := by
    rw [← hpow]
    exact fun h => hzpow k (Subtype.ext h)
  have hprefix : ∀ j < 2 * finrank K R - 1, ∃ i, (E ^ j) z ∈ S i := by
    intro j hj
    rw [finrank_eq_card_basis b, Fintype.card_fin] at hj
    apply (hiff _ (hzpow j)).mpr
    obtain ⟨μ, hμ⟩ := hcol (t + j) (by omega)
    refine ⟨μ, ?_⟩
    intro u
    rw [hE]
    change T u ((E ^ j) (b ⟨0, hr⟩) : V) = μ u • A ((E ^ j) (b ⟨0, hr⟩) : V)
    rw [hpow]
    simpa only [pow_succ', Module.End.mul_apply] using hμ u
  have hforever : ∀ k : ℕ, ∃ i, (E ^ k) z ∈ S i := by
    by_cases hc : 2 ≤ Fintype.card (Set.range lam)
    · exact (pure_prefix_potential_stabilizes E S hS hSne hc z hz hprefix).2
    · let η : Set.range lam := ⟨lam ⟨0, hr⟩, ⟨⟨0, hr⟩, rfl⟩⟩
      haveI : Subsingleton (Set.range lam) := ⟨Fintype.card_le_one_iff.mp (by omega)⟩
      letI : Unique (Set.range lam) := ⟨⟨η⟩, fun i => Subsingleton.elim i η⟩
      have ht : S η = ⊤ := by
        simpa only [iSup_unique, show (default : Set.range lam) = η from rfl] using hStop
      intro k
      exact ⟨η, ht.symm ▸ Submodule.mem_top⟩
  have htail (k : ℕ) : ∃ μ : κ → K,
      ∀ u, T u ((A ^ (t + k)) x) = μ u • ((A ^ (t + k + 1)) x) := by
    obtain ⟨μ, hμ⟩ := (hiff _ (hzpow k)).mp (hforever k)
    refine ⟨μ, ?_⟩
    intro u
    have h := hμ u
    rw [hE] at h
    change T u ((E ^ k) (b ⟨0, hr⟩) : V) = μ u • A ((E ^ k) (b ⟨0, hr⟩) : V) at h
    simpa only [hpow, ← Module.End.mul_apply, ← pow_succ'] using h
  intro n
  by_cases hn : n < t
  · exact ⟨hnz n (by omega), hcol n (by omega)⟩
  · have heq : n = t + (n - t) := by omega
    rw [heq]
    exact ⟨hnonzero _, htail _⟩

/-- For the channel supplied by any complete finite Kraus family, purity at
times zero through 2d-1 forces purity at every time. -/
theorem finite_pure_prefix_extension {d : ℕ} {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∑ u, (K u).conjTranspose * K u = 1) (ρ : DensityState (Fin d))
    (hpure : ∀ n < 2 * d, IsPure (((finite_kraus_quantum_channel K hK).choose.mapState)^[n] ρ)) :
    ∀ n : ℕ, IsPure (((finite_kraus_quantum_channel K hK).choose.mapState)^[n] ρ) := by
  let channel := (finite_kraus_quantum_channel K hK).choose
  have hchannel := (finite_kraus_quantum_channel K hK).choose_spec
  have hd : 0 < d := by
    by_contra h
    have hd : d = 0 := by omega
    subst d
    have h := ρ.2.2
    simp [Matrix.trace] at h
  obtain ⟨A, x, ⟨hx, hinit⟩, hnz, hcol⟩ :=
    linear_lift_of_pure_prefix (N := 2 * d - 1) channel K hchannel
      (fun n => (channel.mapState)^[n] ρ)
      (fun n _ => Function.iterate_succ_apply' ..)
      (fun n hn => hpure n (by omega))
  let T (u : κ) := (K u).mulVecLin
  have hall : ∀ n : ℕ, (A ^ n) x ≠ 0 ∧
      ∃ μ : κ → ℂ, ∀ u, T u ((A ^ n) x) = μ u • ((A ^ (n + 1)) x) := by
    apply collinear_orbit_extension A T x
    · simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hnz
    · simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one,
        T, Matrix.mulVecLin_apply] using hcol
  have hactual (n : ℕ) : (channel.mapState)^[n] ρ = directionState ((A ^ n) x) (hall n).1 := by
    induction n with
    | zero => simpa using hinit.symm
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      obtain ⟨μ, hμ⟩ := (hall n).2
      exact map_directionState_of_collinear channel K hchannel _ _ (hall n).1 (hall (n + 1)).1 μ hμ
  intro n
  rw [hactual]
  exact ⟨_, rfl⟩

end D5.S3.Quantum.Dynamics.FinitePureOrbitExtension
