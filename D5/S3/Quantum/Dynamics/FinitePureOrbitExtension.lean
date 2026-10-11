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
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.FinitePureOrbitExtension

open Module Finset
open scoped BigOperators
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel

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

/- A finite Kraus family whose action on one input direction is collinear with a
   unit output direction sends the corresponding pure state to a pure state. -/
theorem pure_output_of_kraus_collinear
    {d : ℕ} (channel : QuantumChannel (Fin d) (Fin d))
    (K : (Fin d × Fin d) → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ M : Matrix (Fin d) (Fin d) ℂ,
      CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)) =
        ∑ r, K r * M * (K r).conjTranspose)
    (ψ φ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (hφ : star φ ⬝ᵥ φ = 1)
    (c : Fin d × Fin d → ℂ)
    (hcol : ∀ r, Matrix.mulVec (K r) ψ = c r • φ)
    (hweight : ∑ r, star (c r) * c r = 1) :
    IsPure (channel.mapState (pureState ψ hψ)) := by
  refine ⟨φ, ?_⟩
  have houter (r : Fin d × Fin d) :
      K r * Matrix.vecMulVec ψ (star ψ) * (K r).conjTranspose =
        Matrix.vecMulVec (Matrix.mulVec (K r) ψ)
          (star (Matrix.mulVec (K r) ψ)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  have hsum :
      (∑ r, K r * Matrix.vecMulVec ψ (star ψ) * (K r).conjTranspose) =
        Matrix.vecMulVec φ (star φ) := by
    simp_rw [houter, hcol]
    ext i j
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, Pi.star_apply, star_mul, starRingEnd_apply]
    calc
      (∑ x, c x * φ i * (star (φ j) * star (c x))) =
          ∑ x, (star (c x) * c x) * (φ i * star (φ j)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = (∑ x, star (c x) * c x) * (φ i * star (φ j)) := by
            rw [Finset.sum_mul]
      _ = φ i * star (φ j) := by rw [hweight, one_mul]
  rw [QuantumChannel.mapState_value]
  change channel.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.vecMulVec ψ (star ψ))) = _
  have hmap := hK (Matrix.vecMulVec ψ (star ψ))
  have hmap' := congrArg CStarMatrix.ofMatrix hmap
  have hmap'' : channel.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.vecMulVec ψ (star ψ))) =
      CStarMatrix.ofMatrix
        (∑ r, K r * Matrix.vecMulVec ψ (star ψ) * (K r).conjTranspose) := by
    change channel.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.vecMulVec ψ (star ψ))) = _ at hmap'
    exact hmap'
  rw [hmap'', hsum]

/- The word-space descent now supplies the finite-prefix part of the channel
   argument.  The remaining channel-specific input is exactly the Kraus
   collinearity contract on each member of the supplied pure-direction family. -/
theorem pure_prefix_channel_directions
    {d : ℕ} {ι : Type*} [Fintype ι]
    (channel : QuantumChannel (Fin d) (Fin d))
    (A : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ))
    (S : ι → Submodule ℂ (Fin d → ℂ))
    (hS : iSupIndep S) (hne : ∀ i, S i ≠ ⊥)
    (hcard : 2 ≤ Fintype.card ι)
    (ψ : Fin d → ℂ) (hψ : ψ ≠ 0)
    (hnorm : ∀ k : ℕ, star ((A ^ k) ψ) ⬝ᵥ ((A ^ k) ψ) = 1)
    (hprefix : ∀ j < 2 * finrank ℂ (Fin d → ℂ) - 1,
      ∃ i, (A ^ j) ψ ∈ S i)
    (hcol : ∀ (i : ι) (v : Fin d → ℂ), v ∈ S i → v ≠ 0 →
      ∃ (φ : Fin d → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
        (c : Fin d × Fin d → ℂ),
        (∀ r, Matrix.mulVec
            ((krausRepresentation
              channel.toCompletelyPositiveMap).1 r) v = c r • φ) ∧
          ∑ r, star (c r) * c r = 1) :
    ∀ k : ℕ, ∃ i, (A ^ k) ψ ∈ S i ∧
      IsPure (channel.mapState (pureState ((A ^ k) ψ) (hnorm k))) := by
  let K := (krausRepresentation
    channel.toCompletelyPositiveMap).1
  have hK : ∀ M : Matrix (Fin d) (Fin d) ℂ,
      CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)) =
        ∑ r, K r * M * (K r).conjTranspose :=
    (krausRepresentation
      channel.toCompletelyPositiveMap).2
  have hpotential := pure_prefix_potential_stabilizes
    (K := ℂ) (V := Fin d → ℂ) A S hS hne hcard ψ hψ hprefix
  intro k
  obtain ⟨i, hi⟩ := hpotential.2 k
  have hne_k : (A ^ k) ψ ≠ 0 := (A ^ k).map_ne_zero_iff.mpr hψ
  obtain ⟨φ, hφ, c, hcol', hweight⟩ := hcol i ((A ^ k) ψ) hi hne_k
  refine ⟨i, hi, ?_⟩
  exact pure_output_of_kraus_collinear channel K hK ((A ^ k) ψ) φ
    (hnorm k) hφ c hcol' hweight

#print axioms pure_prefix_potential_stabilizes
#print axioms pure_output_of_kraus_collinear
#print axioms pure_prefix_channel_directions

end D5.S3.Quantum.Dynamics.FinitePureOrbitExtension
