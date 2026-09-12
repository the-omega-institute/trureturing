/- GID: D5/S3/Quantum/StationaryPreparation/PhysicalResiduals
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PhysicalResiduals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact fixed-isometry stationary preparation yields residuals,
     Gram formulas, and rank bounds. -/

import D5.S1.Ledger.BoundedTimeSlice
import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
import D5.S3.Quantum.Algebra.StationaryGramRank
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] [Nonempty σ]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

abbrev Box (a : σ → ℕ) := D5.S1.Ledger.BoundedTimeSlice.TailBox a

def values {a : σ → ℕ} (r : Box a) : σ → ℕ := fun i => (r i).val

def mass (b : σ → ℕ) : ℕ := ∑ i, b i

def M (b : σ → ℕ) : ℕ := (mass b).factorial / ∏ i, (b i).factorial

def counts (w : List σ) : σ → ℕ := fun i => w.count i

def profile (b : σ → ℕ) : Multiset σ := ∑ i, Multiset.replicate (b i) i

def top (a : σ → ℕ) : Box a := fun i => ⟨a i, Nat.lt_succ_self _⟩

def sub {a : σ → ℕ} (r : Box a) (b : σ → ℕ) : Box a :=
  fun i => ⟨(r i).val - b i, lt_of_le_of_lt (Nat.sub_le _ _) (r i).isLt⟩

def lower {a : σ → ℕ} (r : Box a) (i : σ) : Box a :=
  sub r (fun j => if j = i then 1 else 0)

def realSqrt (x : ℝ) : ℂ := (Real.sqrt x : ℂ)

noncomputable def tensorCoordinates :
    (EuclideanSpace ℂ σ ⊗[ℂ] H) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : σ => H) :=
  (((EuclideanSpace.basisFun σ ℂ).tensorProduct (stdOrthonormalBasis ℂ H)).repr).trans
    ((D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.curry
      σ (Fin (Module.finrank ℂ H))).trans
      (LinearIsometryEquiv.piLpCongrRight 2
        (fun _ : σ => (stdOrthonormalBasis ℂ H).repr.symm)))

def letter (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (i : σ) (x : H) : H :=
  tensorCoordinates (V x) i

def wordOp (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) : List σ → H → H
  | [], x => x
  | i :: w, x => wordOp V w (letter V i x)

def sector (a : σ → ℕ) : EuclideanSpace ℂ (Fin (mass a) → σ) :=
  WithLp.toLp 2 (fun w =>
    if counts (List.ofFn w) = a then (realSqrt (M a : ℝ))⁻¹ else 0)

def emitted (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (n : ℕ) (x : H) :
    EuclideanSpace ℂ (Fin n → σ) ⊗[ℂ] H :=
  ∑ w : Fin n → σ, (EuclideanSpace.basisFun (Fin n → σ) ℂ) w
    ⊗ₜ[ℂ] wordOp V (List.ofFn w) x

def prefixRepresentative (a : σ → ℕ) (r : Box a) : List σ :=
  let t := profile (fun i => a i - (r i).val)
  List.ofFn (D5.S3.Quantum.Entanglement.OccupancyWordSectors.representative
    t (n := t.card) rfl)

def residual (a : σ → ℕ)
    (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (ψ : H) (r : Box a) : H :=
  realSqrt ((M a : ℝ) / (M (values r) : ℝ)) •
    wordOp V (prefixRepresentative a r) ψ

def Step (a : σ → ℕ)
    (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (φ : Box a → H) : Prop :=
  ∀ r : Box a, r ≠ 0 → ∀ i : σ,
    letter V i (φ r) =
      if 0 < (r i).val then
        realSqrt (((r i).val : ℝ) / (mass (values r) : ℝ)) • φ (lower r i)
      else 0

structure PhysicalPreparation (a : σ → ℕ) where
  V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)
  initial : H
  final : H
  initial_unit : ‖initial‖ = 1
  final_unit : ‖final‖ = 1
  output : emitted V (mass a) initial = sector a ⊗ₜ[ℂ] final

structure NormalizedResiduals (a : σ → ℕ)
    (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
    (ψ f : H) (φ : Box a → H) : Prop where
  unit : ∀ r : Box a, ‖φ r‖ = 1
  zero : φ 0 = f
  initial : φ (top a) = ψ
  actual_prefix : ∀ (r : Box a) (w : List σ),
    (∀ i, w.count i = a i - (r i).val) →
    wordOp V w ψ =
      realSqrt ((M (values r) : ℝ) / (M a : ℝ)) • φ r
  step : Step a V φ

theorem actual_residuals_of_preparation
    (a : σ → ℕ) (P : PhysicalPreparation (H := H) a) :
    NormalizedResiduals a P.V P.initial P.final (residual a P.V P.initial) := by
  classical
  have tensor_component_equation {ι : Type u} [Fintype ι] [DecidableEq ι] (i j : ι) (x : H) :
      tensorCoordinates ((EuclideanSpace.basisFun ι ℂ) i ⊗ₜ[ℂ] x) j =
        if j = i then x else 0 := by
    unfold tensorCoordinates
    rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.piLpCongrRight_apply]
    apply (stdOrthonormalBasis ℂ H).repr.injective
    ext q
    simp only [LinearIsometryEquiv.apply_symm_apply]
    change (((curry ι (Fin (Module.finrank ℂ H)))
          (((EuclideanSpace.basisFun ι ℂ).tensorProduct (stdOrthonormalBasis ℂ H)).repr
            ((EuclideanSpace.basisFun ι ℂ) i ⊗ₜ[ℂ] x))).ofLp j) q =
      ((stdOrthonormalBasis ℂ H).repr (if j = i then x else 0)).ofLp q
    unfold curry
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
      LinearIsometryEquiv.piLpCurry_apply, Equiv.piCongrLeft'_apply, Sigma.curry,
      Equiv.symm_symm, Equiv.sigmaEquivProd_apply]
    change (((EuclideanSpace.basisFun ι ℂ).tensorProduct (stdOrthonormalBasis ℂ H)).repr
        ((EuclideanSpace.basisFun ι ℂ) i ⊗ₜ[ℂ] x)).ofLp (j, q) = _
    rw [OrthonormalBasis.tensorProduct_repr_tmul_apply]
    by_cases h : j = i <;> simp [h]
  have tensor_tmul_component {ι : Type u} [Fintype ι] [DecidableEq ι] (u : EuclideanSpace ℂ ι) (x : H) (j : ι) :
      (tensorCoordinates (u ⊗ₜ[ℂ] x)).ofLp j = u j • x := by
    rw [← (EuclideanSpace.basisFun ι ℂ).sum_repr u]
    simp only [map_sum, TensorProduct.sum_tmul, WithLp.ofLp_sum, Finset.sum_apply]
    simp_rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    simp only [map_smul, PiLp.smul_apply]
    simp_rw [tensor_component_equation]
    simp [EuclideanSpace.basisFun_apply]
  have emitted_component (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
      (n : ℕ) (x : H) (w : Fin n → σ) :
      (tensorCoordinates (emitted V n x)).ofLp w = wordOp V (List.ofFn w) x := by
    simp only [emitted, map_sum]
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single w]
    · rw [tensor_component_equation]
      simp
    · intro b hb hne
      have hwb : ¬ w = b := fun h => hne h.symm
      rw [tensor_component_equation]
      simp [hwb]
    · intro hw
      simp at hw
  have emitted_word_output (a : σ → ℕ) (P : PhysicalPreparation (H := H) a) (w : Fin (mass a) → σ) :
      wordOp P.V (List.ofFn w) P.initial =
        if counts (List.ofFn w) = a then (realSqrt (M a : ℝ))⁻¹ • P.final else 0 := by
    have h := congrArg (fun y => (tensorCoordinates y).ofLp w) P.output
    rw [emitted_component] at h
    rw [tensor_tmul_component] at h
    simpa [sector] using h
  have emitted_list_output (a : σ → ℕ) (P : PhysicalPreparation (H := H) a)
      (l : List σ) (hl : l.length = mass a) :
      wordOp P.V l P.initial =
        if counts l = a then (realSqrt (M a : ℝ))⁻¹ • P.final else 0 := by
    let w : Fin (mass a) → σ := fun i => l.get ⟨i, by omega⟩
    have hw : List.ofFn w = l := by
      rw [List.ofFn_congr hl.symm]
      simp [w, List.ofFn_getElem]
    have h := emitted_word_output a P w
    rw [hw] at h
    exact h
  have profile_count (b : σ → ℕ) (i : σ) : (profile b).count i = b i := by
    simp [profile, Multiset.count_sum', Multiset.count_replicate]
  have prefix_counts (a : σ → ℕ) (r : Box a) (i : σ) :
    counts (prefixRepresentative a r) i = a i - (r i).val := by
    let b : σ → ℕ := fun j => a j - (r j).val
    let t : Multiset σ := profile b
    change List.count i (List.ofFn (representative t rfl)) = b i
    have h := occupation_representative t rfl
    have hc := congrArg (Multiset.count i) h
    have hleft : List.count i (List.ofFn (representative t rfl)) =
        (occupation (representative t rfl)).count i := by simp [occupation]
    calc
      List.count i (List.ofFn (representative t rfl)) =
          (occupation (representative t rfl)).count i := hleft
      _ = t.count i := congrArg (Multiset.count i) h
      _ = b i := by change (profile b).count i = b i; exact profile_count b i
  have list_len_mass_counts (l : List σ) : l.length = mass (counts l) := by
    simpa [mass, counts] using
      (Multiset.sum_count_eq_card (m := (l : Multiset σ))
        (fun _ _ => Finset.mem_univ _)).symm
  have box_le (a : σ → ℕ) (r : Box a) (i : σ) : (r i).val ≤ a i := Nat.le_of_lt_succ (r i).isLt
  have mass_split (a : σ → ℕ) (r : Box a) :
      mass (fun i => a i - (r i).val) + mass (values r) = mass a := by
    rw [show mass (fun i => a i - (r i).val) = ∑ i, (a i - (r i).val) by rfl,
      show mass (values r) = ∑ i, (r i).val by rfl, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.sub_add_cancel (box_le a r i)
  have wordOp_append (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
      (u v : List σ) (x : H) :
      wordOp V (u ++ v) x = wordOp V v (wordOp V u x) := by
    induction u generalizing x with
    | nil => rfl
    | cons i u ih => simpa [wordOp] using ih (letter V i x)
  have continuation_inner (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
      (n : ℕ) (x y : H) :
      inner ℂ x y = ∑ w : Fin n → σ,
        inner ℂ (wordOp V (List.ofFn w) x) (wordOp V (List.ofFn w) y) := by
    induction n generalizing x y with
    | zero => simp [wordOp]
    | succ n ih =>
      have hls : inner ℂ x y = ∑ i, inner ℂ (letter V i x) (letter V i y) := by
        rw [← V.inner_map_map x y, ← tensorCoordinates.inner_map_map]
        simp only [PiLp.inner_apply]
        rfl
      calc
        inner ℂ x y = ∑ i, inner ℂ (letter V i x) (letter V i y) := hls
        _ = ∑ i, ∑ w : Fin n → σ,
            inner ℂ (wordOp V (List.ofFn w) (letter V i x))
              (wordOp V (List.ofFn w) (letter V i y)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact ih _ _
        _ = ∑ w : Fin (n+1) → σ,
            inner ℂ (wordOp V (List.ofFn w) x) (wordOp V (List.ofFn w) y) := by
          let F : σ × (Fin n → σ) → ℂ := fun p =>
            inner ℂ (wordOp V (List.ofFn p.2) (letter V p.1 x))
              (wordOp V (List.ofFn p.2) (letter V p.1 y))
          have hprod : (∑ p : σ × (Fin n → σ), F p) =
              ∑ i : σ, ∑ w : Fin n → σ, F (i, w) := by
            simpa only [Finset.univ_product_univ] using
              (Finset.sum_product (Finset.univ : Finset σ)
                (Finset.univ : Finset (Fin n → σ)) F)
          rw [← hprod]
          rw [← (Fin.consEquiv (fun _ : Fin (n+1) => σ)).sum_comp]
          apply Finset.sum_congr rfl
          intro p hp
          rcases p with ⟨i, w⟩
          change inner ℂ (wordOp V (List.ofFn w) (letter V i x))
              (wordOp V (List.ofFn w) (letter V i y)) =
            inner ℂ (wordOp V (List.ofFn (Fin.cons i w)) x)
              (wordOp V (List.ofFn (Fin.cons i w)) y)
          rw [show List.ofFn (Fin.cons i w) = i :: List.ofFn w by simp]
          simp only [wordOp]
  have letter_add (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (i : σ) (x y : H) :
      letter V i (x+y) = letter V i x + letter V i y := by simp [letter, map_add]
  have letter_neg (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (i : σ) (x : H) :
      letter V i (-x) = - letter V i x := by simp [letter, map_neg]
  have wordOp_add (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (w : List σ) (x y : H) :
      wordOp V w (x+y) = wordOp V w x + wordOp V w y := by
    induction w generalizing x y with
    | nil => simp [wordOp]
    | cons i w ih => simp only [wordOp, letter_add, ih]
  have wordOp_neg (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (w : List σ) (x : H) :
      wordOp V w (-x) = - wordOp V w x := by
    induction w generalizing x with
    | nil => simp [wordOp]
    | cons i w ih => simp only [wordOp, letter_neg, ih]
  have wordOp_sub (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (w : List σ) (x y : H) :
      wordOp V w (x-y) = wordOp V w x - wordOp V w y := by
    simpa only [sub_eq_add_neg, wordOp_add, wordOp_neg, sub_eq_add_neg]
      using wordOp_add V w x (-y)
  have continuation_injective (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
      (n : ℕ) (x y : H)
      (h : ∀ w : Fin n → σ, wordOp V (List.ofFn w) x = wordOp V (List.ofFn w) y) : x = y := by
    have hz : x - y = 0 := inner_self_eq_zero.mp (by
      rw [continuation_inner V n (x-y) (x-y)]
      apply Finset.sum_eq_zero
      intro w hw
      rw [wordOp_sub, h]
      simp)
    exact sub_eq_zero.mp hz
  have prefix_length (a : σ → ℕ) (r : Box a) :
      (prefixRepresentative a r).length = mass (fun i => a i - (r i).val) := by
    rw [list_len_mass_counts]
    apply congrArg mass
    funext i
    exact prefix_counts a r i
  have append_counts_eq (a : σ → ℕ) (r : Box a) (u : List σ)
      (hu : ∀ i, u.count i = a i - (r i).val)
      (v : Fin (mass (values r)) → σ)
      (hv : counts (List.ofFn v) = values r) :
      counts (u ++ List.ofFn v) = a := by
    funext i
    rw [counts, List.count_append, hu i]
    have hv_i := congrArg (fun q => q i) hv
    change List.count i (List.ofFn v) = (r i).val at hv_i
    rw [hv_i]
    exact Nat.sub_add_cancel (box_le a r i)
  have append_counts_eq_rep (a : σ → ℕ) (r : Box a)
      (v : Fin (mass (values r)) → σ) (hv : counts (List.ofFn v) = values r) :
      counts (prefixRepresentative a r ++ List.ofFn v) = a := by
    apply append_counts_eq a r (prefixRepresentative a r) (prefix_counts a r) v hv
  have prefix_coincidence (a : σ → ℕ) (P : PhysicalPreparation (H := H) a)
      (r : Box a) (u : List σ)
      (hu : ∀ i, u.count i = a i - (r i).val) :
      wordOp P.V u P.initial = wordOp P.V (prefixRepresentative a r) P.initial := by
    have hul : u.length = mass (fun i => a i - (r i).val) := by
      rw [list_len_mass_counts]
      apply congrArg mass
      funext i
      exact hu i
    have hrl := prefix_length a r
    have hlen : u.length = (prefixRepresentative a r).length := hul.trans hrl.symm
    have hs (v : Fin (mass (values r)) → σ) :
        wordOp P.V (List.ofFn v) (wordOp P.V u P.initial) =
          wordOp P.V (List.ofFn v) (wordOp P.V (prefixRepresentative a r) P.initial) := by
      rw [← wordOp_append, ← wordOp_append]
      have hlen1 : (u ++ List.ofFn v).length = mass a := by
        rw [List.length_append, hul, List.length_ofFn, mass_split]
      have hlen2 : (prefixRepresentative a r ++ List.ofFn v).length = mass a := by
        rw [List.length_append, hrl, List.length_ofFn, mass_split]
      rw [emitted_list_output a P _ hlen1, emitted_list_output a P _ hlen2]
      by_cases hv' : counts (List.ofFn v) = values r
      · rw [if_pos (append_counts_eq a r u hu v hv')]
        rw [if_pos (append_counts_eq_rep a r v hv')]
      · have hn1 : ¬ counts (u ++ List.ofFn v) = a := by
          intro h
          apply hv'
          funext i
          change List.count i (List.ofFn v) = (r i).val
          have hi := congrArg (fun q => q i) h
          change List.count i (u ++ List.ofFn v) = a i at hi
          rw [List.count_append, hu i] at hi
          omega
        have hn2 : ¬ counts (prefixRepresentative a r ++ List.ofFn v) = a := by
          intro h
          apply hv'
          funext i
          change List.count i (List.ofFn v) = (r i).val
          have hi := congrArg (fun q => q i) h
          have hpi := prefix_counts a r i
          change List.count i (prefixRepresentative a r ++ List.ofFn v) = a i at hi
          change List.count i (prefixRepresentative a r) = a i - (r i).val at hpi
          rw [List.count_append, hpi] at hi
          omega
        rw [if_neg hn1, if_neg hn2]
    apply continuation_injective P.V (mass (values r)) _ _ hs
  have prefix_norm_sq (a : σ → ℕ) (P : PhysicalPreparation (H := H) a)
      (r : Box a) :
      ‖wordOp P.V (prefixRepresentative a r) P.initial‖ ^ 2 =
        (M (values r) : ℝ) / (M a : ℝ) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rw [continuation_inner P.V (mass (values r))]
    have hterm (v : Fin (mass (values r)) → σ) :
        inner ℂ
            (wordOp P.V (List.ofFn v)
              (wordOp P.V (prefixRepresentative a r) P.initial))
            (wordOp P.V (List.ofFn v)
              (wordOp P.V (prefixRepresentative a r) P.initial)) =
          if counts (List.ofFn v) = values r then
            (realSqrt (M a : ℝ))⁻¹ * (realSqrt (M a : ℝ))⁻¹ else 0 := by
      have hlen : (prefixRepresentative a r ++ List.ofFn v).length = mass a := by
        rw [List.length_append, prefix_length a r, List.length_ofFn, mass_split]
      rw [← wordOp_append, emitted_list_output a P _ hlen]
      by_cases hv : counts (List.ofFn v) = values r
      · have hcond := append_counts_eq_rep a r v hv
        simp only [if_pos hcond, if_pos hv]
        rw [inner_smul_left, inner_smul_right]
        have hs : star (realSqrt (M a : ℝ)) = realSqrt (M a : ℝ) := by
          simp [realSqrt]
        simp only [map_inv₀, hs]
        simp [P.final_unit, inner_self_eq_norm_sq_to_K]
        exact Or.inl hs
      · have hn : ¬ counts (prefixRepresentative a r ++ List.ofFn v) = a := by
          intro h
          apply hv
          funext i
          change List.count i (List.ofFn v) = (r i).val
          have hi := congrArg (fun q => q i) h
          have hp := prefix_counts a r i
          change List.count i (prefixRepresentative a r ++ List.ofFn v) = a i at hi
          change List.count i (prefixRepresentative a r) = a i - (r i).val at hp
          rw [List.count_append, hp] at hi
          omega
        simp only [if_neg hn, if_neg hv]
        simp
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    have hcard : (Finset.univ.filter (fun v : Fin (mass (values r)) → σ =>
        counts (List.ofFn v) = values r)).card = M (values r) := by
      let b : σ → ℕ := values r
      let t : Multiset σ := profile b
      have ht : t.card = mass b := by simp [t, profile, mass]
      have hmult := D5.S3.Quantum.Entanglement.OccupancyWordSectors.sector_words_card_multinomial t ht
      have hfilter : Finset.univ.filter (fun v : Fin (mass b) → σ =>
          counts (List.ofFn v) = b) =
          D5.S3.Quantum.Entanglement.OccupancyWordSectors.sectorWords (mass b) t := by
        ext v
        constructor
        · intro hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          simp only [D5.S3.Quantum.Entanglement.OccupancyWordSectors.sectorWords,
            Finset.mem_filter, Finset.mem_univ, true_and]
          apply Multiset.ext.mpr
          intro i
          have hvi := congrArg (fun q => q i) hv
          change List.count i (List.ofFn v) = b i at hvi
          simpa [D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation,
            t, profile_count] using hvi
        · intro hv
          have hv' : occupation v = t := by
            simpa [D5.S3.Quantum.Entanglement.OccupancyWordSectors.sectorWords] using hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          apply funext
          intro i
          have hi := congrArg (Multiset.count i) hv'
          change List.count i (List.ofFn v) = b i
          simpa [D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation,
            t, profile_count] using hi
      rw [hfilter, hmult]
      rw [Nat.multinomial]
      dsimp [t]
      simp_rw [profile_count]
      rfl
    rw [show (∑ v ∈ (Finset.univ.filter (fun v : Fin (mass (values r)) → σ => counts (List.ofFn v) = values r)),
        (realSqrt (M a : ℝ))⁻¹ * (realSqrt (M a : ℝ))⁻¹) =
        (M (values r) : ℕ) • ((realSqrt (M a : ℝ))⁻¹ * (realSqrt (M a : ℝ))⁻¹) by simp [hcard]]
    have hM_eq : M a = D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity
        (mass a) (profile a) := by
      rw [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity_eq_factorial
        (profile a) (by simp [profile, mass])]
      simp only [profile_count]
      rfl
    have hM : 0 < M a := by
      rw [hM_eq]
      exact D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity_pos
        (profile a) (by simp [profile, mass])
    have hma : (realSqrt (M a : ℝ)) ≠ 0 := by
      dsimp [realSqrt]
      exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hM)).ne'
    have hsq : (realSqrt (M a : ℝ)) * (realSqrt (M a : ℝ)) = (M a : ℂ) := by
      dsimp [realSqrt]
      norm_cast
      exact Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hfinal : (realSqrt (M a : ℝ))⁻¹ * (realSqrt (M a : ℝ))⁻¹ =
        ((M a : ℝ) : ℂ)⁻¹ := by
      rw [← mul_inv]
      rw [hsq]
      norm_cast
      norm_num
    rw [hfinal]
    norm_num [map_div₀]
    norm_cast
  have M_eq_multiplicity (b : σ → ℕ) :
      M b = D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity
        (mass b) (profile b) := by
    rw [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity_eq_factorial
        (profile b) (by simp [profile, mass])]
    simp only [profile_count]
    rfl
  have profile_lower_erase (b : σ → ℕ) (i : σ) (hi : 0 < b i) :
      profile (Function.update b i (b i - 1)) = (profile b).erase i := by
    apply Multiset.ext.mpr
    intro j
    rw [profile_count]
    by_cases hji : j = i
    · subst j
      rw [Multiset.count_erase_self]
      rw [profile_count]
      simp [Function.update]
    · rw [Multiset.count_erase_of_ne]
      · simpa [Function.update, hji] using (profile_count b j).symm
      · exact hji
  have mass_lower {a : σ → ℕ} (r : Box a) (i : σ) (hi : 0 < (r i).val) :
      mass (values (lower r i)) = mass (values r) - 1 := by
    have hb : values (lower r i) = Function.update (values r) i ((values r) i - 1) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [values, lower, sub, Function.update]
      · simp [values, lower, sub, Function.update, hji]
    have hprof := profile_lower_erase (values r) i hi
    rw [← hb] at hprof
    have hmem : i ∈ profile (values r) := by
      rw [← Multiset.count_pos, profile_count]
      exact hi
    have hcL : (profile (values (lower r i))).card =
        mass (values (lower r i)) := by simp [profile, mass]
    have hcR : (profile (values r)).card = mass (values r) := by simp [profile, mass]
    calc
      mass (values (lower r i)) = (profile (values (lower r i))).card := hcL.symm
      _ = ((profile (values r)).erase i).card := by rw [hprof]
      _ = (profile (values r)).card - 1 := Multiset.card_erase_of_mem hmem
      _ = mass (values r) - 1 := by rw [hcR]
  have M_lower_recurrence {a : σ → ℕ} (r : Box a) (i : σ) (hi : 0 < (r i).val) :
      mass (values r) * M (values (lower r i)) = (r i).val * M (values r) := by
    have hb : values (lower r i) = Function.update (values r) i ((r i).val - 1) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [values, lower, sub, Function.update]
      · simp [values, lower, sub, Function.update, hj]
    have hp : profile (values (lower r i)) = (profile (values r)).erase i := by
      rw [hb]
      exact profile_lower_erase (values r) i hi
    have hle : (r i).val ≤ mass (values r) := by
      change values r i ≤ ∑ j, values r j
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hm : 0 < mass (values r) := hi.trans_le hle
    have hmem : i ∈ profile (values r) := by
      rw [← Multiset.count_pos, profile_count]
      exact hi
    have hcard : (profile (values r)).card = mass (values r) := by simp [profile, mass]
    have hrec := multiplicity_erase_mul (a := profile (values r))
      (n := mass (values r) - 1) (by omega) i hmem
    rw [Nat.sub_add_cancel hm, profile_count] at hrec
    rw [M_eq_multiplicity, M_eq_multiplicity, mass_lower r i hi, hp]
    exact hrec
  have mass_pos_of_ne_zero {a : σ → ℕ} (r : Box a) (hr : r ≠ 0) : 0 < mass (values r) := by
    classical
    by_contra h
    have hz : mass (values r) = 0 := Nat.eq_zero_of_not_pos h
    have hall : ∀ i, (r i).val = 0 := by
      intro i
      have hi : (r i).val ≤ mass (values r) := by
        change (values r) i ≤ ∑ j, (values r) j
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    apply hr
    funext i
    apply Fin.ext
    exact hall i
  have realSqrt_mul_ratio {A R L q m : ℕ} (hA : 0 < A) (hR : 0 < R)
      (hL : 0 < L) (hm : 0 < m) (hq : 0 < q) (hrel : m * L = q * R) :
      realSqrt ((q : ℝ) / m) * realSqrt ((A : ℝ) / L) =
        realSqrt ((A : ℝ) / R) := by
    dsimp [realSqrt]
    norm_cast
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (q : ℝ) / m)]
    congr 1
    field_simp
    exact_mod_cast hrel.symm
  have M_pos (b : σ → ℕ) : 0 < M b := by
    rw [M_eq_multiplicity]
    exact D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity_pos
      (profile b) (by simp [profile, mass])
  have realSqrt_self_ratio {n : ℕ} (hn : 0 < n) :
      realSqrt ((n : ℝ) / n) = 1 := by
    dsimp [realSqrt]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [div_self hn', Real.sqrt_one]
    norm_num
  have scalar_step {A : ℕ} {a : σ → ℕ} (r : Box a) (i : σ)
      (hA : 0 < A) (hi : 0 < (r i).val) :
      realSqrt (((r i).val : ℝ) / (mass (values r) : ℝ)) *
          realSqrt ((A : ℝ) / (M (values (lower r i)) : ℝ)) =
        realSqrt ((A : ℝ) / (M (values r) : ℝ)) := by
    have hmpos : 0 < mass (values r) := by
      have hle : (r i).val ≤ mass (values r) := by
        change (values r) i ≤ ∑ j, (values r) j
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega
    apply realSqrt_mul_ratio hA (M_pos (values r))
      (M_pos (values (lower r i))) hmpos hi
    exact M_lower_recurrence r i hi
  have residual_scalar_step {a : σ → ℕ} (r : Box a) (i : σ)
      (hi : 0 < (r i).val) :
    realSqrt (((r i).val : ℝ) / (mass (values r) : ℝ)) *
          realSqrt ((M a : ℝ) / (M (values (lower r i)) : ℝ)) =
        realSqrt ((M a : ℝ) / (M (values r) : ℝ)) :=
    scalar_step r i (M_pos a) hi
  have wordOp_smul (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
      (w : List σ) (c : ℂ) (x : H) :
      wordOp V w (c • x) = c • wordOp V w x := by
    induction w generalizing x with
    | nil => rfl
    | cons i w ih =>
        simp [wordOp, letter, ih]
  have realSqrt_ratio_cancel {A R : ℕ} (hA : 0 < A) (hR : 0 < R) :
      realSqrt ((R : ℝ) / A) * realSqrt ((A : ℝ) / R) = 1 := by
    dsimp [realSqrt]
    norm_cast
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (R : ℝ) / A)]
    congr 1
    field_simp
    norm_num
  have realSqrt_mul_inv_self {A : ℕ} (hA : 0 < A) :
      realSqrt (A : ℝ) * (realSqrt (A : ℝ))⁻¹ = 1 := by
    dsimp [realSqrt]
    norm_cast
    have hs : Real.sqrt (A : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (by exact_mod_cast hA : (0 : ℝ) < (A : ℝ))).ne'
    exact mul_inv_cancel₀ hs
  have values_top (a : σ → ℕ) : values (top a) = a := by
    funext i
    rfl
  have prefix_top_nil (a : σ → ℕ) : prefixRepresentative a (top a) = [] := by
    apply List.eq_nil_of_length_eq_zero
    have h := prefix_length a (top a)
    simpa [top, values, mass] using h
  have M_zero {a : σ → ℕ} : M (values (0 : Box a)) = 1 := by
    simp [M, values, mass]
  have prefix_zero_output (a : σ → ℕ) (P : PhysicalPreparation (H := H) a) :
      wordOp P.V (prefixRepresentative a (0 : Box a)) P.initial =
        (realSqrt (M a : ℝ))⁻¹ • P.final := by
    have hlen := prefix_length a (0 : Box a)
    have hcount : counts (prefixRepresentative a (0 : Box a)) = a := by
      funext i
      rw [prefix_counts]
      simp
    rw [emitted_list_output a P _ hlen, if_pos]
    exact hcount
  let φ : Box a → H := residual a P.V P.initial
  have hMa : 0 < M a := M_pos a
  have hunit_prefix (r : Box a) :
      ‖wordOp P.V (prefixRepresentative a r) P.initial‖ ^ 2 =
        (M (values r) : ℝ) / (M a : ℝ) := prefix_norm_sq a P r
  have hMr (r : Box a) : 0 < M (values r) := M_pos (values r)
  have hunit : ∀ r : Box a, ‖φ r‖ = 1 := by
    intro r
    have hsnon : 0 ≤ (M a : ℝ) / M (values r) := by positivity
    have hrnon : 0 ≤ (M (values r) : ℝ) / M a := by positivity
    have hy : 0 ≤ ‖wordOp P.V (prefixRepresentative a r) P.initial‖ := norm_nonneg _
    have hc : ‖realSqrt ((M a : ℝ) / (M (values r) : ℝ))‖ =
        Real.sqrt ((M a : ℝ) / (M (values r) : ℝ)) := by
      simp [realSqrt, Complex.norm_real,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [show φ r = realSqrt ((M a : ℝ) / (M (values r) : ℝ)) •
        wordOp P.V (prefixRepresentative a r) P.initial by rfl]
    rw [norm_smul, hc]
    have hsq := hunit_prefix r
    have hsquare : (Real.sqrt ((M a : ℝ) / (M (values r) : ℝ)) *
        ‖wordOp P.V (prefixRepresentative a r) P.initial‖) ^ 2 = 1 := by
      rw [mul_pow, Real.sq_sqrt hsnon]
      rw [hunit_prefix r]
      have hMaR : (M a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hMa)
      have hMrR : (M (values r) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hMr r))
      field_simp [hMaR, hMrR]
    have hprodnon : 0 ≤ Real.sqrt ((M a : ℝ) / (M (values r) : ℝ)) *
        ‖wordOp P.V (prefixRepresentative a r) P.initial‖ :=
      mul_nonneg (Real.sqrt_nonneg _) hy
    nlinarith
  have hzero : φ (0 : Box a) = P.final := by
    change residual a P.V P.initial (0 : Box a) = P.final
    rw [residual, M_zero, prefix_zero_output]
    simp only [Nat.cast_one, div_one]
    have hma : (realSqrt (M a : ℝ)) ≠ 0 := by
      dsimp [realSqrt]
      exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hMa : (0 : ℝ) < (M a : ℝ))).ne'
    rw [smul_smul, realSqrt_mul_inv_self hMa, one_smul]
  have hinitial : φ (top a) = P.initial := by
    change residual a P.V P.initial (top a) = P.initial
    rw [residual, prefix_top_nil, wordOp, values_top]
    simp [realSqrt_self_ratio hMa]
  refine ⟨hunit, hzero, hinitial, ?_, ?_⟩
  · intro r w hw
    have hco := prefix_coincidence a P r w hw
    rw [residual, hco]
    rw [smul_smul]
    have hcancel := realSqrt_ratio_cancel hMa (hMr r)
    rw [hcancel, one_smul]
  · intro r hr i
    by_cases hri : 0 < (r i).val
    · have hu : ∀ j, (prefixRepresentative a r ++ [i]).count j =
          a j - (lower r i j).val := by
        intro j
        rw [List.count_append]
        have hp := prefix_counts a r j
        change List.count j (prefixRepresentative a r) = a j - (r j).val at hp
        rw [hp]
        by_cases hji : j = i
        · subst j
          have hbound := box_le a r i
          simp [lower, sub, counts]
          omega
        · simp [lower, sub, counts, hji, Ne.symm hji]
      have hco := prefix_coincidence a P (lower r i)
        (prefixRepresentative a r ++ [i]) hu
      rw [wordOp_append] at hco
      have hletter : letter P.V i
          (wordOp P.V (prefixRepresentative a r) P.initial) =
          wordOp P.V (prefixRepresentative a (lower r i)) P.initial := by
        simpa [wordOp] using hco
      rw [if_pos hri]
      change letter P.V i (realSqrt ((M a : ℝ) / M (values r)) •
          wordOp P.V (prefixRepresentative a r) P.initial) =
        realSqrt (((r i).val : ℝ) / mass (values r)) •
          (realSqrt ((M a : ℝ) / M (values (lower r i))) •
            wordOp P.V (prefixRepresentative a (lower r i)) P.initial)
      rw [show letter P.V i (realSqrt ((M a : ℝ) / M (values r)) •
          wordOp P.V (prefixRepresentative a r) P.initial) =
          realSqrt ((M a : ℝ) / M (values r)) •
            letter P.V i (wordOp P.V (prefixRepresentative a r) P.initial) by
        simp [letter]]
      rw [hletter, smul_smul, residual_scalar_step r i hri]
    · have hri0 : (r i).val = 0 := Nat.eq_zero_of_not_pos hri
      have hmpos := mass_pos_of_ne_zero r hr
      have hletter : letter P.V i
          (wordOp P.V (prefixRepresentative a r) P.initial) = 0 := by
        apply continuation_injective P.V (mass (values r) - 1)
        intro v
        have hlen : (prefixRepresentative a r ++ (i :: List.ofFn v)).length = mass a := by
          rw [List.length_append, prefix_length, List.length_cons, List.length_ofFn]
          have hsplit := mass_split a r
          omega
        have hbad : ¬ counts (prefixRepresentative a r ++ (i :: List.ofFn v)) = a := by
          intro hh
          have hi_count := congrArg (fun q => q i) hh
          change List.count i (prefixRepresentative a r ++ (i :: List.ofFn v)) = a i at hi_count
          rw [List.count_append] at hi_count
          have hp := prefix_counts a r i
          change List.count i (prefixRepresentative a r) = a i - (r i).val at hp
          rw [hp, hri0] at hi_count
          simp at hi_count
        calc
          wordOp P.V (List.ofFn v)
              (letter P.V i (wordOp P.V (prefixRepresentative a r) P.initial)) =
              wordOp P.V (prefixRepresentative a r ++ (i :: List.ofFn v)) P.initial := by
            simp [wordOp_append, wordOp]
          _ = 0 := by rw [emitted_list_output a P _ hlen, if_neg hbad]
          _ = wordOp P.V (List.ofFn v) 0 := by
            symm
            simpa using (wordOp_smul P.V (List.ofFn v) (0 : ℂ) (0 : H))
      rw [if_neg hri]
      change letter P.V i (realSqrt ((M a : ℝ) / M (values r)) •
          wordOp P.V (prefixRepresentative a r) P.initial) = 0
      rw [show letter P.V i (realSqrt ((M a : ℝ) / M (values r)) •
          wordOp P.V (prefixRepresentative a r) P.initial) =
          realSqrt ((M a : ℝ) / M (values r)) •
            letter P.V i (wordOp P.V (prefixRepresentative a r) P.initial) by
        simp [letter]]
      rw [hletter, smul_zero]


end D5.S3.Quantum.StationaryPreparation.PhysicalGram
